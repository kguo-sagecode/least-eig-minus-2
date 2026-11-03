#!/usr/bin/env python3
"""Build the library, measure its checker modules, and audit the main theorems.

Run from any directory: python3 LineGraphs/scripts/verify.py
Fetch the Mathlib cache first with `lake exe cache get`. No Mathlib target is built explicitly.
Canonical Lake setup/import artifacts are used; there is no private import overlay.
Logs and GNU time output go to .lake/checkers/verify. Published summaries go to
LineGraphs/Computations/timings.tsv and axioms.txt.
"""
import argparse
import csv
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'LineGraphs' / 'Computations'
LOGS = ROOT / '.lake' / 'checkers' / 'verify'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def timed(command, name):
    log = LOGS / (name + '.log')
    timing = LOGS / (name + '.time')
    with log.open('w') as output:
        proc = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *command],
                              cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    text = log.read_text()
    if proc.returncode:
        print(text, flush=True)
        raise SystemExit(f'{name}: failed (exit {proc.returncode})')
    return text, timing.read_text()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--no-build', action='store_true',
                        help='Use a successful, current lake build LineGraphs')
    args = parser.parse_args()
    LOGS.mkdir(parents=True, exist_ok=True)
    if not args.no_build:
        output, _ = timed(['lake', 'build', 'LineGraphs'], 'build')
        if re.search(r'warning: LineGraphs/Computations/', output):
            print(output, flush=True)
            raise SystemExit('The library build has checker warnings')
    results = []
    sources = sorted(BASE.glob('*.lean')) + sorted((ROOT / 'LineGraphs/Spectral').glob('*.lean'))
    for source in sources:
        relative = source.relative_to(ROOT)
        module = '.'.join(relative.with_suffix('').parts)
        setup = ROOT / '.lake/build/ir' / relative.with_suffix('.setup.json')
        if not setup.exists():
            raise SystemExit(f'Missing canonical Lake setup: {setup}; run lake build LineGraphs')
        output, timing = timed(['lake', 'env', 'lean', '--setup', str(setup), str(relative)], module)
        if re.search(r'\b(?:error|warning):', output):
            print(output, flush=True)
            raise SystemExit(f'{module}: warnings are not allowed')
        wall = re.search(r'Elapsed \(wall clock\) time .*: (\S+)', timing).group(1)
        rss = int(re.search(r'Maximum resident set size \(kbytes\): (\d+)', timing).group(1))
        results.append((str(relative), wall, rss, f'{rss / 1048576:.3f}'))
        print(f'{module}: {wall}, {rss / 1048576:.3f} GiB', flush=True)
    audit = ''.join((LOGS / (name + '.log')).read_text() for name in
                    ['LineGraphs.Computations.Audit', 'LineGraphs.Computations.ModelsAudit'])
    groups = re.findall(r'depends on axioms:\s*\[([^]]*)\]', audit)
    if not groups:
        raise SystemExit('No axiom audit results were printed')
    axioms = {word.strip() for group in groups for word in group.split(',') if word.strip()}
    if axioms - ALLOWED:
        raise SystemExit(f'Unexpected axioms: {sorted(axioms - ALLOWED)}')
    (BASE / 'axioms.txt').write_text(audit)
    with (BASE / 'timings.tsv').open('w', newline='') as output:
        writer = csv.writer(output, delimiter='\t', lineterminator='\n')
        writer.writerow(('file', 'wall', 'peak_RSS_KiB', 'peak_RSS_GiB'))
        writer.writerows(results)
    print(f'{len(results)} modules passed; {len(groups)} axiom checks: {sorted(axioms)}', flush=True)


if __name__ == '__main__':
    main()
