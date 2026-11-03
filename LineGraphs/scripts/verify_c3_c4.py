#!/usr/bin/env python3
"""Recheck each C3/C4/C20/C21 module under /usr/bin/time -v.

Run after `lake build LineGraphs`. This invokes
Lean directly through `lake env`, so it never rebuilds Mathlib. At most two checks run
concurrently by default. Detailed logs go in .lake/c3_c4_verify. The rows of the checked modules
are merged into LineGraphs/Computations/timings.tsv (created if absent), and
the audit modules C3C4Audit and C4C20FixesAudit must print only the standard axioms.
"""
import argparse
import concurrent.futures
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
COMP = ROOT / "LineGraphs/Computations"
LOGS = ROOT / ".lake/c3_c4_verify"
SUPPORT = [
    "ModelCertificates", "ModelIsoProperties", "NeighborCertificates", "NeighborData",
    "RootMapCertificates", "RootMapData", "SimpleRootCertificates", "StarCertificates",
]
AUDITS = ["C3C4Audit", "C4C20FixesAudit"]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def elapsed_seconds(value):
    result = 0.0
    for part in value.split(":"):
        result = 60 * result + float(part)
    return result


def check_axiom_audit(source, text):
    """Require every directive, including indented ones, with only standard axioms."""
    expected = set(re.findall(r"^[ \t]*#print axioms (\S+)", source, re.MULTILINE))
    entries = re.findall(
        r"'(\S+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        text,
    )
    audited = {name for name, _ in entries}
    if not expected or not expected <= audited:
        raise ValueError(f"Missing axiom audit declarations: {sorted(expected - audited)}")
    found = set(re.findall(r"[\w.]+", " ".join(axioms for _, axioms in entries)))
    if not found <= STANDARD:
        raise ValueError(f"Unexpected axioms: {sorted(found - STANDARD)}")


def check(path):
    output = LOGS / f"{path.stem}.log"
    resources = LOGS / f"{path.stem}.time"
    with output.open("w") as log:
        proc = subprocess.run(
            ["/usr/bin/time", "-v", "-o", str(resources), "lake", "env", "lean",
             str(path.relative_to(ROOT))], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
            check=False,
        )
    stats = resources.read_text()
    wall = re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.*)", stats)
    rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", stats)
    text = output.read_text()
    ok = proc.returncode == 0 and not re.search(r"\bwarning:", text)
    print(f"{path.stem}: {'PASS' if ok else 'FAIL'}", flush=True)
    return path.stem, elapsed_seconds(wall[1]), int(rss[1]), proc.returncode, ok


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    LOGS.mkdir(parents=True, exist_ok=True)
    paths = sorted({p for prefix in ["C3", "C4", "C20", "C21"]
                    for p in COMP.glob(prefix + "*.lean")} |
                   {COMP / (stem + ".lean") for stem in SUPPORT})
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(check, paths))
    timings = COMP / "timings.tsv"
    if timings.exists():
        header, *lines = timings.read_text().splitlines()
    else:
        header = "file\twall\tpeak_RSS_KiB\tpeak_RSS_GiB"
        lines = []
    table = {line.split("\t")[0]: line for line in lines}
    for n, t, r, _, _ in rows:
        name = f"LineGraphs/Computations/{n}.lean"
        wall = f"{int(t // 60)}:{t % 60:05.2f}"
        table[name] = f"{name}\t{wall}\t{r}\t{r / 2**20:.3f}"
    timings.write_text("\n".join([header] + [table[k] for k in sorted(table)]) + "\n")
    if not all(row[-1] for row in rows):
        raise SystemExit("One or more modules failed or produced warnings; see .lake/c3_c4_verify.")
    for audit in AUDITS:
        text = (LOGS / f"{audit}.log").read_text()
        try:
            check_axiom_audit((COMP / f"{audit}.lean").read_text(), text)
        except ValueError as error:
            raise SystemExit(f"{audit}: {error}") from error
    print(f"All {len(rows)} modules passed without warnings.")


if __name__ == "__main__":
    main()
