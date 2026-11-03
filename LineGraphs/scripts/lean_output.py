"""Shared formatting for untrusted generators of kernel-checked Lean data."""
import re

COPYRIGHT = '''/-
Copyright (c) 2026 Krystal Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Krystal Guo
-/
'''


def write_lean(path, source, title):
    if not source.startswith('/-\nCopyright'):
        source = COPYRIGHT + source
    if '/-!\n# ' not in source:
        source = source.replace('/-! ', '/-!\n# ' + title + '\n\n', 1)
    matches = list(re.finditer(r'^def ([^\s:(]+)', source, re.M))
    for match in reversed(matches):
        if source[:match.start()].rstrip().endswith('-/'):
            continue
        name = match.group(1)
        if 'Indices' in name:
            doc = 'Structured root indices for the certified materialized table.'
        elif name.endswith('Roots'):
            doc = 'The materialized integer root table.'
        elif name.endswith('Tree'):
            doc = 'Balanced membership tree storing each complete integer root.'
        elif name.endswith('Decode'):
            doc = 'Executable root membership using the balanced lookup tree.'
        else:
            raise ValueError(f'Missing documentation for {name}')
        source = source[:match.start()] + '/-- ' + doc + ' -/\n' + source[match.start():]
    path.write_text(source)
