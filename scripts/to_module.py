#!/usr/bin/env python3
"""Mechanically convert Lean files to the module system.

  module
  public import X          (every `import X`)
  <module docstring>
  @[expose] public section (everything public, definition bodies exposed: same visibility as before)

Usage: to_module.py FILE_OR_DIR...   (skips files already starting with `module`).
"""
import re, sys, pathlib

def convert(p):
    s = p.read_text()
    lines = s.split('\n')
    i = 0
    # skip leading blank lines and block/line comments that are not docstrings
    def skip_comments(i):
        while i < len(lines):
            t = lines[i].strip()
            if t == '' or t.startswith('--'):
                i += 1; continue
            if t.startswith('/-') and not t.startswith('/-!') and not t.startswith('/--'):
                while '-/' not in lines[i]: i += 1
                i += 1; continue
            break
        return i
    i = skip_comments(0)
    if i < len(lines) and re.match(r'module\b', lines[i].strip()):
        return False
    head = i
    j = i
    imports = []
    while True:
        j = skip_comments(j)
        if j < len(lines) and lines[j].startswith('import '):
            imports.append(j); j += 1
        else:
            break
    for k in imports:
        lines[k] = 'public ' + lines[k]
    # place public section after the module docstring if one directly follows, else after imports
    k = skip_comments(j)
    if k < len(lines) and lines[k].lstrip().startswith('/-!'):
        while '-/' not in lines[k]: k += 1
        k += 1
        ins = k
    else:
        ins = j
    lines[ins:ins] = ['', '@[expose] public section', '']
    lines[head:head] = ['module', '']
    p.write_text('\n'.join(lines))
    return True

n = 0
for a in sys.argv[1:]:
    a = pathlib.Path(a)
    for p in ([a] if a.is_file() else sorted(a.rglob('*.lean'))):
        n += convert(p)
print(f'converted {n} files')
