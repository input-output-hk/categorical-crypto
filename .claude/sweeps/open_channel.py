#!/usr/bin/env python3
"""qual-noise, the `Channel.` case: `Channel.inType` / `Channel.outType` used
620 times across 17 in-scope modules, where a local `open Channel` makes the
projections available bare, as `Channel/Core.agda` itself does.

Insertion point: the end of the PREAMBLE, meaning the last import or the
`module … where` line, whichever comes later, scanning only while every line so
far has been a pragma, comment, blank, module header or import.  All three
refinements are needed: most files here put their `open import`s before the
module line and `Machine/Iso.agda` does not, and `Machine/Core.agda` and
`Examples/Channels.agda` carry further imports in the middle of the file, which
a plain "last import" rule would wrongly take as the anchor.  Idempotent.
"""
import re, sys

# Blank, comment, pragma, import, module header, or any INDENTED continuation
# of one of those: a top-level declaration is never indented, so `^\s+\S`
# cannot end the preamble by mistake, and it catches a `using (…)` list broken
# over several lines with names on the second one.
PREAMBLE = re.compile(r'^\s*$|^\s*--|^\{-#|^(open )?import \S|^module\s|^\s+\S')

for p in sys.argv[1:]:
    s = open(p, encoding='utf-8').read()
    if not re.search(r'Channel\.(in|out)Type', s):
        continue
    ls = s.split('\n')
    at = -1
    for i, l in enumerate(ls):
        if not PREAMBLE.match(l):
            break
        if re.match(r'^(open )?import \S', l) or re.match(r'^module\s', l):
            at = i
    # an import may carry its `using (…)` / `hiding (…)` list on following
    # indented lines; land after the last of them, or the open attaches to it
    while at + 1 < len(ls) and re.match(r'^\s+\S', ls[at + 1]):
        at += 1
    if not any(re.match(r'^open Channel\s*$', l) for l in ls):
        ls.insert(at + 1, '')
        ls.insert(at + 2, 'open Channel')
    s = '\n'.join(ls)
    s = re.sub(r'\bChannel\.(in|out)Type\b', r'\1Type', s)
    open(p, 'w', encoding='utf-8').write(s)
    print('rewrote', p)
