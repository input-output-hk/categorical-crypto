#!/usr/bin/env python3
"""Hand-rolled style sweep for this repository, driven by the real typecheck
oracle (there is no tree-sitter toolkit here; see .claude/sweeps/README.md).

Each class enumerates candidate single-site edits by line-oriented parsing.
`--enumerate` lists them; `--apply N[,N...]` applies a subset.  The parent
drives the keep/revert decision with .claude/sweeps/check.sh, bisecting a red
batch, so the oracle decides every site.

Classes
  using-drop        `open import X using (a; b)` -> `open import X`
                    (skips `using () renaming`, skips `public`, skips `hiding`)
  implicit-app      an explicit `{A}` argument at an application site
  pat-implicit      an unused `{x}` pattern on a clause LHS
  join-lines        a continuation line that fits within 80 cols when joined
  enum-with         a `with` block, flagged when it has a single scrutinee
  enum-where        a `where`/`let` binding used exactly once in its scope
  qual-noise        a module qualifier `R.` used 3+ times in one definition
"""
import argparse, json, re, sys, os

def lines(p):
    return open(p, encoding='utf-8').read().split('\n')

def write(p, ls):
    open(p, 'w', encoding='utf-8').write('\n'.join(ls))

# ---------------------------------------------------------------- enumerate

def c_using_drop(p, ls):
    out = []
    i = 0
    while i < len(ls):
        l = ls[i]
        m = re.match(r'^(\s*)open import (\S+)\s+using\s*\(', l)
        if m and 'public' not in l and 'renaming' not in l:
            # gather the (possibly multi-line) using list
            j, depth = i, 0
            while j < len(ls):
                depth += ls[j].count('(') - ls[j].count(')')
                if depth <= 0 and j >= i:
                    break
                j += 1
            blob = '\n'.join(ls[i:j+1])
            if 'renaming' in blob or 'public' in blob:
                i = j + 1
                continue
            out.append(dict(cls='using-drop', file=p, start=i+1, end=j+1,
                            names=len(re.findall(r';', blob)) + 1,
                            new=[m.group(1) + 'open import ' + m.group(2)],
                            old=ls[i:j+1]))
            i = j + 1
            continue
        i += 1
    return out

IMPL = re.compile(r'\{([A-Za-z_][^{}=:]*?)\}')

def c_implicit_app(p, ls):
    out = []
    for i, l in enumerate(ls):
        s = l.strip()
        if s.startswith('--') or not s:
            continue
        if re.match(r'^\s*(open |import |module |\{-#)', l):
            continue
        # only applications: a `{X}` that is not part of a binder `(x : A)` or
        # a signature's leading telescope, and not `{ field = ...}` records
        if '=' not in l:
            continue          # only right-hand sides: a binder is never one
        if re.search(r'\{[^{}]*=', l):
            continue          # record expression
        eq = l.index('=')
        if l[eq-1:eq+1] in ('==',) or l[eq:eq+2] == '=>':
            continue
        for m in IMPL.finditer(l):
            if m.start() < eq:
                continue      # left of the `=`: a pattern, not an argument
            arg = m.group(1).strip()
            if not arg or arg.startswith('-') or '→' in arg or '=' in arg:
                continue
            out.append(dict(cls='implicit-app', file=p, start=i+1, end=i+1,
                            arg=arg, col=m.start(),
                            new=[l[:m.start()].rstrip() + ' ' + l[m.end():].lstrip()
                                 if l[m.end():].strip() else l[:m.start()].rstrip()],
                            old=[l]))
    return out

def c_pat_implicit(p, ls):
    out = []
    for i, l in enumerate(ls):
        if l.strip().startswith('--') or '=' not in l:
            continue
        lhs, _, rhs = l.partition('=')
        if ':' in lhs or lhs.strip().startswith(('open', 'import', 'module')):
            continue
        for m in IMPL.finditer(lhs):
            name = m.group(1).strip()
            if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\'′ᵢₒ]*', name):
                continue
            # the bound name must not occur in the rhs or in later where-lines
            scope = [rhs]
            j = i + 1
            while j < len(ls) and (not ls[j].strip() or
                                   len(ls[j]) - len(ls[j].lstrip()) >
                                   len(l) - len(l.lstrip())):
                scope.append(ls[j]); j += 1
            if any(re.search(r'\b' + re.escape(name) + r'\b', t) for t in scope):
                continue
            out.append(dict(cls='pat-implicit', file=p, start=i+1, end=i+1,
                            name=name,
                            new=[l[:m.start()].rstrip() + ' ' + l[m.end():].lstrip()],
                            old=[l]))
    return out

def c_join_lines(p, ls):
    out = []
    for i in range(len(ls) - 1):
        a, b = ls[i], ls[i+1]
        if not a.strip() or not b.strip():
            continue
        if a.strip().startswith('--') or b.strip().startswith('--'):
            continue
        if '--' in a or '--' in b:
            continue
        ia, ib = len(a) - len(a.lstrip()), len(b) - len(b.lstrip())
        if ib <= ia:
            continue                       # not a continuation
        if re.match(r'^\s*(where|with|module|open|import|\{-#)', b):
            continue
        if re.search(r'\bwhere\s*$', a) or a.rstrip().endswith(('(', 'λ')):
            continue
        joined = a.rstrip() + ' ' + b.strip()
        if len(joined) <= 80:
            out.append(dict(cls='join-lines', file=p, start=i+1, end=i+2,
                            new=[joined], old=[a, b]))
    return out

def c_enum_with(p, ls):
    out = []
    for i, l in enumerate(ls):
        m = re.search(r'\bwith\b(.*)$', l)
        if not m or l.strip().startswith('--'):
            continue
        scrut = m.group(1).strip()
        n = len([x for x in scrut.split('|') if x.strip()])
        out.append(dict(cls='enum-with', file=p, start=i+1, end=i+1,
                        scrutinees=n, scrut=scrut,
                        singleUseCandidate=(n == 1)))
    return out

def c_enum_where(p, ls):
    out = []
    for i, l in enumerate(ls):
        if not re.match(r'^\s*(where|let)\b', l) and not re.search(r'\bwhere\s*$', l):
            continue
        # a `record … where` / `data … where` / `module … where` block is a
        # declaration, not a local binding group: its members are fields.
        if re.search(r'\b(record|data|module|private)\b', l):
            continue
        base = len(l) - len(l.lstrip())
        j = i + 1
        body = []
        while j < len(ls) and (not ls[j].strip() or
                               len(ls[j]) - len(ls[j].lstrip()) > base):
            body.append((j, ls[j])); j += 1
        blob = '\n'.join(t for _, t in body)
        for k, t in body:
            mm = re.match(r'^\s*([A-Za-z_][A-Za-z0-9_\'′ᵢₒ⁻]*)\s*[:=]', t)
            if not mm:
                continue
            nm = mm.group(1)
            uses = len(re.findall(r'\b' + re.escape(nm) + r'\b', blob)) - \
                   len(re.findall(r'^\s*' + re.escape(nm) + r'\s*[:=]', blob, re.M))
            out.append(dict(cls='enum-where', file=p, start=k+1, end=k+1,
                            name=nm, uses=uses,
                            singleUseCandidate=(uses == 1)))
    return out

def c_qual_noise(p, ls):
    from collections import Counter
    out = []
    cur, start = None, 0
    def flush(end):
        if cur is None:
            return
        blob = '\n'.join(ls[start:end])
        c = Counter(re.findall(r'\b([A-Z][A-Za-z0-9_]*)\.[A-Za-z_]', blob))
        for q, n in c.items():
            if n >= 3:
                out.append(dict(cls='qual-noise', file=p, start=start+1, end=end,
                                qualifier=q, hits=n, definition=cur))
    for i, l in enumerate(ls):
        m = re.match(r'^([A-Za-z_Ͱ-῿℀-⅏][^\s:]*)\s*:', l)
        if m:
            flush(i); cur, start = m.group(1), i
    flush(len(ls))
    return out

CLASSES = dict(**{'using-drop': c_using_drop, 'implicit-app': c_implicit_app,
                  'pat-implicit': c_pat_implicit, 'join-lines': c_join_lines,
                  'enum-with': c_enum_with, 'enum-where': c_enum_where,
                  'qual-noise': c_qual_noise})

def enumerate_(cls, files):
    res = []
    for p in files:
        res += CLASSES[cls](p, lines(p))
    for n, r in enumerate(res):
        r['id'] = n
    return res

def apply_(res, ids):
    # apply high line numbers first so earlier edits keep their offsets
    byfile = {}
    for i in ids:
        r = res[i]
        byfile.setdefault(r['file'], []).append(r)
    for p, rs in byfile.items():
        ls = lines(p)
        for r in sorted(rs, key=lambda r: -r['start']):
            if 'new' not in r:
                print('NOT-MECHANICAL', r['cls'], r['file'], r['start'], file=sys.stderr)
                continue
            ls[r['start']-1:r['end']] = r['new']
        write(p, ls)

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--sweep', required=True, choices=sorted(CLASSES))
    ap.add_argument('--apply', default='')
    ap.add_argument('--json', action='store_true')
    ap.add_argument('files', nargs='+')
    a = ap.parse_args()
    res = enumerate_(a.sweep, a.files)
    if a.apply:
        ids = [int(x) for x in a.apply.split(',') if x != '']
        apply_(res, ids)
        print(f'applied {len(ids)} of {len(res)}')
    elif a.json:
        print(json.dumps(res, indent=1, ensure_ascii=False))
    else:
        for r in res:
            extra = ' '.join(f'{k}={v}' for k, v in r.items()
                             if k not in ('cls','file','start','end','new','old','id'))
            print(f"{r['id']}\t{r['file']}:{r['start']}-{r['end']}\t{extra}")
        print(f'-- {len(res)} candidates in class {a.sweep}', file=sys.stderr)
