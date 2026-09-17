#!/usr/bin/env python3
"""Enumerate every comment block in the given Agda files, with noise flags.

Classes: header (block starting at line 1, before the `module` line), banner
(standalone block immediately followed by a blank line or another comment run
that precedes a section), standalone (own-line run), inline (trailing `--` on a
code line).  Flags mirror the contract's dimension-5 list:
  singleDefBanner  block precedes exactly one definition before the next block
  leftoverMarker   TODO/FIXME/XXX/HACK/NOTE:/old/was/temporarily
  typeEcho         block's words are largely the identifier / type that follows
  headerOverTier   file header longer than 25 lines
  insideDefinition block sits inside a definition body (indented, after a `=`)
Usage: enum_comments.py FILE...   (prints TSV; --json for json)
"""
import json, re, sys

MARKER = re.compile(r'\b(TODO|FIXME|XXX|HACK|NOTE:|obsolete|deprecated|for now|previously|used to)\b', re.I)

def blocks(path):
    lines = open(path).read().split('\n')
    out = []
    i = 0
    n = len(lines)
    while i < n:
        s = lines[i]
        st = s.strip()
        if st.startswith('--') or st.startswith('{-'):
            start = i
            if st.startswith('{-'):
                while i < n and '-}' not in lines[i]:
                    i += 1
                i += 1
            else:
                while i < n and lines[i].strip().startswith('--'):
                    i += 1
            out.append(dict(kind='standalone', start=start+1, end=i,
                            text='\n'.join(lines[start:i]),
                            indent=len(s) - len(s.lstrip())))
            continue
        # inline trailing comment (crude: ignore -- inside a string/mixfix name)
        m = re.search(r'\s--(\s.*)?$', s)
        if m and not st.startswith('--'):
            out.append(dict(kind='inline', start=i+1, end=i+1, text=s.strip(),
                            indent=len(s) - len(s.lstrip())))
        i += 1
    # classify header / following definition
    modline = next((k for k, l in enumerate(lines, 1)
                    if re.match(r'\s*module\b', l)), 10**9)
    for b in out:
        if b['kind'] == 'standalone' and b['start'] < modline:
            b['kind'] = 'header'
            b['headerOverTier'] = (b['end'] - b['start'] + 1) > 25
        # what follows
        nxt, ndefs = None, 0
        for k in range(b['end'], len(lines)):
            l = lines[k]
            if not l.strip() or l.strip().startswith('--'):
                continue
            if nxt is None:
                nxt = l.strip()
            mm = re.match(r'(\S+)\s*:(\s|$)', l)
            if mm:
                ndefs += 1
        b['next'] = nxt
        b['leftoverMarker'] = bool(MARKER.search(b['text']))
        if b['kind'] in ('standalone', 'banner') and b['indent'] > 0:
            b['insideDefinition'] = True
        if nxt:
            words = set(re.findall(r'[A-Za-z⁻¹ᴹᴷ₀₁₂ᵁℰ]+', b['text'].replace('--', '')))
            nw = set(re.findall(r'[A-Za-z⁻¹ᴹᴷ₀₁₂ᵁℰ]+', nxt))
            if nw and len(words) <= 8 and len(words & nw) >= max(1, len(words) // 2):
                b['typeEcho'] = True
    return out

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    res = {p: blocks(p) for p in args}
    if '--json' in sys.argv:
        print(json.dumps(res, indent=1))
    else:
        for p, bs in res.items():
            for b in bs:
                fl = ','.join(k for k in ('leftoverMarker','typeEcho','headerOverTier',
                                          'insideDefinition','singleDefBanner') if b.get(k))
                print(f"{p}\t{b['start']}-{b['end']}\t{b['kind']}\t{fl}\t{b['text'][:110]!r}")
