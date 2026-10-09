# Still-missing sources

As of 2026-07-11 every source cited by the review is retrieved in `../papers/`
(the last two, RSIM Inf.&Comp. 2007 and ILC PLDI 2019, were browser-downloaded by the
maintainer past the publisher bot-walls).

Later additions, 2026-07-31 (symbolic-crypto classics; full URL list and block reasons in
the "Not retrieved" section of `symbolic-crypto-classics.md`):

- Dolev–Yao 1983, IEEE TIT 29(2) — sole open-access copy is on `www.cs.huji.ac.il`
  (default-deny blocked); the 1981 Stanford TR preprint is on `i.stanford.edu` (blocked).
  **Allowlist request: `www.cs.huji.ac.il`, `i.stanford.edu`, `web.archive.org`.**
- Abadi–Fournet, POPL 2001 — ACM DL 403; Blanchet's author page
  `bblanche.gitlabpages.inria.fr` blocked. Superseded by the JACM version
  (`abadi2018applied.pdf`), which subsumes it. **Allowlist request:
  `bblanche.gitlabpages.inria.fr`.**
- Needham–Schroeder, CACM 1978 — ACM DL 403 was the only route found; the protocol is
  quoted verbatim in `lowe1996.pdf` and `paulson1998inductive.pdf`.

Later addition, 2026-10-09 (`docs/uc-setup-itm.md`):

- Canetti, UC, ePrint 2000/067, latest revision 2020-02-12 (intended file
  `canetti2001uc.pdf`) — `https://eprint.iacr.org/2000/067.pdf`. First three attempts:
  default-deny firewall (403 "Blocked by network policy"). After the domain was opened, the
  landing page `https://eprint.iacr.org/2000/067` loads (200), but the PDF and
  `/archive/versions/2000/067` sit behind a Cloudflare "Just a moment…" bot challenge that
  plain curl, a browser user-agent and headless Chromium (CDP) all fail. Needs a
  maintainer browser download.

Later addition, 2026-10-09 (`docs/uc-setup-ssp.md`):

- Dupressoir, Kohbrok, Oechsner, Bringing state-separating proofs to EasyCrypt — a
  security proof for Cryptobox, CSF 2022 (intended file `dupressoir2022.pdf`) —
  `https://eprint.iacr.org/2021/326.pdf`. Three curl attempts 90 s apart: Cloudflare
  "Just a moment…" challenge (the landing page `https://eprint.iacr.org/2021/326` loads,
  abstract only). Author/institution mirrors (`fdupress.net`, `soechsner.de`,
  `kkohbrok.github.io`, `research.vu.nl`, `www.research.ed.ac.uk`) are default-deny 403.
- Larsen, Schürmann, Nominal state-separating proofs, CSF 2025 (intended file
  `larsen2025nominal.pdf`) — `https://eprint.iacr.org/2025/598.pdf`. Same Cloudflare
  challenge, three attempts; `pure.itu.dk` is 403. Needs a maintainer browser download.

Later addition, 2026-10-09 (`docs/uc-setup-symbolic.md`): the Dolev–Yao 1983 entry above is
resolved. `dolevyao1983.pdf` was archived from the `web.archive.org` snapshot of the
`www.cs.huji.ac.il` copy; the direct host now answers with an HTML page instead of the PDF.
Nothing else for that plan was blocked.
