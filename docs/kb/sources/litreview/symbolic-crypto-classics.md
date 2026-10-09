# Symbolic-cryptography classics — primary sources for the three proof genres

Retrieval + read-verification pass, 2026-07-31, for the symbolic-instance architecture of
`docs/uc-symbolic-crypto.md`. Genres: **(1)** Dolev–Yao model / intruder deduction /
weak secrecy; **(2)** applied pi calculus / frames / static equivalence / diff-equivalence;
**(3)** protocol attacks and inductive proofs.

House rule applied throughout: no claim below comes from memory. Every paper was
downloaded, converted, and read at the cited section; page numbers are the **printed**
page numbers of the archived PDF unless stated otherwise. PDFs: `../papers/<bibkey>.pdf`.

## Retrieved and verified

### `abadicortier2006` — genre 1 (deducibility) + genre 2 (static equivalence)
M. Abadi, V. Cortier, "Deciding knowledge in security protocols under equational
theories", *Theoretical Computer Science* 367(1–2):2–32, 2006 (conference version
ICALP 2004). Archived PDF = the openly available full version, INRIA Research Report
RR-5169 (2004), from HAL `inria-00071420`; printed pages below are RR pages.
VERIFIED: **frames** νñσ over a signature Σ with equational theory E, §2.2 p. 6;
**deducibility** φ ⊢ M as a four-rule inference system (substitution image, fresh-name
side condition `s ∉ ñ`, function application, closure under `=E`), §2.3 p. 6, with the
context characterization `νñσ ⊢ M ⟺ ∃ζ. fn(ζ) ∩ ñ = ∅ ∧ ζσ =E M` (Prop 1, p. 6);
**static equivalence** — equality of terms in a frame (Def 1, p. 7) and `φ ≈s ψ` iff
`dom φ = dom ψ` and `(M =E N)φ ⟺ (M =E N)ψ` for all M, N (Def 2, p. 7).
Canonical modern reference for both notions; this is the paper our
"ℰ_sym = deducibility presheaf, ≈ℰ_sym = static equivalence" reading of
`docs/uc-symbolic-crypto.md` §4.1 must match definition-for-definition.
Note (non-folklore): the two relations are **not** interchangeable. `⊢` reduces to `≈s`
once `dec(enc(x,y),y) = x` is available (Prop 3, §3.2 p. 8) but not conversely — Prop 4
(§3.3 p. 8) exhibits a theory where `≈s` is undecidable while `⊢` is decidable. So an
attacker-knowledge presheaf built from deducibility alone is strictly weaker than one
built from indistinguishability, even symbolically.

### `abadi2018applied` — genre 2
M. Abadi, B. Blanchet, C. Fournet, "The applied pi calculus: mobile values, new names,
and secure communication", *JACM* 65(1), 2018 (arXiv:1609.03003; the paper states it
"essentially subsumes" Abadi–Fournet, POPL 2001, filling gaps and incorporating
improvements). Printed pages = arXiv pages.
VERIFIED: extended processes with **active substitutions** `{M/x}` and **frames** as the
extended processes built from `0` and active substitutions by `|` and restriction, with
`φ(A)` the static-knowledge approximation of `A` (§2.1, p. 4); **static equivalence**
§4.2 — equality in a frame (Def 4.2) and `φ ≈s ψ` (Def 4.3), both p. 15; Lemma 4.2
(observational equivalence and static equivalence coincide *on frames*) and Lemma 4.3
(observational equivalence is strictly finer on extended processes), pp. 15–16.
Classical source for frames-as-static-knowledge — the exact dual of our
environment-as-presheaf, and the justification for restricting ℰ to DY-definable tests.

### `blanchet2016proverif` — genre 2 (proof method)
B. Blanchet, "Modeling and verifying security protocols with the applied pi calculus and
ProVerif", *Foundations and Trends in Privacy and Security* 1(1–2):1–135, 2016
(HAL `hal-01423760`, CC BY).
VERIFIED: **strong secrecy** as indistinguishability of `P₀{M/s}` and `P₀{N/s}` for all
closed M, N (Def 3.7, p. 72); **biprocesses** as the representation of a pair of processes
differing only in terms (p. 72–73); **diff-equivalence** as the absence of a reachable
*diverging* configuration, with the divergence rules (Div I/O), (Div Eval) (Def 3.9,
p. 74); **Theorem 3.5**: diff-equivalence ⇒ observational equivalence, p. 74.
Canonical source for the diff-equivalence proof method — the mechanized counterpart of
"prove ≈ℰ by a lockstep bisimulation of a paired process".
Note: the survey states plainly that diff-equivalence is *sufficient but not necessary*
for observational equivalence, with the counterexample
`if diff[true,false] then P else P'` (p. 74) — i.e. the mechanizable relation is strictly
finer than the semantic one, the same gap our exact-`≡` vs `≈ℰ` split has.

### `lowe1996` — genre 3 (attack)
G. Lowe, "Breaking and fixing the Needham-Schroeder public-key protocol using FDR",
*TACAS* 1996, LNCS 1055:147–166.
VERIFIED: the **man-in-the-middle attack** on NSPK, both as the FDR-produced CSP trace
and as the two interleaved runs α, β with the intruder using A as a decryption oracle
(p. 154); the **NSL fix** — put the responder's identity inside message 2,
`B → A : B.A.{Na.Nb.B}pK(A)` — and why it kills the attack (§4, p. 155); plus the
small-system-to-arbitrary-size reduction (§6, from p. 161).
Classical source for "the symbolic model finds real attacks": the reference point for any
claim that possibilistic simulation failure at the Rel-setup is a *useful* notion.

### `paulson1998inductive` — genre 3 (inductive proofs)
L. C. Paulson, "The inductive approach to verifying cryptographic protocols",
*Journal of Computer Security* 6(1–2):85–128, 1998 (Cambridge author version, minor
corrections Nov 2000; printed pages are that version's).
VERIFIED: protocols **inductively defined as sets of traces**, a trace being a list of
events `Says A B X` / `Notes A X` (abstract, and §3.5 p. 16); the three knowledge-closure
operators **`parts`, `analz`, `synth`**, each an inductively defined least closed set,
with the stated laws (`Crypt K X ∈ parts H ⇒ X ∈ parts H`, `analz H ⊆ parts H`,
`K ∈ synth H ⇒ K ∈ H`), §2.2 pp. 4–5, formal definitions §3.2 p. 12; the spy sending
messages drawn from **`synth(analz H)`** (§2.3 p. 5); secrecy proved by induction over
traces with regularity/unicity/secrecy lemma layers (§2.6–2.9 pp. 8–10, worked out for
Otway–Rees §4 and for NSPK-with-Lowe's-attack §5.1 p. 24).
Canonical inductive-invariant method; `synth(analz H)` is the concrete ancestor of the
"attacker closure" our attack structures abstract.

### `canettiherzog2006` — genre 1 ∩ UC bridge
R. Canetti, J. Herzog, "Universally composable symbolic analysis of mutual authentication
and key-exchange protocols", *TCC* 2006, LNCS 3876:380–403 (ePrint 2004/334).
VERIFIED: the **protocol mapping** `symb(·)` from concrete simple protocols (UC ITMs
using `Fcpke`) to symbolic protocols over a message algebra, and the induced **trace
mapping** (§4, p. 394); the **Mapping Lemma** (Lemma 1, p. 394): for all simple protocols
p, adversaries A, environments Z and polynomial-length inputs,
`Pr[t ← trace_{p,A,Z}(k,z) : symb(t) is not a valid DY trace for symb(p)]` is negligible;
the use of the JUC theorem to give each party a single `Fcpke` instance (p. 394).
Directly relevant as the prior art for our inter-setup transfer theorem.
Note (high value, and stronger than the folklore "symbolic analysis is sound"):
**Theorem 1** (p. 399) is an **iff** — a simple protocol p UC-realizes `F2ke` *if and
only if* `symb(p)` achieves Dolev–Yao secure key exchange, and the equivalence is
unconditional. The symbolic criterion is both sound *and complete* for the UC one at this
protocol class, which is exactly the shape of the equivalence conjectures in
`docs/equivalence-conjectures.md`. Their symbolic criterion also has a
"real-or-random secrecy" clause phrased as equality of *patterns* (p. 399), i.e.
Abadi–Rogaway patterns, not static equivalence.

## Not retrieved

Firewall-blocked; **not** filed, and nothing about their content is claimed anywhere.

- `dolevyao1983` — D. Dolev, A. C. Yao, "On the Security of Public Key Protocols",
  IEEE Trans. Inf. Theory 29(2):198–208, 1983 (genre 1, CORE). Semantic Scholar reports
  exactly one open-access copy, `www.cs.huji.ac.il/~dolev/pubs/dolev-yao-ieee-01056650.pdf`,
  and that host is default-deny blocked (HTTP 503 "Blocked by network policy"). Also
  blocked: `i.stanford.edu` (the 1981 Stanford TR CS-TR-81-854 preprint),
  `web.archive.org`, `scholar.archive.org`, `ieeexplore.ieee.org`, `apps.dtic.mil`;
  `dl.acm.org` and `researchgate.net` return 403; `citeseerx.ist.psu.edu` fails to
  connect. **Worth allowlisting: `www.cs.huji.ac.il` (first choice), `i.stanford.edu`,
  `web.archive.org`.**
- `abadifournet2001` — M. Abadi, C. Fournet, "Mobile Values, New Names, and Secure
  Communication", POPL 2001 (genre 2). `dl.acm.org/doi/pdf/10.1145/360204.360213` → 403;
  Blanchet's author page `bblanche.gitlabpages.inria.fr` is default-deny blocked; the MSR
  publication page 404s. Superseded here by `abadi2018applied`, which the JACM paper
  itself says subsumes it. **Worth allowlisting: `bblanche.gitlabpages.inria.fr`.**
- `needhamschroeder1978` — R. Needham, M. Schroeder, "Using Encryption for Authentication
  in Large Networks of Computers", CACM 21(12):993–999, 1978 (genre 3, bonus). Only route
  found was `dl.acm.org/doi/pdf/10.1145/359657.359659` → 403. The protocol itself is
  quoted verbatim in `lowe1996` (p. 149) and `paulson1998inductive` (§5.1), so the primary
  is not on the critical path.

Reachability notes for the next retrieval pass (measured this session): `arxiv.org`,
`link.springer.com` (open-access LNCS chapter PDFs at
`/content/pdf/<doi>.pdf` — this is how `lowe1996` and `canettiherzog2006` were obtained),
`inria.hal.science` / `hal.science` (intermittent anubis bot check on `/document`),
`www.cl.cam.ac.uk`, `www.cs.cornell.edu`, `www.cs.cmu.edu`, `dspace.mit.edu`,
`api.semanticscholar.org` (rate-limited, ~15 s spacing) are reachable;
`eprint.iacr.org` HTML pages are reachable but its PDF endpoint returns a Cloudflare 403.
