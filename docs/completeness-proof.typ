#set document(title: "Completeness of the APROP hypergraph decoder", author: "categorical-crypto")
#set page(numbering: "1", margin: (x: 2.2cm, y: 2.4cm))
#set par(justify: true, leading: 0.62em)
#set text(size: 10.5pt, font: "New Computer Modern")
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => block(above: 1.2em, below: 0.7em)[#it]
#set math.equation(numbering: "(1)")

#align(center)[
  #text(17pt, weight: "bold")[An informal proof of #raw("completeness-full")]
  #v(0.2em)
  #text(11pt)[Faithfulness of the free-SMC #sym.arrow.r hypergraph translation, \
  resting on a single generator-free permutation-coherence axiom]
  #v(0.3em)
  #text(9pt, style: "italic")[categorical-crypto · APROP completeness · working note]
]

#v(0.5em)

This note develops, by hand, a proof of the APROP completeness theorem
$
  #raw("completeness-full") : quad ⟪f⟫ space tilde.equiv^("H") space ⟪g⟫ quad => quad f approx_("Term") g,
$
the faithfulness direction of the string-diagram / hypergraph correspondence for the
*free symmetric monoidal category* (PROP) on a signature. The goal is a proof that is
mathematically transparent and whose every step maps onto a concrete formal obligation,
so that the formalization can be guided (and simplified) by it. The proof rests on a
*single* hard axiom — generator-free permutation coherence (Kelly 1964) — with every
other ingredient being either an existing `≈Term` axiom or finite constructive
combinatorics.

We write $approx$ for $approx_("Term")$ and $tilde.equiv^("H")$ for the hypergraph iso
$#raw("≅ᴴ")$ throughout.

= Objects

We work with the (unpruned) translation `⟪f⟫F`, written $H_f$, since that is what the
decoder operates on. For a term $f : A -> B$:

- *vertices* $V$ (wires), labelled $"vlab" : V -> X$ by atoms;
- *edges* $E$ (generator-boxes), each $e$ carrying a generator $g_e : "mor" A_e space B_e$
  with ordered input/output wire-lists $"ein" e, "eout" e : "List" V$, subject to
  $ "map" "vlab" ("ein" e) = "flatten" A_e, quad "map" "vlab" ("eout" e) = "flatten" B_e ; $
- an *ordered boundary* $"dom", "cod" : "List" V$ with
  $"map" "vlab" "dom" = "flatten" A$ and $"map" "vlab" "cod" = "flatten" B$.

== The decoder

Reading off `Decode.agda`, the decoder produces a term
$"unflatten"("dom") -> "unflatten"("cod")$ by sequentialising the diagram:

$
  "decode" H = underbrace("permute"(pi_("cod")), "final") compose "layer"_(n-1) compose dots.c compose "layer"_0,
$ <decode>

processing the edges in `Fin` order $0, dots, n-1$ while threading a *stack* of live wires
(initially $"dom"$). Each layer is

$
  "layer"_e = ("coerce") compose ("Agen" g_e space times.o space "id") compose ("coerce") compose "permute"(pi_e),
$ <layer>

where $pi_e$ is the permutation that brings $"ein" e$ to the front of the current stack and
updates it to $"eout" e space "++" space "rest"$, and $pi_("cod")$ matches the final stack
to $"cod"$. *Crucially, every $"permute"(dot.c)$ and every coercion is built solely from
$sigma, alpha, lambda, rho, "id"$ — no generator occurs in them.* Thus $"decode" H$ is a
*canonical sequentialisation* of the string diagram $H$: a composite of one box-layer per
edge, framed by pure wiring.

== Isomorphisms

An iso $Phi = (phi, psi) : H tilde.equiv^("H") J$ is a vertex bijection $phi$ and an edge
bijection $psi$ with
$
  "vlab"_H = "vlab"_J compose phi quad ("φ-lab"), \
  "ein"_J (psi space e) = "map" phi ("ein"_H space e), quad "eout"_J (psi space e) = "map" phi ("eout"_H space e), \
  "dom"_J = "map" phi ("dom"_H), quad "cod"_J = "map" phi ("cod"_H),
$
and $g_(psi e) = g_e$ up to the induced label equalities (`ψ-elab`).

= The skeleton of the proof

$
  f quad underbrace(approx, "(I)") quad "decode" ⟪f⟫ quad underbrace(approx, "(II)") quad "decode" ⟪g⟫ quad underbrace(approx, "(I)") quad g.
$ <skeleton>

Everything reduces to two theorems:

#block(inset: (left: 1em))[
  *(I) Normal-form theorem.* #h(0.4em) $f approx "decode" ⟪f⟫$ — every term equals its own canonical decoding.

  *(II) Iso-invariance.* #h(0.4em) $⟪f⟫ tilde.equiv^("H") ⟪g⟫ => "decode" ⟪f⟫ approx "decode" ⟪g⟫$.
]

The iso is used *only* in (II).

= Lemma 0: vertex relabelling is free

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma 0.* #h(0.3em) $"decode" H$ depends on $H$ only through $"vlab"$ and the ordered
  incidence/boundary lists $"ein", "eout", "dom", "cod"$ — never on the vertex identities.
]

*Proof.* Every quantity the decoder touches — the stack contents, each $pi_e$, the final
$pi_("cod")$, and hence every layer in @decode and @layer — is a function of
$"map" "vlab" (dot.c)$ applied to the incidence and boundary lists. The vertex set $V$
appears only as an index domain. #h(1fr) $square.stroked$

Now an iso carries incidence and boundary across by $"map" phi$ and satisfies
$"vlab"_H = "vlab"_J compose phi$, so for every edge
$
  "map" "vlab"_H ("ein"_H space e) = "map" ("vlab"_J compose phi)("ein"_H space e)
    = "map" "vlab"_J ("map" phi ("ein"_H space e)) = "map" "vlab"_J ("ein"_J (psi space e)),
$
and likewise for $"eout", "dom", "cod"$. Hence, *after re-indexing $J$'s edges by $psi$, the
two hypergraphs present identical $"vlab"$-level data.* This is precisely *why $phi$ may be
discarded*: it is genuinely redundant, not vacuously dropped.

#block(inset: (left: 1em), above: 0.6em, below: 0.6em)[
  #text(9.5pt)[*Remark (it does not collapse $sigma$ and $"id"$).* Take
  $sigma, "id" : A times.o A -> A times.o A$. Both translate to edge-free graphs
  with two $A$-labelled wires and $"dom" = [v_0, v_1]$, but $"cod"_("id") = [v_0,v_1]$ while
  $"cod"_sigma = [v_1, v_0]$. No $phi$ can match both $"dom"$ and the swapped $"cod"$, so
  $⟪sigma⟫$ and $⟪"id"⟫$ are *not* $tilde.equiv^("H")$-related; and the final
  $"permute"(pi_("cod"))$ reads the $"cod"$ ordering, so the decoder distinguishes them. The
  wiring lives in the boundary *order*, which $phi$ must respect.]
]

#block(stroke: (left: 1.5pt + luma(50%)), inset: (left: 10pt), above: 0.7em)[
  *Corollary (reduction of (II)).* After the $phi$/$psi$ identification, $"decode" ⟪f⟫$ and
  $"decode" ⟪g⟫$ are two runs of the decoder on *the same* $"vlab"$-level hypergraph that
  differ *only* in the order in which edges are processed: $"decode" ⟪f⟫$ uses the identity
  order; $"decode" ⟪g⟫$ uses the order $tau$ that $psi$ induces on $f$'s edges.
]

= (II) Iso-invariance via edge-order independence

Define the *dependency relation* $prec_H$ on the edges of $H$ by shared wires:
$
  e prec_H e' quad :<=> quad ("wires of " "eout"_H e) inter ("wires of " "ein"_H e') eq.not emptyset
$
($e$ produces a wire that $e'$ consumes), and likewise $prec_J$ on $J$. The corollary above
says the two decodings differ only in the order their edges are processed; to compare them
we must know that this order-difference lives over *one* poset. That needs the bridge from
the iso to the dependency structure, which has two parts.

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma A (the iso is a dependency-order isomorphism) #emph[— formalized].* #h(0.3em)
  $e prec_H e' <=> psi space e prec_J psi space e'$.
  #h(0.3em) #text(8.5pt)[(`Discharge/EdgeDependency.agda`, `--safe`, no postulates.)]

  #v(0.3em)
  #text(9.5pt)[*Proof.* The iso gives $"eout"_J (psi space e) = "map" phi ("eout"_H space e)$
  and $"ein"_J (psi space e') = "map" phi ("ein"_H space e')$, so
  $ ("wires of " "eout"_J (psi space e)) inter ("wires of " "ein"_J (psi space e'))
    = phi("eout"_H space e) inter phi("ein"_H space e')
    = phi(("eout"_H space e) inter ("ein"_H space e')), $
  the last step because $phi$ is *injective*. As $phi$ is a bijection, the right side is
  nonempty iff $("eout"_H space e) inter ("ein"_H space e')$ is. $square.stroked$]
]

So if we pull $J$'s processing order back through $psi$ to an order $tau$ on $H$'s edges,
Lemma A makes $tau$ a linear extension of $prec_H$ *iff* $J$'s order is a linear extension of
$prec_J$. The remaining question is whether the actual `Fin` orders *are* such linear
extensions — i.e. that they are topologically valid. This is *not* automatic for an
arbitrary hypergraph (whose $prec$ may even have cycles); it holds because the hypergraph
comes from a term:

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma C (topological validity — already formalized).* #h(0.3em) The natural `Fin` order on
  the edges of $⟪f⟫$ is a linear extension of $prec_(⟪f⟫)$; equivalently, processing edges in
  `Fin` order fires every edge successfully. This is exactly `AllFire-natural-range`
  (`AllFireNatural.agda`), which is *constructively proven* in the codebase.
]

Two supporting facts complete the bridge, both of the cheap "incidence-only" kind rather than
coherence content: (i) *monogamy* — each wire is produced once and consumed once — which makes
$prec$ a strict order and the notion of *independent* edges meaningful; this is the existing
`Linear` predicate (`Linearity.agda`), provable for every $⟪f⟫$. (ii) `AllFire` *transports
across the iso*: since firing depends only on incidence, which the iso preserves,
$"AllFire"(J, o_J)$ gives $"AllFire"(H, tau)$ — the same propositional, coherence-free flavour
as Lemma 0.

Combining: both $H$'s identity `Fin` order $o_H$ (Lemma C) and the pulled-back order $tau$
(Lemma A + transport) are linear extensions of the *same* poset $prec_H$. Now the
order-difference is purely combinatorial:

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Combinatorial fact (constructive) #emph[— formalized].* Any two linear extensions of a
  finite poset are connected by a finite sequence of transpositions of
  *adjacent, $prec$-incomparable* elements, each step preserving validity (no-inversion).
  (Bubble-to-front + well-founded induction on length.)
  #h(0.3em) #text(8.5pt)[(`Combinatorics/LinearExtension.agda`, `connectivity`, `--safe`, no
  postulates; needs only irreflexivity of $prec$, not transitivity.)]
]

So it suffices to show that swapping two adjacent *independent* edges $e, e'$ in the
processing order changes $"decode"$ only up to $approx$. Locally the two runs read

$
  dots.c compose "layer"_(e') compose "layer"_e compose dots.c
  quad "vs." quad
  dots.c compose "layer"_e compose "layer"_(e') compose dots.c .
$

Since $e, e'$ are independent, $"ein" e'$ is disjoint from $"eout" e$; the two boxes act on
disjoint blocks of wires and both runs reach the same stack-multiset afterwards. The two
local composites are therefore equal by the *interchange (symmetry-naturality) axiom*

$
  sigma compose (p times.o q) quad approx quad (q times.o p) compose sigma,
$ <interchange>

instantiated at $p = ("Agen" g_e times.o "id")$, $q = ("Agen" g_(e') times.o "id")$
— *parametric in the boxes, treating them as opaque*. The surrounding wire-permutations $pi$
differ between the two orders, but the *total $"dom" -> "cod"$ wiring of the whole composite
is the same bijection*: it is fixed by the hypergraph's incidence, and reordering boxes does
not move wires. Matching those two permutation-terms is exactly the generator-free coherence

$
  "eval"(pi) approx_("fb") "eval"(pi') quad => quad "permute"(pi) approx "permute"(pi')
  quad quad (bold(K) = #raw("FaithfulnessResidual")).
$ <K>

Chaining over the linear-extension connection yields $"decode" ⟪f⟫ approx "decode" ⟪g⟫$.
#h(1fr) $square.stroked$

#block(inset: (left: 1em), above: 0.5em)[
  #text(9.5pt)[*The linchpin.* The one joint that deserves formal scrutiny is the claim that
  the per-step $pi_e$ differences always compose to the *same* $"eval"$-bijection, so that
  @K applies. This is the invariance of the total $"dom" -> "cod"$ wiring under box
  reordering; it is the place where a hidden obligation could lurk, and the natural first
  target when formalizing (II).]
]

= (I) Normal-form theorem

By induction on $f$, using the action of $⟪dot.c⟫$:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 4pt, y: 5pt),
  align: (left + top, left + top),
  [*$"id"$, $alpha, lambda, rho$*],
  [translate to edge-free graphs (pure rewiring); $"decode"$ is a single $"permute"$
   realising the identity/reassociation bijection, equal to the term by monoidal coherence
   ($bold(M)$, constructive via `MonoidalCoherence`).],
  [*$sigma$*],
  [edge-free; $"decode" ⟪sigma⟫$ is $"permute"$ of the swap bijection, equal to $sigma$ by
   $bold(K)$ (a one-transposition instance).],
  [*$"Agen" u$*],
  [one edge; $"decode" ⟪"Agen" u⟫ = ("coerce") compose ("Agen" u times.o "id") compose ("coerce") compose "permute"("id")$,
   equal to $"Agen" u$ by $bold(M)$ (unitor/associator isos around the single box). No
   reordering.],
  [*$g compose h$*],
  [$⟪g compose h⟫$ glues $"cod" ⟪h⟫$ to $"dom" ⟪g⟫$ and unions edges; $"decode"$ factors as
   $"decode" ⟪g⟫ compose "decode" ⟪h⟫$ (the stack at the gluing frontier *is*
   $"decode" ⟪h⟫$'s output) — the *$compose$-shape lemma* ($bold(S)$) — then apply the IH.],
  [*$g times.o h$*],
  [$⟪g times.o h⟫$ is the disjoint juxtaposition; $"decode"$ factors as
   $("coerce") compose ("decode" ⟪g⟫ times.o "decode" ⟪h⟫) compose ("coerce")$ after
   interleaving the two edge-streams — the *$times.o$-shape lemma* ($bold(S)$), using
   interchange ($bold(N)$) to separate the blocks — then apply the IH.],
)

#h(1fr) $square.stroked$

= Ledger: what the proof rests on

#table(
  columns: (auto, 1fr, auto),
  inset: 7pt,
  align: (left + horizon, left + horizon, left + horizon),
  stroke: 0.5pt + luma(70%),
  table.header(
    [*Ingredient*], [*Where used*], [*Status*],
  ),
  [$bold(K)$ — generator-free permutation \ coherence (`FaithfulnessResidual`)],
  [(II) wiring match; (I) $sigma$ and accumulated wiring],
  [*the one postulate* \ (Kelly 1964)],

  [$bold(N)$ — interchange axiom \ $sigma compose (p times.o q) approx (q times.o p) compose sigma$],
  [(II) adjacent swap; (I) $times.o$-case],
  [*an `≈Term` axiom* \ — free],

  [$bold(M)$ — monoidal ($alpha, lambda, rho$) \ coherence],
  [(I) base / coercion cases],
  [*constructive* \ (`MonoidalCoherence`)],

  [$bold(S)$ — structural combinatorics: \ Lemma 0, Lemma A (order-iso) *✓*, \ connectivity *✓*, Lemma C (= AllFire) *✓*, \ $compose$/$times.o$-shape, Lemma 0],
  [(I), (II)],
  [*constructive*; \ Lemma A + connectivity \ now formalized (`--safe`); \ Lemma C = `AllFire`],
)

= Consequences for the formalization

#enum(
  [*"Generator interchange" is not extra trust.* It is the interchange axiom $bold(N)$
   (@interchange) applied with opaque box parameters — exactly what
   `swap-atom-aligned` / `decode-Agen-collapse` are really asking, currently buried under
   coercion bookkeeping. The proof never needs a generator-specific coherence.],
  [*$phi$ is genuinely free (Lemma 0).* This soundly justifies the current code's discarding
   of the iso's vertex bijection, and means much of the `IsoInducesEdgePerm` / `StackPerm`
   $phi$-tracking machinery is unnecessary.],
  [*A cleaner architecture for the stuck step.* The replacement for the
   `process-term-permute-aligned` / `stack-↭` apparatus is the explicit structure
   #emph[edge poset $->$ linear extensions $->$ adjacent independent transpositions $->$
   interchange] — a standard, well-understood combinatorial object, much cleaner than the
   current coercion-heavy stack alignment.],
)

In particular the proof *validates Reading A*: `completeness-full` does rest on the single
generator-free axiom $bold(K)$, with $bold(N)$ an existing axiom and $bold(M)$, $bold(S)$
constructive.
