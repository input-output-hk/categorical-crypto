#set document(
  title: "A hypergraph soundness theorem for free symmetric monoidal categories",
  author: "categorical-crypto",
)
#set page(numbering: "1", margin: (x: 2.2cm, y: 2.4cm))
#set par(justify: true, leading: 0.62em)
#set text(size: 10.5pt, font: "New Computer Modern")
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => block(above: 1.2em, below: 0.7em)[#it]
#set math.equation(numbering: "(1)")

#align(center)[
  #text(16pt, weight: "bold")[A hypergraph soundness theorem for \ free symmetric monoidal categories]
  #v(0.25em)
  #text(11pt)[An informal proof]
  #v(0.3em)
  #text(9pt, style: "italic")[`categorical-crypto` — the APROP soundness development]
]

#v(0.6em)

#block(inset: (x: 1.2em), [
  #text(9.5pt)[*Abstract.* We prove the faithfulness (soundness) direction of the
  string-diagram / hypergraph correspondence for the *free symmetric monoidal category*
  (PROP) on a signature: if two terms translate to isomorphic labelled hypergraphs, they are
  equal in the free category. The proof sequentialises a string diagram into a term via a
  *decoder*, and quotients by the order in which independent generator-boxes are processed.
  Its one mathematical kernel is symmetric-monoidal coherence on the permutation fragment
  (Kelly 1964); the bijection-level (`FinBij`) coherence underneath it is treated elsewhere and
  out of scope here.]
])

= Introduction

Morphisms of a free symmetric monoidal category (SMC) on a signature — equivalently, a PROP
— are *string diagrams*: networks of generator-boxes wired together, considered up to the
symmetric-monoidal axioms. Such diagrams are faithfully represented by labelled *hypergraphs*
taken up to isomorphism. The translation $⟪dot.c⟫$ sending a term $f : A -> B$ to its
hypergraph $⟪f⟫$ is a strict symmetric monoidal functor; its *completeness*
($f approx_("Term") g => ⟪f⟫ tilde.equiv^("H") ⟪g⟫$) is routine, and its *faithfulness* —
the soundness theorem
$
  #raw("soundness-full") : quad ⟪f⟫ space tilde.equiv^("H") space ⟪g⟫ quad => quad f approx_("Term") g
$ <main>
— is the subject of this report. Faithfulness is exactly *coherence* for the free SMC:
two terms with the same string diagram are interconvertible by the SMC axioms.

This document gives a *transparent informal proof* of @main, structured so that every step is a
concrete, checkable claim.

*The proof in one line.* Every term equals the canonical *sequentialisation* (decoding) of
its own hypergraph (part #strong[(I)]), and that decoding is invariant under hypergraph
isomorphism (part #strong[(II)]); an isomorphism only *relabels* wires (which the decoder
does not see) and *reorders independent* generator-boxes (which the interchange law absorbs).
The single hard ingredient is the coherence needed to identify two wirings that realise the
same permutation.

*Notation.* We write $approx$ for the free-category term equivalence $approx_("Term")$, and
$tilde.equiv^("H")$ for hypergraph isomorphism ($#raw("≅ᴴ")$ in the source). Throughout,
$bold(K)$, $bold(N)$, $bold(M)$, $bold(S)$ name the four kinds of ingredient catalogued near
the end. Inline monospace names (e.g. `connectivity`) refer to definitions in the Agda
development.

= Objects

The translation $⟪f⟫$ of a term $f : A -> B$ is a finite labelled hypergraph $H$:

- *vertices* $V$ (the wires), labelled $"vlab" : V -> X$ by atoms of the signature;
- *edges* $E$ (the generator-boxes), each $e$ carrying a generator $g_e : "mor" A_e space B_e$
  with ordered input/output wire-lists $"ein" e, "eout" e : "List" V$, subject to
  $ "map" "vlab" ("ein" e) = "flatten" A_e, quad "map" "vlab" ("eout" e) = "flatten" B_e ; $
- an *ordered boundary* $"dom", "cod" : "List" V$ with
  $"map" "vlab" "dom" = "flatten" A$ and $"map" "vlab" "cod" = "flatten" B$.

The translated hypergraph is *monogamous and acyclic*: each wire is produced once and
consumed once (the `Linear` invariant), and the producer/consumer relation among edges is a
strict partial order. These properties hold for every $⟪f⟫$ and are what make the decoder
below total.

== The decoder

The decoder produces a term $"unflatten"("dom") -> "unflatten"("cod")$ by *sequentialising*
the diagram — laying the edges out in a linear order and reading off one box-layer per edge:

$
  "decode" H = underbrace("permute"(pi_("cod")), "final") compose "layer"_(n-1) compose dots.c compose "layer"_0,
$ <decode>

processing the edges in the natural index order $0, dots, n-1$ while threading a *stack* of
currently-live wires (initially $"dom"$). Each layer is

$
  "layer"_e = ("coerce") compose ("Agen" g_e space times.o space "id") compose ("coerce") compose "permute"(pi_e),
$ <layer>

where $pi_e$ is the permutation bringing $"ein" e$ to the front of the current stack (updating
it to $"eout" e space "++" space "rest"$), and $pi_("cod")$ matches the final stack to $"cod"$.
*Every $"permute"(dot.c)$ and every coercion is built solely from $sigma, alpha, lambda, rho,
"id"$ — no generator occurs in them.* Thus $"decode" H$ is a *canonical sequentialisation* of
$H$: a composite of one box-layer per edge, framed by pure wiring.

== Isomorphisms

An isomorphism $Phi = (phi, psi) : H tilde.equiv^("H") J$ is a vertex bijection $phi$ and an
edge bijection $psi$ with
$
  "vlab"_H = "vlab"_J compose phi, quad
  "ein"_J (psi space e) = "map" phi ("ein"_H space e), quad
  "eout"_J (psi space e) = "map" phi ("eout"_H space e), \
  "dom"_J = "map" phi ("dom"_H), quad "cod"_J = "map" phi ("cod"_H),
$
and $g_(psi e) = g_e$ up to the induced label equalities.

= The skeleton of the proof

The soundness theorem @main follows from the chain

$
  f quad underbrace(approx, "(I)") quad "decode" ⟪f⟫ quad underbrace(approx, "(II)") quad "decode" ⟪g⟫ quad underbrace(approx, "(I)") quad g,
$ <skeleton>

which reduces everything to two statements:

#block(inset: (left: 1em))[
  *(I) Normal-form theorem.* #h(0.4em) $f approx "decode" ⟪f⟫$ — every term equals its own
  canonical decoding.

  *(II) Iso-invariance.* #h(0.4em) $⟪f⟫ tilde.equiv^("H") ⟪g⟫ => "decode" ⟪f⟫ approx "decode" ⟪g⟫$.
]

The isomorphism hypothesis is used *only* in (II). We first read the whole proof categorically
(next section), then prove Lemma 0 (the relabelling lemma underpinning (II)), then (II), then (I).

= A categorical reading

One framing makes the proof's *shape* inevitable: the whole theorem is the statement *$"decode"$
is an inverse functor to the translation*; parts (I) and (II) are its two halves, and Lemma 0 is
its naturality in the iso.

*The firing category and the decoder functor.* Read a hypergraph $H$ as a graph on *states*
(sub-collections of its wires): a hyperedge $e$ is an arrow $S -> S'$ removing $"ein" e$ and
adding $"eout" e$, defined when $"ein" e$ is available in $S$ ("fire $e$"). Let $C(H)$ be the
*free category* on this graph; a morphism $"dom" -> "cod"$ is a *complete* firing sequence — a
topological order of the edges, i.e. a choice of *decoding*. By the universal property, the
assignment $L_H : S |-> "unflatten"(S)$, $(e : S -> S') |-> "layer"_e$ extends *uniquely* to a
functor, with $"decode" H = L_H(p)$ for the natural-order maximal path $p$. The soundness
theorem @main is exactly that $L_(dot.c)$ is an inverse to $⟪dot.c⟫ : "FreeSMC" -> "HypProp"$
(morphisms = hypergraphs-with-boundary up to $tilde.equiv^("H")$): soundness is the
*faithfulness* of $⟪dot.c⟫$. The skeleton's two halves are the two halves of "$L_(dot.c)$ is that
inverse" — (I) the round-trip $"decode" compose ⟪dot.c⟫ approx "id"$, (II) well-definedness on
$tilde.equiv^("H")$-classes (a *trace quotient*).

*Lemma 0 is a commuting triangle, reduced to generators.* An iso $(phi, psi)$ is an iso of
firing graphs, so $"Free"(phi, psi) : C(H) space tilde.equiv space C(J)$ *automatically* ("a
functor preserves isomorphisms"). The *content* of Lemma 0 is the step beyond — the decoder
triangle $L_H approx L_J compose "Free"(phi, psi)$ commutes — and since functors out of a free
category agree iff they agree on *generators*, it reduces to the per-edge
$"layer"_e^H approx "layer"_(psi space e)^J$: object part = Lemma 0a, generator part = Lemma 0b.
The edge-list induction is exactly this free extension from generators to paths.

*Where $bold(K)$ comes from.* If states are taken as *unordered* collections, $"unflatten"(S)$
is well-defined only up to the symmetric-coherence isomorphism — and that well-definedness *is*
$bold(K)$. So $bold(K)$ is the price of forgetting wire-order: coherence of the *braiding*, the
only non-formal part of the symmetric monoidal structure that $⟪dot.c⟫$ and $L_(dot.c)$ must
preserve — which is why the single deep ingredient sits there.

= Lemma 0: naturality of the decoder under relabelling

An isomorphism does two things to the data the decoder sees: it *relabels* vertices by $phi$
and *re-indexes* edges by $psi$. Lemma 0 says the decoder *commutes* with this relabelling —
it is natural in the iso. This is the precise form of "the decoder reads only the labels of
wires, not their identities". The naturality holds *on the nose* for the stack the decoder
threads, and *up to $approx$* for the term it produces.

Fix $Phi = (phi, psi)$, so $"vlab"_H = "vlab"_J compose phi$,
$"ein"_J (psi space e) = "map" phi ("ein"_H space e)$, and likewise $"eout", "dom", "cod"$,
with $phi, psi$ bijections. For an edge-list $"es"$ and an initial stack $s$, write
$"stack" H space "es" space s$ and $"term" H space "es" space s$ for the final stack and the
produced HomTerm of the run $"process-edges" H space "es" space s$.

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma 0a (stack naturality — on the nose).* For all $"es", s$,
  $ "stack" J space ("map" psi space "es") space ("map" phi space s)
      quad ≡ quad "map" phi space ("stack" H space "es" space s). $
]

#text(9.5pt)[*Proof.* Induction on $"es"$. The base case is the hypothesis on the initial stack.
For the step: $"extract-prefix"$ branches only on decidable vertex equality, which the bijection
$phi$ preserves, so the J-edge $psi space e$ and the H-edge $e$ make the *same* fire/skip
decision on $"map" phi$-related stacks; then $"ein"_J(psi space e) = "map" phi("ein"_H space e)$
and $"eout"_J(psi space e) = "map" phi("eout"_H space e)$ keep the resulting stacks
$"map" phi$-related. #h(1fr) $square.stroked$]

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma 0b (term naturality — up to $approx$).* For all $"es", s$ — writing $T$ for the boundary
  transport that aligns the two runs' types along Lemma 0a and $"vlab"_H = "vlab"_J compose phi$ —
  $ T space ("term" J space ("map" psi space "es") space ("map" phi space s))
      quad approx quad "term" H space "es" space s, $
  but *not* on the nose. Per layer @layer the reconciliation has irreducible content:
  - the wire-permute factor $"permute"(pi_e)$ — $"extract-prefix"$ returns a $↭$-derivation
    realising the correct wire-bijection but not the syntactic $phi$-image of the H-side's, so
    the two $"permute"$ terms agree only by *$bold(K)$* (at the $"map" "vlab"$ level, repeated
    atom labels block a propositional equality);
  - the box factor $(#raw("Agen") g_e times.o "id")$ framed by the $"unflatten-++-≅"$
    coercions — by *$bold(M)$* (Mac-Lane / monoidal coherence).
]

#text(9.5pt)[*Proof of 0b.* By the free-category extension of §4 it suffices to compare a
*single* layer; the induction threads the stack-invariant of Lemma 0a, keeping the two runs'
stacks $"map" phi$-related. By Lemma 0a the two runs take the *same* fire/skip branch. *Skip:*
both layers are $"id"$. *Fire:* write the layer @layer as
$("coerce") compose (#raw("Agen") g times.o "id") compose ("coerce") compose "permute"(pi)$ and
compare the two factors.
- *Box — by $bold(M)$.* The generator is preserved, $g_(psi e) = g_e$, and the framing
  $"unflatten-++-≅"$ coercions relate the *equal* label-lists
  $"map" "vlab"_J ("ein"_J (psi e)) = "map" "vlab"_H ("ein"_H e)$ — from
  $"vlab"_J compose phi = "vlab"_H$, and likewise $"eout"$ and $"rest"$ — so the two framed
  boxes agree up to those coherence isos.
- *Permute — by $bold(K)$.* The two search-permutations $pi^H : s_H ↭ "ein"_H e "++" "rest"_H$ and
  $pi^J : "map" phi space s_H ↭ "map" phi ("ein"_H e) "++" "rest"_J$ realise the *same*
  wire-bijection: by Lemma 0a the search makes the same positional choices on $phi$-related
  stacks, so $"rest"_J = "map" phi space "rest"_H$ and $pi^J$ is the $phi$-image of $pi^H$ at
  the position level. Hence their *evaluated* bijections coincide ($phi$-equivariance of
  $"eval"$, using $"vlab"_J compose phi = "vlab"_H$), and the two $"permute"$ terms agree by
  @K. Note we route through $"eval"$, not a syntactic identity of the derivations: $bold(K)$
  consumes only the evaluated bijection, which is what sidesteps the $≡$/$approx$ gap.
Composing the two ($compose$-resp-$approx$) gives the layer agreement; the induction lifts it to
all of $"decode"$. #h(1fr) $square.stroked$]

The two lemmas are the *same naturality square* for $"process-edges"$ under $Phi$ — once on
$"stack"$ (holds propositionally, 0a) and once on $"term"$ (holds up to $approx$, 0b). So $phi$
is *genuinely used*, not vacuously discarded: it is free at the stack level, but the term-level
square (0b) invokes $bold(K)$ — which is exactly what makes the use of the isomorphism *sound*.
Lemma 0b bottoms out in the same $bold(K) + bold(M)$ kernel as parts (I) and (II).

#block(inset: (left: 1em), above: 0.6em, below: 0.6em)[
  #text(9.5pt)[*Remark (the relabelling does not collapse $sigma$ and $"id"$).* For
  $sigma, "id" : A times.o A -> A times.o A$, both translate to edge-free graphs with
  $"dom" = [v_0, v_1]$, but $"cod"_("id") = [v_0,v_1]$ while $"cod"_sigma = [v_1, v_0]$; no
  $phi$ matches both, so $⟪sigma⟫$ and $⟪"id"⟫$ are *not* $tilde.equiv^("H")$-related, and the
  final $"permute"(pi_("cod"))$ distinguishes them. The wiring lives in the boundary *order*,
  which $phi$ must respect.]
]

#block(stroke: (left: 1.5pt + luma(50%)), inset: (left: 10pt), above: 0.7em)[
  *Corollary (reduction of (II)).* After the $phi$/$psi$ identification (Lemma 0a),
  $"decode" ⟪f⟫$ and $"decode" ⟪g⟫$ are two runs of the decoder on the *same* $"vlab"$-level
  hypergraph, differing *only* in the order their edges are processed: $"decode" ⟪f⟫$ uses the
  identity order, $"decode" ⟪g⟫$ the order $tau$ that $psi$ induces on $f$'s edges. (The
  residual term-equality of the two runs is Lemma 0b.)
]

= Iso-invariance, part (II)

By the Corollary, (II) reduces to *edge-order independence*: decoding the same hypergraph in
two linear orders yields $approx$-equal terms.

== The dependency order

Define the *dependency relation* $prec_H$ on the edges of $H$ by shared wires:
$
  e prec_H e' quad :<=> quad ("wires of " "eout"_H e) inter ("wires of " "ein"_H e') eq.not emptyset
$
($e$ produces a wire that $e'$ consumes), and likewise $prec_J$ on $J$. To compare the two
decodings we must know the order-difference lives over *one* poset; this is bridged by the
following.

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma A (an isomorphism is a dependency-order isomorphism).* #h(0.3em)
  $e prec_H e' <=> psi space e prec_J psi space e'$.

  #v(0.3em)
  #text(9.5pt)[*Proof.* From $"eout"_J (psi space e) = "map" phi ("eout"_H space e)$ and
  $"ein"_J (psi space e') = "map" phi ("ein"_H space e')$,
  $ ("wires of " "eout"_J (psi space e)) inter ("wires of " "ein"_J (psi space e'))
    = phi("eout"_H space e) inter phi("ein"_H space e')
    = phi(("eout"_H space e) inter ("ein"_H space e')), $
  the last step by injectivity of $phi$. As $phi$ is a bijection, the right side is nonempty
  iff $("eout"_H space e) inter ("ein"_H space e')$ is. $square.stroked$]
]

Pulling $J$'s processing order back through $psi$ to an order $tau$ on $H$'s edges, Lemma A
makes $tau$ a linear extension of $prec_H$ exactly when $J$'s order is a linear extension of
$prec_J$. That the natural orders *are* such linear extensions is *topological validity*:

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Lemma C (topological validity).* #h(0.3em) The natural edge order of $⟪f⟫$ is a linear
  extension of $prec_(⟪f⟫)$; equivalently, processing edges in that order fires every edge
  successfully. (This is *not* automatic for an arbitrary hypergraph, whose $prec$ may have
  cycles; it holds because $⟪f⟫$ comes from a term.)
]

Two supporting facts complete the bridge, both incidence-only rather than coherence content:
*monogamy* (each wire produced once, consumed once — the `Linear` invariant), which makes
$prec$ a strict order and the notion of *independent* (incomparable) edges meaningful; and the
fact that topological validity *transports across the isomorphism* (firing depends only on
incidence, which $phi$/$psi$ preserve — the same propositional, coherence-free flavour as
Lemma 0a).

== The combinatorial core

#block(stroke: 0.5pt + luma(60%), inset: 10pt, radius: 3pt)[
  *Combinatorial fact.* Any two linear extensions of a finite poset are connected by a finite
  sequence of transpositions of *adjacent, incomparable* elements, each step preserving the
  no-inversion property. (Proof: bubble-to-front + well-founded induction on length; requires
  only irreflexivity of $prec$, not transitivity.)
]

Combining: both $H$'s natural order $o_H$ (Lemma C) and the pulled-back order $tau$ (Lemma A +
transport) are linear extensions of the *same* poset $prec_H$, so they are connected by
adjacent-incomparable transpositions. It therefore suffices to show that swapping two
adjacent *independent* edges $e, e'$ changes $"decode"$ only up to $approx$. Locally:

$
  dots.c compose "layer"_(e') compose "layer"_e compose dots.c
  quad "vs." quad
  dots.c compose "layer"_e compose "layer"_(e') compose dots.c .
$

Since $e, e'$ are independent, $"ein" e'$ is disjoint from $"eout" e$ (and conversely): the two
boxes act on disjoint blocks of wires, and both orders reach the same stack-multiset. The two
local composites are equal by the *interchange (symmetry-naturality) axiom*

$
  sigma compose (p times.o q) quad approx quad (q times.o p) compose sigma,
$ <interchange>

at $p = ("Agen" g_e times.o "id")$, $q = ("Agen" g_(e') times.o "id")$ — *parametric in the
boxes, treating them as opaque*. The surrounding wire-permutations differ between the two
orders, but the *total $"dom" -> "cod"$ wiring of the whole composite is the same bijection*
(it is fixed by the hypergraph's incidence; reordering boxes does not move wires). Matching the
two permutation-terms is the generator-free coherence

$
  "eval"(pi) approx_("fb") "eval"(pi') quad => quad "permute"(pi) approx "permute"(pi')
  quad quad (bold(K)).
$ <K>

Chaining over the linear-extension connection yields $"decode" ⟪f⟫ approx "decode" ⟪g⟫$.
#h(1fr) $square.stroked$

#block(inset: (left: 1em), above: 0.5em)[
  #text(9.5pt)[*The analytic crux.* The load-bearing claim is that the per-step permutation
  differences always compose to the *same* evaluated bijection, so that @K applies. This — the
  invariance of the total $"dom" -> "cod"$ wiring under box reordering — is where the genuine
  coherence content of (II) resides; everything around it is combinatorial.]
]

#block(inset: (left: 1em), above: 0.6em)[
  #text(9.5pt)[*Categorically: a trace quotient.* Part (II) says $L_H$ sends the *distinct*
  complete paths of the firing category $C(H)$ to $approx$-equal terms — it *factors through the
  Mazurkiewicz trace quotient* of $C(H)$ by independent-firing commutations. The combinatorial
  fact above is the classical statement that the linear extensions of a pomset form a single
  trace class; the factoring needs $bold(N)$ (firings commute) and $bold(K)$ (wiring).]
]

== The per-swap step in detail

Write $D_(e e')$ for the decoder term of the order "process $e$, then $e'$, then the tail", and
$D_(e' e)$ for the swapped order, both run from the shared post-prefix stack $s_p$; let $r$ be
the *reshuffle* — the permutation between the two orders' post-front stacks. The swap equation is

$
  D_(e' e) quad approx quad "permute"(r) compose D_(e e') .
$ <runeq>

Each fired layer expands (as in @layer) to
$
  "layer"_e = "to"("unflatten-++-≅") compose (#raw("Agen") g_e times.o "id")
              compose "from"("unflatten-++-≅") compose "permute"(pi_e),
$
i.e. *permute $"ein" e$ to the front, re-bracket the stack as
$"unflatten"("ein") times.o "unflatten"("rest")$, apply the box, re-bracket back.* @runeq then
decomposes into exactly one piece per ledger class:

+ *Disjointness ($bold(S)$).* Independence ($e, e'$ incomparable — neither consumes the other's
  output) together with linearity (each wire produced/consumed at most once) gives that
  $"ein" e$, $"ein" e'$ are disjoint, and $"eout" e$ is disjoint from $"ein" e'$ (and
  symmetrically). Hence the two edges occupy *disjoint wire-blocks*, both orders fire, and they
  reach the *same stack-multiset* — the reshuffle $r$.

+ *Box-commute ($bold(N)$).* Brought to disjoint adjacent factors, the two boxes
  $(#raw("Agen") g_e times.o "id")$ and $(#raw("Agen") g_(e') times.o "id")$ act on *disjoint
  tensor factors* and commute by the *bifunctor interchange*
  $(a times.o b) compose (c times.o d) = (a compose c) times.o (b compose d)$ (`⊗-∘-dist`). This
  is the literal "independent firings commute". The braided form @interchange is its conjugate;
  but for disjoint *aligned* blocks plain bifunctoriality suffices — there is *no braiding on the
  boxes themselves* (the braiding lives entirely in the reshuffle, item 4).

+ *Re-bracketing ($bold(M)$).* The two orders thread the stack through *different* intermediate
  shapes (after $e$ fires, $e'$ sees residual $"eout" e ++ dots.c$; after $e'$ fires, $e$ sees
  $"eout" e' ++ dots.c$). To bring both boxes to the common disjoint-aligned form that
  `⊗-∘-dist` needs, the `unflatten-++-≅` coercions must be re-associated — pure Mac-Lane
  coherence ($alpha, lambda, rho$ + coercion naturality). This is the bulk of the work: it has
  no canonical-form solver in the symmetric fragment, so it is chased per positional case.

+ *Reshuffle ($bold(K)$).* The two orders bring the input wires forward in different orders and
  leave the output blocks in swapped positions; the net difference is a pure wire-permutation,
  realised by $"permute"(r)$. Matching it is @K. Plus a tail recursion: the suffix runs on the
  reshuffled stack and commutes with $r$ by naturality.

So @runeq is *$bold(S)$ (disjointness) $+ bold(N)$ (one bifunctor interchange) $+ bold(M)$ (the
re-association bulk) $+ bold(K)$ (the reshuffle)*. The boxes themselves commute by plain
bifunctoriality; the braiding lives entirely in the reshuffle, absorbed by $bold(K)$; and the
genuine bulk is the $bold(M)$ re-bracketing, the solver-unfriendly heart of braided-monoidal
coherence.

= The normal-form theorem, part (I)

By induction on $f$, using the action of $⟪dot.c⟫$ on each constructor:

#table(
  columns: (auto, 1fr),
  stroke: none,
  inset: (x: 4pt, y: 5pt),
  align: (left + top, left + top),
  [*$"id"$, $alpha, lambda, rho$*],
  [translate to edge-free graphs (pure rewiring); $"decode"$ is a single $"permute"$ realising
   the identity/reassociation bijection, equal to the term by monoidal coherence ($bold(M)$).],
  [*$sigma$*],
  [edge-free; $"decode" ⟪sigma⟫$ is $"permute"$ of the swap bijection, equal to $sigma$ by
   $bold(K)$ (a one-transposition instance).],
  [*$"Agen" u$*],
  [one edge; $"decode" ⟪"Agen" u⟫ = ("coerce") compose ("Agen" u times.o "id") compose ("coerce") compose "permute"("id")$,
   equal to $"Agen" u$ by $bold(M)$ (unitor/associator isos around the single box).],
  [*$g compose h$*],
  [$⟪g compose h⟫$ glues $"cod" ⟪h⟫$ to $"dom" ⟪g⟫$ and unions edges; $"decode"$ factors as
   $"decode" ⟪g⟫ compose "decode" ⟪h⟫$ (the stack at the gluing frontier *is*
   $"decode" ⟪h⟫$'s output) — the $compose$-shape lemma ($bold(S)$) — then the IH.],
  [*$g times.o h$*],
  [$⟪g times.o h⟫$ is the disjoint juxtaposition; $"decode"$ factors as
   $("coerce") compose ("decode" ⟪g⟫ times.o "decode" ⟪h⟫) compose ("coerce")$ after
   interleaving the two edge-streams — the $times.o$-shape lemma ($bold(S)$), using interchange
   ($bold(N)$) to separate the blocks — then the IH.],
)

#h(1fr) $square.stroked$

= The ingredients

Every step above draws on one of four kinds of ingredient.

#table(
  columns: (auto, 1fr),
  inset: 7pt,
  align: (left + horizon, left + horizon),
  stroke: 0.5pt + luma(70%),
  table.header([*Ingredient*], [*Where used*]),

  [$bold(K)$ — generator-free permutation coherence (Kelly 1964)],
  [(II) wiring match; (I) $sigma$; Lemma 0b permute factor],

  [$bold(N)$ — interchange axiom $sigma compose (p times.o q) approx (q times.o p) compose sigma$],
  [(II) adjacent swap; (I) $times.o$-case],

  [$bold(M)$ — monoidal ($alpha, lambda, rho$) coherence],
  [(I) base/coercion cases; Lemma 0b box factor],

  [$bold(S)$ — structural combinatorics: Lemma 0a, Lemma A, connectivity, Lemma C, $compose$/$times.o$-shape],
  [(I), (II)],
)

$bold(K)$ is the one deep ingredient: the symmetric-monoidal coherence theorem restricted to the
permutation fragment — two derivations of the same permutation give $approx$-equal $"permute"$
terms. It reduces to coherence at the bijection (`FinBij`) level — $"permute"(pi) approx
"permute"(pi')$ whenever $"eval"(pi) = "eval"(pi')$ — which is treated separately and out of scope
here. $bold(N)$ is one of the SMC equational axioms, applied to opaque boxes; $bold(M)$ and
$bold(S)$ are monoidal coherence and finite combinatorics.

= Conclusion

The soundness theorem @main — the faithfulness of the hypergraph representation of free
symmetric monoidal categories — follows from the round-trip and decoder agreement (part (I)),
the iso-invariance through linear-extension connectivity and the per-swap interchange (part
(II)), and the naturality of the decoder under relabelling (Lemma 0). Each step is one of the
four ingredients $bold(K), bold(N), bold(M), bold(S)$, and the only deep one is the
permutation-coherence kernel $bold(K)$.

$bold(K)$ bottoms out in coherence at the bijection (`FinBij`) level — in effect the word problem
for the symmetric group — which is out of scope for this report. Everything above the bijection
level is covered here in full.
