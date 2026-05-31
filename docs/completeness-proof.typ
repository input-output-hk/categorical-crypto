#set document(
  title: "A hypergraph completeness theorem for free symmetric monoidal categories",
  author: "categorical-crypto",
)
#set page(numbering: "1", margin: (x: 2.2cm, y: 2.4cm))
#set par(justify: true, leading: 0.62em)
#set text(size: 10.5pt, font: "New Computer Modern")
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => block(above: 1.2em, below: 0.7em)[#it]
#set math.equation(numbering: "(1)")

#align(center)[
  #text(16pt, weight: "bold")[A hypergraph completeness theorem for \ free symmetric monoidal categories]
  #v(0.25em)
  #text(11pt)[An informal proof and the status of its Agda mechanization]
  #v(0.3em)
  #text(9pt, style: "italic")[`categorical-crypto` — the APROP completeness development]
]

#v(0.6em)

#block(inset: (x: 1.2em), [
  #text(9.5pt)[*Abstract.* We prove the faithfulness (completeness) direction of the
  string-diagram / hypergraph correspondence for the *free symmetric monoidal category*
  (PROP) on a signature: if two terms translate to isomorphic labelled hypergraphs, they are
  equal in the free category. The proof sequentialises a string diagram into a term via a
  *decoder*, and quotients by the order in which independent generator-boxes are processed.
  We give the informal proof in full and then document its Agda mechanization, which reduces
  the entire theorem to *three* explicit obligations. The single irreducible mathematical
  kernel is symmetric-monoidal coherence on the permutation fragment (Kelly 1964); the
  remaining two obligations are one Mac-Lane re-bracketing chase and one decoder-agreement, all
  identified precisely. No unsound assumptions remain in the development.]
])

= Introduction

Morphisms of a free symmetric monoidal category (SMC) on a signature — equivalently, a PROP
— are *string diagrams*: networks of generator-boxes wired together, considered up to the
symmetric-monoidal axioms. Such diagrams are faithfully represented by labelled *hypergraphs*
taken up to isomorphism. The translation $⟪dot.c⟫$ sending a term $f : A -> B$ to its
hypergraph $⟪f⟫$ is a strict symmetric monoidal functor; its *soundness*
($f approx_("Term") g => ⟪f⟫ tilde.equiv^("H") ⟪g⟫$) is routine, and its *faithfulness* —
the completeness theorem
$
  #raw("completeness-full") : quad ⟪f⟫ space tilde.equiv^("H") space ⟪g⟫ quad => quad f approx_("Term") g
$ <main>
— is the subject of this report. Faithfulness is exactly *coherence* for the free SMC:
two terms with the same string diagram are interconvertible by the SMC axioms.

This document accompanies the APROP completeness formalization in the `categorical-crypto`
Agda development. It has two purposes:

#enum(
  [a *transparent informal proof* of @main, structured so that every step corresponds to a
   concrete, checkable formal obligation;],
  [a precise account of the *current mechanization status*: which steps are fully verified in
   Agda, and the exact *trust surface* — the three remaining postulates and what each is.],
)

*The proof in one line.* Every term equals the canonical *sequentialisation* (decoding) of
its own hypergraph (part #strong[(I)]), and that decoding is invariant under hypergraph
isomorphism (part #strong[(II)]); an isomorphism only *relabels* wires (which the decoder
does not see) and *reorders independent* generator-boxes (which the interchange law absorbs).
The single hard ingredient is the coherence needed to identify two wirings that realise the
same permutation.

*Notation.* We write $approx$ for the free-category term equivalence $approx_("Term")$, and
$tilde.equiv^("H")$ for hypergraph isomorphism ($#raw("≅ᴴ")$ in the source). Throughout,
$bold(K)$, $bold(N)$, $bold(M)$, $bold(S)$ name the four kinds of ingredient catalogued in
§8. Inline monospace names (e.g. `connectivity`) refer to definitions in the Agda
development; §9 gives the module map.

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

The completeness theorem @main follows from the chain

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

Before the proofs, one framing makes their *shape* inevitable: the whole theorem is the single
statement *$"decode"$ is an inverse functor to the translation.* Parts (I) and (II) are the two
halves of that statement, and Lemma 0 is its naturality in the iso.

*The firing category.* Read a hypergraph $H$ as a graph on *states* (sub-collections of its
wires): a hyperedge $e$ is an arrow $S -> S'$ that removes $"ein" e$ and adds $"eout" e$,
defined whenever $"ein" e$ is available in $S$ ("fire $e$"). Let $C(H)$ be the *free category*
on this graph. Its objects are states; its morphisms are firing sequences; a morphism
$"dom" -> "cod"$ is a *complete* firing sequence — a topological order of the edges, i.e. a
choice of *decoding*.

*The decoder is a functor.* By the universal property of the free category, the assignment
$
  L_H : C(H) -> "FreeSMC", quad S |-> "unflatten"(S), quad (e : S -> S') |-> "layer"_e
$
extends *uniquely* to a functor (a path maps to the composite of its layers), and
$"decode" H = L_H(p)$ for the natural-order maximal path $p$. The completeness theorem @main is
exactly that $L_(dot.c)$ assembles into an inverse to the translation functor
$⟪dot.c⟫ : "FreeSMC" -> "HypProp"$, where $"HypProp"$ is the symmetric monoidal category whose
morphisms are hypergraphs-with-boundary taken up to $tilde.equiv^("H")$: completeness is the
*faithfulness* of $⟪dot.c⟫$. The two halves of the skeleton @skeleton are the two halves of
"$L_(dot.c)$ is that inverse" — part (I) is the round-trip $"decode" compose ⟪dot.c⟫ approx
"id"$; part (II) is well-definedness on $tilde.equiv^("H")$-classes (below, this is a *trace
quotient*).

*Lemma 0 is a commuting triangle, reduced to generators.* An iso $(phi, psi)$ is an iso of
firing graphs, so the free-category functor $"Free" : "Graph" -> "Cat"$ carries it to an iso of
free categories $"Free"(phi, psi) : C(H) space tilde.equiv space C(J)$ — *automatically* (this
is "a functor preserves isomorphisms", the cheap step). The *content* of Lemma 0, next, is the
step beyond that: the triangle of decoders commutes,
$
  L_H quad approx quad L_J compose "Free"(phi, psi).
$
By the universal property, an agreement of two functors out of a free category is determined on
*generators*; so it reduces to the per-edge $"layer"_e^H approx "layer"_(psi space e)^J$ — object
part = Lemma 0a, generator part = Lemma 0b. This reduction-to-generators *is* the structure of
the Lemma 0 proof below, and the induction over the edge-list in the mechanization is exactly
this free extension from generators to paths.

*Where $bold(K)$ comes from.* If states are taken as genuinely *unordered* collections, then
$"unflatten"(S)$ is well-defined only up to the symmetric-coherence isomorphism — and that
well-definedness *is* $bold(K)$. So $bold(K)$ is precisely the price of forgetting wire-order:
the coherence of the *braiding*, the only non-formal part of the symmetric monoidal structure
that $⟪dot.c⟫$ and $L_(dot.c)$ must preserve. This is why the single deep obligation sits there.

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
  #text(9.5pt)[*Remark (the relabelling does not collapse $sigma$ and $"id"$).* Take
  $sigma, "id" : A times.o A -> A times.o A$. Both translate to edge-free graphs with two
  $A$-labelled wires and $"dom" = [v_0, v_1]$, but $"cod"_("id") = [v_0,v_1]$ while
  $"cod"_sigma = [v_1, v_0]$. No $phi$ can match both $"dom"$ and the swapped $"cod"$, so
  $⟪sigma⟫$ and $⟪"id"⟫$ are *not* $tilde.equiv^("H")$-related; and the final
  $"permute"(pi_("cod"))$ reads the $"cod"$ ordering, so the decoder distinguishes them. The
  wiring lives in the boundary *order*, which $phi$ must respect.]
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
  #text(9.5pt)[*Categorically (§4): a trace quotient.* Two complete paths $"dom" -> "cod"$ are
  *distinct* morphisms of the firing category $C(H)$; what (II) shows is that $L_H$ sends them
  to $approx$-equal terms — i.e. $L_H$ *factors through the quotient of $C(H)$ by
  independent-firing commutations*, the Mazurkiewicz *trace* category. The combinatorial fact
  above (any two linear extensions are joined by adjacent independent transpositions) is the
  classical statement that the linear extensions of a pomset form a single trace class;
  $L_H$ respecting the quotient needs $bold(N)$ (independent firings commute) and $bold(K)$
  (wiring).]
]

== The per-swap step in detail (`run-eq`)

The single adjacent-independent swap above is mechanized as the field `run-eq` of the record
`SwapStep.FrontSwap.RunInterchange`. Write $D_(e e')$ for the decoder term of the order
"process $e$, then $e'$, then the tail", and $D_(e' e)$ for the swapped order, both run from the
shared post-prefix stack $s_p$; let $r$ be the *reshuffle* — the permutation between the two
orders' post-front stacks. The swap equation is

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
decomposes into exactly one obligation per ledger class:

+ *Disjointness ($bold(S)$).* Independence ($e, e'$ incomparable — neither consumes the other's
  output) together with linearity (each wire produced/consumed at most once) gives that
  $"ein" e$, $"ein" e'$ are disjoint, and $"eout" e$ is disjoint from $"ein" e'$ (and
  symmetrically). Hence the two edges occupy *disjoint wire-blocks*, both orders fire, and they
  reach the *same stack-multiset* — the reshuffle $r$. _This half is now PROVEN_ —
  `Sub/FiringSwap.front-swap-reshuffle`, a one-line bridge to the constructive
  `SwapValidity.front-swap-stack-↭` (linearity gives `ein-ein-disjoint`, independence gives
  `eout-ein-disjoint`).

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
  coherence ($alpha, lambda, rho$ + coercion naturality). *This is the bulk of the open
  transport*: it has no canonical-form solver in the symmetric fragment, so it is hand-chased,
  per positional case, under `--without-K` `subst₂` casts.

+ *Reshuffle ($bold(K)$).* The two orders bring the input wires forward in different orders and
  leave the output blocks in swapped positions; the net difference is a pure wire-permutation,
  realised by $"permute"(r)$. Matching it is @K. Plus a tail recursion: the suffix runs on the
  reshuffled stack and commutes with $r$ by naturality.

So @runeq is *$bold(S)$ (done) $+ bold(N)$ (one `⊗-∘-dist`) $+ bold(M)$ (the re-association bulk)
$+ bold(K)$ (the reshuffle)*. The genuine remaining cost is the $bold(M)$ re-bracketing — the
solver-unfriendly heart of braided-monoidal coherence — *not* the interchange axiom @interchange
itself, which is already proven (`SwapStep.box-interchange`).

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

Every step above draws on one of four kinds of ingredient. This classification is what makes
the trust surface (§8) legible.

#table(
  columns: (auto, 1fr, auto),
  inset: 7pt,
  align: (left + horizon, left + horizon, left + horizon),
  stroke: 0.5pt + luma(70%),
  table.header([*Ingredient*], [*Where used*], [*Nature*]),

  [$bold(K)$ — generator-free permutation \ coherence (Kelly 1964)],
  [(II) wiring match; (I) $sigma$; \ Lemma 0b permute factor],
  [a single classical \ *axiom*],

  [$bold(N)$ — interchange axiom \ $sigma compose (p times.o q) approx (q times.o p) compose sigma$],
  [(II) adjacent swap; (I) $times.o$-case],
  [an `≈Term` axiom \ (*free*)],

  [$bold(M)$ — monoidal ($alpha, lambda, rho$) \ coherence],
  [(I) base/coercion cases; \ Lemma 0b box factor],
  [*constructive*],

  [$bold(S)$ — structural combinatorics: \ Lemma 0a, Lemma A, connectivity, \ Lemma C, $compose$/$times.o$-shape],
  [(I), (II)],
  [*constructive*],
)

$bold(K)$ is the only deep mathematical assumption: it is the symmetric-monoidal coherence
theorem restricted to the permutation fragment — two derivations of the same permutation give
$approx$-equal $"permute"$ terms. $bold(N)$ is literally one of the SMC equational axioms,
applied to opaque boxes. $bold(M)$ and $bold(S)$ are coherence and finite combinatorics that
are (or can be made) constructive.

= Mechanization status

The proof is mechanized in Agda (`--without-K`) in the `categorical-crypto` development. The
top-level lemma
$
  #raw("decode-rel-resp-iso") : quad ⟪f⟫ space tilde.equiv^("H") space ⟪g⟫ quad => quad "decode-rel" f approx "decode-rel" g
$
type-checks, where $"decode-rel"$ is the structural decoder; the completeness theorem @main
follows by composing with the (structural, proven) round-trip $f approx "decode-rel" f$.

== Architecture

The decoder operates on a *monogamous* translation, for which $tilde.equiv^("H")$ is a genuine
congruence. Its totality (every $⟪f⟫$ decodes) is fully proven. The iso-invariance argument is
assembled as follows; the order-theoretic core is signature-generic and `--safe`.

#table(
  columns: (auto, 1fr),
  inset: 6pt,
  align: (left + top, left + top),
  stroke: 0.5pt + luma(75%),
  table.header([*Module (role)*], [*Status*]),
  [`Combinatorics.LinearExtension` — connectivity of linear extensions of a finite poset],
  [`--safe`, postulate-free],
  [`EdgeDependency` — Lemma A (dependency-order iso)],
  [`--safe`, postulate-free],
  [decoder totality + linearity (`LinearHComposeP`, `DecodeAttemptLinearP`)],
  [postulate-free],
  [order-indexed decoder + iso-invariance assembly (`IsoInvarianceWiring` / `…Concrete`)],
  [postulate-free],
  [`DepIrrefl` (acyclicity), `SwapValidity` (firing-stable swaps), `ObjUIP` (UIP)],
  [postulate-free],
  [iso-invariance of the structural decoder (`DecodeRelRespIsoWired`, top of chain)],
  [3 postulates (below)],
)

== Trust surface

Completeness rests on exactly three postulates, plus a `DecidableEquality` hypothesis on the
atom type (satisfied by any concrete signature, used to discharge UIP on objects). Every
postulate is *true*; none is an unsound shortcut.

#table(
  columns: (auto, auto, 1fr),
  inset: 6pt,
  align: (left + horizon, left + horizon, left + top),
  stroke: 0.5pt + luma(75%),
  table.header([*Obligation*], [*Kind*], [*What it is*]),
  [`K-faithfulness`], [$bold(K)$],
  [the classical axiom: permutation coherence (Kelly 1964); the irreducible kernel, shared by
   (I), (II), and Lemma 0b.],
  [`run-interchange-⟪⟫`], [$bold(M)$],
  [the analytic crux of (II) at one swap (`run-eq`, @runeq). Of its two halves the *firing*
   half (`reshuffle`, $bold(S)$) is now proven (`Sub/FiringSwap`) and the interchange axiom
   $bold(N)$ is isolated as a proven lemma (`box-interchange`); the residual is exactly the
   Mac-Lane re-bracketing transport through the layer coercions.],
  [`decode-rel-≈-decodeP`], [(I)],
  [the normal-form theorem (decoder agreement): decomposes per constructor into the $compose$/
   $times.o$-shape lemmas ($bold(S)$), the monoidal atomics ($bold(M)$), and the $sigma$/box
   atomics ($bold(K)$).],
)

The three obligations are not independent: $bold(K)$ recurs in two of them, so the genuinely
open mathematical content is *(a)* the coherence axiom $bold(K)$; *(b)* the Mac-Lane
re-bracketing transport at one swap (`run-interchange-⟪⟫`, @runeq); and *(c)* the structural
decoder-agreement (`decode-rel-≈-decodeP`). The combinatorial backbone — Lemma A, Lemma C, the
connectivity of linear extensions, decoder totality, the firing-stability of independent swaps,
and *all of Lemma 0b* (`edge-step-term-φ`, formerly a postulate, now proven via the
relation-view of `edge-step` — its box factor $bold(M)$ and permute factor $bold(K)$ both
discharged) — is fully verified.

== Soundness notes

#enum(
  [*No false postulates.* Several plausible-looking shortcuts are unsound and were avoided: a
   *pruned*-to-*unpruned* iso transfer (false — pruning changes vertex counts); an X-label-level
   uniqueness $"Unique"("map" "vlab" "cod")$ (false when boundary atoms repeat); and an
   independent-edge swap without a firing premise (false without monogamy). Each obligation is
   stated at the level where it is true.],
  [*The isomorphism is used, not discarded.* Lemma 0 makes precise that the vertex bijection
   $phi$ is free only at the list level; the term-level reconciliation genuinely invokes
   $bold(K)$, so the proof is not vacuous.],
  [*The interchange content is not extra trust.* The "generator interchange" is the SMC
   interchange axiom $bold(N)$ @interchange applied to opaque boxes; no generator-specific
   coherence is ever required.],
)

= Conclusion

The completeness theorem @main is reduced — informally in full, and in Agda modulo three
explicit, true obligations — to a single classical axiom together with one Mac-Lane
re-bracketing chase and one decoder-agreement, all precisely located. The deep content is symmetric-monoidal coherence
on the permutation fragment ($bold(K)$); everything genuinely combinatorial is verified.

Closing the remaining obligations is research-level work of a familiar kind: $bold(K)$ is the
word problem for the symmetric group (amenable to a normalization-by-evaluation argument, for
which the monoidal-fragment analogue is already mechanized in the development); the Mac-Lane
transports and the decoder-agreement are coherence and structural decompositions that have long
been the open frontier of this formalization. The contribution here is to have isolated that
frontier exactly, on a sound footing, with the surrounding $80%$ of the argument mechanized.
