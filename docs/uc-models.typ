// Standalone: typst compile docs/uc-models.typ   (needs the `fletcher` package; offline:
// nix shell --impure --expr 'let pkgs = (builtins.getFlake "nixpkgs").legacyPackages.${builtins.currentSystem};
//   in pkgs.typst.withPackages (p: [ p.fletcher_0_5_8 ])' --command typst compile docs/uc-models.typ)
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

#set document(title: "The UC models of categorical-crypto: setups, morphisms, theorems")
#set page(numbering: "1", margin: (x: 2.1cm, y: 2.2cm))
#set text(size: 10pt, lang: "en")
#set par(justify: true)
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => { v(0.6em); it; v(0.2em) }
#show link: set text(fill: rgb("#1d4f91"))
#show raw.where(block: false): set text(size: 8.6pt)

// ---------------------------------------------------------------------------
// Source links: every link points at the defining line on branch uc-setup-landscape.
#let repo = "https://github.com/input-output-hk/categorical-crypto/blob/uc-setup-landscape/src/"
#let ag(path, line, name) = link(repo + path + "#L" + str(line), raw(name))
#let cc(path, line, name) = ag("CategoricalCrypto/" + path, line, name)
#let srcs(..xs) = text(size: 8.3pt, fill: luma(28%))[(Agda: #xs.pos().join([, ]))]
// Design documents (not type-checked), on the same branch.
#let plan(name) = link("https://github.com/input-output-hk/categorical-crypto/blob/uc-setup-landscape/docs/" + name, raw(name))

// Status tags
#let tag(c, s) = box(fill: c, inset: (x: 2.5pt), outset: (y: 2pt), radius: 2pt, text(size: 7.3pt, weight: "bold", s))
#let design = tag(rgb("#fbe1bd"), "DESIGN")
#let formal = tag(rgb("#cfe9cf"), "FORMAL")
#let instance = tag(rgb("#dbe4f5"), "INSTANCE")

// Theorem-like environments, numbered in one sequence
#show figure.where(kind: "thm"): it => block(width: 100%, breakable: true, above: 1.05em, below: 1.05em, {
  set align(left)
  set par(justify: true)
  strong[#it.supplement #it.counter.display(it.numbering)]
  if it.caption != none [ (#it.caption.body)]
  [. ]
  it.body
})
#let thmkind(s) = (name: none, body) => figure(kind: "thm", supplement: s, numbering: "1",
  outlined: false, caption: name, body)
#let definition = thmkind([Definition])
#let theorem = thmkind([Theorem])
#let proposition = thmkind([Proposition])
#let corollary = thmkind([Corollary])
#let lemma = thmkind([Lemma])
#let remark = thmkind([Remark])
#let proofidea(body) = block(above: 0.5em, below: 0.9em, text(size: 9.4pt)[_Proof idea._ #body])

// Names of setups (fixed throughout)
#let PM = $sans("PM")$
#let RS = $sans("RS")$
#let PMwb = $sans("PM")[sans("wb")]$
#let Wsub = $cal(W)$
#let Wio = $cal(W)[iota^* cal(E)^o]$
#let WW = $cal(W)[cal(E)^W]$
#let SSP = $sans("SSP")$
#let SSPd = $sans("SSP")^sans("d")$
#let ITM = $sans("ITM")$
#let ITMiso = $sans("ITM")_≅$
#let Iso = $sans("Iso")$
#let Rel = $sans("Rel")$
#let PMom = $sans("PM")^omega$
#let PMN = $sans("PM")^sans("N")$
#let QPM = $sans("QPM")$
#let QRS = $sans("QRS")$
#let IPDL = $sans("IPDL")$
#let CB = $sans("CB")$
#let Sym = $sans("Sym")$
#let Symiso = $sans("Sym")_≅$
#let Symcert = $sans("Sym")_≅^sans("c")$
#let NDA = $sans("ND")_sans("A")$
#let NDB = $sans("ND")_sans("B")$
#let Std = $sans("Std")$

// Names of morphisms
#let mrs = $sans("rs")$
#let mitm = $sans("itm")$
#let mitmiso = $sans("itm")_≅$
#let mq = $sans("q")$
#let mwb = $sans("wb")$
#let mdet = $sans("det")$
#let mcoarse = $sans("coarse")$
#let msym = $sans("sym")_≅$
#let mcs = $sans("cs")$
#let mck = $sans("ck")$
#let mincl = $sans("incl")$
#let mres = $sans("res")$
#let mgr = $sans("gr")$
#let mcomp = $sans("comp")$
#let miota = $iota$

// Relations and operators
#let eqE = $scripts(≈)_cal(E)$
#let eqU = $scripts(≈)^upright(U)$
#let apx = $scripts(≈)$
#let leUC = $scripts(≤)_"UC"$
#let eqR = $scripts(≈)_sans("R")$
#let eqB = $scripts(≈)_sans("B")$
#let eqM = $scripts(≈)_sans("M")$
#let eqP = $scripts(≈)_sans("p")$
#let isoM = $scripts(≅)_sans("M")$
#let simW = $scripts(∼)_cal(W)$
#let simA = $scripts(∼)^sans("a")$
#let opsub = $op("sub")$
#let opext = $op("ext")$
#let oprun = $op("run")$
#let opid = $op("id")$
#let Obs = $op("Obs")$
#let Dp = $D_p$

// ---------------------------------------------------------------------------

#align(center)[
  #text(size: 17pt, weight: "bold")[The UC models of `categorical-crypto`]
  #v(1pt)
  #text(size: 12.5pt)[Setups, the morphisms between them, and the major theorems]
  #v(3pt)
  Branch `uc-setup-landscape`, 12 October 2026
]

#v(6pt)

This note is a self-contained mathematical account of the models of universally composable (UC)
security — _setups_ — that the library formalises, of the structure-preserving maps between them,
and of the theorems proved about them. It is written for a reader who knows category theory and
cryptography and does not read Agda: it says nothing about how the formalisation is organised.

*Names and links.* Every setup, setup morphism and major theorem has one mathematical name, fixed in
@sec:table and @sec:morphisms and used throughout. Every formal statement ends with a list
#srcs([links]) to the Agda identifiers that define or prove it on branch `uc-setup-landscape`; the
link text is the identifier, the target its defining line.

*Status.* #formal marks definitions and proofs integrated and checked in the tree; it does not
certify correspondence to a stronger native security theory. #design marks an unformalised design,
proposal or source-derived argument; it is not an impossibility theorem about every possible
interpretation. #instance marks an instantiation of a proved general theorem at proved hypotheses.
A statement with neither tag nor link is notation made for this exposition. The dated dispositions
of #plan("uc-setup-adversarial-review.md") distinguish historical findings from their current status.

*Refresh boundary.* This account includes the checked W comparisons, distributional SSP clients,
availability API, positive-error QRS example, PM-choice initialization repair, symbolic theory/static
and certified layers, pure-interface simulation, opt-in terminal runtime, protocol-indexed errors
and initialized probabilistic ITM security/observation clients. The integrated proof boundary is
`63d03981` (ITM clients: `90911024`; preceding boundary: `ec1b6a17`; terminal: `b606503c`,
`41f603b9`; purity: `84b408c8`; original five-item integration: `cf6653e6`).
Initialized _relational_-ITM execution and an interactive symbolic transmission/decryption
construction remain ongoing isolated work, not results claimed here. The proposed island
connections in @sec:designed are research obligations, not newly checked edges.

#{
  set text(size: 8.7pt)
  set par(leading: 0.45em)
  outline(depth: 2, indent: auto)
}

#pagebreak()

= The abstract framework <sec:framework>

== UC setups

#definition(name: [UC setup])[
A _UC setup_ $𝕊 = (cal(C), cal(I), cal(M), cal(E))$ consists of a category $cal(C)$ of computations;
a monoidal category $(cal(I), ⊗, I)$ of interfaces, used as _grades_; an $cal(I)$-graded monad
$cal(M)$ on $cal(C)$, that is, a lax monoidal functor $cal(M) : cal(I) → ([cal(C), cal(C)], ∘, "Id")$;
and a presheaf of setoids $cal(E) : cal(C)^"op" → sans("Setoid")$, the _tests_.
#srcs(cc("UCSetup.agda", 21, "UCSetup"))
] <def:setup>

We write $T_X := cal(M)(X)$, $η : "Id" ⇒ T_I$ and $μ_(X,Y) : T_X T_Y ⇒ T_(X ⊗ Y)$ for the lax structure,
and $opsub_c := cal(M)(c) : T_X ⇒ T_(X')$ for $c : X → X'$ in $cal(I)$. The Kleisli extension of
$h : B → T_Y C$ at grade $X$ is $opext_X h := μ_(X,Y) ∘ T_X h$, and for $f : A → T_X B$ the _serial
composite_ is $h ∙ f := opext_X h ∘ f : A → T_(X ⊗ Y) C$ #srcs(cc("UCSetup.agda", 56, "_∙_")). Graded
monads are those of @fujii2016.

The cryptographic reading is fixed once and for all.

- A _protocol_ (or functionality) from $A$ to $B$ with _adversary interface_ $X$ is a morphism
  $f : A → T_X B$ of $cal(C)$.
- An _adversary_ is a morphism $a : X → X'$ of $cal(I)$; it attacks $f$ by regrading, $opsub_a ∘ f$.
  A _simulator_ is the same kind of object, acting on the ideal protocol.
- A _test_ on $A$ is an element $e ∈ cal(E)(A)$; a morphism $h : A' → A$ acts on tests by restriction,
  $e · h := cal(E)(h)(e)$.
- For $W ∈ cal(I)$ (an _ancilla_), the _prefix context_ of $f$ is
  $μ_(W,X) ∘ T_W f : T_W A → T_(W ⊗ X) B$, and $oprun_W (f)(e) := e · (μ_(W,X) ∘ T_W f)$ runs $f$
  inside the environment $e ∈ cal(E)(T_(W ⊗ X) B)$ #srcs(cc("UCSetup.agda", 123, "prefix"), cc("UCSetup.agda", 126, "run")).

== Two equivalences

#definition(name: [observational kernel])[
For parallel $f, g : A → B$ in $cal(C)$, $f eqE g$ iff $cal(E)(f) = cal(E)(g)$, i.e. $e · f ≈ e · g$ in
$cal(E)(A)$ for every $e ∈ cal(E)(B)$. It is the kernel congruence of the functor $cal(E)$, hence a
congruence on $cal(C)$ containing its hom-equality.
#srcs(ag("Categories/KernelCongruence.agda", 26, "_∼_"))
] <def:kernel>

#definition(name: [U-kernel])[
For $f, g : A → T_X B$, $f eqU g$ iff $μ_(W,X) ∘ T_W f eqE μ_(W,X) ∘ T_W g$ for every $W ∈ cal(I)$:
the two protocols agree in every environment at every ancilla.
#srcs(cc("Abstract2.agda", 45, "_≈ᵁ_"))
] <def:U>

The name: $eqU$ is the kernel of the enriched forgetful functor that sends a graded morphism to the
family of its prefix contexts; the underlying locally graded structure is that of McDermott and
Uustalu (MPC 2022).

#proposition(name: [congruence])[
$eqU$ is an equivalence relation that contains the hom-equality and is contained in $eqE$. It is a
congruence for regrading ($f eqU f' ⇒ opsub_c ∘ f eqU opsub_c ∘ f'$), for Kleisli extension
($f eqU f' ⇒ opext_X h ∘ f eqU opext_X h ∘ f'$) and for serial composition in the other argument
($h eqU h' ⇒ h ∙ f eqU h' ∙ f$).
#srcs(cc("Abstract2.agda", 63, "≈C⇒≈ᵁ"), cc("Abstract2.agda", 117, "≈ᵁ⇒≈ℰ"), cc("Abstract2.agda", 66, "sub-cong"), cc("Abstract2.agda", 71, "ext-cong"), cc("Abstract2.agda", 77, "∙-cong-arg"))
] <prop:U-congruence>

#definition(name: [grade stability])[
$𝕊$ is _grade-stable_ if every $T_Y$ respects $eqE$: $h eqE h' ⇒ T_Y h eqE T_Y h'$. Equivalently, the
kernel of $cal(E)$ is a congruence of $cal(M)$-modules.
#srcs(cc("UCSetup.agda", 146, "GradeStable"))
] <def:gs>

#proposition(name: [bridges from $eqE$ to $eqU$])[
(i) In a grade-stable setup, $f eqE g ⇒ f eqU g$ for graded $f, g$; with @prop:U-congruence the two
relations then coincide on graded morphisms. (ii) If $cal(E)$ is faithful, $𝕊$ is grade-stable.
(iii) If the kernel is generated by a conjugation-closed relation that is detected at every $T_V$, and
every $μ_(X,Y)$ has a retraction, $𝕊$ is grade-stable.
#srcs(cc("Abstract2.agda", 124, "bridge"), cc("UCSetup.agda", 150, "faithful⇒grade-stable"), cc("UCSetup.agda", 155, "GradeStableFromTests"))
] <prop:bridge>

Grade stability is used by nothing in the metatheory of @sec:metatheory. It matters only when a fact
proved at the bare kernel $eqE$ has to be imported into $eqU$, and when a morphism is asked to carry
emulation (@thm:transport). The main model of the library is _not_ grade-stable
(@prop:not-gs), which shapes much of what follows.

== Emulation and the metatheory <sec:metatheory>

#definition(name: [emulation])[
For $f : A → T_X B$ and $g : A → T_Y B$, $f leUC g$ iff for every adversary $a : X → X'$ there is a
simulator $s : Y → X'$ with $opsub_a ∘ f eqU opsub_s ∘ g$.
#srcs(cc("Abstract2.agda", 131, "_≤UC_"))
] <def:leUC>

#theorem(name: [UC metatheory])[
In every UC setup, with no hypotheses:
+ $leUC$ is a preorder, invariant under the hom-equality, and $f eqU g ⇒ f leUC g$.
+ _Dummy-adversary completeness._ $f leUC g$ iff there is $s_0 : Y → X$ with $f eqU opsub_(s_0) ∘ g$; the
  simulator for an adversary $a$ is then $a ∘ s_0$.
+ _Composition._ If $f leUC g$ and $h leUC k$ then $h ∙ f leUC k ∙ g$. With $s$, $t$ the dummy
  simulators of the two hypotheses, the simulator for $a$ is $a ∘ (opid ⊗ t) ∘ (s ⊗ opid)$.
+ Regrading along a split monomorphism $c$ of $cal(I)$ preserves $leUC$.
#srcs(cc("Abstract2.agda", 139, "≤UC-refl"), cc("Abstract2.agda", 142, "≤UC-trans"), cc("Abstract2.agda", 149, "≤UC-resp-≈"), cc("Abstract2.agda", 163, "≈ᵁ⇒≤UC"), cc("Abstract2.agda", 156, "dummy-complete"), cc("Abstract2.agda", 166, "≤UC⇒dummy"), cc("Abstract2.agda", 171, "≤UCᵈ⇔≤UC"), cc("Abstract2.agda", 174, "UC-compose"), cc("Abstract2.agda", 223, "≤UC-sub"))
] <thm:metatheory>

#proofidea[(2) is the heart. Given $s_0$, the congruence of $eqU$ under $opsub_a$ and functoriality of
$cal(M)$ give $opsub_a f eqU opsub_a opsub_(s_0) g = opsub_(a s_0) g$; conversely take $a = opid$.
(3) chains the congruences of @prop:U-congruence with the naturality of $opsub$ against $opext$.]

These four statements are the UC metatheorems of the literature (@canetti2001; @canetti2020uc): every
setup below inherits them, with the same proofs, because they are stated over $eqU$ rather than
over $eqE$.

== Morphisms of setups <sec:setup-morphisms>

#definition(name: [setup morphism])[
A morphism $𝕄 = (F, Φ, κ, ν) : 𝕊 → 𝕊'$ consists of
- a functor $F : cal(C) → cal(C)'$;
- a lax monoidal functor $Φ : cal(I) → cal(I)'$, with structure maps $Φ_ε : I' → Φ I$ and
  $Φ_(X,Y) : Φ X ⊗ Φ Y → Φ(X ⊗ Y)$;
- components $κ_(X,A) : F(T_X A) → T'_(Φ X)(F A)$ satisfying
  $ κ ∘ F η_A = opsub'_(Φ_ε) ∘ η'_(F A), quad
    κ ∘ F(opext_X f) = opsub'_(Φ_(X,Y)) ∘ opext'_(Φ X)(κ ∘ F f) ∘ κ, quad
    κ ∘ F(opsub_c) = opsub'_(Φ c) ∘ κ ; $
- a natural transformation $ν : cal(E) ⇒ cal(E)' ∘ F^"op"$: a test on $A$ becomes a test on $F A$.
The _action on protocols_ is $G(f) := κ ∘ F f : F A → T'_(Φ X)(F B)$. $ν$ is _Epi_ if every component
$ν_A$ is surjective, _Mono_ if every component is injective (as maps of setoids).
#srcs(cc("UCSetup/Morphism.agda", 31, "UCSetupMorphism"), ag("Categories/Monad/Graded/Morphism.agda", 58, "GradedKleisliMorphism"), ag("Categories/Monad/Graded/Morphism.agda", 47, "IsGradedKleisliMorphism"), ag("Categories/Functor/Presheaf/Morphism.agda", 32, "PresheafMorphism"), cc("Abstract2/Morphism.agda", 35, "G"), ag("Categories/Functor/Presheaf/Morphism.agda", 47, "Epi"), ag("Categories/Functor/Presheaf/Morphism.agda", 50, "Mono"))
] <def:morphism>

The three $κ$-laws say that $(F, κ)$ is a morphism of graded Kleisli triples along the change of
grading $Φ$: $κ$ is a 2-cell between the two ways around the square $cal(I) × cal(C) → cal(C)'$,
compatible with unit and multiplication. The general constructions are all formal:

- _identities and composites_ $opid_𝕊$ and $𝕄' ∘ 𝕄$ (with test map $ν'_F ∘ ν$); the unit laws hold
  componentwise #srcs(cc("UCSetup/Morphism.agda", 57, "idᵁ"), cc("UCSetup/Morphism.agda", 65, "composeᵁ"), cc("UCSetup/Morphism.agda", 83, "identityʳ-κ"), cc("UCSetup/Morphism.agda", 86, "identityˡ-κ"));
- _change of kernel_: for $ν : cal(E) ⇒ cal(E)'$ over the same $(cal(C), cal(I), cal(M))$,
  $mck_ν := ("Id", "Id", opid, ν)$ #srcs(cc("UCSetup/Morphism.agda", 48, "changeKernel"), cc("Abstract2/Morphism.agda", 114, "reobserve"));
- _image factorisation_: every $𝕄$ factors as an Epi change of kernel $𝕊 → 𝕊[op("Im") ν]$ followed by a
  morphism with Mono test map, where $op("Im") ν (A)$ is $cal(E)(A)$ with the equality induced by $ν_A$
  #srcs(cc("UCSetup/Morphism.agda", 101, "Factorization"), ag("Categories/Functor/Presheaf/Morphism.agda", 89, "image"), cc("UCSetup/Morphism.agda", 110, "coarsen-to-image"), cc("UCSetup/Morphism.agda", 113, "image-morphism"));
- _wide subcategories_: a wide subcategory $cal(W) ⊆ cal(C)$ closed under identities, composition,
  $η$, $μ$, every $T_V$ and every $opsub_c$, with tests $cal(E)'$ on $cal(W)$ presented by
  $ν : cal(E)' ⇒ cal(E) ∘ ι^"op"$, gives a setup $𝕊|_cal(W)$ and an inclusion $mincl : 𝕊|_cal(W) → 𝕊$;
  for $cal(E)' = ι^* cal(E)$, emulation in $𝕊|_cal(W)$ is the restriction of emulation in $𝕊$
  #srcs(cc("Abstract2/WideSubcategory.agda", 52, "SetupSubcategory"), cc("Abstract2/WideSubcategory.agda", 106, "Restriction"), cc("Abstract2/WideSubcategory.agda", 118, "inclusion"), cc("Abstract2/WideSubcategory.agda", 158, "restrict-≤UC"), cc("Abstract2/WideSubcategory.agda", 172, "unrestrict-≤UC")).

#theorem(name: [transport along a morphism])[
Let $𝕄 = (F, Φ, κ, ν) : 𝕊 → 𝕊'$.
+ If $ν$ is Epi, $F$ preserves $eqE$; if $ν$ is Mono, $F$ reflects $eqE$.
+ If $ν$ is Epi and $𝕊'$ is grade-stable, then $f leUC g ⇒ G f leUC G g$; contrapositively, an
  impossibility proved in $𝕊'$ is one in $𝕊$.
+ If $Φ$ is full, $κ$ is mono up to $eqE$ ($κ ∘ h eqE κ ∘ h' ⇒ h eqE h'$), $ν$ is Mono and $𝕊$ is
  grade-stable, then $G f leUC G g ⇒ f leUC g$.
#srcs(ag("Categories/Functor/Presheaf/Morphism.agda", 73, "epi⇒preserves"), ag("Categories/Functor/Presheaf/Morphism.agda", 81, "mono⇒reflects"), cc("Abstract2/Morphism.agda", 51, "epi⇒preserves-≈ℰ"), cc("Abstract2/Morphism.agda", 54, "mono⇒reflects-≈ℰ"), cc("Abstract2/Morphism.agda", 75, "transfer"), cc("Abstract2/Morphism.agda", 79, "transfer-impossible"), cc("Abstract2/Morphism.agda", 83, "κ-Mono"), cc("Abstract2/Morphism.agda", 90, "reflects-≤UC"))
] <thm:transport>

#proofidea[(1) is one naturality square of $ν$, cancelled on the surjective or the injective side.
For (2): take the dummy simulator $s_0$ of $f leUC g$; Epi carries $f eqE opsub_(s_0) g$ along $F$; the
$κ$-law for $opsub$ rewrites $G(opsub_(s_0) g)$ as $opsub'_(Φ s_0) G g$; grade stability of $𝕊'$
(@prop:bridge) lifts the target $eqE$ to $eqU$; dummy completeness concludes.]

The hypotheses of (2) and (3) fail in several interesting cases: #PM is not grade-stable, and
test maps out of syntactic models are rarely Epi. The more general `transfer⁺` needs only
$f eqU g ⇒ G f eqU G g$. One may prove this directly, by density, or, for standard morphisms,
from preservation of $eqE$ and essential surjectivity of $F$ on objects (hence target ancillas).
The latter route gives the full-test W inclusion; it does not assume the false #PM grade-stability
premise. The refinement below and the explicit construction theorem of @sec:rs give other routes.
#srcs(cc("Abstract2/Morphism.agda", 65, "transfer⁺"), cc("Standard2/Morphism.agda", 97, "surjective⇒preserves-≈ᵁ"))

#theorem(name: [refinement of the observation])[
Let $cal(E)'$ be a second test presheaf on the same $cal(C)$ with $eqE ⊆ scripts(≈)_(cal(E)')$. Then
$eqU ⊆ scripts(≈)^upright(U)'$ and $leUC ⊆ scripts(≤)'_"UC"$, with the same simulators. No epi, mono or
grade-stability hypothesis is spent.
#srcs(cc("Abstract2/Morphism.agda", 125, "Refine"), cc("Abstract2/Morphism.agda", 139, "≈ᵁ-refine"), cc("Abstract2/Morphism.agda", 142, "≤UC-refine"))
] <thm:refine>

== The standard instantiation <sec:std>

#definition(name: [standard setup])[
For a monoidal category $𝕄$ and a presheaf $cal(E)$ on its underlying category,
$Std(𝕄, cal(E)) := (|𝕄|, 𝕄, X ↦ X ⊗ (-), cal(E))$: computations and interfaces are the same category,
and the graded monad is the curried tensor.
#srcs(cc("Standard2.agda", 19, "StdUC"), cc("Standard2.agda", 31, "StdSetup"), cc("Standard2.agda", 28, "ℳ-standard"), ag("Categories/Functor/Monoidal/CurriedTensor.agda", 37, "curriedTensor"))
] <def:std>

Concretely $T_X B = X ⊗ B$, $T_W h = opid_W ⊗ h$, $η = λ^(-1)$, $μ_(X,Y) = α^(-1) : X ⊗ (Y ⊗ B) → (X ⊗ Y) ⊗ B$,
$opsub_c = c ⊗ opid$ and $h ∙ f = α^(-1) ∘ (opid_X ⊗ h) ∘ f$. Since $α$ is invertible, the two relations
of @sec:metatheory read
$ f eqU g & ⟺ quad ∀ W. quad opid_W ⊗ f eqE opid_W ⊗ g quad "(agreement under every left ancilla)", \
  f leUC g & ⟺ quad ∀ a : X → X'. ∃ s : Y → X'. quad (a ⊗ opid_B) ∘ f eqU (s ⊗ opid_B) ∘ g . $
An adversary is an ordinary morphism plugged onto the adversary interface, a simulator one plugged
onto the ideal protocol's. The principal setups below are standard; #NDA/#NDB are
grade-side regradings of standard setups, as specified in @sec:nd.

#proposition(name: [standard morphisms])[
If $F : 𝕄 → 𝕄'$ is strong monoidal and $ν : cal(E) ⇒ cal(E)' ∘ F^"op"$, then $(F, F, δ, ν)$ is a setup
morphism $Std(𝕄, cal(E)) → Std(𝕄', cal(E)')$, where $δ_(X,A) : F(X ⊗ A) → F X ⊗ F A$ is the inverse of
the strong comparison.
#srcs(cc("Standard2/Morphism.agda", 41, "StdUCMorphism"))
] <prop:std-morphism>

The general @def:morphism requires comparisons in the displayed direction and their unit,
composition and regrading laws. An operational interpreter, or an unrelated lax comparison, does
not supply them. Conversely, a difference between product and interleaving interfaces is not a
universal no-functor theorem: bundled messages, a restricted carrier or a different lawful tensor
may change the question. @sec:non-morphisms records obstructions to specified candidates.

#proposition(name: [monoidal quotients and the two-sided ancilla kernel])[
+ Let $∼$ be a _monoidal congruence_ on $𝕄$: an equivalence on each hom-set that contains the
  hom-equality and is preserved by $∘$ and $⊗$. Then $𝕄 slash ∼$ (same objects, morphisms and
  structure, equality $∼$) is monoidal, and the identity-on-the-nose functor $𝕄 → 𝕄 slash ∼$ is strong
  monoidal. If moreover $∼ ⊆ eqE$, then $cal(E)$ descends to $𝕄 slash ∼$ and the comparison of tests
  is the identity, both Epi and Mono.
+ For any $cal(E)$, the relation
  $f scripts(∼)^cal(E) g :⟺ ∀ Y, Z. thin (opid_Y ⊗ f) ⊗ opid_Z eqE (opid_Y ⊗ g) ⊗ opid_Z$
  is a monoidal congruence (no braiding is needed: the other factor of a tensor is absorbed into an
  ancilla) lying between the hom-equality and $eqU$; in particular it is contained in $eqE$, so
  $cal(E)$ descends to the quotient.
#srcs(ag("Categories/Category/Monoidal/Construction/Quotient.agda", 33, "MonoidalCongruence"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 65, "quotient"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 74, "quotientF"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 92, "descend"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 101, "descendᵛ-mono"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 104, "descendᵛ-epi"), cc("Standard2/UKernel.agda", 101, "uKernel"), cc("Standard2/UKernel.agda", 106, "∼⇒≈ℰ"), cc("Standard2/UKernel.agda", 118, "∼⇒≈ᵁ"))
] <prop:quotient>

== Robust compilation: a theorem about $leUC$, not a setup <sec:robust>

Let $sans("Pred")^upright(U)(A, B)$ consist of families $H = (H_(X'))_(X')$ of $eqU$-invariant
predicates on attacked protocols $A → T_(X') B$, and say $f$ _robustly satisfies_ $H$ if
$H(opsub_a ∘ f)$ holds for every adversary $a$.

#theorem(name: [UC is robust compilation])[
+ $f leUC g$ iff every $H ∈ sans("Pred")^upright(U)(A, B)$ robustly satisfied by $g$ is robustly
  satisfied by $f$. The witness for "if" is $"Hyp"(g) := $ "is $eqU$-equal to an attacked $g$".
+ Robust preservation of _environment-blind_ predicates (on observations, ignoring the environment)
  is exactly _outcome inclusion_ $f ⊆^o g :⟺ ∀ W, e. thin ∃ e'. thin oprun_W (f)(e) ≈ oprun_W (g)(e')$;
  it is strictly weaker than $leUC$ (@thm:rel-blind).
+ _Trace form._ $f eqU g$ iff $f$ and $g$ robustly satisfy the same environment-indexed trace
  properties; hence $f leUC g$ iff for every $a$ there is $s$ such that every such property of
  $opsub_s ∘ g$ is one of $opsub_a ∘ f$.
+ _Two setups._ Along $𝕄 : 𝕊 → 𝕊'$: if $ν$ is Epi and $𝕊'$ grade-stable, $f leUC g$ implies that
  every robust hyperproperty of $G g$ in $𝕊'$ is one of $G f$; conversely if $Φ$ is full, $κ$ mono up to
  $eqE$, $ν$ Mono and $𝕊$ grade-stable.
#srcs(cc("UC/Robust/Compilation.agda", 64, "Predᵁ"), cc("UC/Robust/Compilation.agda", 67, "Robustᵁ"), cc("UC/Robust/Compilation.agda", 71, "Hyp"), cc("UC/Robust/Compilation.agda", 91, "≤UC⇔robustᵁ"), cc("UC/Robust/Compilation.agda", 44, "_⊆ᵒ_"), cc("UC/Robust/Compilation.agda", 52, "robust⇔outcomes"), cc("UC/Robust/Compilation.agda", 115, "≈ᵁ⇔robustᵗ"), cc("UC/Robust/Compilation.agda", 121, "≤UC⇔robustᵗ"), cc("UC/Robust/Compilation.agda", 150, "robustᵁ-transfer"), cc("UC/Robust/Compilation.agda", 155, "robustᵁ-reflect"), cc("UC/Robust/Compilation.agda", 161, "≤UC⇔robustᵁ-along"))
] <thm:robust>

Item 1 is Patrignani et al.'s "UC is robust hyperproperty preservation" (@patrignani2024, Thm 4;
@patrignani2024csf, Thm 3) in this setting; it needs neither grade stability nor any closure
condition on environments. In item 3 the simulator is chosen before the property. Two refinements
are designed but not formalised #design: the _reactive-simulatability_ order
$∀ a ∀ W, e ∃ s. thin oprun_W (opsub_a f)(e) ≈ oprun_W (opsub_s g)(e)$, which robust preservation of
all trace properties should characterise (the conjecture of @patrignani2024, §8.2.1) and which lies
between $leUC$ and outcome inclusion; and the criteria hierarchy of robust compilation
(@abate2019journey) as a family of test presheaves on one $(cal(C), cal(I), cal(M))$, ordered by kernel
refinement (@thm:refine).

#page(flipped: true)[
= The setups at a glance <sec:table>

For standard setups (@def:std), each row gives the monoidal category $𝕄$ — objects with their
tensor, morphisms with their hom-equality — and the test presheaf. ND additionally restricts
the grade category without restricting computations. #design rows are planned, not built.

#{
  set text(size: 7.6pt)
  set par(justify: false, leading: 0.5em)
  table(
    columns: (auto, 1.55fr, 2.5fr, 2.0fr, 1.25fr, 1.75fr),
    stroke: 0.4pt + luma(62%),
    inset: 3.2pt,
    align: left + top,
    table.header([*Name*], [*Objects; $⊗$*], [*Morphisms; hom-equality*], [*Tests $cal(E)(A)$*], [*Model of*], [*Status; source*]),
    [#PM \ protocol model], [interfaces $A = (A^+, A^-)$, pairs of sets; componentwise $+$],
    [probabilistic Mealy machines $A^+ + B^- → A^- + B^+$ over the probabilistic delay monad, composed by feedback (G-construction); simulation equivalence $eqM$],
    [tests $e : A → Ω$, identified when $Obs(e ∘ m) simA Obs(e' ∘ m)$ for every closure $m : 0 → A$],
    [UC @canetti2020uc],
    [#formal #cc("UC/Model/Setup.agda", 25, "StdUC 𝔾ᵒ ℰᵒ"), #cc("UC/Model/Seal.agda", 43, "𝔾ᵒ"), #cc("UC/Model/Setup.agda", 24, "ℰᵒ")],
    [#RS \ random systems], [as #PM],
    [#PM's globally initialized partial machines; behavioural equivalence $eqR$: equal verdict laws against every adaptive distinguisher],
    [#PM's tests, descended],
    [random systems @maurer2002, constructive cryptography @maurer2011cc],
    [#formal #cc("UC/RandomSystems/Setup.agda", 39, "StdUC 𝔾ᴿ ℰᴿ"), #cc("UC/RandomSystems/Setup.agda", 28, "𝔾ᴿ"), #cc("UC/RandomSystems/Setup.agda", 36, "ℰᴿ")],
    [#Wio, #WW \ well-bracketed machines], [oracle signatures (as #SSP); tensor transported from #PM],
    [#PM morphisms between flattened signatures that are $eqM$-equal to a well-bracketed machine; $eqM$],
    [$iota^* cal(E)^o$: all #PM tests; $cal(E)^W$: well-bracketed tests modulo well-bracketed closures],
    [call/return discipline inside #PM; respectfulness @lochbihler2019cc],
    [#formal #cc("UC/Bracket/Monoidal.agda", 309, "𝒲ᴹ"), #cc("UC/Bracket/Monoidal.agda", 332, "StdUC.StdSetup 𝒲ᴹ ι*ℰᵒ"), #cc("UC/Bracket/Setup.agda", 75, "StdUC 𝒲ᴹ ℰᵂ")],
    [#PMwb \ well-bracketed quotient], [as #Wsub],
    [#Wsub's morphisms modulo the two-sided ancilla kernel $simW$ of well-bracketed tests],
    [$cal(E)^W$, descended],
    [#PM against call/return environments],
    [#formal #cc("UC/Bracket/Setup.agda", 153, "StdUC PM[wb]ᴹ ℰ[wb]"), #cc("UC/Bracket/Setup.agda", 88, "PM[wb]ᴹ"), #cc("UC/Bracket/Setup.agda", 150, "ℰ[wb]")],
    [#SSP \ call/return packages], [oracle signatures $(sans("Ch"), Q, R)$; disjoint union of channels],
    [packages: a state, an initial state, and a step answering each query by a finite tree of calls, rational coins and aborts; composition by inlining; $eqP$: simulations up to syntactic tree equality],
    [distinguishers $D : A → Ω$, identified when all games $G : 1 → A$ give close verdict subdistributions],
    [state-separating proofs @brzuska2018 @ssprove2023],
    [#formal #cc("SSP/Setup.agda", 23, "StdUC Protᴹ ℰᵖ"), #cc("SSP/Protocol/Monoidal.agda", 232, "Protᴹ"), #cc("SSP/Setup.agda", 22, "ℰᵖ")],
    [#ITM \ interactive Turing machines], [finite trees of bitstring ports; concatenation of trees],
    [terms of the free monoidal category on finite-table interactive Turing machines; free monoidal congruence],
    [#PM's tests of the interpreted interface],
    [static-port, always-reply ITM fragment; not full Canetti/IITM correspondence],
    [#formal #cc("ITM/Setup.agda", 39, "StdUC 𝕋ᴹ ℰᵀ"), #cc("ITM/Core.agda", 206, "𝕋ᴹ"), #cc("ITM/Setup.agda", 36, "ℰᵀ"); @thm:itm-client],
    [#ITMiso \ uninitialized relational ITMs], [as #ITM], [as #ITM],
    [arbitrary #Iso tests of all-state halting relations; whole-composite state isomorphism],
    [structural, unweighted transition interpretation; not initialized execution security],
    [#formal #cc("ITM/Relational.agda", 125, "StdUC 𝕋ᴹ ℰᴵˢᵒ"), #cc("ITM/Relational.agda", 122, "ℰᴵˢᵒ")],
    [#Sym, #Symiso \ Dolev–Yao], [trees of atoms: term ports, the verdict, the void; concatenation of trees],
    [free monoidal category on Dolev–Yao roles with unit-free boundaries; free monoidal congruence],
    [role circuits with an ancilla; #Sym: possible verdicts in fixed token-passing runs with globally fresh names; #Symiso: circuit syntax],
    [restricted symbolic may-testing / syntactic proof IR; not general applied-pi UC],
    [#formal #cc("Symbolic/Setup.agda", 105, "StdUC 𝔻𝕐 ℰˢʸᵐ"), #cc("Symbolic/Fine.agda", 74, "StdUC 𝔻𝕐 ℰ≅"), #cc("Symbolic/Fine.agda", 41, "𝔻𝕐"), #cc("Symbolic/Setup.agda", 102, "ℰˢʸᵐ"), #cc("Symbolic/Fine.agda", 71, "ℰ≅")],
    [#Symcert \ certified symbolic source], [as #Symiso],
    [free circuits whose generators carry direct positive-rate query certificates for their actual parameterized runtime; coherence equality],
    [syntactic tests of certified circuits],
    [query-admissible interpretation, not a PPT or crypto-security theorem],
    [#formal #cc("Symbolic/Computational.agda", 143, "Sym≅ᶜ"), #cc("Symbolic/Computational.agda", 214, "fine→comp"); @sec:symbolic-interpretations],
    [#Iso \ relational machines], [channels $(sans("in"), sans("out"))$ of sets; $+$, grade on the right],
    [relations $S × sans("In") × (sans("Out") + 1) × S$ without initial state; composition by ping-pong; $isoM$: step-preserving bijection of state sets],
    [pairs $(Y, E : A ⊗ Y → Ω)$ of an ancilla and an environment, up to $isoM$],
    [nondeterministic machines up to isomorphism],
    [#formal #cc("Machine/UC.agda", 114, "StdUC machines ℰ-tests"), #cc("Machine/UC.agda", 109, "machines"), #cc("Machine/UC.agda", 91, "ℰ-tests")],
    [#Rel \ relations], [sets; $×$], [relations; equality of relations],
    [subsets, i.e. $op("Hom")(-, 1)$],
    [possibilistic one-shot security; cf. @broadbent2022],
    [#formal #cc("Examples/RelSetup.agda", 38, "StdUC Rel ℰ-tests"), #cc("Examples/RelSetup.agda", 31, "Rel"), #cc("Examples/RelSetup.agda", 35, "ℰ-tests")],
    [#PMom \ vanishing tier], [$ℕ$-indexed families of #PM interfaces; levelwise],
    [levelwise #PM morphisms certified at a rate polynomial in the security parameter; levelwise $eqM$],
    [family tests, identified up to vanishing advantage],
    [asymptotic UC],
    [#formal #cc("UC/Family.agda", 148, "ucSetup^ω"), at #PM: #cc("UC/Model/Family.agda", 26, "𝔾ᵒ qevaluationᵒ gradingᵒ")],
    [#PMN \ negligible tier], [as #PMom], [as #PMom],
    [family tests, identified up to local negligible advantage],
    [local negligible observation with query rates; PPT correspondence needs extra hypotheses],
    [#formal #cc("UC/Family/Negligible/Setup.agda", 51, "ucSetupᴺ"), at #PM: #cc("UC/Model/Family.agda", 35, "𝔾ᵒ qevaluationᵒ gradingᵒ")],
    [#QPM \ quantitative #PM], [as #PM], [as #PM],
    [an approximation space: $e scripts(≈)_ε e'$ iff every closure is observed within $ε$],
    [#PM with errors kept],
    [#formal #cc("UC/Quantitative/Observed.agda", 124, "QSetup"), at #PM: #cc("UC/Model/Quantitative.agda", 25, "QSetup to QSetupᵒ")],
    [#QRS \ quantitative #RS], [as #RS], [as #RS],
    [#RS's tests at a measured error, read through the _closed_ verdict slack],
    [constructive cryptography's security condition at exact $ε$ @maurer2011cc],
    [#formal #cc("UC/RandomSystems/Quantitative.agda", 74, "QSetupᴿ"), #cc("UC/RandomSystems/Quantitative.agda", 63, "qevaluationᴿ")],
    [#SSPd \ distributional #SSP], [as #SSP],
    [#SSP packages modulo the two-sided contextual distributional kernel $scripts(≈)^sans("d")$],
    [#SSP's tests, descended], [deferred sampling as an equation; same security order],
    [#formal #cc("SSP/Dist/Setup.agda", 26, "Protᵈ"), #cc("SSP/Dist/Setup.agda", 32, "StdUC Protᵈ ℰᵈ"); @prop:ssp-dist-morphism],
    [#IPDL], [polarised typed channel contexts $"pos" ⇌ "neg"$; concatenation],
    [reaction networks; composition $"new" B "in" (f ∥ g)$; IPDL's exact equational theory],
    [IPDL protocols into $Ω$, identified modulo IPDL closures],
    [IPDL @gancher2023ipdl],
    [#design #plan("uc-setup-ipdl.md")],
    [#CB \ causal converter design], [pairs of slot alphabets; $×$ (concurrency)],
    [proposed two-phase resource-preserving converters, including zero-delay wires; not all native strictly causal boxes],
    [proposed causal distinguishers; native correspondence open],
    [classical causal fragment @portmann2017],
    [#design #plan("uc-setup-causal-boxes.md"); @sec:causal-island],
    [$sans("RSIM")$], [typed service/clock ports with ownership; proposed disjoint union],
    [open buffered collections with default scheduling; gluing/identity laws unproved],
    [native honest views; test correspondence unproved],
    [@backes2007rsim],
    [#design proposed, no setup implementation; @sec:rsim-island],
    [task-PIOA], [input-enabled automata and explicit oblivious scripts; proposed shuffle-aware tensor],
    [scheduled probabilistic transitions; no implemented category or setup],
    [environment-indexed sets of trace distributions],
    [@canetti2006taskpioa],
    [#design proposed, no setup implementation; @sec:task-island],
    [#NDA, #NDB \ nondeterministic choice], [#PM's (or #SSP's) objects; grades $X ⊗ C_(S_1) ⊗ dots.c ⊗ C_(S_n)$ with choice factors $C_S = (1, S)$],
    [#PM's morphisms; grade morphisms: all of them between such grades (#NDB), or $u ⊗ ρ$ with $ρ$ a relabelling of choice factors (#NDA)],
    [the ambient tests],
    [B: unrestricted ambient regrading; A: environment-triggered, simulator-translated choice; not native task-PIOA],
    [#formal over any symmetric 𝕄, at #SSP: #cc("ND/SSP/Setup.agda", 127, "NDB"), #cc("ND/SSP/Setup.agda", 130, "NDA"); at #PM: #cc("ND/PM/Setup.agda", 31, "NDB"), #cc("ND/PM/Setup.agda", 34, "NDA"); @sec:nd],
  )
}
]

= The setups <sec:setups>

== #PM: the protocol model <sec:pm>

*The base.* $Dp$ is the rational probabilistic delay monad: $Dp A = ν X. S_ℚ (A + X)$, coinductive trees
of biased rational coins whose leaves are values or further delay; mass that never lands is
divergence, and $apx_p$ is the delay-insensitive equality of the resulting laws, whose masses are
lower reals #srcs(ag("ProbabilisticLogic/Dp.agda", 48, "Dₚ"), ag("ProbabilisticLogic/Dp.agda", 430, "_≈ₚ_")).
Its Kleisli category on sets is symmetric monoidal under $×$ (commutativity of $Dp$),
distributive, and has an Elgot iteration #srcs(cc("Machines/Base.agda", 77, "𝒱ₚ"), cc("Machines/Base.agda", 246, "Elgotₚ")).
A _Mealy machine_ $A → B$ over it is a state set $S$, an initial law $s_0 ∈ Dp S$ and a step
$S × A → Dp (S × B)$; machines form a symmetric monoidal category under $+$, traced by the
iteration-based $+$-trace #srcs(cc("Machines/Core.agda", 42, "Machine"), cc("Machines/Core.agda", 27, "State"), cc("Machines/Base.agda", 269, "ℳₚ"), cc("Machines/Base.agda", 272, "Tracedₚ")) (cf. @katis1997 @bonchidilavore2025).
Their hom-equality is _simulation equivalence_ $eqM$: the equivalence closure of the relation "there is
a function $θ : S → S'$ with $θ s_0 = s'_0$ and $"step"' ∘ (θ × opid) = (θ × opid) ∘ "step"$"
#srcs(cc("Machines/Sim.agda", 39, "_≲_"), cc("Machines/Sim.agda", 50, "_≈ᴹ_")).

#definition(name: [#PM])[
$𝔾^o$ is the Int (G) construction (@jsv1996) on traced Mealy machines. Its objects are interfaces
$A = (A^+, A^-)$ ($A^+$ travels up to the caller, $A^-$ down); a morphism $A → B$ is a machine
$A^+ + B^- → A^- + B^+$; composition is feedback over the middle interface, the identity is the
copycat, and $A ⊗ C = (A^+ + C^+, A^- + C^-)$. The verdict interface is $Ω = (sans("Bool"), 1)$: the
environment's single activation is the tick on $1$. A _closure_ of $A$ is a morphism $m : 0 → A$; a
closed system $u : 0 → Ω$ is observed as $Obs(u) ∈ Dp sans("Bool")$, its run on the tick. Two laws are
close, $d simA d'$, when for every rational $ε > 0$ their $sans("true")$-masses and their
$sans("false")$-masses agree within $ε$ (comparing both masses separates answering $sans("false")$
from diverging). The tests are
$ cal(E)^o (A) = 𝔾^o (A, Ω) slash ≋, quad e ≋ e' :⟺ ∀ m : 0 → A. thin Obs(e ∘ m) simA Obs(e' ∘ m), $
the image of the evaluation functional, and $PM := Std(𝔾^o, cal(E)^o)$.
#srcs(cc("Machines/Base.agda", 282, "𝒢ₚᴹ"), cc("UC/Model/Seal.agda", 43, "𝔾ᵒ"), cc("UC/Model/Observation.agda", 48, "Ωᵒ"), cc("UC/Model/Observation.agda", 52, "Obs"), cc("UC/Machine.agda", 123, "Approximationᴹ"), cc("UC/Core.agda", 103, "Evaluation"), cc("UC/Core.agda", 93, "ℰᴼ"), cc("UC/Model/Observation.agda", 75, "evaluationᵒ"), cc("UC/Model/Setup.agda", 24, "ℰᵒ"), cc("UC/Model/Setup.agda", 25, "StdUC 𝔾ᵒ ℰᵒ"))
] <def:pm>

In #PM, $f eqE g$ says that every closed context $t ∘ f ∘ m$ is observed like $t ∘ g ∘ m$; $f eqU g$ says
the same with an arbitrary ancilla beside the hole; and $f leUC g$ is UC emulation in the usual
"for every adversary there is a simulator such that no environment tells them apart" form, the
environment being a pair (closure, test). Compared with @canetti2001, machines are arbitrary
probabilistic Mealy machines rather than polynomial ITMs, and the execution model is the one of the
G-construction: each activation is answered by exactly one message, and divergence is missing mass.
The hom-equality is observed exactly: $u eqM v ⇒ Obs(u) apx_p Obs(v)$ #srcs(cc("UC/Model/Observation.agda", 60, "obs-resp")).

Initialization is global: the initial law is bound even for a zero-query verdict, and tensor
initializes both factors. A divergent portless simulator can therefore abort an untouched honest
interface. These are partial-mass models, not automatically Maurer's normalized systems; neither
availability nor total initialization follows from emulation. Both verdict masses are compared,
but this individual readout distance is not total variation on `Bool + divergence`: masses
$(1/2,1/2)$ and $(1/4,1/4)$ differ by $1/4$ per bit and by $1/2$ in total termination probability.
The all-strategy quantifier can observe the latter by returning true on every terminating path.
These distinctions persist in #RS, #QRS and PM-based choice.

#theorem(name: [full abstraction of #PM])[
For $f, g : A → X ⊗ B$ in #PM, $f eqU g$ iff $f eqR g$, i.e. iff $f$ and $g$ are the same random
system (@sec:rs). One ancilla suffices: if $T_(A^*) f eqE T_(A^*) g$ for the dual interface
$A^* = (A^-, A^+)$, then $f eqR g$.
#srcs(cc("UC/RandomSystems/FullAbstraction.agda", 174, "≈ᵁ⇒≈ᴿ"), cc("UC/RandomSystems/FullAbstraction.agda", 170, "T₁-≈ℰ⇒∼ᴿ"), cc("UC/RandomSystems/Morphism.agda", 35, "≈ᴿ⇒≈ᵁ"))
] <thm:fullabs>

#proofidea[($⇒$) The closure $op("cup") : 0 → A^* ⊗ A$ hands the letters of a distinguisher strategy $d$ to
the hole and back, and the test that plays $d$ observes exactly the run of $d$ against $f$:
$Obs((op("play")_d ∘ (opid ⊗ f)) ∘ op("cup")) apx_p op("run")(f, d)$
#srcs(cc("UC/RandomSystems/FullAbstraction.agda", 151, "play-cup"), cc("UC/RandomSystems/FullAbstraction.agda", 148, "cupᵒ"), cc("UC/RandomSystems/FullAbstraction.agda", 144, "playᵒ")). ($⇐$) The test map of
$mrs : PM → RS$ is Mono (@sec:formal-morphisms).]

So the library's security notion has a semantic meaning: two protocols are UC-equivalent in #PM exactly
when they are the same random system in the sense of @maurer2002.

#proposition(name: [#PM is not grade-stable])[
Let $A = (∅, sans("Bool"))$, $B = (∅, 1)$ and let $r_b : A → B$ be the stateless machine that answers the
activation from $B$ by sending $b$ down to $A$. Then $r_sans("true") eqE r_sans("false")$ — a closure of
$A$ can receive $b$ but has nothing to answer with, so every closed composite diverges — while
$r_sans("true") ≉_sans("R") r_sans("false")$, hence (@thm:fullabs)
$T_(A^*) r_sans("true") ≉_cal(E) T_(A^*) r_sans("false")$. So #PM is not grade-stable.
#srcs(cc("UC/RandomSystems/FullAbstraction.agda", 80, "revealᴹ"), cc("UC/RandomSystems/FullAbstraction.agda", 186, "reveal-≈ℰ"), cc("UC/RandomSystems/FullAbstraction.agda", 121, "reveal-≉ᴿ"), cc("UC/RandomSystems/FullAbstraction.agda", 189, "¬gradeStableᵒ"))
] <prop:not-gs>

Consequently @prop:bridge(i) is unavailable in #PM: a fact proved at $eqE$ reaches $eqU$ through
behavioural equality (@thm:fullabs) instead, and the target hypothesis of @thm:transport(2) never holds
with #PM as target. Emulation in #PM is invariant under behavioural equality of either side
#srcs(cc("UC/RandomSystems/Morphism.agda", 38, "≤UC-resp-≈ᴿ")).

== #RS: random systems <sec:rs>

#definition(name: [distinguishers, behavioural equivalence])[
A _distinguisher_ for a machine with inputs $X$ and outputs $Y$ is a finite decision tree
$d ∈ sans("Strat")(X, Y)$ whose leaves output a bit and whose nodes either ask $x ∈ X$ and branch on
the answer, or toss a rational coin; $op("run")(f, d) ∈ Dp sans("Bool")$ runs $f$ from its initial
state against $d$. Then $f eqR g$ iff $op("run")(f, d) simA op("run")(g, d)$ for every $d$ (adaptive
equivalence, @maurer2002 Defs. 9–10). The non-adaptive equivalence $f eqB g$ asks, for every input
word and every $[0,1]$-valued function on output words, equal expectations within every $ε > 0$
(@maurer2002 Def. 3).
#srcs(cc("Strategy.agda", 24, "Strat"), cc("UC/Machine/Run.agda", 58, "runˢ"), cc("UC/Machine/Behaviour.agda", 38, "_≈ᴿ_"), cc("UC/Machine/Behaviour.agda", 62, "_≈ᴮ_"))
] <def:behaviour>

#theorem(name: [behavioural equivalence is a monoidal congruence])[
$eqM ⊆ eqR$, and $eqR$ is preserved by composition and tensor of $𝔾^o$ (@maurer2002 Lemma 4).
#srcs(cc("UC/Machine/Behaviour.agda", 49, "≈ᴹ⇒≈ᴿ"), cc("UC/Machine/Behaviour/Congruence.agda", 267, "composeᴳ-resp-≈ᴿ"), cc("UC/Machine/Behaviour/Congruence.agda", 302, "⊗₁ᴳ-resp-≈ᴿ"), cc("UC/RandomSystems/Seal.agda", 37, "congᴿ"))
] <thm:rs-congruence>

#proofidea[A context that a distinguisher can simulate is _absorbed_ into it: the context's own coins are
unfolded into the strategy, and since the context may loop while strategies are finite, the
absorbed distinguisher is the family of its budget-truncations
#srcs(cc("UC/Machine/Behaviour/Absorb.agda", 246, "Absorbs"), cc("UC/Machine/Behaviour/Absorb.agda", 269, "absorbs⇒resp")). Composition and tensor with a fixed machine on either side are absorbable.]

#definition(name: [#RS])[
$𝔾^R := 𝔾^o slash eqR$ (@prop:quotient). Tests cannot separate behaviourally equal machines, so
$cal(E)^o$ descends to $cal(E)^R$, and $RS := Std(𝔾^R, cal(E)^R)$.
#srcs(cc("UC/RandomSystems/Setup.agda", 28, "𝔾ᴿ"), cc("UC/RandomSystems/Setup.agda", 31, "∼ᴿ⇒≋"), cc("UC/RandomSystems/Setup.agda", 36, "ℰᴿ"), cc("UC/RandomSystems/Setup.agda", 39, "StdUC 𝔾ᴿ ℰᴿ"))
] <def:rs>

#proposition(name: [non-adaptive suffices on finite alphabets])[
If the query alphabet $X$ is finite with decidable equality, $f eqB g ⇒ f eqR g$.
#srcs(cc("UC/Machine/Behaviour/Finite.agda", 415, "≈ᴮ⇒≈ᴿ-fin"))
] <prop:finite>

The general statement is classical (@lochbihler2019cc, Thm. 2) and open here; the adaptive $eqR$ was
chosen as the hom-equality because the congruence proof needs it.

*The random-systems toolkit.* A verdict mass is a lower real, so the distinguishing advantage is a
relation in a rational slack rather than a number.

#definition(name: [advantage])[
$Δ_d (f, g) ≤ ε$ iff for every $δ > 0$ the laws $op("run")(f, d)$ and $op("run")(g, d)$ have both masses within
$ε + δ$ (a _closed_ slack); $f eqR^ε g$ iff $Δ_d (f, g) ≤ ε$ for every distinguisher $d$
(@maurer2002 Def. 10, @maurer2011cc §4.5).
#srcs(cc("UC/RandomSystems/Advantage.agda", 42, "Δ[_]⟨_,_⟩≤_"), cc("UC/RandomSystems/Advantage.agda", 46, "_≈ᴿ[_]_"))
] <def:advantage>

#proposition(name: [Δ is a pseudometric on #RS])[
$f eqR^ε g$ and $g eqR^(ε') h$ give $f eqR^(ε + ε') h$ (@maurer2002 Lemma 5(i)); $f eqR g$ iff $f eqR^0 g$
iff $f eqR^ε g$ for every $ε > 0$; and bounds are invariant under $eqR$ on either side, so $Δ$ descends
to the homs of $𝔾^R$.
#srcs(cc("UC/RandomSystems/Advantage.agda", 52, "≈ᴿ[]-trans"), cc("UC/RandomSystems/Advantage.agda", 81, "≈ᴿ⇔≈ᴿ[0]"), cc("UC/RandomSystems/Advantage.agda", 85, "≈ᴿ⇔≈ᴿ[+]"), cc("UC/RandomSystems/Advantage.agda", 91, "≈ᴿ[]-resp"))
] <prop:pseudometric>

#theorem(name: [composition theorem at a slack])[
Absorbable contexts do not increase $Δ$: $f eqR^ε g ⇒ C f eqR^ε C g$. Hence $f eqR^ε h$ and
$g eqR^δ i$ give $f ∘ g eqR^(ε + δ) h ∘ i$ and $f ⊗ g eqR^(ε + δ) h ⊗ i$ (@maurer2002 Lemma 5(ii)–(iii),
@maurer2011cc Def. 2), and a closing context observes at most $Δ$: if $f eqR^ε g$ then
$Obs((t ∘ (opid ⊗ f)) ∘ m)$ and $Obs((t ∘ (opid ⊗ g)) ∘ m)$ are within $ε$ (closed slack).
#srcs(cc("UC/RandomSystems/Composition.agda", 66, "absorbs-Δ"), cc("UC/RandomSystems/Composition.agda", 73, "absorbs-≈ᴿ[]"), cc("UC/RandomSystems/Composition.agda", 91, "composeᴳ-≈ᴿ[]"), cc("UC/RandomSystems/Composition.agda", 100, "⊗₁ᴳ-≈ᴿ[]"), cc("UC/RandomSystems/Composition.agda", 130, "∘-resp-∼ᴿ[]"), cc("UC/RandomSystems/Composition.agda", 136, "⊗-resp-∼ᴿ[]"), cc("UC/RandomSystems/Composition.agda", 155, "close-∼ᴿ[]"))
] <thm:rs-composition>

#lemma(name: [hybrid argument])[
In any approximation with rational errors, $H_i scripts(≈)_(ε_i) H_(i+1)$ for $i < n$ gives
$H_0 scripts(≈)_(sum_(i<n) ε_i) H_n$. In #RS, if hybrid $i$ is $C_i (f)$ and hybrid $i+1$ is $C_i (g)$ up to
$eqR$, with every $C_i$ absorbable, then $f eqR^ε g$ gives $H_0 eqR^(n ε) H_n$.
#srcs(cc("Approx/Rational.agda", 95, "hybrid"), cc("UC/RandomSystems/Composition.agda", 78, "hybrid-absorbs"))
] <lem:hybrid>

#definition(name: [security-only construction])[
$f$ _security-only constructs_ $g$ within $ε$, $sans("Constructs")_ε (f, g)$, iff there is a simulator $s$ with
$f eqR^ε opsub_s ∘ g$ — condition 2 of constructive cryptography (@maurer2011cc §5.1,
Def. 3), with every strategy as distinguisher and no availability claim.
#srcs(cc("UC/RandomSystems/Construction.agda", 76, "Constructs"))
] <def:constructs>

#theorem(name: [security-only construction is emulation])[
+ For $f, g$ in #PM: $f leUC g$ in #PM $⟺ sans("Constructs")_0 (f, g) ⟺ mrs(f) leUC mrs(g)$ in #RS.
+ $Δ$ is the quantitative U-agreement of #QPM (@sec:qpm) up to slack: $f eqR^ε g$ iff
  $f eqU_(ε + δ) g$ for every $δ > 0$. Accordingly $sans("Constructs")_ε (f, g)$ iff one simulator
  witnesses $eqU_(ε + δ)$ for every $δ > 0$, and a quantitative witness at $ε$ gives security-only construction within $ε$.
+ (@maurer2011cc Thm. 1, security obligations) $sans("Constructs")_0 (f, f)$; $sans("Constructs")_ε (f, g)$ and
  $sans("Constructs")_(ε') (g, h)$ give $sans("Constructs")_(ε + ε') (f, h)$ with the simulators composed;
  $sans("Constructs")_ε (f, g)$ and $sans("Constructs")_(ε') (u, v)$ give
  $sans("Constructs")_(ε' + ε) (u ∙ f, v ∙ g)$.
+ In #RS, $eqU$ is $eqR$.
#srcs(cc("UC/RandomSystems/Construction.agda", 89, "≤UC⇔Constructs₀"), cc("UC/RandomSystems/Construction.agda", 114, "≤UCᴿ⇔Constructs₀"), cc("UC/RandomSystems/Construction.agda", 66, "∼ᴿ[]⇔≈ᵁ[]"), cc("UC/RandomSystems/Construction.agda", 120, "Witness⁺"), cc("UC/RandomSystems/Construction.agda", 130, "Constructs⇔Witness⁺"), cc("UC/RandomSystems/Construction.agda", 134, "Witness⇒Constructs"), cc("UC/RandomSystems/Construction.agda", 141, "constructs-refl"), cc("UC/RandomSystems/Construction.agda", 146, "constructs-trans"), cc("UC/RandomSystems/Construction.agda", 158, "constructs-∙"), cc("UC/RandomSystems/Construction.agda", 93, "≈ᵁᴿ⇒∼ᴿ"))
] <thm:constructs>

#definition(name: [full secure construction with designated modes])[
For fixed converters $a : X → I$ and $b : Y → I$, let
$sans("no-adversary")(a, f) := λ ∘ opsub_a ∘ f : A → B$.
$sans("SecurelyConstructs")_(ε_s, ε_a)(a, b, f, g)$ requires both
$sans("Constructs")_(ε_s)(f, g)$ and
$sans("no-adversary")(a, f) eqR^(ε_a) sans("no-adversary")(b, g)$.
The honest protocol is already included in $f = π R$; the converters shield Eve's
outside port and may answer internal mode queries. They are fixed before all
distinguishers. Taking $ε_s = ε_a = ε$ and a shared designated converter $a = b = bot$
at the same Eve interface gives both conditions of @maurer2011cc Def. 3 at the
compiled honest boundary; distinct typed converters give resource-specific modes.
The qualitative $sans("SecureConstruction")$
uses behavioural equality for availability and $leUC$ for security, and is
equivalent to the two-error predicate at $(0, 0)$.
#srcs(cc("UC/RandomSystems/Availability.agda", 38, "no-adversary"), cc("UC/RandomSystems/Availability.agda", 55, "SecureConstruction"), cc("UC/RandomSystems/Availability.agda", 61, "SecurelyConstructs"), cc("UC/RandomSystems/Availability.agda", 67, "SecureConstruction⇔SecurelyConstructs₀"))
] <def:full-constructs>

Full _replacement transitivity_ adds security and availability errors separately,
provided the designated converters on the intermediate resource are behaviourally equal
(`securely-constructs-trans`). This is not a general serial/parallel honest-protocol
composition theorem for availability. A simulator factoring suffices when composing it
with the real no-adversary converter preserves the designated ideal mode
(`secure-construction-factor`).
The mode-bit consumer proves a forced-true
nonidentity simulator with the same designated mode on both sides, also proves
compatibility for bit-flipping converters with resource-specific modes, exercises
composition twice, and rejects full construction for a forced-false simulator,
despite zero security error.
#srcs(cc("UC/RandomSystems/Availability.agda", 94, "secure-construction-factor"), cc("UC/RandomSystems/Availability.agda", 118, "securely-constructs-trans"), cc("Examples/RandomSystems/Availability.agda", 206, "not-full₀"), cc("Examples/RandomSystems/Availability.agda", 210, "forced-true-full"), cc("Examples/RandomSystems/Availability.agda", 233, "twice-full₀"))

The records do not add AB-converter syntax, normalization, termination, query bounds or
computational feasibility. The existing HashForward proof is also transported to actual #RS
security-only construction; no HashForward availability theorem is asserted.
Not covered #design: availability-qualified serial/parallel honest-protocol composition,
and a separate parallel security-construction theorem. The required braiding already exists
in the sealed G-construction (#cc("UC/Model/Symmetric.agda", 37, "𝔾ˢ")); its existence alone
is not that theorem. Amplification (@maurer2007) needs conditional probabilities and minima
of masses not supplied by the lower-real API. @sec:qrs gives exact-$ε$ security-only construction.

== #Wsub and #PMwb: well-bracketed machines <sec:wb>

These three setups share well-bracketed computations but distinguish full #PM testing, restricted
closures and the observational quotient. They connect to #SSP's call/return discipline (@sec:ssp).
For an oracle signature $A$ (@def:signature), its _flattening_ $op("flat") A$ is the #PM interface
whose upward messages are channel-tagged replies $Σ_c R_A (c)$ and whose downward messages are
channel-tagged queries $Σ_c Q_A (c)$.

#definition(name: [well-bracketed machine])[
A machine $f : op("flat") A → op("flat") B$ is at any time in one of three _phases_: $op("idle")$;
$op("serving") b$ (a query on $b ∈ sans("Ch")_B$ is open); $op("calling") (b, a)$ (it called $a ∈ sans("Ch")_A$
on behalf of $b$). The environment's legal moves are a query on $b$ when idle (to $op("serving") b$) and
a reply on $a$ when $op("calling") (b, a)$ (to $op("serving") b$); the machine's legal moves from
$op("serving") b$ are a call on some $a$ (to $op("calling") (b, a)$) and an answer on $b$ (to $op("idle")$).
$f$ is _well-bracketed_ if some invariant on (state, phase) holds initially at $op("idle")$ and, from any
state satisfying it, every legal environment move leads — on the support of the step, at every
finite depth — to a legal move of $f$ into a state satisfying it again.
#srcs(cc("UC/Bracket.agda", 50, "Phase"), cc("UC/Bracket.agda", 57, "Opp"), cc("UC/Bracket.agda", 62, "Ply"), cc("UC/Bracket.agda", 70, "W"))
] <def:wb>

This is a partial-response extension of CryptHOL's respectfulness (@lochbihler2019cc, Def. 3).
It is conditional safety under legal opponent moves, not a monitor enforcing legality against
hostile contexts. Divergent initialization, an always-diverging reply or an infinite internal
call chain can satisfy it; no liveness or probability-one return follows.

#theorem(name: [closure of well-bracketedness])[
Compiled #SSP packages are well-bracketed; so are the identity (copycat) and every relabelling wire
that returns on the queried channel. Well-bracketed machines are closed under the composition of #PM
(collapsed to a single traced machine, which is $eqM$-equal to the composite) and under the
channel-dispatching tensor, which is $eqM$-equal to #PM's tensor conjugated by the relabellings
$φ : op("flat") A ⊗ op("flat") C ≅ op("flat") (A ⊗ C)$.
#srcs(cc("UC/Bracket.agda", 120, "morphism-W"), cc("UC/Bracket.agda", 128, "id-W"), cc("UC/Bracket.agda", 160, "wire-W"), cc("UC/Bracket/Category.agda", 103, "⊙-W"), cc("UC/Bracket/Category.agda", 50, "⊙≈∘"), cc("UC/Bracket/Tensor.agda", 154, "⊗ʷ-W"), cc("UC/Bracket/Tensor.agda", 206, "conj≈⊗ʷ"))
] <thm:wb-closure>

#definition(name: [#Wsub, #Wio, #WW])[
$cal(W)$ has oracle signatures as objects; $cal(W)(A, B)$ consists of the #PM morphisms
$op("flat") A → op("flat") B$ that are $eqM$-equal to a well-bracketed machine; equality is $eqM$; the
monoidal structure is #PM's transported along the relabelling isomorphisms $φ$ and $υ : 0 ≅ op("flat") 1$.
The inclusion $ι : cal(W) → 𝔾^o$ is strong monoidal, neither full nor wide. Two observations:
$Wio := Std(cal(W), cal(E)^o ∘ ι^"op")$ (all #PM tests and closures), and $WW := Std(cal(W), cal(E)^W)$
with
$ cal(E)^W (A) = cal(W)(A, Ω) slash ≋, quad t ≋ t' :⟺ ∀ m ∈ cal(W)(1, A). thin Obs(t ∘ m) simA Obs(t' ∘ m), $
well-bracketed tests modulo well-bracketed closures, observed exactly as #PM observes them.
#srcs(cc("UC/Bracket/Monoidal.agda", 255, "Wᵒ"), cc("UC/Bracket/Monoidal.agda", 145, "Uᵂ"), cc("UC/Bracket/Monoidal.agda", 151, "φ"), cc("UC/Bracket/Monoidal.agda", 161, "υ"), cc("UC/Bracket/Monoidal.agda", 309, "𝒲ᴹ"), cc("UC/Bracket/Monoidal.agda", 312, "ιᴹ"), cc("UC/Bracket/Monoidal.agda", 318, "ι*ℰᵒ"), cc("UC/Bracket/Setup.agda", 59, "Obsᵂ"), cc("UC/Bracket/Setup.agda", 71, "ℰᵂ"), cc("UC/Bracket/Setup.agda", 75, "StdUC 𝒲ᴹ ℰᵂ"))
] <def:W>

Well-bracketedness reads the support of a step, which the equality $apx_p$ of laws does not preserve; this
is why $cal(W)$ takes the saturation "equal to a well-bracketed machine" as its morphisms.

#definition(name: [#PMwb])[
Let $simW$ be the two-sided ancilla kernel of $cal(E)^W$ (@prop:quotient(2)). Then
$PMwb := Std(cal(W) slash simW, cal(E)^W "descended")$.
#srcs(cc("UC/Bracket/Setup.agda", 88, "PM[wb]ᴹ"), cc("UC/Bracket/Setup.agda", 93, "∼⇒≋ᵂ"), cc("UC/Bracket/Setup.agda", 150, "ℰ[wb]"), cc("UC/Bracket/Setup.agda", 153, "StdUC PM[wb]ᴹ ℰ[wb]"))
] <def:pmwb>

The quotient changes neither the contexts nor the kernel, so emulation in #PMwb is emulation in #WW.
It is needed because the functor of a setup morphism must respect the _target's_ hom-equality: with
$eqM$ the compiled identity wire of #SSP is not the identity of #PM (@sec:non-morphisms), whereas
the checked call/return bridge proves it $simW$-equal to the identity (@def:mwb).

#proposition(name: [$ι$ carries the kernel both ways])[
$ι : Wio → PM$ is a standard morphism whose test map is the identity, Epi and Mono. Hence $f eqE g$ in
#Wio iff $ι f eqE ι g$ in #PM.
#srcs(cc("UC/Bracket/Monoidal.agda", 332, "ι⇒prot"), cc("UC/Bracket/Monoidal.agda", 326, "νι-epi"), cc("UC/Bracket/Monoidal.agda", 329, "νι-mono"))
] <prop:iota>

#proposition(name: [restriction of observations])[
There is a natural, componentwise-surjective map $ν_W : ι^* cal(E)^o → cal(E)^W$ on $cal(W)$.
The resulting change of kernel $mck_(ν_W) : Wio → WW$ composes with $mq : WW → PMwb$.
#srcs(cc("UC/Bracket/ObservationRestriction.agda", 56, "verdict-W"), cc("UC/Bracket/ObservationRestriction.agda", 134, "ν-restrict"), cc("UC/Bracket/ObservationRestriction.agda", 144, "ν-restrict-epi"), cc("UC/Bracket/ObservationRestriction.agda", 147, "restriction⇒wb"), cc("UC/Bracket/ObservationRestriction.agda", 150, "full⇒PM[wb]"))
] <prop:Wrestriction>

#proofidea[The verdict signature $Ω$ has one channel. For every process $op("flat") A → op("flat") Ω$,
take the invariant $I(s, φ) = ⊤$: after a legal input, every output is a legal call or an answer on that
sole channel. Thus every #PM verdict test can be repacked through the inverse verdict-respelling wire,
without a monitor or scheduler. Equality against all #PM closures implies equality against the
well-bracketed closures, associativity gives naturality, and respelling a well-bracketed test back gives
a preimage.]

The full-test setup #Wio and the restricted-closure setup #WW remain distinct. The reverse
underlying-test inclusion is not a setoid map: tests reacting differently to a wrong-channel return can
agree on every well-bracketed closure but disagree on an unrestricted one. This is an obstruction to
that representative inclusion, not to the forward observation coarsening.
The two forward paths form a fork
$ Wio → PM quad "and" quad Wio → WW → PMwb. $
They do not reverse to a path $SSP → PMwb → PM$: SSP confidentiality against legal closures
does not imply confidentiality against unrestricted PM contexts.

== #SSP: call/return packages <sec:ssp>

#definition(name: [oracle signatures])[
An _oracle signature_ $A = (sans("Ch")_A, Q_A, R_A)$ is a set of channels with decidable equality, each
with a query type $Q_A (c)$ and a reply type $R_A (c)$. $A ⊗ C$ has channels $sans("Ch")_A + sans("Ch")_C$; the
unit has none. A morphism of signatures $A ⇒ B$ maps channels and queries forwards and replies backwards
(a container morphism).
#srcs(cc("SSP/Iface.agda", 32, "Iface"), cc("SSP/Iface.agda", 42, "_⊗ᴵ_"), cc("SSP/Iface.agda", 46, "_⇒ᴵ_"), cc("SSP/Iface.agda", 112, "flat"))
] <def:signature>

#definition(name: [packages])[
$sans("Calls")_A (X)$ is the set of finite trees with leaves $op("ret") x$ and $op("dead")$ (abort) and
nodes $op("call") c thin q$ (branching on $R_A (c)$) and $op("coin") μ$ (a rational law on $sans("Bool")$).
A _package_ $P : A → B$ — it imports $A$ and exports $B$ — is a state set $"St"$, an initial state, and
$ "step" : "St" → (c : sans("Ch")_B) → Q_B (c) → sans("Calls")_A ("St" × R_B (c)). $
$P_2 ∘ P_1$ inlines $P_1$'s steps at the calls of $P_2$ (@brzuska2018, Def. 4); the identity is the wire
forwarding each query; $P ⊗ P'$ serves a query with the factor owning its channel and replies on that
channel, so control stays one thread; shared imports are $(P ⊗ P') ∘ ⌜∇⌝$. Equality $eqP$ is the
equivalence closure of _simulations_: functions $θ : "St" → "St"'$ preserving the initial state and
carrying each step tree to the corresponding one, trees compared syntactically ($apx_c$). This is a
symmetric monoidal category.
#srcs(cc("SSP/Protocol.agda", 37, "Calls"), cc("SSP/Protocol.agda", 116, "Protocol"), cc("SSP/Protocol.agda", 138, "_∘ᵖ_"), cc("SSP/Protocol.agda", 148, "wireᵖ"), cc("SSP/Protocol.agda", 153, "_⊗ᵖ_"), cc("SSP/Protocol.agda", 58, "_≈ᶜ_"), cc("SSP/Protocol.agda", 166, "_≲ᵖ_"), cc("SSP/Protocol.agda", 182, "_≈ᵖ_"), cc("SSP/Protocol/Category.agda", 109, "Prot"), cc("SSP/Protocol/Monoidal.agda", 232, "Protᴹ"), cc("SSP/Protocol/Monoidal.agda", 277, "Protˢ"))
] <def:packages>

#definition(name: [#SSP])[
$Ω$ has one channel with query $1$ and reply $sans("Bool")$. A _game_ is a package $G : 1 → A$, a
_distinguisher_ one $D : A → Ω$. A closed $W : 1 → Ω$ is read as the finite subdistribution
$op("run")(W) ∈ sans("Dist")_⊥ (sans("Bool"))$ obtained by multiplying out the coins (aborts are missing
mass); laws are compared on both verdict masses. Then
$ cal(E)^p (A) = SSP(A, Ω) slash ≋, quad D ≋ D' :⟺ ∀ G : 1 → A. thin op("run")(D ∘ G) simA op("run")(D' ∘ G), $
and $SSP := Std(sans("Prot"), cal(E)^p)$. So $eqE$ is perfect indistinguishability in every game
context (@brzuska2018 Def. 8 at $ε = 0$).
#srcs(cc("SSP/Observation.agda", 45, "evalC"), cc("SSP/Observation.agda", 57, "runᵖ"), cc("SSP/Observation.agda", 69, "Approximation⊥"), cc("SSP/Observation.agda", 88, "evaluationᵖ"), cc("SSP/Setup.agda", 22, "ℰᵖ"), cc("SSP/Setup.agda", 23, "StdUC Protᴹ ℰᵖ"))
] <def:ssp>

In the grade reading a protocol $A → X ⊗ B$ also exports adversary oracles $X$, and a simulator is a
package plugged on them. The flat interface of #PM is the one-channel case; channels are what lets
the tensor answer each query on the channel it was asked on.

#theorem(name: [state-separating reasoning])[
Write $G_0 scripts(≈)_ε G_1$ when every distinguisher reads the two games within $ε$. Then
$G_0 scripts(≈)_ε G_1 scripts(≈)_δ G_2 ⇒ G_0 scripts(≈)_(ε + δ) G_2$ (@brzuska2018 Lemma 5);
$op("run")((D ∘ M) ∘ G) = op("run")(D ∘ (M ∘ G))$ (the reduction lemma, Lemma 6); and
$G_0 scripts(≈)_ε G_1 ⇒ M ∘ G_0 scripts(≈)_ε M ∘ G_1$.
#srcs(cc("SSP/Reduction.agda", 43, "_≈ᵍ[_]_"), cc("SSP/Reduction.agda", 47, "≈ᵍ-trans"), cc("SSP/Reduction.agda", 52, "reduction"), cc("SSP/Reduction.agda", 57, "≈ᵍ-reduce"))
] <thm:ssp-lemmas>

#proposition(name: [closed bridge])[
For _closed_ protocols $f, g : 1 → X ⊗ B$, $f eqE g ⇒ f eqU g$, without grade stability; in particular
perfectly indistinguishable games are U-equivalent.
#srcs(cc("SSP/Reduction.agda", 105, "closed-bridge"), cc("SSP/Reduction.agda", 112, "≈ᵍ⇒≈ᵁ"))
] <prop:closed-bridge>

#proofidea[An ancilla closure $m : 1 → Y ⊗ 1$ slides past a closed protocol by naturality,
interchange and $λ_1 = ρ_1$, leaving one test of the protocol alone. The argument is valid in any
standard setup whose closures start at the unit.]

#theorem(name: [the one-time pad])[
In #SSP let $op("aut")$ be the authenticated channel (Eve reads the message and cannot change it),
$op("ideal")$ the secure channel (Eve learns only that a message was sent), $op("key")$ a uniform key
drawn when first fetched, and $op("otp")$ the encryption and decryption converters sharing the key,
composed with $op("aut")$ and $op("key")$ (@maurer2011cc §3.2–3.3; @brzuska2018 Def. 9). Then
$op("otp") leUC op("ideal")$, with the simulator "on Eve's first poll after a send, draw a uniform
ciphertext and keep it". Moreover $op("ideal") leUC op("aut")$ and $op("otp") leUC op("aut")$ (leakage
may be added), while $op("aut") ≰_"UC" op("ideal")$.
#srcs(cc("Examples/SSP/OneTimePad.agda", 90, "aut"), cc("Examples/SSP/OneTimePad.agda", 94, "ideal"), cc("Examples/SSP/OneTimePad.agda", 97, "key"), cc("Examples/SSP/OneTimePad.agda", 132, "otp"), cc("Examples/SSP/OneTimePad.agda", 136, "sim"), cc("Examples/SSP/OneTimePad.agda", 263, "otp≤ideal"), cc("Examples/SSP/OneTimePad.agda", 319, "ideal≤aut"), cc("Examples/SSP/OneTimePad.agda", 322, "otp≤aut"), cc("Examples/SSP/OneTimePad.agda", 332, "relay≤aut"), cc("Examples/SSP/OneTimePad.agda", 379, "leaky-not-secure"))
] <thm:otp>

#proofidea[$op("otp")$ inlines to a single package $op("real")$, and the simulated ideal to a package
$op("simulated")$, each by one simulation; $op("real")$ and $op("simulated")$ are perfectly
indistinguishable by a deferred-sampling induction over the distinguisher, with the bijection
$k ↦ m ⊕ k$ at Eve's poll; @prop:closed-bridge turns that into $eqU$, and dummy completeness concludes
#srcs(cc("Examples/SSP/OneTimePad.agda", 174, "otp≲real"), cc("Examples/SSP/OneTimePad.agda", 185, "ideal≲simulated"), cc("Examples/SSP/OneTimePad.agda", 260, "perfect")). For $op("aut") ≰_"UC" op("ideal")$: relabelling the message by negation is invisible to the
secure channel and turns one probe into the other, whatever the simulator.]

#proposition(name: [no tree simulation])[
For every simulator $s$, $op("otp") scripts(≉)_sans("p") opsub_s ∘ op("ideal")$: simulations compare coins syntactically,
and the key is drawn at Alice's send, whereas the simulated ideal can draw only at Eve's poll.
#srcs(cc("Examples/SSP/OneTimePad.agda", 299, "no-tree-simulation"))
] <prop:no-tree>

So the call/return discipline buys clean composition, not clean probabilistic reasoning at
$eqP$. The distributional quotient #SSPd makes the deferred-sampling step a hom-equation without
changing the tests or the security relation.

=== #SSPd: distributional state-separating proofs <sec:ssp-dist>

#definition(name: [the distributional quotient])[
For packages $P, P' : A → B$ define
$ P scripts(≈)^sans("d") P' :⟺ ∀ Y, Z. thin (opid_Y ⊗ P) ⊗ opid_Z eqE (opid_Y ⊗ P') ⊗ opid_Z. $
The two-sided ancillas allow the distinguisher and game to share oracles. This is a monoidal
congruence coarser than $eqP$ and contained in $eqE$. The same tests descend to the quotient:
$SSPd := Std(sans("Prot") slash scripts(≈)^sans("d"), cal(E)^sans("d"))$.
#srcs(cc("SSP/Dist.agda", 37, "_≈ᵈ_"), cc("SSP/Dist.agda", 54, "congᵈ"), cc("SSP/Dist.agda", 65, "≈ᵈ⇒≋"), cc("Standard2/UKernel.agda", 101, "uKernel"), cc("SSP/Dist/Setup.agda", 26, "Protᵈ"), cc("SSP/Dist/Setup.agda", 29, "ℰᵈ"))
] <def:ssp-dist>

#theorem(name: [deferred sampling in #SSPd])[
The OTP and its simulated ideal are hom-equal in #SSPd. Hence
$op("otp") leUC op("ideal")$ in this setup, with the same simulator as @thm:otp. For every
adversary $a$ the simulator is $a ∘ op("sim")$, and the target prefix-context verdicts agree
for every ancilla, distinguisher and game. The authenticated channel still does not realize the
secure one: $op("aut") ≰_"UC" op("ideal")$, and no simulator gives target U-equivalence.
#srcs(cc("Examples/SSP/OneTimePad/Dist.agda", 95, "otp≈idealᵈ"), cc("Examples/SSP/OneTimePad/Dist.agda", 106, "otp≤ideal-dist"), cc("Examples/SSP/OneTimePad/Dist.agda", 112, "otp-simulator-dist"), cc("Examples/SSP/OneTimePad/Dist.agda", 116, "otp-observations-dist"), cc("Examples/SSP/OneTimePad/Dist.agda", 124, "leaky-not-secure-dist"), cc("Examples/SSP/OneTimePad/Dist.agda", 127, "leaky-no-simulator-dist"))
] <thm:otp-dist>

#proofidea[A sampling kernel per state commutes with each activation against every import oracle.
It gives a padded-protocol equation by readout. In the pad example, deferred sampling reduces to
nine per-activation squares: six computations, two pad cancellations and one fair-coin bijection.
The impossibility crosses by reflection of security, not by one-way preservation
(@prop:ssp-dist-morphism).]

The example is passive and reliable: a one-bit, first-send-only pollable-state channel with finite
rational call trees. Bob can read the stored message without Eve authorizing delivery; there is no
drop/corruption command. It does not establish general SSProve samplers, reentrant activations,
asynchronous delivery control or resource-sensitive security. The unrestricted SSP/QRS bounds
quantify all admitted tests, not a fixed query budget or an adversary-indexed advantage.

== #ITM and #ITMiso: interactive Turing machines <sec:itm>

#definition(name: [#ITM])[
A _port interface_ is a finite binary tree whose leaves are ports of polarity $+$ (answers going out) or
$-$ (queries coming in), each carrying bitstrings. A generator $A → B$ is a finite-table Turing machine
reading the ports $A^+ + B^-$ and writing $A^- + B^+$: finitely many control states, a work tape that
persists across activations, an input tape holding the activation's message and an output buffer;
its instructions write and move, toss a fair coin, or _send_ on a port, which ends the activation.
$𝕋$ is the free monoidal category on these generators: morphisms are terms built from generators,
identities, composition, tensor and the structural isomorphisms, modulo the free monoidal congruence
$apx_"Term"$. Its interpretation $F^p : 𝕋 → 𝔾^o$ is the strict monoidal free functor whose leaves run
their table: an activation iterates the table lookup (Elgot iteration) until it sends, coins are fair
coins, and an activation that never sends diverges. $ITM := Std(𝕋, cal(E)^o ∘ (F^p)^"op")$: a test
on ports is a #PM test on their interpretation.
#srcs(cc("ITM/Core.agda", 47, "Ports"), cc("ITM/Core.agda", 154, "Instr"), cc("ITM/Core.agda", 159, "TM"), cc("ITM/Core.agda", 164, "Gen"), cc("ITM/Core.agda", 206, "𝕋ᴹ"), ag("Categories/FreeMonoidal.agda", 141, "_≈Term_"), cc("ITM/Run.agda", 46, "runᵀᴹ"), cc("ITM/Run.agda", 62, "runᴾ"), cc("ITM/Functor.agda", 65, "Fᴾ"), ag("Categories/FreeMonoidal.agda", 519, "freeStrongMonoidal"), cc("ITM/Setup.agda", 36, "ℰᵀ"), cc("ITM/Setup.agda", 39, "StdUC 𝕋ᴹ ℰᵀ"))
] <def:itm>

A system is a term, never a product table, so $F^p (g ∘ f) = F^p g ∘ F^p f$ holds by definition.
This is a static-port, always-reply fragment motivated by @canetti2020uc and @kusters2020iitm,
not an established correspondence to either full model. Silent deactivation/master reactivation,
dynamic instances, SID routing and adaptive corruption are not instructions of this fragment.
A change of test kernel or a wide subcategory alone cannot add these transitions, so no GNUC/iUC
identification (@hofheinz2015gnuc; @camenisch2019iuc) is asserted.

#definition(name: [#ITMiso])[
$F^r : 𝕋 → Iso$ is the strict monoidal free functor into the relational machines of @sec:iso (whose
tensor is reversed, so trees are read mirrored) that reads a leaf as its _halting relation_: from
memory $m$ and input $x$ the activation can end with output $y$ in memory $m'$; coins become
nondeterministic choice, divergence has no transition, and the initial memory is forgotten.
$ITMiso := Std(𝕋, cal(E)^≅ ∘ (F^r)^"op")$.
#srcs(cc("ITM/Relational.agda", 51, "Halts"), cc("ITM/Relational.agda", 113, "leafᴿ"), cc("ITM/Relational.agda", 117, "Fᴿ"), cc("ITM/Relational.agda", 122, "ℰᴵˢᵒ"), cc("ITM/Relational.agda", 125, "StdUC 𝕋ᴹ ℰᴵˢᵒ"))
] <def:itmiso>

The two observations on $𝕋$ must remain distinct: #ITMiso forgets the start memory, probabilities
and divergence mass, but retains unreachable and redundant states in whole-composite isomorphism.
It is neither initialized trace security nor a probability-preserving abstraction of #ITM.
The unrestricted claim that no natural map can relate the presheaves is too strong:
mapping every test to an empty-state relational environment gives a degenerate constant natural
map #design. That map is not Epi/Mono and supplies no useful security correspondence.

#theorem(name: [the kernel of #ITM is that of #PM])[
For parallel $f, g$ in $𝕋$: $f eqE g$ in #ITM iff $F^p f eqE F^p g$ in #PM.
#srcs(cc("ITM/Setup.agda", 57, "≈ℰ⇔"))
] <thm:itm-kernel>

Here emulation is perfect and unbounded, despite each generator having a finite table. The pulled-back
#PM environments need not have computable source realizers. Intrinsic ITM tests need a context/density
theorem. #design Polynomial running time is not generally a composition-closed property of these
morphisms (@hofheinz2013, §1.5); computational UC additionally needs uniform security-parameter
families, admissibility quantifiers and their composition laws, not just a finite program.

#theorem(name: [an initialized probabilistic #ITM client])[
#formal Let `Service` be a signed request/reply interface. The four-state tables
$"real", "ideal" : I → "Service" ⊗ "Service"$ start from their designated blank memories,
return a fresh fair bit on each honest request, and return respectively true or false on
the adversarial service. A two-state source simulator $s : "Service" → "Service"$ normalizes
adversarial requests to the empty bitstring and rewrites their replies to `[true]`, leaving
the honest service untouched. In the actual #ITM setup,
$ "real" eqU (s ⊗ opid) ∘ "ideal", quad "real" leUC "ideal". $
The first claim uses this explicit simulator; dummy completeness gives the second for every
source adversary, not merely for a chosen observation.
#srcs(cc("Examples/ITM/Tables.agda", 81, "resource"), cc("Examples/ITM/Tables.agda", 169, "simulator"), cc("Examples/ITM/Tests.agda", 41, "explicit-simulator"), cc("Examples/ITM/Tests.agda", 44, "secure"))
] <thm:itm-client>

#proofidea[Point-preserving simulations relate the initialized table executions and their
composite. The resulting compiled hom-equality survives every source prefix and every
pulled-back test/closure by `≈ᴾ⇒≈ᵁ`. This route does not assume PM grade stability and does
not establish a general security-transfer theorem from #ITM to #PM.
#srcs(cc("Examples/ITM/Tables.agda", 145, "resource-correct"), cc("Examples/ITM/Tables.agda", 203, "simulator-correct"), cc("Examples/ITM/Interpretation.agda", 62, "compiled-correct"), cc("ITM/Setup.agda", 63, "≈ᴾ⇒≈ᵁ"))]

A concrete source `Env` distinguishes the two unsimulated marker observations through `pull`:
the closed real and ideal verdicts are respectively true and false. Thus
$¬("real" eqE "ideal")$ and $¬("real" eqU "ideal")$; installing the simulator changes
observations, and its source arrow is not identity. These are _observational negatives_,
not a no-simulator or non-emulation theorem: the positive $leUC$ result above holds.
The honest consumers check one fair reply and a two-reply comparison with the law of
two independent fair draws.
#srcs(cc("Examples/ITM/Tests.agda", 38, "marker-environment"), cc("Examples/ITM/Tests.agda", 54, "marker-pull-distinct"), cc("Examples/ITM/Tests.agda", 58, "initialized-distinct"), cc("Examples/ITM/Tests.agda", 61, "initialized-distinctᵁ"), cc("Examples/ITM/Tests.agda", 64, "simulation-observable"), cc("Examples/ITM/Tests.agda", 67, "simulator-nonidentity"), cc("Examples/ITM/Interpretation.agda", 92, "honest-coin"), cc("Examples/ITM/Interpretation.agda", 95, "honest-independent"))

This is a finite static-table service under perfect, unrestricted PM-pullback tests, not
encryption/secrecy, PPT or negligible security, dynamic ITI creation, adaptive corruption,
or full IITM correspondence. It neither changes the always-reply instruction set nor
completes the separately ongoing initialized _relational_ interpretation.

== #Sym and #Symiso: the Dolev–Yao model <sec:sym>

#definition(name: [#Sym, #Symiso])[
$𝔻 𝕐$ is the free monoidal category on _Dolev–Yao roles_ — finite reactive programs whose outputs are
recipes over their own frame (the roles of @canettiherzog2006), between unit-free trees of term
ports — with the free monoidal congruence as hom-equality. A test on $A$ is a pair $(Y, T : Y ⊗ A →
Ω)$ of an ancilla and a role circuit, as in #Iso but with the ancilla on the grade side. In #Symiso two
tests are equal when their circuits are. In #Sym they are equal when every closure allows the same
verdicts, each possible verdict being the answer of the closed run in #PM at term alphabets under
some globally fresh naming: every generator occurrence draws its names from a supply of its own,
and the supplies are injective.
#srcs(cc("Symbolic/Role.agda", 203, "Role"), cc("Symbolic/Fine.agda", 41, "𝔻𝕐"), cc("Symbolic/Fine.agda", 71, "ℰ≅"), cc("Symbolic/Fine.agda", 74, "StdUC 𝔻𝕐 ℰ≅"), cc("Symbolic/Semantics.agda", 92, "runᴿ"), cc("Symbolic/Semantics.agda", 114, "eval"), cc("Symbolic/Semantics.agda", 123, "eval-cong"), cc("Symbolic/Setup.agda", 102, "ℰˢʸᵐ"), cc("Symbolic/Setup.agda", 105, "StdUC 𝔻𝕐 ℰˢʸᵐ"))
] <def:sym>

#theorem(name: [the kernel of #Sym])[
(1) #Sym is grade-stable without hypotheses, so $f eqU g$ iff $f eqE g$. (2) Roles emit and store
canonical forms of a convergent theory $E$, so two programs of one shape whose recipes agree modulo
$E$ on every frame are $eqE$-equal generators.
#srcs(cc("Symbolic/Setup.agda", 123, "grade-stable"), cc("Symbolic/Setup.agda", 129, "≈ᵁ⇔≈ℰ"), cc("Symbolic/Role.agda", 495, "exec-≈E"), cc("Symbolic/Setup.agda", 146, "emit-≈E"))
] <thm:sym-kernel>

The kernel of #Sym is fixed-circuit deterministic token-passing may-testing. It is not a proved
identification with applied-pi contextual bisimulation or Böhl–Unruh symbolic UC
(@abadi2018applied; @bohlunruh2013): races, dynamic replication and independent live-session
routing need actual encodings and context theorems. Growing terms do not by themselves supply
that machinery. #Symiso, in contrast, observes syntax and is a proof/interpretation IR.

*Admissible equations and freshness.* #formal `EqTheory.subst-cong` requires arbitrary
sort-preserving _name-to-term_ substitution, `Substitution = ∀ {s} → Name → Tm s`, not just
renaming. Uniform and sort-indexed renaming congruence follow. With per-sort nontriviality,
`fresh-name` forbids a name being equal to a term in which it does not occur; `name-injective`,
recipe non-deducibility and `Run.emits≉fresh` lift this to unowned names absent from the
exposed/received frame. The checked collapse tests refute the old renaming-only countertheory
as an admissible `EqTheory`; E₀ satisfies the stronger contract.
#srcs(cc("Symbolic/Term.agda", 67, "Substitution"), cc("Symbolic/Term.agda", 274, "subst-cong"), cc("Symbolic/Term.agda", 290, "fresh-name"), cc("Symbolic/Term.agda", 298, "name-injective"), cc("Symbolic/Deduction.agda", 87, "⊬-fresh"), cc("Symbolic/Role.agda", 463, "emits≉fresh"), cc("Symbolic/TheoryTests.agda", 102, "collapse-not-EqTheory"))

Literal absence is important: a key occurring inside a ciphertext is not absent, so this is
not ciphertext secrecy or a concrete nonce-guessing bound. Raw name codes and ownership remain
unsorted; one owned code can be used at two sorts, and `Own κ` conservatively grants all
counters at occurrence $κ$, including not-yet-allocated ones. Sorted substitution is not a
sorted-name representation migration. Static frame equality also excludes every occurring name
via `Foreign`, rather than carrying an independent restriction list. It is a private-frame
interface, not the full public/restricted-name frame theory of @abadi2018applied.
#srcs(cc("Symbolic/TheoryTests.agda", 134, "owned-at-two-sorts"))

*Ground guards are not termination.* #formal The weaker predicate formerly called `Simple`
is `GroundGuarded`: guard failure reaches ground payload/control conditions, without a single
fixed output or input independence. A distinct opt-in `Terminal p err` fixes the terminal
control and closed error emission. Its `step-terminal`/`run-terminal` runtime enters an
absorbing stopped state; derived trace results give a silent suffix after the terminal jump
and the complete single-emission trace. Checked forwarding/guard consumers separate these
contracts. The original total `Run.exec`/`step` and #Symiso's arbitrary role generators are
unchanged; neither `GroundGuarded` nor `Terminal` is automatically enforced by Fine.
This is not the missing CLC/applied-pi correspondence (@comonlundhcortier2008 §3.3).
#srcs(cc("Symbolic/Role.agda", 234, "GroundGuarded"), cc("Symbolic/Role.agda", 269, "Terminal"), cc("Symbolic/Role.agda", 353, "step-terminal"), cc("Symbolic/Role.agda", 367, "run-terminal"), cc("Symbolic/Role.agda", 381, "terminal-jump-no-further-behavior"), cc("Symbolic/Role.agda", 396, "terminal-transition-trace"), cc("Symbolic/TerminalTests.agda", 49, "forwarding-not-terminal"), cc("Symbolic/Fine.agda", 36, "symData"))

#theorem(name: [static equivalence of frame emitters])[
For every signature and admissible convergent theory, statically equivalent frames have $eqE$-equal emitters.
For the single-sorted pairing/symmetric-encryption theory $E_0$, the converse also holds:
two frame emitters are $eqE$-equal iff their frames are statically equivalent at every name supply.
#srcs(cc("Symbolic/Static.agda", 175, "≈ₛ⇒≈ℰ"), cc("Symbolic/Static/PairEnc.agda", 28, "≈ℰ⇔≈ₛ"), cc("Symbolic/StaticTests.agda", 23, "empty-kernel"), cc("Symbolic/StaticTests.agda", 30, "two-port-kernel"))
] <thm:sym-static>

#proofidea[The same-recipe relation is a span through an apex machine. Its point and step are
couplings; pure projections make feedback preserve the span, and G-composition and tensor carry it
through every role context. Conversely, an $E_0$ tester queries all frame ports, draws its own names
for the recipes' foreign names, and compares them. A non-injective renaming restores the foreign
names after the possible run changes its existential naming.
#srcs(cc("Machines/Sim/Relational.agda", 255, "RelSim"), cc("Machines/Sim/Relational.agda", 290, "trace-relsim"), cc("UC/Machine/Relational.agda", 252, "HSim-∘"), cc("Symbolic/Static/Distinguish/Run.agda", 160, "run"), cc("Symbolic/Static/Distinguish.agda", 146, "≈ℰ⇒≈ₛ"))]

The generic relational simulation contract now requires pure input and output interface legs
as well as the state leg; trace carries explicit purity of every projection it uses. In
$"Kl"(Dp)$ this gives deterministic marginal pushforwards from a shared random apex, retaining
genuine nonidentity spans. The checked fair-coin-interface example is excluded rather than
misdescribed as an ordinary coupling. Abstract `PureSub` alone is a pure-square contract,
not a theorem that every base category is probabilistic. The static and E₀ theorem statements
are unchanged by this repair.
#srcs(cc("Machines/Sim/Relational.agda", 150, "_≲[_∣_]_"), cc("Symbolic/Static/Relational.agda", 121, "proc-rel"))

The multi-sort converse is not established for admissible theories. Raw names and ownership remain
unsorted, but `EqTheory.subst-cong` requires arbitrary sort-preserving name-to-term substitution.
The historical cross-sort-sharing obstruction fails that closure and does not refute a converse for
this class. The supported contract, checked fresh-name-collapse rejection, and exact remaining scope
are in #plan("uc-setup-symbolic.md") §3.2 and §3.7; the theorem above has no added assumption on $E_0$.

#theorem(name: [fixed-public-message ciphertext opacity])[
For a public constant $n$, the protocol $"smt"(n)$ gives its honest receiver $n$ and Eve a
fresh symmetric ciphertext of $n$. The ideal gives the same honest answer and has a void
Eve interface. In #Sym, $"smt"(n) leUC "ideal"(n)$, witnessed by the non-identity simulator
that emits a fresh encryption of $0$ independently of the honest wire.
#srcs(cc("Symbolic/Example/SecureChannel.agda", 68, "honest"), cc("Symbolic/Example/SecureChannel.agda", 71, "simulator"), cc("Symbolic/Example/SecureChannel.agda", 74, "smt"), cc("Symbolic/Example/SecureChannel.agda", 77, "ideal"), cc("Symbolic/Example/SecureChannel.agda", 111, "smt≤ideal"), cc("Symbolic/StaticTests.agda", 39, "regression"))
] <thm:sym-channel>

#proofidea[The ciphertext frame span is carried beside the unchanged honest emitter by the
relational tensor theorem and the apex context construction. Tensor interchange identifies
the simulated protocol with the simulator plugged into the ideal. Grade stability and dummy
completeness (@thm:metatheory(2)) conclude. The honest output and ciphertext are independent
emitters for a message fixed at the definition site; no receiver consumes/decrypts an adversarial
ciphertext. Tensor factorization alone would realize this ideal even with the real emitter as
simulator (or with plaintext leakage). The nontrivial result is the common encryption-of-zero
simulator and associated static opacity, not environment-selected-message transmission, delivery
acceptance or a cryptographic secure-channel construction.]
#srcs(cc("Symbolic/Static.agda", 160, "emitter-emits"), cc("Symbolic/Static/Relational.agda", 151, "context"))

== #Iso: relational machines up to isomorphism <sec:iso>

#definition(name: [#Iso])[
Objects are _channels_ $(sans("in"), sans("out"))$ of sets, with componentwise disjoint union. A
machine $A → B$ is a state set $S$ and a step relation $S × sans("In") × (sans("Out") + 1) × S$ on the
transposed channel: nondeterministic, possibly silent, and without initial state. Composition lets
internal messages bounce between the two machines (an inductive ping-pong relation) until an
external output or silence. The hom-equality $isoM$ is a bijection of state sets that preserves and
reflects steps. The tensor is reversed, so the grade sits on the right: $T_X B = B ⊗ X$. A test on $A$
is a pair $(Y, E)$ of an ancilla $Y$ and an environment $E : A ⊗ Y → Ω$ (which outputs a bit); two tests
are equal when their ancillas coincide and their environments are $isoM$-isomorphic.
$Iso := Std(sans("Mach")^"rev", cal(E)^≅)$.
#srcs(cc("Channel/Core.agda", 33, "Channel"), cc("Machine/Core.agda", 26, "Machine"), cc("Machine/Core.agda", 146, "TraceRel"), cc("Machine/Iso.agda", 28, "_≅ᴹ_"), cc("Machine/UC.agda", 109, "machines"), cc("Machine/UC.agda", 59, "Test"), cc("Machine/UC.agda", 62, "SameTest"), cc("Machine/UC.agda", 91, "ℰ-tests"), cc("Machine/UC.agda", 114, "StdUC machines ℰ-tests"))
] <def:iso>

Because the equality is isomorphism, $f leUC g$ in #Iso asserts _isomorphic_ composites under every
environment, which is stronger than indistinguishability; a failure of it is not an attack.

#theorem(name: [#Iso is grade-stable])[
#Iso is grade-stable: a test with ancilla $Y$ on $B ⊗ Z$ regroups into a test with ancilla $Z ⊗ Y$ on $B$.
Hence $eqU = eqE$ in #Iso, and with the trivial ancilla $eqE$ refines isomorphism under every
environment.
#srcs(cc("Machine/UC.agda", 164, "grade-stable"), cc("Machine/UC.agda", 173, "≈ᵁ⇔≈ℰ"), cc("Machine/UC.agda", 130, "≈ℰ⇒≅ℰ"))
] <thm:iso-gs>

#proposition(name: [isomorphism is finer than bisimilarity])[
The identity machine with one redundant bit of state is not $isoM$-isomorphic to the identity.
#srcs(cc("Machine/Iso.agda", 50, "padded-not-iso"))
] <prop:padded>

== #Rel: relations <sec:rel>

#definition(name: [#Rel])[
$Rel := Std((sans("Rel"), ×, 1), op("Hom")(-, 1))$: sets and relations under the cartesian product; a
test on $B$ is a subset of $B$, restricted along relations by preimage. A protocol $A → X × B$ relates
inputs to (leakage, output) pairs.
#srcs(cc("Examples/RelSetup.agda", 31, "Rel"), cc("Examples/RelSetup.agda", 35, "ℰ-tests"), cc("Examples/RelSetup.agda", 38, "StdUC Rel ℰ-tests"))
] <def:rel>

#theorem(name: [#Rel is faithful])[
The test presheaf of #Rel is faithful. Hence #Rel is grade-stable, $eqU$ is equality of relations, and
$f leUC g$ iff $f = (s × opid) ∘ g$ for some relation $s$ (possibilistic simulation).
#srcs(cc("Examples/RelSetup.agda", 50, "ℰ-faithful"), cc("Examples/RelSetup.agda", 67, "≈ᵁ⇒≈"), cc("Abstract2.agda", 63, "≈C⇒≈ᵁ"), cc("Abstract2.agda", 171, "≤UCᵈ⇔≤UC"))
] <thm:rel-faithful>

#theorem(name: [possibilistic one-time pad])[
Encryption with a uniform key is the relation "any ciphertext" after discarding the message; the
one-time-pad channel emulates the ideal channel, emulation composes along relays, and leakage may
always be added; the relay leaking the message does not emulate the ideal channel.
#srcs(cc("Examples/RelSetup.agda", 94, "otp-perfect"), cc("Examples/RelSetup.agda", 130, "send≤ideal"), cc("Examples/RelSetup.agda", 143, "relayed-otp"), cc("Examples/RelSetup.agda", 146, "relayed-otp²"), cc("Examples/RelSetup.agda", 154, "ideal≤leaky"), cc("Examples/RelSetup.agda", 157, "send≤leaky"), cc("Examples/RelSetup.agda", 164, "leaky-not-secure"))
] <thm:rel-otp>

#theorem(name: [environment-blind robustness is incomplete])[
The leaky relay is outcome-included in the ideal channel, yet does not emulate it. Hence no level of
environment-blind robust property preservation implies $leUC$ (@thm:robust(2)).
#srcs(cc("Examples/RelSetup.agda", 187, "relay-outcomes"), cc("Examples/RelSetup.agda", 199, "blind-incomplete"))
] <thm:rel-blind>

#Rel is an implemented, separately connected possibilistic one-shot comparison component.
The cartesian functions-under-$×$ reading of Turing machines is only a design node, distinct from
the implemented ports-ITM syntax. No cross-component setup morphism is implemented here;
this is not a universal product-versus-interleaving obstruction. @sec:batch-island and
@sec:causal-island propose restricted stochastic-kernel/support routes into #Rel, with explicit
probability-loss and security-nonreflection boundaries.

== Quantitative setups: #QPM, #QRS and the security-parameter tiers <sec:qpm>

The setups so far identify two tests or two protocols outright. Cryptographic statements carry an
error, and the library keeps it in a quantitative variant of @def:setup.

#definition(name: [quantitative UC setup])[
Fix an ordered error algebra $(cal(R), ⊕, ε_0, ⊑)$; the examples use $(ℚ, +, 0, ≤)$ or functions
$ℕ → ℚ$ pointwise. A _quantitative UC setup_ $(cal(C), cal(I), cal(M), Q)$ is a UC setup whose test
presheaf is replaced by a presheaf $Q$ of _approximation spaces_: each $Q(A)$ carries relations
$e apx_ε e'$ that hold reflexively at $ε_0$, are symmetric and monotone in $ε$, and compose by
$e apx_ε e' apx_δ e'' ⇒ e apx_(ε ⊕ δ) e''$; restriction along $h$ is nonexpansive. The _U-agreement at $ε$_ is
$ f eqU_ε g :⟺ ∀ W ∈ cal(I), e ∈ Q(T_(W ⊗ X) B). quad oprun_W (f)(e) apx_ε oprun_W (g)(e), $
and a _witness at $ε$_ is a simulator $s$ with $f eqU_ε opsub_s ∘ g$; write $sans("Wit")_ε (f, g)$ if one
exists.
#srcs(cc("UC/Quantitative.agda", 40, "QUCSetup"), cc("UC/Quantitative.agda", 112, "_≈ᵁ[_]_"), cc("UC/Quantitative/Witness.agda", 41, "At"), cc("UC/Quantitative/Witness.agda", 45, "Witness"))
] <def:qsetup>

#theorem(name: [quantitative metatheory])[
In every quantitative UC setup:
+ $eqU_ε$ is reflexive at $ε_0$, symmetric, monotone, and $f eqU_ε g eqU_δ h ⇒ f eqU_(ε ⊕ δ) h$.
+ _Dummy adversary at a fixed error._ $sans("Wit")_ε (f, g)$ iff for every adversary $a$ there is a
  simulator $s$ with $opsub_a ∘ f eqU_ε opsub_s ∘ g$; the simulator is $a ∘ s_0$, independent of $ε$.
+ _Composition._ $sans("Wit")_ε (f, g)$ and $sans("Wit")_δ (g, h)$ give $sans("Wit")_(ε ⊕ δ) (f, h)$;
  $sans("Wit")_(ε_f) (f, g)$ and $sans("Wit")_(ε_u) (u, v)$ give $sans("Wit")_(ε_u ⊕ ε_f) (u ∙ f, v ∙ g)$, with
  simulator $(opid ⊗ t) ∘ (s ⊗ opid)$ as in @thm:metatheory.
+ _Forgetting the error._ Identifying tests at $ε_0$ gives a UC setup $𝕊_0$ in which
  $eqU thick ⟺ thick eqU_(ε_0)$ and $leUC thick ⟺ thick sans("Wit")_(ε_0)$. Identifying tests that are $ε$-close for every
  positive $ε$ gives a UC setup $𝕊_+$ in which $f eqU g$ iff $f eqU_ε g$ for every $ε > 0$, and
  $f leUC g$ iff _one_ simulator witnesses every $ε > 0$ (a simulator depending on $ε$ is not enough).
#srcs(cc("UC/Quantitative.agda", 117, "ctx-refl"), cc("UC/Quantitative.agda", 120, "ctx-sym"), cc("UC/Quantitative.agda", 123, "ctx-trans"), cc("UC/Quantitative.agda", 126, "ctx-mono"), cc("UC/Quantitative/Witness.agda", 53, "dummy⇒universal"), cc("UC/Quantitative/Witness.agda", 58, "universal⇒dummy"), cc("UC/Quantitative/Witness.agda", 66, "at-trans"), cc("UC/Quantitative/Witness.agda", 73, "at-compose"), cc("UC/Quantitative.agda", 55, "underlying₀"), cc("UC/Quantitative.agda", 58, "underlying₊"), cc("UC/Quantitative/Bridge.agda", 52, "zero-agreement"), cc("UC/Quantitative/Bridge.agda", 66, "zero-emulation"), cc("UC/Quantitative/Bridge.agda", 87, "positive-agreement"), cc("UC/Quantitative/Bridge.agda", 91, "Witness₊"), cc("UC/Quantitative/Bridge.agda", 105, "positive-emulation"), cc("UC/Quantitative/Bridge.agda", 111, "Witness₊⇒Witness"))
] <thm:qmetatheory>

Fixed positive-error closeness is not transitive at the same error, so it is not the hom-equality
of any setup; only its all-positive closure in (4) is. This is why a quantitative statement is kept
quantitative until the end and forgotten once.

=== #QPM: the protocol model with errors kept

#definition(name: [#QPM])[
For verdict laws $d, d' ∈ Dp sans("Bool")$, $d apx_ε d'$ iff each verdict mass of either law is dominated
by the other's up to $ε$ at every finite approximant (an _open_ slack: the masses are lower reals).
On tests, $e apx_ε e'$ iff $Obs(e ∘ m) apx_ε Obs(e' ∘ m)$ for every closure $m : 0 → A$. Then
$QPM := (𝔾^o, 𝔾^o, X ⊗ (-), Q^o)$, with $Q^o (A) = 𝔾^o (A, Ω)$ under these relations.
#srcs(ag("ProbabilisticLogic/Dp/Advantage.agda", 51, "_≈ₚ[_]_"), cc("UC/Quantitative/Observed.agda", 90, "_≈ᵗ[_]_"), cc("UC/Quantitative/Observed.agda", 110, "Q"), cc("UC/Quantitative/Observed.agda", 124, "QSetup"), cc("UC/Model/Quantitative.agda", 25, "QSetupᵒ"))
] <def:qpm>

#proposition(name: [#QPM forgets to #PM])[
(1) $f eqU_ε g$ iff for every ancilla $Y$, test $t$ on $Y ⊗ B$ and closure $m$ of $Y ⊗ A$, the runs
$Obs(t ∘ (opid ⊗ f) ∘ m)$ and $Obs(t ∘ (opid ⊗ g) ∘ m)$ are $ε$-close. (2) Two tests are equal in
$cal(E)^o$ iff they are $ε$-close for every $ε > 0$: $cal(E)^o$ is the all-positive forgetting of $Q^o$, and
$PM = QPM_+$ up to the order of the closure and error quantifiers. #instance Hence, by
@thm:qmetatheory(4) and @thm:refine in both directions, $f eqU g$ in #PM iff $f eqU_ε g$ in #QPM for every
$ε > 0$, and $f leUC g$ in #PM iff one simulator is a #QPM witness at every $ε > 0$.
#srcs(cc("UC/Quantitative/Observed.agda", 149, "≈ℰ[]⇔≈ᵁ[]"), cc("UC/Quantitative/Observed.agda", 167, "Q₊⇔ℰ₊"), cc("UC/Quantitative/Observed.agda", 191, "≋⇔∼₊"), cc("UC/Quantitative/Observed.agda", 182, "absorbᵘ"))
] <prop:qpm-forget>

=== #QRS: random systems with an exact error <sec:qrs>

The open slack of #QPM does not descend to $𝔾^R$: the hom-equality $eqR$ there is only the limit of
$Δ$ at zero (@prop:pseudometric), and an open bound at $ε$ is not invariant under it. Its _closure_ is:
$d scripts(≈̄)_ε d'$ iff $d apx_(ε + δ) d'$ for every $δ > 0$.

#definition(name: [#QRS])[
$QRS := (𝔾^R, 𝔾^R, X ⊗ (-), Q^R)$, with $Q^R (A) = 𝔾^R (A, Ω)$ and $e apx_ε e'$ iff
$Obs(e ∘ m) scripts(≈̄)_ε Obs(e' ∘ m)$ for every closure $m$.
#srcs(cc("Approx/Rational.agda", 49, "_≈̄[_]_"), cc("Approx/Rational.agda", 67, "closure"), cc("UC/RandomSystems/Quantitative.agda", 60, "spaceᴿ"), cc("UC/RandomSystems/Quantitative.agda", 63, "qevaluationᴿ"), cc("UC/RandomSystems/Quantitative.agda", 74, "QSetupᴿ"))
] <def:qrs>

#theorem(name: [security-only constructive cryptography at an exact $ε$])[
For #PM protocols $f, g$, read in $𝔾^R$:
+ $f eqU_ε g$ in #QRS iff $f eqR^ε g$: the U-agreement of #QRS is the advantage bound, with no slack spent.
+ $g$ has a #QRS witness at $ε$ for $f$, written $f leUC^ε g$, iff $sans("Constructs")_ε (f, g)$
  (@def:constructs; @maurer2011cc Def. 3 condition 2 at $ε$).
+ _Along_ $mrs$: a #QPM agreement (witness) at $ε$ gives a #QRS agreement (witness) at $ε$; and
  $f eqU_ε g$ in #QRS iff $f eqU_(ε + δ) g$ in #QPM for every $δ > 0$, $f leUC^ε g$ in #QRS iff one
  simulator is a #QPM witness at every $ε + δ$.
+ At $ε = 0$ it is emulation in #RS: $mrs(f) leUC mrs(g)$ iff $f leUC^0 g$.
+ (@maurer2011cc Thm. 1, security obligations at a slack.) $f leUC^0 f$; $f leUC^ε g leUC^(ε') h ⇒ f leUC^(ε + ε') h$; and
  $f leUC^ε g$, $u leUC^(ε') v$ give $u ∙ f leUC^(ε' + ε) v ∙ g$.
#srcs(cc("UC/RandomSystems/Quantitative.agda", 87, "≈ᵁᴿ[]⇔∼ᴿ[]"), cc("UC/RandomSystems/Quantitative.agda", 97, "_≤UCᴿ[_]_"), cc("UC/RandomSystems/Quantitative.agda", 106, "≤UCᴿ[]⇔Constructs"), cc("UC/RandomSystems/Quantitative.agda", 126, "≈ᵁ[]⇒≈ᵁᴿ[]"), cc("UC/RandomSystems/Quantitative.agda", 131, "Witness⇒≤UCᴿ[]"), cc("UC/RandomSystems/Quantitative.agda", 138, "≈ᵁᴿ[]⇔≈ᵁ[]⁺"), cc("UC/RandomSystems/Quantitative.agda", 144, "≤UCᴿ[]⇔Witness⁺"), cc("UC/RandomSystems/Quantitative.agda", 151, "≤UCᴿ⇔≤UCᴿ[0]"), cc("UC/RandomSystems/Quantitative.agda", 159, "≤UCᴿ[]-refl"), cc("UC/RandomSystems/Quantitative.agda", 162, "≤UCᴿ[]-trans"), cc("UC/RandomSystems/Quantitative.agda", 169, "≤UCᴿ[]-∙"))
] <thm:qrs>

The quantitative emulation order is exactly the _security condition_ of
@maurer2011cc Definition 3, not full secure construction. Its security composition
is the generic one of @thm:qmetatheory(3). Full construction additionally fixes
no-adversary converters and checks availability (@def:full-constructs).
#PM's own $eqU_ε$ matches security only up to every positive slack (item 3).

#theorem(name: [FaultFlag: a tight half-error construction])[
#formal The real resource caches a bit with true probability $1/2$, the intermediate one a bit
with true probability $1/4$, and the ideal always returns false. The sampled bit persists across
adaptive reads; it is not a fresh trial at each query. Their initial laws have mass one.
Live nonidentity tag-converting simulators witness
$ "real" leUC^(1/4) "middle" leUC^(1/4) "ideal", quad
  "real" leUC^(1/4 + 1/4) "ideal" $
in the actual #QRS setup. The composed simulator is $s ∘ s$ and the bound is exactly $1/2$.
For every rational $ε < 1/2$ and every simulator, the construction at $ε$ is impossible:
one honest read sees real true mass $1/2$, simulated-ideal true mass zero. This is security-only
replacement transitivity, not availability or a parallel-resource theorem.
#srcs(cc("Examples/FaultFlag.agda", 83, "real"), cc("Examples/FaultFlag.agda", 239, "half-quarter-cache"), cc("Examples/FaultFlag.agda", 248, "quarter-false-cache"), cc("Examples/FaultFlag/UC.agda", 80, "first-security"), cc("Examples/FaultFlag/UC.agda", 83, "second-security"), cc("Examples/FaultFlag/UC.agda", 86, "composed-security"), cc("Examples/FaultFlag/UC.agda", 92, "composed-simulator"), cc("Examples/FaultFlag/UC.agda", 104, "no-small-construction"), cc("Examples/FaultFlag/UC.agda", 107, "no-small-security"))
] <thm:faultflag>

The epsilon-preserving raw/sealed bridges quantify arbitrary sealed simulators, including
partial initializers. The lower bound therefore rejects all witnesses, not just the displayed
tag converter. The same simulator precedes every adaptive test and every positive slack.

=== #PMom and #PMN: the vanishing and the negligible tier

#definition(name: [#PMom, #PMN])[
$𝔾^o_ω$ is the category of $ℕ$-indexed families: objects are families $(A_n)_n$ of #PM interfaces,
morphisms are levelwise #PM morphisms carrying a certificate of a resource rate polynomial in the
security parameter, the tensor is levelwise. Families of laws are compared _eventually_:
$μ apx^ω_ε ν$ iff $μ_n apx_ε ν_n$ for all large $n$.
- $PMom := Std(𝔾^o_ω, cal(E)^ω)$ identifies tests that are eventually $ε$-close for every $ε > 0$
  under every closure: _vanishing advantage_.
- $PMN := Std(𝔾^o_ω, cal(E)^sans("N"))$ identifies tests $t, t'$ when for every closure $m$ there is a
  negligible $δ$ with $Obs(t ∘ m)_n apx_(δ(n)) Obs(t' ∘ m)_n$ for all $n$: _local negligibility_.
#srcs(ag("Categories/LocallyGraded/Family.agda", 43, "Obj^ω"), ag("Categories/LocallyGraded/Family.agda", 59, "_⇒^ω_"), ag("Categories/LocallyGraded/Family.agda", 115, "Famᴹ"), cc("UC/Model/Enrichment.agda", 46, "gradingᵒ"), cc("UC/Family.agda", 90, "_≈^ω[_]_"), cc("UC/Family.agda", 122, "Evaluation^ω"), cc("UC/Family.agda", 148, "ucSetup^ω"), cc("UC/Family/Negligible.agda", 78, "Evaluationᴺ"), cc("UC/Family/Negligible/Setup.agda", 51, "ucSetupᴺ"), cc("UC/Model/Family.agda", 26, "𝔾ᵒ qevaluationᵒ gradingᵒ"))
] <def:tiers>

#theorem(name: [the tiers])[
+ _Concrete bounds._ Say $f apx_ε g$ for $ε : ℕ × ℕ → ℚ$ if at every ancilla context the level-$n$
  advantage is at most $ε(n, q)$, $q$ the allowance the context affords. If $ε$ vanishes at every
  polynomial allowance, $f eqU g$ in #PMom; if it is negligible, so too, and the bound with its
  witness kept ($f apx^sans("N") g$) gives $f eqU g$ in #PMom and $f leUC g$ in #PMN.
+ #PMom and #PMN have the same category, grades and graded monad, on the nose: they differ only in
  their tests.
+ Each is the forgetting of one quantitative setup on $𝔾^o_ω$: for #PMom, $eqU$ and $leUC$ coincide
  with those of the all-positive forgetting; for #PMN only one direction holds — a bound at _one_
  negligible schedule good for every context is a #PMN witness — and the converse
  (uniformisation) is open.
#srcs(cc("UC/Family.agda", 161, "_≈ℰ[_]_"), cc("UC/Family.agda", 188, "absorb"), cc("UC/Family.agda", 223, "absorb-negl"), cc("UC/Family.agda", 233, "_≈ℰⁿ_"), cc("UC/Family.agda", 249, "≈ℰⁿ⇒≈ᵁ"), cc("UC/Family/Negligible/Setup.agda", 60, "≈ℰⁿ⇒≤UC"), cc("UC/Family/Negligible/Setup.agda", 71, "shared-computational"), cc("UC/Family/Quantitative.agda", 97, "≈ᵁ^ω⇔≈ᵁ₊"), cc("UC/Family/Quantitative.agda", 103, "≤UC^ω⇒≤UC₊"), cc("UC/Family/Quantitative.agda", 108, "≤UC₊⇒≤UC^ω"), cc("UC/Family/Negligible/Quantitative.agda", 83, "uniform⇒local"), cc("UC/Family/Negligible/Quantitative.agda", 101, "≤UCˢ⇒≤UCᴺ"), cc("UC/Family/Negligible/Quantitative.agda", 108, "uniform-witness⇒≤UCᴺ"))
] <thm:tiers>

Both tiers inherit the abstract composition theorem of @thm:metatheory. Identifying #PMN with
computational UC (@canetti2001) still needs a concrete feasibility/attacker correspondence:
query-rate certificates alone are not PPT bounds. The relation $eqU$ of #PMom is too weak to carry a property whose
error must stay negligible (a bad event of probability $1/(n+1)$ vanishes); #PMN keeps the witness. A
family tier over #RS would now be possible — $𝔾^R$ has the quantitative readout of #QRS — but needs a
resource grading on $𝔾^R$, which is not built.

== #NDA and #NDB: nondeterministic choice <sec:nd>

#formal Choice interfaces and their ownership restrictions are placed in the _grade_.
These are built instances, not the planned native scheduler models of @sec:designed.

#definition(name: [choice factors, #NDB, #NDA])[
Let $𝕄$ be #PM (with the sealed symmetric bundle $𝔾^s$) or #SSP. For a set $S$ the _choice factor_ is
the interface $C_S := (1, S)$. A protocol with $n$ choice sites is
$f : A → (X ⊗ C_(S_1) ⊗ dots.c ⊗ C_(S_n)) ⊗ B$. In #PM $op("choose")$ suspends its first activation,
requests a pick on its fresh head factor, initializes the selected branch and retains that branch
for its lifetime. It does not revisit the head site. In #SSP a step cannot suspend or call its
exported grade: compilation queues externally preloaded picks and consumes them on activation;
an empty queue aborts, not a resumable pending request.
- $𝒢_B$ is the full subcategory of grades $X ⊗ C_(S_1) ⊗ dots.c ⊗ C_(S_n)$, $n ≥ 0$, with their choice
  factors designated. It is closed under $⊗$ up to the symmetry that moves choice factors to the right
  (formalised at #PM as $𝔾^s$), contains the unit at $n = 0$, and its
  inclusion into $𝕄$ is strong monoidal. Since $n = 0$ is allowed it contains every interface:
  $NDB := Std(𝕄)|_(𝒢_B)$ has the ambient emulation order, with choice factors designated;
  this is a proved regrading equivalence, not literal identity of the grade presentations.
- $𝒢_A ⊆ 𝒢_B$ is the wide subcategory of morphisms $u ⊗ ρ$, with $u$ arbitrary on $X$ and $ρ$ a
  _relabelling_ of choice factors: a stateless partial wire, given by a partial injection of real
  sites into ideal sites and a function on each site's picks. An ideal request travels through the
  partial inverse and a real pick through the forward map; in #PM an absent route diverges on either
  polarity. The choice part is the image of $sans("Alph")^"op"$.
  $NDA := Std(𝕄)|_(𝒢_A)$.
Both are grade-side restrictions: the computations, the tests and $cal(M)$ restricted along the
inclusion (a graded monad pulls back along a lax monoidal functor) are those of $Std(𝕄)$, and
$ NDA arrow.r.hook NDB arrow.r.hook Std(𝕄) $
are setup morphisms $("Id", mincl, opid, opid)$.
#srcs(ag("Categories/Monad/Graded/Pullback.agda", 35, "pullback"), cc("Abstract2/Regrade.agda", 55, "regraded"), cc("Abstract2/Regrade.agda", 62, "inclusion"), cc("Abstract2/Regrade.agda", 97, "Preserves"), cc("ND/Grade.agda", 81, "𝒢B"), cc("ND/Grade.agda", 84, "ιB"), cc("ND/Grade.agda", 100, "NDB"), cc("ND/A.agda", 59, "Relabelling"), cc("ND/A.agda", 134, "closedA"), cc("ND/A.agda", 170, "𝒢A"), cc("ND/A.agda", 173, "incl"), cc("ND/A.agda", 179, "NDA"), ag("Categories/Category/Monoidal/Construction/Transport.agda", 229, "weaken"))
] <def:nd>

*Who resolves.* In #NDB arbitrary grade morphisms can generate picks and use their own state and
public transcript. This permits adaptive adversarial/simulator choices, but does not itself encode
Canetti's delivery scheduler (@canetti2020uc; @canetti2015suc). In #NDA the choice leg forwards
matched requests to the environment; its site routing is partial-injective, but payload maps are
_arbitrary functions_, not necessarily bijections. A constant payload map may eliminate an ideal
alternative. The ordinary factor $u$ remains unrestricted and may abort through initialization.
Thus A expresses environment-triggered, simulator-translated refinement, not unchanged ownership
of all alternatives or oblivious scheduling. At #SSP the swap simulator proves equivalence of
$op("choose")[p,q]$ and $op("choose")[q,p]$ after relabelling picks; it is not commutation under the
same schedule. The private-counter commutation example needs its particular callee equations.

#proposition(name: [emulation in #NDA implies emulation in #NDB])[
#formal For protocols $f, g$ graded in $𝒢_A$: if $f leUC g$ in #NDA then $f leUC g$ in #NDB, and in #NDB
$leUC$ is $Std(𝕄)$'s. The converse fails (built at #SSP: one choice site copied to two). Over any
symmetric $𝕄$; instantiated at #SSP and #PM. The separate #PM non-reflection witness is not claimed.
#srcs(cc("ND/A.agda", 182, "A⇒B"), cc("ND/Grade.agda", 103, "≤UC-B⇔≤UC"), cc("ND/SSP/Setup.agda", 142, "A⇒B"), cc("ND/SSP/Setup.agda", 145, "A⇒SSP"), cc("ND/PM/Setup.agda", 42, "A⇒B"), cc("ND/PM/Setup.agda", 46, "A⇒PM"), cc("ND/PM/Setup.agda", 39, "≤UC-B⇔≤UC"), cc("ND/PM/Setup.agda", 50, "relabel-≤UC"), cc("ND/PM/Setup.agda", 55, "≤UC⇒relabel"), cc("ND/SSP/Reflect.agda", 147, "¬reflect"), cc("ND/SSP/Laws.agda", 198, "Swap.order-indep"))
] <prop:nd-incl>

#proofidea[$𝒢_A$ is wide in $𝒢_B$, so the two setups have the same grade objects, hence the same
ancillas, prefix contexts and tests: $eqU$ is literally the same relation in both. By dummy
completeness (@thm:metatheory(2), valid in every setup), $f leUC g$ in #NDA gives
$s_0 ∈ 𝒢_A (Y, X)$ with $f eqU opsub_(s_0) ∘ g$; since $𝒢_A (Y, X) ⊆ 𝒢_B (Y, X)$, the same $s_0$ is a
dummy simulator in #NDB. The converse fails because a #NDB simulator may answer requests or copy a
pick to several sites, which no relabelling does; at #SSP a simulator forwarding each real pick to two
ideal sites is the witness. The inclusion preserves $leUC$ and does not reflect it; @thm:transport is not
needed (and its hypotheses fail: #PM is not grade-stable, and $mincl$ is not full).]

Every proved A-emulation is usable in B; branch-permutation equivalence is not a general
“send to several observable recipients in any order” theorem. PM's tests remain adaptive, so an
environment may first sample a bit and then answer a public request with it. Task-PIOA instead
separates an adaptive environment automaton from an oblivious residual schedule (@sec:task-island).
The superseded observe-only demonic-choice proposal in #plan("uc-setup-nondeterministic.md")
is not the implemented model, but rejecting it does not establish that literature correspondence.

#formal The #PM compiler reads flat processes $A → C^f_(vec(S)) ⊗ B$ through the isomorphism
$C_(vec(S)) ≅ C^f_(vec(S))$. Its choice-free, sequential and tensor equations use the unitor,
concatenation comparison and middle-four interchange of $𝔾^s$, including the explicit interface
tensor comparisons across the seal. The request/resume pins use Boolean picks; two-site sequential
and parallel pins instantiate these equations.
#srcs(cc("UC/Model/Symmetric.agda", 32, "symmetricᵒ"), cc("ND/PM/Factor.agda", 124, "ψ"), cc("ND/PM/Relabel.agda", 54, "relabelling"), cc("ND/PM/Choice.agda", 92, "choose"), cc("ND/PM/Choice/Compose.agda", 47, "⌈⌉-plain"), cc("ND/PM/Choice/Compose.agda", 55, "⌈⌉-∘"), cc("ND/PM/Choice/Compose.agda", 67, "⌈⌉-⊗"), cc("ND/PM/Choice/Pin.agda", 57, "request"), cc("ND/PM/Choice/Pin.agda", 60, "resume"), cc("ND/PM/Choice/Pin.agda", 83, "two-compiled"), cc("ND/PM/Choice/Pin.agda", 91, "parallel-compiled"))

#formal Constant-pick refinement for choice-free branches $p_s$ requires a selected $s : S$
and almost-sure totality (`ASTotal`) of _that branch's initialization_, not a fixed finite
termination cutoff. No condition is imposed on unselected branches or later steps.
With grades $(I, [])$ and $(I, [S])$, the explicit unitor
insertion $op("at")$ and online constant picker prove $p_s leUC op("choose")(p)$ in #NDB.
The constant-family instance is $p leUC op("choose")(op("const")(p))$. The unrestricted law
is false: a half-terminating initialization is observed even by a zero-query strategy, bounding
the same simulator's surviving initial mass by $1/2$. One ordinary activation also passes
through the ideal's deferred half-terminating initialization, so its mass is at most $1/4$, against
the real world's $1/2$. This is a checked #NDB refutation via #PM full abstraction, not a
compiler-shape equation. The total-initialized consumer uses distinct activations and a retained
state update through the actual plugged machine and the closed ancilla/cup observation.
#srcs(cc("ND/PM/Choice/Initialization.agda", 231, "TotalInitialization"), cc("ND/PM/Choice/Initialization/Graded.agda", 61, "at"), cc("ND/PM/Choice/Initialization/Graded.agda", 123, "constant-pick-≤UC-B"), cc("ND/PM/Choice/Initialization/Graded.agda", 182, "B-emulation⇒closed-resolver"), cc("ND/PM/Choice/Initialization/Example.agda", 205, "half-initialization-≰UC-B"), cc("ND/PM/Choice/Initialization/Example.agda", 233, "stateful-≤UC-B"), cc("ND/PM/Choice/Initialization/Example.agda", 255, "stateful-closed-run"), cc("ND/PM/Choice/Initialization/Example.agda", 267, "stateful-observed-run"))

The positive toggle consumer retains state: starting at true, activations false then true each
return true; reinitializing before the second would fail its closed conjunction test. Early or
repeated head picks and overlapping activations instead produce `botₚ`, aborting the whole run,
including a sibling that has not yet been queried. They are not ignored invalid scheduler inputs.
Repeated visits require a separate persistent scheduler, not another invocation of this one-shot
constructor. These PM-B clients do not supply a PM-A rejection or PM A/B nonreflection theorem.

In SSP, a simulator with no callable export cannot preload an ideal choice queue merely because an
honest query arrives elsewhere. Even redundant choice may therefore be unsimulatable without
external preload. A continuation that starves may erase a preceding imported communication from
the final-return observation; this is not an online prefix-observation law. FIFO tail append has a
source-level quadratic aggregate traversal pattern for long preloads, not a measured benchmark.

The existing $mwb : SSP → PMwb$ carries pick-ahead compiled protocols into well-bracketed machine
semantics, and $miota$ includes their computations in #PM. It retains the queued interaction
discipline; it is not an equality with the separate on-demand #PM choice combinator.

= Planned native models and bounded connections <sec:designed>

#design None of the IPDL, causal-box, RSIM or task-PIOA native categories, tests or bridges
below is implemented. IPDL and causal boxes have detailed plans; RSIM and task-PIOA are
proposed interpretations, not existing setup nodes. “Island” means _no implemented native
bridge_, not a classification or impossibility theorem for all setup morphisms.

Three deliverables must be separated. An _operational interpretation_ proves agreement with a
specified driver. A _setup morphism_ additionally provides $F, Φ, κ, ν$ and all laws of
@def:morphism, including congruence and naturality of the test map. A _security transfer_ must
then preserve the ancilla-closed kernel, or discharge a sufficient condition of @thm:transport.
Pulled-back tests make a formal map cheap but do not prove native-test correspondence.
Reflection additionally needs representable target simulators and the relevant cancellation,
Mono/fullness or direct contextual argument. Regrading restricts ownership or simulator classes;
it cannot repair identities/composition, recover erased timing, or make adaptive tests oblivious.

== #IPDL: native interaction before compilation <sec:ipdl-island>

The proposed open source has polarised typed contexts under concatenation, reaction networks,
composition $"new" B "in" (P ∥ Q)$ and copy reactions as identities, modulo IPDL's exact equations.
The protocol-test presentation of #plan("uc-setup-ipdl.md") still needs comparison with the
paper's operational distinguishers; it is not an already proved native kernel.

=== Push/poll resource interpretation

The promising first target is a finite #SSPd _resource_, not yet an IPDL setup morphism.
@gancher2023ipdl §4.2.2, Definitions 4.5–4.7 and Fig. 9 expose the adaptive API
$ "Input"_i : τ_i → 1, quad "Get"_o : 1 → "Maybe" τ_o, quad "Step" : 1 → 1. $
`Input(i,v)` assigns once; further writes do nothing. `Get(o)` reads the current residual
network _before that round's_ evaluation to quiescence; `Step` requests no observation.
Quiescence follows every query. State contains residual reactions, persistent assignments and
already sampled randomness, with pure initialization. Absence returns `None`, not `dead`, so
later input can unblock an output.

This API hides internal read demands. The old plan's pull compiler instead exposes
`read i; read j` versus `read j; read i` to an order-sensitive oracle. That separates _that
compiler_, not Fig. 9 semantics: native exchange lemmas 4.18–4.19 already quantify arbitrary
API distinguishers, including absence tests. Finite names/values and normalized rational
sampling give a bounded exact/statistical experiment; no cryptographic axioms or PPT claim.

The necessary witnesses are:
+ `o := read i`, driven by `Step; Get o; Input(i,false); Get o; Input(i,true); Get o`,
  must return `None, Some false, Some false`.
+ Both read-order programs must agree against every finite legal API strategy, while the
  demand-exposing encoding retains its separating oracle.
+ A hidden sampled bit reused twice must remain one shared bit, not be redrawn on each `Get`.
+ Retain the correlation separator from the plan: two nets agreeing under every independent
  partial input assignment can be separated when a context supplies `i` only after reading `o`.
  The final distributions $(1/2,0,1/2)$ and $(1/4,1/4,1/2)$ on (true, false, undefined) are
  distinguished by `Step; Get(o); conditional Input(i,false); Get(o₂)`.

A run-correspondence theorem would transport exact resource equations into #SSPd; its SSP
presentation also has the existing #PMwb route. An open bridge additionally needs the
_hidden-channel linker square_ for $"new" B "in" (P ∥ Q)$, preserving shared randomness and
mutual dependencies, plus identity and context/test correspondence. Ordinary package
composition is not automatically that linking operation. The plan's weaker test presentation
must either be proved equivalent or replaced by an explicitly named Fig. 9 observation setup.

=== Single-assignment disciplined quotient

A possible actual open bridge is finite IPDL into a new single-assignment observation discipline,
say $PM[sans("sa")]$ or $SSP[sans("sa")]$, using the W pattern rather than identifying it with #PMwb.
The legal contract must ensure persistent values, equal repeat reads, demand-order opacity,
preserved stage correlations, compositional/tensor closure and identity aliases on legal histories.
“Read each channel at most once” is insufficient: an oracle returning true to the first of two
distinct channels and false to the second still reveals read order. Well-bracketing alone also
does not enforce confluence.

Start with acyclic unidirectional nets whose boundary inputs are committed before evaluation;
interactive feedback requires the push/poll or another genuinely interactive contract.
First construct a closed typed carrier retaining structural wires, then quotient by a lawful
two-sided test kernel (@prop:quotient). `changeKernel` alone cannot fix a raw compiler's failed
identity at hom-equality. Splitting a proven memoizing idempotent in a Karoubi envelope is a
heavier conceivable alternative, not implemented here and not a cure for demand-order leakage.
Test-map naturality is the linker theorem; its congruence requires source-equivalent legal
closures. Security needs contextual density/backtranslation with ancillas or explicit object
coverage, and reflection still needs simulator representability.

=== Finite batch kernels and support into #Rel <sec:batch-island>

A smaller high-confidence candidate restricts IPDL to finite, total, acyclic, unidirectional nets:
all inputs arrive together; all outputs terminate; sampling is rational and normalized;
tests observe the joint final output, not availability or intermediate interaction. For typed
contexts $Γ, Δ$ propose
$ F_0 Γ = product_(s ∈ Γ) s, quad F_1 P : F_0 Γ → "Dist"_ℚ (F_0 Δ). $
A small finite stochastic-kernel setup would use Kleisli composition and independent product
tensor; context-concatenation/product isomorphisms give the strong comparisons. Hidden shared
coins remain shared inside the joint law. Constants and deterministic finite predicates naming
every input and separating every output make equality of all acceptance probabilities determine
that kernel. This is the proposed direct $eqU$-preservation argument, not a theorem already present.

The next proposed leg takes positive-weight support:
$ R_P(x,y) ⟺ "Pr"[F_1 P(x)=y] > 0, quad ν(t)(x) ⟺ "Pr"[t(x)="true"] > 0. $
Existing support/return/bind lemmas are reusable, but finite kernels, tensor laws and test wrapper
still need packaging. Into full #Rel, direct preservation via relation equality avoids an
unjustified epi claim onto arbitrary relation-valued predicates; universe lifting is bookkeeping,
not the semantic obstruction.
Here `supp` filters zero-weight entries; representation-level `OnSupport` is not this
extensional support predicate.
#srcs(ag("ProbabilisticLogic/Distribution/RationalDist/Support.agda", 169, "supp-return"), ag("ProbabilisticLogic/Distribution/RationalDist/Support.agda", 172, "supp-bind"))

The positive witness should prove the uniform one-bit OTP kernel equation and reach the actual
#Rel theorem @thm:rel-otp with the same support simulator. The mandatory negative is a
$3/4$-biased pad: full support can look perfectly secret while its probability law leaks.
Thus support cannot reflect probability-sensitive security. Arbitrarily small, even negligible,
statistical differences may change support, so approximate security cannot be sent to support
equality without extra hypotheses. This bridge loses feedback, blocking, intermediate
availability and timing; its support leg additionally loses all weights.
#srcs(ag("ProbabilisticLogic/Distribution/RationalDist/Support.agda", 269, "pad-supp-perfect"), ag("ProbabilisticLogic/Distribution/RationalDist/Support.agda", 277, "pad-not-perfect"), ag("ProbabilisticLogic/Distribution/RationalDist/Support.agda", 298, "close-supp-differs"))

== RSIM: explicit buffers, scheduler and ownership <sec:rsim-island>

@backes2007rsim §§1.4, 3.4–3.5 has one active machine at a time, explicit buffers, clock-port
ownership and a default scheduler; Definition 3.16 specifies the finite-phase global step.
Adversarial and procedure-call scheduling are special cases. Immediate G-wire delivery therefore
does not forbid an explicit buffer _component_; it only rules out treating an asynchronous
connection as the same naked wire. The SSP pollable-state example already illustrates storage.

Propose finite Boolean collections with rational kernels, designated total initial states and
finite-view observations, interpreted as a #PM/#SSPd service with activation/delivery commands.
State records queues, component states, the active machine and phase. Activation may enqueue a
batch and acknowledge; delivery releases a selected queued message. An invalid/missing-message
schedule must return control to the default scheduler, not abort the whole run.
A centralized interpreter closely following Definition 3.16 is a useful operational theorem,
but does not establish functoriality of open composition.

The open candidate uses typed service and clock ports with ownership, disjoint-union tensor and
named-port gluing. Identities are aliases, not extra buffers. Buffer completion must commute
with gluing or be explicit in syntax. An initial compiler may use free monoidal syntax and fine
PM equality; any later external-view quotient needs a lawful contextual congruence.
An honest user $H$ becomes a driver seeing exactly $H$'s native view, with compiler-only
acknowledgements hidden. Target tests must not inspect private queue/scheduler states or phase
labels: prove legal-test backtranslation or a natural observation coarsening.
Adversary-owned clocks belong in the adversarial grade; honest/default controls retain their
owners. Regrading does not license giving every clock to an adaptive attacker.

The minimal witness is two senders enqueuing 0 and 1, and a receiver returning the first delivery.
Prove finite-view agreement for orders 01 and 10, withholding, invalid index and default fallback,
then an identity square and a nontrivial two-component gluing square. Those are prerequisites
to packaging $F$ and $ν$, together with simulator wiring/ownership and ancilla coverage.

Native GRSIM, URSIM and BRSIM are not interchangeable. In §1.6, URSIM has
$∀ A. ∃ A'. ∀ H$; BRSIM additionally asks for a fixed black-box simulator.
The repository's dummy-complete grade converter must be compared with a specified variant.
Finite-view equality alone gives neither fairness nor availability preservation: active polling
changes liveness unless the driver contract reproduces native scheduling. @def:full-constructs
is a useful specification pattern, not an existing RSIM liveness theorem. No PPT correspondence
is part of this first finite experiment.

== Task-PIOA: schedules are not online choice <sec:task-island>

@canetti2006taskpioa §§1–2, Definition 1, separates an explicit adaptive adversarial automaton
from a static/oblivious residual task sequence fixed independently of execution. Inputs are
enabled; action/transition determinism gives at most one enabled transition for a task;
a disabled task stutters. #NDA's public online picks and #PM's lifetime chooser do not supply
these properties.

Propose finite action-deterministic automata with an explicit finite task script and a
`tick(task)`/external-input interface in #PM/#SSP. A disabled tick returns a no-action
acknowledgement, never `botₚ`. Persistent scheduler state supports repeated visits to one task.
In a product automaton, a selected output synchronizes matching input transitions; independent
component kernels form one logical transition with its trace label.
Tests are indexed by an environment automaton $E$ and an oblivious word $ρ$; unscheduled native
semantics is a _set_ of scheduled distributions, not one distribution sampled by an attacker.
Precommitted schedule grades may transform script structure but cannot inspect runtime state.
Their tensor must retain interleaving/shuffle information, not merely two projected task words;
monoidal closure and object/simulator coverage remain unproved.

The native security quantifiers (Definition 2) are
$ ∀ E. quad "tdists"(T_1 ∥ E) ⊆ "tdists"(T_2 ∥ E). $
The matching ideal schedule can depend on $E$ and the real schedule. This is not automatically
one UC simulator fixed before every environment. The paper's schedule-prefix Skolem function
and open-system corollary do not erase that distinction; §5 discusses local-scheduler uniformity.
A native $scripts(≤)_0$–$leUC$ correspondence needs an explicit uniform-simulation theorem,
possibly a stronger premise. Unrestricted PM simulators are too adaptive for automatic reflection.

Bounded witnesses should cover disabled-then-enabled ticks, two visits to the same task,
independent private-bit commutation when external effects commute, and an order-sensitive
first-message-wins receiver. A scheduler-information separator is a hidden fair bit followed
by tasks committing guess 0 or 1, then revelation: an oblivious schedule matches with probability
$1/2$, while a state-peeking scheduler can match with probability 1. This is a proposed
counterexample experiment, not a checked source theorem.

== Causal boxes: a category boundary and two restricted routes <sec:causal-island>

@portmann2017 §§3.1, 4.3–4.5, 6–7 permits compatible wire connections but explicitly states
that identity is not causal: a direct loop takes no time, a strictly causal box introduces delay.
Native strictly causal boxes under ordinary sequential connection therefore do not directly form
the unital category required by StdUC. The two-phase `Box A B` of
#plan("uc-setup-causal-boxes.md") instead admits zero-delay structural paths while guarding
caller-input to caller-output. It is a proposed category of resource-preserving _converters/
wiring contexts_; not every arrow is a native strictly causal box on one external clock.
Resource and admissible-plugging correspondence is still required. Guarded trace
(@goncharov2018) is relevant infrastructure, not an already proved equivalence.

=== Synchronous one-way histories

For normalized finite rational one-way synchronous transducers with _product_ tensor, fix a
horizon $h$ and propose
$ F_h(A) = A^h, quad F_h(f) : A^h → "Dist"_ℚ(B^h). $
Finite unfolding preserves cascade and synchronous product, using the history-shuffle
isomorphism. This requires a product-tensored stochastic carrier, not the existing interleaving
$+$ tensor of `SFunM.Monoidal`. @bonchidilavore2025, extended arXiv version (2026),
Proposition 6.9, Proposition 6.12 and Corollary 6.13 supply the primary causal-process/trace
motivation; their numbering refers to that extended version.
The existing `SFunM.trace-∘` supplies a finite sequential-run law, not the missing product-tensor
or native causal-box correspondence.
#srcs(cc("SFunM.agda", 93, "trace-∘"))

Complete input histories and separating Boolean predicates on output histories define an
$h$-observed batch setup, with a proposed exact-security-preserving map to finite kernels and
then the support leg of @sec:batch-island. It is not the adaptive bidirectional CB environment
class. Arbitrary batch simulators can inspect later inputs before simulating early outputs;
reflection requires prefix-causal target grade maps and a causal reconstruction/fullness theorem.
An early/late-secret example should show why a batch simulator can copy a later secret backwards
while a causal simulator cannot. Start with a two-round one-bit delay register and two independent
parallel registers, proving prefix dependence, cascade and the product/history square.
The loss is fixed horizon, one-way synchrony, and no arbitrary loops, dense-time insertion,
relativistic timing or quantum superpositions; support further forgets probabilities.

=== Tick interpretation versus monoidal interpretation

A finite classical two-phase resource can be encoded as a #PM/#SSP round/batch service:
one letter carries a whole bundle and vacuum is an ordinary `Maybe` value. This addresses the
superficial one-message-per-activation objection, but a joint round is not automatically
isomorphic to two independently callable target interfaces. A global barrier must tick both
components together; an unrestricted tensor context can tick just one. Two counters advancing
every round expose the difference between one joint tick and two independent calls.
This is a promising _operational interpreter_, not a strong monoidal functor until a synchronized
discipline, lawful tensor/comparisons and test class are supplied. `Construction.Transport`
cannot manufacture the missing interface isomorphisms.

=== Obstructions with their actual scope

+ _Activation-count timing._ If $f$ answers 0, $g$ calls it twice before answering, and $k$ answers
  0 directly, untimed $g ∘ f eqR k$ can have different completion positions under the proposed
  timed encoding. A deadline distinguishes with advantage 1. This blocks that timing-exposing
  compiler, not every possible CB/PM map.
+ _Retiming is not generally contextual._ A 0-sender at time 1 versus time 3 has the same
  untimed output. Racing either against a 1-sender at time 2 gives first-arrival outputs 0
  versus 1. Merely deleting final timestamps is not a congruence against arbitrary timed
  contexts; retain timing/scheduling or restrict to delay-insensitive contexts.
+ _Single-slot multiplexing._ `"Maybe" P × "Maybe" Q` admits simultaneous messages whereas
  `"Maybe"(P + Q)` does not. This refutes the particular single-slot comparison, not all tensor
  interpretations: @portmann2017 Eq. 9 supplies Fock-space wire decomposition, and classical
  batches can hold both values. Scheduling and naturality still need proof.
+ _Strict identity._ Delay one is not identity when time is observed; its square delays two.
  Formal wire identities and strictly causal resource devices must remain distinct.
+ _Losslessness._ Normalized boxes have consistent prefix marginals. A later failed partial
  computation may erase earlier finite-run mass in PM. Begin with total initialization and
  normalized finite kernels, or prove an explicit subnormalized dilation/postselection
  contract as in @portmann2017 Definition 4.7.
+ _Quantum observations._ All routes above are classical. Equal Z-measurement probabilities
  can hide states distinguished in the X basis. Diagonal observations do not preserve the full
  quantum test theory, so no quantum UC transfer is supplied.

Families of timed realizations (@portmann2017 §9) may support a different refinement theorem
with new uniform-simulator obligations. Extending setup morphisms to lax/set-valued compilation
merely to draw an arrow is not the next step; the concrete finite squares above are more informative.

== Reuse and ranked experiments <sec:island-experiments>

The existing machinery removes categorical boilerplate, not the semantic obligations:

#{
  set text(size: 8.5pt)
  set par(justify: false)
  table(columns: (1fr, 1.25fr, 1.35fr), inset: 4pt, stroke: 0.35pt + luma(65%),
    table.header([*Mechanism*], [*Useful reuse*], [*Not supplied*]),
    [#SSPd / SSP density], [finite probabilistic runs; deferred sampling; WB transfer], [IPDL hidden linking, RSIM gluing, unrestricted PM security],
    [W restriction / U-kernel quotient], [natural legal-driver coarsening; lawful contextual congruence], [reverse WB security, closure of a proposed legal test class],
    [`Transport` / `Regrade`], [closed typed carrier and real interface isomorphisms; ownership/simulator restrictions], [synchronous barrier, input enabling, fairness, lost timing],
    [`freeStrongMonoidal`], [initial compiler on explicit components], [native equations, behavioral full abstraction or native tests],
    [positive support / `rewrite⇒RS`], [exact support or behavioral coarsening of a valid interpretation], [probability reflection, negligible-error transfer, repair of observably false identities],
  )
}

A finite rational sampler is not inherently uninterpretable in PM: rational coins give an
operational implementation. The obligation is representation-independent equality at the chosen
target, not necessarily a stronger monad morphism into fine tree equality.

The ranking separates a small theorem demonstration from prospective reactive-security payoff.
Every row remains #design; none is a promised or implemented graph edge.

#{
  set text(size: 8.3pt)
  set par(justify: false)
  table(columns: (0.32fr, 1.2fr, 1.8fr), inset: 4pt, stroke: 0.35pt + luma(65%),
    table.header([*Order*], [*Bounded experiment / expected theorem*], [*Restrictions, success criterion and priority*]),
    [A], [IPDL Fig. 9 → #SSPd resource], [High operational confidence; finite exact API agreement for every legal strategy and all four witnesses. Then one hidden-Boolean linker with identity and feedback. Best first IPDL experiment; open bridge only after linking/tests.],
    [B], [RSIM buffers/default scheduler → legal-view PM], [High finite-interpreter, medium native-bridge confidence. First-delivery witness plus identity/gluing squares and ownership. Highest prospective reactive payoff; fairness/PPT excluded.],
    [C], [Batch IPDL → rational kernels → #Rel], [High restricted-morphism confidence. Supply $F, Φ, κ, ν$, direct U-preservation and target OTP, plus biased-pad nonreflection. Best small genuine new setup edge; heavy batch/support semantic loss.],
    [D], [Task-PIOA scripted execution], [High operational, lower UC-correspondence confidence. Stuttering, repeated tasks, synchronized products, shuffle-aware scripts and scheduler separator; write uniform UC/native quantifiers before transfer.],
    [E], [Synchronous causal histories], [High confidence for the stated finite product fragment. Delay-one/two and joint/independent ticks first; then prefix-causal two-round strong-monoidal square. Reflection needs causal grades.],
    [Later], [IPDL single-assignment quotient], [Medium confidence; only after API/linker experiments establish a closed interaction contract and legal-context density. WB alone is insufficient.],
    [Later], [Full classical causal converters → synchronized PM], [Moderate/low confidence; correct converter category, resource correspondence, barrier tensor and causal tests remain substantial.],
    [Defer], [Timed realization families / quantum bridges], [Different refinement or quantum infrastructure and uniformity needed; no immediate UCSetupMorphism claim.],
  )
}


= Morphisms between the setups <sec:morphisms>

*Diagram legend.* Solid black arrows are implemented setup morphisms, not automatically
security-transfer theorems. Blue dashed arrows are proposed constructions with their restrictions
stated below: `O` is only an operational interpretation; `M` is a proposed setup morphism.
Red dotted arrows marked × identify a _specific obstructed candidate_, not a universal no-map
theorem. Quantitative forgetting and family refinements (@thm:refine) are omitted.
The #Symcert source is distinct from #Symiso and #Sym; its solid arrow to #PMN certifies a
formal query-admissible interpretation, not cryptographic soundness.

#figure(
  diagram(
    spacing: (16mm, 11mm),
    node-stroke: 0.5pt,
    node-inset: 4pt,
    node-corner-radius: 2pt,
    label-size: 8pt,
    node((0, 0), $Sym$, name: <sym>),
    node((1.3, 0), $Symiso$, name: <symiso>),
    node((2.6, 0), $Iso$, name: <iso>),
    node((3.9, 0), $ITMiso$, name: <itmiso>),
    node((0, 1), $PMN$, name: <pmn>),
    node((1.3, 1), $Symcert$, name: <symcert>),
    node((2.6, 1), $PM$, name: <pm>),
    node((3.9, 1), $ITM$, name: <itm>),
    node((1.3, 2), $Wio$, name: <wio>),
    node((2.6, 2), $RS$, name: <rs>),
    node((3.9, 2), $NDB$, name: <ndb>),
    node((0, 4), $SSP$, name: <ssp>),
    node((0, 3), $SSPd$, name: <sspd>),
    node((1.3, 4), $PMwb$, name: <pmwb>),
    node((1.3, 3), $WW$, name: <ww>),
    node((3.9, 3), $NDA$, name: <nda>),
    node((2.6, 4), [#Rel \ one-shot], name: <rel>),
    edge(<symiso>, <sym>, "->", label: $mcoarse$, label-side: right),
    edge(<symiso>, <iso>, "->", label: $msym$),
    edge(<symcert>, <pmn>, "->", label: $mcs$),
    edge(<itmiso>, <iso>, "->", label: $mitmiso$, label-side: right),
    edge(<itm>, <pm>, "->", label: $mitm$),
    edge(<pm>, <rs>, "->", label: $mrs$),
    edge(<wio>, <pm>, "->", label: $miota$),
    edge(<wio>, <ww>, "->", label: $mck_(ν_W)$, label-side: right),
    edge(<ssp>, <pmwb>, "->", label: $mwb$, label-side: right),
    edge(<ssp>, <sspd>, "->", label: $mq$, label-side: right),
    edge(<ww>, <pmwb>, "->", label: $mq$),
    edge(<nda>, <ndb>, "->", label: $mincl$, label-side: right),
    edge(<ndb>, <pm>, "->", label: $mincl$, label-side: right),
    edge(<ssp>, <pm>, "..>", stroke: red + 0.6pt, bend: -35deg, label: text(fill: red)[$mcomp$ ×]),
    edge(<pm>, <iso>, "..>", stroke: red + 0.6pt, label: text(fill: red)[state-retaining ×], label-side: right),
  ),
  caption: [Implemented setup components and two candidate-specific obstructions. The W arrows
    point from full tests to PM and to restricted W/PM[wb]; there is no directed SSP-to-PM
    security path. #Rel is an actual separate component, not an impossibility class.],
) <fig:graph>

#figure(
  diagram(
    spacing: (10mm, 8mm),
    node-stroke: 0.4pt,
    node-inset: 3pt,
    node-corner-radius: 2pt,
    label-size: 7.5pt,
    node((0, 0), [finite IPDL \ Fig. 9 API], name: <api>),
    node((1.5, 0), [#SSPd resource], name: <api-target>),
    node((0, 1), [finite RSIM \ explicit buffers], name: <rsim-source>),
    node((1.5, 1), [PM legal \ finite views], name: <rsim-target>),
    node((0, 2), [finite task-PIOA \ oblivious script], name: <task-source>),
    node((1.5, 2), [scheduled \ PM resource], name: <task-target>),
    node((0, 3), [batch IPDL], name: <batch-source>),
    node((1.5, 3), [finite rational \ kernels], name: <kernel-target>),
    node((3, 3), $Rel$, name: <support-target>),
    node((0, 4), [synchronous causal \ finite histories], name: <causal-source>),
    node((0, 5), [single-assignment \ IPDL], name: <sa-source>),
    node((1.5, 5), [legal SA \ quotient], name: <sa-target>),
    edge(<api>, <api-target>, "-->", stroke: blue, label: [O]),
    edge(<rsim-source>, <rsim-target>, "-->", stroke: blue, label: [O]),
    edge(<task-source>, <task-target>, "-->", stroke: blue, label: [O]),
    edge(<batch-source>, <kernel-target>, "-->", stroke: blue, label: [M]),
    edge(<kernel-target>, <support-target>, "-->", stroke: blue, label: [M: support]),
    edge(<causal-source>, <kernel-target>, "-->", stroke: blue, label: [M], label-side: right),
    edge(<sa-source>, <sa-target>, "-->", stroke: blue, label: [M]),
  ),
  caption: [Proposed bounded connections, all unformalised. O-edges do not supply open
    linking/gluing or uniform UC simulation. M-edges require the carriers, tests and preservation
    proofs in @sec:designed. Support is exact-only and nonreflecting; batch reflection also
    needs causal simulators on the causal route.],
) <fig:proposed>

== Formal morphisms <sec:formal-morphisms>

=== $mrs : PM → RS$

#proposition(name: [the random-systems quotient])[
$mrs$ is the standard morphism (@prop:std-morphism) of the quotient functor $𝔾^o → 𝔾^o slash eqR$
(@prop:quotient(1)): identity on objects and on representatives, $κ = opid$, and test map the
identity, Epi and Mono. It preserves and reflects emulation: $f leUC g$ in #PM iff $mrs(f) leUC mrs(g)$
in #RS (@thm:constructs(1)); it reflects $eqU$ ($f eqR g ⇒ f eqU g$), and with @thm:fullabs the U-kernel
of #PM _is_ its image's hom-equality.
#srcs(cc("UC/RandomSystems/Morphism.agda", 30, "rewrite⇒RS"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 74, "quotientF"), ag("Categories/Category/Monoidal/Construction/Quotient.agda", 101, "descendᵛ-mono"), cc("UC/RandomSystems/Morphism.agda", 35, "≈ᴿ⇒≈ᵁ"), cc("UC/RandomSystems/Morphism.agda", 38, "≤UC-resp-≈ᴿ"), cc("UC/RandomSystems/Construction.agda", 114, "≤UCᴿ⇔Constructs₀"))
] <prop:mrs>

The preservation of $leUC$ is _not_ @thm:transport(2) (#RS's grade stability is not known); it is the
explicit characterisation by constructions, which holds on both sides.

=== $mitm : ITM → PM$

#proposition(name: [interpreting Turing machines])[
$mitm = (F^p, F^p, opid, ν^T)$ with $F^p$ the strict monoidal interpretation of @def:itm and
$ν^T$ the identity on tests (the tests of #ITM are #PM's, pulled back), Epi and Mono. Hence $F^p$
preserves and reflects $eqE$ (@thm:itm-kernel). Neither half of @thm:transport(2)–(3) applies: #PM is
not grade-stable and $F^p$ is not full.
#srcs(cc("ITM/Setup.agda", 54, "itm⇒prot"), cc("ITM/Functor.agda", 65, "Fᴾ"), cc("ITM/Setup.agda", 44, "νᵀ"), cc("ITM/Setup.agda", 48, "νᵀ-epi"), cc("ITM/Setup.agda", 51, "νᵀ-mono"), cc("ITM/Setup.agda", 57, "≈ℰ⇔"), ag("Categories/FreeMonoidal.agda", 519, "freeStrongMonoidal"))
] <prop:mitm>

=== $mitmiso : ITMiso → Iso$

#proposition(name: [Turing machines as relations])[
$mitmiso = (F^r, F^r, opid, ν^r)$ with $F^r$ the halting-relation interpretation of @def:itmiso and
$ν^r$ Epi and Mono. #instance Since #Iso is grade-stable (@thm:iso-gs), @thm:transport(1)–(2) apply:
$F^r$ preserves and reflects $eqE$, and $f leUC g$ in #ITMiso implies $F^r f leUC F^r g$ in #Iso, so an
impossibility in #Iso is one in #ITMiso.
#srcs(cc("ITM/Relational.agda", 138, "itm⇒iso"), cc("ITM/Relational.agda", 117, "Fᴿ"), cc("ITM/Relational.agda", 128, "νᴿ"), cc("ITM/Relational.agda", 132, "νᴿ-epi"), cc("ITM/Relational.agda", 135, "νᴿ-mono"), cc("Machine/UC.agda", 164, "grade-stable"), cc("Abstract2/Morphism.agda", 75, "transfer"))
] <prop:mitmiso>

This instantiates the grade-stable general transport theorem. The inclusion of #Wio below instead
uses essential surjectivity of its computational functor. Any proposed triangle with a modified
initialized, deterministic nonsilent #Iso source also needs that source translation and the mirror
isomorphism of port trees; no commuting triangle for the unrestricted setups is asserted #design.

=== $miota : Wio → PM$

The inclusion of well-bracketed machines, with the identity test map, Epi and Mono (@prop:iota).
It preserves and reflects $eqE$, and preserves $eqU$ and $leUC$ in the forward direction.
Every #PM object $X$ is isomorphic to the image of the singleton-channel signature
$op("one") (op("obj") X)$, through stateless wires adding and removing the channel tag. Hence $ι$ is
essentially surjective, and @thm:transport's $sans("transfer")^+$ applies after
$sans("surjective⇒preserves-≈ᵁ")$: every target ancilla is an image up to isomorphism.
No #PM grade-stability assumption is used, and non-fullness does not obstruct preservation.
This is not a reflection theorem.
#srcs(cc("UC/Bracket/InclusionTransfer.agda", 39, "oneᵒ"), cc("UC/Bracket/InclusionTransfer.agda", 51, "ι-essentially-surjective"), cc("UC/Bracket/InclusionTransfer.agda", 54, "ι-preserves-≈ℰ"), cc("UC/Bracket/InclusionTransfer.agda", 57, "ι-preserves-≈ᵁ"), cc("UC/Bracket/InclusionTransfer.agda", 61, "ι-preserves-≤UC"))

The source-facing consumer compiles the probabilistic, stateful one-time-pad protocol and its
inlined real resource. Their machine hom-equality proves $eqU$ and $leUC$ in the exact full-test
setup #Wio, and the inclusion transports that security to #PM. A second consumer uses the actual
compiled random simulator across different grades. These are inlining and simulator-construction
theorems, not a claim that #PMwb's one-time-pad confidentiality reverses into full-context security.
#srcs(cc("Examples/SSP/OneTimePad/FullTests.agda", 29, "otp≈real-full"), cc("Examples/SSP/OneTimePad/FullTests.agda", 32, "otp≤real-full"), cc("Examples/SSP/OneTimePad/FullTests.agda", 35, "otp≤real-PM"), cc("Examples/SSP/OneTimePad/FullTests.agda", 48, "ideal-with-sim≤ideal-full"), cc("Examples/SSP/OneTimePad/FullTests.agda", 51, "ideal-with-sim≤ideal-PM"))

=== $mck_(ν_W) : Wio → WW$

The observation coarsening of @prop:Wrestriction leaves the computational category, grades and
their action unchanged. Its epi test map preserves $eqE$; the shared prefix contexts then preserve
$eqU$ and $leUC$ without grade stability. Composition with $mq$ reaches #PMwb, not ordinary #PM.
#srcs(cc("UC/Bracket/ObservationRestriction.agda", 156, "restriction-preserves-≈ℰ"), cc("UC/Bracket/ObservationRestriction.agda", 159, "full-≈ᵁ⇒wb-≈ᵁ"), cc("UC/Bracket/ObservationRestriction.agda", 162, "full-≤UC⇒wb-≤UC"), cc("UC/Bracket/ObservationRestriction.agda", 186, "full-preserves-≤UC"))

The composed bridge is exercised on the genuine full-test OTP inlining theorem and the compiled
random-simulator construction, including its change of grade. These uses do not assume a reverse
map from #PMwb to #PM.
#srcs(cc("Examples/SSP/OneTimePad/ObservationRestriction.agda", 18, "otp≤real-coarsened"), cc("Examples/SSP/OneTimePad/ObservationRestriction.agda", 21, "ideal-with-sim≤ideal-coarsened"))

=== $mwb : SSP → PMwb$

#theorem(name: [the call/return bridge])[
On objects, flattening $A ↦ op("flat") A$; on packages, compilation to a flat protocol (queries
tagged with their channel, a reply on the wrong channel is an abort) followed by the machine semantics,
which lands in well-bracketed machines (@thm:wb-closure), then the quotient by $simW$; it is a strong
monoidal functor because the compiled identity wire is $simW$-equal to the identity and the compiled
tensor to #PMwb's (both fail at $eqM$, @sec:non-morphisms). The test map sends a distinguisher to its
compiled test; it is well defined because SSP games are dense among well-bracketed closures: a closure
from each state, its steps cut at finite depth, is an SSP game. Approximation is pointwise/cofinal
for each fixed finite-depth test observation, not uniform over every test. Compiled distinguishers are likewise dense
among well-bracketed tests, so $mwb$ preserves $eqE$, and since $mwb$ is the identity on objects it
preserves $leUC$ without grade stability. In particular the one-time pad (@thm:otp) holds in #PMwb.
#srcs(cc("SSP/Semantics.agda", 151, "Fᵂ"), cc("SSP/Semantics.agda", 110, "wire≈σ"), cc("SSP/Semantics.agda", 131, "⊗≈⊗"), cc("Protocol/Machine/Oracle.agda", 113, "oracle≈∘"), cc("SSP/Dense.agda", 365, "games-dense"), cc("SSP/Dense.agda", 381, "SSP→PM[wb]"), cc("SSP/Dense/Tests.agda", 460, "tests-dense"), cc("SSP/Dense/Tests.agda", 474, "preserves-≈ℰ"), cc("SSP/Dense/Tests.agda", 489, "preserves-≤UC"), cc("Standard2/Morphism.agda", 97, "surjective⇒preserves-≈ᵁ"), cc("Examples/SSP/OneTimePad/WB.agda", 15, "otp≤idealᵂ"))
] <def:mwb>

The test map is not known to be Epi, and likely is not: a well-bracketed test can carry an
irrational verdict mass, a distinguisher only a finite rational one. Preservation needs no Epi: both
densities serve their quantifier by approximation, not by representation.
A geometric-delay closure illustrates the distinction: a depth-$n$ cut answers one call with
mass $1-2^(-n)$, so a test making $k$ calls has discrepancy $1-(1-2^(-n))^k$, approaching 1
as $k$ grows at fixed $n$. A test-independent cut family is not a test-uniform error/running-time
bound. No query-sensitive or quantitative efficiency transfer is asserted.

=== $mq : SSP → SSPd$

#proposition(name: [security across the distributional quotient])[
The quotient functor and descended presheaf define a standard setup morphism $mq : SSP → SSPd$,
identity on objects and protocol representatives, with identity test map, Epi and Mono.
It preserves and reflects emulation:
$ f leUC g " in " SSP quad ⇔ quad f leUC g " in " SSPd. $
Preservation on the mapped protocols uses the surjective-ancilla theorem
(the same argument as @def:mwb), not grade stability. Reflection applies Mono at every unchanged prefix
context; it likewise requires no grade stability. Removing the structural identity in the mapped
protocol identifies this comparison with the original representatives. Reflection is not an
inverse functor at hom-equality: it does not say $scripts(≈)^sans("d") ⇒ eqP$.
#srcs(cc("SSP/Dist/Setup.agda", 34, "ssp⇒dist"), cc("SSP/Dist/Setup.agda", 49, "preserves-≤UC"), cc("SSP/Dist/Setup.agda", 56, "ssp≤⇒dist≤"), cc("SSP/Dist/Setup.agda", 62, "dist≈ᵁ⇒ssp≈ᵁ"), cc("SSP/Dist/Setup.agda", 67, "dist≤⇒ssp≤"), cc("SSP/Dist/Setup.agda", 71, "reflects-≤UC"), cc("Examples/SSP/OneTimePad/Dist.agda", 109, "otp≤ideal-image-dist"))
] <prop:ssp-dist-morphism>

=== $mq : WW → PMwb$

The quotient morphism of @prop:quotient(1) at $simW$, with the descended test map.
#srcs(cc("UC/Bracket/Setup.agda", 155, "q"))

=== $mcoarse : Symiso → Sym$

The change of kernel $mck$ from syntactic equality of test circuits to equality of their possible
verdicts: identity on tests, Epi, so it carries every #Symiso emulation to #Sym by
@thm:transport(2) with @thm:sym-kernel(1).
#srcs(cc("Symbolic/Setup.agda", 154, "coarse"), cc("Symbolic/Setup.agda", 159, "coarse-epi"), cc("Symbolic/Setup.agda", 162, "fine→sym"))

=== Formal symbolic interpretations <sec:symbolic-interpretations>

*$msym : Symiso → Iso$.* #formal The free strong monoidal interpretation of role circuits into
(reversed) relational machines is `Symbolic/Machine.sym≅→iso`. It respects source coherence,
not #Sym's observational kernel: its relational execution deliberately forgets global freshness
and initialization. No Epi/Mono or UC-security transfer result is asserted for this test map.
#srcs(cc("Symbolic/Machine.agda", 115, "Fᴿ"), cc("Symbolic/Machine.agda", 188, "νᴿ"), cc("Symbolic/Machine.agda", 195, "sym≅→iso"))

*$mcs : Symcert → PMN$.* #formal `CertifiedSource sch` is a distinct source setup, not an alias
for unrestricted #Symiso. Each generator carries a role, unit-free endpoints, a positive natural
rate and a direct `Certified` query-bound witness for its actual runtime at every parameter.
The constant polynomial schedule embeds its execution in `Famᴹ`; free interpretation and the
syntactic test map give `fine→comp : UCSetupMorphism Sym≅ᶜ.StdSetup ucSetupᴺ`.
This certifies query admissibility, not PPT, correct cryptographic equations or game security.
Given a sort and an inhabitant of the scheme's `Bits` carrier, `no-backwards-certificate` refutes
direct certificates at every natural rate for the backwards role; it is not an obstruction theorem
about `QB`'s machine-equivalence closure.
#srcs(cc("Symbolic/Computational.agda", 100, "Generator"), cc("Symbolic/Computational.agda", 143, "Sym≅ᶜ"), cc("Symbolic/Computational.agda", 214, "fine→comp"), cc("Symbolic/Computational/Obstruction.agda", 67, "no-backwards-certificate"))

*Operational runtime versus certified families.* `Scheme` supplies bit carriers and primitive
operations; `Execution.Fᶜ η` runs all roles as raw PM processes, with concrete guards and
independently sampled `new`, not symbolic normalization on bitstrings. The record alone imposes
no equation correctness, disjoint/injective tags, secure nonce distribution, PPT or game security.
Certified generators measure interaction/query resources, not CPU or bit complexity.
The rate-one forwarding client is genuine; the backwards obstruction concerns direct
`Certified` witnesses, not `QB`'s closure under machine equivalence. The certified test map
closes its interpreted ancilla with `deadᶠ`; naturality is not coverage of arbitrary target tests.

*Derived conditional soundness.* #formal For each spectator and feasible computational context,
`Backtranslation` supplies an `Extraction`: one sampled symbolic experiment, including its
distribution, ancilla, test and closure, fixed _before_ the honest circuit. `Maybe Bool`
classification retains divergence separately from false. The mandatory `ProtocolError`
then assigns `error f η` and negligibility to each eligible `GroundGuardedC f`, with a
one-system realization bound. The experiment is shared; the error is _protocol-indexed_.
For a fixed eligible pair, exact classification and source-kernel equality identify their
sampled symbolic outcomes, and `sound⁺` combines
$ "error"(f,η) + "error"(g,η). $
No premise merely assumes the desired kernel-preservation conclusion.
#srcs(cc("Symbolic/Soundness/Errors.agda", 21, "ProtocolError"), cc("Symbolic/Soundness/Errors.agda", 35, "compare"), cc("Symbolic/Soundness.agda", 96, "Extraction"), cc("Symbolic/Soundness.agda", 120, "Backtranslation"), cc("Symbolic/Soundness.agda", 126, "sound⁺"))

The checked error experiments use a fixed-budget recorded-guess experiment with uniform
$η$-bit nonce and bound $N · 2^(-η)$; the consumer compares budgets 1 and 2 with their separate
errors. `no-uniform-comparison` rejects one negligible bound for every fixed finite budget
(at each $η$, the already-quantified $N=2^η$ exhausts the nonce space).
`no-uniform-factorization` also rejects uniform approximation through an arbitrary shared
predicted subdistribution. These are formal closed experiments, not an embedding of the
review's parallel symbolic-circuit counterexample.
#srcs(cc("Symbolic/Soundness/ErrorTests.agda", 84, "error"), cc("Symbolic/Soundness/ErrorTests.agda", 117, "one-system"), cc("Symbolic/Soundness/ErrorTests.agda", 168, "no-uniform-comparison"), cc("Symbolic/Soundness/ErrorTests.agda", 186, "no-uniform-factorization"))

`sound-≤UC` is also genuinely derived, but returns `DummyWitness`: one symbolic simulator
chosen before all spectator/feasible contexts, with a separate ground-guarded eligibility proof
and feasible raw-family agreement. Its quantifiers are, for the fixed honest pair,
$ ∀ W. ∀ c " feasible". ∃ ε " negligible". ∀ η. $
It is not the canonical target order $∀ a. ∃ s. ∀ W,e,m$: neither target-family
honest/simulator admissibility nor feasibility closure absorbing arbitrary computational
adversaries is supplied. A vacuous externally supplied `Feasible` predicate gives a vacuous
application; no nonvacuous cryptographic instance is constructed.
#srcs(cc("Symbolic/Soundness.agda", 74, "DummyWitness"), cc("Symbolic/Soundness.agda", 156, "sound-≤UC"))

No joint IND-CPA/INT-CTXT attacker-extraction reduction establishes `Backtranslation`.
The source-eligibility issue is independent: if concrete projection maps two malformed
non-pairs to the same error, a ground test $π_1(c_0)=π_1(c_1)$ can disagree with E₀'s distinct
irreducible projections. This conditional, unformalised witness requires error-aware parsing/
well-formedness correspondence, not merely encryption security or terminal behavior.
CLC additionally needs its key hierarchy, randomness and process/equivalence correspondence
(@comonlundhcortier2008, Theorem 12, Lemmas 24–25); Abadi–Rogaway's passive acyclic-expression
result (@abadirogaway2002) is not active UC. Canetti–Herzog/BPW routes require their certified
encryption/library and trace-mapping machinery (@canettiherzog2006; @backes2003library).
Neither formal interpretation supplies a morphism from #Sym's observational quotient,
and no concrete cryptographic/target-UC acceptance/rejection result follows from the normalized
echo/projected-pair conditional consumers.

=== The generic morphisms, instantiated

Besides $mcoarse$ and the observation restriction @prop:Wrestriction, change of kernel $mck$ and
the wide-subcategory inclusion $mincl$ (@sec:setup-morphisms) instantiate the refinements between
each tier and its quantitative family (@thm:tiers(3), through @thm:refine) and #NDA $→$ #NDB
(@prop:nd-incl, formal at #SSP and #PM).

== Designed morphisms <sec:designed-morphisms>

*$mdet$ from a modified #Iso fragment to #PM.* #design This proposal does not have the
unrestricted #Iso of @def:iso as source. Add an initial state and require isomorphisms to preserve
it; restrict to deterministic nonsilent transitions; establish closure of the resulting carrier
under composition/tensor. Then interpret its execution in $Dp$ and construct a lawful test map.
A proposed ancilla closure using a divergent process must be checked for observational
usefulness, not just naturality. No full-source map or security theorem is asserted.

*$mgr : sans("TM")_× → Rel$.* #design The cartesian reading of Turing machines (bitstring tuples under
$×$, computable functions) maps strongly into #Rel: a function to its graph, a computable predicate to
its subset.

== Obstructed candidates, not universal non-morphisms <sec:non-morphisms>

#proposition(name: [scope of the obstructions])[
The following statements concern the named encodings or comparisons, not every functor between
the displayed setups.
+ _Raw SSP compilation into PM._ Copycat accepts an unsolicited return whereas the compiled
  wire requires an outstanding query. Interleaving tensor also admits hostile traces excluded
  by SSP's call/return tensor. These prevent the specified raw compiler's identity/strong-tensor
  laws at PM simulation equality; the source-described semifunctor is not a setup morphism.
  #design The WB quotient repairs precisely the legal-context laws (@def:mwb), not unrestricted
  security.
+ _State-retaining PM-to-Iso interpretation._ Preserving all state sets cannot send a
  simulation-equivalent padded identity to machine isomorphism: @prop:padded is a checked
  state-bijection obstruction. This is not a no-functor theorem for all abstractions.
+ _Demand-exposing IPDL compiler._ Read-order exchange is distinguishable to a demand-order
  oracle even without repeated queries. This refutes that compiler, not the paper's Fig. 9 API
  or the batch/single-assignment proposals (@sec:ipdl-island). No unconditional native-IPDL
  security or attack transfer follows without the actual context map.
+ _Timing-exposing and single-slot causal encodings._ Delay/cascade, races under retiming,
  and simultaneous slots give the specific separations of @sec:causal-island. They do not
  prohibit bundled round interpreters or a product-tensored finite-history bridge.
+ _Reverse representative inclusion $WW → Wio$._ Restricted-closure equality need not survive
  hostile closures, so this inclusion is not a setoid map (@prop:Wrestriction). The forward
  natural epi and full-test inclusion remain proved.
+ _Reflection of the A-to-B inclusion._ The checked SSP copying witness refutes reflection of
  that inclusion (@prop:nd-incl); it does not rule out every possible reverse morphism, and is
  not a PM A/B nonreflection theorem.
+ _Positive-support reflection._ A biased pad and arbitrarily close laws with different support
  delimit probability/reflection claims; @sec:batch-island proposes only exact preservation.
The IPDL/causal arguments here are #design unless a linked existing theorem is explicitly named.
#srcs(cc("Protocol/Machine.agda", 71, "morphism"), cc("Machine/Iso.agda", 50, "padded-not-iso"), cc("ND/SSP/Reflect.agda", 147, "¬reflect"))
] <prop:obstructions>

= Open problems <sec:open>

+ _Non-adaptive equivalence._ $eqB ⇒ eqR$ beyond finite alphabets (@prop:finite; @lochbihler2019cc
  Thm. 2), or a reason to keep $eqR$.
+ _Grade stability_ of #SSP, #RS and #PMwb: neither proved nor refuted.
+ _Reactive simulatability_ and the trace-property characterisation of @patrignani2024 §8.2.1
  (@sec:robust).
+ _Uniformisation_ in the negligible tier: local negligibility implies a uniform negligible witness?
  (@thm:tiers(3)).
+ _Construction beyond replacement._ Availability is built with designated compatible modes
  (@def:full-constructs); its serial/parallel honest-protocol composition remains open.
  The PM braiding is built. Amplification and an RS family tier still need conditional-probability
  and resource-grading infrastructure respectively.
+ _Feasibility and native models._ Intrinsic computable ITM tests need a context/density theorem;
  initialized execution, silent control transfer and computational validity are distinct issues.
+ _The modified deterministic #Iso fragment:_ initialized, nonsilent execution and a useful test map
  behind $mdet$.
+ _Native island connections:_ the ranked concrete witnesses/linker squares of
  @sec:island-experiments, not a new lax abstraction or reinstatement of the withdrawn raw arrows.
  #NDA/#NDB are already built; their scheduler-adequacy and remaining PM-A clients are separate.
+ _Computational soundness:_ construct the operational `Backtranslation` from game-based
  assumptions, establish the literature correspondence for the honest-role restriction, and
  supply feasibility closure for adversary-quantified UC transfer. The formal $mcs$ from #Symcert
  and the derived conditional implication do not discharge these obligations.
+ _Symbolic representation and realization._ Sort-indexed names/ownership, explicit public-frame
  restrictions, a generic static converse, dynamic session routing, and error-aware source
  eligibility remain open. The substitution/freshness repair, pure-interface spans, opt-in
  terminal runtime and per-protocol errors solve their particular contracts, not these problems.

== Current review dispositions <sec:dispositions>

The stable IDs in #plan("uc-setup-adversarial-review.md") retain their historical snapshot.
This ledger records their current scope; absence of a public client is not nonexpressibility.

#{
  set text(size: 8.4pt)
  set par(justify: false)
  table(columns: (0.85fr, 2.5fr), inset: 4pt, stroke: 0.35pt + luma(65%),
    table.header([*Review IDs*], [*Current disposition*]),
    [001–002, 010–013], [Global partial initialization and unrestricted/readout-sensitive observation remain. Availability is separately built with designated modes, not inferred from security; finite-rational SSP and passive reliable OTP retain their restrictions.],
    [003–009], [ITM structural/uninitialized versus probabilistic/perfect tests are explicitly separated. The unrestricted presheaf no-go is withdrawn. The probabilistic security/observation client is checked; initialized relational traces remain ongoing. Native silent-control/PPT/context correspondence remains open.],
    [014–018], [W is conditional safety, not hostile enforcement or liveness; density is pointwise/cofinal. Both full-test forward bridges (016–017) are formal. Neither supplies reverse WB security.],
    [019–026, 036], [Choice payload/ownership, SSP preload/starvation, branch-permutation, PM lifetime and fail-stop boundaries remain. The selected-branch ASTotal repair and all-resolver half-init refutation (023) are formal; FIFO scaling is not a benchmark.],
    [027–033, 038], [Fine/coarse observations remain distinct. Sorted term substitution and fresh-name rejection (028) are formal; the older multisort impossibility is withdrawn (038). Raw names/public frames remain restricted. GroundGuarded and opt-in Terminal now separate the old terminal overclaim (030); general applied-pi/session correspondence is not proved.],
    [034–035], [Actual SSPᵈ positive/negative reflection, W full/restricted positive transfers, RS security/full-construction consumers, QRS nonzero tight bound, PM-B clients and the probabilistic ITM simulator/observational negatives are integrated. The ITM negatives are not non-emulation. SSPᵈ is built; W/PM[wb] negatives, PM-A clients and full-context OTP confidentiality remain absent.],
    [037, 039], [Pure interface legs are enforced (037). The checked channel remains fixed-public-message factorized opacity (039); interactive transmission/decryption is ongoing and not claimed here.],
    [040–041], [Protocol-indexed errors with shared extraction and closed finite-budget positive/negative experiments repair 040. Crypto backtranslation, target UC, and malformed-projection/error-aware eligibility (041) remain unproved.],
  )
}

#bibliography("kb/refs.bib", title: [References])
