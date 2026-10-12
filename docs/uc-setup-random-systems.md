# Random systems as a UC setup

Plan, 2026-10-09.  §3–§5 are the design; steps 1–9 of §6 are implemented on branch
`rs-quotient`, and §6 records what landed, under which names, and where it departs from the
design; §4.4's toolkit (Δ, composition, hybrids, security-only construction) is on `rs-toolkit`.
It refines `docs/uc-setup-landscape.md` §4 (random systems) and corrects its full-abstraction
remark (§5.3).

## 1. Summary

**RS** `= quotient 𝔾ᵒ congᴿ`: protocol-rewrite's machine category (`UC/Model/Seal.agda:41-43`)
with the same objects, machines, G-composition and ⊎-tensor, but hom equality *behavioural* —
`_≈ᴿ_`: every `Strategy.Strat` distinguisher has advantage 0 (maurer2002 Defs 9–10) — instead of
simulation (`Machines/Sim.agda:_≈ᴹ_`); tests are `ℰᵒ` descended along the quotient.
**Morphisms:** `rewrite⇒RS : protocol-rewrite → RS` is a `StdUCMorphism` (identity on objects,
machines and tests); none back.  ITM, IPDL and machine-category (deterministic fragment) land in
RS; symbolic does not, and nothing leaves RS for causal boxes.  **Hard part:** congruence of
`_≈ᴿ_` for G-composition (maurer2002 Lemmas 4(i), 5(ii)), by absorbing contexts into truncated
distinguishers.  **Full abstraction:** `ℰᵒ`'s bare kernel `≈ℰ` is not behavioural equality
(counterexample; `ℰᵒ` is not `GradeStable`); its U-kernel `≈ᵁ` is (`≈ᵁ⇒≈ᴿ`, §6 step 8).

## 2. The source model

**Systems, equality.** An (X,Y)-random automaton (maurer2002 Def 2) is a state machine
`fᵢ : X × R → Y` with a distribution over randomness and initial state; its random system (Def 3)
is the sequence of conditionals `p_{Yᵢ|XⁱYⁱ⁻¹}`, and `F ≡ G` iff these agree wherever defined, or
equivalently (Def 3, fn. 6) iff the products `p_{Yⁱ|Xⁱ}` agree for all i.  Query types join into
one alphabet (remark after Def 3), so a G-hom `A ⇒ B` is a `(Pos A ⊎ Neg B, Neg A ⊎ Pos B)`-system,
as in lochbihler2019cc §IV.  `Machines/Core.agda:Machine` (state, effectful `point`, step in
Kl(Dₚ)) is bonchidilavore2025 §3.1's effectful machine, `_≈ᴹ_` its bisimilarity (Def 3.6:
connectedness by homomorphisms, ours pure).  Maurer's systems are total; ours may diverge, like
CryptHOL's sub-probabilistic resources (lochbihler2019cc fn. 1).

**Composition, tensor.** Cascade `FG` (maurer2002 Def 8) and invocation `C(·)`, which calls `F`
zero, one or several times per input (§3.3, Fig. 4); in constructive cryptography a cryptographic
algebra ⟨Φ, Σ⟩: resources with parallel composition `||`, converters attached at an interface
(`αⁱR`), converter composition `αβ` (maurer2011cc §4.4 Def 1).  Here both are G-composition,
`composeᴳ f g = trace (α ∘ f ⊗ g ∘ γ)` (`GConstruction.agda:55-56`): an invocation whose
ping-pong is an unguarded Elgot loop inside one activation (`Machines/Trace.agda:74-75`,
`Dp/Iter.agda:iterₚ`).  `R₁ || R₂` routes queries by tag (lochbihler2019cc Def 2): `_⊗ᵉ_`
(`Machines/Tensor.agda:98-99`), on G-homs `_⊗₁ᴳ_ = mid ∘ f ⊗ g ∘ mid` (`GConstructionMonoidal.agda:58-64`).

**Distinguishers, advantage, equality.** A distinguisher for (X,Y)-systems is a (Y,X)-system with
an initial query that outputs a bit after k queries (maurer2002 Def 9);
`Δₖ(F,G) = max_D |P^{DF}(Eₖ) − P^{DG}(Eₖ)|` (Def 10); in CC `d(R,S) = Δ^𝒟(R,S) =
sup_{D∈𝒟} Δ^D(R,S)` (maurer2011cc §4.5).  `Strategy.Strat` (`Strategy.agda:24-27`) is Def 9 with
rational coins, `asks≤ k` the query bound.  Trace equivalence, defined by conditioning on observed
outputs (lochbihler2019cc Def 5), holds iff `D ⊳ R₁ = D ⊳ R₂` for every distinguisher (Thm 2);
bisimilar ⇒ trace equivalent (Cor 1), not conversely (Fig. 6); bonchidilavore2025 Thm 7.19:
effectful streams coincide with causal processes, stochastic case included.

**Composition theorems.** `F ≡ G ⇒ C(F) ≡ C(G)` (maurer2002 Lemma 4(i); proof: the joint law is
the product of the conditionals of F and of C(·)); `Δₖ(C(F),C(G)) ≤ Δ_{m_C(k)}(F,G)` (Lemma
5(ii); proof: "by simulating C(·) one can construct a distinguisher for F and G"); `Δ^𝒟` is
compatible with `||` and converters when 𝒟 is closed under emulating converters and parallel
resources (maurer2011cc Lemma 1; "non-expanding", maurerrenner2016 Def 2).

## 3. The `StdUC` instantiation

### 3.1 Decisions

**Carrier: `Machine` with a coarser setoid, not a behavioural presentation.**  (1) Conditionals
need conditioning on an observed output, i.e. division by a mass that in Dₚ is a lower real never
formed (`Dp.agda:112-117`): Lochbihler's `trace` (Def 5) is not definable.  (2) Families
`List X → Dₚ (List Y)` need a causality condition and a composition that *is* the adaptive product
(below), and every 𝒢ₚᴹ law would be re-proved; effectful streams are a setoid too (dinaturality,
bonchidilavore2025 §1.2), with free feedback (Thm 4.4), not the Elgot trace.  (3) No quotient types.

**Setoid: adaptive.**

| | definition | congruence for `∘ᴳ` | role |
|---|---|---|---|
| `_≈ᴮ_` (Def 3, fn. 6) | ∀ xs, `runᴸ f xs` and `runᴸ g xs` agree on every [0,1]-test | Lemma 4's product formula: pick the context's next query by an indicator on X, i.e. decidable equality on every message type (`Iface` fields are bare `Set`s) | derived |
| **`_≈ᴿ_`** (Defs 9–10) | ∀ `d : Strat X Y`, `runˢ f d ∼ᵃ runˢ g d` | absorb the context into a truncated distinguisher; no decidability | **hom equality** |
| `≈ᵁ` of `ℰᵒ` (grade unit) | ∀ Y, `T₁ Y f ≈ℰ T₁ Y g` | free (AbstractUC) | `= _≈ᴿ_`, planned (§4.2) |

`origin/machine-category` hit the non-adaptive wall: its `Machine/Trace.agda` header records
that `_∘ᵖ_` is not provably a congruence for trace equivalence.

**Dₚ equality: `∼ᵃ`, not `_≈ₚ_`.** `_≈ₚ_` is cofinal domination with exact rational witnesses
(`Dp.agda:427-431`, `LowerReal.agda:32-33`).  A rejection-sampled bit (⅓ true, ⅓ false, ⅓ retry,
as a G-composite loop produces) has true-mass at most `½(1 − 3⁻ⁿ)` at depth n, never the ½ that
`coinₚ` has at depth 2: one random system, two `_≈ₚ_`-classes.  (Per-activation `_≈ₚ_` equality
is `_≈ᴮ_` with `_≈ₚ_`: too fine, and non-adaptive.)  `∼ᵃ`, every positive slack of `_≈ₚ[_]_` on
both verdict masses (`Dp/Advantage.agda:48-52`, `Approx/Error.agda:118-119`), is equality of
lower-real masses, i.e. Δ = 0, and is what `ℰᵒ` reads (`UC/Model/Observation.agda:45`).  Cost:
no slack-0 readout in the open space, hence no `QEvaluation` over 𝔾ᴿ on it
(`Approx/Evaluation.agda:5-7, 43`).  The slack-closed space, `d ≈̄[ε] e := ∀ δ > 0,
d ≈ₚ[ε + δ] e` (`Approx.Rational.Closure`), restores it: `qevaluationᴿ` (§4.4).  A `UC.Family`
tier on RS is not planned.

### 3.2 The behavioural setoid (`UC/Machine/Behaviour.agda`)

Beside `UC/Machine/Run.agda` (closed runs against `Strat`), reusing `UC.Machine.Approximationᴹ`.
`runᴹ` stays: `runᴹFrom`/`resumeᴹ` are named in 11 modules.

```agda
{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.UC.Machine.Behaviour where
-- imports: Dp{,.Advantage,.Coin,.Reasoning}, Approx.Error, Machines.{Base,Core,Pointwise,Sim},
-- Protocol.Machine (Closed, runᴹ), Strategy, UC.Machine (Approximationᴹ)

private
  module Ap = AllPositive ℚ-refinement Approximationᴹ
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  variable X Y : Set

-- `Protocol.Machine.runᴹ` at any alphabet pair: a distinguisher (maurer2002 Def 9) run.
module _ (M : MC.Machine X Y) where
  resumeˢ : (MC.St M → Y → Dₚ Bool) → MC.St M × Y → Dₚ Bool
  resumeˢ c (m′ , y) = c m′ y

  runFromˢ : MC.St M → Strat X Y → Dₚ Bool
  runFromˢ m (out b)    = returnₚ b
  runFromˢ m (coin μ k) = coinₚ μ >>=ₚ λ b → runFromˢ m (k b)
  runFromˢ m (ask x k)  = MC.step M (m , x) >>=ₚ resumeˢ λ m′ y → runFromˢ m′ (k y)

  runˢ : Strat X Y → Dₚ Bool
  runˢ d = MC.point (MC.state M) tt >>=ₚ λ m → runFromˢ m d

-- Δ^D(f, g) = 0 for every distinguisher D (maurer2002 Def 10).
_≈ᴿ_ : MC.Machine X Y → MC.Machine X Y → Set
f ≈ᴿ g = (d : Strat X Y) → runˢ f d Ap.∼ᵃ runˢ g d

≈ᴿ-isEquivalence : IsEquivalence (_≈ᴿ_ {X} {Y})      -- pointwise Ap.∼ᵃ-isEquivalence

-- UC.Machine.Run.runFrom-ϕ at any X Y: induction on the strategy, one ask per activation
runFromˢ-ϕ : {f g : MC.Machine X Y} (ϕ : MC.St f → MC.St g)
           → ((p : MC.St f × X) → (MC.step f p >>=ₚ padϕ ϕ) ≈ₚ MC.step g (ϕ (proj₁ p) , proj₂ p))
           → (m : MC.St f) (d : Strat X Y) → runFromˢ f m d ≈ₚ runFromˢ g (ϕ m) d
runˢ-sim : {f g : MC.Machine X Y} → f MS.≲ g → (d : Strat X Y) → runˢ f d ≈ₚ runˢ g d

≈ᴹ⇒≈ᴿ : {f g : MC.Machine X Y} → f MS.≈ᴹ g → f ≈ᴿ g
≈ᴹ⇒≈ᴿ = EqC.fold ≈ᴿ-isEquivalence λ s d ε ε>0 → ≈ₚ[]-mono (ℚ.<⇒≤ ε>0) (≈ₚ⇒≈ₚ[0] (runˢ-sim s d))
closeˢ : Strat (Neg B) (Pos B) → Strat (⊥ ⊎ Neg B) (⊥ ⊎ Pos B)
closeˢ = mapStrat inj₂ [ ⊥-elim , id ]
runᴹ≈runˢ : (M : Closed B) (d : Strat (Neg B) (Pos B)) → runᴹ M d ≈ₚ runˢ M (closeˢ d)

-- Def 3, fn. 6: p_{Yⁱ|Xⁱ}, tested by [0,1]-valued events
runᴸ : MC.Machine X Y → List X → Dₚ (List Y)
_≈ᴮ_ : MC.Machine X Y → MC.Machine X Y → Set
f ≈ᴮ g = (xs : List X) (P : List Y → ℚ) → (∀ ys → 0ℚ ℚ.≤ P ys × P ys ℚ.≤ 1ℚ)
       → (ε : ℚ) → 0ℚ ℚ.< ε → Dom P ε (runᴸ f xs) (runᴸ g xs) × Dom P ε (runᴸ g xs) (runᴸ f xs)

≈ᴿ⇒≈ᴮ : f ≈ᴿ g → f ≈ᴮ g             -- ask xs in turn, then coin with bias P ys: Pr[true] = E P
det-≈ᴮ⇒≈ᴿ : Deterministic f → Deterministic g → f ≈ᴮ g → f ≈ᴿ g
-- steps are `detₚ`; induction on d, transporting depth-n verdict masses as ℚ-valued tests of
-- the answer, so no decidable equality is needed
```

**F-resp-≈, "simulation ⇒ behavioural equality".**  `runFromˢ-ϕ` is `UC/Machine/Run.agda:63-72`
with `resumeᴹ` generalised: induction on the strategy, i.e. the activation count; each step law is
`fnStep (θ-pure s) (θ-step s)` (pureness yields the state *function* ϕ), the start `point-sim`
(`Run.agda:86-87`), the closure `EqC.fold`.  No new coinduction: the Dₚ side is `>>=ₚ-cong`
(`Dp.agda:626-630`, via `bindᶠ`/`bindˣ`).  Same change: re-derive `Run.agda:runFrom-ϕ` from
`runFromˢ-ϕ` and `runᴹ≈runˢ`, statement unchanged (`Run/Lax.agda`, `StateEvent.agda` use it).

### 3.3 Congruence: Maurer's composition theorem, constructively

`Strat` is well-founded while a context may loop or diverge, so the context is simulated up to a
budget, spending a default verdict `v` on exhaustion.  That truncation scores 0 under
`indᵇ (not v)` — the situation `Dp/Dominate.agda` (header, lines 3-7) was written for.

```agda
-- UC/Machine/Behaviour/Absorb.agda (--safe --without-K --guardedness)
-- maurer2002 Lemma 5(ii), maurer2011cc Lemma 1: a context that a distinguisher can simulate
-- preserves Δ = 0.
record Absorbs {A B P Q : Set} (C : MC.Machine A B → MC.Machine P Q) : Set₁ where
  field
    ♯     : Strat P Q → ℕ → Bool → Strat A B          -- strategy, budget, verdict on exhaustion
    depth : ℕ → ℕ
    lower : (f : MC.Machine A B) (d : Strat P Q) (v : Bool) (k : ℕ)
          → cum k (runˢ (C f) d) (indᵇ (not v)) ℚ.≤ cum (depth k) (runˢ f (♯ d k v)) (indᵇ (not v))
    upper : (f : MC.Machine A B) (d : Strat P Q) (v : Bool) (k : ℕ)
          → Cofinal (indᵇ (not v)) (indᵇ (not v)) (runˢ f (♯ d k v)) (runˢ (C f) d)

absorbs⇒resp : Absorbs C → f ≈ᴿ f′ → C f ≈ᴿ C f′
-- per verdict b, v := not b:  cum k (C f) ≤ cum (depth k) (f , ♯ d k v)            lower
--   ≤ cum m (f′ , ♯ d k v) + ε   (hypothesis at strategy ♯ d k v)  ≤ cum m′ (C f′) + ε   upper

absorbs-∘ : Absorbs C → Absorbs C′ → Absorbs (C ∘′ C′)
-- ♯ d k v = 𝔹.♯ (𝔸.♯ d k v) (𝔸.depth k) v; depth = 𝔹.depth ∘′ 𝔸.depth;
-- lower by ≤-trans (𝔸.lower …) (𝔹.lower …), upper by cofinal-trans (𝔹.upper …) (𝔸.upper …)
wtᴰ : Dₚ R → Dist-ℚ Bool        -- (wt d true , true) ∷ (wt d false , false); wt-1, wt-nn
-- a Dₚ computation inside a strategy; recursion on the budget, as Dp.flatten
unfoldˢ : ℕ → Bool → Dₚ R → (ℕ → R → Strat Q′ A) → Strat Q′ A
unfoldˢ zero    v d k = out v
unfoldˢ (suc n) v d k = coin (wtᴰ d) λ c → [ k n , (λ d′ → unfoldˢ n v d′ k) ] (br d c)
```

The five instances simulate a fixed machine `h` beside or around `f`, or the loop:

```agda
-- UC/Machine/Behaviour/Congruence.agda; the trace instance in …/Behaviour/Trace.agda
⊗ᵉ-absorbʳ : (h : MC.Machine C D) → Absorbs {A} {B} (h ⊗ᵉ_)
⊗ᵉ-absorbˡ : (h : MC.Machine C D) → Absorbs {A} {B} (_⊗ᵉ h)
∘ᴹ-absorbʳ : (h : MC.Machine B C) → Absorbs {A} {B} (h ∘ᴹ_)
∘ᴹ-absorbˡ : (h : MC.Machine C A) → Absorbs {A} {B} (_∘ᴹ h)
traceᴹ-absorb : Absorbs {A ⊎ X} {B ⊎ X} {A} {B} (traceᴹ A B X)

-- ⊗ᵉ-absorbʳ h: h's state threads through the strategy, its steps become coins
go : MC.St h → Strat (C ⊎ A) (D ⊎ B) → ℕ → Bool → Strat A B
go s (out b)          n v = out b
go s (coin μ k)       n v = coin μ λ c → go s (k c) n v
go s (ask (inj₂ a) k) n v = ask a λ b → go s (k (inj₂ b)) n v
go s (ask (inj₁ c) k) n v = unfoldˢ n v (MC.step h (s , c)) λ n′ (s′ , e) → go s′ (k (inj₁ e)) n′ v
♯ d n v = unfoldˢ n v (MC.point (MC.state h) tt) λ n′ s → go s d n′ v

-- traceᴹ-absorb: re-ask f's loop letters; the budget is per activation
loop : ℕ → Bool → (B → Strat (A ⊎ X) (B ⊎ X)) → B ⊎ X → Strat (A ⊎ X) (B ⊎ X)
loop n       v k (inj₁ b) = k b
loop zero    v k (inj₂ x) = out v
loop (suc n) v k (inj₂ x) = ask (inj₂ x) (loop n v k)
♯ (out b)    n v = out b
♯ (coin μ k) n v = coin μ λ c → ♯ (k c) n v
♯ (ask a k)  n v = ask (inj₁ a) (loop n v λ b → ♯ (k b) n v)
```

`lower` holds with budget k because each Dₚ node of `h` and each `iterₚ` turn costs at least one
depth level of the composite run (`Dp.agda:13-14`, `Dp/Iter.agda:37-38`); `depth` is linear (a
`coinₚ` costs two levels, `Dp/Coin.agda:42-43`).  `upper` holds because every not-v verdict of the
truncated run is a composite run with the same weights.  At the G-level (homs of `𝒢ₚ 0ℓ`, object
implicits passed explicitly as `𝒫ᴵ` does, `UC/Machine.agda:65-69`):

```agda
composeᴳ-resp-≈ᴿ : f ≈ᴿ f′ → g ≈ᴿ g′ → (f G.∘ g) ≈ᴿ (f′ G.∘ g′)
-- f G.∘ g ≈ᴹ traceᴹ _ _ _ (α ∘ᴹ (f ⊗ᵉ g) ∘ᴹ γ) by GConstruction.composeᴳ-raw, then ≈ᴹ⇒≈ᴿ;
-- in f the context is traceᴹ ∘ (α ∘ᴹ_) ∘ (_∘ᴹ γ) ∘ (_⊗ᵉ g), absorbed by absorbs-∘; g alike
⊗₁ᴳ-resp-≈ᴿ : f ≈ᴿ f′ → g ≈ᴿ g′ → (f ⊗₁ᴳ g) ≈ᴿ (f′ ⊗₁ᴳ g′)
-- mid ∘ᴹ (f ⊗ᵉ g) ∘ᴹ mid, by a new ⊗₁ᴳ-raw beside ⊗₁ᴳ-resp-≈ (GConstructionMonoidal.agda:66-73)
```

### 3.4 Quotient, `𝔾ᴿ`, `ℰᴿ`

Neither agda-categories 0.3.0 nor the tree has a quotient category; it is generic, beside
`Monoidal/Construction/Thin.agda`.

```agda
{-# OPTIONS --safe --without-K #-}

module Categories.Category.Monoidal.Construction.Quotient where
-- imports: Categories.{Category,Category.Monoidal,Functor.Monoidal{,.Properties},Functor.Presheaf{,.Morphism}}

record MonoidalCongruence {o ℓ e} (𝕄 : MonoidalCategory o ℓ e) (e′ : Level)
       : Set (o ⊔ ℓ ⊔ e ⊔ suc e′) where
  open MonoidalCategory 𝕄
  field
    _∼_      : {A B : Obj} → Rel (A ⇒ B) e′
    ∼-equiv  : {A B : Obj} → IsEquivalence (_∼_ {A} {B})
    ≈⇒∼      : {A B : Obj} {f g : A ⇒ B} → f ≈ g → f ∼ g
    ∘-resp-∼ : {A B C : Obj} {f h : B ⇒ C} {g i : A ⇒ B} → f ∼ h → g ∼ i → (f ∘ g) ∼ (h ∘ i)
    ⊗-resp-∼ : {A B C D : Obj} {f h : A ⇒ B} {g i : C ⇒ D} → f ∼ h → g ∼ i → (f ⊗₁ g) ∼ (h ⊗₁ i)

module _ {o ℓ e e′} (𝕄 : MonoidalCategory o ℓ e) (Q : MonoidalCongruence 𝕄 e′) where
  private module M = MonoidalCategory 𝕄
  open MonoidalCongruence Q

  quotient : MonoidalCategory o ℓ e′
  quotient = record { U = 𝒬 ; monoidal = monoidalHelper 𝒬 record
    { ⊗ = record { F₀ = M.⊗.F₀ ; F₁ = M.⊗.F₁ ; identity = ≈⇒∼ M.⊗.identity
                 ; homomorphism = ≈⇒∼ M.⊗.homomorphism ; F-resp-≈ = λ (p , q) → ⊗-resp-∼ p q }
    ; unit = M.unit ; unitorˡ = lift≅ M.unitorˡ ; unitorʳ = lift≅ M.unitorʳ
    ; associator = lift≅ M.associator
    ; unitorˡ-commute = ≈⇒∼ M.unitorˡ-commute-from ; unitorʳ-commute = ≈⇒∼ M.unitorʳ-commute-from
    ; assoc-commute = ≈⇒∼ M.assoc-commute-from ; triangle = ≈⇒∼ M.triangle
    ; pentagon = ≈⇒∼ M.pentagon } }
    where
    𝒬 : Category o ℓ e′
    𝒬 = record { Obj = M.Obj ; _⇒_ = M._⇒_ ; _≈_ = _∼_ ; id = M.id ; _∘_ = M._∘_
               ; assoc = ≈⇒∼ M.assoc ; sym-assoc = ≈⇒∼ M.sym-assoc ; identityˡ = ≈⇒∼ M.identityˡ
               ; identityʳ = ≈⇒∼ M.identityʳ ; identity² = ≈⇒∼ M.identity²
               ; equiv = ∼-equiv ; ∘-resp-≈ = ∘-resp-∼ }
    lift≅ : {A B : M.Obj} → M.U [ A ≅ B ] → 𝒬 [ A ≅ B ]          -- same arrows, ≈⇒∼ on isoˡ/ʳ

  -- identity on objects and morphisms; the laws are idF's, read through ≈⇒∼
  quotientF : StrongMonoidalFunctor 𝕄 quotient
  quotientF = record
    { F = record { F₀ = λ A → A ; F₁ = λ f → f ; identity = ∼-refl ; homomorphism = ∼-refl
                 ; F-resp-≈ = ≈⇒∼ }
    ; isStrongMonoidal = record
      { ε = ≅-refl ; ⊗-homo = idⁿ-components   -- η = M.id, commute = ≈⇒∼ id-comm-sym
      ; associativity = ≈⇒∼ (IsStrongMonoidalFunctor.associativity (idF-IsStrongMonoidal 𝕄))
      ; unitaryˡ = ≈⇒∼ (IsStrongMonoidalFunctor.unitaryˡ (idF-IsStrongMonoidal 𝕄))
      ; unitaryʳ = ≈⇒∼ (IsStrongMonoidalFunctor.unitaryʳ (idF-IsStrongMonoidal 𝕄)) } }

  -- a presheaf blind to ∼ descends with its tests untouched
  descend : (P : Presheaf M.U (Setoids cs ℓs))
          → ({A B : M.Obj} {f g : A M.⇒ B} → f ∼ g → Setoids cs ℓs [ Functor.₁ P f ≈ Functor.₁ P g ])
          → Presheaf (MonoidalCategory.U quotient) (Setoids cs ℓs)
  descend P resp = record { F₀ = P.₀ ; F₁ = P.₁ ; identity = P.identity
                          ; homomorphism = P.homomorphism ; F-resp-≈ = resp }

  descendᵛ : PresheafMorphism (StrongMonoidalFunctor.F quotientF) P (descend P resp)
  descendᵛ = record { ν = ntHelper record
    { η = λ _ → record { to = λ x → x ; cong = λ e → e } ; commute = λ _ → Setoid.refl _ } }
```

The congruence is built where the seal is transparent, as `UC/Model/Seal.agda` does (header,
disciplines 1–4), so 𝔾ᴿ quotients the *sealed* 𝔾ᵒ.

```agda
-- UC/RandomSystems/Seal.agda (--safe --without-K --guardedness)
opaque
  unfolding 𝔾ᵒ unprocᵒ procᵒ

  congᴿ : MonoidalCongruence 𝔾ᵒ 0ℓ
  congᴿ = record
    { _∼_ = λ {X} {Y} → _≈ᴿ_ {proj₁ X ⊎ proj₂ Y} {proj₂ X ⊎ proj₁ Y}
    ; ∼-equiv = ≈ᴿ-isEquivalence ; ≈⇒∼ = ≈ᴹ⇒≈ᴿ
    ; ∘-resp-∼ = composeᴳ-resp-≈ᴿ ; ⊗-resp-∼ = ⊗₁ᴳ-resp-≈ᴿ }

  ∼ᴿ⇒Obs : {u v : 𝟘ᵒ G.⇒ Ωᵒ} → MonoidalCongruence._∼_ congᴿ u v → Obs u Ap.∼ᵃ Obs v
  ∼ᴿ⇒Obs e ε pos = ≈ₚ[]-resp (≈sym (runᴹ≈runˢ _ _)) (≈sym (runᴹ≈runˢ _ _))
                              (e (closeˢ (ask tt out)) ε pos)

  -- one coercion per shape, both ways: ≈ᴿ⇒∼ᴿ (Proc, via procᵒ) and ∼ᴿ⇒≈ᴿ (via unprocᵒ)
```

```agda
{-# OPTIONS --safe --without-K --guardedness #-}

-- Random systems (maurer2002 Defs 3, 9, 10): 𝔾ᵒ with simulation coarsened to behavioural
-- equality.  See docs/uc-setup-random-systems.md.

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Presheaf
open import Level

-- `using`: UC.Model.Setup re-exports StdUC 𝔾ᵒ ℰᵒ, which clashes with the open below
open import CategoricalCrypto.UC.Model.Seal using (𝔾ᵒ)
open import CategoricalCrypto.UC.Model.Setup using (ℰᵒ)
open import CategoricalCrypto.UC.RandomSystems.Seal
import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.RandomSystems.Setup where

𝔾ᴿ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ
𝔾ᴿ = quotient 𝔾ᵒ congᴿ

-- tests t : B ⇒ Ωᵒ, t ≋ t′ ⟺ ∀ m : 𝟘ᵒ ⇒ B, Obs (t ∘ m) ∼ᵃ Obs (t′ ∘ m): ℰᵒ's, by descent
ℰᴿ : Presheaf (MonoidalCategory.U 𝔾ᴿ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᴿ = descend 𝔾ᵒ congᴿ ℰᵒ ∼ᴿ⇒≋     -- ∼ᴿ⇒≋ e m = ∼ᴿ⇒Obs (∘-resp-∼ (∘-resp-∼ ∼-refl e) ∼-refl)

open Std2.StdUC 𝔾ᴿ ℰᴿ public
```

### 3.5 Levels, options, layout

Objects, machines, `id = σ⇒`, `∘ = composeᴳ`, `⊗ = _⊗₁ᴳ_`, unit `(⊥ , ⊥)`, unitors and associator
are 𝔾ᵒ's verbatim; only `_≈_` changes.  `_≈ᴿ_ : Set` (it quantifies over `Strat X Y : Set` and ℚ),
so `𝔾ᴿ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ` and `StdSetup : UCSetup (suc 0ℓ) (suc 0ℓ) 0ℓ
(suc 0ℓ) (suc 0ℓ) 0ℓ (suc 0ℓ) (suc 0ℓ)`; `ℰᴿ` keeps `ℰᵒ`'s `cs = ℓs = suc 0ℓ`, as
`UCSetupMorphism` requires (`UCSetup/Morphism.agda:25-26`), and `StdUCMorphism` allows `e = 0ℓ`
against 𝔾ᵒ's `suc 0ℓ`.  OPTIONS: `--safe --without-K` for the generic `Quotient`;
`--safe --without-K --guardedness` for `UC/Machine/Behaviour{,/Absorb,/Trace,/Congruence,/Finite}`
and `UC/RandomSystems/{Seal,Setup,Morphism,FullAbstraction}` (Dₚ).  Layout: §6.

## 4. Morphisms

### 4.1 `protocol-rewrite → RS`

`StdUCMorphism` applies: `quotientF` is strong monoidal on the nose.

```agda
-- UC/RandomSystems/Morphism.agda (--safe --without-K --guardedness)
import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.RandomSystems.Setup as Sᴿ

rewrite⇒RS : UCSetupMorphism Sᵒ.StdSetup Sᴿ.StdSetup
rewrite⇒RS = StdUCMorphism 𝔾ᵒ Sᴿ.𝔾ᴿ ℰᵒ Sᴿ.ℰᴿ (quotientF 𝔾ᵒ congᴿ) (descendᵛ 𝔾ᵒ congᴿ ℰᵒ ∼ᴿ⇒≋)

-- the payoff: a behavioural equality is a UC-equivalence of protocol-rewrite
≈ᴿ⇒≈ᵁ : {f g : A Sᵒ.⇒ Sᵒ.T₀ X B} → MonoidalCongruence._∼_ congᴿ f g → f Sᵒ.≈ᵁ g
≈ᴿ⇒≈ᵁ e Y = Transfer.mono⇒reflects-≈ℰ rewrite⇒RS (λ x → x) (Sᴿ.≈C⇒≈ᵁ e Y)

≤UC-resp-≈ᴿ : f ∼ᴿ f′ → g ∼ᴿ g′ → f Sᵒ.≤UC g → f′ Sᵒ.≤UC g′    -- dummy-complete + ≈ᵁ-trans
```

| component | value | obligation | discharged by |
|---|---|---|---|
| `F` | `F₀ A = A`, `F₁ f = f` | F-resp-≈: `≈ᴹ ⇒ ∼ᴿ` | `≈ᴹ⇒≈ᴿ` (§3.2), as `congᴿ`'s `≈⇒∼` |
| | | identity, homomorphism up to `∼ᴿ` | `∼-refl`: on the nose |
| `Φ` | `StrongMonoidalFunctor.monoidalFunctor quotientF` | lax-monoidal laws | `≈⇒∼` of `idF-IsStrongMonoidal 𝔾ᵒ` |
| `κ` | `Oplax.δ`, i.e. `id` | κ-return, κ-sub, κ-ext | `Standard2/Morphism.agda:43-55`, generic |
| `ν` | `descendᵛ`, identity `Func`s | cong; naturality | `λ e → e` (same setoid `ℰᵒ.₀ A`); refl (both sides `t ∘ f`) |

Reused: `StdUCMorphism`, `Oplax`, `idF-IsStrongMonoidal`, `Transfer.mono⇒reflects-≈ℰ`
(`Abstract2/Morphism.agda:51-52`), `ℰᵒ`.  New: `quotient`, `quotientF`, `descend`, `descendᵛ`,
`congᴿ`, `∼ᴿ⇒Obs`.  There is no morphism back: with `F = id`, F-resp-≈ would be `∼ᴿ ⇒ ≈ᴹ`
(false, §4.2), and another F would need canonical representatives of behaviours, i.e. a quotient;
RS-proved equalities reach protocol-rewrite through `≈ᴿ⇒≈ᵁ` and `≤UC-resp-≈ᴿ` instead.

### 4.2 Full abstraction, and what `Mono` does and does not say

`descendᵛ` is `Mono` and `Epi` (`Presheaf/Morphism.agda:47-52`) by `λ e → e` and `y , refl`: tests
and `_≋_` are unchanged, so `Transfer.epi⇒preserves-≈ℰ`/`mono⇒reflects-≈ℰ` only say that F
leaves the kernel alone.  Full abstraction is about *morphisms*: is `ℰᴿ`'s kernel (`ℰᵒ`'s `≈ℰ`)
equal to `∼ᴿ`, i.e. is `ℰᴿ` `Faithful` (`UCSetup.agda:149-151`)?

| inclusion | status |
|---|---|
| `∼ᴿ ⊆ ≈ℰ` (soundness) | holds: it is `ℰᴿ`'s `F-resp-≈` |
| `≈ℰ ⊆ ∼ᴿ` | **false** (§5.3, `¬gradeStableᵒ`); so `ℰᴿ` is not faithful, and neither RS nor 𝔾ᵒ is `GradeStable` (same `T₁`, same `≈ℰ`) |
| `≈ᵁ` `⊆ ∼ᴿ` | proved (`FullAbstraction.≈ᵁ⇒≈ᴿ`, at any grade): ancilla `A* = Neg A ⇿ Pos A`, closure the cup `𝟘ᵒ ⇒ A* ⊗ A`, test `strategyEnv` running `d`; `play-cup : Obs (tstᵈ ∘ T₁ A* f ∘ cup) ≈ₚ runˢ f d` (§6 step 8).  With `≈ᴿ⇒≈ᵁ`: **`∼ᴿ = ≈ᵁ`** |
| `≈ᴮ ⊆ ∼ᴿ` (Def 3 ⇒ adaptive) | classical (lochbihler2019cc Thm 2); proved for a finite query alphabet with decidable equality (`Behaviour/Finite.≈ᴮ⇒≈ᴿ-fin`, §6 step 9); planned for deterministic machines (`det-≈ᴮ⇒≈ᴿ`); open for bare `Set`s |
| `∼ᴿ ⊆ ≈ᴹ` | false (lazy vs eager sampling; lochbihler2019cc Fig. 6) |

To make `ℰᴿ` faithful, replace its tests by ancilla-closed pairs `(Y , t : Y ⊗ B ⇒ Ωᵒ)` as
machine-iso does (`Machine/UC.agda:14-19`): the kernel becomes `≈ᵁ = ∼ᴿ`, `GradeStable` is
hypothesis-free, and ν (`t ↦ (unit , t)`) stays `Mono` but stops being `Epi`.  Optional.

### 4.3 Other setups

- **ITM → RS** (`docs/uc-setup-itm.md`): `composeᵁ rewrite⇒RS itm⇒prot`; nothing on this side.
- **machine-iso → RS**: through protocol-rewrite after landscape §2's three changes, by `composeᵁ`.
- **IPDL → RS** (`docs/uc-setup-ipdl.md`): strong monoidal (⊎ both sides).  RS provides `∼ᴿ`, the
  `Absorbs` congruences (IPDL's composition rules), `≈ᴹ⇒≈ᴿ`, `≈ᴮ⇒≈ᴿ-fin` (IPDL's value types are
  finite, so axioms may be checked non-adaptively), `≈ᴿ⇒≈ᵁ`.  `≈_ε` with ε > 0 does not land here.
- **origin/machine-category → RS**: `≈ᵗ` is possibilistic, so only the deterministic fragment
  maps (landscape §2 items 2–3: `detₚ` steps, silence ↦ `botₚ`; `Machineᵖ` already has `init`).
  F-resp-≈: `≈ᵗ` gives equal deterministic runs, hence `≈ᴮ`, hence `det-≈ᴮ⇒≈ᴿ`, with no
  decidable equality.  Reflection (`∼ᴿ ⇒ ≈ᵗ` on images) needs decidable equality on messages;
  with it, RS supplies the `∘ᵖ`-congruence that branch could not prove.
- **symbolic** (`docs/uc-setup-symbolic.md`): none.  Exact soundness fails once names exist (a
  sampled nonce is guessed with positive probability, canettiherzog2006; backes2003library §5.3),
  and negligible soundness needs a `QEvaluation` — 𝔾ᴿ's is `qevaluationᴿ` (§4.4), but that plan
  targets 𝔾ᵒ's tier.
- **Causal boxes** (`docs/uc-setup-causal-boxes.md`): none, either direction (§4.1–4.2 there).
- **SSP** (`docs/uc-setup-ssp.md`): none.  `morphism wireᵖ` is not the G-identity under any
  distinguisher equality — a `Strat` may send an unsolicited answer (`Protocol/Machine.agda:14-19`).

### 4.4 Toolkit: Δ, composition, hybrids, security-only construction

Branch `rs-toolkit`; all proved, `--safe`, no postulates.  New modules
`Approx/Rational.agda` (generic), `UC/RandomSystems/{Advantage,Composition,Construction}.agda`;
`Behaviour/Absorb.agda` gains `absorbs-dom` and `Behaviour/Congruence.agda` exports its G-level
`Absorbs` instances, the old lemmas re-derived from them with their statements unchanged.

**Δ** (maurer2002 Def 10, maurer2011cc §4.5).  A verdict mass is a lower real, never a number
(`Dp/Advantage.agda`), so Δ is a relation in a rational slack, and the slack is *closed*:

```agda
-- Approx/Rational.agda, for any approximation A with rational errors (module Closure A)
record _≈̄[_]_ (x : Obs) (ε : ℚ) (y : Obs) : Set ℓa where
  constructor slack
  field ≈̄⇒≈ : (δ : ℚ) → 0ℚ ℚ.< δ → x ≈[ ε ℚ.+ δ ] y
-- UC/RandomSystems/Advantage.agda; Verdict = Closure Approximationᴹ, the closure of _≈ₚ[_]_
Δ[ d ]⟨ f , g ⟩≤ ε = runˢ f d Verdict.≈̄[ ε ] runˢ g d
f ≈ᴿ[ ε ] g        = (d : Strat X Y) → Δ[ d ]⟨ f , g ⟩≤ ε     -- Δ^𝒟, 𝒟 = every Strat
```

Open, Δ ≤ 0 would be `≈ₚ[ 0ℚ ]`, strictly finer than `≈ᴿ` (rejection sampling, §3.1), and a
bound would not survive a `≈ᴿ`-change of a machine.  Closed, `≈ᴿ` is the limit both at zero and
from above, and Δ is a distance on 𝔾ᴿ's homs.  The closure is a record so that ε is recoverable
by unification (`ε + δ` alone is not).

| statement | name |
|---|---|
| compatible with `_≈ₚ[_]_`: `runˢ f d ≈ₚ[ ε ] runˢ g d → Δ[ d ]⟨ f , g ⟩≤ ε`, and back at `ε + δ` for every δ > 0 | `Verdict.≈⇒≈̄`, the field `Verdict.≈̄⇒≈` |
| triangle inequality (maurer2002 Lemma 5(i)) | `Verdict.≈̄-trans` (per distinguisher), `≈ᴿ[]-trans` |
| approximations of machines: per distinguisher, uniform | `advantage d`, `approxᴿ` |
| `≈ᴿ` at zero: `(f ≈ᴿ g) ⇔ (f ≈ᴿ[ 0ℚ ] g)` | `≈ᴿ⇔≈ᴿ[0]` |
| `≈ᴿ` from above: `(f ≈ᴿ g) ⇔ (∀ ε → 0ℚ < ε → f ≈ᴿ[ ε ] g)` | `≈ᴿ⇔≈ᴿ[+]` |
| Δ descends to 𝔾ᴿ: `f′ ≈ᴿ f → g ≈ᴿ g′ → f ≈ᴿ[ ε ] g → f′ ≈ᴿ[ ε ] g′` | `≈ᴿ[]-resp` |
| generic: the closure is closed, its zero error is `∼ᵃ`, a bound respects `∼ᵃ` | `≈̄-closed`, `≈̄[0]⇔∼ᵃ`, `≈̄-resp-∼ᵃ` |

**The composition theorem** (maurer2002 Lemma 5(ii)–(iii); maurer2011cc Def 2, Lemma 1).  `Absorbs`
(§3.3) is the simulation of a context 𝒞 by a distinguisher; `♯ d b i` is d∘𝒞 cut off at budget
`i` with verdict `not b`.  A context may loop while `Strat` is well-founded, so d∘𝒞 is the family
of cut-offs and Δ^{d∘𝒞}(f, g) ≤ ε means every member is within ε:

```agda
absorbs-dom  : (𝔸 : Absorbs C) (d : Strat X′ Y′) (b : Bool)                   -- Absorb.agda
             → ((i : Ix) → Dom (indᵇ b) ε (runˢ f (♯ d b i)) (runˢ f′ (♯ d b i)))
             → Dom (indᵇ b) ε (runˢ (C f) d) (runˢ (C f′) d)
absorbs-Δ    : (𝔸 : Absorbs C) (d : Strat X′ Y′)                              -- Composition.agda
             → ((b : Bool) (i : Ix) → Δ[ ♯ d b i ]⟨ f , g ⟩≤ ε) → Δ[ d ]⟨ C f , C g ⟩≤ ε
absorbs-≈ᴿ[] : Absorbs C → f ≈ᴿ[ ε ] g → C f ≈ᴿ[ ε ] C g
```

`absorbs⇒resp` (§3.3) is `absorbs-dom` at every positive slack.  The instances are the five raw
ones and, exported from `Behaviour/Congruence.agda`, G-composition with the hole on either side
and the G-tensor (`∘ᴳ-absorbˡ`, `∘ᴳ-absorbʳ`, `⊗₁ᴳ-absorbˡ`, `⊗₁ᴳ-absorbʳ`):

| context | statement | raw `𝒢ₚᴹ` | sealed 𝔾ᵒ |
|---|---|---|---|
| cascade (Lemma 5(iii)) | `f ≈ᴿ[ ε ] h → g ≈ᴿ[ δ ] i → f ∘ g ≈ᴿ[ ε + δ ] h ∘ i` | `composeᴳ-≈ᴿ[]` | `∘-resp-∼ᴿ[]` |
| tensor (Def 2 (3)) | `… → f ⊗₁ g ≈ᴿ[ ε + δ ] h ⊗₁ i` | `⊗₁ᴳ-≈ᴿ[]` | `⊗-resp-∼ᴿ[]` |
| hom equality, closed homs, a closing context | `f G.≈ g → f ∼ᴿ[ 0ℚ ] g`; `u ∼ᴿ[ ε ] v → Obs u ≈̄[ ε ] Obs v`; `f ∼ᴿ[ ε ] g → Obs ((t ∘ (id ⊗₁ f)) ∘ m) ≈̄[ ε ] Obs ((t ∘ (id ⊗₁ g)) ∘ m)` | | `≈⇒∼ᴿ[0]`, `obs-∼ᴿ[]`, `close-∼ᴿ[]` |

On 𝔾ᵒ, `f ∼ᴿ[ ε ] g = unhomᵒ f ≈ᴿ[ ε ] unhomᵒ g` (`FullAbstraction.unhomᵒ`), with `approxᵒ` and
`∼ᴿ⇔∼ᴿ[0] : (f Q.∼ g) ⇔ (f ∼ᴿ[ 0ℚ ] g)`; one `opaque unfolding unhomᵒ` block proves the sealed
rows from the raw ones.  Not tracked: Maurer's budget k′ = m_𝒞(k).  Δ ranges over all strategies,
and the ask bounds (`asks≤`) of `♯ d b i` are not computed, which a query-bounded Δₖ would need.

**Hybrids.**  `Approx.Rational.hybrid`, at any approximation with rational errors:

```agda
hybrid : (H : Fin (suc n) → Obs) (ε : Fin n → ℚ) → ((i : Fin n) → H (inject₁ i) ≈[ ε i ] H (suc i))
       → H zero ≈[ ∑[ i < n ] ε i ] H (fromℕ n)
```

At `advantage d`, `approxᴿ` and `approxᵒ` it is Δ(H₀, Hₙ) ≤ Σ Δ(Hᵢ, Hᵢ₊₁) per distinguisher,
uniformly, and on 𝔾ᵒ.  The hybrid argument proper, one replacement per step, is
`hybrid-absorbs`: if hybrid i is ≈ᴿ-equal to `C i f` and hybrid i+1 to `C i g`, each `C i`
absorbable, then `f ≈ᴿ[ ε ] g` gives `H zero ≈ᴿ[ ∑[ i < n ] ε ] H (fromℕ n)`.

**Security-only construction** (maurer2011cc §5.1 Def 3, condition 2;
Def 2 is the compatibility of §4.4 there), with d = Δ over every `Strat` (`Construction.agda`):

```agda
Constructs ε f g = Σ[ s ∈ Y ℐ.⇒ X ] f ∼ᴿ[ ε ] (sub s ∘ g)     -- f = π R, g = S, s = σ
```

| statement | name |
|---|---|
| at ε = 0 it is UC-emulation over 𝔾ᵒ: `(f Sᵒ.≤UC g) ⇔ Constructs 0ℚ f g` | `≤UC⇔Constructs₀` |
| … and over 𝔾ᴿ along `rewrite⇒RS`: `(Transfer.G rewrite⇒RS f Sᴿ.≤UC Transfer.G rewrite⇒RS g) ⇔ Constructs 0ℚ f g` | `≤UCᴿ⇔Constructs₀` (via `≈ᵁᴿ⇒∼ᴿ`) |
| Δ against `UC.Quantitative.Observed`'s `≈ᵁ[ε]` at 𝔾ᵒ (`UC.Model.Quantitative.QUCᵒ`): `(f ∼ᴿ[ ε ] g) ⇔ (∀ δ → 0ℚ < δ → f QUCᵒ.≈ᵁ[ ε + δ ] g)` | `≈ᵁ[]⇒∼ᴿ[]` (the cup, `play-cup`), `∼ᴿ[]⇒≈ᵁ[]` (`close-∼ᴿ[]`), `∼ᴿ[]⇔≈ᵁ[]` |
| the ε-version: `Constructs ε f g ⇔ Witness⁺ ε f g`, `Witness⁺ ε f g = Σ[ s ] (∀ δ → 0ℚ < δ → QUCᵒ.At s (ε + δ) f g)`; `QUCᵒ.Witness ε f g → Constructs ε f g` | `Constructs⇔Witness⁺`, `Witness⇒Constructs` |
| Thm 1, security obligations: (iii); (i), simulators composed in fn. 15's order, error ε + ε′; serial composition (`UC-compose`), simulator `(id ⊗ t) ∘ (s ⊗ id)`, error ε′ + ε | `constructs-refl`, `constructs-trans`, `constructs-∙` |
| exact, at 𝔾ᴿ (`UC/RandomSystems/Quantitative.agda`, `QUCᴿ` = Observed at 𝔾ᴿ read through `Verdict.closure`, `qevaluationᴿ`): `(f QUCᴿ.≈ᵁ[ ε ] g) ⇔ (f ∼ᴿ[ ε ] g)` | `≈ᵁᴿ[]⇒∼ᴿ[]` (the cup), `∼ᴿ[]⇒≈ᵁᴿ[]` (`close-∼ᴿ[]`), `≈ᵁᴿ[]⇔∼ᴿ[]` |
| Def 3 condition 2 at ε, exactly: `f ≤UCᴿ[ ε ] g = QUCᴿ.Witness ε f g`, `(f ≤UCᴿ[ ε ] g) ⇔ Constructs ε f g`; at zero `(G f Sᴿ.≤UC G g) ⇔ (f ≤UCᴿ[ 0ℚ ] g)` | `≤UCᴿ[]⇔Constructs`, `≤UCᴿ⇔≤UCᴿ[0]` |
| along `rewrite⇒RS` (`G = Transfer.G rewrite⇒RS`), pointwise: 𝔾ᵒ's error crosses unchanged, `f QUCᵒ.≈ᵁ[ ε ] g → G f QUCᴿ.≈ᵁ[ ε ] G g` and `QUCᵒ.Witness ε f g → G f ≤UCᴿ[ ε ] G g`; 𝔾ᴿ's is the slack closure of 𝔾ᵒ's, `(G f QUCᴿ.≈ᵁ[ ε ] G g) ⇔ (∀ δ → 0ℚ < δ → f QUCᵒ.≈ᵁ[ ε + δ ] g)` and `(G f ≤UCᴿ[ ε ] G g) ⇔ Witness⁺ ε f g` | `≈ᵁ[]⇒≈ᵁᴿ[]`, `Witness⇒≤UCᴿ[]`, `≈ᵁᴿ[]⇔≈ᵁ[]⁺`, `≤UCᴿ[]⇔Witness⁺` (with `≈ᵁᴿ[]-G⇔`, `≤UCᴿ[]-G⇔`) |
| Thm 1's security obligations at `≤UCᴿ[ ε ]`: errors 0, ε + ε′, ε′ + ε as above | `≤UCᴿ[]-refl`, `≤UCᴿ[]-trans`, `≤UCᴿ[]-∙` |

The levels permit the ε-version: `QUCᵒ.≈ᵁ[ε]` is `Set₁` (it quantifies over ancillas), Δ is
`Set`, and the `⇔`s straddle them.  At 𝔾ᵒ it holds up to every positive slack, not at ε itself,
because Observed's readout space there is `spaceᴹ`, the open `_≈ₚ[_]_`; the simulator is fixed
before the slack, `Witness₊`'s discipline (`UC/Quantitative/Bridge.agda`).  The open space is no
`QEvaluation` over 𝔾ᴿ: its zero error is `≈ₚ`, which 𝔾ᴿ's hom equality `∼ᴿ` does not imply
(§3.1).  The closed one is: its zero error is `∼ᵃ` (`≈̄[0]⇔∼ᵃ`), which `∼ᴿ⇒Obs` reads off a
closed `∼ᴿ`.  There the match is exact — `close-∼ᴿ[]` lands at `≈̄[ ε ]` and the cup reads it
back — and so is Def 3's security condition at ε. `UC/Quantitative.agda` has no
quantitative `UCSetupMorphism`, so the relation to `QUCᵒ` is stated pointwise.
Thm 1's security obligations at `≤UCᴿ[ ε ]` are `constructs-*` transported along
`≤UCᴿ[]⇔Constructs`; `QUCᴿ.at-trans` and `QUCᴿ.at-compose` give the same errors
directly. Availability is a separate obligation (§4.5); the emulation equivalences
do not fix the designated no-adversary converters. Thm 1 (ii), parallel construction,
still needs a graded tensor and the interchange
`(X ⊗ B) ⊗ (X′ ⊗ B′) ≅ (X ⊗ X′) ⊗ (B ⊗ B′)`.

**Amplification** (maurer2007 Thm 1, the product theorem): not attempted.  Its proof rests on
Lemma 5 there, systems with a monotone binary output whose conditionals are
`min(p^S_{Yⁱ|Xⁱ}, p^T_{Yⁱ|Xⁱ})` and differences of such, and on Δ being the statistical distance of
transcripts (Def 12 there): conditionals, minima and differences of masses, which `Dₚ`'s lower
reals do not form — the wall that rules out Lochbihler's `trace` (§3.1 (1)).

### 4.5 Full secure construction with designated no-adversary modes

`UC/RandomSystems/Availability.agda` implements both obligations of Maurer 2011
§5.1 Definition 3 at an already-compiled honest boundary `f = πR`, `g = S`.
The grade is the aggregate Eve interface; the remaining boundary `A ⇒ B`
contains the honest interfaces. Fix `a : X ⇒ I` and `b : Y ⇒ I` in advance:
their outside interfaces are empty, but they can answer internal queries that
select a resource's no-adversary mode (the paper's cheating-bit example).
Closing Eve is `no-adversary a f = unitorˡ.from ∘ (sub a ∘ f)`.

```agda
AvailableWithin εₐ a b f g = no-adversary a f ∼ᴿ[ εₐ ] no-adversary b g
SecurelyConstructs εₛ εₐ a b f g
  -- fields: security : Constructs εₛ f g
  --         availability : AvailableWithin εₐ a b f g
```

Both bounds use the existing closed rational advantage over **every** adaptive
well-founded `Strat`. The security simulator is one converter chosen before all
strategies and all positive slacks; the availability converters are designated
parameters, not existential simulators. With `εₛ = εₐ = ε` and a shared designated
converter `a = b = ⊥` at the same Eve interface, these are Definition 3's two
inequalities at this compiled boundary. Distinct typed converters give the
resource-specific-mode generalization. The qualitative
`SecureConstruction a b f g` uses `f ≤UC g` for security and behavioural
`Available a b f g` for availability; `SecureConstruction⇔SecurelyConstructs₀`
proves equivalence at `(0, 0)`. Record constructors introduce both obligations,
and their `.security` / `.availability` projections expose them independently.

`secure-construction-factor` derives both obligations from a machine factoring
and explicit converter compatibility `a ∘ s ∼ᴿ b`: the simulator must preserve
the designated ideal no-adversary mode. `securely-constructs-trans` adds the two
security errors and the two availability errors separately, provided the
intermediate designated converters are behaviourally equal. Its qualitative
counterpart is `secure-construction-trans`. This is replacement composition at
a fixed honest boundary, not an unproved full parallel-construction theorem or
the full honest-protocol serial theorem of the paper.

`Examples/RandomSystems/Availability.agda` proves the concrete counterexample:
the ideal server asks Eve which bit to answer; the no-adversary converter answers
`true`, while a forced-false simulator answers `false`. `security-only` gives
zero-error `Constructs`, but `not-available`, `not-full`, and `not-full₀` reject
the designated full construction. `mode-bit` and `bit-run` compute the two closed
executions, and `tell` is the honest one-query separating strategy.
`forced-true-full` / `forced-true-full₀` prove a nonidentity forced-true simulator
with the **same** designated `mode true` on both sides, the literal shared-⊥
specialization. A bit-flipping simulator with compatible resource-specific
designated answers gives `flipped-full` / `flipped-full₀`; `twice-full` /
`twice-full₀` exercise both composition entry points and return to a shared mode.
No security or availability premise is assumed for these examples.
`HashForwardConsumer.hash-security` also transports the existing inhabited-grade,
three-state HashForward simulator through `≤UC⇒Constructs₀`, and `hash-rs`
consumes `Constructs₀⇒≤UCᴿ`. This is security-only coverage: no availability
theorem for arbitrary HashForward resources is claimed.

The ambient model remains the effectful-machine quotient: initialization is
eager and may diverge, and activation feedback may diverge. This predicate does
not certify normalized random systems, probabilistic termination, per-query
budgets, feasibility, or a separate syntactic Alice/Bob converter discipline.
Comparisons with Maurer 2002's normalized resources or CryptHOL's termination
assumptions require those restrictions independently; adding availability does
not remove them.

### 4.6 Concrete positive-error construction

`Examples/FaultFlag.agda` and `Examples/FaultFlag/UC.agda` exercise **QSetupᴿ**, starting
from raw `Proc`s and crossing the opaque graded seal.  This is a SECURITY-ONLY construction,
not a theorem of `SecurelyConstructs`: no designated no-adversary converters or availability
proof are provided here.  The separate full predicate is described in §4.5.

The resource is a persistent fault flag: initialization samples one Boolean, and every
honest read returns that same bit.  The real resource samples `true` with probability `½`,
the intermediate one with `¼`, and the ideal always answers `false`.  Repeating reads cannot
amplify a single cached sample.  The adversary can independently request the resource's
version tag (`original`, `previous`, `latest` respectively).  The simulator is a live
stateless converter: it forwards the request and translates the returned tag by one
revision.  On the relevant transactions it maps `latest → previous → original`; it is not
an identity or an aborting scalar.  The two probabilistic initial laws have mass exactly
one at depth 2 (`initialization-mass`).

| module | public evidence |
|---|---|
| `Examples.FaultFlag` | `half-quarter-cache` and `quarter-false-cache`: uniform `≈ᴿ[¼]` bounds for every adaptive `Strat`, proved by finite cumulative-mass arithmetic and `cum-≤1`, with no security premise |
| same | `cache-simulates`, `false-cache-clean`: actual machine equalities used only to place the version translator and remove the deterministic cached state; they do not supply the positive error |
| same | `cache-read`, `clean-read`, `half-true`, `quarter-true`, `component-gap`: the honest event is “the returned fault bit is true”; its masses are `½`, `¼`, `0`, with a quarter gap at each step |
| same | `simulator-reply`, `double-simulator-reply`, `simulator-not-identity`, `double-simulator-not-identity`: live request/reply executions and refutations of zero-error equality to the identity, including the composed simulator |
| same | `simulated-clean-read`, `simulated-clean-no-true`: **every** raw simulator leaves honest true-mass zero, even if its initialization diverges; divergence can suppress a false reply but cannot manufacture a true one |
| `Examples.FaultFlag.UC` | `first-security : realᵒ ≤UCᴿ[¼] middleᵒ`, `second-security : middleᵒ ≤UCᴿ[¼] idealᵒ`, `composed-security : realᵒ ≤UCᴿ[¼ + ¼] idealᵒ`, `half-security : realᵒ ≤UCᴿ[½] idealᵒ` |
| same | `composed-simulator`, `composed-simulator-image`: the exported witness uses `simᵒ ∘ simᵒ`, whose raw image is `doubleSimulator` |
| same | `security-condition : Constructs ½ realᵒ idealᵒ`; `no-small-construction` and `no-small-security`: for every rational `ε < ½`, no simulator establishes the corresponding construction or quantitative UC witness |

Composition here is the transitive chain of **two imperfect construction steps**, using
`Quantitative.≤UCᴿ[]-trans` (and hence the existing advantage/context-absorption triangle
argument), not a claim about two independent parallel resources.  The composed half bound
is tight over **all** simulators: one honest read has true-mass `½` in the real system and
zero in every simulated ideal.  The smaller-bound rejection is a checked theorem, not a
reviewer's source-derived counterexample.

The witness quantifier is `∃ simulator, ∀ δ > 0, ∀ adaptive strategy`, with both verdict
masses compared at `ε + δ`; `QUCᴿ` additionally states the equivalent agreement over all
ancilla closing contexts.  The simulator is fixed before the slack and the strategy.
`Composition.{procᵒ-≈ᴿ[],unprocᵒ-∼ᴿ[],gradedᵒ-≈ᴿ[],ungradedᵒ-∼ᴿ[]}` preserve the same
error across the seal; `Model.Seal.procᵒ-unprocᵒ` makes the smaller-bound rejection apply
to arbitrary sealed simulators, not just raw images chosen by the example author.
The UC leaf is registered in `CategoricalCrypto.agda`.  No family tier, query-budget
transformation, availability result or full-Maurer-construction claim is made by this example.

## 5. Hard parts and risks

### 5.1 The absorption proofs

Five `cum` sandwiches in the style of `Dp/Iter.agda` (`stepᵢ-boundA/B`, `Tᵗ`) and
`Dp/Dominate.agda` (`Dom≤`, `dom≤⇒cofinal`, `cofinal-bind`).  The trace instance is the largest:
`loop` is matched against `iterₚ`'s `stepᵢ` through the `returnₚ` junctions of Kleisli `traceStep`
(`Machines/Base.agda:12-15`).  Estimate 1–1.5 kLOC, the trace instance in its own module
(`Machines/G.agda:50-51`: a co-located trace proof measured 397 s against 7 s + 7 s).
**Fallback** if it stalls: `congᴿ := uKernel` (`Standard2/UKernel`, planned in
`docs/uc-setup-ssp.md`), the two-sided ancilla closure `∀ Y Z → (id {Y} ⊗₁ f) ⊗₁ id {Z} ≈ℰ
(id {Y} ⊗₁ g) ⊗₁ id {Z}` (two-sided: 𝔾ᵒ exports no braiding), whose congruence is pre/post-
composition plus associators.  Its level is `suc 0ℓ` (it quantifies over objects), so 𝔾ᴿ's `e`
becomes `suc 0ℓ`; §3.4–§4.1 are otherwise unchanged, and the absorption lemmas move to the
characterisation `≈ᵁ ⇔ ≈ᴿ`.

### 5.2 Coinduction, quotients, K, performance

`--guardedness` wherever Dₚ appears (infective).  No new coinductive definition: `Strat` is
inductive, and `runˢ`, `unfoldˢ`, `♯`, `loop` recurse on the tree or the budget, as `Dp.flatten`
does (`Dp.agda:208-209`); the landscape's "coinductively in Dₚ" is already inside `>>=ₚ-cong`.
Setoids only: `MonoidalCongruence` + `quotient`; the presheaf descends rather than being rebuilt
(a rebuilt `ℰᵒ` costs 80 s against 9 s, `UC/Model/Setup.agda:8-12`).  `--without-K` throughout;
seal coercions are `refl` inside opaque blocks.  Performance: (i) 𝔾ᴿ quotients the sealed 𝔾ᵒ,
so `open StdUC 𝔾ᴿ ℰᴿ` should sit at `UC.Model.Setup`'s floor — if not, seal 𝔾ᴿ as one bundle
under Seal.agda's four disciplines; (ii) `congᴿ`'s body is checked with 𝔾ᵒ unfolded, so every
`_≈ᴿ_` at G-homs takes explicit sum implicits (`UC/Machine.agda:65-69`: inference normalises 𝒢ₚ,
10 GiB); (iii) `composeᴳ`, `_⊗₁ᴳ_` stay opaque, used only through `composeᴳ-raw` and `⊗₁ᴳ-raw`.

### 5.3 Disagreements with the landscape

1. "Whether `ℰᵒ`'s kernel already *is* behavioural equivalence is … whether this morphism is
   `Mono`": `Mono` compares *tests* (`Presheaf/Morphism.agda:50-52`) and holds trivially for
   ν = identity (§4.2).  And the kernel is **not** behavioural equivalence.  Counterexample at
   `A = ⊤ ⇿ Bool`, `B = Bool ⇿ Cmd`, `Cmd = {go, reveal}`, state `Maybe Bool`:
   - `revealᶠ`: on `go`, flip c, store c, answer c on B; on `reveal`, send c on A; on any
     answer on A, `botₚ`.
   - `revealᵍ`: the same, but `go` answers a fresh independent c′.

   They are `≈ℰ`-equal: a closure `m : 𝟘ᵒ ⇒ A` hears c only after `reveal`, and every run that
   reaches m diverges (m can only answer f, which then diverges), so the verdict depends on the
   pre-reveal views, i.i.d. fair bits under both.  They are not `T₁ (Bool ⇿ ⊥)`-`≈ℰ`-equal: m
   forwards c on the ancilla and t compares it with the bit it got (always equal under ᶠ, half
   the time under ᵍ); the `Strat` `ask go; ask reveal; out (x == c)` separates them likewise.
   Hence `¬ GradeStable` for `ℰᵒ`: `bridge` (`Abstract2.agda:124-125`) is unusable there, and an
   `ROData` at `ℰᵒ` would have an unsatisfiable `stable` (`RandomOracle2.agda:73-74`); `≈ᴿ⇒≈ᵁ`
   is the route to `≈ᵁ` artefacts instead.
2. "tests unchanged": in carrier and `≋` yes, but the presheaf is re-based on the quotient with a
   new `F-resp-≈` (`descend`); the term `ℰᵒ` cannot be reused as-is.
3. "Coarser machine equalities go to random systems": yes, but `origin/machine-category`'s `≈ᵗ`
   is possibilistic, so only its deterministic fragment maps (§4.3).

## 6. Work breakdown

Status 2026-10-09; row 11 2026-10-10; row 12 2026-10-10.  "Warm" is a single-module check
(`+RTS -M3G -H1G -RTS`, one `Checking` line) on a ≈12 s startup floor; `UC.Model.Setup` itself
measures 13.7 s.  Every landed row is green with an empty warning gate.  Row 11's times were taken
beside one to three other agda runs on the shared box.

| # | module(s) | landed (exports) | warm |
|---|---|---|---|
| 1 | `Categories/Category/Monoidal/Construction/Quotient.agda` | `MonoidalCongruence` (with `module ∼`), `quotient`, `quotientF : StrongMonoidalFunctor 𝕄 (quotient 𝕄 Q)`, `descend`, `descendᵛ`, `descendᵛ-mono`, `descendᵛ-epi` | 4.4 s |
| 2 | `UC/Machine/Run.agda`; `UC/Machine/Behaviour.agda` | Run: `resumeˢ`, `runFromˢ`, `runˢ`, `runFromˢ-ϕ`, `closeˢ`, `runᴹFrom≈runFromˢ`, `runᴹ≈runˢ`, `runˢ-sim`, `runˢ-resp-≈ᴹ`; `runFrom-ϕ`, `run-sim`, `runᴹ-resp-≈ᴹ` re-derived with their statements unchanged.  Behaviour: `_≈ᴿ_`, `≈ᴿ-isEquivalence`, `≈ᴹ⇒≈ᴿ`, and with step 9 `runᴸFrom`, `runᴸ`, `_≈ᴮ_` | 12.8 s; 12.4 s |
| 3 | `UC/Machine/Behaviour/Absorb.agda` | `wtᴰ`, `unfoldˢ`, `module Approximation` (`Approx`, `approx-ret`, `approx-≈`, `bind-cofinal`, `approx-bind`, `approx-unfold`), `Absorbs`, `absorbs-dom` (row 11), `absorbs⇒resp` (derived from it), `absorbs-∘`, `absorbs-resp`, `absorbs-≈ᴹ`, `approx⇒absorbs` | 12.7 s; 12.8 s with `absorbs-dom` |
| 4 | `…/Behaviour/Trace.agda`; `…/Behaviour/Congruence.agda` | Trace: `loop`, `traceˢ`, `trace-step`, `trace-run`, `loop-approx`, `trace-approx`, `traceᴹ-absorb`.  Congruence: `⊗ᵉ-absorbˡ`, `⊗ᵉ-absorbʳ`, `∘ᴹ-absorbˡ`, `∘ᴹ-absorbʳ` (from `besideˡ`, `besideʳ`, `after`, `before` and their `-approx`), `∘ᴳ-absorbˡ`, `∘ᴳ-absorbʳ`, `⊗₁ᴳ-absorbˡ`, `⊗₁ᴳ-absorbʳ` (row 11), `composeᴳ-resp-≈ᴿ`, `⊗₁ᴳ-raw`, `⊗₁ᴳ-resp-≈ᴿ` (both resp lemmas derived from the G-level instances) | 12.6 s; 21.7 s, 21.0 s with the instances exported |
| 5 | `UC/RandomSystems/Seal.agda` | `congᴿ`, `∼ᴿ⇒Obs`, `≈ᴿ⇒∼ᴿ`, `∼ᴿ⇒≈ᴿ` | 12.8 s |
| 6 | `UC/RandomSystems/Setup.agda` | `𝔾ᴿ`, `∼ᴿ⇒≋`, `ℰᴿ`, `open StdUC 𝔾ᴿ ℰᴿ public` | 13.8 s |
| 7 | `UC/RandomSystems/Morphism.agda` | `rewrite⇒RS : UCSetupMorphism Sᵒ.StdSetup Sᴿ.StdSetup`, `≈ᴿ⇒≈ᵁ`, `≤UC-resp-≈ᴿ` | 13.7 s |
| 8 | `UC/Machine/Cup.agda`; `UC/RandomSystems/FullAbstraction.agda` | Cup: `dualᴵ`, `cupᴵ`, `bendᴹ`, `bend-run`, `cup-≈`, `cup-run`.  FullAbstraction: `≈ᵁ⇒≈ᴿ`, `T₁-≈ℰ⇒∼ᴿ`, `play-cup`, `¬gradeStableᵒ`, `reveal-≈ℰ`; the counterexample `Aʳ`, `Bʳ`, `revealᴹ`, `reveal-∘`, `reveal-≉ᴿ`; seal coercions `dualᵒ`, `unhomᵒ`, `∼ᴿ-intro`, `playᵒ`, `cupᵒ`, `reveal-∘≈`, `reveal-≁ᴿ` | 12.2 s; 13.1 s |
| 9 | `UC/Machine/Behaviour/Finite.agda` | `≈ᴮ⇒≈ᴿ-fin : DecidableEquality X → (enum : List X) → (∀ x → x ∈ enum) → f ≈ᴮ g → f ≈ᴿ g`; its steps `Below`, `FirstAsksIn`, `play`, `answer`, `cut`, `keep`, `drop`, `only`, `without`, `next`, the `asks-`/`first-` bounds, `bind-split`, `feed`, `Ψ`, `feed-cong`, `feed-snoc`, `feed-runᴸ`, `feed-cofinal`, `feed-split`, `play-run`, `cut-approx`, `run-split`, `asked`, `only-step`, `Ψ-split`, `Ψ-only`, `Ψ-askfree`, `Ψ-bounded` | 13.1 s |
| 10 | `src/CategoricalCrypto.agda`; `docs/uc-setup-landscape.md` §4 | entry point; correct the `Mono` remark | not started |
| 11 | `Approx/Rational.agda`; `UC/RandomSystems/Advantage.agda`; `…/Composition.agda`; `…/Construction.agda` (§4.4) | Rational: `½-split`, `module Closure` (`_≈̄[_]_` with `slack`/`≈̄⇒≈`, `≈⇒≈̄`, `≈̄-trans`, `closure`, `≈̄-closed`, `≈̄[0]⇔∼ᵃ`, `≈̄-resp-∼ᵃ`), `hybrid`.  Advantage: `Verdict`, `Δ[_]⟨_,_⟩≤_`, `_≈ᴿ[_]_`, `≈ᴿ[]-trans`, `≈ᴿ[]-mono`, `advantage`, `approxᴿ`, `≈ᴿ⇔≈ᴿ[0]`, `≈ᴿ⇔≈ᴿ[+]`, `≈ᴿ[]-resp`.  Composition: `absorbs-Δ`, `absorbs-≈ᴿ[]`, `hybrid-absorbs`, `composeᴳ-≈ᴿ[]`, `⊗₁ᴳ-≈ᴿ[]`, `_∼ᴿ[_]_`, `approxᵒ`, `∘-resp-∼ᴿ[]`, `⊗-resp-∼ᴿ[]`, `≈⇒∼ᴿ[0]`, `∼ᴿ⇔∼ᴿ[0]`, `obs-∼ᴿ[]`, `close-∼ᴿ[]`.  Construction: `≈ᵁ[]⇒∼ᴿ[]`, `∼ᴿ[]⇒≈ᵁ[]`, `∼ᴿ[]⇔≈ᵁ[]`, `Constructs`, `≤UC⇒Constructs₀`, `Constructs₀⇒≤UC`, `≤UC⇔Constructs₀`, `≈ᵁᴿ⇒∼ᴿ`, `≤UCᴿ⇒Constructs₀`, `Constructs₀⇒≤UCᴿ`, `≤UCᴿ⇔Constructs₀`, `Witness⁺`, `Constructs⇒Witness⁺`, `Witness⁺⇒Constructs`, `Constructs⇔Witness⁺`, `Witness⇒Constructs`, `constructs-refl`, `constructs-trans`, `constructs-∙` | 6.1 s; 13.0 s; 13.7 s; 15.9 s |
| 12 | `UC/RandomSystems/Quantitative.agda` (§4.4, the exact ε-version) | `spaceᴿ`, `qevaluationᴿ`, `module Observedᴿ` (Observed at 𝔾ᴿ), `Qᴿ`, `QSetupᴿ`, `module QUCᴿ`; `≈ᵁᴿ[]⇒∼ᴿ[]`, `∼ᴿ[]⇒≈ᵁᴿ[]`, `≈ᵁᴿ[]⇔∼ᴿ[]`, `_≤UCᴿ[_]_`, `≤UCᴿ[]⇒Constructs`, `Constructs⇒≤UCᴿ[]`, `≤UCᴿ[]⇔Constructs`, `≈ᵁᴿ[]-G⇔`, `≤UCᴿ[]-G⇔`, `≈ᵁ[]⇒≈ᵁᴿ[]`, `Witness⇒≤UCᴿ[]`, `≈ᵁᴿ[]⇔≈ᵁ[]⁺`, `≤UCᴿ[]⇔Witness⁺`, `≤UCᴿ⇔≤UCᴿ[0]`, `≤UCᴿ[]-refl`, `≤UCᴿ[]-trans`, `≤UCᴿ[]-∙` | 24 s at `-M5G -H1G` (exhausts `-M4G`) |

Departures from §3–§5:

- **Step 2.**  The strategy runs live in `UC/Machine/Run.agda`, where `runFrom-ϕ` is re-derived
  from them, not in `Behaviour.agda`.  `runᴸ` and `_≈ᴮ_` landed with step 9; `≈ᴿ⇒≈ᴮ` and
  `det-≈ᴮ⇒≈ᴿ` did not land.  `runᴹ-resp-≈ᴹ`, re-derived through `runˢ`, is `opaque`: it is the
  readouts' `cong`, and transparent it took the merged tree's `UC.Graded` past the 1800 s
  closure ceiling, all in `≤UC[]ᵍ` (warm at `-M3G -H1G`: 74.5 s before the merge, of which
  `≤UC[]ᵍ` 61.5 s; 24.1 s opaque, of which 9.9 s).
- **Step 3.**  `Absorbs` carries an abstract budget type `Ix` and existential depths
  (`lower : … → Σ[ i ∈ Ix ] Σ[ m ∈ ℕ ] cum j (runˢ (C f) d) (indᵇ b) ℚ.≤ cum m (runˢ f (♯ d b i)) (indᵇ b)`)
  instead of `♯ d k v` with a `depth` function; `Approximation b` packages the cut-off calculus.
- **Step 4.**  `⊗₁ᴳ-raw` sits in `Behaviour/Congruence.agda` (opaque, unfolding `midᴹ` and
  `_⊗₁ᴳ_`); `GConstructionMonoidal.agda` is unchanged.
- **Step 8.**  §5.3's counterexample is replaced by a smaller one with the same mechanism:
  `Aʳ = ⊥ ⇿ Bool`, `Bʳ = ⊥ ⇿ ⊤`, and `revealᴹ b` stateless, answering the query from `B` by
  sending `b` on `A`.  A closure of `A` hears `b` and, `Pos Aʳ` being empty, can answer nothing,
  so both composites with it never land and are `≈ᴹ` (`reveal-∘`); hence
  `revealᴹ true ≈ℰ revealᴹ false` (`reveal-≈ℰ`), while the one-ask strategy reads `b`
  (`reveal-≉ᴿ`).  `¬gradeStableᵒ` then follows from `T₁-≈ℰ⇒∼ᴿ` at the ancilla
  `Aʳ* = Bool ⇿ ⊥`, which is §5.3's `Y`.  `≈ᵁ⇒≈ᴿ` holds at every grade and uses that one
  ancilla only: the closure is the cup `I → A* ⊗ A` (new module `UC/Machine/Cup.agda`, whose
  composite with `T₁ᴵ A* f` is `f` read as a closed process, `cup-≈`), the test is
  `UC.Seam.strategyEnv`, and the adequacy is `UC.Seam.Adequacy.adequacy` — no `Absorbs`.  The
  `Dₚ` fact that two runs over an empty type are `≈ₚ` (`≈ₚ-void`) belongs in
  `ProbabilisticLogic.Dp`; it is private to FullAbstraction because editing `Dp` rebuilds the
  whole library.
- **Step 9.**  Not §4.2's indicator decomposition: the first layer of the strategy is split
  along the enumerated query alphabet, exactly at every depth (`run-split`, `Ψ-split`); a fixed
  first question moves into the input prefix, the strategy's coins commuting with the machine's
  step (`>>=ₚ-swap` in `only-step`, `Ψ-only`); the induction is on the ask bound and the
  enumeration, halving the slack per split (`Ψ-bounded`); an ask-free remainder is a
  `[0,1]`-valued test of the prefix's outputs, read at depth `j` as `cum j`, which is what
  `_≈ᴮ_` compares (`Ψ-askfree`); an unbounded strategy is the limit of its cut-offs
  (`cut-approx`).  Only the query alphabet is finite; the answer alphabet is arbitrary.
- **Row 11.**  `Construction.agda` passes the morphisms of `_≤UC_`, `_≈ᵁ_` and `At` explicitly:
  left to inference they are solved by unfolding those relations at the concrete 𝔾ᵒ, and
  `≤UC⇔Constructs₀` alone exhausted a 4 GiB heap in 98 s; explicit, the module is at 15.9 s.
  Measured with `runᴹ-resp-≈ᴹ` opaque (step 2); the inferring version ran past 15 min before that
  change and exhausted 6 GiB in 244 s after it.  `UC.RandomSystems.Construction` is a new leaf,
  not yet in the root (row 10).
- **Row 12.**  Exhausts `-M3G` and `-M4G`: 2.3 GB residency against 1.2 GB for its imports
  alone; the rest is the `Observed` application, which costs `UC.Model.Quantitative` the same (a
  copy of it exhausts `-M4G`).  Checked warm at `-M5G -H1G`.  Morphisms are passed explicitly as
  in row 11.  A new leaf, not yet in the root (row 10).

Order: 1 ∥ 2; 2 → 3 → … → 8; 9 after 2; 11 after 8; 12 after 11.  Steps 1–7 give setup and
morphism, 8–9 the characterisation, 11–12 the toolkit.

## 7. Sources

`maurer2002` (Defs 2, 3, 8–10; §3.3; Lemmas 4, 5), `maurer2011cc` (§4.4 Defs 1–2, §4.5 Lemma 1,
§5.1 Def 3, §5.2 Thm 1), `maurer2011` (cryptographic algebra, background), `maurerrenner2016`
(Def 2), `lochbihler2019cc` (§IV, Def 2, §V Defs 4–5, Thm 1, Cor 1, Fig. 6, §VI Def 6, Thm 2),
`bonchidilavore2025` (§3.1, Def 3.6, Thm 7.19); `maurer2007` (Thm 1, Lemma 5, Def 12) only for
§4.4; `portmann2017`, `gancher2023ipdl` only for §4.3.  All already archived.
