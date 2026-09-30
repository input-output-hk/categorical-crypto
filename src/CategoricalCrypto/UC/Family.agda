{-# OPTIONS --safe --without-K #-}

-- `𝒞^ω`, the indexed family layer: objects are `Ix`-indexed object families and
-- homs are levelwise certified at a rate schedule polynomial in the security
-- parameter.  The category and its monoidal structure are
-- `Categories.LocallyGraded.Family` at the `Poly⁺` admissibility over the
-- resource grading; this module adds the observation on top of it.
--
-- The index is a PARAMETER `Ix` with a security-parameter projection
-- `κ : Ix → ℕ`, where the reference arc hardwired `Ix = ℕ`.  Only three things
-- ever needed `ℕ` there: the polynomial's argument, the asymptotics' order, and
-- the allowance arithmetic — and all three read the index through `κ` alone.  So
-- a second axis costs nothing: `Ix = ℕ × ℕ` with `κ = proj₁` gives a family
-- graded by the security parameter and anything else, and `(ℕ , id)` recovers
-- the reference.
--
-- `κ` must be COFINAL, and that is a soundness requirement rather than
-- bookkeeping: eventual closeness quantifies over the indices above a
-- threshold, so a bounded `κ` (constantly zero, say) makes every eventual
-- statement — hence the whole UC preorder — vacuously true.  `κ-cofinal` is
-- what `≈^ω-witness` spends.  It is an ASYMPTOTIC-INSTANCE requirement and not
-- a requirement of general UC: nothing in the core or the emulation metatheory
-- mentions an index at all.
--
-- This layer is where the notes' quantitative-to-qualitative arrow runs.
-- Everything categorical is levelwise, so the whole monoidal structure
-- transports; the readout, however, is CONSTRUCTED rather than transported —
-- the base's ε-closeness becomes *eventual* ε-closeness in `κ`, and
-- `Approx.Evaluation.qual₊` turns that into the qualitative agreement the core
-- consumes, which is then literally the vanishing-advantage relation (its ε/2
-- transitivity proved once, in `UC.Approximate`).  `absorb` is that
-- coarsening read at a vanishing error.
--
-- Vanishing is all `absorb` spends, but it is not what a cryptographic bound
-- must satisfy: that is NEGLIGIBILITY, eventually below every inverse
-- polynomial (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`).
-- Hence the negligible layer below, at the same allowances — which grade the
-- PREMISE and nothing else.  `_≈ᵁ_` is vanishing agreement whichever grade
-- goes in, so it does not transport a property whose slack must stay
-- negligible: a bad bit of probability `1/(n+1)` is `≈ᵁ`-equal to an
-- always-safe one.  A statement of that kind keeps its error witness instead:
-- `_≈ℰⁿ_`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.Family
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive using (ℕ⁺; _·_; poly⁺-1; poly⁺-·; Poly⁺; value)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤-trans)
open import Data.Product.Base using (Σ-syntax; _×_; _,_)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (ℚ-ordered)
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
  using (QEvaluation; qual₊)
open import CategoricalCrypto.Approx.Space ℚ-ordered using (ApproxSpace)
open import CategoricalCrypto.UC.Approximate
  using ( Approximation; Negligible; Negligible-+; Negligible-0
        ; Negligible⇒→0; NegligibleBound; NegligibleBound⇒VanishingBound; VanishingBound
        ; ℚ-errors; ℚ-refinement )
open import CategoricalCrypto.UC.Core using (Evaluation; Observable)
open import CategoricalCrypto.UCSetup using (UCSetup)

import CategoricalCrypto.Standard2 as Std2

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Family
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) (κ-cofinal : (N : ℕ) → Σ[ i ∈ Ix ] N ℕ.≤ κ i) where

open MonoidalCategory M
open QEvaluation qro
open GradedSubCat Rg

open Families Rg Ix κ Poly⁺ poly⁺-1 (λ {s} {t} → poly⁺-· {s} {t}) public

------------------------------------------------------------------------
-- The observation, asymptotically

infix 4 _≈^ω[_]_

-- Eventually ε-close in the security parameter.
_≈^ω[_]_ : (Ix → Carrier) → ℚ → (Ix → Carrier) → Set ℓa
μ ≈^ω[ ε ] ν = Σ[ N ∈ ℕ ] ((i : Ix) → N ℕ.≤ κ i → μ i ≈[ ε ] ν i)

-- Cofinality is what keeps the eventual relation from being satisfiable by
-- fiat: every threshold is met by some index, so an eventual closeness is
-- witnessed by an actual one.
≈^ω-witness : {μ ν : Ix → Carrier} {ε : ℚ} → μ ≈^ω[ ε ] ν → Σ[ i ∈ Ix ] μ i ≈[ ε ] ν i
≈^ω-witness (N , h) = let i , le = κ-cofinal N in i , h i le

Approximation^ω : Approximation (Ix → Carrier) ℚ-errors ℓa
Approximation^ω = record
  { _≈[_]_    = _≈^ω[_]_
  ; ≈[]-refl  = 0 , λ _ _ → ≈[]-refl
  ; ≈[]-sym   = λ (N , h) → N , λ i le → ≈[]-sym (h i le)
  ; ≈[]-trans = λ (N₁ , h₁) (N₂ , h₂) → N₁ ℕ.⊔ N₂ , λ i le →
      ≈[]-trans (h₁ i (≤-trans (m≤m⊔n N₁ N₂) le)) (h₂ i (≤-trans (m≤n⊔m N₁ N₂) le))
  ; ≈[]-mono  = λ le (N , h) → N , λ i le′ → ≈[]-mono le (h i le′)
  }

space^ω : ApproxSpace os ℓa
space^ω = record { Carrier = Ix → Carrier ; approx = Approximation^ω }

-- The family is again a quantitative model, so the construction iterates.
QEvaluation^ω : QEvaluation Fam os ℓa
QEvaluation^ω = record
  { J = Δ J ; Ω = Δ Ω ; X = space^ω
  ; eval₀ = record
      { to = λ u i → read ⌊ hom u i ⌋ ; cong = λ eq → 0 , λ i _ → read-resp₀ (eq i) }
  }

-- …and the qualitative readout the core consumes: `S`'s equality is vanishing
-- advantage.
Evaluation^ω : Evaluation Fam os ℓa
Evaluation^ω = qual₊ ℚ-refinement QEvaluation^ω

------------------------------------------------------------------------
-- Ingestion: a concrete bound, and its collapse

module R^ω = Evaluation Evaluation^ω

open R^ω public using (Closure; observe)

open Observable R^ω.observable public using (Test; _≋_) renaming (ℰᴼ to ℰ^ω)

private module Std^ω = Std2.StdUC Famᴹ ℰ^ω

open Std^ω public using (_≈ᵁ_; ≈ᵁ-refl; ≈ᵁ-sym; ≈ᵁ-trans; ≈ᵁ-setoid; ≈C⇒≈ᵁ; sub-cong)

-- P6 of `docs/stduc-supersession-plan.md`: the four fields of `UCSetup` at
-- `Fam`.  `ℳ` is the curried tensor of `Famᴹ` and `ℰ` is `Observable`'s
-- `Im θ` construction at `Evaluation^ω`, so the whole of
-- `Abstract2.AbstractUC` — `≤UC-refl`, `dummy-complete`, `≤UC-trans`,
-- `UC-compose`, `≈ᵁ⇒≈ℰ` — is available at the asymptotic family.
--
-- Spelled through `Std^ω`, as a consumer's `Std2.StdUC` application is: the
-- direct `Std2.StdUC.StdSetup Famᴹ ℰ^ω` makes the `refl` of
-- `UC.Family.Negligible.Setup.shared-computational` unfold the curried tensor
-- past a 16 GiB heap (measured), where this spelling checks in seconds.
ucSetup^ω : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetup^ω = Std^ω.StdSetup

infix 4 _≈ℰ[_]_

-- The shape a concrete security theorem has: at every ancilla context, the
-- level-`i` advantage is at most `ε` of the security parameter and of the
-- allowance the context affords — any polynomial rate certified for its test,
-- scaled by the rate its closure carries.  This is the only place a resource
-- bound earns its keep: an uncertified context would make `ε` a function of
-- nothing, and `absorb` below would have no polynomial to close over.  The
-- test's rate is quantified rather than read off its own schedule, so the bound
-- is read at any certificate the test has.
_≈ℰ[_]_ : {A B : Obj^ω} → A ⇒^ω B → (ℕ → ℕ → ℚ) → A ⇒^ω B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≈ℰ[_]_ {A} {B} f ε g =
  (Y : Obj^ω) (Et : Test (Y ⊛ω B)) (m : Closure (Y ⊛ω A)) {pc : ℕ → ℕ⁺} → Poly⁺ pc
  → ((i : Ix) → Image forget (pc (κ i)) ⌊ hom Et i ⌋) → (i : Ix)
  → observe (Et Std^ω.∘ Std^ω.id Std^ω.⊗₁ f) m i
      ≈[ ε (κ i) (value (pc (κ i) · schedOf m (κ i))) ]
    observe (Et Std^ω.∘ Std^ω.id Std^ω.⊗₁ g) m i

-- `_≈ᵁ_` plugs a process into a test behind the prefix `α⇐ ∘ id ⊗₁ w`, and
-- `_≈ℰ[_]_` into the same test at `Et ∘ α⇐`: one reassociation apart, at any
-- readout on `Fam`.
module Reassoc {cs ℓs : Level} (R : Evaluation Fam cs ℓs) {A B X Y : Obj^ω}
  (Et : ((Y ⊛ω X) ⊛ω B) ⇒^ω Evaluation.Ω R) (m : Evaluation.J R ⇒^ω (Y ⊛ω A)) where
  private module R = Evaluation R

  plugα plugᵁ : A ⇒^ω (X ⊛ω B) → R.Closure R.Ω
  plugα w = ((Et Std^ω.∘ Std^ω.α⇐ {Y} {X} {B}) Std^ω.∘ Std^ω.id Std^ω.⊗₁ w) Std^ω.∘ m
  plugᵁ w = (Et Std^ω.∘ Std^ω.α⇐ {Y} {X} {B} Std^ω.∘ Std^ω.id Std^ω.⊗₁ w) Std^ω.∘ m

  reassoc : {f g : A ⇒^ω (X ⊛ω B)} → R.read (plugα f) R.S.≈ R.read (plugα g)
          → R.read (plugᵁ f) R.S.≈ R.read (plugᵁ g)
  reassoc {f} {g} = R.read-cast {plugα f} {plugᵁ f} {plugα g} {plugᵁ g}
                                (λ _ → ∘-resp-≈ˡ assoc) (λ _ → ∘-resp-≈ˡ assoc)

-- A vanishing bound collapses the quantitative statement to environment
-- agreement.  The context supplies the polynomial — its test certified at its
-- own rate — and `poly⁺-·` closes it.
absorb : {A B X : Obj^ω} {f g : A ⇒^ω (X ⊛ω B)} {ε : ℕ → ℕ → ℚ}
       → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ᵁ g
absorb {A} {B} {X} {f} {g} {ε} bnd van Y = Std^ω.KE.mk∼ λ {Et} m →
  let Et′ = Et Std^ω.∘ Std^ω.α⇐ {Y} {X}
  in Reassoc.reassoc Evaluation^ω {A} {B} {X} {Y} Et m {f} {g} λ δ δ>0 →
       let N , hN = van (λ n → value (schedOf Et′ n · schedOf m n))
                        (poly⁺-· {schedOf Et′} {schedOf m} (schedOf-adm Et′) (schedOf-adm m))
                        δ δ>0
       in N , λ i le → ≈[]-mono (hN (κ i) le)
                         (bnd Y Et′ m {schedOf Et′} (schedOf-adm Et′)
                              (λ i → hom Et′ i , Equiv.refl) i)

------------------------------------------------------------------------
-- The negligible layer

-- `VanishingBound` is the WEAKER enrichment, and stays: `absorb` spends nothing
-- more than convergence.  A cryptographic bound is held to `Negligible` instead
-- (proposal §3, `docs/kb/frontier/15-probabilistic-uc-model.typ`), and the
-- allowances it is negligible at are the ones the model already supplies: a
-- polynomial rate of the test scaled by the closure's.

-- The §3 discipline read at exactly the allowances `_≈ℰ[_]_` evaluates `ε` on.
CarriedNegligible : (ℕ → ℕ → ℚ) → Set (o ⊔ ℓ ⊔ e ⊔ qs)
CarriedNegligible ε = {A B : Obj^ω} (Y : Obj^ω) (Et : Test (Y ⊛ω B))
                      (m : Closure (Y ⊛ω A)) {pc : ℕ → ℕ⁺} → Poly⁺ pc
                    → ((i : Ix) → Image forget (pc (κ i)) ⌊ hom Et i ⌋)
                    → Negligible (λ n → ε n (value (pc n · schedOf m n)))

-- …and it is no extra assumption: `poly⁺-·` is the polynomial witness.
carried-negligible : {ε : ℕ → ℕ → ℚ} → NegligibleBound ε → CarriedNegligible ε
carried-negligible neg Y Et m {pc} Ppc _ =
  neg (λ n → value (pc n · schedOf m n)) (poly⁺-· {pc} {schedOf m} Ppc (schedOf-adm m))

-- A sufficient condition into the SAME `≈ᵁ`: the grade is spent going in and
-- cannot be read back out (header).
absorb-negl : {A B X : Obj^ω} {f g : A ⇒^ω (X ⊛ω B)} {ε : ℕ → ℕ → ℚ}
            → f ≈ℰ[ ε ] g → NegligibleBound ε → f ≈ᵁ g
absorb-negl {A} {B} {X} {f} {g} {ε} bnd neg =
  absorb {A} {B} {X} {f} {g} {ε} bnd (NegligibleBound⇒VanishingBound {ε} neg)

infix 4 _≈ℰⁿ_

-- Reading the grade back out means not throwing the witness away: `_≈ℰⁿ_` is
-- `absorb-negl`'s premise with its `ε` KEPT, so a property whose slack must
-- stay negligible survives it where `_≈ᵁ_` loses it.
_≈ℰⁿ_ : {A B : Obj^ω} → A ⇒^ω B → A ⇒^ω B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≈ℰⁿ g = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] CarriedNegligible ε × f ≈ℰ[ ε ] g

≈ℰⁿ-refl : {A B : Obj^ω} {f : A ⇒^ω B} → f ≈ℰⁿ f
≈ℰⁿ-refl = (λ _ _ → 0ℚ) , (λ _ _ _ _ _ → Negligible-0) , λ _ _ _ _ _ _ → ≈[]-refl

≈ℰⁿ-sym : {A B : Obj^ω} {f g : A ⇒^ω B} → f ≈ℰⁿ g → g ≈ℰⁿ f
≈ℰⁿ-sym (ε , neg , bnd) = ε , neg , λ Y Et m {pc} Ppc c i → ≈[]-sym (bnd Y Et m {pc} Ppc c i)

≈ℰⁿ-trans : {A B : Obj^ω} {f g h : A ⇒^ω B} → f ≈ℰⁿ g → g ≈ℰⁿ h → f ≈ℰⁿ h
≈ℰⁿ-trans (ε₁ , neg₁ , bnd₁) (ε₂ , neg₂ , bnd₂) =
    (λ n q → ε₁ n q ℚ.+ ε₂ n q)
  , (λ Y Et m {pc} Ppc c → Negligible-+ (neg₁ Y Et m {pc} Ppc c) (neg₂ Y Et m {pc} Ppc c))
  , λ Y Et m {pc} Ppc c i → ≈[]-trans (bnd₁ Y Et m {pc} Ppc c i) (bnd₂ Y Et m {pc} Ppc c i)

-- It refines the vanishing agreement — `absorb` read at the test's own rate.
≈ℰⁿ⇒≈ᵁ : {A B X : Obj^ω} {f g : A ⇒^ω (X ⊛ω B)} → f ≈ℰⁿ g → f ≈ᵁ g
≈ℰⁿ⇒≈ᵁ {A} {B} {X} {f} {g} (ε , neg , bnd) Y = Std^ω.KE.mk∼ λ {Et} m →
  let Et′ = Et Std^ω.∘ Std^ω.α⇐ {Y} {X}
  in Reassoc.reassoc Evaluation^ω {A} {B} {X} {Y} Et m {f} {g} λ δ δ>0 →
       let Pc = schedOf-adm Et′ ; c = λ i → hom Et′ i , Equiv.refl
           N , hN = Negligible⇒→0 (neg Y Et′ m {schedOf Et′} Pc c) δ δ>0
       in N , λ i le → ≈[]-mono (hN (κ i) le) (bnd Y Et′ m {schedOf Et′} Pc c i)

-- What is NOT delivered here is an `Evaluation` whose comparison is `_≈ℰⁿ_`:
-- `qual₊` coarsens by quantifying an ambient ε AWAY, and retaining the
-- witness is the opposite move.  That would mean either a second `Evaluation`
-- on `Fam` carrying this relation, with every emulation notion re-derived
-- over it (`≤UC` included), or an `Evaluation` interface parameterized by its
-- grade — redesigns of the core's readout interface rather than of this
-- module, which is why the negligible tier consumers use lives at layer 1.
--
-- Of the two, the first proved NOT to be a core redesign: `UC.Core.Evaluation`
-- asks for an arbitrary setoid, so `UC.Family.Negligible` builds that
-- second `Evaluation` on `Fam` and inherits the emulation notions at it with
-- nothing in the qualitative core moving.  Neither is owed by the ε-RETAINING
-- composition law any more: `UC.Model.Family.Contextual.Compose` proves it
-- directly over the contextual relation, carrying the simulator witness and
-- charging each plugged
-- morphism's allowance substitution, and only forgets into `_≈ℰⁿ_`/`_≈ᵁ_` at
-- the end.
