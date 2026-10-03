{-# OPTIONS --safe --without-K #-}

-- `𝒞^ω`, the indexed family layer: `Categories.LocallyGraded.Family` at the
-- `Poly⁺` admissibility over the resource grading, with an asymptotic
-- observation on top — eventual ε-closeness in `κ`, coarsened by
-- `Approx.Evaluation.qual₊` to vanishing advantage, into which `absorb` reads
-- a vanishing bound.
-- `κ` must be cofinal, or every eventual statement, hence the whole UC
-- preorder, is vacuously true.
-- A cryptographic bound must be NEGLIGIBLE, which `_≈ᵁ_` does not transport —
-- a bad event of probability `1/(n+1)` is `≈ᵁ`-equal to none — so a statement
-- of that kind keeps its error witness: `_≈ℰⁿ_`.

open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.LocallyGraded
open import Categories.LocallyGraded.Family
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Approx.Evaluation ℚ-ordered
open import CategoricalCrypto.Approx.Space ℚ-ordered
open import CategoricalCrypto.UC.Approximate
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UCSetup

import CategoricalCrypto.Standard2 as Std2

module CategoricalCrypto.UC.Family
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e)
  (qro : QEvaluation (MonoidalCategory.U M) os ℓa)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  (Ix : Set) (κ : Ix → ℕ) where

open MonoidalCategory M
open QEvaluation qro
open GradedSubCat Rg

open Families Rg Ix κ Poly⁺ poly⁺-1 (λ {s} {t} → poly⁺-· {s} {t}) public

------------------------------------------------------------------------
-- The observation, asymptotically

-- Eventually ε-close in the security parameter.
Approximation^ω : Approximation (Ix → Carrier) ℚ-ordered ℓa
Approximation^ω = Eventually (ApproxSpace.approx X) Ix κ

infix 4 _≈^ω[_]_

_≈^ω[_]_ : (Ix → Carrier) → ℚ → (Ix → Carrier) → Set ℓa
_≈^ω[_]_ = Approximation._≈[_]_ Approximation^ω

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

open R^ω public using (Closure; observe; Test; _≋_) renaming (ℰᴼ to ℰ^ω)

-- The INHERITED order: `absorb` below concludes a `_≈ᵁ_` witness, hence one
-- for `Canonical^ω._≤UC_` through `Canonical^ω.≈ᵁ⇒≤UC`.
module Canonical^ω = Std2.StdUC Famᴹ ℰ^ω

open Canonical^ω public using (_≈ᵁ_; ≈ᵁ-refl; ≈ᵁ-sym; ≈ᵁ-trans; ≈ᵁ-setoid; ≈C⇒≈ᵁ; sub-cong)

-- Spelled through `Canonical^ω`, as a consumer's `Std2.StdUC` application is: the
-- direct `Std2.StdUC.StdSetup Famᴹ ℰ^ω` makes the `refl` of
-- `UC.Family.Negligible.shared-computational` unfold the curried tensor
-- past a 16 GiB heap (measured), where this spelling checks in seconds.
ucSetup^ω : UCSetup o (ℓ ⊔ qs) e o (ℓ ⊔ qs) e (ℓ ⊔ qs) (ℓ ⊔ qs ⊔ ℓa)
ucSetup^ω = Canonical^ω.StdSetup

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
  → observe (Et Canonical^ω.∘ Canonical^ω.id Canonical^ω.⊗₁ f) m i
      ≈[ ε (κ i) (value (pc (κ i) · schedOf m (κ i))) ]
    observe (Et Canonical^ω.∘ Canonical^ω.id Canonical^ω.⊗₁ g) m i

-- `_≈ᵁ_` plugs a process into a test behind the prefix `α⇐ ∘ id ⊗₁ w`, and
-- `_≈ℰ[_]_` into the same test at `Et ∘ α⇐`: one reassociation apart, at any
-- readout on `Fam`.
module Reassoc {cs ℓs : Level} (R : Evaluation Fam cs ℓs) {A B X Y : Obj^ω}
  (Et : ((Y ⊛ω X) ⊛ω B) ⇒^ω Evaluation.Ω R) (m : Evaluation.J R ⇒^ω (Y ⊛ω A)) where
  private module R = Evaluation R

  plugα plugᵁ : A ⇒^ω (X ⊛ω B) → R.Closure R.Ω
  plugα w = ((Et Canonical^ω.∘ Canonical^ω.α⇐ {Y} {X} {B}) Canonical^ω.∘ Canonical^ω.id Canonical^ω.⊗₁ w) Canonical^ω.∘ m
  plugᵁ w = (Et Canonical^ω.∘ Canonical^ω.α⇐ {Y} {X} {B} Canonical^ω.∘ Canonical^ω.id Canonical^ω.⊗₁ w) Canonical^ω.∘ m

  reassoc : {f g : A ⇒^ω (X ⊛ω B)} → R.read (plugα f) R.S.≈ R.read (plugα g)
          → R.read (plugᵁ f) R.S.≈ R.read (plugᵁ g)
  reassoc {f} {g} = R.read-cast {plugα f} {plugᵁ f} {plugα g} {plugᵁ g}
                                (λ _ → ∘-resp-≈ˡ assoc) (λ _ → ∘-resp-≈ˡ assoc)

-- A vanishing bound collapses the quantitative statement to environment
-- agreement.  The context supplies the polynomial — its test certified at its
-- own rate — and `poly⁺-·` closes it.
absorb : {A B X : Obj^ω} {f g : A ⇒^ω (X ⊛ω B)} {ε : ℕ → ℕ → ℚ}
       → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ᵁ g
absorb {A} {B} {X} {f} {g} {ε} bnd van Y = Canonical^ω.KE.mk∼ λ {Et} m →
  let Et′ = Et Canonical^ω.∘ Canonical^ω.α⇐ {Y} {X}
  in Reassoc.reassoc Evaluation^ω {A} {B} {X} {Y} Et m {f} {g} λ δ δ>0 →
       let N , hN = van (λ n → value (schedOf Et′ n · schedOf m n))
                        (poly⁺-· {schedOf Et′} {schedOf m} (schedOf-adm Et′) (schedOf-adm m))
                        δ δ>0
       in N , λ i le → ≈[]-mono (hN (κ i) le)
                         (bnd Y Et′ m {schedOf Et′} (schedOf-adm Et′)
                              (λ i → hom Et′ i , Equiv.refl) i)

------------------------------------------------------------------------
-- The negligible layer

-- `absorb` spends no more than convergence; a cryptographic bound is held to
-- `Negligible` instead, read at exactly the allowances `_≈ℰ[_]_` evaluates `ε`
-- on: a polynomial rate of the test scaled by the closure's.
CarriedNegligible : (ℕ → ℕ → ℚ) → Set (o ⊔ ℓ ⊔ e ⊔ qs)
CarriedNegligible ε = {A B : Obj^ω} (Y : Obj^ω) (Et : Test (Y ⊛ω B))
                      (m : Closure (Y ⊛ω A)) {pc : ℕ → ℕ⁺} → Poly⁺ pc
                    → ((i : Ix) → Image forget (pc (κ i)) ⌊ hom Et i ⌋)
                    → Negligible (λ n → ε n (value (pc n · schedOf m n)))

-- …and it is no extra assumption: `poly⁺-·` is the polynomial witness.
carried-negligible : {ε : ℕ → ℕ → ℚ} → NegligibleBound ε → CarriedNegligible ε
carried-negligible neg Y Et m {pc} Ppc _ =
  neg (λ n → value (pc n · schedOf m n)) (poly⁺-· {pc} {schedOf m} Ppc (schedOf-adm m))

infix 4 _≈ℰⁿ_

-- Reading the grade back out means not throwing the witness away: `_≈ℰⁿ_` is
-- `absorb`'s premise at a negligible `ε`, KEPT, so a property whose slack must
-- stay negligible survives it where `_≈ᵁ_` loses it.
_≈ℰⁿ_ : {A B : Obj^ω} → A ⇒^ω B → A ⇒^ω B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≈ℰⁿ g = Σ[ ε ∈ (ℕ → ℕ → ℚ) ] CarriedNegligible ε × f ≈ℰ[ ε ] g
