{-# OPTIONS --safe --without-K #-}

-- The query-sensitive test model as a genuine filtered instance
-- (`docs/quantitative-uc-setup-plan.typ` §7.3).
--
-- Tests are compared through CERTIFIED closures, at a schedule read off the
-- closure's own rate.  Pulling a test back along a morphism of rate `r` moves
-- BOTH indices, and each move is one law of the resource grading: the closure
-- `h ∘ m` is the graded composite at `r′ · r`, so the schedule is reindexed by
-- `_· r`, and the test `E ∘ h` is the graded composite at `q · r`, so the
-- admitted allowance is reindexed by `_· r` too.  That is exactly a
-- `Approx.Filtered` map, error control and allowance map together.
--
-- The base is therefore the RATED morphisms, not `𝒞`: an arbitrary morphism
-- induces no controlled map on bounded tests, and a control has to be
-- determined by the morphism, so the rate is part of the hom and of its
-- equality.  Closure schedules and test allowances are both indexed by `ℕ⁺`,
-- so no schedule is read at a rate no certificate has.  Only the non-tensor part
-- of the graded subcategory is spent.

open import Categories.Category using (Category)
open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Presheaf using (Presheaf)
open import Categories.LocallyGraded
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; sym; trans)

open import CategoricalCrypto.Approx.Error
  using (Approximation; OrderedErrorAlgebra; ℚ-ordered; ≈[]-resp₀)
open import CategoricalCrypto.Approx.Schedule using (pointwise; module Reindexing)

import CategoricalCrypto.Approx.Controlled as Controlledᴹ
import CategoricalCrypto.Approx.Filtered as Filteredᴹ
import CategoricalCrypto.Approx.Space as Spaceᴹ
import Data.Nat.Properties as ℕₚ
import Data.Rational.Properties as ℚₚ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Quantitative.Query where

-- Schedules in the closure rate.
Sched = pointwise ℕ⁺ ℚ-ordered

-- One application, shared with the consumers (`UC.Quantitative.Contextual`):
-- a second one would make every crossing pay for re-elaborating it.
module Fl = Filteredᴹ Sched ≤⁺-poset

private
  module S = Controlledᴹ Sched
  open OrderedErrorAlgebra Sched using (_⊑_)

open Reindexing {I = ℕ⁺} ℚ-ordered using (reindex; reindex-cong)

------------------------------------------------------------------------
-- The two absorptions of a rated morphism, as schedule equalities

-- An error `ε` read at a test rate `c` scaled by a closure rate is a
-- schedule in the closure rate.  Absorbing a morphism of rate `r` substitutes
-- that allowance, and both substitutions are exact, so the two schedules agree
-- in both directions: into the TEST it rescales the test's rate…
absorb-test : (c r : ℕ⁺) (ε : ℕ → ℚ)
            → ((λ r′ → ε (value (c · r · r′))) ⊑ (λ r′ → ε (value (c · r′ · r))))
            × ((λ r′ → ε (value (c · r′ · r))) ⊑ (λ r′ → ε (value (c · r · r′))))
absorb-test c r ε = (λ r′ → ℚₚ.≤-reflexive (cong ε (scale-comm (value c) r r′)))
                  , λ r′ → ℚₚ.≤-reflexive (cong ε (scale-comm (value c) r′ r))

-- …and into the CLOSURE it multiplies the closure's rate.
absorb-closure : (c r : ℕ⁺) (ε : ℕ → ℚ)
               → ((λ r′ → ε (value (c · (r′ · r)))) ⊑ (λ r′ → ε (value (c · r′ · r))))
               × ((λ r′ → ε (value (c · r′ · r))) ⊑ (λ r′ → ε (value (c · (r′ · r)))))
absorb-closure c r ε = (λ r′ → ℚₚ.≤-reflexive (cong ε (scale-· (value c) r′ r)))
                     , λ r′ → ℚₚ.≤-reflexive (cong ε (sym (scale-· (value c) r′ r)))

module Tests
  {o ℓ e os ℓa qs : Level} (M : MonoidalCategory o ℓ e)
  (Rg : GradedSubCat Rates.monoidalCategory M qs)
  {Obs : Set os} (Ap : Approximation Obs ℚ-ordered ℓa)
  (𝟙 Ω : MonoidalCategory.Obj M)
  (⟦_⟧ : MonoidalCategory._⇒_ M 𝟙 Ω → Obs)
  (obs-resp : {u v : MonoidalCategory._⇒_ M 𝟙 Ω}
            → MonoidalCategory._≈_ M u v → Approximation._≈[_]_ Ap ⟦ u ⟧ 0ℚ ⟦ v ⟧)
  where

  open MonoidalCategory M
  open GradedSubCat Rg
  module L = LocallyGradedCategory L

  private
    module Sp = Spaceᴹ Sched
    module A  = Approximation Ap

  Test Closure : Obj → Set ℓ
  Test C    = C ⇒ Ω
  Closure C = 𝟙 ⇒ C

  -- A certificate read as the graded hom it certifies, whose interpretation is
  -- the certified morphism ON THE NOSE: `pred-resp` moves the certificate, so
  -- no consumer transports along the certificate's equation.
  certifiedᴴ : {r : ℕ⁺} {C D : Obj} {h : C ⇒ D} → Image forget r h → L.Hom r C D
  certifiedᴴ {h = h} (ĥ , ĥ≈h) = record { arr = h ; Parr = pred-resp ĥ≈h (Predicate.Parr ĥ) }

  ------------------------------------------------------------------------
  -- Tests at a schedule

  infix 4 _≈ᵠ[_]_

  _≈ᵠ[_]_ : {C : Obj} → Test C → (ℕ⁺ → ℚ) → Test C → Set (ℓ ⊔ e ⊔ ℓa ⊔ qs)
  _≈ᵠ[_]_ {C} E τ F =
    (m : Closure C) (r′ : ℕ⁺) → Image forget r′ m → ⟦ E ∘ m ⟧ A.≈[ τ r′ ] ⟦ F ∘ m ⟧

  approxᵠ : (C : Obj)
          → Approximation (Test C) Sched (ℓ ⊔ e ⊔ ℓa ⊔ qs)
  approxᵠ C = record
    { _≈[_]_    = _≈ᵠ[_]_
    ; ≈[]-refl  = λ _ _ _ → A.≈[]-refl
    ; ≈[]-sym   = λ h m r′ cm → A.≈[]-sym (h m r′ cm)
    ; ≈[]-trans = λ h k m r′ cm → A.≈[]-trans (h m r′ cm) (k m r′ cm)
    ; ≈[]-mono  = λ le h m r′ cm → A.≈[]-mono (le r′) (h m r′ cm)
    }

  spaceᵠ : Obj → Sp.ApproxSpace ℓ (ℓ ⊔ e ⊔ ℓa ⊔ qs)
  spaceᵠ C = record { Carrier = Test C ; approx = approxᵠ C }

  -- …and the filtration: which allowance admits which test.
  filteredᵠ : Obj → Fl.FilteredSpace ℓ (ℓ ⊔ e ⊔ ℓa ⊔ qs) (ℓ ⊔ e ⊔ qs)
  filteredᵠ C = record
    { space = spaceᵠ C ; Admit = λ q E → Image forget q E
    ; admit-mono = λ le (Ê , Ê≈E) → L.sub[ le ] Ê , Ê≈E }

  ------------------------------------------------------------------------
  -- The rated base

  -- The Σ-total of `L`.
  Budgeted : Obj → Obj → Set (ℓ ⊔ qs)
  Budgeted C D = Σ[ r ∈ ℕ⁺ ] L.Hom r C D

  infix 4 _≈ᵇ_

  _≈ᵇ_ : {C D : Obj} → Budgeted C D → Budgeted C D → Set e
  f ≈ᵇ g = (⌊ proj₂ f ⌋ ≈ ⌊ proj₂ g ⌋) × (proj₁ f ≡ proj₁ g)

  -- The rate is in the hom EQUALITY too: two morphisms certified at different
  -- rates reindex a schedule differently.
  𝒞ᵇ : Category o (ℓ ⊔ qs) e
  𝒞ᵇ = record
    { Obj = Obj
    ; _⇒_ = Budgeted
    ; _≈_ = _≈ᵇ_
    ; id  = 1⁺ , L.id
    ; _∘_ = λ (s , g) (r , f) → r · s , g L.∙ f
    ; assoc     = λ {_} {_} {_} {_} {(r , _)} {(s , _)} {(t , _)} →
        assoc , value-injective (sym (ℕₚ.*-assoc (value r) (value s) (value t)))
    ; sym-assoc = λ {_} {_} {_} {_} {(r , _)} {(s , _)} {(t , _)} →
        sym-assoc , value-injective (ℕₚ.*-assoc (value r) (value s) (value t))
    ; identityˡ = λ {_} {_} {(r , _)} → identityˡ , value-injective (ℕₚ.*-identityʳ (value r))
    ; identityʳ = λ {_} {_} {(r , _)} → identityʳ , value-injective (ℕₚ.*-identityˡ (value r))
    ; identity² = identity² , value-injective refl
    ; equiv = record
        { refl  = Equiv.refl , refl
        ; sym   = λ (he , be) → Equiv.sym he , sym be
        ; trans = λ (he₁ , be₁) (he₂ , be₂) → Equiv.trans he₁ he₂ , trans be₁ be₂ }
    ; ∘-resp-≈ = λ (he₁ , be₁) (he₂ , be₂) → ∘-resp-≈ he₁ he₂ , cong₂ _·_ be₂ be₁
    }

  ------------------------------------------------------------------------
  -- Pullback moves both indices, each by one law of the grading

  pullᵠ : {C D : Obj} → Budgeted C D → Fl.Filtered (filteredᵠ D) (filteredᵠ C)
  pullᵠ (r , ĥ) = record
    { underlying = record
        { map     = λ E → E ∘ ⌊ ĥ ⌋
        ; control = reindex (_· r)
        ; preserves = λ hyp n r″ (n̂ , n̂≈n) →
            ≈[]-resp₀ ℚ-ordered Ap (obs-resp assoc) (obs-resp sym-assoc)
              (hyp (⌊ ĥ ⌋ ∘ n) (r″ · r) (ĥ L.∙ n̂ , ∘-resp-≈ʳ n̂≈n))
        }
    ; allowance = record { at = _· r ; monotone = ℕₚ.*-monoˡ-≤ (value r) }
    ; admits = λ {q} (Ê , Ê≈E) →
        L.sub[ ℕₚ.≤-reflexive (ℕₚ.*-comm (value r) (value q)) ] (Ê L.∙ ĥ) , ∘-resp-≈ˡ Ê≈E
    }

  Qᵠ : Presheaf 𝒞ᵇ (Fl.Filt ℓ (ℓ ⊔ e ⊔ ℓa ⊔ qs) (ℓ ⊔ e ⊔ qs))
  Qᵠ = record
    { F₀ = filteredᵠ
    ; F₁ = pullᵠ
    ; identity = ( reindex-cong (λ r′ → value-injective (ℕₚ.*-identityʳ (value r′)))
                 , λ _ _ _ _ → obs-resp (∘-resp-≈ˡ identityʳ) )
               , λ q → value-injective (scale-unit (value q))
    ; homomorphism = λ {_} {_} {_} {(r , _)} {(s , _)} →
        ( reindex-cong (λ r′ → value-injective (sym (ℕₚ.*-assoc (value r′) (value s) (value r))))
        , λ _ _ _ _ → obs-resp (∘-resp-≈ˡ sym-assoc) )
        , λ q → value-injective (trans (scale-· (value q) s r) (scale-comm (value q) s r))
    ; F-resp-≈ = λ (he , be) → ( reindex-cong (λ r′ → cong (r′ ·_) be)
                               , λ _ _ _ _ → obs-resp (∘-resp-≈ˡ (∘-resp-≈ʳ he)) )
                               , λ q → cong (q ·_) be
    }
