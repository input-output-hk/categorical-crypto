{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Total-function extraction from `PartialMap`.  When the search succeeds,
-- `totalise` demands a `just`-value at every `Fin n` position, returning the
-- total function `f` together with the pointwise witness `∀ i → p i ≡ just (f i)`.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Match.Totals where

open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; map)
open import Data.List.Properties using (map-∘; map-cong)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

-- Σ-packaged total function with pointwise evidence.
Total : ∀ {n m} → (Fin n → Maybe (Fin m)) → Set
Total {n} {m} p = Σ (Fin n → Fin m) λ f → ∀ i → p i ≡ just (f i)

totalise : ∀ {n m} (p : Fin n → Maybe (Fin m)) → Maybe (Total p)
totalise {ℕ.zero}  p = just ((λ ()) , λ ())
totalise {ℕ.suc n} p with p zero in eq
... | nothing = nothing
... | just j₀ with totalise {n} (λ i → p (suc i))
...   | nothing = nothing
...   | just (f , ev) =
        just ( (λ { zero    → j₀
                  ; (suc i) → f i })
             , (λ { zero    → eq
                  ; (suc i) → ev i }) )

-- `map vlab₂ ys ≡ map vlab₁ xs` from `ys ≡ map φ xs` and the pointwise
-- label-agreement `vlab₂ (φ i) ≡ vlab₁ i`.  Shared by `Verify` (H/J labels)
-- and `Verify-Sub` (L/S labels); both invoke it per edge (verify body and the
-- atom-ein/atom-eout record fields).
deriveAtomEq
  : ∀ {V₁ V₂ X : Set}
      (vlab₁ : V₁ → X) (vlab₂ : V₂ → X)
      (φ : V₁ → V₂)
  → (∀ i → vlab₂ (φ i) ≡ vlab₁ i)
  → ∀ (xs : List V₁) (ys : List V₂)
  → ys ≡ map φ xs
  → map vlab₂ ys ≡ map vlab₁ xs
deriveAtomEq vlab₁ vlab₂ φ φ-lab xs ys p =
  trans (cong (map vlab₂) p)
  (trans (sym (map-∘ xs))
         (map-cong φ-lab xs))
