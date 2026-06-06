{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Total-function extraction from `PartialMap`.  When the search succeeds,
-- `totalise` demands a `just`-value at every `Fin n` position, returning the
-- total function `f` together with the pointwise witness `∀ i → p i ≡ just (f i)`.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Totals where

open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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
