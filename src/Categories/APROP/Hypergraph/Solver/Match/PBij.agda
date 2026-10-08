{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Partial vertex/edge maps (TensorRocq §4.2).
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Match.PBij where

open import Data.Fin
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

private
  variable
    n m : ℕ

PartialMap : ℕ → ℕ → Set
PartialMap n m = Fin n → Maybe (Fin m)

empty : PartialMap n m
empty _ = nothing

extend : PartialMap n m → Fin n → Fin m → Maybe (PartialMap n m)
extend p i j with p i
... | nothing = just (λ k → case k ≟F i of λ { (yes _) → just j ; (no _) → p k })
... | just j' with j ≟F j'
...   | yes _ = just p
...   | no _  = nothing

record PBij (n m : ℕ) : Set where
  field forward : PartialMap n m
        backward : PartialMap m n

open PBij public

emptyBij : PBij n m
emptyBij = record { forward = empty ; backward = empty }

extend-bij : PBij n m → Fin n → Fin m → Maybe (PBij n m)
extend-bij b i j =
  extend (forward  b) i j >>= λ f' →
  extend (backward b) j i >>= λ g' →
  just (record { forward = f' ; backward = g' })

pairUp : PBij n m → List (Fin n) → List (Fin m) → Maybe (PBij n m)
pairUp b [] []             = just b
pairUp b (_ ∷ _) []        = nothing
pairUp b [] (_ ∷ _)        = nothing
pairUp b (i ∷ is) (j ∷ js) = extend-bij b i j >>= λ b' → pairUp b' is js

totalise : (p : PartialMap n m) → Maybe (Fin n → Fin m)
totalise {ℕ.zero}  p = just λ ()
totalise {ℕ.suc n} p with p zero
... | nothing = nothing
... | just j₀ =
      Maybe.map (λ f → λ { zero → j₀ ; (suc i) → f i })
                (totalise {n} (p ∘ suc))

