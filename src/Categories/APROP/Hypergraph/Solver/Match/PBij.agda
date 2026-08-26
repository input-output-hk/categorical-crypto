{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Partial vertex/edge maps (TensorRocq §4.2).
--
-- A partial map is a pure function `Fin n → Maybe (Fin m)`.  `PBij n m`
-- carries forward *and* backward partial maps; `extend-bij` updates both
-- atomically and refuses conflicting extensions.  `totalise` — the partial
-- map's totalisation — lives here too; the bijection laws (`φ-left`,
-- `φ-rght`) are NOT its business: `Verify` decides them separately.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.Match.PBij where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Properties.Ext using (map-∘-cong)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
open import Relation.Nullary using (yes; no)

--------------------------------------------------------------------------------
-- Partial map.

PartialMap : ℕ → ℕ → Set
PartialMap n m = Fin n → Maybe (Fin m)

empty : ∀ {n m} → PartialMap n m
empty _ = nothing

-- Update a binding at `i` to `j` if consistent; `nothing` when `i` is
-- already bound to a different value.
extend : ∀ {n m} → PartialMap n m → Fin n → Fin m → Maybe (PartialMap n m)
extend {n} {m} p i j with p i
... | nothing = just (λ k → case-≟ k i j (p k))
  where
    case-≟ : Fin n → Fin n → Fin m → Maybe (Fin m) → Maybe (Fin m)
    case-≟ k i' j' pk with k ≟F i'
    ... | yes _ = just j'
    ... | no _  = pk
... | just j' with j ≟F j'
...   | yes _ = just p
...   | no _  = nothing

--------------------------------------------------------------------------------
-- Symmetric partial bijection (forward/backward kept in sync by `extend-bij`).

record PBij (n m : ℕ) : Set where
  field
    forward  : PartialMap n m
    backward : PartialMap m n

open PBij public

emptyBij : ∀ {n m} → PBij n m
emptyBij = record { forward = empty ; backward = empty }

-- Extend with `i ↔ j`, updating both directions atomically; fails on conflict.
extend-bij : ∀ {n m} → PBij n m → Fin n → Fin m → Maybe (PBij n m)
extend-bij b i j =
  extend (forward  b) i j >>= λ f' →
  extend (backward b) j i >>= λ g' →
  just (record { forward = f' ; backward = g' })

--------------------------------------------------------------------------------
-- Pairing two lists into a partial bijection (used at interface-seeding
-- time to pair H.dom with J.dom and H.cod with J.cod).

open import Data.List.Base using (List; []; _∷_; map)

pairUp : ∀ {n m} → PBij n m → List (Fin n) → List (Fin m) → Maybe (PBij n m)
pairUp b [] []             = just b
pairUp b (_ ∷ _) []        = nothing   -- length mismatch
pairUp b [] (_ ∷ _)        = nothing   -- length mismatch
pairUp b (i ∷ is) (j ∷ js) = extend-bij b i j >>= λ b' → pairUp b' is js

--------------------------------------------------------------------------------
-- Total-function extraction.  When the search succeeds, `totalise` demands a
-- `just`-value at every `Fin n` position and returns the total function it
-- reads off.  It carries NO pointwise witness `∀ i → p i ≡ just (f i)`: the
-- two consumers (`Verify.verify`, `SubMatch.verifySub`) re-derive every
-- `_≅ᴴ_`/`_↪ᴴ_` law they need by their own decidable checks and discarded
-- that witness at all six call sites.

totalise : ∀ {n m} (p : PartialMap n m) → Maybe (Fin n → Fin m)
totalise {ℕ.zero}  p = just λ ()
totalise {ℕ.suc n} p with p zero
... | nothing = nothing
... | just j₀ =
      Maybe.map (λ f → λ { zero → j₀ ; (suc i) → f i })
                (totalise {n} (λ i → p (suc i)))

-- `map vlab₂ ys ≡ map vlab₁ xs` from `ys ≡ map φ xs` and the pointwise
-- label-agreement `vlab₂ (φ i) ≡ vlab₁ i`.  Shared by `Verify` (H/J labels)
-- and `Verify-Sub` (L/S labels); both invoke it per edge (verify body and the
-- atom-ein/atom-eout record fields).
deriveAtomEq
  : ∀ {V₁ V₂ X : Set} {vlab₁ : V₁ → X} {vlab₂ : V₂ → X} {φ : V₁ → V₂}
  → (∀ i → vlab₂ (φ i) ≡ vlab₁ i)
  → ∀ (xs : List V₁) {ys : List V₂} → ys ≡ map φ xs
  → map vlab₂ ys ≡ map vlab₁ xs
deriveAtomEq {vlab₂ = vlab₂} φ-lab xs p =
  trans (cong (map vlab₂) p) (map-∘-cong φ-lab xs)
