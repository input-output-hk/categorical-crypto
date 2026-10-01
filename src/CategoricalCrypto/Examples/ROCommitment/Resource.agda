{-# OPTIONS --safe --without-K --guardedness #-}

-- The resource both worlds sit on, as a machine: a lazily sampled oracle
-- (`Examples.ROCommitment.Oracle.fetchT`'s kernel, in `Dₚ`) and the one-shot
-- cell that is `F_com`'s memory.  Off-protocol activations — a second `putᴿ`,
-- a `getᴿ` before one — are `botₚ`; neither machine above sends them.

open import Class.DecEq

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Resource (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k

open Core (𝒱ₚ 0ℓ)

-- Every machine that holds the table answers a query through this one term,
-- so their steps share its stuck subterm.
lazyₚ : {R : Set} → (Tbl → Dig → R) → Tbl → Pt → Dₚ R
lazyₚ κ t x = case lookupPt t x of λ where
  (just d) → returnₚ (κ t d)
  nothing  → uniformₚ k >>=ₚ λ h → returnₚ (κ ((x , h) ∷ t) h)

lazy-hit : {R : Set} (κ : Tbl → Dig → R) (t : Tbl) (x : Pt) (d : Dig) → lookupPt t x ≡ just d
         → lazyₚ κ t x ≈ₚ returnₚ (κ t d)
lazy-hit _ t x d eq rewrite eq = ≈ₚ-refl _

lazy-miss : {R : Set} (κ : Tbl → Dig → R) (t : Tbl) (x : Pt) → lookupPt t x ≡ nothing
          → lazyₚ κ t x ≈ₚ (uniformₚ k >>=ₚ λ h → returnₚ (κ ((x , h) ∷ t) h))
lazy-miss _ t x eq rewrite eq = ≈ₚ-refl _

-- The lookup is scrutinized by both sides at once, so it is `rewrite`n once.
lazy-bind : {R R′ : Set} (κ : Tbl → Dig → R) (κ′ : Tbl → Dig → R′) (K : R → Dₚ R′)
          → ((u : Tbl) (d : Dig) → K (κ u d) ≈ₚ returnₚ (κ′ u d))
          → (t : Tbl) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
          → (lazyₚ κ t x >>=ₚ K) ≈ₚ lazyₚ κ′ t x
lazy-bind _ _ K hK t x (just d) eq rewrite eq = >>=ₚ-identityˡ _ K ⟨≈⟩ hK t d
lazy-bind _ _ K hK t x nothing  eq rewrite eq =
  >>=ₚ-assoc (uniformₚ k) _ K ⟨≈⟩ bindᶠ λ h → >>=ₚ-identityˡ _ K ⟨≈⟩ hK ((x , h) ∷ t) h

lazy-map : {R R′ : Set} (f : R → R′) (κ : Tbl → Dig → R) (t : Tbl) (x : Pt)
           (w : Maybe Dig) → lookupPt t x ≡ w
         → mapₚ f (lazyₚ κ t x) ≈ₚ lazyₚ (λ u d → f (κ u d)) t x
lazy-map f κ = lazy-bind κ _ (returnₚ ∘′ f) λ _ _ → ≈ₚ-refl _

RState : Set
RState = Tbl × Maybe Bool

resStep : RState × (Pos unitᴵ ⊎ Neg Resᴵ) → Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))
resStep (_ , inj₁ ())
resStep ((t , m) , inj₂ (hashᴿ x)) = lazyₚ (λ u d → (u , m) , inj₂ (digᴿ d)) t x
resStep ((t , m) , inj₂ (putᴿ b))  = case m of λ where
  nothing → returnₚ ((t , just b) , inj₂ rcptᴿ)
  _       → botₚ
resStep ((t , m) , inj₂ getᴿ)      = case m of λ where
  (just b) → returnₚ ((t , just b) , inj₂ (outᴿ b))
  nothing  → botₚ
resStep ((t , m) , inj₂ nakᴿ)      = returnₚ ((t , m) , inj₂ rejᴿ)

stateᵒ : State
stateᵒ = initˢ RState ([] , nothing)

resource : Proc unitᴵ Resᴵ
resource = mk stateᵒ resStep

------------------------------------------------------------------------
-- The cell's steps, and the query bound

cell-put : (t : Tbl) (b : Bool)
         → step resource ((t , nothing) , inj₂ (putᴿ b)) ≈ₚ returnₚ ((t , just b) , inj₂ rcptᴿ)
cell-put t b = ≈ₚ-refl _

cell-get : (t : Tbl) (b : Bool)
         → step resource ((t , just b) , inj₂ getᴿ) ≈ₚ returnₚ ((t , just b) , inj₂ (outᴿ b))
cell-get t b = ≈ₚ-refl _

cell-nak : (t : Tbl) (m : Maybe Bool)
         → step resource ((t , m) , inj₂ nakᴿ) ≈ₚ returnₚ ((t , m) , inj₂ rejᴿ)
cell-nak t m = ≈ₚ-refl _

resourceQB : QB 0 resource
resourceQB = qb-closed resource
