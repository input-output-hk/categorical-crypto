{-# OPTIONS --safe --without-K #-}

-- The random oracle over the naive locally graded layer (`Standard2`):
-- `MD ≤UC RO` derived from `dummy-complete`.  Protocols are bare machine
-- morphisms; the real one is the composite `MD-mach ∘ Comp-M`, because
-- `T₀ Jre GenIf` reduces to `Jre ⊗ GenIf` under the `curriedTensor` triple.
-- The one hypothesis the ≈ᵁ formulation adds is `stable : GradeStable`, which
-- turns the bare ≈ℰ equality `md-emulate` into the ≈ᵁ that `_≤UC_` consumes
-- (`bridge`).  Everything open is bundled in `ROData`; the module itself is
-- hypothesis-free.

module CategoricalCrypto.RandomOracle2 where

open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Level
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor.Presheaf

open import CategoricalCrypto.Standard2

module RO
  {o ℓ e cs ℓs ℓq ℓr : Level}
  (ℐ-machines : MonoidalCategory o ℓ e)
  (ℰ-standard : Presheaf (MonoidalCategory.U ℐ-machines) (Setoids cs ℓs))
  (ℚ          : Set ℓq)
  -- `Jre`/`Kid`: the real and ideal adversary interfaces, distinct as the
  -- `E`/`E''` of `Machine.Core._≤UC_`; `Mid`: the compression interface;
  -- `GenIf`: the RO output channel.
  (GenIf Mid Jre Kid : MonoidalCategory.Obj ℐ-machines)
  where

  open StdUC ℐ-machines ℰ-standard

  -- The protocol domain is closed on the input side.
  Ao Bo : Channel
  Ao = unit ⊗₀ unit
  Bo = Jre ⊗₀ GenIf

  record ROData : Set (suc ℓr ⊔ ℓq ⊔ o ⊔ ℓ ⊔ cs ⊔ ℓs) where
    infix 4 _≈ℰ[_]_
    field
      -- `f ≈ℰ[ ε ] g`: every distinguisher of ≤ n queries has advantage ≤ ε n
      -- (`Protocol.Observe._≈adv[_]_`, at an arbitrary domain).
      _≈ℰ[_]_ : ∀ {A B} → ∣machines∣ [ A , B ] → (ℕ → ℚ) → ∣machines∣ [ A , B ] → Set ℓr
      bound   : ℕ → ℚ
      Comp-M    : ∣machines∣ [ Ao , Mid ]
      MD-mach   : ∣machines∣ [ Mid , Bo ]
      General-M : ∣machines∣ [ Ao , Bo ]
      MD-secure : General-M ≈ℰ[ bound ] MD-mach ∘ Comp-M
      -- Bridge: a vanishing per-budget bound absorbs into `≈ℰ`, the kernel of
      -- `ℰ-standard`.
      VanishingBound : (ℕ → ℚ) → Set ℓr
      van            : VanishingBound bound
      absorb : ∀ {A B} {f g : ∣machines∣ [ A , B ]} {ε : ℕ → ℚ} → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ℰ g
      -- Bridge: the ideal protocol and its simulator.
      roIdeal     : ∣machines∣ [ Ao , T₀ Kid GenIf ]
      roSimulator : ∣machines∣ [ Kid , Jre ]
      ideal-bridge : sub roSimulator ∘ roIdeal ≈ℰ General-M
      -- The ℳ-module property of `ℰ-standard` (see the `Abstract2` header).
      stable : GradeStable

  module Payoff (ro : ROData) where
    open ROData ro

    mdProtocol : ∣machines∣ [ Ao , T₀ Jre GenIf ]
    mdProtocol = MD-mach ∘ Comp-M

    md-emulate : mdProtocol ≈ℰ sub roSimulator ∘ roIdeal
    md-emulate = begin
        mdProtocol                 ≈⟨ absorb MD-secure van ⟨
        General-M                  ≈⟨ ideal-bridge ⟨
        sub roSimulator ∘ roIdeal  ∎
      where open SetoidR (≈ℰ-setoid Ao Bo)

    MD≤UC-RO : mdProtocol ≤UC roIdeal
    MD≤UC-RO = dummy-complete (roSimulator , bridge stable md-emulate)
