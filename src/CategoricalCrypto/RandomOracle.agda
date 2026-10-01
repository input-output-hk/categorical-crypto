{-# OPTIONS --safe --without-K #-}

-- The random oracle over the standard model: `MD ≤UC RO` derived from the
-- dummy-adversary theorem `dummy-complete`.  The Merkle–Damgård statement (a
-- stand-in for `Examples.MerkleDamgard.indistinguishable`), the ε-absorption
-- bridge and the protocol bridges are the fields of `ROData`; the module itself
-- is hypothesis-free.

module CategoricalCrypto.RandomOracle where

open import Level
open import Data.Nat.Base using (ℕ)
open import Data.Product
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor.Presheaf

open import Categories.CoherenceIsos
open import CategoricalCrypto.Standard

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
  open Coherence ℐ-machines

  -- U lands OAP-homs at `T₀ J · = J ⊗ ·`, so the machines live over these
  -- channels; the protocol domain is the OAP unit 𝟙ⱽ (a resource, closed on the
  -- input side).
  Ao Bo : Channel
  Ao = unit ⊗₀ unit
  Bo = Jre ⊗₀ GenIf

  𝟙ⱽ : Objᴼᴾ
  𝟙ⱽ = ⟨ unit , ℂ.unit ⟩ᴼᴾ

  record ROData : Set (suc ℓr ⊔ ℓq ⊔ o ⊔ ℓ ⊔ cs ⊔ ℓs) where
    infix 4 _≈ℰ[_]_
    field
      -- `f ≈ℰ[ ε ] g`: every distinguisher of ≤ n queries has advantage ≤ ε n
      -- (`Protocol.Observe._≈adv[_]_`, at the U-image domain).
      _≈ℰ[_]_ : ∀ {A B} → ∣machines∣ [ A , B ] → (ℕ → ℚ) → ∣machines∣ [ A , B ] → Set ℓr
      bound   : ℕ → ℚ
      Comp-M    : ∣machines∣ [ Ao , Mid ]
      MD-mach   : ∣machines∣ [ Mid , Bo ]
      General-M : ∣machines∣ [ Ao , Bo ]
      MD-secure : General-M ≈ℰ[ bound ] (MD-mach ∘ Comp-M)
      -- Bridge: a vanishing per-budget bound absorbs into `≈ℰ`, the kernel of
      -- `ℰ-standard`.
      VanishingBound : (ℕ → ℚ) → Set ℓr
      van            : VanishingBound bound
      absorb : ∀ {A B} {f g : ∣machines∣ [ A , B ]} {ε : ℕ → ℚ} → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ℰ g
      -- Bridge: the OP protocols and the U-images of real / simulated ideal.
      mdProtocol  : 𝟙ⱽ ⇒ᴼᴾ ⟨ GenIf , Var Jre ⟩ᴼᴾ
      roIdeal     : 𝟙ⱽ ⇒ᴼᴾ ⟨ GenIf , Var Kid ⟩ᴼᴾ
      roSimulator : ∣machines∣ [ Kid , Jre ]
      U-real  : U (ι mdProtocol) ≈ℰ (MD-mach ∘ Comp-M)
      U-ideal : U (pureAtk roSimulator OAP.∘ ι roIdeal) ≈ℰ General-M

  module Payoff (ro : ROData) where
    open ROData ro

    MD⊚Comp : ∣machines∣ [ Ao , Bo ]
    MD⊚Comp = MD-mach ∘ Comp-M

    -- `dummy-complete`'s input-side mediator is `ℐ.id`: the MD statement is
    -- closed on the resource side.
    md-emulate : ι mdProtocol ≈ℰ' (pureAtk roSimulator OAP.∘ ι roIdeal OAP.∘ pureAtk ℐ.id)
    md-emulate = U-≈ℰ⇒≈ℰ' (begin
        U (ι mdProtocol)                                            ≈⟨ U-real ⟩
        MD⊚Comp                                                     ≈⟨ absorb MD-secure van ⟨
        General-M                                                   ≈⟨ U-ideal ⟨
        U (pureAtk roSimulator OAP.∘ ι roIdeal)
          ≈⟨ ≈ℰ'⇒U-≈ℰ (≈'-congˡ (pureAtk roSimulator) (≈'-sym (atk-idʳ (ι roIdeal)))) ⟩
        U (pureAtk roSimulator OAP.∘ ι roIdeal OAP.∘ pureAtk ℐ.id)  ∎)
      where open SetoidR (≈ℰ-setoid Ao Bo)

    MD≤UC-RO : mdProtocol ≤UC roIdeal
    MD≤UC-RO = dummy-complete {f = mdProtocol} {g = roIdeal} (roSimulator , ℐ.id , md-emulate)
