{-# OPTIONS --safe --without-K #-}

-- §3 of the plan (M5/M6): the random oracle, end to end.  Over the standard
-- model (§2) plus the RO/Merkle–Damgård artifacts (hypothesised at their exact
-- types in src/CategoricalCrypto/Examples/MerkleDamgard.agda on branch
-- `random-oracle`, modulo the ℚ/Dist stand-ins), the ε-absorption bridge, and
-- the OP-level protocol bridges, `MD ≤UC RO` is DERIVED from the §1
-- dummy-adversary theorem.  Co-consumption of the abstract theorem and the
-- existing MD theorem in one term is the plan's thesis.  Everything still open
-- is bundled in `ROData` — this module itself is hypothesis-free.

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
  -- The RO interface has DISTINCT adversary interfaces for real (Jre) and ideal
  -- (Kid) — Machine.Core's E vs E''.  GenIf is the generator/RO output channel.
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

  -- ── The RO/MD interface, hypothesised at its MerkleDamgard.agda types ───────
  --   E Dgr asks≤ runWith badProb Pr₁ adv
  --   Preserved badProb-super SuperCert badProb-bounded
  --   Coupling{fR,fI,realK,idealK,FLGP}  _≈ℰ[_]_  bound
  record ROData : Set (suc ℓr ⊔ ℓq ⊔ o ⊔ ℓ ⊔ cs ⊔ ℓs) where
    infix 4 _≈ℰ[_]_
    field
      -- `_≈ℰ[ ε ]_`: any distinguisher of ≤ n queries has advantage ≤ ε n
      -- (MD `_≈ℰ[_]_`, generalised from the closed domain to the U-image domain).
      _≈ℰ[_]_ : ∀ {A B} → ∣machines∣ [ A , B ] → (ℕ → ℚ) → ∣machines∣ [ A , B ] → Set ℓr
      bound   : ℕ → ℚ                              -- bound
      Comp-M    : ∣machines∣ [ Ao , Mid ]          -- Comp.M
      MD-mach   : ∣machines∣ [ Mid , Bo ]          -- MD
      General-M : ∣machines∣ [ Ao , Bo ]           -- General.M (the ideal RO)
      MD-secure : General-M ≈ℰ[ bound ] (MD-mach ∘ Comp-M)  -- indistinguishable
      -- BRIDGE (M5): a concrete per-budget bound with a vanishing profile
      -- establishes the ε-absorption setoid equality (the kernel of ℰ-standard).
      VanishingBound : (ℕ → ℚ) → Set ℓr
      van            : VanishingBound bound
      absorb : ∀ {A B} {f g : ∣machines∣ [ A , B ]} {ε : ℕ → ℚ} → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ℰ g
      -- BRIDGE (M6): the OP protocols and the U-images of real / simulated ideal.
      mdProtocol  : 𝟙ⱽ ⇒ᴼᴾ ⟨ GenIf , Var Jre ⟩ᴼᴾ
      roIdeal     : 𝟙ⱽ ⇒ᴼᴾ ⟨ GenIf , Var Kid ⟩ᴼᴾ
      roSimulator : ∣machines∣ [ Kid , Jre ]
      U-real  : U (ι mdProtocol) ≈ℰ (MD-mach ∘ Comp-M)
      U-ideal : U (pureAtk roSimulator OAP.∘ ι roIdeal) ≈ℰ General-M

  -- ── THE PAYOFF, DERIVED ─────────────────────────────────────────────────────
  module Payoff (ro : ROData) where
    open ROData ro

    MD⊚Comp : ∣machines∣ [ Ao , Bo ]
    MD⊚Comp = MD-mach ∘ Comp-M

    -- Consumes ONLY the §1 abstract theorem (dummy-complete), the bridge
    -- (absorb + U-real/U-ideal + van), and the existing MD artifact (MD-secure).
    -- `dummy-complete`'s input-side mediator is instantiated at `ℐ.id`: the
    -- concrete MD statement is closed on the resource side.
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
