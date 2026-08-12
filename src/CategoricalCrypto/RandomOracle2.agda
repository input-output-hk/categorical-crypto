{-# OPTIONS --safe --without-K #-}

-- §3 of the plan (M5/M6) over the naive locally graded layer: the random
-- oracle, end to end, derived from the Abstract2 §1 metatheory.  Protocols are
-- bare machine morphisms: the real protocol IS the composite MD-mach ∘ Comp-M,
-- because `T₀ Jre GenIf` reduces to `Jre ⊗ GenIf` under the curriedTensor
-- triple.  The one honest new hypothesis of the ≈ᵁ formulation is
-- `stable` : GradeStable, the ℳ-module property of the concrete ℰ — the
-- conservation-law payment made once here at artifact ingestion, which converts
-- the bare ≈ℰ equality `md-emulate` into the U-kernel ≈ᵁ that `_≤UC_` consumes
-- (via `bridge`).  The MD artifacts are hypothesised at their exact types in
-- src/CategoricalCrypto/Examples/MerkleDamgard.agda on branch `random-oracle`,
-- and `MD ≤UC RO` is DERIVED from the §1 dummy-adversary theorem.  Everything
-- still open is bundled in `ROData` — this module itself is hypothesis-free.

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
  {o ℓ e cs ℓs ℓq ℓr ℓv : Level}
  (ℐ-machines : MonoidalCategory o ℓ e)
  (ℰ-standard : Presheaf (MonoidalCategory.U ℐ-machines) (Setoids cs ℓs))
  (ℚ          : Set ℓq)
  -- The RO interface has DISTINCT adversary interfaces for real (Jre) and ideal
  -- (Kid) — Machine.Core's E vs E''.  GenIf is the generator/RO output channel.
  (GenIf Mid Jre Kid : MonoidalCategory.Obj ℐ-machines)
  where

  open StdUC ℐ-machines ℰ-standard

  -- The protocol domain is closed on the input side; Bo = T₀ Jre GenIf.
  Ao Bo : Channel
  Ao = unit ⊗₀ unit
  Bo = Jre ⊗₀ GenIf

  -- ── The RO/MD interface, hypothesised at its MerkleDamgard.agda types ───────
  --   E Dgr asks≤ runWith badProb Pr₁ adv
  --   Preserved badProb-super SuperCert badProb-bounded
  --   Coupling{fR,fI,realK,idealK,FLGP}  _≈ℰ[_]_  bound
  record ROData : Set (suc ℓr ⊔ suc ℓv ⊔ ℓq ⊔ o ⊔ ℓ ⊔ cs ⊔ ℓs) where
    infix 4 _≈ℰ[_]_
    field
      -- `_≈ℰ[ ε ]_`: any distinguisher of ≤ n queries has advantage ≤ ε n.  MD's
      -- own `_≈ℰ[_]_` already quantifies the codomain but pins the domain at the
      -- unit channel; only that domain is generalised here.
      _≈ℰ[_]_ : ∀ {A B} → ∣machines∣ [ A , B ] → (ℕ → ℚ) → ∣machines∣ [ A , B ] → Set ℓr
      bound   : ℕ → ℚ                              -- bound
      Comp-M    : ∣machines∣ [ Ao , Mid ]          -- Comp.M
      MD-mach   : ∣machines∣ [ Mid , Bo ]          -- MD
      General-M : ∣machines∣ [ Ao , Bo ]           -- General.M (the ideal RO)
      MD-secure : General-M ≈ℰ[ bound ] MD-mach ∘ Comp-M  -- indistinguishable
      -- BRIDGE (M5): a concrete per-budget bound with a vanishing profile
      -- establishes the ε-absorption setoid equality (the kernel of ℰ-standard).
      VanishingBound : (ℕ → ℚ) → Set ℓv
      van            : VanishingBound bound
      absorb : ∀ {A B} {f g : ∣machines∣ [ A , B ]} {ε : ℕ → ℚ} → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ℰ g
      -- BRIDGE (M6): the ideal protocol and its simulator.
      roIdeal     : ∣machines∣ [ Ao , T₀ Kid GenIf ]
      roSimulator : ∣machines∣ [ Kid , Jre ]
      ideal-bridge : sub roSimulator ∘ roIdeal ≈ℰ General-M
      -- The ℳ-module property of ℰ-standard: bare kernel = U-kernel (see the
      -- Abstract2 header).  The only hypothesis the ≈ᵁ formulation adds.
      stable : GradeStable

  -- ── THE PAYOFF, DERIVED ─────────────────────────────────────────────────────
  module Payoff (ro : ROData) where
    open ROData ro

    -- The real protocol is the MD composite itself — a bare machine morphism at
    -- grade Jre.
    mdProtocol : ∣machines∣ [ Ao , T₀ Jre GenIf ]
    mdProtocol = MD-mach ∘ Comp-M

    -- Consumes only the ε-absorption of the existing MD artifact (MD-secure +
    -- van) and `ideal-bridge`.
    md-emulate : mdProtocol ≈ℰ sub roSimulator ∘ roIdeal
    md-emulate = begin
        mdProtocol                 ≈⟨ absorb MD-secure van ⟨
        General-M                  ≈⟨ ideal-bridge ⟨
        sub roSimulator ∘ roIdeal  ∎
      where open SetoidR (≈ℰ-setoid Ao Bo)

    MD≤UC-RO : mdProtocol ≤UC roIdeal
    MD≤UC-RO = dummy-complete (roSimulator , bridge stable md-emulate)
