{-# OPTIONS --safe --without-K --guardedness #-}

-- A plumbing demo: `UC.Seam.Carry.agreeToAdv` at two concrete systems.  It
-- turns an environment agreement between the two variants' machine images into
-- the `_≈adv[_]_` the example's transfer lemma consumes.  Additions only — the
-- example is untouched.
--
-- What it does NOT show is that one variant emulates the other.  `Emulᴸ` is
-- `Agreeˢ`, i.e. EXACT agreement at every positive slack, and at the pair this
-- example exists to compare it is refutable: at `Replay.s₀`,
-- `watch s₀ (audited Replay.replay)` returns `true` with probability 1 against
-- `chimeric` and `false` with probability 1 against `inputConsuming`, which
-- `Pin.chimeric-violates`/`consuming-safe` pin.  So the premise is available
-- only at states where the two variants coincide.  The `δ` is likewise slack
-- inherited from `Agreeˢ`'s formulation — exact agreement wants `ε`, not
-- `ε + δ` — not something the ledger needs.
--
-- `advᴸ` names that advantage once rather than inlining it, and that is not
-- taste: the two systems are concrete here, and the seam left as a SUBTERM of
-- `pov-transfer`'s argument does not finish in 1750 s, where naming it makes the
-- whole module a 16 s warm check.  Same lever as `UC.Seam`'s header records for
-- the observations.

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.UC.Model.Seal using (procᵒ)
open import CategoricalCrypto.UC.Model.Setup using (_∘_; _≤UC_)
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Carry
open import CategoricalCrypto.UC.Seam.Grounded using (ιᴳ; unitGrade)

import CategoricalCrypto.Examples.ChimericLedger.POV as POV

module CategoricalCrypto.Examples.ChimericLedger.Carry
  (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

open Ledger ℓ
open POV ℓ ser

open import CategoricalCrypto.Examples.ChimericLedger.Total ℓ ser
  using (nodead-oracle; totalRun-Sys)

-- Exact agreement of the two variants' machine images: no embedded strategy
-- separates them.  Strictly stronger than an emulation, and refutable at the
-- interesting pair — see the header.
Emulᴸ : Variant → Variant → LState → Set
Emulᴸ v₁ v₂ s₀ = Agreeˢ LedgerIf (morphism (Sys v₁ s₀)) (morphism (Sys v₂ s₀))

advᴸ : (v₁ v₂ : Variant) (s₀ : LState) → Emulᴸ v₁ v₂ s₀ → (δ : ℚ) → 0ℚ ℚ.< δ
     → Sys v₁ s₀ ≈adv[ (λ _ → δ) ] Sys v₂ s₀
advᴸ v₁ v₂ s₀ = agreeToAdv (Sys v₁ s₀) (Sys v₂ s₀)

pov-carryᴸ : (v₁ v₂ : Variant) (s₀ : LState) → Emulᴸ v₁ v₂ s₀
           → {ε : ℕ → ℚ} (δ : ℚ) → 0ℚ ℚ.< δ
           → POVaudit v₁ s₀ ε → POVaudit v₂ s₀ (λ q → ε q ℚ.+ δ)
pov-carryᴸ v₁ v₂ s₀ ag δ δ>0 = pov-transfer v₁ v₂ s₀ (advᴸ v₁ v₂ s₀ ag δ δ>0)

-- …and the same premise in UC vocabulary.  `Emulᴸ` is the seam's own form; an
-- emulation at the TRIVIAL GRADE is one (`UC.Seam.Grounded.unitGrade`, whose
-- totality hypotheses `ChimericLedger.Total` discharges), so the carry can be
-- stated with the simulator visible instead of as a direct agreement.  Which
-- variant emulates which is a separate question, and the chimeric attack
-- answers it in the negative for the insecure one
-- (`docs/protocol-implementation-review.md`, completion goal).
Emulᵁᶜ : Variant → Variant → LState → Set₁
Emulᵁᶜ v₁ v₂ s₀ = ιᴳ LedgerIf ∘ procᵒ (morphism (Sys v₁ s₀))
               ≤UC ιᴳ LedgerIf ∘ procᵒ (morphism (Sys v₂ s₀))

emulᵁᶜ : (v₁ v₂ : Variant) (s₀ : LState) → Emulᵁᶜ v₁ v₂ s₀ → Emulᴸ v₁ v₂ s₀
emulᵁᶜ v₁ v₂ s₀ = unitGrade LedgerIf _ _ (totalRun-Sys oracle nodead-oracle v₁ s₀)
                                         (totalRun-Sys oracle nodead-oracle v₂ s₀)

pov-carryᵁᶜ : (v₁ v₂ : Variant) (s₀ : LState) → Emulᵁᶜ v₁ v₂ s₀
            → {ε : ℕ → ℚ} (δ : ℚ) → 0ℚ ℚ.< δ
            → POVaudit v₁ s₀ ε → POVaudit v₂ s₀ (λ q → ε q ℚ.+ δ)
pov-carryᵁᶜ v₁ v₂ s₀ em = pov-carryᴸ v₁ v₂ s₀ (emulᵁᶜ v₁ v₂ s₀ em)
