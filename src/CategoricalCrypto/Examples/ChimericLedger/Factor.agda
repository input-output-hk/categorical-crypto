{-# OPTIONS --safe --without-K --guardedness #-}

-- The chimeric ledger factored as `ledger ∘ hash` at the UC LAYER.
--
-- The factoring exists at layer 1 already — `ChimericLedger.POV.Sysᴴ` is
-- `ledger vr s₀ ∘ᵖ hash` — but everything the UC layer sees is the CLOSED
-- system `closedᵒ (morphism (Sysᴴ …))`, inside which the hash is invisible.
-- `ledger-factor` is that reading repaired: the same closed system is
-- `ledgerᵒ ∙ hashᵒ hash` regraded by the unit, where `hashᵒ hash n` is a hom
-- whose codomain is the PORT `hashPortᵒ n = ifaceᵒ (HashIf^ω n)` and `ledgerᵒ`
-- is a hom out of that port.
--
-- What the exposed port buys is `ChimericLedger.FactorEps`'s lifts: the
-- emulation may be assumed of the hash alone.  What it does NOT give is a
-- nontrivial simulator (`docs/ledger-factoring.md`).

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Factor
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated
open import CategoricalCrypto.UC.Seam.Grounded

module CategoricalCrypto.Examples.ChimericLedger.Factor
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Schedule ser

------------------------------------------------------------------------
-- The port

HashIf^ω : ℕ → Iface
HashIf^ω = L.HashIf

-- The hash interface read at the graded objects: the object a hash
-- implementation lands on and the ledger reads from.
hashPortᵒ : ℕ → Channel
hashPortᵒ n = ifaceᵒ (HashIf^ω n)

oracle^ω : Systems HashIf^ω
oracle^ω = L.oracle

-- A hash implementation as a UC-level morphism, trivially graded.
hashᵒ : Systems HashIf^ω → (n : ℕ) → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (hashPortᵒ n)
hashᵒ hash n = closedᵒ (morphism (hash n))

-- …and the ledger as a morphism OUT of the port, which is the factor the UC
-- layer could not see before.
ledgerᵒ : (n : ℕ) (vr : Variant) (s : Ledger.LState n)
        → hashPortᵒ n ⇒ T₀ 𝟘ᴳ (ifaceᵒ (LedgerIf^ω n))
ledgerᵒ n vr s = stageᵒ (morphism (L.ledger n vr s))

------------------------------------------------------------------------
-- The factoring

-- The UC-object image of `ChimericLedger.POV.Sysᴴ`, with the hash exposed.
ledger-factor : (hash : Systems HashIf^ω) (vr : Variant) (n : ℕ) (s : Ledger.LState n)
              → closedᵒ (morphism (L.Sysᴴ n (hash n) vr s))
                ≈ sub λ⇒ ∘ (ledgerᵒ n vr s ∙ hashᵒ hash n)
ledger-factor hash vr n s = factorᵖ (L.ledger n vr s) (hash n)

-- The real family at an arbitrary hash: `Real.Real`'s shape with the state
-- schedule and the variant free.
Realᴴ : Systems HashIf^ω → Variant → ((n : ℕ) → Ledger.LState n)
      → Systems LedgerIf^ω
Realᴴ hash vr s n = L.Sysᴴ n (hash n) vr (s n)
