{-# OPTIONS --safe --without-K --guardedness #-}

-- The chimeric ledger factored as `ledger ∘ hash` at the UC LAYER, and the
-- end-to-end corollary at a hash-level premise.
--
-- The factoring exists at layer 1 already — `ChimericLedger.POV.Sysᴴ` is
-- `ledger vr s₀ ∘ᵖ hash` — but everything the UC layer sees is the CLOSED
-- system `closedᵒ (morphism (Sysᴴ …))`, inside which the hash is invisible.
-- `ledger-factor` is that reading repaired: the same closed system is
-- `ledgerᵒ ∙ hashᵒ hash` regraded by the unit, where `hashᵒ hash n` is a hom
-- whose codomain is the PORT `hashPortᵒ n = ifaceᵒ (HashIf^ω n)` and `ledgerᵒ`
-- is a hom out of that port.
--
-- `hash-lift` is what the exposed port buys: the emulation may be assumed of
-- the hash alone, and `UC-compose` carries it to the system
-- (`UC.Factor.liftᵖ`).  `ledger-pov-from-hash` is `Real.ledger-pov` behind it —
-- the same conclusion, with `Real ≤UC^ω Ideal` replaced by
-- `hash ≤UC^ω oracle^ω`, which is `docs/end-to-end.md`'s continuation item 1.
-- Nothing about the ledger is assumed: it enters the lift only through
-- `≤UC-refl`.
--
-- What this does NOT give is a nontrivial simulator.  The ledger is pure with
-- respect to the graded monad and the random oracle exposes no adversary
-- interface, so the simulator `UC-compose` builds here is the trivial one; the
-- interactive-simulator example of
-- `docs/protocol-implementation-review.md` §3 belongs at this port but is a
-- separate construction (`docs/ledger-factoring.md`).

open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly using (Poly)
open import Data.Product.Base using (Σ-syntax; _×_)
open import Data.Rational as ℚ using (ℚ)

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface using (Iface; Neg; Pos; unitᴵ)
open import CategoricalCrypto.Protocol.Live using (NoDeadStep)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Observe using (PrHit)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Approximate using (Negligible)
open import CategoricalCrypto.UC.Asymptotic using (_≤UC^ω_)
open import CategoricalCrypto.UC.Factor using (factorᵖ; liftᵖ)
open import CategoricalCrypto.UC.Model.Seal using (ifaceᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Saturated using (Systems)
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ; stageᵒ; 𝟘ᴳ)

module CategoricalCrypto.Examples.ChimericLedger.Factor
  (ser : (n : ℕ) → Ledger.Tx n → List Bool) where

open import CategoricalCrypto.Examples.ChimericLedger.Real ser
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
-- The factoring, and the lift

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

-- The slides-literal premise: `H ≤UC RO` at the port, `Ledger ∘ H ≤UC Ledger ∘ RO`
-- at the system.  The hash premise is the SAME relation the system-level one is
-- stated in (`UC.Asymptotic._≤UC^ω_`), read at the hash interface.
hash-lift : (hash : Systems HashIf^ω) (vr : Variant) (s : (n : ℕ) → Ledger.LState n)
          → hash ≤UC^ω oracle^ω → Realᴴ hash vr s ≤UC^ω Realᴴ oracle^ω vr s
hash-lift hash vr s hp n = liftᵖ (L.ledger n vr (s n)) (hash n) (oracle^ω n) (hp n)

------------------------------------------------------------------------
-- The corollary at the hash premise

module _ (a V : ℕ) (hash : Systems HashIf^ω) (nd : (n : ℕ) → NoDeadStep (hash n)) where

  -- `Real.ledger-pov` verbatim, with the emulation assumed of the hash alone.
  ledger-pov-from-hash : SerInj → hash ≤UC^ω oracle^ω → (p : ℕ → ℕ) → Poly p
                       → Σ[ f ∈ (ℕ → ℚ) ] Negligible f
                         × ((n : ℕ) (d : Strat (Neg (LedgerIf^ω n)) (Pos (LedgerIf^ω n)))
                            → asks≤ (p n) d
                            → PrHit (Real a V inputConsuming hash nd n)
                                    (badReal a V inputConsuming hash nd n) d ℚ.≤ f n)
  ledger-pov-from-hash si hp =
    ledger-pov a V inputConsuming hash nd si
               (hash-lift hash inputConsuming (gen a V) hp)
