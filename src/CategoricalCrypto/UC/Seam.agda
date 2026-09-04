{-# OPTIONS --safe --without-K --guardedness #-}

-- Where layer 1's `POV`/`_≈adv[_]_`/`transfer` sit relative to `_≤UC_`.
--
-- Layer 1 already has the carry: `Protocol.Observe.transfer` turns a safety
-- bound on one system into a bound on an indistinguishable one, with the
-- advantage added, and that is what the ledger example's `pov-transfer` uses.
-- What an emulation at the machine layer buys is the *hypothesis* of that
-- theorem — nothing more — so the seam is one stated implication and one
-- composite, and the composite is proved here.
--
-- The stated implication's two halves are themselves already stated:
-- `UC.Bridge.Reflects` reads an ancilla context as a single strategy, and
-- `Protocol.Machine.PrAgree` reads `runᴹ`'s cumulative mass as layer 1's `Pr`.
-- Neither is assumed anywhere.

open import Data.Nat.Base using (ℕ)
open import Data.Rational as ℚ using (ℚ; 0ℚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol using (Protocol)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Observe using (Bounded; _≈adv[_]_; transfer)
open import CategoricalCrypto.Strategy using (Strat; asks≤)
open import CategoricalCrypto.UC.Base using (Grading)
open import CategoricalCrypto.UC.Machine using (𝒫ᴵ; UCBaseᴹ)

import CategoricalCrypto.UC.Emulation as Em

module CategoricalCrypto.UC.Seam (G : Grading 𝒫ᴵ) where

private module E = Em (UCBaseᴹ G)

-- Environment agreement at the machine layer gives layer 1's advantage bound
-- at every positive slack.  Stated, not proved.
AgreeToAdv : Set₁
AgreeToAdv = {B : Iface} (P Q : Protocol unitᴵ B)
           → E._≈ℰ_ (morphism P) (morphism Q)
           → (ε : ℚ) → 0ℚ ℚ.< ε → P ≈adv[ (λ _ → ε) ] Q

-- The POV carry: a bound on the ideal system's bad event becomes one on the
-- real system's, at `ε + δ` for an arbitrarily small `δ`.
pov-carry : AgreeToAdv → {B : Iface} (P Q : Protocol unitᴵ B)
          → E._≈ℰ_ (morphism P) (morphism Q)
          → {bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)} {ε : ℕ → ℚ}
          → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
          → (δ : ℚ) → 0ℚ ℚ.< δ
          → Bounded Q bad ε → Bounded P bad (λ q → ε q ℚ.+ δ)
pov-carry a2a P Q em bad-asks δ δ>0 =
  transfer bad-asks (a2a Q P (E.≈ℰ-sym em) δ δ>0)
