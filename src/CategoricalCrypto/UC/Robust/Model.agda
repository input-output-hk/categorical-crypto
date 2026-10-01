{-# OPTIONS --safe --without-K --guardedness #-}

-- The qualitative carry at the intended instance: `UC.Robust` at the model's
-- setup, and its acceptance test at a selected environment class.

open import Data.Empty
open import Data.Sum.Base

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup

module CategoricalCrypto.UC.Robust.Model where

open import CategoricalCrypto.UC.Robust StdSetup using (Factors; Robust; factors-closed; uc-preserves-at)
open import Relation.Binary.Properties.Setoid.Ext S

-- The stateless relay that exposes its own caller interface as its adversary
-- grade, so `relayᵒ A` is a graded hom whose grade is real data.  `gradedᵒ` is
-- what makes it nameable: the seal hides `_⊗₀_`, so `T₀ X B` cannot be met by a
-- machine on the interface sum without a coercion out of the `opaque` block.
relayᵒ : (A : Iface) → ifaceᵒ A ⇒ T₀ (ifaceᵒ A) (ifaceᵒ unitᴵ)
relayᵒ A = gradedᵒ (wireᴹ inj₁ [ (λ n → n) , ⊥-elim ])

-- The acceptance test the top class cannot give: a nontrivial `Adm`
-- (`UC.Robust.Factors`), a simulator that is a real machine — `relayᵒ` — and
-- the preservation applied at that explicit witness rather than at an
-- all-simulators closure.
relay-selectedᵒ : (𝔄 : Iface) (r : S.Carrier) (V : Channel)
                → Robust (λ W → always {D = T₀ W (ifaceᵒ 𝔄)} ∼[ r ]) (Factors V) (relayᵒ 𝔄)
                → Robust (λ W → always {D = T₀ W (ifaceᵒ 𝔄)} ∼[ r ]) (Factors V)
                         (sub (relayᵒ 𝔄) ∘ relayᵒ 𝔄)
relay-selectedᵒ 𝔄 r V = uc-preserves-at (λ W → always {D = T₀ W (ifaceᵒ 𝔄)} ∼[ r ]) (Factors V)
                                         (relayᵒ 𝔄) ≈ᵁ-refl (factors-closed V (relayᵒ 𝔄))
