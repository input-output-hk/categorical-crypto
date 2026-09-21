{-# OPTIONS --safe --without-K --guardedness #-}

-- The UC-object reading of layer 1's `_∘ᵖ_`: a closed system built from two
-- protocols is a CATEGORICAL composite of two homs of the seal, so its lower
-- component is an identifiable factor with an exposed interface, and an
-- emulation assumed of that factor alone lifts to the whole system.
--
-- The two homs are `UC.Seam.Grounded`'s `closedᵒ` and `stageᵒ`, both trivially
-- graded, the stage's DOMAIN being the interface the lower component answers on
-- — the port.  The trivial grade is also the graded monad's `return`
-- (`CurriedTensor.Properties.return-λ⇐`): a protocol image carries no adversary
-- interface, so both homs are pure and the port is the only interface the
-- factoring exposes.
--
-- `factorᵖ` is the factoring, in 𝒞's own equality — machine simulation
-- equivalence, strictly finer than `_≈ᵁ_` — and it is one `assoc` away from
-- being definitional: `procᵒ` is functorial on the nose (`Seal.procᵒ-∘`) and
-- `morphism` maps `_∘ᵖ_` to the machine composite
-- (`Protocol.Machine.Total.morphismCompose`), so the only content is the unit
-- grade the Kleisli composition introduces, removed by `sub λ⇒`.

open import Categories.Functor.Monoidal.CurriedTensor.Properties using (return-λ⇐)

open import CategoricalCrypto.Iface using (Iface; unitᴵ)
open import CategoricalCrypto.Protocol using (Protocol; _∘ᵖ_)
open import CategoricalCrypto.Protocol.Machine using (morphism)
open import CategoricalCrypto.Protocol.Machine.Total using (morphismCompose)
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Model.Seal using (procᵒ; procᵒ-∘; 𝔾ᵒ; ≈ᴹ⇒≈ᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam.Grounded using (closedᵒ; stageᵒ; ιᴳ)

import CategoricalCrypto.Abstract2.Factor as F

module CategoricalCrypto.UC.Factor where

open HomReasoning

private module Fc = F StdSetup

------------------------------------------------------------------------
-- The factoring

-- The trivial grade is the graded monad's unit, which is what lets a pure
-- composite be recognized as one.
closedᵒ-return : {B : Iface} (w : Proc unitᴵ B) → closedᵒ w ≈ return ∘ procᵒ w
closedᵒ-return _ = ⟺ (return-λ⇐ 𝔾ᵒ) ⟩∘⟨refl

factorᵒ : {B C : Iface} (g : Proc B C) (w : Proc unitᴵ B)
        → sub λ⇒ ∘ (stageᵒ g ∙ closedᵒ w) ≈ ιᴳ C ∘ (procᵒ g ∘ procᵒ w)
factorᵒ g w = (refl⟩∘⟨ (refl⟩∘⟨ closedᵒ-return w))
            ○ Fc.∙-return (stageᵒ g) (procᵒ w) ○ assoc

-- The UC-object image of `_∘ᵖ_`: the closed system IS the stage composed with
-- the closed lower component, regraded by the unit.
factorᵖ : {B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol unitᴵ B)
        → closedᵒ (morphism (P₂ ∘ᵖ P₁))
          ≈ sub λ⇒ ∘ (stageᵒ (morphism P₂) ∙ closedᵒ (morphism P₁))
factorᵖ P₂ P₁ =
  (refl⟩∘⟨ (≈ᴹ⇒≈ᵒ (morphismCompose P₂ P₁) ○ procᵒ-∘ (morphism P₂) (morphism P₁)))
  ○ ⟺ (factorᵒ (morphism P₂) (morphism P₁))
