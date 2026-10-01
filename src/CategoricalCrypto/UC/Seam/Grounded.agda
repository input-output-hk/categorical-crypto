{-# OPTIONS --safe --without-K --guardedness #-}

-- The trivial grade at the sealed machine bundle (`UC.Model.Setup`): the grade
-- object, the wire that inflates a process to it, the images of open and
-- closed processes there, and how the degenerate ancilla reads back.
--
-- The grade is the sealed bundle's OWN monoidal unit, not `unitᴵ`: the two are
-- the empty interface spelled with two different empty types, and the iso
-- between them is over the perf bar (`docs/stduc-supersession-plan.md` §1.1).

open import Categories.Category
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Data.Bool.Base
open import Data.Unit.Base

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Compose
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.Seam

import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.UC.Seam.Grounded where

private module 𝒫 = Category 𝒫ᴵ

open MonR monoidal
open MR ∣machines∣

------------------------------------------------------------------------
-- The trivial grade

𝟘ᴳ : Channel
𝟘ᴳ = unit

ιᴳ : (B : Iface) → ifaceᵒ B ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
ιᴳ _ = unitorˡ.to

-- A protocol image at the trivial grade, OPEN at the port the component below
-- it answers on (`factorᵖ`, where two are the factors of a closed two-stage
-- system)…
stageᵒ : {A B : Iface} → Proc A B → ifaceᵒ A ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
stageᵒ {B = B} g = ιᴳ B ∘ procᵒ g

-- …and a CLOSED one, as the UC layer sees it.
closedᵒ : {B : Iface} → Proc unitᴵ B → ifaceᵒ unitᴵ ⇒ T₀ 𝟘ᴳ (ifaceᵒ B)
closedᵒ = stageᵒ

------------------------------------------------------------------------
-- A closed two-stage system as a categorical composite

-- Layer 1's `_∘ᵖ_` read as a composite of two homs of the seal, so its lower
-- component is a factor with an exposed interface, and an emulation assumed of
-- that factor alone lifts to the whole system.  Both homs are pure (the trivial
-- grade is the graded monad's `return`, `λ⇐` on the nose), so the port is the
-- only interface the factoring exposes.  `factorᵖ` holds in 𝒞's own
-- equality, strictly finer than `_≈ᵁ_`.

-- `closedᵒ w` is `return ∘ procᵒ w` on the nose, which is what lets a pure
-- composite be recognized as one.
factorᵒ : {B C : Iface} (g : Proc B C) (w : Proc unitᴵ B)
        → sub λ⇒ ∘ (stageᵒ g ∙ closedᵒ w) ≈ ιᴳ C ∘ (procᵒ g ∘ procᵒ w)
factorᵒ g w = ∙-return (stageᵒ g) (procᵒ w) ○ assoc

factorᵖ : {B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol unitᴵ B)
        → closedᵒ (morphism (P₂ ∘ᵖ P₁))
          ≈ sub λ⇒ ∘ (stageᵒ (morphism P₂) ∙ closedᵒ (morphism P₁))
factorᵖ P₂ P₁ =
  (refl⟩∘⟨ (≈ᴹ⇒≈ᵒ (morphismCompose P₂ P₁) ○ procᵒ-∘ (morphism P₂) (morphism P₁)))
  ○ ⟺ (factorᵒ (morphism P₂) (morphism P₁))

------------------------------------------------------------------------
-- The degenerate ancilla

plug-λ : {D X : Channel} (t : X ⇒ Ωᵒ) (w : D ⇒ X)
       → ((t ∘ unitorˡ.from) ∘ T₁ 𝟘ᴳ w) ∘ unitorˡ.to ≈ t ∘ w
plug-λ t w = (assoc ○ (refl⟩∘⟨ unitorˡ-commute-from) ○ sym-assoc) ⟩∘⟨refl
           ○ cancelʳ unitorˡ.isoʳ

-- The environment's composite, read across the seal.
plug-run : (B : Iface) (d : Strat (Neg B) (Pos B)) (w : Proc unitᴵ B)
         → ⟦ strategyEnv B d 𝒫.∘ w ⟧ᴼ ≈ₚ Obs (procᵒ (strategyEnv B d) ∘ procᵒ w)
plug-run B d w = runᴹ-resp-≈ᴹ (Pw.S.⟺ᴹ (unprocᵒ-∘ (strategyEnv B d) w)) (ask tt out)
