{-# OPTIONS --safe --without-K --guardedness #-}

-- A reply is not the same observation as absence of a reply. The dropping
-- converter diverges on the honest request, whereas the benign designated
-- mode returns true. These are native RS machines and native no-adversary
-- closure, not a liveness semantics; no fairness or deadline is assumed.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Rational as ℚ using (0ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Examples.RandomSystems.Availability
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (padϕ; point-⊛; simFn)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Cup
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.Availability
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.Quantitative
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Model.Setup as PM

module CategoricalCrypto.Examples.RandomSystems.Delivery where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module P = Category 𝒫ᴵ
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ

alwaysDrop : Proc unitᴵ Ωᴵ
alwaysDrop = MC.mk MC.Iˢ λ _ → botₚ

dropConverter : Proc Eve 𝟭ᴵ
dropConverter = MC.mk MC.Iˢ λ _ → botₚ

dropSimulator : Proc Eve Eve
dropSimulator = MC.mk MC.Iˢ λ _ → botₚ

drop-mode : ifaceᵒ Eve G.⇒ G.unit
drop-mode = procᵘ dropConverter

drop-sim : ifaceᵒ Eve G.⇒ ifaceᵒ Eve
drop-sim = procᵒ dropSimulator

dropping : ifaceᵒ unitᴵ G.⇒ PM.T₀ (ifaceᵒ Eve) (ifaceᵒ Ωᴵ)
dropping = PM.sub drop-sim G.∘ ideal

private
  module CapDrop where
    a = answer true
    c = dropSimulator
    S₀ = Col.Sᴳ a c
    open Col.Loop (⊤ ⊎ ⊥) (Bool ⊎ ⊥) (Bool ⊎ ⊤) S₀ (Col.kᴳ a c)

    step-law : (p : MC.obj S₀ × (⊤ ⊎ ⊥))
             → (MC.step tracedᴹ p >>=ₚ padϕ (λ _ → ttᵛ))
               ≈ₚ MC.step dropConverter (ttᵛ , proj₂ p)
    step-law ((sa , sc) , inj₁ tt) =
      bindˣ (step-red (sa , sc) (inj₁ tt)
        ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _)
      ⟨≈⟩ bot-bind-≈ₚ _
    step-law ((_ , _) , inj₂ ())

    point-law : (x : ⊤ᵛ) → (MC.point S₀ x >>=ₚ λ _ → returnₚ ttᵛ) ≈ₚ returnₚ x
    point-law ttᵛ = bindˣ (point-⊛ MC.Iˢ MC.Iˢ ttᵛ)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _)
      ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

    equality : P._≈_ {Eve} {𝟭ᴵ} (P._∘_ {Eve} {Eve} {𝟭ᴵ} a c) dropConverter
    equality = S.⟺ᴹ (Col.compose-raw≈∘ᴳ a c) S.○ᴹ Col.collapseᵀ a c
      S.○ᴹ S.≲⇒≈ᴹ (simFn (λ _ → ttᵛ) point-law step-law)

  lifted-drop : Proc unitᴵ (𝟭ᴵ ⊗ᴵ Ωᴵ)
  lifted-drop = MC.mk MC.Iˢ λ _ → botₚ

  module CloseDrop where
    a = subᴵ {Eve} {𝟭ᴵ} {Ωᴵ} dropConverter
    c = cupᴵ Ωᴵ
    S₀ = Col.Sᴳ a c
    open Col.Loop (⊥ ⊎ (Neg 𝟭ᴵ ⊎ ⊤)) (⊥ ⊎ (Pos 𝟭ᴵ ⊎ Bool))
                  ((Bool ⊎ ⊤) ⊎ (⊤ ⊎ Bool)) S₀ (Col.kᴳ a c)

    step-law : (p : MC.obj S₀ × (⊥ ⊎ (Neg 𝟭ᴵ ⊎ ⊤)))
             → (MC.step tracedᴹ p >>=ₚ padϕ (λ _ → ttᵛ))
               ≈ₚ MC.step lifted-drop (ttᵛ , proj₂ p)
    step-law ((_ , _) , inj₁ ())
    step-law ((_ , _) , inj₂ (inj₁ ()))
    step-law ((sa , sc) , inj₂ (inj₂ tt)) =
      bindˣ (step-red (sa , sc) (inj₂ (inj₂ tt))
        ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (sa , inj₁ (inj₂ tt)) _)
        ⟨≈⟩ >>=ₚ-identityˡ ((sa , sc) , inj₂ (inj₁ (inj₂ tt))) (contᵢ body)
        ⟨≈⟩ loop-pass (sa , sc) (inj₁ (inj₂ tt)) (sa , sc) (inj₂ (inj₂ (inj₁ tt)))
                      (>>=ₚ-identityˡ (sc , inj₂ (inj₁ tt)) _)
        ⟨≈⟩ loop-bot (sa , sc) (inj₂ (inj₁ tt))
                      (bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _))
      ⟨≈⟩ bot-bind-≈ₚ _

    point-law : (x : ⊤ᵛ) → (MC.point S₀ x >>=ₚ λ _ → returnₚ ttᵛ) ≈ₚ returnₚ x
    point-law ttᵛ = bindˣ (point-⊛ MC.Iˢ MC.Iˢ ttᵛ)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _)
      ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

    equality : P._≈_ {unitᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ}
      (P._∘_ {unitᴵ} {Eve ⊗ᴵ Ωᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} a c) lifted-drop
    equality = S.⟺ᴹ (Col.compose-raw≈∘ᴳ a c) S.○ᴹ Col.collapseᵀ a c
      S.○ᴹ S.≲⇒≈ᴹ (simFn (λ _ → ttᵛ) point-law step-law)

  closed-drop : P._≈_ {unitᴵ} {Ωᴵ}
    (P._∘_ {unitᴵ} {Eve ⊗ᴵ Ωᴵ} {Ωᴵ} (plugᴹ dropConverter) (cupᴵ Ωᴵ)) alwaysDrop
  closed-drop = P.Equiv.trans (P.assoc {unitᴵ} {Eve ⊗ᴵ Ωᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} {Ωᴵ})
    (P.Equiv.trans (P.∘-resp-≈ʳ {unitᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} {Ωᴵ} CloseDrop.equality)
      (wire-∘ᴹ {unitᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} {Ωᴵ} drop⇒ˡ inj₂ lifted-drop
        S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ _ → bot-bind-≈ₚ _)))

drop-compatible : (mode true G.∘ drop-sim) G.≈ drop-mode
drop-compatible = G.Equiv.trans (G.Equiv.sym (procᵘ-∘ (answer true) dropSimulator))
  (≈ᴹ⇒≈ᵘ CapDrop.equality)

drop-closed : no-adversary drop-mode ideal G.≈ procᵒ alwaysDrop
drop-closed = G.Equiv.trans (plug-gradedᵒ dropConverter (cupᴵ Ωᴵ)) (≈ᴹ⇒≈ᵒ closed-drop)

dropping-closed : no-adversary (mode true) dropping Q.∼ procᵒ alwaysDrop
dropping-closed = Q.∼.trans (Q.≈⇒∼ (no-adversary-regrade (mode true) drop-sim ideal))
  (Q.∼.trans (no-adversary-resp-converter ideal (Q.≈⇒∼ drop-compatible)) (Q.≈⇒∼ drop-closed))

drop-run : runˢ alwaysDrop tell ≈ₚ botₚ
drop-run = >>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ bot-bind-≈ₚ _

reply-not-drop : ¬ (procᵒ (bitᴹ true) Q.∼ procᵒ alwaysDrop)
reply-not-drop e =
  let m , le = proj₁ (≈ₚ[]-resp (bit-run true) drop-run
                               (∼ᴿ⇒≈ᴿ-image e tell ½ (toWitness {a? = 0ℚ ℚ.<? ½} _))) true 1
  in 1≰½ (≤-trans (≤-reflexive (sym (returnₚ-cum 0 true (indᵇ true))))
    (≤-trans le (≤-reflexive (trans (cong (ℚ._+ ½) (botₚ-cum m (indᵇ true))) (+-identityˡ ½)))))

drop-security : QAvailabilityᴿ.Witness 0ℚ dropping ideal
drop-security = drop-sim , QUCᴿ.ctx-refl

drop-not-available : ¬ QAvailabilityᴿ.Availability 0ℚ (mode true) (mode true) dropping ideal
drop-not-available h = reply-not-drop
  (Q.∼.trans (Q.≈⇒∼ (G.Equiv.sym (mode-bit true)))
    (Q.∼.trans (Q.∼.sym (Equivalence.from (Available⇔AvailableWithin₀ {f = dropping} {g = ideal})
      (Equivalence.to (Availability⇔AvailableWithin {f = dropping} {g = ideal}) h))) dropping-closed))

reliable-composition : no-adversary (mode true) twice Q.∼ procᵒ (bitᴹ true)
reliable-composition = Q.∼.trans
  (Equivalence.from (Available⇔AvailableWithin₀ {f = twice} {g = ideal})
    (Equivalence.to (Availability⇔AvailableWithin {f = twice} {g = ideal})
      (QAvailabilityᴿ.SecureAvailable.availability generic-twice))) (Q.≈⇒∼ (mode-bit true))

reliable-reply : runˢ (unprocᵒ (no-adversary (mode true) twice)) tell ≈ₚ returnₚ true
reliable-reply = ≈trans (∼ᴿ⇒≈ᴿ reliable-composition tell) (bit-run true)
