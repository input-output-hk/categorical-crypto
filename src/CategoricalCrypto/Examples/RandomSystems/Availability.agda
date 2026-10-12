{-# OPTIONS --safe --without-K --guardedness #-}

-- Maurer 2011 Definition 3's two modes, through the public construction API.
-- The ideal bit server asks its Eve port how to answer an honest query.
-- Forcing false simulates a real server perfectly but changes its designated
-- no-adversary answer from true to false. A bit-flipping simulator, with the
-- compatible designated mode, gives a full construction and composes twice.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (id)
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (padϕ; point-⊛; simFn)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Graded
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
open import CategoricalCrypto.UC.RandomSystems.Morphism
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.Examples.HashForward.UC as HashForward
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Model.Setup as Sᵒ
import CategoricalCrypto.UC.RandomSystems.Setup as Sᴿ

module CategoricalCrypto.Examples.RandomSystems.Availability where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module G = MonoidalCategory 𝔾ᵒ
  module Q = MonoidalCongruence congᴿ
  module 𝒫 = Category 𝒫ᴵ

Eve : Iface
Eve = dualᴵ Ωᴵ

answer : Bool → Proc Eve 𝟭ᴵ
answer b = MC.mk MC.Iˢ λ where
  (s , inj₁ tt) → returnₚ (s , inj₁ b)
  (_ , inj₂ ())

mode : Bool → ifaceᵒ Eve G.⇒ G.unit
mode b = procᵘ (answer b)

ideal : ifaceᵒ unitᴵ G.⇒ Sᵒ.T₀ (ifaceᵒ Eve) (ifaceᵒ Ωᴵ)
ideal = gradedᵒ (cupᴵ Ωᴵ)

adapt : (Bool → Bool) → Proc Eve Eve
adapt h = wireᴹ id h

adaptᵒ : (Bool → Bool) → ifaceᵒ Eve G.⇒ ifaceᵒ Eve
adaptᵒ h = procᵒ (adapt h)

adapted : (Bool → Bool) → ifaceᵒ unitᴵ G.⇒ Sᵒ.T₀ (ifaceᵒ Eve) (ifaceᵒ Ωᴵ)
adapted h = Sᵒ.sub (adaptᵒ h) G.∘ ideal

private
  answer-adapt : (b : Bool) (h : Bool → Bool)
               → 𝒫._≈_ {Eve} {𝟭ᴵ} (𝒫._∘_ {Eve} {Eve} {𝟭ᴵ} (answer b) (adapt h)) (answer (h b))
  answer-adapt b h = ∘-wireᴹ {Eve} {Eve} {𝟭ᴵ} id h (answer b)
    S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
      (s , inj₁ tt) → >>=ₚ-identityˡ (s , inj₁ b) _
      (_ , inj₂ ()))

mode-adapt : (b : Bool) (h : Bool → Bool) → (mode b G.∘ adaptᵒ h) Q.∼ mode (h b)
mode-adapt b h = Q.≈⇒∼ (G.Equiv.trans (G.Equiv.sym (procᵘ-∘ (answer b) (adapt h)))
                                       (≈ᴹ⇒≈ᵘ (answer-adapt b h)))

------------------------------------------------------------------------
-- The designated modes really answer opposite bits
------------------------------------------------------------------------

bitᴹ : Bool → Proc unitᴵ Ωᴵ
bitᴹ b = MC.mk MC.Iˢ λ where
  (_ , inj₁ ())
  (s , inj₂ tt) → returnₚ (s , inj₂ b)

private
  lifted-bit : Bool → Proc unitᴵ (𝟭ᴵ ⊗ᴵ Ωᴵ)
  lifted-bit b = MC.mk MC.Iˢ λ where
    (_ , inj₁ ())
    (_ , inj₂ (inj₁ ()))
    (s , inj₂ (inj₂ tt)) → returnₚ (s , inj₂ (inj₂ b))

  module Close (b : Bool) where
    a = subᴵ {Eve} {𝟭ᴵ} {Ωᴵ} (answer b)
    c = cupᴵ Ωᴵ
    S₀ = Col.Sᴳ a c
    open Col.Loop (⊥ ⊎ (Neg 𝟭ᴵ ⊎ ⊤)) (⊥ ⊎ (Pos 𝟭ᴵ ⊎ Bool))
                  ((Bool ⊎ ⊤) ⊎ (⊤ ⊎ Bool)) S₀ (Col.kᴳ a c)

    step-law : (p : MC.obj S₀ × (⊥ ⊎ (Neg 𝟭ᴵ ⊎ ⊤)))
             → (MC.step tracedᴹ p >>=ₚ padϕ (λ _ → ttᵛ))
               ≈ₚ MC.step (lifted-bit b) (ttᵛ , proj₂ p)
    step-law ((_ , _) , inj₁ ())
    step-law ((_ , _) , inj₂ (inj₁ ()))
    step-law ((sa , sc) , inj₂ (inj₂ tt)) =
      bindˣ (step-red (sa , sc) (inj₂ (inj₂ tt))
        ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (sa , inj₁ (inj₂ tt)) _)
        ⟨≈⟩ >>=ₚ-identityˡ ((sa , sc) , inj₂ (inj₁ (inj₂ tt))) (contᵢ body)
        ⟨≈⟩ loop-pass (sa , sc) (inj₁ (inj₂ tt)) (sa , sc) (inj₂ (inj₂ (inj₁ tt)))
                      (>>=ₚ-identityˡ (sc , inj₂ (inj₁ tt)) _)
        ⟨≈⟩ loop-pass (sa , sc) (inj₂ (inj₁ tt)) (sa , sc) (inj₂ (inj₁ (inj₁ b)))
                      (bindˣ (>>=ₚ-identityˡ (sa , inj₁ b) _) ⟨≈⟩ >>=ₚ-identityˡ (sa , inj₁ (inj₁ b)) _)
        ⟨≈⟩ loop-pass (sa , sc) (inj₁ (inj₁ b)) (sa , sc) (inj₂ (inj₂ (inj₂ b)))
                      (>>=ₚ-identityˡ (sc , inj₂ (inj₂ b)) _)
        ⟨≈⟩ loop-pass (sa , sc) (inj₂ (inj₂ b)) (sa , sc) (inj₁ (inj₂ (inj₂ b)))
                      (>>=ₚ-identityˡ (sa , inj₂ (inj₂ b)) _))
      ⟨≈⟩ >>=ₚ-identityˡ ((sa , sc) , inj₂ (inj₂ b)) _

    point-law : (x : ⊤ᵛ) → (MC.point S₀ x >>=ₚ λ _ → returnₚ ttᵛ) ≈ₚ returnₚ x
    point-law ttᵛ = bindˣ (point-⊛ MC.Iˢ MC.Iˢ ttᵛ)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _)
      ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , ttᵛ) _

    inner-equality : 𝒫._≈_ {unitᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ}
                       (𝒫._∘_ {unitᴵ} {Eve ⊗ᴵ Ωᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} a c) (lifted-bit b)
    inner-equality = S.⟺ᴹ (Col.compose-raw≈∘ᴳ a c) S.○ᴹ Col.collapseᵀ a c
      S.○ᴹ S.≲⇒≈ᴹ (simFn (λ _ → ttᵛ) point-law step-law)

  closed-equality : (b : Bool)
                   → 𝒫._≈_ {unitᴵ} {Ωᴵ}
                       (𝒫._∘_ {unitᴵ} {Eve ⊗ᴵ Ωᴵ} {Ωᴵ} (plugᴹ (answer b)) (cupᴵ Ωᴵ)) (bitᴹ b)
  closed-equality b = 𝒫.Equiv.trans (𝒫.assoc {unitᴵ} {Eve ⊗ᴵ Ωᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} {Ωᴵ})
    (𝒫.Equiv.trans (𝒫.∘-resp-≈ʳ {unitᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} {Ωᴵ} (Close.inner-equality b))
      (wire-∘ᴹ {unitᴵ} {𝟭ᴵ ⊗ᴵ Ωᴵ} {Ωᴵ} drop⇒ˡ inj₂ (lifted-bit b)
        S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
          (_ , inj₁ ())
          (s , inj₂ tt) → >>=ₚ-identityˡ (s , inj₂ (inj₂ b)) _)))

mode-bit : (b : Bool) → no-adversary (mode b) ideal G.≈ procᵒ (bitᴹ b)
mode-bit b = G.Equiv.trans (plug-graded (answer b) (cupᴵ Ωᴵ)) (≈ᴹ⇒≈ᵒ (closed-equality b))

tell : Strat (⊥ ⊎ ⊤) (⊥ ⊎ Bool)
tell = ask (inj₂ tt) λ where
  (inj₁ ())
  (inj₂ b) → out b

bit-run : (b : Bool) → runˢ (bitᴹ b) tell ≈ₚ returnₚ b
bit-run b = >>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₂ b) _

bits-separated : ¬ (procᵒ (bitᴹ true) Q.∼ procᵒ (bitᴹ false))
bits-separated e =
  let m , le = proj₁ (≈ₚ[]-resp (bit-run true) (bit-run false)
                               (∼ᴿ⇒≈ᴿ-image e tell ½ (toWitness {a? = 0ℚ ℚ.<? ½} _))) true 1
  in 1≰½ (≤-trans (≤-reflexive (sym (returnₚ-cum 0 true (indᵇ true))))
    (≤-trans le (≤-trans (+-monoˡ-≤ ½ (returnₚ-cum-≤ m false (indᵇ true) (indᵇ-nn true)))
                         (≤-reflexive (+-identityˡ ½)))))

------------------------------------------------------------------------
-- Security does not imply availability; compatible modes do
------------------------------------------------------------------------

security-only : Constructs 0ℚ (adapted (λ _ → false)) ideal
security-only = adaptᵒ (λ _ → false) , ≈⇒∼ᴿ[0] G.Equiv.refl

not-available : ¬ Available (mode true) (mode true) (adapted (λ _ → false)) ideal
not-available e = bits-separated
  (Q.∼.trans (Q.≈⇒∼ (G.Equiv.sym (mode-bit true)))
    (Q.∼.trans (Q.∼.sym e)
      (Q.∼.trans (Q.≈⇒∼ (no-adversary-regrade (mode true) (adaptᵒ (λ _ → false)) ideal))
        (Q.∼.trans (no-adversary-resp-converter ideal (mode-adapt true (λ _ → false)))
                   (Q.≈⇒∼ (mode-bit false))))))

not-full : ¬ SecureConstruction (mode true) (mode true) (adapted (λ _ → false)) ideal
not-full c = not-available (SecureConstruction.availability c)

not-full₀ : ¬ SecurelyConstructs 0ℚ 0ℚ (mode true) (mode true) (adapted (λ _ → false)) ideal
not-full₀ c = not-full (Equivalence.from
  (SecureConstruction⇔SecurelyConstructs₀ {f = adapted (λ _ → false)} {g = ideal}) c)

forced-true-full : SecureConstruction (mode true) (mode true) (adapted (λ _ → true)) ideal
forced-true-full = secure-construction-factor {s = adaptᵒ (λ _ → true)}
  {f = adapted (λ _ → true)} {g = ideal} G.Equiv.refl (mode-adapt true (λ _ → true))

forced-true-full₀ : SecurelyConstructs 0ℚ 0ℚ (mode true) (mode true) (adapted (λ _ → true)) ideal
forced-true-full₀ = Equivalence.to
  (SecureConstruction⇔SecurelyConstructs₀ {f = adapted (λ _ → true)} {g = ideal}) forced-true-full

flipped-full : SecureConstruction (mode false) (mode true) (adapted not) ideal
flipped-full = secure-construction-factor {s = adaptᵒ not} G.Equiv.refl (mode-adapt false not)

twice : ifaceᵒ unitᴵ G.⇒ Sᵒ.T₀ (ifaceᵒ Eve) (ifaceᵒ Ωᴵ)
twice = Sᵒ.sub (adaptᵒ not) G.∘ adapted not

twice-to-flipped : SecureConstruction (mode true) (mode false) twice (adapted not)
twice-to-flipped = secure-construction-factor {s = adaptᵒ not} G.Equiv.refl (mode-adapt true not)

twice-full : SecureConstruction (mode true) (mode true) twice ideal
twice-full = secure-construction-trans Q.∼.refl twice-to-flipped flipped-full

flipped-full₀ : SecurelyConstructs 0ℚ 0ℚ (mode false) (mode true) (adapted not) ideal
flipped-full₀ = Equivalence.to (SecureConstruction⇔SecurelyConstructs₀ {f = adapted not} {g = ideal}) flipped-full

twice-full₀ : SecurelyConstructs 0ℚ 0ℚ (mode true) (mode true) twice ideal
twice-full₀ = securely-constructs-trans Q.∼.refl
  (Equivalence.to (SecureConstruction⇔SecurelyConstructs₀ {f = twice} {g = adapted not}) twice-to-flipped)
  flipped-full₀

-- HashForward's public PM proof transports to the actual RS construction
-- relation. It does not choose designated no-adversary converters.
module HashForwardConsumer (Msg Dig : Set) where
  module H = HashForward Msg Dig

  hash-security : Constructs 0ℚ H.realᵒ H.idealᵒ
  hash-security = ≤UC⇒Constructs₀ {f = H.realᵒ} {g = H.idealᵒ} H.real-≤UC

  hash-rs : Transfer.G rewrite⇒RS H.realᵒ Sᴿ.≤UC Transfer.G rewrite⇒RS H.idealᵒ
  hash-rs = Constructs₀⇒≤UCᴿ {f = H.realᵒ} {g = H.idealᵒ} hash-security
