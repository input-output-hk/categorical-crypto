{-# OPTIONS --safe --without-K --guardedness #-}

-- The quarter-error security steps come from finite initialization laws, not
-- weakening exact comparisons. A fixed passive cap ignores version tags, so
-- the same steps also bound the honest fault observation independently.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base using (id)
open import Function.Bundles
open import Level using (0ℓ)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable.Core using (toWitness)

open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Examples.FaultFlag
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (padϕ; point-⊛; simFn)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Tensor
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Graded
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Seal.Monoidal
open import CategoricalCrypto.UC.RandomSystems.Advantage
open import CategoricalCrypto.UC.RandomSystems.Composition
open import CategoricalCrypto.UC.RandomSystems.Availability
open import CategoricalCrypto.UC.RandomSystems.Availability.Composition
open import CategoricalCrypto.UC.RandomSystems.Availability.Parallel
open import CategoricalCrypto.UC.RandomSystems.Construction
open import CategoricalCrypto.UC.RandomSystems.Quantitative
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.Model.Setup as PM
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.Examples.FaultFlag.UC where

private
  module G = MonoidalCategory 𝔾ᵒ
  module P = Category 𝒫ᴵ
  module Q = MonoidalCongruence congᴿ
  variable ε : ℚ

realᵒ middleᵒ idealᵒ : ifaceᵒ unitᴵ PM.⇒ PM.T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
realᵒ = gradedᵒ real
middleᵒ = gradedᵒ middle
idealᵒ = gradedᵒ ideal

simᵒ : ifaceᵒ Advᴵ PM.ℐ.⇒ ifaceᵒ Advᴵ
simᵒ = procᵒ simulator

private
  first-factor : gradedᵒ (cache quarter original) G.≈ PM.sub simᵒ PM.∘ middleᵒ
  first-factor = G.Equiv.trans (≈ᴹ⇒≈ᵍ (cache-simulates quarter previous))
    (G.Equiv.sym (sub-gradedᵒ simulator middle))

  second-factor : gradedᵒ (cache (returnₚ false) previous) G.≈ PM.sub simᵒ PM.∘ idealᵒ
  second-factor = G.Equiv.trans
    (≈ᴹ⇒≈ᵍ (P.Equiv.trans (cache-simulates (returnₚ false) latest)
      (P.∘-resp-≈ʳ (false-cache-clean latest))))
    (G.Equiv.sym (sub-gradedᵒ simulator ideal))

  first-bound : realᵒ ∼ᴿ[ ¼ ] (PM.sub simᵒ PM.∘ middleᵒ)
  first-bound = Approximation.≈[]-mono approxᵒ (≤-reflexive (+-identityʳ ¼))
    (Approximation.≈[]-trans approxᵒ
      (gradedᵒ-≈ᴿ[] (half-quarter-cache original)) (≈⇒∼ᴿ[0] first-factor))

  second-bound : middleᵒ ∼ᴿ[ ¼ ] (PM.sub simᵒ PM.∘ idealᵒ)
  second-bound = Approximation.≈[]-mono approxᵒ (≤-reflexive (+-identityʳ ¼))
    (Approximation.≈[]-trans approxᵒ
      (gradedᵒ-≈ᴿ[] (quarter-false-cache previous)) (≈⇒∼ᴿ[0] second-factor))

  raw-bound : (s : ifaceᵒ Advᴵ PM.ℐ.⇒ ifaceᵒ Advᴵ)
             → realᵒ ∼ᴿ[ ε ] (PM.sub s PM.∘ idealᵒ)
             → real ≈ᴿ[ ε ] P._∘_ (subᴵ {A = Honᴵ} (unprocᵒ s)) ideal
  raw-bound {ε} s e = ungradedᵒ-∼ᴿ[]
    (Approximation.≈[]-mono approxᵒ (≤-reflexive (+-identityʳ ε))
      (Approximation.≈[]-trans approxᵒ e (≈⇒∼ᴿ[0] factor)))
    where
    factor : (PM.sub s PM.∘ idealᵒ) G.≈ gradedᵒ (P._∘_ (subᴵ {A = Honᴵ} (unprocᵒ s)) ideal)
    factor = G.Equiv.trans
      (G.∘-resp-≈ˡ (G.⊗.F-resp-≈ (G.Equiv.sym (procᵒ-unprocᵒ s) , G.Equiv.refl)))
      (sub-gradedᵒ (unprocᵒ s) ideal)

first-security : realᵒ ≤UCᴿ[ ¼ ] middleᵒ
first-security = Constructs⇒≤UCᴿ[] {f = realᵒ} {g = middleᵒ} (simᵒ , first-bound)

second-security : middleᵒ ≤UCᴿ[ ¼ ] idealᵒ
second-security = Constructs⇒≤UCᴿ[] {f = middleᵒ} {g = idealᵒ} (simᵒ , second-bound)

composed-security : realᵒ ≤UCᴿ[ ¼ ℚ.+ ¼ ] idealᵒ
composed-security = ≤UCᴿ[]-trans {f = realᵒ} {g = middleᵒ} {h = idealᵒ} first-security second-security

half-security : realᵒ ≤UCᴿ[ ½ ] idealᵒ
half-security = composed-security

composed-simulator : proj₁ composed-security ≡ simᵒ PM.ℐ.∘ simᵒ
composed-simulator = refl

composed-simulator-image : proj₁ composed-security G.≈ procᵒ doubleSimulator
composed-simulator-image = G.Equiv.sym (procᵒ-∘ simulator simulator)

composed-error-positive : 0ℚ ℚ.< (¼ ℚ.+ ¼)
composed-error-positive = +-mono-< 0<¼ 0<¼

security-condition : Constructs ½ realᵒ idealᵒ
security-condition = ≤UCᴿ[]⇒Constructs {f = realᵒ} {g = idealᵒ} half-security

no-small-construction : ε ℚ.< ½ → ¬ (Constructs ε realᵒ idealᵒ)
no-small-construction small (s , e) = no-small-simulation small (unprocᵒ s) (raw-bound s e)

no-small-security : ε ℚ.< ½ → ¬ (realᵒ ≤UCᴿ[ ε ] idealᵒ)
no-small-security {ε} small w = no-small-construction small
  (≤UCᴿ[]⇒Constructs {ε = ε} {f = realᵒ} {g = idealᵒ} w)

------------------------------------------------------------------------
-- A fixed passive mode retains the honest initialization error
------------------------------------------------------------------------

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

passiveᴹ : Proc Advᴵ 𝟭ᴵ
passiveᴹ = MC.mk MC.Iˢ λ where
  (_ , inj₁ _) → botₚ
  (_ , inj₂ ())

passive : ifaceᵒ Advᴵ G.⇒ G.unit
passive = procᵘ passiveᴹ

passive-simulator : (passive G.∘ simᵒ) G.≈ passive
passive-simulator = G.Equiv.trans (G.Equiv.sym (procᵘ-∘ passiveᴹ simulator))
  (≈ᴹ⇒≈ᵘ (∘-wireᴹ {Advᴵ} {Advᴵ} {𝟭ᴵ} previousTag id passiveᴹ
    S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
      (_ , inj₁ _) → bot-bind-≈ₚ _
      (_ , inj₂ ()))))

first-full : QAvailabilityᴿ.SecureAvailable ¼ ¼ passive passive realᵒ middleᵒ
first-full = QAvailabilityᴿ.secure-mode-preserving
  {s = simᵒ} {f = realᵒ} {g = middleᵒ} (Q.≈⇒∼ passive-simulator) (proj₂ first-security)

second-full : QAvailabilityᴿ.SecureAvailable ¼ ¼ passive passive middleᵒ idealᵒ
second-full = QAvailabilityᴿ.secure-mode-preserving
  {s = simᵒ} {f = middleᵒ} {g = idealᵒ} (Q.≈⇒∼ passive-simulator) (proj₂ second-security)

composed-full : QAvailabilityᴿ.SecureAvailable (¼ ℚ.+ ¼) (¼ ℚ.+ ¼) passive passive realᵒ idealᵒ
composed-full = QAvailabilityᴿ.secure-trans
  {f = realᵒ} {g = middleᵒ} {h = idealᵒ} first-full second-full

native-full : SecurelyConstructs ½ ½ passive passive realᵒ idealᵒ
native-full = Equivalence.to
  (SecureAvailable⇔SecurelyConstructs {f = realᵒ} {g = idealᵒ}) composed-full

no-small-full : ε ℚ.< ½ → ¬ (QAvailabilityᴿ.SecureAvailable ε ½ passive passive realᵒ idealᵒ)
no-small-full small c = no-small-security small (QAvailabilityᴿ.SecureAvailable.security c)

------------------------------------------------------------------------
-- Two independent quarter constructions, with a product passive cap
------------------------------------------------------------------------

parallel-real parallel-ideal : (ifaceᵒ unitᴵ G.⊗₀ ifaceᵒ unitᴵ) G.⇒
  PM.T₀ (ifaceᵒ Advᴵ G.⊗₀ ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ G.⊗₀ ifaceᵒ Honᴵ)
parallel-real = parallel middleᵒ middleᵒ
parallel-ideal = parallel idealᵒ idealᵒ

parallel-passive : (ifaceᵒ Advᴵ G.⊗₀ ifaceᵒ Advᴵ) G.⇒ G.unit
parallel-passive = cap-compose passive passive

parallel-full : QAvailabilityᴿ.SecureAvailable (¼ ℚ.+ ¼) (¼ ℚ.+ ¼)
  parallel-passive parallel-passive parallel-real parallel-ideal
parallel-full = QParallelᴿ.secure-parallel
  {f = middleᵒ} {g = idealᵒ} {u = middleᵒ} {v = idealᵒ} second-full second-full

parallel-native-full : SecurelyConstructs ½ ½
  parallel-passive parallel-passive parallel-real parallel-ideal
parallel-native-full = Equivalence.to
  (SecureAvailable⇔SecurelyConstructs {f = parallel-real} {g = parallel-ideal}) parallel-full

parallel-simulator : proj₁ (QAvailabilityᴿ.SecureAvailable.security parallel-full) ≡ (simᵒ G.⊗₁ simᵒ)
parallel-simulator = refl

faultᴹ : Dₚ Bool → Proc unitᴵ Honᴵ
faultᴹ μ = MC.mk (record { obj = Bool ; point = λ _ → μ }) λ where
  (b , inj₁ ())
  (b , inj₂ tt) → returnₚ (b , inj₂ b)

private
  module CloseFault (μ : Dₚ Bool) (c : Tag) where
    a = subᴵ {Advᴵ} {𝟭ᴵ} {Honᴵ} passiveᴹ
    f = cache μ c
    S₀ = Col.Sᴳ a f
    open Col.Loop (Pos unitᴵ ⊎ Neg (𝟭ᴵ ⊗ᴵ Honᴵ)) (Neg unitᴵ ⊎ Pos (𝟭ᴵ ⊗ᴵ Honᴵ))
      (Neg (Advᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) S₀ (Col.kᴳ a f)

    lifted : Proc unitᴵ (𝟭ᴵ ⊗ᴵ Honᴵ)
    lifted = MC.mk (record { obj = Bool ; point = λ _ → μ }) λ where
      (b , inj₁ ())
      (b , inj₂ (inj₁ ()))
      (b , inj₂ (inj₂ tt)) → returnₚ (b , inj₂ (inj₂ b))

    step-law : (p : MC.obj S₀ × (Pos unitᴵ ⊎ Neg (𝟭ᴵ ⊗ᴵ Honᴵ)))
      → (MC.step tracedᴹ p >>=ₚ padϕ proj₂) ≈ₚ MC.step lifted (proj₂ (proj₁ p) , proj₂ p)
    step-law ((_ , _) , inj₁ ())
    step-law ((_ , _) , inj₂ (inj₁ ()))
    step-law ((st , b) , inj₂ (inj₂ tt)) =
      bindˣ (step-red (st , b) (inj₂ (inj₂ tt))
        ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (st , inj₁ (inj₂ tt)) _)
        ⟨≈⟩ >>=ₚ-identityˡ ((st , b) , inj₂ (inj₁ (inj₂ tt))) _
        ⟨≈⟩ loop-pass (st , b) (inj₁ (inj₂ tt)) (st , b)
          (inj₂ (inj₂ (inj₂ b))) (>>=ₚ-identityˡ (b , inj₂ (inj₂ b)) _)
        ⟨≈⟩ loop-pass (st , b) (inj₂ (inj₂ b)) (st , b)
          (inj₁ (inj₂ (inj₂ b))) (>>=ₚ-identityˡ (st , inj₂ (inj₂ b)) _))
      ⟨≈⟩ >>=ₚ-identityˡ ((st , b) , inj₂ (inj₂ b)) _

    point-law : (x : ⊤ᵛ) → (MC.point S₀ x >>=ₚ λ p → returnₚ (proj₂ p)) ≈ₚ μ
    point-law ttᵛ = bindˣ (point-⊛ MC.Iˢ (MC.state f) ttᵛ)
      ⟨≈⟩ >>=ₚ-assoc (returnₚ ttᵛ) _ _
      ⟨≈⟩ >>=ₚ-identityˡ ttᵛ _
      ⟨≈⟩ >>=ₚ-assoc μ (λ b → returnₚ (ttᵛ , b)) _
      ⟨≈⟩ bindᶠ (λ b → >>=ₚ-identityˡ (ttᵛ , b) _)
      ⟨≈⟩ >>=ₚ-identityʳ μ

    equality : P._≈_ {unitᴵ} {𝟭ᴵ ⊗ᴵ Honᴵ} (P._∘_ {unitᴵ} {Advᴵ ⊗ᴵ Honᴵ} {𝟭ᴵ ⊗ᴵ Honᴵ} a f) lifted
    equality = S.⟺ᴹ (Col.compose-raw≈∘ᴳ a f) S.○ᴹ Col.collapseᵀ a f
      S.○ᴹ S.≲⇒≈ᴹ (simFn proj₂ point-law step-law)

    closed : P._≈_ {unitᴵ} {Honᴵ} (P._∘_ {unitᴵ} {Advᴵ ⊗ᴵ Honᴵ} {Honᴵ} (plugᴹ passiveᴹ) f) (faultᴹ μ)
    closed = P.Equiv.trans (P.assoc {unitᴵ} {Advᴵ ⊗ᴵ Honᴵ} {𝟭ᴵ ⊗ᴵ Honᴵ} {Honᴵ})
      (P.Equiv.trans (P.∘-resp-≈ʳ {unitᴵ} {𝟭ᴵ ⊗ᴵ Honᴵ} {Honᴵ} equality)
        (wire-∘ᴹ {unitᴵ} {𝟭ᴵ ⊗ᴵ Honᴵ} {Honᴵ} drop⇒ˡ inj₂ lifted
          S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
            (b , inj₁ ())
            (b , inj₂ tt) → >>=ₚ-identityˡ (b , inj₂ (inj₂ b)) _)))

  close-cache : (μ : Dₚ Bool) (c : Tag)
    → no-adversary passive (gradedᵒ (cache μ c)) G.≈ procᵒ (faultᴹ μ)
  close-cache μ c = G.Equiv.trans (plug-gradedᵒ passiveᴹ (cache μ c)) (≈ᴹ⇒≈ᵒ (CloseFault.closed μ c))

  close-ideal : no-adversary passive idealᵒ G.≈ procᵒ (faultᴹ (returnₚ false))
  close-ideal = G.Equiv.trans
    (G.∘-resp-≈ʳ (G.∘-resp-≈ʳ (≈ᴹ⇒≈ᵍ (S.⟺ᴹ (false-cache-clean latest)))))
    (close-cache (returnₚ false) latest)

parallelReadˡ parallelReadʳ : Strat
  (Pos (unitᴵ ⊗ᴵ unitᴵ) ⊎ Neg (Honᴵ ⊗ᴵ Honᴵ))
  (Neg (unitᴵ ⊗ᴵ unitᴵ) ⊎ Pos (Honᴵ ⊗ᴵ Honᴵ))
parallelReadˡ = ask (inj₂ (inj₁ tt)) λ where
  (inj₁ (inj₁ ()))
  (inj₁ (inj₂ ()))
  (inj₂ (inj₁ b)) → out b
  (inj₂ (inj₂ _)) → out false
parallelReadʳ = ask (inj₂ (inj₂ tt)) λ where
  (inj₁ (inj₁ ()))
  (inj₁ (inj₂ ()))
  (inj₂ (inj₁ _)) → out false
  (inj₂ (inj₂ b)) → out b

private
  tensor-fault-readˡ : (μ ν : Dₚ Bool)
    → runˢ (tensorᴹ (faultᴹ μ) (faultᴹ ν)) parallelReadˡ
      ≈ₚ (μ >>=ₚ λ b → ν >>=ₚ λ _ → returnₚ b)
  tensor-fault-readˡ μ ν =
    bindᶠ (λ (b , c) →
      bindˣ (tensor-stepˡ (faultᴹ μ) (faultᴹ ν) b c tt
        ⟨≈⟩ >>=ₚ-identityˡ (b , inj₂ b) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₂ (inj₁ b)) _)
    ⟨≈⟩ bindˣ (point-⊛ (MC.state (faultᴹ μ)) (MC.state (faultᴹ ν)) ttᵛ)
    ⟨≈⟩ >>=ₚ-assoc μ _ _
    ⟨≈⟩ bindᶠ (λ b → >>=ₚ-assoc ν _ _
      ⟨≈⟩ bindᶠ (λ c → >>=ₚ-identityˡ (b , c) _))

  tensor-fault-readʳ : (μ ν : Dₚ Bool)
    → runˢ (tensorᴹ (faultᴹ μ) (faultᴹ ν)) parallelReadʳ
      ≈ₚ (μ >>=ₚ λ _ → ν >>=ₚ returnₚ)
  tensor-fault-readʳ μ ν =
    bindᶠ (λ (b , c) →
      bindˣ (tensor-stepʳ (faultᴹ μ) (faultᴹ ν) b c tt
        ⟨≈⟩ >>=ₚ-identityˡ (c , inj₂ c) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₂ (inj₂ c)) _)
    ⟨≈⟩ bindˣ (point-⊛ (MC.state (faultᴹ μ)) (MC.state (faultᴹ ν)) ttᵛ)
    ⟨≈⟩ >>=ₚ-assoc μ _ _
    ⟨≈⟩ bindᶠ (λ b → >>=ₚ-assoc ν _ _
      ⟨≈⟩ bindᶠ (λ c → >>=ₚ-identityˡ (b , c) _))

parallel-passive-compatible : (parallel-passive G.∘ (simᵒ G.⊗₁ simᵒ)) Q.∼ parallel-passive
parallel-passive-compatible = QParallelᴿ.mode-parallel
  (Q.≈⇒∼ passive-simulator) (Q.≈⇒∼ passive-simulator)

private
  parallel-real-closed : no-adversary parallel-passive parallel-real G.≈
    tensorᵒ (tensorᴹ (faultᴹ quarter) (faultᴹ quarter))
  parallel-real-closed = G.Equiv.trans
    (no-adversary-parallel passive passive middleᵒ middleᵒ)
    (G.Equiv.trans (G.⊗.F-resp-≈ (close-cache quarter previous , close-cache quarter previous))
      (procᵒ-tensor (faultᴹ quarter) (faultᴹ quarter)))

  parallel-ideal-closed : no-adversary parallel-passive parallel-ideal G.≈
    tensorᵒ (tensorᴹ (faultᴹ (returnₚ false)) (faultᴹ (returnₚ false)))
  parallel-ideal-closed = G.Equiv.trans
    (no-adversary-parallel passive passive idealᵒ idealᵒ)
    (G.Equiv.trans (G.⊗.F-resp-≈ (close-ideal , close-ideal))
      (procᵒ-tensor (faultᴹ (returnₚ false)) (faultᴹ (returnₚ false))))

opaque
  unfolding tensorᵒ untensorᵒ

  parallel-real-replyˡ : runˢ (untensorᵒ (no-adversary parallel-passive parallel-real)) parallelReadˡ
    ≈ₚ (quarter >>=ₚ λ b → quarter >>=ₚ λ _ → returnₚ b)
  parallel-real-replyˡ = runˢ-resp-≈ᴹ (≈⊗ᵒ⇒≈ᴹ parallel-real-closed) parallelReadˡ
    ⟨≈⟩ tensor-fault-readˡ quarter quarter

  parallel-real-replyʳ : runˢ (untensorᵒ (no-adversary parallel-passive parallel-real)) parallelReadʳ
    ≈ₚ (quarter >>=ₚ λ _ → quarter >>=ₚ returnₚ)
  parallel-real-replyʳ = runˢ-resp-≈ᴹ (≈⊗ᵒ⇒≈ᴹ parallel-real-closed) parallelReadʳ
    ⟨≈⟩ tensor-fault-readʳ quarter quarter

  parallel-ideal-replyˡ : runˢ (untensorᵒ (no-adversary parallel-passive parallel-ideal)) parallelReadˡ
    ≈ₚ returnₚ false
  parallel-ideal-replyˡ = runˢ-resp-≈ᴹ (≈⊗ᵒ⇒≈ᴹ parallel-ideal-closed) parallelReadˡ
    ⟨≈⟩ tensor-fault-readˡ (returnₚ false) (returnₚ false)
    ⟨≈⟩ >>=ₚ-identityˡ false _ ⟨≈⟩ >>=ₚ-identityˡ false _

parallel-honest-fault : Pr≤ 5 (quarter >>=ₚ λ b → quarter >>=ₚ λ _ → returnₚ b) ≡ ¼
parallel-honest-fault = refl

parallel-not-perfect : ¬ Available parallel-passive parallel-passive parallel-real parallel-ideal
parallel-not-perfect e =
  let δ = ¼ ℚ.* ½
      pos = toWitness {a? = 0ℚ ℚ.<? δ} tt
      small = toWitness {a? = δ ℚ.<? ¼} tt
      near = ≈ₚ[]-resp parallel-real-replyˡ parallel-ideal-replyˡ
        (∼ᴿ⇒≈ᴿ-tensor e parallelReadˡ δ pos)
      m , bd = proj₁ near true 5
      false≤0 = returnₚ-cum-≤ m false (indᵇ true) (indᵇ-nn true)
  in <-irrefl refl (≤-<-trans
    (≤-trans (≤-reflexive (sym parallel-honest-fault))
      (≤-trans bd (≤-trans (+-monoˡ-≤ δ false≤0) (≤-reflexive (+-identityˡ δ))))) small)

parallel-not-zero-full : ¬ SecurelyConstructs 0ℚ 0ℚ
  parallel-passive parallel-passive parallel-real parallel-ideal
parallel-not-zero-full c = parallel-not-perfect
  (Equivalence.from (Available⇔AvailableWithin₀ {f = parallel-real} {g = parallel-ideal})
    (SecurelyConstructs.availability c))
