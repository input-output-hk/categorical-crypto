{-# OPTIONS --safe --without-K #-}

-- The positive linker result is the supported two-component square, not
-- preservation under arbitrary open IPDL wiring. Peeking below is illegal.
module CategoricalCrypto.IPDL.SchedulerInformationTests where

open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base as List hiding (lookup; take)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Sum.Base hiding (map₁; map₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.IPDL.Linker as Linker
open import CategoricalCrypto.IPDL.Native
open import CategoricalCrypto.IPDL.SchedulerInformation
open import CategoricalCrypto.IPDL.SSP
open import CategoricalCrypto.IPDL.Syntax hiding (value)
import CategoricalCrypto.IPDL.Tests as Existing
import CategoricalCrypto.SSP.Dist.FiniteTesting as F
import CategoricalCrypto.SSP.Dist.Kernel as K
import CategoricalCrypto.SSP.Dist.SchedulerInformation as Information
open import CategoricalCrypto.SSP.Iface using (Iface; Ωᴵ)
open import CategoricalCrypto.SSP.Observation
import CategoricalCrypto.SSP.Protocol as P
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind)
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform

Bit : Ctx
Bit = bit ∷ []

get : Command [] Bit
get = inj₂ (inj₁ zero)

step : Command [] Bit
step = inj₂ (inj₂ tt)

absent : Response Bit
absent = inj₂ (inj₁ nothing)

sealed : Bool → Net [] Bit
sealed b = record { H = Bit ; def = (1 , read zero ret) , (0 , ret b) , tt }

state : (b ready : Bool) → Residual.State (sealed b)
state b false = Residual.initial (sealed b)
state b true = tt , waiting 1 (read zero ret) , assigned b , tt

publicReply : Command [] Bit → Response Bit
publicReply (inj₂ (inj₁ zero)) = absent
publicReply (inj₂ (inj₂ tt)) = inj₁ tt

local-round : ∀ b ready t → Model.kernel (sealed b) t (state b ready)
  ≈Mℚ return-ℚ (publicReply t , state b true)
local-round b false (inj₂ (inj₁ zero)) ξ = refl
local-round b true (inj₂ (inj₁ zero)) ξ = refl
local-round b false (inj₂ (inj₂ tt)) ξ = refl
local-round b true (inj₂ (inj₂ tt)) ξ = refl

PublicAPI : Iface
PublicAPI = F.Uniform (Command [] Bit) (Response Bit) (command-dec [] Bit)

publicOracle : K.Oracle PublicAPI Bool
publicOracle ready t _ = return⊥ (true , publicReply t)

native-square : ∀ b → K.Samples {A = PublicAPI} (λ ready → return-ℚ (state b ready))
  publicOracle (F.oracle (Model.kernel (sealed b)))
native-square b false (inj₂ (inj₁ zero)) tt ξ = refl
native-square b true (inj₂ (inj₁ zero)) tt ξ = refl
native-square b false (inj₂ (inj₂ tt)) tt ξ = refl
native-square b true (inj₂ (inj₂ tt)) tt ξ = refl

local-context-closure : ∀ {X} b (a : P.Calls PublicAPI X) ready
  → F.observe (Model.kernel (sealed b)) a (state b ready)
    ≈Mℚ Information.observeOracle publicOracle a ready
local-context-closure b a ready ξ = trans
  (sym (>>=ᴹ-identityˡ (state b ready)
    (λ s → Information.observeOracle {I = PublicAPI} (F.oracle (Model.kernel (sealed b))) a s) ξ))
  (Information.sample-result {I = PublicAPI} {ρ = λ r → return-ℚ (state b r)}
    {O = publicOracle} {O′ = F.oracle (Model.kernel (sealed b))} (native-square b) a ready ξ)

publicContext : P.Protocol PublicAPI Ωᴵ
publicContext = record
  { St = Bool ; init = false
  ; step = λ previous _ _ → P.coin uniform-Bool λ challenge → P.call get tt λ where
      (inj₂ (inj₁ nothing)) → P.call step tt λ _ → P.call get tt λ where
        (inj₂ (inj₁ nothing)) → P.ret (not previous , challenge)
        _ → P.ret (not previous , false)
      _ → P.ret (not previous , false) }

linked-context-square : ∀ b → K.Samples {A = Ωᴵ}
  (K.second (λ ready → return-ℚ (state b ready)))
  (publicContext K.· publicOracle)
  (publicContext K.· F.oracle (Model.kernel (sealed b)))
linked-context-square b = Information.link-samples
  {I = PublicAPI} {ρ = λ ready → return-ℚ (state b ready)}
  {O = publicOracle} {O′ = F.oracle (Model.kernel (sealed b))}
  (native-square b) publicContext

linked-context-closure : ∀ {X} b (a : P.Calls Ωᴵ X) previous ready
  → (K.second (λ r → return-ℚ (state b r)) (previous , ready) >>=ᴹ
      λ s → Information.observeOracle (publicContext K.· F.oracle (Model.kernel (sealed b))) a s)
    ≈Mℚ Information.observeOracle (publicContext K.· publicOracle) a (previous , ready)
linked-context-closure b a previous ready = Information.sample-result
  {I = Ωᴵ} {ρ = K.second (λ r → return-ℚ (state b r))}
  {O = publicContext K.· publicOracle}
  {O′ = publicContext K.· F.oracle (Model.kernel (sealed b))}
  (linked-context-square b) a (previous , ready)

fixed-word : ∀ b ts ready → F.word (Model.kernel (sealed b)) ts (state b ready)
  ≈Mℚ return-ℚ (List.map publicReply ts)
fixed-word b [] ready ξ = refl
fixed-word b (t ∷ ts) ready ξ = trans
  (>>=ᴹ-congʳ (λ (r , s) → Dmap (r ∷_) (F.word (Model.kernel (sealed b)) ts s))
    (Model.kernel (sealed b) t (state b ready)) (return-ℚ (publicReply t , state b true))
    (local-round b ready t) ξ)
  (trans (>>=ᴹ-identityˡ (publicReply t , state b true)
    (λ (r , s) → Dmap (r ∷_) (F.word (Model.kernel (sealed b)) ts s)) ξ)
    (trans (lookupᴰℚ-Dmap (publicReply t ∷_) (F.word (Model.kernel (sealed b)) ts (state b true)) ξ)
      (trans (fixed-word b ts true (ξ ∘ (publicReply t ∷_)))
        (trans (lookupᴰℚ-return (List.map publicReply ts) (ξ ∘ (publicReply t ∷_)))
          (sym (lookupᴰℚ-return (publicReply t ∷ List.map publicReply ts) ξ))))))

native-information : ∀ b ts → Model.execute (sealed b)
  (Information.compileWord (instrumentation (sealed b)) ts) (Residual.initial (sealed b))
  ≈Mℚ return-ℚ (List.map publicReply ts)
native-information b ts ξ = trans
  (sym (lookupᴰℚ-Dmap (λ xs → xs)
    (Model.execute (sealed b) (Information.compileWord (instrumentation (sealed b)) ts)
      (Residual.initial (sealed b))) ξ))
  (trans (Information.extraction (instrumentation (sealed b)) ts (Residual.initial (sealed b)) ξ)
    (fixed-word b ts false ξ))

same-information : ∀ ts → Model.execute (sealed false)
  (Information.compileWord (instrumentation (sealed false)) ts) (Residual.initial (sealed false))
  ≈Mℚ Model.execute (sealed true)
    (Information.compileWord (instrumentation (sealed true)) ts) (Residual.initial (sealed true))
same-information ts ξ = trans (native-information false ts ξ) (sym (native-information true ts ξ))

legal-privacy : ∀ {X} (a : P.Calls (F.Uniform (Command [] Bit) (Response Bit) (command-dec [] Bit)) X)
  → Experiment.run (sealed false) (Model.legal (sealed false) a)
    ≈Mℚ Experiment.run (sealed true) (Model.legal (sealed true) a)
legal-privacy = fixed-information-to-native (sealed false) (sealed true)
  (Residual.initial (sealed false)) (Residual.initial (sealed true)) same-information

native-privacy : ∀ {X} (a : Strategy [] Bit X)
  → Experiment.runWith (sealed false) return⊥ a (Residual.initial (sealed false))
    ≈Mℚ Experiment.runWith (sealed true) return⊥ a (Residual.initial (sealed true))
native-privacy = fixed-information-to-strategies (sealed false) (sealed true)
  (Residual.initial (sealed false)) (Residual.initial (sealed true)) same-information

private-adaptive : P.Calls (F.Uniform (Command [] Bit) (Response Bit) (command-dec [] Bit)) Bool
private-adaptive = P.coin uniform-Bool λ b → P.call get tt λ where
  (inj₂ (inj₁ nothing)) → P.call step tt λ _ → P.call get tt λ where
    (inj₂ (inj₁ nothing)) → P.ret b
    _ → P.dead
  _ → P.ret false

private-composed : runᵖ (tester (mapStrategy accept (Model.legal (sealed false) private-adaptive)) P.∘ᵖ resource (sealed false))
  ≈Mℚ runᵖ (tester (mapStrategy accept (Model.legal (sealed true) private-adaptive)) P.∘ᵖ resource (sealed true))
private-composed = Consumers.composed-output (sealed false) (sealed true) same-information private-adaptive

absence-test : Strategy [] Bit Bool
absence-test = ask (Get zero) tt λ where
  nothing → finish true
  (just _) → finish false

successful-absence : ∀ b → entries (runᵖ (tester absence-test P.∘ᵖ resource (sealed b)))
  ≡ entries (return⊥ true)
successful-absence b = refl

hidden-peek : (b : Bool) → Residual.State (sealed b) → Maybe Bool
hidden-peek b (_ , _ , hidden , _) = CategoricalCrypto.IPDL.Syntax.value hidden

illegal-observation : (b : Bool) → Dist-ℚ (Maybe Bool)
illegal-observation b = Dmap (hidden-peek b ∘ proj₁) (K.sample (Interaction.turn (sealed b) (Residual.initial (sealed b)) Step tt))

illegal-false : entries (illegal-observation false) ≡ entries (return-ℚ (just false))
illegal-false = refl

illegal-true : entries (illegal-observation true) ≡ entries (return-ℚ (just true))
illegal-true = refl

initial-get : entries (Model.execute Existing.constant
  (Model.logger Existing.constant (get ∷ get ∷ [])) (Residual.initial Existing.constant))
  ≡ entries (return-ℚ (absent ∷ inj₂ (inj₁ (just true)) ∷ []))
initial-get = refl

input-persistent : entries (Model.execute Existing.copy
  (Model.logger Existing.copy (inj₁ (inj₁ false) ∷ inj₁ (inj₁ true) ∷ inj₂ (inj₁ zero) ∷ []))
  (Residual.initial Existing.copy))
  ≡ entries (return-ℚ (inj₁ tt ∷ inj₁ tt ∷ inj₂ (inj₁ (just false)) ∷ []))
input-persistent = refl

recover-absence : recoverResponse {I = []} (Get zero) absent ≡ just nothing
recover-absence = refl

reject-ack : recoverResponse {I = []} {O = Bit} (Get zero) (inj₁ tt) ≡ nothing
reject-ack = refl

reject-other-port : recoverResponse {I = []} {O = bit ∷ Bit} (Get zero)
  (inj₂ (inj₂ (inj₁ (just true)))) ≡ nothing
reject-other-port = refl

linked-repeat : Strategy [] Bit Bool
linked-repeat = random uniform-Bool λ challenge → ask Step tt λ _ → ask (Get zero) tt λ a →
  ask (Get zero) tt λ b → finish (matches challenge a b)
  where
  matches : Bool → Maybe Bool → Maybe Bool → Bool
  matches false (just false) (just false) = true
  matches true (just true) (just true) = true
  matches _ _ _ = false

linked-composed : runᵖ (tester linked-repeat P.∘ᵖ Linker.Shared.L.linked)
  ≈Mℚ (Experiment.run Linker.Shared.L.flat linked-repeat >>=ᴹ return⊥)
linked-composed = Linker.Shared.adaptive-square linked-repeat

linked-correlated : Strategy [] Bit Bool
linked-correlated = ask Step tt λ _ → ask (Get zero) tt λ a →
  ask (Get zero) tt λ b → finish (same a b)
  where
  same : Maybe Bool → Maybe Bool → Bool
  same (just false) (just false) = true
  same (just true) (just true) = true
  same _ _ = false

linked-correlation : entries (runᵖ (tester linked-correlated P.∘ᵖ Linker.Shared.L.linked))
  ≡ entries (uniform-Bool >>=ᴹ λ _ → return⊥ true)
linked-correlation = refl

flat-correlation : entries (runᵖ (tester linked-correlated P.∘ᵖ resource Linker.Shared.L.flat))
  ≡ entries (uniform-Bool >>=ᴹ λ _ → return⊥ true)
flat-correlation = refl

acceptReward : Maybe Bool → ℚ
acceptReward (just true) = 1ℚ
acceptReward _ = 0ℚ

linked-correlation-mass : E (runᵖ (tester linked-correlated P.∘ᵖ Linker.Shared.L.linked)) acceptReward ≡ 1ℚ
linked-correlation-mass = refl

flat-correlation-mass : E (runᵖ (tester linked-correlated P.∘ᵖ resource Linker.Shared.L.flat)) acceptReward ≡ 1ℚ
flat-correlation-mass = refl

linked-acceptance : E (runᵖ (tester linked-repeat P.∘ᵖ Linker.Shared.L.linked)) acceptReward
  ≡ E (uniform-Bool >>=ᴹ return⊥) acceptReward
linked-acceptance = refl

context-acceptance : ∀ b
  → E ((publicContext K.· F.oracle (Model.kernel (sealed b))) (false , state b false) tt tt)
      (λ z → acceptReward (Data.Maybe.Base.map proj₂ z))
    ≡ E (uniform-Bool >>=ᴹ return⊥) acceptReward
context-acceptance b = refl

linked-acceptance-half : E (runᵖ (tester linked-repeat P.∘ᵖ Linker.Shared.L.linked)) acceptReward ≡ ½
linked-acceptance-half = refl

flat-acceptance-half : E (runᵖ (tester linked-repeat P.∘ᵖ resource Linker.Shared.L.flat)) acceptReward ≡ ½
flat-acceptance-half = refl

context-acceptance-half : ∀ b
  → E ((publicContext K.· F.oracle (Model.kernel (sealed b))) (false , state b false) tt tt)
      (λ z → acceptReward (Data.Maybe.Base.map proj₂ z)) ≡ ½
context-acceptance-half b = refl

successful-absence-mass : ∀ b → E (runᵖ (tester absence-test P.∘ᵖ resource (sealed b))) acceptReward ≡ 1ℚ
successful-absence-mass b = refl

illegal-false-mass : E (illegal-observation false) acceptReward ≡ 0ℚ
illegal-false-mass = refl

illegal-true-mass : E (illegal-observation true) acceptReward ≡ 1ℚ
illegal-true-mass = refl

illegal-separation : E (illegal-observation false) acceptReward
  ≢ E (illegal-observation true) acceptReward
illegal-separation ()
