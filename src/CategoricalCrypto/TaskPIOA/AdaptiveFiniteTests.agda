{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.TaskPIOA.AdaptiveFiniteTests where

open import Data.Bool.Base
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using (none; _·_; ⟦_⟧)
open import CategoricalCrypto.SSP.Iface using (Ωᴵ)
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.AdaptiveFinite
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.SSPAdapter using (Tick; resource)
import CategoricalCrypto.TaskPIOA.SSPAdapterTests as Existing
import CategoricalCrypto.TaskPIOA.Tests as Source
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind; maybeℚ)
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (uniform-Bool)

S : Signature
S = Source.coinSignature empty

M : Automaton S
M = Existing.correlated

N : Automaton S
N = record
  { states = bit ⊠ one ; initial = false , tt ; input = λ ()
  ; choose = λ where (b , _) false → just (inj₂ tt) ; (b , _) true → just (inj₁ b)
  ; owns = λ where (b , _) false a refl → refl ; (b , _) true a refl → refl
  ; kernel = λ where (inj₂ _) _ → Dmap (λ b → b , tt) uniform-Bool ; (inj₁ _) q → return-ℚ q }

projectReply : Maybe Bool × (Bool × ⊤) → Maybe Bool × Bool
projectReply (o , (b , _)) = o , b

tick-related : ∀ t b f → E (tick M t b) f
  ≡ E (tick N t (b , tt)) (f ∘ projectReply)
tick-related false b f = trans (lookupᴰℚ-Dmap (nothing ,_) uniform-Bool f)
  (sym (trans (lookupᴰℚ-Dmap (nothing ,_) (Dmap (λ b → b , tt) uniform-Bool) (f ∘ projectReply))
    (lookupᴰℚ-Dmap (λ b → b , tt) uniform-Bool (λ q → f (projectReply (nothing , q))))))
tick-related true b f = trans (lookupᴰℚ-Dmap (just b ,_) (return-ℚ b) f)
  (trans (lookupᴰℚ-return b (λ q → f (just b , q)))
    (sym (trans (lookupᴰℚ-Dmap (just b ,_) (return-ℚ (b , tt)) (f ∘ projectReply))
      (lookupᴰℚ-return (b , tt) (λ q → f (projectReply (just b , q)))))))

padded-related : ∀ ρ b → paddedReplyRun M ρ b ≈Mℚ paddedReplyRun N ρ (b , tt)
padded-related [] b ξ = refl
padded-related (t ∷ ρ) b ξ = trans
  (E-bind (tick M t b) (λ (o , b′) → Dmap (o ∷_) (paddedReplyRun M ρ b′)) ξ)
  (trans (lookupᴰℚ-cong-P (entries (tick M t b)) (λ { (o , b′) →
    trans (lookupᴰℚ-Dmap (o ∷_) (paddedReplyRun M ρ b′) ξ)
      (padded-related ρ b′ (ξ ∘ (o ∷_))) }))
    (trans (tick-related t b (λ (o , b′) → E (paddedReplyRun N ρ (b′ , tt)) (ξ ∘ (o ∷_))))
      (sym (trans (E-bind (tick N t (b , tt)) (λ (o , q) → Dmap (o ∷_) (paddedReplyRun N ρ q)) ξ)
        (lookupᴰℚ-cong-P (entries (tick N t (b , tt))) (λ { (o , (b′ , tt)) →
          lookupᴰℚ-Dmap (o ∷_) (paddedReplyRun N ρ (b′ , tt)) ξ }))))))

next : Maybe Bool → Bool
next (just b) = b
next nothing = false

replySample : P.Calls (Tick S) Bool
replySample = P.call false tt λ _ → P.call true tt λ reply → P.ret (next reply)

false-branch-half : E (resourceResult M none tt replySample (initial M))
  (maybeℚ (λ where false → 1ℚ ; true → 0ℚ)) ≡ ½
false-branch-half = refl

true-branch-half : E (resourceResult M none tt replySample (initial M))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ ½
true-branch-half = refl

different-next-tasks : next (just false) ≢ next (just true)
different-next-tasks ()

adaptive : P.Calls (Tick S) Bool
adaptive = P.call false tt λ _ → P.call true tt λ reply →
  P.call (next reply) tt λ result → P.ret (next result)

consumer : P.Protocol (Tick S) Ωᴵ
consumer = record { St = ⊤ ; init = tt ; step = λ _ _ _ → P.mapᶜ (tt ,_) adaptive }

adaptive-results : finiteResult M adaptive (initial M) ≈Mℚ finiteResult N adaptive (initial N)
adaptive-results = padded-implies-finite-calls M N (initial M) (initial N) (λ ρ → padded-related ρ false) adaptive

native-adaptive-results : resourceResult M none tt adaptive (initial M)
  ≈Mℚ resourceResult N none tt adaptive (initial N)
native-adaptive-results = padded-implies-resource-calls M N (initial M) (initial N)
  (λ ρ → padded-related ρ false) none tt adaptive

adaptive-half : E (finiteResult M adaptive (initial M)) (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ ½
adaptive-half = refl

native-consumer-results : resourceResult M none tt (P.step consumer tt tt tt) (initial M)
  ≈Mℚ resourceResult N none tt (P.step consumer tt tt tt) (initial N)
native-consumer-results = padded-implies-resource-calls M N (initial M) (initial N)
  (λ ρ → padded-related ρ false) none tt (P.step consumer tt tt tt)

composed-consumer-results : runᵖ (consumer P.∘ᵖ resource M) ≈Mℚ runᵖ (consumer P.∘ᵖ resource N)
composed-consumer-results = padded-implies-consumers M N (λ ρ → padded-related ρ false) consumer

composed-consumer-half : E (runᵖ (consumer P.∘ᵖ resource M))
  (maybeℚ (λ where false → 0ℚ ; true → 1ℚ)) ≡ ½
composed-consumer-half = refl

with-failure : P.Calls (Tick S) Bool
with-failure = P.coin uniform-Bool λ where false → P.dead ; true → adaptive

failure-preserved : finiteResult M with-failure (initial M) ≈Mℚ finiteResult N with-failure (initial N)
failure-preserved = padded-implies-finite-calls M N (initial M) (initial N)
  (λ ρ → padded-related ρ false) with-failure

failure-half : E (finiteResult M with-failure (initial M)) (λ where nothing → 1ℚ ; (just _) → 0ℚ) ≡ ½
failure-half = refl

reverse-public : ∀ ρ → paddedReplyRun M ρ (initial M) ≈Mℚ paddedReplyRun N ρ (initial N)
reverse-public = finite-calls-implies-padded M N (initial M) (initial N)
  (padded-implies-finite-calls M N (initial M) (initial N) (λ ρ → padded-related ρ false))
