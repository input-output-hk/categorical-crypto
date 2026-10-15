{-# OPTIONS --safe --without-K #-}

-- Unlike runFrom, a padded word retains the reply of every activation,
-- including hidden and disabled activations.
module CategoricalCrypto.TaskPIOA.AdaptiveFinite where

open import Class.DecEq
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.SSP.Dist.FiniteTesting as F
open import CategoricalCrypto.SSP.Dist.Kernel using (Oracle; ⟦_⟧; _·_; none)
import CategoricalCrypto.SSP.Dist.SchedulerInformation as Information
open import CategoricalCrypto.SSP.Iface using (unitᴵ; Ωᴵ)
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.SSPAdapter using
  (Tick; tickOracle; finite-dec; resource; native-samples)
open import CategoricalCrypto.TaskPIOA.Simulation using (Simulation; stateMap; tick-match)
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Product using (mapped-bind; map-cong)

paddedReplyRun : ∀ {S} (M : Automaton S) → Schedule S → State M
  → Dist-ℚ (List (Maybe (Output S)))
paddedReplyRun M = F.word (tick M)

private variable
  S : Signature
  X : Set

padded-word : ∀ (M : Automaton S) ρ q → paddedReplyRun M ρ q ≈Mℚ F.word (tick M) ρ q
padded-word M ρ q ξ = refl

simulation-implies-padded : ∀ {M N : Automaton S} (s : Simulation M N) ρ q
  → paddedReplyRun M ρ q ≈Mℚ paddedReplyRun N ρ (stateMap s q)
simulation-implies-padded s [] q ξ = refl
simulation-implies-padded {M = M} {N} s (t ∷ ρ) q =
  mapped-bind (map₂ (stateMap s)) (tick M t q) (tick N t (stateMap s q))
    (λ (o , q′) → Dmap (o ∷_) (paddedReplyRun M ρ q′))
    (λ (o , q′) → Dmap (o ∷_) (paddedReplyRun N ρ q′))
    (tick-match s q t) (λ (o , q′) → map-cong (o ∷_)
      (paddedReplyRun M ρ q′) (paddedReplyRun N ρ (stateMap s q′))
      (simulation-implies-padded s ρ q′))

finiteResult : (M : Automaton S) → P.Calls (Tick S) X → State M → Dist⊥ X
finiteResult M c q = Dmap (Maybe.map proj₁) (⟦ c ⟧ (tickOracle M) q)

padded-implies-finite-calls : ∀ (M N : Automaton S) q r
  → (∀ ρ → paddedReplyRun M ρ q ≈Mℚ paddedReplyRun N ρ r)
  → (c : P.Calls (Tick S) X) → finiteResult M c q ≈Mℚ finiteResult N c r
padded-implies-finite-calls {S} M N q r equal =
  Information.words-to-calls (DecEq._≟_ (DecEq-Maybe ⦃ finite-dec (outputs S) ⦄))
    (tick M) q (tick N) r equal

finite-calls-implies-padded : ∀ (M N : Automaton S) q r
  → (∀ {X} (c : P.Calls (Tick S) X) → finiteResult M c q ≈Mℚ finiteResult N c r)
  → ∀ ρ → paddedReplyRun M ρ q ≈Mℚ paddedReplyRun N ρ r
finite-calls-implies-padded M N q r equal ρ ξ = trans (padded-word M ρ q ξ)
  (trans (F.calls-to-fixed (tick M) q (tick N) r equal ρ ξ)
    (sym (padded-word N ρ r ξ)))

padded⇔finite-calls : ∀ (M N : Automaton S) q r
  → (∀ ρ → paddedReplyRun M ρ q ≈Mℚ paddedReplyRun N ρ r)
    ⇔ (∀ {X} (c : P.Calls (Tick S) X) → finiteResult M c q ≈Mℚ finiteResult N c r)
padded⇔finite-calls M N q r = mk⇔
  (λ equal {X} c → padded-implies-finite-calls M N q r equal c)
  (finite-calls-implies-padded M N q r)

resourceResult : ∀ {Y} (M : Automaton S) (O : Oracle unitᴵ Y) → Y
  → P.Calls (Tick S) X → State M → Dist⊥ X
resourceResult M O s c q = Dmap (Maybe.map proj₁) (⟦ c ⟧ (resource M · O) (q , s))

resource-result-agreement : ∀ {Y} (M : Automaton S) (O : Oracle unitᴵ Y) s
  (c : P.Calls (Tick S) X) q → resourceResult M O s c q ≈Mℚ finiteResult M c q
resource-result-agreement {S = S} M O s c q ξ = trans
  (sym (>>=ᴹ-identityˡ (q , s) (Information.observeOracle (resource M · O) c) ξ))
  (Information.sample-result {I = Tick S} {ρ = λ q′ → return-ℚ (q′ , s)}
    {O = tickOracle M} {O′ = resource M · O} (native-samples M O s) c q ξ)

padded-implies-resource-calls : ∀ {Y} (M N : Automaton S) q r
  → (∀ ρ → paddedReplyRun M ρ q ≈Mℚ paddedReplyRun N ρ r)
  → (O : Oracle unitᴵ Y) (s : Y) (c : P.Calls (Tick S) X)
  → resourceResult M O s c q ≈Mℚ resourceResult N O s c r
padded-implies-resource-calls M N q r equal O s c ξ =
  trans (resource-result-agreement M O s c q ξ)
    (trans (padded-implies-finite-calls M N q r equal c ξ)
      (sym (resource-result-agreement N O s c r ξ)))

consumer-kernel-agreement : (M : Automaton S) (D : P.Protocol (Tick S) Ωᴵ)
  → runᵖ (D P.∘ᵖ resource M) ≈Mℚ Dmap (Maybe.map proj₂)
    (resourceResult M none tt (P.step D (P.init D) tt tt) (initial M))
consumer-kernel-agreement M D ξ = trans (F.closed-compose-result D (resource M) ξ)
  (trans (lookupᴰℚ-Dmap (Maybe.map (proj₂ ∘ proj₁)) μ ξ)
    (trans (lookupᴰℚ-cong-P (entries μ) (λ where nothing → refl ; (just _) → refl))
      (sym (trans (lookupᴰℚ-Dmap (Maybe.map proj₂)
        (resourceResult M none tt c (initial M)) ξ)
        (lookupᴰℚ-Dmap (Maybe.map proj₁) μ (ξ ∘ Maybe.map proj₂))))))
  where
  c = P.step D (P.init D) tt tt
  μ = ⟦ c ⟧ (resource M · none) (initial M , tt)

padded-implies-consumers : (M N : Automaton S)
  → (∀ ρ → paddedReplyRun M ρ (initial M) ≈Mℚ paddedReplyRun N ρ (initial N))
  → (D : P.Protocol (Tick S) Ωᴵ)
  → runᵖ (D P.∘ᵖ resource M) ≈Mℚ runᵖ (D P.∘ᵖ resource N)
padded-implies-consumers M N equal D ξ = trans (consumer-kernel-agreement M D ξ)
  (trans (lookupᴰℚ-Dmap (Maybe.map proj₂) lhs ξ)
    (trans (padded-implies-resource-calls M N (initial M) (initial N) equal none tt c
      (ξ ∘ Maybe.map proj₂))
      (trans (sym (lookupᴰℚ-Dmap (Maybe.map proj₂) rhs ξ))
        (sym (consumer-kernel-agreement N D ξ)))))
  where
  c = P.step D (P.init D) tt tt
  lhs = resourceResult M none tt c (initial M)
  rhs = resourceResult N none tt c (initial N)
