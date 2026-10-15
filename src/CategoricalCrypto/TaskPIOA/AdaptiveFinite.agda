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
open import CategoricalCrypto.SSP.Iface using (unitᴵ; Ωᴵ)
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.SSPAdapter using
  (Tick; tickOracle; finite-dec; resource; all-calls-agreement)
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind)
open import ProbabilisticLogic.Distribution.RationalDist.Partial

paddedReplyRun : ∀ {S} (M : Automaton S) → Schedule S → State M
  → Dist-ℚ (List (Maybe (Output S)))
paddedReplyRun M [] q = return-ℚ []
paddedReplyRun M (t ∷ ρ) q = tick M t q >>=ᴹ λ (o , q′) →
  Dmap (o ∷_) (paddedReplyRun M ρ q′)

private variable
  S : Signature
  X : Set

padded-word : ∀ (M : Automaton S) ρ q → paddedReplyRun M ρ q ≈Mℚ F.word (tick M) ρ q
padded-word M [] q ξ = refl
padded-word M (t ∷ ρ) q ξ = trans
  (E-bind (tick M t q) (λ (o , q′) → Dmap (o ∷_) (paddedReplyRun M ρ q′)) ξ)
  (trans (lookupᴰℚ-cong-P (entries (tick M t q)) (λ { (o , q′) →
    trans (lookupᴰℚ-Dmap (o ∷_) (paddedReplyRun M ρ q′) ξ)
      (trans (padded-word M ρ q′ (ξ ∘ (o ∷_)))
        (sym (lookupᴰℚ-Dmap (o ∷_) (F.word (tick M) ρ q′) ξ))) }))
    (sym (E-bind (tick M t q) (λ (o , q′) → Dmap (o ∷_) (F.word (tick M) ρ q′)) ξ)))

finiteResult : (M : Automaton S) → P.Calls (Tick S) X → State M → Dist⊥ X
finiteResult M c q = Dmap (Maybe.map proj₁) (⟦ c ⟧ (tickOracle M) q)

padded-implies-finite-calls : ∀ (M N : Automaton S) q r
  → (∀ ρ → paddedReplyRun M ρ q ≈Mℚ paddedReplyRun N ρ r)
  → (c : P.Calls (Tick S) X) → finiteResult M c q ≈Mℚ finiteResult N c r
padded-implies-finite-calls {S} M N q r equal c =
  Proof.fixed-to-calls (tick M) q (tick N) r fixed c
  where
  module Proof = F.Cylinders (DecEq._≟_ (DecEq-Maybe ⦃ finite-dec (outputs S) ⦄))
  fixed : ∀ ρ → F.word (tick M) ρ q ≈Mℚ F.word (tick N) ρ r
  fixed ρ ξ = trans (sym (padded-word M ρ q ξ))
    (trans (equal ρ ξ) (padded-word N ρ r ξ))

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
resource-result-agreement {Y = Y} M O s c q ξ = trans
  (lookupᴰℚ-Dmap (Maybe.map proj₁) native ξ)
  (trans (sym (>>=ᴹ-identityˡ (q , s) (⟦ c ⟧ (resource M · O)) (F.lift ξ)))
    (trans (all-calls-agreement M O s c q (F.lift ξ))
      (trans (E-bind source (kmaybe embed) (F.lift ξ))
        (trans (lookupᴰℚ-cong-P (entries source) point)
          (sym (lookupᴰℚ-Dmap (Maybe.map proj₁) source ξ))))))
  where
  native = ⟦ c ⟧ (resource M · O) (q , s)
  source = ⟦ c ⟧ (tickOracle M) q
  embed = λ p → return-ℚ (proj₂ p , s) >>=ᴹ λ u → return⊥ (proj₁ p , u)
  point : ∀ p → E (kmaybe embed p) (F.lift ξ) ≡ F.lift ξ p
  point nothing = lookupᴰℚ-return nothing (F.lift {Q = State M × Y} ξ)
  point (just (x , q′)) = trans
    (>>=ᴹ-identityˡ (q′ , s) (λ u → return⊥ (x , u)) (F.lift ξ))
    (lookupᴰℚ-return (just (x , (q′ , s))) (F.lift ξ))

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
