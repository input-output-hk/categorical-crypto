{-# OPTIONS --safe --guardedness #-}

-- The finite native relay interpreter and the categorical Mealy trace agree
-- already at the original probabilistic equality, before forgetting weights.
module CategoricalCrypto.Machine.Relational.Presentation.Feedback where

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base using (id)
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Iter.Transfer
open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
import CategoricalCrypto.Machine.Relational.Presentation.Trace as Tr
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machines.Sandwich as Old
import CategoricalCrypto.Machines.Pointwise as Point
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Positive.Feedback as Fb
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Pointwise as PositivePoint
import CategoricalCrypto.Machines.Positive.Feedback.Model as PublicFeedback
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Iface as I

private
  module R = Re.At 0ℓ
  module T = MonoidalCategory Model.𝔾₊
  iface : Channel → I.Iface
  iface A = Channel.inType A I.⇿ Channel.outType A
  variable A B C : Channel

-- These are the existing Channel tensor constructors/destructors, used as
-- actual deterministic port relabellings.  Keeping them explicit avoids
-- assuming that the Channel seal computes in public theorem signatures.
tensor-input : {A B C : Channel}
  → (Channel.inType A ⊎ Channel.inType C) ⊎ (Channel.outType B ⊎ Channel.outType C)
  → Channel.inType (A ⊗₀ C) ⊎ Channel.outType (B ⊗₀ C)
tensor-input {A} {B} {C} (inj₁ i) = inj₁ (construct-⊗ {A} {C} {In} i)
tensor-input {A} {B} {C} (inj₂ i) = inj₂ (construct-⊗ {B} {C} {Out} i)

tensor-output : {A B C : Channel}
  → Channel.outType (A ⊗₀ C) ⊎ Channel.inType (B ⊗₀ C)
  → (Channel.outType A ⊎ Channel.outType C) ⊎ (Channel.inType B ⊎ Channel.inType C)
tensor-output {A} {B} {C} (inj₁ o) = inj₁ (destruct-⊗ {A} {C} {Out} o)
tensor-output {A} {B} {C} (inj₂ o) = inj₂ (destruct-⊗ {B} {C} {In} o)

tensor-positive : {F : Initialized (A ⊗₀ C) (B ⊗₀ C)} → Presentation F
  → R.Q.Machine ((Channel.inType A ⊎ Channel.inType C) ⊎ (Channel.outType B ⊎ Channel.outType C))
      ((Channel.outType A ⊎ Channel.outType C) ⊎ (Channel.inType B ⊎ Channel.inType C))
tensor-positive {A} {C} {B} P = PositivePoint.sandwichᴹ (EP.toPositive P)
  (tensor-input {A} {B} {C}) (tensor-output {A} {B} {C})

module Proof {F : Initialized (A ⊗₀ C) (B ⊗₀ C)} (P : Presentation F) where
  private
    S FI FO EI EO X : Set
    S = M.Machine.State (machine F)
    FI = (Channel.inType A ⊎ Channel.inType C) ⊎ (Channel.outType B ⊎ Channel.outType C)
    FO = (Channel.outType A ⊎ Channel.outType C) ⊎ (Channel.inType B ⊎ Channel.inType C)
    EI = Channel.inType A ⊎ Channel.outType B
    EO = Channel.outType A ⊎ Channel.inType B
    X = Channel.outType C ⊎ Channel.inType C

  opaque
    unfolding _⊗₀_

    f-step : S × FI → Dₚ (S × FO)
    f-step = EP.positive-step P

  f : R.P.Machine FI FO
  f = R.unpack (tensor-positive P)

  f-agreement : R.repack f R.QS.≈ᴹ tensor-positive P
  f-agreement = R.repack-unpack (tensor-positive P)

  native : R.P.Machine EI EO
  native = R.unpack (EP.toPositive (Tr.trace-presentation P))

  route : S × FO → S × (EO ⊎ FI)
  route (s , inj₁ (inj₁ a)) = s , inj₁ (inj₁ a)
  route (s , inj₁ (inj₂ c)) = s , inj₂ (inj₂ (inj₂ c))
  route (s , inj₂ (inj₁ b)) = s , inj₁ (inj₂ b)
  route (s , inj₂ (inj₂ c)) = s , inj₂ (inj₁ (inj₂ c))

  body : Body S FI EO
  body z = mapₚ route (R.P.step f z)

  module L = Col.Loop EI EO X (R.P.state f) (R.P.step (Old.sandwichᴹ f Fb.input Fb.output))

  k : S × X → S × FI
  k (s , x) = s , Fb.input (inj₂ x)

  opaque
    unfolding _⊗₀_ construct-⊗ destruct-⊗ f-step EP.positive-step Tr.body Tr.dispatch

    interpreted : Body S FI EO
    interpreted = Tr.body P

    normalization : (s : S) (i : FI) → f-step (s , i) ≈ₚ R.P.step f (s , i)
    normalization s (inj₁ i) = ≈sym
      (map-eq (stepₚ P s (inj₁ i)) (λ z → proj₁ z , tensor-output {A} {B} {C} (proj₂ z)) id
        (λ { (s′ , inj₁ o) → refl ; (s′ , inj₂ o) → refl })
      ⟨≈⟩ >>=ₚ-identityʳ (stepₚ P s (inj₁ i)))
    normalization s (inj₂ i) = ≈sym
      (map-eq (stepₚ P s (inj₂ i)) (λ z → proj₁ z , tensor-output {A} {B} {C} (proj₂ z)) id
        (λ { (s′ , inj₁ o) → refl ; (s′ , inj₂ o) → refl })
      ⟨≈⟩ >>=ₚ-identityʳ (stepₚ P s (inj₂ i)))

    body-agreement : (z : S × FI) → interpreted z ≈ₚ body z
    body-agreement (s , i) =
      map-eq (stepₚ P s i) (Tr.dispatch P) route
        (λ { (s′ , inj₁ (inj₁ a)) → refl
           ; (s′ , inj₁ (inj₂ c)) → refl
           ; (s′ , inj₂ (inj₁ b)) → refl
           ; (s′ , inj₂ (inj₂ c)) → refl })
      ⟨≈⟩ map-arg route (normalization s i)

  routes : (z : S × FO) → φ k id (proj₁ z , Fb.output (proj₂ z)) ≡ route z
  routes (s , inj₁ (inj₁ a)) = refl
  routes (s , inj₁ (inj₂ c)) = refl
  routes (s , inj₂ (inj₁ b)) = refl
  routes (s , inj₂ (inj₂ c)) = refl

  internal : (z : S × X) → body (k z) ≈ₚ mapₚ (φ k id) (L.body z)
  internal (s , x) = ≈sym (map-fuse (R.P.step f (s , Fb.input (inj₂ x)))
    (λ z → proj₁ z , Fb.output (proj₂ z)) (φ k id) route routes)

  external : (s : S) (i : EI)
    → body (s , Fb.input (inj₁ i)) ≈ₚ
        mapₚ (φ k id) (R.P.step (Old.sandwichᴹ f Fb.input Fb.output) (s , inj₁ i))
  external s i = ≈sym (map-fuse (R.P.step f (s , Fb.input (inj₁ i)))
    (λ z → proj₁ z , Fb.output (proj₂ z)) (φ k id) route routes)

  continuation : (w : S × (EO ⊎ X))
    → contᵢ body (φ k id w) ≈ₚ mapₚ id (contᵢ L.body w)
  continuation (s , inj₁ o) = ≈sym (>>=ₚ-identityˡ (s , o) _)
  continuation (s , inj₂ x) = iterₚ-transfer L.body body k id internal (s , x)

  opaque
    unfolding _⊗₀_ EP.positive-step Tr.trace-presentation Tr.input interpreted

    compiled-step : (s : S) (i : EI)
      → R.P.step native (s , i) ≈ₚ iterₚ body (s , Fb.input (inj₁ i))
    compiled-step s (inj₁ a) = iterₚ-cong interpreted body body-agreement (s , Fb.input (inj₁ (inj₁ a)))
    compiled-step s (inj₂ b) = iterₚ-cong interpreted body body-agreement (s , Fb.input (inj₁ (inj₂ b)))

  step-square : (s : S) (i : EI) → R.P.step native (s , i) ≈ₚ R.P.step L.tracedᴹ (s , i)
  step-square s i = compiled-step s i
    ⟨≈⟩ iterₚ-fix body (s , Fb.input (inj₁ i))
    ⟨≈⟩ bindˣ (external s i)
    ⟨≈⟩ bind-map (R.P.step (Old.sandwichᴹ f Fb.input Fb.output) (s , inj₁ i)) (φ k id) (contᵢ body)
    ⟨≈⟩ bindᶠ continuation
    ⟨≈⟩ ≈sym (map-bind (R.P.step (Old.sandwichᴹ f Fb.input Fb.output) (s , inj₁ i)) (contᵢ L.body) id)
    ⟨≈⟩ map-arg id (≈sym (L.step-red s i))
    ⟨≈⟩ >>=ₚ-identityʳ (R.P.step L.tracedᴹ (s , i))

  opaque
    unfolding Tr.trace-presentation

    point-square : mapₚ id (R.P.point (R.P.state native) tt) ≈ₚ R.P.point (R.P.state f) tt
    point-square = >>=ₚ-identityʳ (initialₚ P)

  opaque
    unfolding Fb.feedbackₚ

    original-trace : native R.PS.≈ᴹ Fb.feedbackₚ f
    original-trace = R.PS.≲⇒≈ᴹ (Point.simFn id (λ { tt → point-square }) λ where
      (s , i) → >>=ₚ-identityʳ (R.P.step native (s , i)) ⟨≈⟩ step-square s i)

opaque
  unfolding _⊗₀_

  toPositive-trace : {F : Initialized (A ⊗₀ C) (B ⊗₀ C)} (P : Presentation F)
    → EP.toPositive (Tr.trace-presentation P) R.QS.≈ᴹ Fb.feedback₊ (tensor-positive P)
  toPositive-trace P = R.QS._○ᴹ_ (R.QS.⟺ᴹ (R.repack-unpack (EP.toPositive (Tr.trace-presentation P))))
    (R.QS._○ᴹ_ (R.repack-resp (Proof.original-trace P))
      (R.QS._○ᴹ_ (Fb.repack-feedback (Proof.f P)) (Fb.feedback-resp (Proof.f-agreement P))))

toQuotient-trace : {F : Initialized (A ⊗₀ C) (B ⊗₀ C)} (P : Presentation F)
  → EP.toQuotient (Tr.trace-presentation P) T.≈
      PublicFeedback.feedback {iface A} {iface C} {iface B}
        (Model.pack-positive {iface A I.⊗ᴵ iface C} {iface B I.⊗ᴵ iface C} (tensor-positive P))
toQuotient-trace P = T.Equiv.trans (Model.pack-positive-resp (toPositive-trace P))
  (PublicFeedback.pack-feedback (tensor-positive P))
