{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.Coherence where

open import Categories.Category.Monoidal.Bundle
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Commutative
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Iter.Transfer
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
open import CategoricalCrypto.Machine.Relational.Presentation.Composition
import CategoricalCrypto.Machine.Relational.Presentation.Kernel as Kernel
import CategoricalCrypto.Machine.Relational.Presentation.Positive as EP
import CategoricalCrypto.Machine.Relational.Presentation.Trace as Tr
import CategoricalCrypto.Machine.Relational.Presentation.Wiring as PW
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Pointwise as Point
import CategoricalCrypto.Machines.Positive.Base as Positive
import CategoricalCrypto.Machines.Positive.Bridge as Bridge
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Iface as I

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  module QG = MonoidalCategory (Positive.𝒢₊ᴹ 0ℓ)
  module Quotient = MonoidalCategory Model.𝔾₊
  variable A B C : Channel

module Proof {F : Initialized A B} {H : Initialized B C} (Q : Presentation H) (P : Presentation F) where
  module N = Kernel.Native Q P
  private
    RS SS X : Set
    RS = M.Machine.State (machine F)
    SS = M.Machine.State (machine H)
    X = Channel.outType B ⊎ Channel.inType B

  f : R.P.Machine (Channel.inType A ⊎ Channel.outType B) (Channel.outType A ⊎ Channel.inType B)
  f = R.unpack (EP.toPositive P)
  g : R.P.Machine (Channel.inType B ⊎ Channel.outType C) (Channel.outType B ⊎ Channel.inType C)
  g = R.unpack (EP.toPositive Q)
  native : R.P.Machine (Channel.inType A ⊎ Channel.outType C) (Channel.outType A ⊎ Channel.inType C)
  native = R.unpack (EP.toPositive (compose-presentation Q P))

  module L = Col.Loop N.EI N.EO X (Col.Sᴳ g f) (Col.kᴳ g f)

  k : (SS × RS) × X → (RS × SS) × N.NI
  k ((s , r) , inj₁ b) = (r , s) , inj₂ (inj₂ b)
  k ((s , r) , inj₂ b) = (r , s) , inj₁ (inj₂ b)

  m : (SS × RS) × N.EO → (RS × SS) × N.EO
  m ((s , r) , o) = (r , s) , o

  opaque
    unfolding _⊗₀_ EP.positive-step N.body

    internal : (z : (SS × RS) × X) → N.body (k z) ≈ₚ mapₚ (φ k m) (L.body z)
    internal ((s , r) , inj₁ b) = ≈sym (map-fuse (stepₚ P r (inj₂ b))
      (λ t → (s , proj₁ t) , Col.outᶠ (proj₂ t)) (φ k m) (N.routeP s) λ where
        (r′ , inj₁ a) → refl
        (r′ , inj₂ b′) → refl)
    internal ((s , r) , inj₂ b) = ≈sym (map-fuse (stepₚ Q s (inj₁ b))
      (λ t → (proj₁ t , r) , Col.outᵍ (proj₂ t)) (φ k m) (N.routeQ r) λ where
        (s′ , inj₁ b′) → refl
        (s′ , inj₂ c) → refl)

    external : (z : RS × SS) (i : N.EI)
      → N.body (z , N.entry i) ≈ₚ mapₚ (φ k m) (Col.kᴳ g f (swap z , inj₁ i))
    external (r , s) (inj₁ a) = ≈sym (map-fuse (stepₚ P r (inj₁ a))
      (λ t → (s , proj₁ t) , Col.outᶠ (proj₂ t)) (φ k m) (N.routeP s) λ where
        (r′ , inj₁ a′) → refl
        (r′ , inj₂ b) → refl)
    external (r , s) (inj₂ c) = ≈sym (map-fuse (stepₚ Q s (inj₂ c))
      (λ t → (proj₁ t , r) , Col.outᵍ (proj₂ t)) (φ k m) (N.routeQ r) λ where
        (s′ , inj₁ b) → refl
        (s′ , inj₂ c′) → refl)

  continuation : (w : (SS × RS) × (N.EO ⊎ X))
    → contᵢ N.body (φ k m w) ≈ₚ mapₚ m (contᵢ L.body w)
  continuation ((s , r) , inj₁ o) = ≈sym (>>=ₚ-identityˡ ((s , r) , o) _)
  continuation ((s , r) , inj₂ x) = iterₚ-transfer L.body N.body k m internal ((s , r) , x)

  opaque
    unfolding _⊗₀_ EP.positive-step Tr.trace-presentation Tr.input N.interpreted

    compiled-step : (z : RS × SS) (i : N.EI)
      → R.P.step native (z , i) ≈ₚ iterₚ N.body (z , N.entry i)
    compiled-step z (inj₁ a) = iterₚ-cong N.interpreted N.body N.body-agreement (z , N.entry (inj₁ a))
    compiled-step z (inj₂ c) = iterₚ-cong N.interpreted N.body N.body-agreement (z , N.entry (inj₂ c))

  step-square : (z : RS × SS) (i : N.EI)
    → R.P.step native (z , i) ≈ₚ mapₚ m (R.P.step L.tracedᴹ (swap z , i))
  step-square z i = compiled-step z i
    ⟨≈⟩ iterₚ-fix N.body (z , N.entry i)
    ⟨≈⟩ bindˣ (external z i)
    ⟨≈⟩ bind-map (Col.kᴳ g f (swap z , inj₁ i)) (φ k m) (contᵢ N.body)
    ⟨≈⟩ bindᶠ continuation
    ⟨≈⟩ ≈sym (map-bind (Col.kᴳ g f (swap z , inj₁ i)) (contᵢ L.body) m)
    ⟨≈⟩ map-arg m (≈sym (L.step-red (swap z) i))

  opaque
    unfolding Tr.trace-presentation pre-presentation PW.tensor-presentation PW.pair-presentation

    compiled-point : R.P.point (R.P.state native) tt ≈ₚ pairₚ (initialₚ P) (initialₚ Q)
    compiled-point = ≈refl

  point-square : mapₚ swap (R.P.point (Col.Sᴳ g f) tt) ≈ₚ R.P.point (R.P.state native) tt
  point-square = map-arg swap (Point.point-⊛ (R.P.state g) (R.P.state f) tt)
    ⟨≈⟩ map-bind (initialₚ Q) (λ s → mapₚ (s ,_) (initialₚ P)) swap
    ⟨≈⟩ bindᶠ (λ s → map-fuse (initialₚ P) (s ,_) swap (_, s) (λ _ → refl))
    ⟨≈⟩ ≈sym (>>=ₚ-comm (initialₚ P) (initialₚ Q))
    ⟨≈⟩ ≈sym compiled-point

  original-compose : native R.PS.≈ᴹ G.composeₚ g f
  original-compose = R.PS._○ᴹ_ (R.PS.≲⇒≈ᴹ˘ simulation)
    (R.PS._○ᴹ_ (R.PS.⟺ᴹ (Col.collapseᵀ g f))
      (R.PS._○ᴹ_ (Col.compose-raw≈∘ᴳ g f) (R.PS.⟺ᴹ (G.composeₚ-project g f))))
    where
    simulation : L.tracedᴹ R.PS.≲ native
    simulation = Point.simFn swap (λ { tt → point-square }) λ where
      ((s , r) , i) → ≈sym (step-square (r , s) i)

toPositive-compose : {F : Initialized A B} {H : Initialized B C} (Q : Presentation H) (P : Presentation F)
  → EP.toPositive (compose-presentation Q P) R.QS.≈ᴹ
      QG._∘_ {EP.interface A} {EP.interface B} {EP.interface C} (EP.toPositive Q) (EP.toPositive P)
toPositive-compose Q P = R.QS._○ᴹ_ (R.QS.⟺ᴹ (R.repack-unpack (EP.toPositive (compose-presentation Q P))))
  (R.QS._○ᴹ_ (R.repack-resp (Proof.original-compose Q P))
    (R.QS._○ᴹ_ (Bridge.repack-compose 0ℓ (Proof.g Q P) (Proof.f Q P))
      (R.QS._○ᴹ_ (G.compose₊-cong (R.repack-unpack (EP.toPositive Q)) (R.repack-unpack (EP.toPositive P)))
        (G.compose₊-project (EP.toPositive Q) (EP.toPositive P)))))

toQuotient-compose : {F : Initialized A B} {H : Initialized B C} (Q : Presentation H) (P : Presentation F)
  → EP.toQuotient (compose-presentation Q P) Quotient.≈ (EP.toQuotient Q Quotient.∘ EP.toQuotient P)
toQuotient-compose {A} {B} {C} Q P = Quotient.Equiv.trans
  (Model.pack-positive-resp {Channel.inType A I.⇿ Channel.outType A} {Channel.inType C I.⇿ Channel.outType C}
    (toPositive-compose Q P))
  (Model.pack-positive-compose {Channel.inType A I.⇿ Channel.outType A}
    {Channel.inType B I.⇿ Channel.outType B} {Channel.inType C I.⇿ Channel.outType C} (EP.toPositive Q) (EP.toPositive P))
