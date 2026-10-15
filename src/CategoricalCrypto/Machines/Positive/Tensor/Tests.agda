{-# OPTIONS --safe --without-K --guardedness #-}

-- The actual public G tensor is activated on BOTH ports by an adaptive finite
-- experiment.  Independent nontrivial probabilistic initializers are sampled;
-- the experiment reads left and right and returns left AND NOT right.
module CategoricalCrypto.Machines.Positive.Tensor.Tests where

open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base
import Data.Unit.Polymorphic.Base as Unit
open import Data.Rational as ℚ using (0ℚ)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Paths
open import ProbabilisticLogic.Dp.Positive.Composition
open import ProbabilisticLogic.Dp.Positive.Monad
import ProbabilisticLogic.Dp.Positive.Examples as Coins
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ; indᵇ-nn)
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Strategy
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Model.Seal as Seal
import CategoricalCrypto.Machines.Pointwise as Point
import CategoricalCrypto.Machines.Pure as Pure
import CategoricalCrypto.Machines.Sandwich as Old
import CategoricalCrypto.Machines.Positive.Pointwise as PositivePoint
import CategoricalCrypto.Machines.Positive.Feedback as Feedback
import CategoricalCrypto.Machines.Positive.Tensor as Tensor
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Run as Run
import CategoricalCrypto.Machines.Positive.Run.Model as PublicRun
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Tests as Public

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  module T = MonoidalCategory Model.𝔾₊
  I O : Set
  I = (⊥ ⊎ ⊥) ⊎ (⊤ ⊎ ⊤)
  O = (⊥ ⊎ ⊥) ⊎ (Bool ⊎ Bool)
  f = Public.biased Coins.half
  g = Public.biased Coins.quarter
  normal = Old.sandwichᴹ (f R.PT.⊗ᵉ g) Pure.midfn Pure.midfn

small : R.P.Machine I O
small = R.P.mk (R.P.state (f R.PT.⊗ᵉ g)) λ where
  (_ , inj₁ (inj₁ ()))
  (_ , inj₁ (inj₂ ()))
  ((b , c) , inj₂ (inj₁ _)) → returnₚ ((b , c) , inj₂ (inj₁ b))
  ((b , c) , inj₂ (inj₂ _)) → returnₚ ((b , c) , inj₂ (inj₂ c))

private
  route-out : (Bool × Bool) × ((⊥ ⊎ Bool) ⊎ (⊥ ⊎ Bool)) → (Bool × Bool) × O
  route-out z = proj₁ z , Pure.midfn (proj₂ z)

  left : ∀ b c u → R.P.step normal ((b , c) , inj₂ (inj₁ u)) ≈ₚ returnₚ ((b , c) , inj₂ (inj₁ b))
  left b c u = map-arg route-out
    (Pure.tstep-inj₁ (R.P.onL (R.P.step f)) (R.P.onR (R.P.step g)) (b , c) (inj₂ u)
      ⟨≈⟩ bindˣ (Point.onL-pt (R.P.step f) b c (inj₂ u) ⟨≈⟩ >>=ₚ-identityˡ (b , inj₂ b) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₂ b) _)
    ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₁ (inj₂ b)) _

  right : ∀ b c u → R.P.step normal ((b , c) , inj₂ (inj₂ u)) ≈ₚ returnₚ ((b , c) , inj₂ (inj₂ c))
  right b c u = map-arg route-out
    (Pure.tstep-inj₂ (R.P.onL (R.P.step f)) (R.P.onR (R.P.step g)) (b , c) (inj₂ u)
      ⟨≈⟩ bindˣ (Point.onR-pt (R.P.step g) b c (inj₂ u) ⟨≈⟩ >>=ₚ-identityˡ (c , inj₂ c) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₂ c) _)
    ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₂ (inj₂ c)) _

  normal-small : normal R.PS.≈ᴹ small
  normal-small = R.PS.≲⇒≈ᴹ (Point.simFn (λ s → s) (λ _ → >>=ₚ-identityʳ _) λ where
    (_ , inj₁ (inj₁ ()))
    (_ , inj₁ (inj₂ ()))
    ((b , c) , inj₂ (inj₁ u)) → >>=ₚ-identityʳ _ ⟨≈⟩ left b c u
    ((b , c) , inj₂ (inj₂ u)) → >>=ₚ-identityʳ _ ⟨≈⟩ right b c u)

  fq = R.repack f
  gq = R.repack g
  actual = G.QG._⊗₁_ {Pos unitᴵ , Neg unitᴵ} {Pos UC.Ωᴵ , Neg UC.Ωᴵ}
    {Pos unitᴵ , Neg unitᴵ} {Pos UC.Ωᴵ , Neg UC.Ωᴵ} fq gq

  small-actual : R.repack small R.QS.≈ᴹ actual
  small-actual = R.QS._○ᴹ_ (R.repack-resp (R.PS.⟺ᴹ normal-small))
    (R.QS._○ᴹ_ (Feedback.repack-sandwich (f R.PT.⊗ᵉ g) Pure.midfn Pure.midfn)
      (R.QS._○ᴹ_ (PositivePoint.sandwich-resp Pure.midfn Pure.midfn (R.repack-mealy-tensor f g))
        (Tensor.normal-form-projected fq gq)))

read-left read-right : O → Bool
read-left (inj₁ (inj₁ ()))
read-left (inj₁ (inj₂ ()))
read-left (inj₂ (inj₁ b)) = b
read-left (inj₂ (inj₂ _)) = false
read-right (inj₁ (inj₁ ()))
read-right (inj₁ (inj₂ ()))
read-right (inj₂ (inj₁ _)) = false
read-right (inj₂ (inj₂ c)) = c

experiment : Strat I O
experiment = ask (inj₂ (inj₁ tt)) λ x → ask (inj₂ (inj₂ tt)) λ y → out (read-left x ∧ not (read-right y))

private
  event : Bool × Bool → Bool
  event (b , c) = b ∧ not c
  pair = Coins.half >>=ₚ λ b → Coins.quarter >>=ₚ λ c → returnₚ (b , c)

  run-law : Run.run (R.repack small) experiment ≈ₚ mapₚ event pair
  run-law = bindᶠ (λ (b , c) → >>=ₚ-identityˡ ((b , c) , inj₂ (inj₁ b)) _
      ⟨≈⟩ >>=ₚ-identityˡ ((b , c) , inj₂ (inj₂ c)) _)
    ⟨≈⟩ map-arg event (Point.point-⊛ (R.P.state f) (R.P.state g) Unit.tt)

  outcome : (b : Bool) → Positive (mapₚ event pair) b
  outcome true = map-path event (bind-path (Coins.half-support true)
    (bind-path (Coins.quarter-support false) (positive-return (true , false))))
  outcome false = map-path event (bind-path (Coins.half-support false)
    (bind-path (Coins.quarter-support true) (positive-return (false , true))))

  value : ∀ b → 0ℚ ℚ.< indᵇ b b
  value true = 0<1ℚ
  value false = 0<1ℚ

  small-may : (b : Bool) → PositiveTest (Run.run (R.repack small) experiment) (indᵇ b)
  small-may b = positive-test-cong (indᵇ-nn b) (≈sym run-law)
    (positive-witness (indᵇ b) (indᵇ-nn b) (outcome b) (value b))

tensor : Seal.ifaceᵒ (unitᴵ ⊗ᴵ unitᴵ) T.⇒ Seal.ifaceᵒ (UC.Ωᴵ ⊗ᴵ UC.Ωᴵ)
tensor = Model.tensor-at Public.half Public.quarter

tensor-may : (b : Bool) → PositiveTest (PublicRun.run tensor experiment) (indᵇ b)
tensor-may b = proj₁
  (≈₊-trans (Run.run-resp small-actual experiment)
    (≈₊-trans (≈₊-sym (PublicRun.pack-run actual experiment))
      (PublicRun.run-resp (Model.pack-positive-tensor fq gq) experiment)))
  (indᵇ b) (indᵇ-nn b) (small-may b)
