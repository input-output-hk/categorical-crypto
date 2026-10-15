{-# OPTIONS --safe --without-K --guardedness #-}

-- Normalize the actual G tensor to its state-preserving interleaving kernel.
-- This reuses the repository's existing pure-wire absorption calculus.
module CategoricalCrypto.Machines.Positive.Tensor where

open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import Level
import CategoricalCrypto.Machines.Pure as Pure
import CategoricalCrypto.Machines.Pointwise as Point
import CategoricalCrypto.Machines.Sandwich as Old
import CategoricalCrypto.UC.Machine.Behaviour.Congruence as Behaviour
import CategoricalCrypto.Machines.Positive.Pointwise as PositivePoint
import CategoricalCrypto.Machines.Positive.Feedback as Feedback
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Bridge as Bridge

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  variable A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ D⁺ D⁻ X Y X′ Y′ : Set

private
  absorbed : (p : R.P.Machine X Y) (i : X′ → X) (o : Y → Y′)
    → (Pure.pureᶠ o R.P.∘ᴹ (p R.P.∘ᴹ Pure.pureᶠ i)) R.PS.≈ᴹ Old.sandwichᴹ p i o
  absorbed p i o = R.PS._○ᴹ_
    (R.PMM.∘-resp-≈ R.PS.reflᴹ (R.PS.≲⇒≈ᴹ (R.PT.pure-∘ʳ (Point.K.pureᵏ i) p)))
    (R.PS._○ᴹ_ (R.PS.≲⇒≈ᴹ (R.PT.pure-∘ˡ (Point.K.pureᵏ o) _))
      (Old.squeeze p i o Point.V.Equiv.refl Point.V.Equiv.refl))

original-normal-form : (f : R.P.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
  (g : R.P.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
  → Old.sandwichᴹ (f R.PT.⊗ᵉ g) Pure.midfn Pure.midfn R.PS.≈ᴹ G.tensorₚ f g
original-normal-form f g = R.PS._○ᴹ_ (R.PS.⟺ᴹ (absorbed (f R.PT.⊗ᵉ g) Pure.midfn Pure.midfn))
  (R.PS._○ᴹ_ (R.PS.⟺ᴹ (R.PMM.∘-resp-≈ Pure.midᴹ-pure (R.PMM.∘-resp-≈ R.PS.reflᴹ Pure.midᴹ-pure)))
    (R.PS._○ᴹ_ (Behaviour.⊗₁ᴳ-raw f g) (R.PS.⟺ᴹ (G.tensorₚ-project f g))))

normal : R.Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺) → R.Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺)
  → R.Q.Machine ((A⁺ ⊎ C⁺) ⊎ (B⁻ ⊎ D⁻)) ((A⁻ ⊎ C⁻) ⊎ (B⁺ ⊎ D⁺))
normal f g = PositivePoint.sandwichᴹ (f R.QT.⊗ᵉ g) Pure.midfn Pure.midfn

private
  mapped-normal : (f : R.Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : R.Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
    → R.repack (Old.sandwichᴹ (R.unpack f R.PT.⊗ᵉ R.unpack g) Pure.midfn Pure.midfn) R.QS.≈ᴹ normal f g
  mapped-normal f g = R.QS._○ᴹ_ (Feedback.repack-sandwich (R.unpack f R.PT.⊗ᵉ R.unpack g) Pure.midfn Pure.midfn)
    (PositivePoint.sandwich-resp Pure.midfn Pure.midfn
      (R.QS._○ᴹ_ (R.repack-mealy-tensor (R.unpack f) (R.unpack g))
        (R.QT.⊗ᵉ-resp-≈ᴹ (R.repack-unpack f) (R.repack-unpack g))))

normal-form : (f : R.Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : R.Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
  → normal f g R.QS.≈ᴹ G.tensor₊ f g
normal-form f g = R.QS._○ᴹ_ (R.QS.⟺ᴹ (mapped-normal f g))
  (R.QS._○ᴹ_ (R.repack-resp (original-normal-form (R.unpack f) (R.unpack g)))
    (R.QS._○ᴹ_ (Bridge.repack-tensor 0ℓ (R.unpack f) (R.unpack g))
      (G.tensor₊-cong (R.repack-unpack f) (R.repack-unpack g))))

normal-form-projected : (f : R.Q.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)) (g : R.Q.Machine (C⁺ ⊎ D⁻) (C⁻ ⊎ D⁺))
  → normal f g R.QS.≈ᴹ G.QG._⊗₁_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} {D⁺ , D⁻} f g
normal-form-projected f g = R.QS._○ᴹ_ (normal-form f g) (G.tensor₊-project f g)
