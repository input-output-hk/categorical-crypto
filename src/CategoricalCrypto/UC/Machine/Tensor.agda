{-# OPTIONS --safe --without-K --guardedness #-}

-- The G tensor has no feedback: its two middle permutations can be absorbed
-- into the interface of a product-state machine.

open import Categories.Category.Monoidal.Bundle
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (onL-pt; onR-pt)
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Behaviour.Congruence using (⊗₁ᴳ-raw)

import Categories.Category.Construction.Kleisli.Discrete as KD
import CategoricalCrypto.Machines.Category as Cat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.UC.Machine.Tensor where

private
  module G = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module V = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module K = KD (Dₚ-DiscreteMonad {0ℓ})
  module MC = Core (𝒱ₚ 0ℓ)
  module C = Cat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module T = Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)
  variable A B C′ D : Iface

tensorᴹ : Proc A B → Proc C′ D → Proc (A ⊗ᴵ C′) (B ⊗ᴵ D)
tensorᴹ f g = sandwichᴹ (f T.⊗ᵉ g) midfn midfn

private
  absorbed : {X Y X′ Y′ : Set} (p : MC.Machine X Y) (i : X′ → X) (o : Y → Y′)
           → (pureᶠ o MC.∘ᴹ (p MC.∘ᴹ pureᶠ i)) S.≈ᴹ sandwichᴹ p i o
  absorbed p i o = C.∘ᴹ-resp-≈ᴹ S.reflᴹ (S.≲⇒≈ᴹ (T.pure-∘ʳ (K.pureᵏ i) p))
    S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ o) _)
    S.○ᴹ squeeze p i o V.Equiv.refl V.Equiv.refl

tensor-correct : (f : Proc A B) (g : Proc C′ D)
               → tensorᴹ f g S.≈ᴹ G._⊗₁_ {Pos A , Neg A} {Pos B , Neg B}
                   {Pos C′ , Neg C′} {Pos D , Neg D} f g
tensor-correct f g = S.⟺ᴹ (absorbed (f T.⊗ᵉ g) midfn midfn)
  S.○ᴹ S.⟺ᴹ (C.∘ᴹ-resp-≈ᴹ midᴹ-pure (C.∘ᴹ-resp-≈ᴹ S.reflᴹ midᴹ-pure))
  S.○ᴹ ⊗₁ᴳ-raw f g

tensor-stepˡ : (f : Proc A B) (g : Proc C′ D) (s : MC.St f) (t : MC.St g) (b : Neg B)
             → MC.step (tensorᴹ f g) ((s , t) , inj₂ (inj₁ b))
               ≈ₚ (MC.step f (s , inj₂ b) >>=ₚ λ r → returnₚ
                 ((proj₁ r , t) , midfn (inj₁ (proj₂ r))))
tensor-stepˡ f g s t b =
  bindˣ (tstep-inj₁ _ _ (s , t) (inj₂ b) ⟨≈⟩ bindˣ (onL-pt (MC.step f) s t (inj₂ b))
    ⟨≈⟩ >>=ₚ-assoc (MC.step f (s , inj₂ b)) _ _
    ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , t) , proj₂ r) _))
  ⟨≈⟩ >>=ₚ-assoc (MC.step f (s , inj₂ b)) _ _
  ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , t) , inj₁ (proj₂ r)) _)

tensor-stepʳ : (f : Proc A B) (g : Proc C′ D) (s : MC.St f) (t : MC.St g) (d : Neg D)
             → MC.step (tensorᴹ f g) ((s , t) , inj₂ (inj₂ d))
               ≈ₚ (MC.step g (t , inj₂ d) >>=ₚ λ r → returnₚ
                 ((s , proj₁ r) , midfn (inj₂ (proj₂ r))))
tensor-stepʳ f g s t d =
  bindˣ (tstep-inj₂ _ _ (s , t) (inj₂ d) ⟨≈⟩ bindˣ (onR-pt (MC.step g) s t (inj₂ d))
    ⟨≈⟩ >>=ₚ-assoc (MC.step g (t , inj₂ d)) _ _
    ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((s , proj₁ r) , proj₂ r) _))
  ⟨≈⟩ >>=ₚ-assoc (MC.step g (t , inj₂ d)) _ _
  ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((s , proj₁ r) , inj₂ (proj₂ r)) _)
