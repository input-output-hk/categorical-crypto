{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.Kernel where

open import Data.Product.Base
open import Data.Sum.Base
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation
import CategoricalCrypto.Machine.Relational.Presentation.Composition as Comp
import CategoricalCrypto.Machine.Relational.Presentation.Trace as Tr
import CategoricalCrypto.Machine.Relational.Presentation.Wiring as PW
import CategoricalCrypto.Machine.Relational.Wiring as W

private variable A B C : Channel

map-four : {X Y Z U V : Set} (d : Dₚ X) (f : X → Y) (g : Y → Z) (h : Z → U) (k : U → V) (l : X → V)
  → (∀ x → k (h (g (f x))) ≡ l x) → mapₚ k (mapₚ h (mapₚ g (mapₚ f d))) ≈ₚ mapₚ l d
map-four d f g h k l eq =
  map-arg k (map-arg h (map-map d f g))
  ⟨≈⟩ map-arg k (map-map d (g ∘′ f) h)
  ⟨≈⟩ map-fuse d (h ∘′ g ∘′ f) k l eq

module Native {R : Initialized A B} {S : Initialized B C} (Q : Presentation S) (P : Presentation R) where
  private
    RS SS : Set
    RS = M.Machine.State (machine R)
    SS = M.Machine.State (machine S)

  NI EI EO : Set
  NI = (Channel.inType A ⊎ Channel.inType B) ⊎ (Channel.outType C ⊎ Channel.outType B)
  EI = Channel.inType A ⊎ Channel.outType C
  EO = Channel.outType A ⊎ Channel.inType C

  routeP : SS → RS × (Channel.outType A ⊎ Channel.inType B) → (RS × SS) × (EO ⊎ NI)
  routeP s (r , inj₁ a) = (r , s) , inj₁ (inj₁ a)
  routeP s (r , inj₂ b) = (r , s) , inj₂ (inj₁ (inj₂ b))

  routeQ : RS → SS × (Channel.outType B ⊎ Channel.inType C) → (RS × SS) × (EO ⊎ NI)
  routeQ r (s , inj₁ b) = (r , s) , inj₂ (inj₂ (inj₂ b))
  routeQ r (s , inj₂ c) = (r , s) , inj₁ (inj₂ c)

  opaque
    unfolding _⊗₀_

    body : Body (RS × SS) NI EO
    body ((r , s) , inj₁ (inj₁ a)) = mapₚ (routeP s) (stepₚ P r (inj₁ a))
    body ((r , s) , inj₁ (inj₂ b)) = mapₚ (routeQ r) (stepₚ Q s (inj₁ b))
    body ((r , s) , inj₂ (inj₁ c)) = mapₚ (routeQ r) (stepₚ Q s (inj₂ c))
    body ((r , s) , inj₂ (inj₂ b)) = mapₚ (routeP s) (stepₚ P r (inj₂ b))

  entry : EI → NI
  entry (inj₁ a) = inj₁ (inj₁ a)
  entry (inj₂ c) = inj₂ (inj₁ c)

  pre : Presentation (W.modify {C = A ⊗₀ B} {D = C ⊗₀ B} (M.∘σ {A} {B} {C}) (R W.⊗₁ S))
  pre = Comp.pre-presentation Q P

  opaque
    unfolding _⊗₀_

    interpreted : Body (RS × SS) NI EO
    interpreted z = Tr.body pre z

  opaque
    unfolding _⊗₀_ destruct-⊗ construct-⊗ ⊗-sym ⊗-right-assoc ⊗-left-assoc
              ⊗-right-intro ⊗-ᵀ-distrib ⊗-ᵀ-factor ⊗-right-neutral ⊗-fusion ⊗-combine
              interpreted Comp.pre-presentation PW.tensor-presentation PW.pair-presentation PW.pair-step
              Tr.body Tr.dispatch body

    body-agreement : (z : (RS × SS) × NI) → interpreted z ≈ₚ body z
    body-agreement ((r , s) , inj₁ (inj₁ a)) =
      map-four (stepₚ P r (inj₁ a)) _ _ _ _ (routeP s) λ where
        (r′ , inj₁ a′) → refl
        (r′ , inj₂ b) → refl
    body-agreement ((r , s) , inj₁ (inj₂ b)) =
      map-four (stepₚ Q s (inj₁ b)) _ _ _ _ (routeQ r) λ where
        (s′ , inj₁ b′) → refl
        (s′ , inj₂ c) → refl
    body-agreement ((r , s) , inj₂ (inj₁ c)) =
      map-four (stepₚ Q s (inj₂ c)) _ _ _ _ (routeQ r) λ where
        (s′ , inj₁ b) → refl
        (s′ , inj₂ c′) → refl
    body-agreement ((r , s) , inj₂ (inj₂ b)) =
      map-four (stepₚ P r (inj₂ b)) _ _ _ _ (routeP s) λ where
        (r′ , inj₁ a) → refl
        (r′ , inj₂ b′) → refl
