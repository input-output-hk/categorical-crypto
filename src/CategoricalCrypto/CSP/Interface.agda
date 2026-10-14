{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.CSP.Interface (Sort : Set) (Payload : Sort → Set) where

open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no)

-- Shapes retain tagged namespaces rather than doing arithmetic on Fin indices.
data Shape : Set where
  empty singleton : Shape
  _⊕_ : Shape → Shape → Shape

⟨_⟩ : Shape → Set
⟨ empty ⟩ = ⊥
⟨ singleton ⟩ = ⊤
⟨ s ⊕ t ⟩ = ⟨ s ⟩ ⊎ ⟨ t ⟩

enumerate : (s : Shape) → List ⟨ s ⟩
enumerate empty = []
enumerate singleton = tt ∷ []
enumerate (s ⊕ t) = map inj₁ (enumerate s) ++ map inj₂ (enumerate t)

enumerate-complete : ∀ s i → i ∈ enumerate s
enumerate-complete empty ()
enumerate-complete singleton tt = here refl
enumerate-complete (s ⊕ t) (inj₁ i) = ∈-++⁺ˡ (∈-map⁺ inj₁ (enumerate-complete s i))
enumerate-complete (s ⊕ t) (inj₂ i) = ∈-++⁺ʳ _ (∈-map⁺ inj₂ (enumerate-complete t i))

index-equality : (s : Shape) (i j : ⟨ s ⟩) → Dec (i ≡ j)
index-equality empty ()
index-equality singleton tt tt = yes refl
index-equality (s ⊕ t) (inj₁ i) (inj₁ j) with index-equality s i j
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })
index-equality (s ⊕ t) (inj₁ i) (inj₂ j) = no (λ ())
index-equality (s ⊕ t) (inj₂ i) (inj₁ j) = no (λ ())
index-equality (s ⊕ t) (inj₂ i) (inj₂ j) with index-equality t i j
... | yes refl = yes refl
... | no neq = no (λ { refl → neq refl })

data Polarity : Set where
  input output : Polarity

dual : Polarity → Polarity
dual input = output
dual output = input

dual-involutive : ∀ p → dual (dual p) ≡ p
dual-involutive input = refl
dual-involutive output = refl

record Port : Set where
  constructor port
  field sort : Sort; polarity : Polarity

record Interface : Set where
  constructor interface
  field shape : Shape; ports : ⟨ shape ⟩ → Port

open Port
open Interface

I : Interface
I = interface empty (λ ())

infixr 6 _⊗₀_
_⊗₀_ : Interface → Interface → Interface
A ⊗₀ B = interface (shape A ⊕ shape B) [ ports A , ports B ]′

Event : Interface → Set
Event A = Σ ⟨ shape A ⟩ (λ i → Payload (sort (ports A i)))

left-event : ∀ {A B} → Event A → Event (A ⊗₀ B)
left-event (p , x) = inj₁ p , x

right-event : ∀ {A B} → Event B → Event (A ⊗₀ B)
right-event (p , x) = inj₂ p , x

-- The endpoints remain disjoint even when their payload sorts are identical.
no-cross-port : ∀ {A B} (a : ⟨ shape A ⟩) (b : ⟨ shape B ⟩)
              → ¬ (inj₁ a ≡ inj₂ b)
no-cross-port a b ()
