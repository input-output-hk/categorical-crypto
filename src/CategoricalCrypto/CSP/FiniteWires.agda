{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.FiniteWires (Sort : Set) (Payload : Sort → Set) where

open import Data.List.Base
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload

open Interface
open Port

record PortIso (A B : Interface) : Set where
  constructor port-iso
  no-eta-equality
  field
    to : ⟨ shape A ⟩ → ⟨ shape B ⟩
    from : ⟨ shape B ⟩ → ⟨ shape A ⟩
    left : ∀ i → from (to i) ≡ i
    right : ∀ i → to (from i) ≡ i
    typed : ∀ i → ports A i ≡ ports B (to i)

port-id : ∀ A → PortIso A A
port-id A = port-iso (λ i → i) (λ i → i) (λ _ → refl) (λ _ → refl) (λ _ → refl)

port-inverse : ∀ {A B} → PortIso A B → PortIso B A
port-inverse {B = B} f = port-iso from to right left
  (λ i → trans (cong (ports B) (sym (right i))) (sym (typed (from i))))
  where open PortIso f

port-compose : ∀ {A B C} → PortIso B C → PortIso A B → PortIso A C
port-compose g f = port-iso (λ i → G.to (F.to i)) (λ i → F.from (G.from i))
  (λ i → trans (cong F.from (G.left (F.to i))) (F.left i))
  (λ i → trans (cong G.to (F.right (G.from i))) (G.right i))
  (λ i → trans (F.typed i) (G.typed (F.to i)))
  where
    module F = PortIso f
    module G = PortIso g

port-tensor : ∀ {A B C D} → PortIso A B → PortIso C D → PortIso (A ⊗₀ C) (B ⊗₀ D)
port-tensor f g = port-iso
  (λ { (inj₁ i) → inj₁ (F.to i) ; (inj₂ i) → inj₂ (G.to i) })
  (λ { (inj₁ i) → inj₁ (F.from i) ; (inj₂ i) → inj₂ (G.from i) })
  (λ { (inj₁ i) → cong inj₁ (F.left i) ; (inj₂ i) → cong inj₂ (G.left i) })
  (λ { (inj₁ i) → cong inj₁ (F.right i) ; (inj₂ i) → cong inj₂ (G.right i) })
  (λ { (inj₁ i) → F.typed i ; (inj₂ i) → G.typed i })
  where
    module F = PortIso f
    module G = PortIso g

wire : ∀ {A B} → PortIso A B → Network A B
wire {A} {B} f = mkNetwork (boxes empty (λ ())) empty (λ ()) (λ { (() , _) }) (λ { (() , _) })
  (map edge (enumerate (shape A))) typed-alias
  where
    open import Data.List.Membership.Propositional using (_∈_)
    module F = PortIso f
    Name : Set
    Name = ⟨ empty ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape B ⟩)
    edge : ⟨ shape A ⟩ → Name × Name
    edge i = inj₂ (inj₁ i) , inj₂ (inj₂ (F.to i))
    name-sort : Name → Sort
    name-sort = [ (λ ()) , [ (λ i → sort (ports A i)) , (λ i → sort (ports B i)) ]′ ]′
    typed-alias : ∀ {u v} → (u , v) ∈ map edge (enumerate (shape A)) → name-sort u ≡ name-sort v
    typed-alias member with ∈-map⁻ edge member
    ... | i , mem , refl = cong sort (F.typed i)

left-unitor : ∀ A → PortIso (I ⊗₀ A) A
left-unitor A = port-iso (λ { (inj₁ ()) ; (inj₂ i) → i }) inj₂
  (λ { (inj₁ ()) ; (inj₂ i) → refl }) (λ _ → refl)
  (λ { (inj₁ ()) ; (inj₂ i) → refl })

right-unitor : ∀ A → PortIso (A ⊗₀ I) A
right-unitor A = port-iso (λ { (inj₁ i) → i ; (inj₂ ()) }) inj₁
  (λ { (inj₁ i) → refl ; (inj₂ ()) }) (λ _ → refl)
  (λ { (inj₁ i) → refl ; (inj₂ ()) })

associator : ∀ A B C → PortIso ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
associator A B C = port-iso
  (λ { (inj₁ (inj₁ i)) → inj₁ i ; (inj₁ (inj₂ i)) → inj₂ (inj₁ i) ; (inj₂ i) → inj₂ (inj₂ i) })
  (λ { (inj₁ i) → inj₁ (inj₁ i) ; (inj₂ (inj₁ i)) → inj₁ (inj₂ i) ; (inj₂ (inj₂ i)) → inj₂ i })
  (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
  (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
  (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
