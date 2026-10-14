{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Plugging (Sort : Set) (Payload : Sort → Set) where

open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload

open Interface
open Port
open Boxes renaming (shape to box-shape)

map-edge : ∀ {X Y : Set} → (X → Y) → X × X → Y × Y
map-edge f (u , v) = f u , f v

map-edge-typed : ∀ {X Y : Set} {sx : X → Sort} {sy : Y → Sort}
  (f : X → Y) (typed : ∀ x → sy (f x) ≡ sx x)
  (edges : List (X × X))
  → (∀ {u v} → (u , v) ∈ edges → sx u ≡ sx v)
  → ∀ {u v} → (u , v) ∈ map (map-edge f) edges → sy u ≡ sy v
map-edge-typed f typed edges proof member with ∈-map⁻ (map-edge f) member
... | (a , b) , mem , refl = trans (typed a) (trans (proof mem) (sym (typed b)))

module Compose {A B C : Interface} (F : Network A B) (G : Network B C) where
  module F = Network F
  module G = Network G
  module WF = Wiring F
  module WG = Wiring G

  private-shape : Shape
  private-shape = (F.private-shape ⊕ shape B) ⊕ G.private-shape

  private-sort : ⟨ private-shape ⟩ → Sort
  private-sort = [ [ F.private-sort , (λ i → sort (ports B i)) ]′ , G.private-sort ]′

  Name : Set
  Name = ⟨ private-shape ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape C ⟩)

  name-sort : Name → Sort
  name-sort = [ private-sort , [ (λ i → sort (ports A i)) , (λ i → sort (ports C i)) ]′ ]′

  left : WF.Name → Name
  left (inj₁ p) = inj₁ (inj₁ (inj₁ p))
  left (inj₂ (inj₁ a)) = inj₂ (inj₁ a)
  left (inj₂ (inj₂ b)) = inj₁ (inj₁ (inj₂ b))

  right : WG.Name → Name
  right (inj₁ p) = inj₁ (inj₂ p)
  right (inj₂ (inj₁ b)) = inj₁ (inj₁ (inj₂ b))
  right (inj₂ (inj₂ c)) = inj₂ (inj₂ c)

  left-type : ∀ n → name-sort (left n) ≡ WF.name-sort n
  left-type (inj₁ p) = refl
  left-type (inj₂ (inj₁ a)) = refl
  left-type (inj₂ (inj₂ b)) = refl

  right-type : ∀ n → name-sort (right n) ≡ WG.name-sort n
  right-type (inj₁ p) = refl
  right-type (inj₂ (inj₁ b)) = refl
  right-type (inj₂ (inj₂ c)) = refl

  components : Boxes
  components = boxes (box-shape F.components ⊕ box-shape G.components)
                     [ label F.components , label G.components ]′

  local-wire : Local components → Name
  local-wire (inj₁ k , p) = left (F.local-wire (k , p))
  local-wire (inj₂ k , p) = right (G.local-wire (k , p))

  opaque
    wire-type : ∀ kp → sort (ports (Component.boundary (label components (proj₁ kp))) (proj₂ kp))
                     ≡ name-sort (local-wire kp)
    wire-type (inj₁ k , p) = trans (F.wire-type (k , p)) (sym (left-type (F.local-wire (k , p))))
    wire-type (inj₂ k , p) = trans (G.wire-type (k , p)) (sym (right-type (G.local-wire (k , p))))

  aliases : List (Name × Name)
  aliases = map (map-edge left) F.aliases ++ map (map-edge right) G.aliases

  opaque
    alias-type : ∀ {u v} → (u , v) ∈ aliases → name-sort u ≡ name-sort v
    alias-type member = [ map-edge-typed left left-type F.aliases F.alias-type
                         , map-edge-typed right right-type G.aliases G.alias-type ]′
                         (∈-++⁻ (map (map-edge left) F.aliases) member)

-- Constructor applications avoid eta-expanding nested graph typing proofs.
-- See the same representation choice in CategoricalCrypto.Channel.Core.
infixr 9 _∘_
_∘_ : ∀ {A B C} → Network B C → Network A B → Network A C
G ∘ F = mkNetwork components private-shape private-sort local-wire wire-type aliases alias-type
  where open Compose F G

module Identity (A : Interface) where
  Name : Set
  Name = ⟨ empty ⟩ ⊎ (⟨ shape A ⟩ ⊎ ⟨ shape A ⟩)

  edge : ⟨ shape A ⟩ → Name × Name
  edge i = inj₂ (inj₁ i) , inj₂ (inj₂ i)

  aliases : List (Name × Name)
  aliases = map edge (enumerate (shape A))

  name-sort : Name → Sort
  name-sort = [ (λ ()) , [ (λ i → sort (ports A i)) , (λ i → sort (ports A i)) ]′ ]′

  alias-type : ∀ {u v} → (u , v) ∈ aliases → name-sort u ≡ name-sort v
  alias-type member with ∈-map⁻ edge member
  ... | i , mem , refl = refl

id : ∀ {A} → Network A A
id {A} = mkNetwork (boxes empty (λ ())) empty (λ ()) (λ { (() , _) }) (λ { (() , _) })
  (Identity.aliases A) (Identity.alias-type A)

module Tensor {A B C D : Interface} (F : Network A B) (G : Network C D) where
  module F = Network F
  module G = Network G
  module WF = Wiring F
  module WG = Wiring G

  private-shape : Shape
  private-shape = F.private-shape ⊕ G.private-shape

  private-sort : ⟨ private-shape ⟩ → Sort
  private-sort = [ F.private-sort , G.private-sort ]′

  Name : Set
  Name = ⟨ private-shape ⟩ ⊎ (⟨ shape (A ⊗₀ C) ⟩ ⊎ ⟨ shape (B ⊗₀ D) ⟩)

  name-sort : Name → Sort
  name-sort = [ private-sort , [ (λ i → sort (ports (A ⊗₀ C) i)) , (λ i → sort (ports (B ⊗₀ D) i)) ]′ ]′

  left : WF.Name → Name
  left (inj₁ p) = inj₁ (inj₁ p)
  left (inj₂ (inj₁ a)) = inj₂ (inj₁ (inj₁ a))
  left (inj₂ (inj₂ b)) = inj₂ (inj₂ (inj₁ b))

  right : WG.Name → Name
  right (inj₁ p) = inj₁ (inj₂ p)
  right (inj₂ (inj₁ c)) = inj₂ (inj₁ (inj₂ c))
  right (inj₂ (inj₂ d)) = inj₂ (inj₂ (inj₂ d))

  left-type : ∀ n → name-sort (left n) ≡ WF.name-sort n
  left-type (inj₁ p) = refl
  left-type (inj₂ (inj₁ a)) = refl
  left-type (inj₂ (inj₂ b)) = refl

  right-type : ∀ n → name-sort (right n) ≡ WG.name-sort n
  right-type (inj₁ p) = refl
  right-type (inj₂ (inj₁ c)) = refl
  right-type (inj₂ (inj₂ d)) = refl

  components : Boxes
  components = boxes (box-shape F.components ⊕ box-shape G.components)
                     [ label F.components , label G.components ]′

  local-wire : Local components → Name
  local-wire (inj₁ k , p) = left (F.local-wire (k , p))
  local-wire (inj₂ k , p) = right (G.local-wire (k , p))

  opaque
    wire-type : ∀ kp → sort (ports (Component.boundary (label components (proj₁ kp))) (proj₂ kp))
                     ≡ name-sort (local-wire kp)
    wire-type (inj₁ k , p) = trans (F.wire-type (k , p)) (sym (left-type (F.local-wire (k , p))))
    wire-type (inj₂ k , p) = trans (G.wire-type (k , p)) (sym (right-type (G.local-wire (k , p))))

  aliases : List (Name × Name)
  aliases = map (map-edge left) F.aliases ++ map (map-edge right) G.aliases

  opaque
    alias-type : ∀ {u v} → (u , v) ∈ aliases → name-sort u ≡ name-sort v
    alias-type member = [ map-edge-typed left left-type F.aliases F.alias-type
                         , map-edge-typed right right-type G.aliases G.alias-type ]′
                         (∈-++⁻ (map (map-edge left) F.aliases) member)

infixr 6 _⊗₁_
_⊗₁_ : ∀ {A B C D} → Network A B → Network C D → Network (A ⊗₀ C) (B ⊗₀ D)
F ⊗₁ G = mkNetwork components private-shape private-sort local-wire wire-type aliases alias-type
  where open Tensor F G
