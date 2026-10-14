{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.Interchange (Sort : Set) (Payload : Sort → Set) where

open import Categories.Category.Core
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.Congruence Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Wiring Sort Payload

module Exchange {A B C D E F : Interface}
  (a : Network A B) (b : Network C D) (c : Network B E) (d : Network D F) where
  module AB = Tensor a b
  module CD = Tensor c d
  module SO = Compose (a ⊗₁ b) (c ⊗₁ d)
  module AC = Compose a c
  module BD = Compose b d
  module TO = Tensor (c ∘ a) (d ∘ b)
  module WS = Wiring ((c ⊗₁ d) ∘ (a ⊗₁ b))
  module WT = Wiring ((c ∘ a) ⊗₁ (d ∘ b))
  module SP = Plug (a ⊗₁ b) (c ⊗₁ d)
  module SAB = Disjoint a b
  module SCD = Disjoint c d
  module TP = Disjoint (c ∘ a) (d ∘ b)
  module TAC = Plug a c
  module TBD = Plug b d

  forward-name : WS.Name → WT.Name
  forward-name (inj₁ (inj₁ (inj₁ (inj₁ p)))) = inj₁ (inj₁ (inj₁ (inj₁ p)))
  forward-name (inj₁ (inj₁ (inj₁ (inj₂ p)))) = inj₁ (inj₂ (inj₁ (inj₁ p)))
  forward-name (inj₁ (inj₁ (inj₂ (inj₁ q)))) = inj₁ (inj₁ (inj₁ (inj₂ q)))
  forward-name (inj₁ (inj₁ (inj₂ (inj₂ q)))) = inj₁ (inj₂ (inj₁ (inj₂ q)))
  forward-name (inj₁ (inj₂ (inj₁ p))) = inj₁ (inj₁ (inj₂ p))
  forward-name (inj₁ (inj₂ (inj₂ p))) = inj₁ (inj₂ (inj₂ p))
  forward-name (inj₂ e) = inj₂ e

  backward-name : WT.Name → WS.Name
  backward-name (inj₁ (inj₁ (inj₁ (inj₁ p)))) = inj₁ (inj₁ (inj₁ (inj₁ p)))
  backward-name (inj₁ (inj₂ (inj₁ (inj₁ p)))) = inj₁ (inj₁ (inj₁ (inj₂ p)))
  backward-name (inj₁ (inj₁ (inj₁ (inj₂ q)))) = inj₁ (inj₁ (inj₂ (inj₁ q)))
  backward-name (inj₁ (inj₂ (inj₁ (inj₂ q)))) = inj₁ (inj₁ (inj₂ (inj₂ q)))
  backward-name (inj₁ (inj₁ (inj₂ p))) = inj₁ (inj₂ (inj₁ p))
  backward-name (inj₁ (inj₂ (inj₂ p))) = inj₁ (inj₂ (inj₂ p))
  backward-name (inj₂ e) = inj₂ e

  forward-type : ∀ n → WS.name-sort n ≡ WT.name-sort (forward-name n)
  forward-type (inj₁ (inj₁ (inj₁ (inj₁ _)))) = refl
  forward-type (inj₁ (inj₁ (inj₁ (inj₂ _)))) = refl
  forward-type (inj₁ (inj₁ (inj₂ (inj₁ _)))) = refl
  forward-type (inj₁ (inj₁ (inj₂ (inj₂ _)))) = refl
  forward-type (inj₁ (inj₂ (inj₁ _))) = refl
  forward-type (inj₁ (inj₂ (inj₂ _))) = refl
  forward-type (inj₂ (inj₁ (inj₁ _))) = refl
  forward-type (inj₂ (inj₁ (inj₂ _))) = refl
  forward-type (inj₂ (inj₂ (inj₁ _))) = refl
  forward-type (inj₂ (inj₂ (inj₂ _))) = refl

  backward-type : ∀ n → WT.name-sort n ≡ WS.name-sort (backward-name n)
  backward-type (inj₁ (inj₁ (inj₁ (inj₁ _)))) = refl
  backward-type (inj₁ (inj₂ (inj₁ (inj₁ _)))) = refl
  backward-type (inj₁ (inj₁ (inj₁ (inj₂ _)))) = refl
  backward-type (inj₁ (inj₂ (inj₁ (inj₂ _)))) = refl
  backward-type (inj₁ (inj₁ (inj₂ _))) = refl
  backward-type (inj₁ (inj₂ (inj₂ _))) = refl
  backward-type (inj₂ (inj₁ (inj₁ _))) = refl
  backward-type (inj₂ (inj₁ (inj₂ _))) = refl
  backward-type (inj₂ (inj₂ (inj₁ _))) = refl
  backward-type (inj₂ (inj₂ (inj₂ _))) = refl

  forward-a : ∀ n → forward-name (SO.left (AB.left n)) ≡ TO.left (AC.left n)
  forward-a (inj₁ _) = refl
  forward-a (inj₂ (inj₁ _)) = refl
  forward-a (inj₂ (inj₂ _)) = refl
  forward-b : ∀ n → forward-name (SO.left (AB.right n)) ≡ TO.right (BD.left n)
  forward-b (inj₁ _) = refl
  forward-b (inj₂ (inj₁ _)) = refl
  forward-b (inj₂ (inj₂ _)) = refl
  forward-c : ∀ n → forward-name (SO.right (CD.left n)) ≡ TO.left (AC.right n)
  forward-c (inj₁ _) = refl
  forward-c (inj₂ (inj₁ _)) = refl
  forward-c (inj₂ (inj₂ _)) = refl
  forward-d : ∀ n → forward-name (SO.right (CD.right n)) ≡ TO.right (BD.right n)
  forward-d (inj₁ _) = refl
  forward-d (inj₂ (inj₁ _)) = refl
  forward-d (inj₂ (inj₂ _)) = refl

  backward-a : ∀ n → backward-name (TO.left (AC.left n)) ≡ SO.left (AB.left n)
  backward-a (inj₁ _) = refl
  backward-a (inj₂ (inj₁ _)) = refl
  backward-a (inj₂ (inj₂ _)) = refl
  backward-b : ∀ n → backward-name (TO.right (BD.left n)) ≡ SO.left (AB.right n)
  backward-b (inj₁ _) = refl
  backward-b (inj₂ (inj₁ _)) = refl
  backward-b (inj₂ (inj₂ _)) = refl
  backward-c : ∀ n → backward-name (TO.left (AC.right n)) ≡ SO.right (CD.left n)
  backward-c (inj₁ _) = refl
  backward-c (inj₂ (inj₁ _)) = refl
  backward-c (inj₂ (inj₂ _)) = refl
  backward-d : ∀ n → backward-name (TO.right (BD.right n)) ≡ SO.right (CD.right n)
  backward-d (inj₁ _) = refl
  backward-d (inj₂ (inj₁ _)) = refl
  backward-d (inj₂ (inj₂ _)) = refl

  forward-a-edge : ∀ {u v} → (u , v) ∈ Network.aliases a
    → WT.Connected (forward-name (SO.left (AB.left u))) (forward-name (SO.left (AB.left v)))
  forward-a-edge {u} {v} edge = WT.join (connection-equality (forward-a u))
    (WT.join (TP.left-connected (TAC.left-connected (Wiring.alias edge))) (WT.reverse (connection-equality (forward-a v))))
  forward-b-edge : ∀ {u v} → (u , v) ∈ Network.aliases b
    → WT.Connected (forward-name (SO.left (AB.right u))) (forward-name (SO.left (AB.right v)))
  forward-b-edge {u} {v} edge = WT.join (connection-equality (forward-b u))
    (WT.join (TP.right-connected (TBD.left-connected (Wiring.alias edge))) (WT.reverse (connection-equality (forward-b v))))
  forward-c-edge : ∀ {u v} → (u , v) ∈ Network.aliases c
    → WT.Connected (forward-name (SO.right (CD.left u))) (forward-name (SO.right (CD.left v)))
  forward-c-edge {u} {v} edge = WT.join (connection-equality (forward-c u))
    (WT.join (TP.left-connected (TAC.right-connected (Wiring.alias edge))) (WT.reverse (connection-equality (forward-c v))))
  forward-d-edge : ∀ {u v} → (u , v) ∈ Network.aliases d
    → WT.Connected (forward-name (SO.right (CD.right u))) (forward-name (SO.right (CD.right v)))
  forward-d-edge {u} {v} edge = WT.join (connection-equality (forward-d u))
    (WT.join (TP.right-connected (TBD.right-connected (Wiring.alias edge))) (WT.reverse (connection-equality (forward-d v))))

  forward-ab : ∀ {u v} → (u , v) ∈ AB.aliases
    → WT.Connected (forward-name (SO.left u)) (forward-name (SO.left v))
  forward-ab member with ∈-++⁻ (map (map-edge AB.left) (Network.aliases a)) member
  ... | inj₁ mem with ∈-map⁻ (map-edge AB.left) mem
  ... | (u , v) , edge , refl = forward-a-edge edge
  forward-ab member | inj₂ mem with ∈-map⁻ (map-edge AB.right) mem
  ... | (u , v) , edge , refl = forward-b-edge edge
  forward-cd : ∀ {u v} → (u , v) ∈ CD.aliases
    → WT.Connected (forward-name (SO.right u)) (forward-name (SO.right v))
  forward-cd member with ∈-++⁻ (map (map-edge CD.left) (Network.aliases c)) member
  ... | inj₁ mem with ∈-map⁻ (map-edge CD.left) mem
  ... | (u , v) , edge , refl = forward-c-edge edge
  forward-cd member | inj₂ mem with ∈-map⁻ (map-edge CD.right) mem
  ... | (u , v) , edge , refl = forward-d-edge edge

  forward-left : ∀ {u v} → (u , v) ∈ map (map-edge SO.left) AB.aliases → WT.Connected (forward-name u) (forward-name v)
  forward-left member with ∈-map⁻ (map-edge SO.left) member
  ... | (u , v) , edge , refl = forward-ab edge
  forward-right : ∀ {u v} → (u , v) ∈ map (map-edge SO.right) CD.aliases → WT.Connected (forward-name u) (forward-name v)
  forward-right member with ∈-map⁻ (map-edge SO.right) member
  ... | (u , v) , edge , refl = forward-cd edge
  forward-connected : ∀ {u v} → WS.Connected u v → WT.Connected (forward-name u) (forward-name v)
  forward-connected = map-connected forward-name (λ member → [ forward-left , forward-right ]′
    (∈-++⁻ (map (map-edge SO.left) AB.aliases) member))

  backward-a-edge : ∀ {u v} → (u , v) ∈ Network.aliases a
    → WS.Connected (backward-name (TO.left (AC.left u))) (backward-name (TO.left (AC.left v)))
  backward-a-edge {u} {v} edge = WS.join (connection-equality (backward-a u))
    (WS.join (SP.left-connected (SAB.left-connected (Wiring.alias edge))) (WS.reverse (connection-equality (backward-a v))))
  backward-b-edge : ∀ {u v} → (u , v) ∈ Network.aliases b
    → WS.Connected (backward-name (TO.right (BD.left u))) (backward-name (TO.right (BD.left v)))
  backward-b-edge {u} {v} edge = WS.join (connection-equality (backward-b u))
    (WS.join (SP.left-connected (SAB.right-connected (Wiring.alias edge))) (WS.reverse (connection-equality (backward-b v))))
  backward-c-edge : ∀ {u v} → (u , v) ∈ Network.aliases c
    → WS.Connected (backward-name (TO.left (AC.right u))) (backward-name (TO.left (AC.right v)))
  backward-c-edge {u} {v} edge = WS.join (connection-equality (backward-c u))
    (WS.join (SP.right-connected (SCD.left-connected (Wiring.alias edge))) (WS.reverse (connection-equality (backward-c v))))
  backward-d-edge : ∀ {u v} → (u , v) ∈ Network.aliases d
    → WS.Connected (backward-name (TO.right (BD.right u))) (backward-name (TO.right (BD.right v)))
  backward-d-edge {u} {v} edge = WS.join (connection-equality (backward-d u))
    (WS.join (SP.right-connected (SCD.right-connected (Wiring.alias edge))) (WS.reverse (connection-equality (backward-d v))))

  backward-ac : ∀ {u v} → (u , v) ∈ AC.aliases
    → WS.Connected (backward-name (TO.left u)) (backward-name (TO.left v))
  backward-ac member with ∈-++⁻ (map (map-edge AC.left) (Network.aliases a)) member
  ... | inj₁ mem with ∈-map⁻ (map-edge AC.left) mem
  ... | (u , v) , edge , refl = backward-a-edge edge
  backward-ac member | inj₂ mem with ∈-map⁻ (map-edge AC.right) mem
  ... | (u , v) , edge , refl = backward-c-edge edge
  backward-bd : ∀ {u v} → (u , v) ∈ BD.aliases
    → WS.Connected (backward-name (TO.right u)) (backward-name (TO.right v))
  backward-bd member with ∈-++⁻ (map (map-edge BD.left) (Network.aliases b)) member
  ... | inj₁ mem with ∈-map⁻ (map-edge BD.left) mem
  ... | (u , v) , edge , refl = backward-b-edge edge
  backward-bd member | inj₂ mem with ∈-map⁻ (map-edge BD.right) mem
  ... | (u , v) , edge , refl = backward-d-edge edge

  backward-left : ∀ {u v} → (u , v) ∈ map (map-edge TO.left) AC.aliases → WS.Connected (backward-name u) (backward-name v)
  backward-left member with ∈-map⁻ (map-edge TO.left) member
  ... | (u , v) , edge , refl = backward-ac edge
  backward-right : ∀ {u v} → (u , v) ∈ map (map-edge TO.right) BD.aliases → WS.Connected (backward-name u) (backward-name v)
  backward-right member with ∈-map⁻ (map-edge TO.right) member
  ... | (u , v) , edge , refl = backward-bd edge
  backward-connected : ∀ {u v} → WT.Connected u v → WS.Connected (backward-name u) (backward-name v)
  backward-connected = map-connected backward-name (λ member → [ backward-left , backward-right ]′
    (∈-++⁻ (map (map-edge TO.left) AC.aliases) member))

  names-left : ∀ n → backward-name (forward-name n) ≡ n
  names-left (inj₁ (inj₁ (inj₁ (inj₁ _)))) = refl
  names-left (inj₁ (inj₁ (inj₁ (inj₂ _)))) = refl
  names-left (inj₁ (inj₁ (inj₂ (inj₁ _)))) = refl
  names-left (inj₁ (inj₁ (inj₂ (inj₂ _)))) = refl
  names-left (inj₁ (inj₂ (inj₁ _))) = refl
  names-left (inj₁ (inj₂ (inj₂ _))) = refl
  names-left (inj₂ _) = refl
  names-right : ∀ n → forward-name (backward-name n) ≡ n
  names-right (inj₁ (inj₁ (inj₁ (inj₁ _)))) = refl
  names-right (inj₁ (inj₂ (inj₁ (inj₁ _)))) = refl
  names-right (inj₁ (inj₁ (inj₁ (inj₂ _)))) = refl
  names-right (inj₁ (inj₂ (inj₁ (inj₂ _)))) = refl
  names-right (inj₁ (inj₁ (inj₂ _))) = refl
  names-right (inj₁ (inj₂ (inj₂ _))) = refl
  names-right (inj₂ _) = refl

  forward : Embedding ((c ⊗₁ d) ∘ (a ⊗₁ b)) ((c ∘ a) ⊗₁ (d ∘ b))
  forward = record
    { box-map = λ { (inj₁ (inj₁ k)) → inj₁ (inj₁ k) ; (inj₁ (inj₂ k)) → inj₂ (inj₁ k) ; (inj₂ (inj₁ k)) → inj₁ (inj₂ k) ; (inj₂ (inj₂ k)) → inj₂ (inj₂ k) }
    ; box-label = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
    ; name-map = forward-name ; name-type = forward-type ; connected = forward-connected ; external = λ _ → WT.same
    ; local = λ { (inj₁ (inj₁ k)) p → connection-equality (forward-a (Network.local-wire a (k , p)))
                ; (inj₁ (inj₂ k)) p → connection-equality (forward-b (Network.local-wire b (k , p)))
                ; (inj₂ (inj₁ k)) p → connection-equality (forward-c (Network.local-wire c (k , p)))
                ; (inj₂ (inj₂ k)) p → connection-equality (forward-d (Network.local-wire d (k , p))) } }

  backward : Embedding ((c ∘ a) ⊗₁ (d ∘ b)) ((c ⊗₁ d) ∘ (a ⊗₁ b))
  backward = record
    { box-map = λ { (inj₁ (inj₁ k)) → inj₁ (inj₁ k) ; (inj₂ (inj₁ k)) → inj₁ (inj₂ k) ; (inj₁ (inj₂ k)) → inj₂ (inj₁ k) ; (inj₂ (inj₂ k)) → inj₂ (inj₂ k) }
    ; box-label = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
    ; name-map = backward-name ; name-type = backward-type ; connected = backward-connected ; external = λ _ → WS.same
    ; local = λ { (inj₁ (inj₁ k)) p → connection-equality (backward-a (Network.local-wire a (k , p)))
                ; (inj₂ (inj₁ k)) p → connection-equality (backward-b (Network.local-wire b (k , p)))
                ; (inj₁ (inj₂ k)) p → connection-equality (backward-c (Network.local-wire c (k , p)))
                ; (inj₂ (inj₂ k)) p → connection-equality (backward-d (Network.local-wire d (k , p))) } }

  plugging-tensor-interchange : ((c ⊗₁ d) ∘ (a ⊗₁ b)) ≅ ((c ∘ a) ⊗₁ (d ∘ b))
  plugging-tensor-interchange = record
    { forward = forward ; backward = backward
    ; boxes-left = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
    ; boxes-right = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
    ; names-left = λ n → connection-equality (names-left n) ; names-right = λ n → connection-equality (names-right n) }

private
  module Cat = Category OpenCSP

-- Keep process labels schematic when a concrete converter specializes this law.
opaque
  converter-adversarial-flattening : ∀ {A X Y X′ B}
    (f : Network A (X ⊗₀ B)) (g : Network A (Y ⊗₀ B)) (h : Network Y X)
    → f ≅ ((h ⊗₁ id {B}) ∘ g) → (a : Network X X′)
    → ((a ⊗₁ id {B}) ∘ f) ≅ (((a ∘ h) ⊗₁ id {B}) ∘ g)
  converter-adversarial-flattening {A} {X} {Y} {X′} {B} f g h flat a =
    let open Cat.HomReasoning in begin
    (a ⊗₁ id {B}) ∘ f
      ≈⟨ Cat.∘-resp-≈ʳ {A = A} {B = X ⊗₀ B} {C = X′ ⊗₀ B}
          {f = f} {h = (h ⊗₁ id {B}) ∘ g} {g = a ⊗₁ id {B}} flat ⟩
    (a ⊗₁ id {B}) ∘ ((h ⊗₁ id {B}) ∘ g)
      ≈⟨ Cat.sym-assoc {A = A} {B = Y ⊗₀ B} {C = X ⊗₀ B} {D = X′ ⊗₀ B}
          {f = g} {g = h ⊗₁ id {B}} {h = a ⊗₁ id {B}} ⟩
    ((a ⊗₁ id {B}) ∘ (h ⊗₁ id {B})) ∘ g
      ≈⟨ Cat.∘-resp-≈ˡ {A = A} {B = Y ⊗₀ B} {C = X′ ⊗₀ B}
          {f = (a ⊗₁ id {B}) ∘ (h ⊗₁ id {B})} {h = (a ∘ h) ⊗₁ id {B}} {g = g}
          tensor-factor ⟩
    ((a ∘ h) ⊗₁ id {B}) ∘ g ∎
    where
    tensor-factor : ((a ⊗₁ id {B}) ∘ (h ⊗₁ id {B})) ≅ ((a ∘ h) ⊗₁ id {B})
    tensor-factor = ≅-trans
      {F = (a ⊗₁ id {B}) ∘ (h ⊗₁ id {B})}
      {G = (a ∘ h) ⊗₁ (id {B} ∘ id {B})} {H = (a ∘ h) ⊗₁ id {B}}
      (Exchange.plugging-tensor-interchange h (id {B}) a (id {B}))
      (TensorIso.tensor-congruence {A = Y} {B = X′} {C = B} {D = B}
        {F = a ∘ h} {F′ = a ∘ h} {G = id {B} ∘ id {B}} {G′ = id {B}}
        (≅-refl {F = a ∘ h}) (Cat.identityˡ {A = B} {B = B} {f = id {B}}))
