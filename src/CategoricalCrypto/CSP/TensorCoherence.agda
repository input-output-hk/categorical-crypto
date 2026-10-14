{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.CSP.TensorCoherence (Sort : Set) (Payload : Sort → Set) where

import Categories.Morphism as Morphism
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Relation.Binary.PropositionalEquality hiding (naturality)

open import CategoricalCrypto.CSP.Category Sort Payload
open import CategoricalCrypto.CSP.Congruence Sort Payload
open import CategoricalCrypto.CSP.FiniteWires Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Plugging Sort Payload
open import CategoricalCrypto.CSP.Reboundary Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.WireLaws Sort Payload
open import CategoricalCrypto.CSP.Wiring Sort Payload

module Edges {A B : Interface} (N : Network A B) where
  module W = Wiring N

  mapped : ∀ {X Y : Set} (edges : List (X × X)) (f : X → Y) (g : Y → W.Name)
    → (∀ {u v} → (u , v) ∈ edges → W.Connected (g (f u)) (g (f v)))
    → ∀ {u v} → (u , v) ∈ map (map-edge f) edges → W.Connected (g u) (g v)
  mapped edges f g proof member with ∈-map⁻ (map-edge f) member
  ... | (u , v) , edge , refl = proof edge

  appended : ∀ {X : Set} (xs ys : List (X × X)) (f : X → W.Name)
    → (∀ {u v} → (u , v) ∈ xs → W.Connected (f u) (f v))
    → (∀ {u v} → (u , v) ∈ ys → W.Connected (f u) (f v))
    → ∀ {u v} → (u , v) ∈ xs ++ ys → W.Connected (f u) (f v)
  appended xs ys f left right member = [ left , right ]′ (∈-++⁻ xs member)

  aligned : ∀ {X : Set} (f g : X → W.Name) → (∀ n → f n ≡ g n)
    → ∀ {u v} → W.Connected (g u) (g v) → W.Connected (f u) (f v)
  aligned f g equal {u} {v} proof = W.join (connection-equality (equal u))
    (W.join proof (W.reverse (connection-equality (equal v))))

module Associate {A B C D E F : Interface}
  (f : Network A B) (g : Network C D) (h : Network E F) where
  module SI = Tensor f g
  module SO = Tensor (f ⊗₁ g) h
  module TI = Tensor g h
  module TO = Tensor f (g ⊗₁ h)
  module SR = Relabel (port-id ((A ⊗₀ C) ⊗₀ E)) (associator B D F) ((f ⊗₁ g) ⊗₁ h)
  module TR = Relabel (port-inverse (associator A C E)) (port-id (B ⊗₀ (D ⊗₀ F))) (f ⊗₁ (g ⊗₁ h))
  module S = Wiring SR.rewire
  module T = Wiring TR.rewire
  module SE = Edges SR.rewire
  module TE = Edges TR.rewire

  forward-name : S.Name → T.Name
  forward-name (inj₁ (inj₁ (inj₁ p))) = inj₁ (inj₁ p)
  forward-name (inj₁ (inj₁ (inj₂ p))) = inj₁ (inj₂ (inj₁ p))
  forward-name (inj₁ (inj₂ p)) = inj₁ (inj₂ (inj₂ p))
  forward-name (inj₂ e) = inj₂ e
  backward-name : T.Name → S.Name
  backward-name (inj₁ (inj₁ p)) = inj₁ (inj₁ (inj₁ p))
  backward-name (inj₁ (inj₂ (inj₁ p))) = inj₁ (inj₁ (inj₂ p))
  backward-name (inj₁ (inj₂ (inj₂ p))) = inj₁ (inj₂ p)
  backward-name (inj₂ e) = inj₂ e

  forward-type : ∀ n → S.name-sort n ≡ T.name-sort (forward-name n)
  forward-type (inj₁ (inj₁ (inj₁ _))) = refl
  forward-type (inj₁ (inj₁ (inj₂ _))) = refl
  forward-type (inj₁ (inj₂ _)) = refl
  forward-type (inj₂ (inj₁ (inj₁ (inj₁ _)))) = refl
  forward-type (inj₂ (inj₁ (inj₁ (inj₂ _)))) = refl
  forward-type (inj₂ (inj₁ (inj₂ _))) = refl
  forward-type (inj₂ (inj₂ (inj₁ _))) = refl
  forward-type (inj₂ (inj₂ (inj₂ (inj₁ _)))) = refl
  forward-type (inj₂ (inj₂ (inj₂ (inj₂ _)))) = refl
  backward-type : ∀ n → T.name-sort n ≡ S.name-sort (backward-name n)
  backward-type (inj₁ (inj₁ _)) = refl
  backward-type (inj₁ (inj₂ (inj₁ _))) = refl
  backward-type (inj₁ (inj₂ (inj₂ _))) = refl
  backward-type (inj₂ (inj₁ (inj₁ (inj₁ _)))) = refl
  backward-type (inj₂ (inj₁ (inj₁ (inj₂ _)))) = refl
  backward-type (inj₂ (inj₁ (inj₂ _))) = refl
  backward-type (inj₂ (inj₂ (inj₁ _))) = refl
  backward-type (inj₂ (inj₂ (inj₂ (inj₁ _)))) = refl
  backward-type (inj₂ (inj₂ (inj₂ (inj₂ _)))) = refl

  sf : Wiring.Name f → S.Name
  sf = λ n → SR.rename (SO.left (SI.left n))
  sg : Wiring.Name g → S.Name
  sg = λ n → SR.rename (SO.left (SI.right n))
  sh : Wiring.Name h → S.Name
  sh = λ n → SR.rename (SO.right n)
  tf : Wiring.Name f → T.Name
  tf = λ n → TR.rename (TO.left n)
  tg : Wiring.Name g → T.Name
  tg = λ n → TR.rename (TO.right (TI.left n))
  th : Wiring.Name h → T.Name
  th = λ n → TR.rename (TO.right (TI.right n))

  forward-f : ∀ n → forward-name (sf n) ≡ tf n
  forward-f (inj₁ _) = refl
  forward-f (inj₂ (inj₁ _)) = refl
  forward-f (inj₂ (inj₂ _)) = refl
  forward-g : ∀ n → forward-name (sg n) ≡ tg n
  forward-g (inj₁ _) = refl
  forward-g (inj₂ (inj₁ _)) = refl
  forward-g (inj₂ (inj₂ _)) = refl
  forward-h : ∀ n → forward-name (sh n) ≡ th n
  forward-h (inj₁ _) = refl
  forward-h (inj₂ (inj₁ _)) = refl
  forward-h (inj₂ (inj₂ _)) = refl
  backward-f : ∀ n → backward-name (tf n) ≡ sf n
  backward-f (inj₁ _) = refl
  backward-f (inj₂ (inj₁ _)) = refl
  backward-f (inj₂ (inj₂ _)) = refl
  backward-g : ∀ n → backward-name (tg n) ≡ sg n
  backward-g (inj₁ _) = refl
  backward-g (inj₂ (inj₁ _)) = refl
  backward-g (inj₂ (inj₂ _)) = refl
  backward-h : ∀ n → backward-name (th n) ≡ sh n
  backward-h (inj₁ _) = refl
  backward-h (inj₂ (inj₁ _)) = refl
  backward-h (inj₂ (inj₂ _)) = refl

  sf-edge : ∀ {u v} → (u , v) ∈ Network.aliases f → S.Connected (sf u) (sf v)
  sf-edge edge = S.alias (∈-map⁺ (map-edge SR.rename) (∈-++⁺ˡ
    (∈-map⁺ (map-edge SO.left) (∈-++⁺ˡ (∈-map⁺ (map-edge SI.left) edge)))))
  sg-edge : ∀ {u v} → (u , v) ∈ Network.aliases g → S.Connected (sg u) (sg v)
  sg-edge edge = S.alias (∈-map⁺ (map-edge SR.rename) (∈-++⁺ˡ
    (∈-map⁺ (map-edge SO.left) (∈-++⁺ʳ (map (map-edge SI.left) (Network.aliases f))
      (∈-map⁺ (map-edge SI.right) edge)))))
  sh-edge : ∀ {u v} → (u , v) ∈ Network.aliases h → S.Connected (sh u) (sh v)
  sh-edge edge = S.alias (∈-map⁺ (map-edge SR.rename) (∈-++⁺ʳ _ (∈-map⁺ (map-edge SO.right) edge)))
  tf-edge : ∀ {u v} → (u , v) ∈ Network.aliases f → T.Connected (tf u) (tf v)
  tf-edge edge = T.alias (∈-map⁺ (map-edge TR.rename) (∈-++⁺ˡ (∈-map⁺ (map-edge TO.left) edge)))
  tg-edge : ∀ {u v} → (u , v) ∈ Network.aliases g → T.Connected (tg u) (tg v)
  tg-edge edge = T.alias (∈-map⁺ (map-edge TR.rename) (∈-++⁺ʳ _
    (∈-map⁺ (map-edge TO.right) (∈-++⁺ˡ (∈-map⁺ (map-edge TI.left) edge)))))
  th-edge : ∀ {u v} → (u , v) ∈ Network.aliases h → T.Connected (th u) (th v)
  th-edge edge = T.alias (∈-map⁺ (map-edge TR.rename) (∈-++⁺ʳ (map (map-edge TO.left) (Network.aliases f))
    (∈-map⁺ (map-edge TO.right) (∈-++⁺ʳ (map (map-edge TI.left) (Network.aliases g))
      (∈-map⁺ (map-edge TI.right) edge)))))

  forward-connected : ∀ {u v} → S.Connected u v → T.Connected (forward-name u) (forward-name v)
  forward-connected = map-connected forward-name
    (TE.mapped SO.aliases SR.rename forward-name
      (TE.appended _ _ (λ n → forward-name (SR.rename n))
        (TE.mapped SI.aliases SO.left (λ n → forward-name (SR.rename n))
          (TE.appended _ _ (λ n → forward-name (SR.rename (SO.left n)))
            (TE.mapped _ SI.left (λ n → forward-name (SR.rename (SO.left n)))
              (λ edge → TE.aligned _ tf forward-f (tf-edge edge)))
            (TE.mapped _ SI.right (λ n → forward-name (SR.rename (SO.left n)))
              (λ edge → TE.aligned _ tg forward-g (tg-edge edge)))))
        (TE.mapped _ SO.right (λ n → forward-name (SR.rename n))
          (λ edge → TE.aligned _ th forward-h (th-edge edge)))))
  backward-connected : ∀ {u v} → T.Connected u v → S.Connected (backward-name u) (backward-name v)
  backward-connected = map-connected backward-name
    (SE.mapped TO.aliases TR.rename backward-name
      (SE.appended _ _ (λ n → backward-name (TR.rename n))
        (SE.mapped _ TO.left (λ n → backward-name (TR.rename n))
          (λ edge → SE.aligned _ sf backward-f (sf-edge edge)))
        (SE.mapped TI.aliases TO.right (λ n → backward-name (TR.rename n))
          (SE.appended _ _ (λ n → backward-name (TR.rename (TO.right n)))
            (SE.mapped _ TI.left (λ n → backward-name (TR.rename (TO.right n)))
              (λ edge → SE.aligned _ sg backward-g (sg-edge edge)))
            (SE.mapped _ TI.right (λ n → backward-name (TR.rename (TO.right n)))
              (λ edge → SE.aligned _ sh backward-h (sh-edge edge)))))))

  opaque
    retag : SR.rewire ≅ TR.rewire
    retag = record
      { forward = record
          { box-map = λ { (inj₁ (inj₁ k)) → inj₁ k ; (inj₁ (inj₂ k)) → inj₂ (inj₁ k) ; (inj₂ k) → inj₂ (inj₂ k) }
          ; box-label = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl }
          ; name-map = forward-name ; name-type = forward-type ; connected = forward-connected
          ; external = λ _ → T.same
          ; local = λ { (inj₁ (inj₁ k)) p → connection-equality (forward-f (Network.local-wire f (k , p)))
                      ; (inj₁ (inj₂ k)) p → connection-equality (forward-g (Network.local-wire g (k , p)))
                      ; (inj₂ k) p → connection-equality (forward-h (Network.local-wire h (k , p))) } }
      ; backward = record
          { box-map = λ { (inj₁ k) → inj₁ (inj₁ k) ; (inj₂ (inj₁ k)) → inj₁ (inj₂ k) ; (inj₂ (inj₂ k)) → inj₂ k }
          ; box-label = λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
          ; name-map = backward-name ; name-type = backward-type ; connected = backward-connected
          ; external = λ _ → S.same
          ; local = λ { (inj₁ k) p → connection-equality (backward-f (Network.local-wire f (k , p)))
                      ; (inj₂ (inj₁ k)) p → connection-equality (backward-g (Network.local-wire g (k , p)))
                      ; (inj₂ (inj₂ k)) p → connection-equality (backward-h (Network.local-wire h (k , p))) } }
      ; boxes-left = λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl }
      ; boxes-right = λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl }
      ; names-left = λ { (inj₁ (inj₁ (inj₁ _))) → S.same ; (inj₁ (inj₁ (inj₂ _))) → S.same
                       ; (inj₁ (inj₂ _)) → S.same ; (inj₂ _) → S.same }
      ; names-right = λ { (inj₁ (inj₁ _)) → T.same ; (inj₁ (inj₂ (inj₁ _))) → T.same
                        ; (inj₁ (inj₂ (inj₂ _))) → T.same ; (inj₂ _) → T.same } }

  opaque
    naturality : (wire (associator B D F) ∘ ((f ⊗₁ g) ⊗₁ h))
      ≅ ((f ⊗₁ (g ⊗₁ h)) ∘ wire (associator A C E))
    naturality = WireSquare.commute
      (associator A C E) (associator B D F) ((f ⊗₁ g) ⊗₁ h) (f ⊗₁ (g ⊗₁ h)) retag

  opaque
    naturality-to :
      Morphism.Iso OpenCSP (wire (associator A C E)) (wire (port-inverse (associator A C E))) →
      Morphism.Iso OpenCSP (wire (associator B D F)) (wire (port-inverse (associator B D F))) →
      (wire (port-inverse (associator B D F)) ∘ (f ⊗₁ (g ⊗₁ h)))
      ≅ (((f ⊗₁ g) ⊗₁ h) ∘ wire (port-inverse (associator A C E)))
    naturality-to a-iso b-iso = WireSquare.inverse-commute
      (associator A C E) (associator B D F) ((f ⊗₁ g) ⊗₁ h) (f ⊗₁ (g ⊗₁ h)) a-iso b-iso naturality

module LeftUnit {A B : Interface} (f : Network A B) where
  module SO = Tensor (id {I}) f
  module SR = Relabel (port-id (I ⊗₀ A)) (left-unitor B) (id ⊗₁ f)
  module TR = Relabel (port-inverse (left-unitor A)) (port-id B) f
  module S = Wiring SR.rewire
  module T = Wiring TR.rewire
  module SE = Edges SR.rewire
  module TE = Edges TR.rewire

  forward-name : S.Name → T.Name
  forward-name (inj₁ (inj₁ ()))
  forward-name (inj₁ (inj₂ p)) = inj₁ p
  forward-name (inj₂ e) = inj₂ e
  backward-name : T.Name → S.Name
  backward-name (inj₁ p) = inj₁ (inj₂ p)
  backward-name (inj₂ e) = inj₂ e
  forward-type : ∀ n → S.name-sort n ≡ T.name-sort (forward-name n)
  forward-type (inj₁ (inj₁ ()))
  forward-type (inj₁ (inj₂ _)) = refl
  forward-type (inj₂ (inj₁ (inj₁ ())))
  forward-type (inj₂ (inj₁ (inj₂ _))) = refl
  forward-type (inj₂ (inj₂ _)) = refl
  backward-type : ∀ n → T.name-sort n ≡ S.name-sort (backward-name n)
  backward-type (inj₁ _) = refl
  backward-type (inj₂ (inj₁ (inj₁ ())))
  backward-type (inj₂ (inj₁ (inj₂ _))) = refl
  backward-type (inj₂ (inj₂ _)) = refl
  forward-factor : ∀ n → forward-name (SR.rename (SO.right n)) ≡ TR.rename n
  forward-factor (inj₁ _) = refl
  forward-factor (inj₂ (inj₁ _)) = refl
  forward-factor (inj₂ (inj₂ _)) = refl
  backward-factor : ∀ n → backward-name (TR.rename n) ≡ SR.rename (SO.right n)
  backward-factor (inj₁ _) = refl
  backward-factor (inj₂ (inj₁ _)) = refl
  backward-factor (inj₂ (inj₂ _)) = refl

  forward-connected : ∀ {u v} → S.Connected u v → T.Connected (forward-name u) (forward-name v)
  forward-connected = map-connected forward-name
    (TE.mapped SO.aliases SR.rename forward-name
      (TE.mapped _ SO.right (λ n → forward-name (SR.rename n))
        (λ edge → TE.aligned _ TR.rename forward-factor (T.alias (∈-map⁺ (map-edge TR.rename) edge)))))
  backward-connected : ∀ {u v} → T.Connected u v → S.Connected (backward-name u) (backward-name v)
  backward-connected = map-connected backward-name
    (SE.mapped _ TR.rename backward-name
      (λ edge → SE.aligned _ (λ n → SR.rename (SO.right n)) backward-factor
        (S.alias (∈-map⁺ (map-edge SR.rename) (∈-map⁺ (map-edge SO.right) edge)))))

  opaque
    retag : SR.rewire ≅ TR.rewire
    retag = record
      { forward = record
          { box-map = λ { (inj₁ ()) ; (inj₂ k) → k } ; box-label = λ { (inj₁ ()) ; (inj₂ _) → refl }
          ; name-map = forward-name ; name-type = forward-type ; connected = forward-connected
          ; external = λ _ → T.same
          ; local = λ { (inj₁ ()) ; (inj₂ k) p → connection-equality (forward-factor (Network.local-wire f (k , p))) } }
      ; backward = record
          { box-map = inj₂ ; box-label = λ _ → refl ; name-map = backward-name ; name-type = backward-type
          ; connected = backward-connected ; external = λ _ → S.same
          ; local = λ k p → connection-equality (backward-factor (Network.local-wire f (k , p))) }
      ; boxes-left = λ { (inj₁ ()) ; (inj₂ _) → refl } ; boxes-right = λ _ → refl
      ; names-left = λ { (inj₁ (inj₁ ())) ; (inj₁ (inj₂ _)) → S.same ; (inj₂ _) → S.same }
      ; names-right = λ { (inj₁ _) → T.same ; (inj₂ _) → T.same } }

  opaque
    naturality : (wire (left-unitor B) ∘ (id ⊗₁ f)) ≅ (f ∘ wire (left-unitor A))
    naturality = WireSquare.commute (left-unitor A) (left-unitor B) (id ⊗₁ f) f retag

  opaque
    naturality-to :
      Morphism.Iso OpenCSP (wire (left-unitor A)) (wire (port-inverse (left-unitor A))) →
      Morphism.Iso OpenCSP (wire (left-unitor B)) (wire (port-inverse (left-unitor B))) →
      (wire (port-inverse (left-unitor B)) ∘ f) ≅ ((id ⊗₁ f) ∘ wire (port-inverse (left-unitor A)))
    naturality-to a-iso b-iso = WireSquare.inverse-commute (left-unitor A) (left-unitor B)
      (id ⊗₁ f) f a-iso b-iso naturality

module RightUnit {A B : Interface} (f : Network A B) where
  module SO = Tensor f (id {I})
  module SR = Relabel (port-id (A ⊗₀ I)) (right-unitor B) (f ⊗₁ id)
  module TR = Relabel (port-inverse (right-unitor A)) (port-id B) f
  module S = Wiring SR.rewire
  module T = Wiring TR.rewire
  module SE = Edges SR.rewire
  module TE = Edges TR.rewire

  forward-name : S.Name → T.Name
  forward-name (inj₁ (inj₁ p)) = inj₁ p
  forward-name (inj₁ (inj₂ ()))
  forward-name (inj₂ e) = inj₂ e
  backward-name : T.Name → S.Name
  backward-name (inj₁ p) = inj₁ (inj₁ p)
  backward-name (inj₂ e) = inj₂ e
  forward-type : ∀ n → S.name-sort n ≡ T.name-sort (forward-name n)
  forward-type (inj₁ (inj₁ _)) = refl
  forward-type (inj₁ (inj₂ ()))
  forward-type (inj₂ (inj₁ (inj₁ _))) = refl
  forward-type (inj₂ (inj₁ (inj₂ ())))
  forward-type (inj₂ (inj₂ _)) = refl
  backward-type : ∀ n → T.name-sort n ≡ S.name-sort (backward-name n)
  backward-type (inj₁ _) = refl
  backward-type (inj₂ (inj₁ (inj₁ _))) = refl
  backward-type (inj₂ (inj₁ (inj₂ ())))
  backward-type (inj₂ (inj₂ _)) = refl
  forward-factor : ∀ n → forward-name (SR.rename (SO.left n)) ≡ TR.rename n
  forward-factor (inj₁ _) = refl
  forward-factor (inj₂ (inj₁ _)) = refl
  forward-factor (inj₂ (inj₂ _)) = refl
  backward-factor : ∀ n → backward-name (TR.rename n) ≡ SR.rename (SO.left n)
  backward-factor (inj₁ _) = refl
  backward-factor (inj₂ (inj₁ _)) = refl
  backward-factor (inj₂ (inj₂ _)) = refl

  forward-connected : ∀ {u v} → S.Connected u v → T.Connected (forward-name u) (forward-name v)
  forward-connected = map-connected forward-name
    (TE.mapped SO.aliases SR.rename forward-name
      (TE.appended _ _ (λ n → forward-name (SR.rename n))
        (TE.mapped _ SO.left (λ n → forward-name (SR.rename n))
          (λ edge → TE.aligned _ TR.rename forward-factor (T.alias (∈-map⁺ (map-edge TR.rename) edge))))
        (λ ())))
  backward-connected : ∀ {u v} → T.Connected u v → S.Connected (backward-name u) (backward-name v)
  backward-connected = map-connected backward-name
    (SE.mapped _ TR.rename backward-name
      (λ edge → SE.aligned _ (λ n → SR.rename (SO.left n)) backward-factor
        (S.alias (∈-map⁺ (map-edge SR.rename) (∈-++⁺ˡ (∈-map⁺ (map-edge SO.left) edge))))))

  opaque
    retag : SR.rewire ≅ TR.rewire
    retag = record
      { forward = record
          { box-map = λ { (inj₁ k) → k ; (inj₂ ()) } ; box-label = λ { (inj₁ _) → refl ; (inj₂ ()) }
          ; name-map = forward-name ; name-type = forward-type ; connected = forward-connected
          ; external = λ _ → T.same
          ; local = λ { (inj₁ k) p → connection-equality (forward-factor (Network.local-wire f (k , p))) ; (inj₂ ()) } }
      ; backward = record
          { box-map = inj₁ ; box-label = λ _ → refl ; name-map = backward-name ; name-type = backward-type
          ; connected = backward-connected ; external = λ _ → S.same
          ; local = λ k p → connection-equality (backward-factor (Network.local-wire f (k , p))) }
      ; boxes-left = λ { (inj₁ _) → refl ; (inj₂ ()) } ; boxes-right = λ _ → refl
      ; names-left = λ { (inj₁ (inj₁ _)) → S.same ; (inj₁ (inj₂ ())) ; (inj₂ _) → S.same }
      ; names-right = λ { (inj₁ _) → T.same ; (inj₂ _) → T.same } }

  opaque
    naturality : (wire (right-unitor B) ∘ (f ⊗₁ id)) ≅ (f ∘ wire (right-unitor A))
    naturality = WireSquare.commute (right-unitor A) (right-unitor B) (f ⊗₁ id) f retag

  opaque
    naturality-to :
      Morphism.Iso OpenCSP (wire (right-unitor A)) (wire (port-inverse (right-unitor A))) →
      Morphism.Iso OpenCSP (wire (right-unitor B)) (wire (port-inverse (right-unitor B))) →
      (wire (port-inverse (right-unitor B)) ∘ f) ≅ ((f ⊗₁ id) ∘ wire (port-inverse (right-unitor A)))
    naturality-to a-iso b-iso = WireSquare.inverse-commute (right-unitor A) (right-unitor B)
      (f ⊗₁ id) f a-iso b-iso naturality

opaque
  identity-wire-tensor : ∀ {A B C} (f : PortIso B C)
    → (id {A} ⊗₁ wire f) ≅ wire (port-tensor (port-id A) f)
  identity-wire-tensor {A} f = ≅-trans (TensorIso.tensor-congruence (≅-sym (wire-id A)) (≅-refl {F = wire f}))
    (TensorWires.tensor-wires (port-id A) f)

  wire-identity-tensor : ∀ {A B C} (f : PortIso A B)
    → (wire f ⊗₁ id {C}) ≅ wire (port-tensor f (port-id C))
  wire-identity-tensor {C = C} f = ≅-trans (TensorIso.tensor-congruence (≅-refl {F = wire f}) (≅-sym (wire-id C)))
    (TensorWires.tensor-wires f (port-id C))

opaque

  triangle : ∀ A B → ((id ⊗₁ wire (left-unitor B)) ∘ wire (associator A I B))
    ≅ (wire (right-unitor A) ⊗₁ id)
  triangle A B = ≅-trans
    (PlugIso.plugging-congruence (≅-refl {F = wire (associator A I B)}) (identity-wire-tensor (left-unitor B)))
    (≅-trans (Composition.compose-wires (associator A I B) (port-tensor (port-id A) (left-unitor B)))
      (≅-trans (Extensional.wire-resp
        (port-compose (port-tensor (port-id A) (left-unitor B)) (associator A I B))
        (port-tensor (right-unitor A) (port-id B))
        (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ ())) ; (inj₂ _) → refl }))
        (≅-sym (wire-identity-tensor (right-unitor A)))))

opaque

  pentagon : ∀ A B C D →
    ((id ⊗₁ wire (associator B C D)) ∘
      (wire (associator A (B ⊗₀ C) D) ∘ (wire (associator A B C) ⊗₁ id)))
    ≅ (wire (associator A B (C ⊗₀ D)) ∘ wire (associator (A ⊗₀ B) C D))
  pentagon A B C D = ≅-trans
    (PlugIso.plugging-congruence
      (PlugIso.plugging-congruence (wire-identity-tensor (associator A B C))
        (≅-refl {F = wire (associator A (B ⊗₀ C) D)}))
      (identity-wire-tensor (associator B C D)))
    (≅-trans
      (PlugIso.plugging-congruence
        (Composition.compose-wires (port-tensor (associator A B C) (port-id D)) (associator A (B ⊗₀ C) D))
        (≅-refl {F = wire (port-tensor (port-id A) (associator B C D))}))
      (≅-trans
        (Composition.compose-wires
          (port-compose (associator A (B ⊗₀ C) D) (port-tensor (associator A B C) (port-id D)))
          (port-tensor (port-id A) (associator B C D)))
        (≅-trans (Extensional.wire-resp
          (port-compose (port-tensor (port-id A) (associator B C D))
            (port-compose (associator A (B ⊗₀ C) D) (port-tensor (associator A B C) (port-id D))))
          (port-compose (associator A B (C ⊗₀ D)) (associator (A ⊗₀ B) C D))
          (λ { (inj₁ (inj₁ (inj₁ _))) → refl ; (inj₁ (inj₁ (inj₂ _))) → refl
             ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl }))
          (≅-sym (Composition.compose-wires (associator (A ⊗₀ B) C D) (associator A B (C ⊗₀ D)))))))
