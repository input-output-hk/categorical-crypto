{-# OPTIONS --safe --without-K #-}

module Categories.APROP.Hypergraph.Model.Dependency where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.Iso

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality

module _ {X : Set} {Gen : List X → List X → Set} where

  open Hypergraph

  Dep : (G : Hypergraph Gen) → Fin (nE G) → Fin (nE G) → Set
  Dep G e e' = ∃[ v ] (v ∈ eout G e × v ∈ ein G e')

  Dep-reflect
    : {sub H : Hypergraph Gen}
    → (embV : Fin (nV sub) → Fin (nV H))
    → (∀ {x y} → embV x ≡ embV y → x ≡ y)
    → (embE : Fin (nE sub) → Fin (nE H))
    → (∀ e → eout H (embE e) ≡ map embV (eout sub e))
    → (∀ e → ein  H (embE e) ≡ map embV (ein  sub e))
    → ∀ {ea eb} → Dep H (embE eb) (embE ea) → Dep sub eb ea
  Dep-reflect {sub} embV embV-inj embE eout-red ein-red {ea} {eb} (v , v∈out , v∈in)
    with ∈-map⁻ embV (subst (v ∈_) (eout-red eb) v∈out)
       | ∈-map⁻ embV (subst (v ∈_) (ein-red ea) v∈in)
  ... | wb , wb∈ , v≡wb | wa , wa∈ , v≡wa =
    wb , wb∈ , subst (_∈ ein sub ea) (embV-inj (trans (sym v≡wa) v≡wb)) wa∈

module _ {X : Set} {Gen : List X → List X → Set}
         {H J : Hypergraph Gen} (Φ : H ≅ᴴ J) where

  open _≅ᴴ_ Φ
  private
    module H = Hypergraph H
    module J = Hypergraph J

  ≺⇒ψ≺ : ∀ {e e'} → Dep H e e' → Dep J (ψ e) (ψ e')
  ≺⇒ψ≺ {e} {e'} (v , v∈out , v∈in) =
    φ v
    , subst (φ v ∈_) (sym (ψ-eout e )) (∈-map⁺ φ v∈out)
    , subst (φ v ∈_) (sym (ψ-ein  e')) (∈-map⁺ φ v∈in)
