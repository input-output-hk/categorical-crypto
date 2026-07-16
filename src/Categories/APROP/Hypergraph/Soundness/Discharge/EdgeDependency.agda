{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The immediate edge-dependency relation `e ≺ e' := ∃ v. v ∈ eout e ×
-- v ∈ ein e'` (a wire produced by `e` is consumed by `e'`), and Lemma A:
-- a hypergraph isomorphism `Φ : H ≅ᴴ J` is an isomorphism of `_≺_`,
--     e ≺_H e'  ⟺  ψ e ≺_J ψ e'.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.Iso

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- The immediate dependency relation.

module _ {X : Set} {Gen : List X → List X → Set} where

  open Hypergraph

  -- `Dep G e e'`: edge `e` produces a wire that edge `e'` consumes.
  Dep : (G : Hypergraph Gen) → Fin (nE G) → Fin (nE G) → Set
  Dep G e e' = ∃[ v ] (v ∈ eout G e × v ∈ ein G e')

  syntax Dep G e e' = e ≺[ G ] e'

  -- Reflect a dependency in a composite `H` back to a sub-hypergraph `sub`
  -- along an edge embedding `embE` and an injective vertex embedding `embV`,
  -- given that `sub`'s in/out ports transport to `H`'s along `embV`.  This is
  -- the mechanical engine shared by the tensor/compose block-reflection lemmas
  -- (`FinOrderNoInv.*-reflect`) and the self-dependency diagonal
  -- (`DepIrrefl`, at `ea ≡ eb`).
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

--------------------------------------------------------------------------------
-- Membership transport along an injective `map φ`.

module _ {A B : Set} (φ : A → B)
         (φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y) where

  ∈-mapφ⁺ : ∀ {v} {l : List A} → v ∈ l → φ v ∈ map φ l
  ∈-mapφ⁺ = ∈-map⁺ φ

  -- From `φ v ∈ map φ l` recover `v ∈ l`, using injectivity of φ.
  ∈-mapφ⁻ : ∀ {v} {l : List A} → φ v ∈ map φ l → v ∈ l
  ∈-mapφ⁻ {v} {l} φv∈ with ∈-map⁻ φ φv∈
  ... | w , w∈l , φv≡φw = subst (_∈ l) (sym (φ-inj φv≡φw)) w∈l

--------------------------------------------------------------------------------
-- Lemma A: a hypergraph isomorphism is an isomorphism of the dependency
-- relation.

module _ {X : Set} {Gen : List X → List X → Set}
         {H J : Hypergraph Gen} (Φ : H ≅ᴴ J) where

  open _≅ᴴ_ Φ
  private
    module H = Hypergraph H
    module J = Hypergraph J

  φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y
  φ-inj {x} {y} eq = trans (sym (φ-left x)) (trans (cong φ⁻¹ eq) (φ-left y))

  -- Forward direction of Lemma A.
  ≺⇒ψ≺ : ∀ {e e'} → e ≺[ H ] e' → ψ e ≺[ J ] ψ e'
  ≺⇒ψ≺ {e} {e'} (v , v∈out , v∈in) =
    φ v
    , subst (φ v ∈_) (sym (ψ-eout e )) (∈-mapφ⁺ φ φ-inj v∈out)
    , subst (φ v ∈_) (sym (ψ-ein  e')) (∈-mapφ⁺ φ φ-inj v∈in)

  -- Backward direction of Lemma A.
  ψ≺⇒≺ : ∀ {e e'} → ψ e ≺[ J ] ψ e' → e ≺[ H ] e'
  ψ≺⇒≺ {e} {e'} (w , w∈out , w∈in)
    -- `w ∈ J.eout (ψ e) = map φ (H.eout e)`, so `w ≡ φ v` for some
    -- `v ∈ H.eout e`.
    with ∈-map⁻ φ (subst (w ∈_) (ψ-eout e) w∈out)
  ... | v , v∈out , w≡φv =
    v
    , v∈out
    , ∈-mapφ⁻ φ φ-inj
        (subst (_∈ map φ (H.ein e'))
               w≡φv
               (subst (w ∈_) (ψ-ein e') w∈in))
