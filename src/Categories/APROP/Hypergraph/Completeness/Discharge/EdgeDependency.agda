{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The edge dependency relation of a hypergraph, and the fact that a
-- hypergraph isomorphism is an isomorphism of that relation ("Lemma A").
--
-- The *immediate dependency relation* on edges is
--
--     e ≺ e'  :=  ∃ vertex v.  v ∈ eout e  ×  v ∈ ein e'
--
-- i.e. some wire produced by `e` is consumed by `e'`.  An isomorphism
-- `Φ : H ≅ᴴ J` carries a vertex bijection `φ` and an edge bijection `ψ`
-- with `J.eout (ψ e) ≡ map φ (H.eout e)` and `J.ein (ψ e) ≡ map φ (H.ein e)`
-- (fields `ψ-eout`, `ψ-ein`).  Lemma A says
--
--     e ≺_H e'   ⟺   ψ e ≺_J ψ e'.
--
-- This is a standalone sketch module; it is not wired into the
-- completeness proof and modifies no other file.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency where

open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.Iso

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- The immediate dependency relation.

module _ {X : Set} {Gen : List X → List X → Set} where

  open Hypergraph

  -- `Dep G e e'`: edge `e` produces a wire that edge `e'` consumes.
  -- (Written `e ≺[ G ] e'` via the syntax declaration below.)
  Dep : (G : Hypergraph Gen) → Fin (nE G) → Fin (nE G) → Set
  Dep G e e' = ∃[ v ] (v ∈ eout G e × v ∈ ein G e')

  syntax Dep G e e' = e ≺[ G ] e'

--------------------------------------------------------------------------------
-- Membership transport along an injective `map φ`.

module _ {A B : Set} (φ : A → B)
         (φ-inj : ∀ {x y} → φ x ≡ φ y → x ≡ y) where

  -- Forward: membership is preserved by `map φ`.  (Just stdlib `∈-map⁺`.)
  ∈-mapφ⁺ : ∀ {v} {l : List A} → v ∈ l → φ v ∈ map φ l
  ∈-mapφ⁺ = ∈-map⁺ φ

  -- Backward: from `φ v ∈ map φ l` recover `v ∈ l`, using injectivity of φ.
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

  -- φ is injective: φ-left exhibits φ⁻¹ as a left inverse.
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
    -- The shared vertex `w` lives in `J.eout (ψ e) ≡ map φ (H.eout e)`,
    -- hence `w ≡ φ v` for some `v ∈ H.eout e`.
    with ∈-map⁻ φ (subst (w ∈_) (ψ-eout e) w∈out)
  ... | v , v∈out , w≡φv =
    v
    , v∈out
    , ∈-mapφ⁻ φ φ-inj
        (subst (_∈ map φ (H.ein e'))
               w≡φv
               (subst (w ∈_) (ψ-ein e') w∈in))

  -- Lemma A as an `⇔`.
  lemmaA : ∀ {e e'} → (e ≺[ H ] e') ⇔ (ψ e ≺[ J ] ψ e')
  lemmaA = mk⇔ ≺⇒ψ≺ ψ≺⇒≺

  -- Conventional name.
  ≺-resp-≅ᴴ : ∀ {e e'} → (e ≺[ H ] e') ⇔ (ψ e ≺[ J ] ψ e')
  ≺-resp-≅ᴴ = lemmaA

--------------------------------------------------------------------------------
-- The dependency *order* is the transitive closure of `_≺[ H ]_`.  Since
-- `ψ` is a bijection on edges and `lemmaA` transports `_≺_` in both
-- directions edge-by-edge, the closure is likewise transported (an easy
-- induction on `Relation.Binary.Construct.Closure.Transitive.Plus′`).
-- We leave the closure lift out of this first sketch.
