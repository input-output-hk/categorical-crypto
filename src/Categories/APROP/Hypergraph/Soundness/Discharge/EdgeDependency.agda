{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The immediate edge-dependency relation `e ≺ e' := ∃ v. v ∈ eout e ×
-- v ∈ ein e'` (a wire produced by `e` is consumed by `e'`), and its two
-- transport laws:
--
--   * `Dep-reflect` reflects a dependency in a composite back into one of
--     its blocks, along an edge embedding.  This is what `FinOrderNoInv`
--     imports, both off the diagonal and (at `ea ≡ eb`) on it.
--   * Lemma A (`≺⇒ψ≺`): a hypergraph isomorphism `Φ : H ≅ᴴ J` carries `_≺_`
--     FORWARD,  e ≺_H e'  →  ψ e ≺_J ψ e'.  One direction, not the stated
--     biconditional of old — the converse is `≺⇒ψ≺ (sym-≅ᴴ Φ)`, and no
--     consumer has ever needed it.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.Iso

open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)

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
  -- (`FinOrderNoInv.*-reflect`) and, at `ea ≡ eb`, the self-dependency
  -- diagonal (`FinOrderNoInv.NoSelfDep-*`).
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
-- Lemma A: a hypergraph isomorphism carries the dependency relation forward.

module _ {X : Set} {Gen : List X → List X → Set}
         {H J : Hypergraph Gen} (Φ : H ≅ᴴ J) where

  open _≅ᴴ_ Φ
  private
    module H = Hypergraph H
    module J = Hypergraph J

  ≺⇒ψ≺ : ∀ {e e'} → e ≺[ H ] e' → ψ e ≺[ J ] ψ e'
  ≺⇒ψ≺ {e} {e'} (v , v∈out , v∈in) =
    φ v
    , subst (φ v ∈_) (sym (ψ-eout e )) (∈-map⁺ φ v∈out)
    , subst (φ v ∈_) (sym (ψ-ein  e')) (∈-map⁺ φ v∈in)
