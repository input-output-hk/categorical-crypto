{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `edge-step` as an inductive relation (`EdgeStepR`, its graph), with the
-- two "view" lemmas:
--   * `edge-step-graph` : the function realises the relation;
--   * `edge-step-sound` : the relation pins the function value.
--
-- Case analysis on the relation's constructors (`skipR`/`fireR`) avoids
-- the green-slime with-abstraction of the opaque `edge-step`.  `fire-term`
-- reconstructs Decode's local `bridged` term, so `fireR`'s HomTerm index
-- is definitionally `proj₂ (edge-step G s e)` (and `edge-step-graph`'s
-- `fireR` clause is `refl`).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; _≅_)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (edge-step; Agen-edge; Agen-edge-aux; extract-prefix)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)

open import Data.Fin using (Fin)
open import Data.List using (List; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst₂)

--------------------------------------------------------------------------------
-- The FIRE "box" as a standalone (hypergraph-agnostic) function of its
-- label lists + generator, with a congruence lemma.

box-of
  : ∀ (einL eoutL restL : List X) → FlatGen einL eoutL
  → HomTerm (unflatten (einL ++ restL)) (unflatten (eoutL ++ restL))
box-of einL eoutL restL g =
  _≅_.to   (unflatten-++-≅ eoutL restL)
  ∘ (Agen-edge-aux g ⊗₁ id)
  ∘ _≅_.from (unflatten-++-≅ einL restL)

-- `box-of` respects equalities of all three lists + a transported generator.
box-of-cong
  : ∀ {einL₁ einL₂ eoutL₁ eoutL₂ restL₁ restL₂ : List X}
      (eq-ein : einL₁ ≡ einL₂) (eq-eout : eoutL₁ ≡ eoutL₂) (eq-rest : restL₁ ≡ restL₂)
      (g₁ : FlatGen einL₁ eoutL₁) (g₂ : FlatGen einL₂ eoutL₂)
  → subst₂ FlatGen eq-ein eq-eout g₁ ≡ g₂
  → subst₂ HomTerm
      (cong unflatten (cong₂ _++_ eq-ein  eq-rest))
      (cong unflatten (cong₂ _++_ eq-eout eq-rest))
      (box-of einL₁ eoutL₁ restL₁ g₁)
    ≡ box-of einL₂ eoutL₂ restL₂ g₂
box-of-cong refl refl refl _ _ refl = refl

module _ (G : Hypergraph FlatGen) where
  private module G = Hypergraph G

  -- The FIRE "box" factor: the edge generator at the front with identity
  -- on the residual, framed by the `unflatten-++-≅` coercions.
  fire-mid
    : ∀ (e : Fin G.nE) (rest : List (Fin G.nV))
    → HomTerm (unflatten (map G.vlab (G.ein  e ++ rest)))
              (unflatten (map G.vlab (G.eout e ++ rest)))
  fire-mid e rest =
    subst₂ HomTerm
      (cong unflatten (sym (map-++ G.vlab (G.ein  e) rest)))
      (cong unflatten (sym (map-++ G.vlab (G.eout e) rest)))
      (box-of (map G.vlab (G.ein e)) (map G.vlab (G.eout e)) (map G.vlab rest)
              (G.elab e))

  -- The reconstructed FIRE term, definitionally `proj₂ (edge-step G s e)`
  -- on the FIRE branch.
  fire-term
    : ∀ (e : Fin G.nE) (s rest : List (Fin G.nV))
    → s Perm.↭ G.ein e ++ rest
    → HomTerm (unflatten (map G.vlab s))
              (unflatten (map G.vlab (G.eout e ++ rest)))
  fire-term e s rest perm = fire-mid e rest ∘ permute-via-vlab G.vlab perm

  data EdgeStepR (s : List (Fin G.nV)) (e : Fin G.nE)
       : (s' : List (Fin G.nV))
       → HomTerm (unflatten (map G.vlab s)) (unflatten (map G.vlab s'))
       → Set where
    skipR : extract-prefix (G.ein e) s ≡ nothing
          → EdgeStepR s e s id
    fireR : ∀ (rest : List (Fin G.nV)) (perm : s Perm.↭ G.ein e ++ rest)
          → extract-prefix (G.ein e) s ≡ just (rest , perm)
          → EdgeStepR s e (G.eout e ++ rest) (fire-term e s rest perm)

  -- The function realises the relation.
  edge-step-graph
    : ∀ (s : List (Fin G.nV)) (e : Fin G.nE)
    → EdgeStepR s e (proj₁ (edge-step G s e)) (proj₂ (edge-step G s e))
  edge-step-graph s e with extract-prefix (G.ein e) s in eq
  ... | nothing            = skipR eq
  ... | just (rest , perm) = fireR rest perm eq

  -- The relation pins the function value.
  edge-step-sound
    : ∀ {s : List (Fin G.nV)} {e : Fin G.nE}
        {s' : List (Fin G.nV)}
        {t : HomTerm (unflatten (map G.vlab s)) (unflatten (map G.vlab s'))}
    → EdgeStepR s e s' t
    → edge-step G s e ≡ (s' , t)
  edge-step-sound (skipR eq)          rewrite eq = refl
  edge-step-sound (fireR rest perm eq) rewrite eq = refl
