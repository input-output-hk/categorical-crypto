{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Verification of the search result. FlatGen matching is conservative:
-- hidden object boundaries must agree, even when their flattened lists do.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Match.Verify (sig : APROPSignature) where

open import Axiom.UniquenessOfIdentityProofs
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Model.Iso
open import Categories.APROP.Hypergraph.Solver.Match.PBij

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Fin.Traversal
open import Data.List.Base
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (dec⇒maybe)

open APROP sig
open FreeMonoidalHelper Symm X using (flatten)

private variable
  n : ℕ
  As Bs As' Bs' : List X

_≟LF_ : DecidableEquality (List (Fin n))
_≟LF_ = ≡-dec _≟F_

UIP-ListX : UIP (List X)
UIP-ListX = ≡-irrelevant _≟X_

-- See FromAPROP.FlatGen for the lazy boundary-proof representation.
record FlatView {As Bs : List X} (x : FlatGen As Bs) : Set where
  constructor flatV
  field A B : ObjTerm
        f : mor A B
        ok-A : flatten A ≡ As
        ok-B : flatten B ≡ Bs
        ok : flat-rec ok-A ok-B f ≡ x

view : (x : FlatGen As Bs) → FlatView x
view (flat-rec {A} {B} oa ob f) = flatV A B f oa ob refl

-- Equal payloads give equal records because UIP-ListX identifies the
-- relevant boundary proofs (see FromAPROP.FlatGen).
flatgen-irrel
  : (p : As ≡ As') (q : Bs ≡ Bs')
      (v : FlatGen As Bs) (y : FlatGen As' Bs')
      {A B : ObjTerm} (f : mor A B)
      (oa : flatten A ≡ As)  (ob : flatten B ≡ Bs)
      (oa' : flatten A ≡ As') (ob' : flatten B ≡ Bs')
  → flat-rec oa ob f ≡ v → flat-rec oa' ob' f ≡ y
  → subst₂ FlatGen p q v ≡ y
flatgen-irrel refl refl _ _ f oa ob oa' ob' refl refl with UIP-ListX oa oa' | UIP-ListX ob ob'
... | refl | refl = refl

-- Compare the underlying payloads without first normalising the transport.
flat-match-subst
  : (p : As ≡ As') (q : Bs ≡ Bs')
      (v : FlatGen As Bs) (y : FlatGen As' Bs')
  → Maybe (subst₂ FlatGen p q v ≡ y)
flat-match-subst {As} {Bs} {As'} {Bs'} p q v y = step (view v) (view y)
  where
    step : FlatView v → FlatView y → Maybe (subst₂ FlatGen p q v ≡ y)
    step (flatV A B f ok-A ok-B ok-v) (flatV A' B' g ok-A' ok-B' ok-y) =
      dispatch (A ≟-ObjTerm A') (B ≟-ObjTerm B')
      where
        dispatch : _ → _ → Maybe (subst₂ FlatGen p q v ≡ y)
        dispatch (yes refl) (yes refl) = compare (f ≟-mor g)
          where
            compare : _ → Maybe (subst₂ FlatGen p q v ≡ y)
            compare (yes refl) = just (flatgen-irrel p q v y f ok-A ok-B ok-A' ok-B' ok-v ok-y)
            compare (no _) = nothing
        dispatch _ _ = nothing

module Verify (H J : Hypergraph FlatGen)
              (φB : PBij (Hypergraph.nV H) (Hypergraph.nV J))
              (ψB : PBij (Hypergraph.nE H) (Hypergraph.nE J)) where

  module H = Hypergraph H
  module J = Hypergraph J

  verify : Maybe (H ≅ᴴ J)
  verify =
    totalise (forward  φB)                                       >>= λ φ   →
    totalise (backward φB)                                       >>= λ φ⁻¹ →
    totalise (forward  ψB)                                       >>= λ ψ   →
    totalise (backward ψB)                                       >>= λ ψ⁻¹ →
    ∀F? (λ i → dec⇒maybe (φ⁻¹ (φ i) ≟F i))                       >>= λ φ-left →
    ∀F? (λ j → dec⇒maybe (φ (φ⁻¹ j) ≟F j))                       >>= λ φ-rght →
    ∀F? (λ e → dec⇒maybe (ψ⁻¹ (ψ e) ≟F e))                       >>= λ ψ-left →
    ∀F? (λ k → dec⇒maybe (ψ (ψ⁻¹ k) ≟F k))                       >>= λ ψ-rght →
    ∀F? (λ i → dec⇒maybe (J.vlab (φ i) ≟X H.vlab i))             >>= λ φ-lab →
    ∀F? (λ e → dec⇒maybe (J.ein  (ψ e) ≟LF map φ (H.ein  e)))  >>= λ ψ-ein →
    ∀F? (λ e → dec⇒maybe (J.eout (ψ e) ≟LF map φ (H.eout e)))  >>= λ ψ-eout →
    dec⇒maybe (J.dom ≟LF map φ H.dom)                          >>= λ φ-dom →
    dec⇒maybe (J.cod ≟LF map φ H.cod)                          >>= λ φ-cod →
    ∀F? (λ e → flat-match-subst
                 (deriveAtomEq φ-lab (H.ein  e) (ψ-ein  e))
                 (deriveAtomEq φ-lab (H.eout e) (ψ-eout e))
                 (J.elab (ψ e))
                 (H.elab e))                                     >>= λ ψ-elab →
    just record
      { φ         = φ
      ; φ⁻¹       = φ⁻¹
      ; φ-left    = φ-left
      ; φ-rght    = φ-rght
      ; ψ         = ψ
      ; ψ⁻¹       = ψ⁻¹
      ; ψ-left    = ψ-left
      ; ψ-rght    = ψ-rght
      ; φ-lab     = φ-lab
      ; ψ-ein     = ψ-ein
      ; ψ-eout    = ψ-eout
      ; φ-dom     = φ-dom
      ; φ-cod     = φ-cod
      ; atom-ein  = λ e → deriveAtomEq φ-lab (H.ein  e) (ψ-ein  e)
      ; atom-eout = λ e → deriveAtomEq φ-lab (H.eout e) (ψ-eout e)
      ; ψ-elab    = ψ-elab
      }
