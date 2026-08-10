{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Record assembly / verification.
--
-- Given `H, J : Hypergraph FlatGen` and a `(φB, ψB) : PBij × PBij`
-- produced by the search, verify all `_≅ᴴ_` invariants and, if they
-- all hold, produce the iso record. If any invariant fails, return
-- `nothing`.
--
-- Every proof field is verified by decidable checks.  The trickiest is
-- `ψ-elab` (edge-label equality at `FlatGen` level): since `flatten` is not
-- injective, pattern matching on two `flat f, flat g : FlatGen As Bs` gets
-- stuck on `flatten A ≟ flatten A'`.  We sidestep this via a `FlatView`
-- record storing each value with explicit equalities.  The resulting
-- `flat-match-subst` is conservative (`just` only when the hidden `A, B` agree
-- and `f ≟-mor g`) — enough for `findIso`, whose edge matches come from
-- `hGen`-generated edges with preserved hidden indices.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature

module Categories.APROP.Hypergraph.Solver.Match.Verify (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.APROP.Hypergraph.Model.Iso
open import Categories.APROP.Hypergraph.Solver.Match.PBij

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base
open import Data.List.Properties
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Function
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality

open import Relation.Nullary
open import Relation.Nullary.Decidable using (dec⇒maybe)

--------------------------------------------------------------------------------
-- ∀F? : universal-quantification decider over `Fin n`.

∀F? : ∀ {ℓ} {n : ℕ} {P : Fin n → Set ℓ} → (∀ i → Maybe (P i)) → Maybe (∀ i → P i)
∀F? {n = ℕ.zero}  d = just λ ()
∀F? {n = ℕ.suc n} d =
  d zero                >>= λ p₀ →
  ∀F? (λ i → d (suc i)) >>= λ ps →
  just λ { zero → p₀ ; (suc i) → ps i }

--------------------------------------------------------------------------------
-- Decidable equality on Fin-index lists, at any arity: the endpoint and
-- boundary checks of `Verify` and of `SubMatch`'s `verifySub` share it.

_≟LF_ : ∀ {n} → DecidableEquality (List (Fin n))
_≟LF_ = ≡-dec _≟F_

--------------------------------------------------------------------------------
-- UIP at `List X`, from decidable atom equality via Hedberg's theorem.

open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Data.List.Properties.Ext using (≡-irrelevant)

UIP-ListX : UIP (List X)
UIP-ListX = ≡-irrelevant _≟X_

--------------------------------------------------------------------------------
-- FlatView : explicit view extracting the hidden `(A, B, f)` from a
-- `FlatGen As Bs` value. Sidesteps the stuck `flatten A ≟ flatten A'`
-- unification when comparing two `FlatGen` values.

-- `view` reads `f`/`A`/`B` and the boundary proofs by shallow record-pattern
-- projection.  Because every `elab` is built as a *direct* `flat-rec` (no
-- `subst₂` wrapper — see `FromAPROP.retype`), this never forces the
-- tower-deep boundary equalities to normalise.
record FlatView {As Bs : List X} (x : FlatGen As Bs) : Set where
  constructor flatV
  field
    A B  : ObjTerm
    f    : mor A B
    ok-A : flatten A ≡ As
    ok-B : flatten B ≡ Bs
    ok   : flat-rec ok-A ok-B f ≡ x

view : ∀ {As Bs} (x : FlatGen As Bs) → FlatView x
view (flat-rec {A} {B} oa ob f) = flatV A B f oa ob refl

--------------------------------------------------------------------------------
-- Conservative `flat`-match via the views, deferring to `_≟-ObjTerm_` and
-- `_≟-mor_`.

-- The relevant payload of two `FlatGen` values is `(A, B, f)`; when `v` and
-- `y` share it, `subst₂ FlatGen p q v ≡ y` holds — both are the *same*
-- `flat-rec` at the *same* indices, the boundary proofs collapsing under UIP.
flatgen-irrel
  : ∀ {As Bs As' Bs'} (p : As ≡ As') (q : Bs ≡ Bs')
      (v : FlatGen As Bs) (y : FlatGen As' Bs')
      {A B} (f : mor A B)
      (oa : flatten A ≡ As)  (ob : flatten B ≡ Bs)
      (oa' : flatten A ≡ As') (ob' : flatten B ≡ Bs')
  → flat-rec oa ob f ≡ v → flat-rec oa' ob' f ≡ y
  → subst₂ FlatGen p q v ≡ y
flatgen-irrel refl refl _ _ f oa ob oa' ob' refl refl with UIP-ListX oa oa' | UIP-ListX ob ob'
... | refl | refl = refl

-- `flat-match-subst p q v y`: compare the *transported* J-label
-- `subst₂ FlatGen p q v` against the H-label `y`, WITHOUT building the
-- transported term — we `view` the underlying `v`/`y` (record-pattern
-- projection only, no proof normalisation), dispatch on the hidden `(A,B,f)`,
-- and assemble the equality directly.  This is the hot path for `findIso`'s
-- per-edge label sweep: all call sites pass exactly `subst₂ FlatGen p q (…elab…)`.
flat-match-subst
  : ∀ {As Bs As' Bs'} (p : As ≡ As') (q : Bs ≡ Bs')
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
            -- `v` and `y` reconstruct from the *same* `(A,B)` boundaries; with
            -- `f ≡ g` their relevant payloads agree, so `flatgen-irrel` settles
            -- the transported equality (boundary proofs being erased).
            compare (yes refl) = just (flatgen-irrel p q v y f ok-A ok-B ok-A' ok-B' ok-v ok-y)
            compare (no _) = nothing
        dispatch _ _ = nothing

--------------------------------------------------------------------------------
-- Main verification.

module Verify (H J : Hypergraph FlatGen)
              (φB : PBij (Hypergraph.nV H) (Hypergraph.nV J))
              (ψB : PBij (Hypergraph.nE H) (Hypergraph.nE J)) where

  module H = Hypergraph H
  module J = Hypergraph J

  --------------------------------------------------------------------------
  -- Main entry point: extract the totals, then check bijection laws, vertex
  -- labels, edge endpoints, boundaries, and finally edge labels.  Every stage
  -- returns `nothing` on first failure — `_>>=_` stops at the first one, in
  -- the order written.

  verify : Maybe (H ≅ᴴ J)
  verify =
    totalise (forward  φB)                                       >>= λ (φ   , _) →
    totalise (backward φB)                                       >>= λ (φ⁻¹ , _) →
    totalise (forward  ψB)                                       >>= λ (ψ   , _) →
    totalise (backward ψB)                                       >>= λ (ψ⁻¹ , _) →
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
