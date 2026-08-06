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
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Function
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as Eq

open import Relation.Nullary
open import Relation.Nullary.Decidable using (dec⇒maybe)

--------------------------------------------------------------------------------
-- ∀F? : universal-quantification decider over `Fin n`.

∀F? : ∀ {ℓ} {n : ℕ} {P : Fin n → Set ℓ} → (∀ i → Maybe (P i)) → Maybe (∀ i → P i)
∀F? {n = ℕ.zero}  d = just λ ()
∀F? {n = ℕ.suc n} d with d zero
... | nothing = nothing
... | just p₀ with ∀F? (λ i → d (suc i))
...   | nothing = nothing
...   | just ps = just λ { zero → p₀ ; (suc i) → ps i }

--------------------------------------------------------------------------------
-- Decidable list equality at the atom alphabet `X`, and UIP derived
-- from it via Hedberg's theorem.

_≟LX_ : DecidableEquality (List X)
_≟LX_ = ≡-dec _≟X_

open import Axiom.UniquenessOfIdentityProofs
import Axiom.UniquenessOfIdentityProofs as UIP-mod

UIP-ListX : UIP (List X)
UIP-ListX = UIP-mod.Decidable⇒UIP.≡-irrelevant _≟LX_

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

  private
    _≟LF-J_ : DecidableEquality (List (Fin J.nV))
    _≟LF-J_ = ≡-dec _≟F_

  --------------------------------------------------------------------------
  -- Main entry point: a nested `with` extracting totals, then checking
  -- bijection laws, vertex labels, edge endpoints, boundaries, and finally
  -- edge labels.  Every stage returns `nothing` on first failure.

  verify : Maybe (H ≅ᴴ J)
  verify with totalise (forward φB) | totalise (backward φB)
              | totalise (forward ψB) | totalise (backward ψB)
  ... | nothing | _       | _       | _       = nothing
  ... | _       | nothing | _       | _       = nothing
  ... | _       | _       | nothing | _       = nothing
  ... | _       | _       | _       | nothing = nothing
  ... | just (φ , _) | just (φ⁻¹ , _)
      | just (ψ , _) | just (ψ⁻¹ , _)
        with ∀F? (λ i → dec⇒maybe (φ⁻¹ (φ i) ≟F i))
           | ∀F? (λ j → dec⇒maybe (φ (φ⁻¹ j) ≟F j))
           | ∀F? (λ e → dec⇒maybe (ψ⁻¹ (ψ e) ≟F e))
           | ∀F? (λ k → dec⇒maybe (ψ (ψ⁻¹ k) ≟F k))
           | ∀F? (λ i → dec⇒maybe (J.vlab (φ i) ≟X H.vlab i))
           | ∀F? (λ e → dec⇒maybe (J.ein  (ψ e) ≟LF-J map φ (H.ein  e)))
           | ∀F? (λ e → dec⇒maybe (J.eout (ψ e) ≟LF-J map φ (H.eout e)))
           | J.dom ≟LF-J map φ H.dom
           | J.cod ≟LF-J map φ H.cod
  ...       | nothing | _ | _ | _ | _ | _ | _ | _     | _     = nothing
  ...       | _ | nothing | _ | _ | _ | _ | _ | _     | _     = nothing
  ...       | _ | _ | nothing | _ | _ | _ | _ | _     | _     = nothing
  ...       | _ | _ | _ | nothing | _ | _ | _ | _     | _     = nothing
  ...       | _ | _ | _ | _ | nothing | _ | _ | _     | _     = nothing
  ...       | _ | _ | _ | _ | _ | nothing | _ | _     | _     = nothing
  ...       | _ | _ | _ | _ | _ | _ | nothing | _     | _     = nothing
  ...       | _ | _ | _ | _ | _ | _ | _       | no _  | _     = nothing
  ...       | _ | _ | _ | _ | _ | _ | _       | _     | no _  = nothing
  ...       | just φ-left | just φ-rght | just ψ-left | just ψ-rght
            | just φ-lab  | just ψ-ein  | just ψ-eout
            | yes φ-dom   | yes φ-cod
              with ∀F? (λ e → flat-match-subst
                     (deriveAtomEq φ-lab (H.ein  e) (ψ-ein  e))
                     (deriveAtomEq φ-lab (H.eout e) (ψ-eout e))
                     (J.elab (ψ e))
                     (H.elab e))
  ...         | nothing = nothing
  ...         | just ψ-elab = just record
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
