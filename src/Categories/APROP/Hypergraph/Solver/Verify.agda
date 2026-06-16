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
-- `flat-match` is conservative (`just` only when the hidden `A, B` agree and
-- `f ≟-mor g`) — enough for `findIso`, whose edge matches come from
-- `hGen`-generated edges with preserved hidden indices.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Verify (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flat; flatten)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Solver.PBij
  using (PBij; forward; backward)
open import Categories.APROP.Hypergraph.Solver.Totals
  using (Total; totalise)

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Properties using (map-∘; map-cong; ≡-dec)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl; cong; cong₂; trans; sym; subst; subst₂)
open import Relation.Nullary using (yes; no; Dec)
import Relation.Nullary
open import Data.Product using (_×_)

--------------------------------------------------------------------------------
-- Convert a `Dec` to `Maybe`, discarding the negative evidence.

dec→maybe : ∀ {ℓ} {A : Set ℓ} → Dec A → Maybe A
dec→maybe (yes p) = just p
dec→maybe (no  _) = nothing

--------------------------------------------------------------------------------
-- ∀F? : universal-quantification decider over `Fin n`.

∀F? : ∀ {ℓ} {n : ℕ} {P : Fin n → Set ℓ}
    → (∀ i → Maybe (P i))
    → Maybe (∀ i → P i)
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

open import Axiom.UniquenessOfIdentityProofs using (UIP)
import Axiom.UniquenessOfIdentityProofs as UIP-mod

UIP-ListX : UIP (List X)
UIP-ListX = UIP-mod.Decidable⇒UIP.≡-irrelevant _≟LX_

--------------------------------------------------------------------------------
-- FlatView : explicit view extracting the hidden `(A, B, f)` from a
-- `FlatGen As Bs` value. Sidesteps the stuck `flatten A ≟ flatten A'`
-- unification when comparing two `FlatGen` values.

record FlatView {As Bs : List X} (x : FlatGen As Bs) : Set where
  constructor flatV
  field
    A B  : ObjTerm
    ok-A : flatten A ≡ As
    ok-B : flatten B ≡ Bs
    f    : mor A B
    ok   : subst₂ FlatGen ok-A ok-B (flat f) ≡ x

view : ∀ {As Bs} (x : FlatGen As Bs) → FlatView x
view (flat {A} {B} f) = flatV A B refl refl f refl

--------------------------------------------------------------------------------
-- Conservative `flat`-match via the views, deferring to `_≟-ObjTerm_` and
-- `_≟-mor_`.

-- Two `subst₂` transports with equal endpoints are equal (UIP).
help-subst-eq
  : ∀ {A₁ A₂ B₁ B₂ : List X}
      (p₁ p₂ : A₁ ≡ A₂) (q₁ q₂ : B₁ ≡ B₂)
      (z : FlatGen A₁ B₁)
  → subst₂ FlatGen p₁ q₁ z ≡ subst₂ FlatGen p₂ q₂ z
help-subst-eq p₁ p₂ q₁ q₂ z
  with UIP-ListX p₁ p₂ | UIP-ListX q₁ q₂
... | refl | refl = refl

-- `flat-match-subst p q v y`: compare the *transported* J-label
-- `subst₂ FlatGen p q v` against the H-label `y`, but WITHOUT first building
-- the transported term and forcing `view` to push through the outer `subst₂`.
-- We `view` the underlying value `v` (one fewer stacked transport for the
-- normaliser to collapse) and `view y`, dispatch on the hidden `(A,B,f)`,
-- and assemble the equality directly.  This is the hot path for `findIso`'s
-- per-edge label sweep: all call sites pass exactly `subst₂ FlatGen p q (…elab…)`.
flat-match-subst
  : ∀ {As Bs As' Bs'} (p : As ≡ As') (q : Bs ≡ Bs')
      (v : FlatGen As Bs) (y : FlatGen As' Bs')
  → Maybe (subst₂ FlatGen p q v ≡ y)
flat-match-subst p q v y = step (view v) (view y)
  where
    step : FlatView v → FlatView y → Maybe (subst₂ FlatGen p q v ≡ y)
    step (flatV A B ok-A ok-B f ok-v) (flatV A' B' ok-A' ok-B' g ok-y) =
      dispatch (A ≟-ObjTerm A') (B ≟-ObjTerm B')
      where
        dispatch : _ → _ → Maybe (subst₂ FlatGen p q v ≡ y)
        dispatch (yes refl) (yes refl) = compare (f ≟-mor g)
          where
            compare : _ → Maybe (subst₂ FlatGen p q v ≡ y)
            -- v = subst₂ FlatGen ok-A ok-B (flat f)  (from ok-v)
            -- y = subst₂ FlatGen ok-A' ok-B' (flat g) (from ok-y)
            -- with f ≡ g and matching endpoints, both `subst₂` stacks
            -- transport the same `flat g` along propositionally-equal
            -- list proofs, so UIP collapses them.
            compare (yes f≡g) =
              just (trans (cong (subst₂ FlatGen p q) (sym ok-v))
                   (trans (cong (λ z → subst₂ FlatGen p q (subst₂ FlatGen ok-A ok-B (flat z))) f≡g)
                   (trans (help-subst-eq2 p ok-A ok-A' q ok-B ok-B' (flat g))
                          ok-y)))
              where
                -- subst₂ p q (subst₂ p' q' z) ≡ subst₂ p'' q'' z  (all via UIP).
                help-subst-eq2
                  : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ : List X}
                      (p₁ : A₂ ≡ A₃) (p₂ : A₁ ≡ A₂) (p₃ : A₁ ≡ A₃)
                      (q₁ : B₂ ≡ B₃) (q₂ : B₁ ≡ B₂) (q₃ : B₁ ≡ B₃)
                      (z : FlatGen A₁ B₁)
                  → subst₂ FlatGen p₁ q₁ (subst₂ FlatGen p₂ q₂ z)
                  ≡ subst₂ FlatGen p₃ q₃ z
                help-subst-eq2 refl refl p₃ refl refl q₃ z
                  with UIP-ListX refl p₃ | UIP-ListX refl q₃
                ... | refl | refl = refl
            compare (no _) = nothing
        dispatch _ _ = nothing

flat-match : ∀ {As Bs} (x y : FlatGen As Bs) → Maybe (x ≡ y)
flat-match x y = step (view x) (view y)
  where
    step : FlatView x → FlatView y → Maybe (x ≡ y)
    step (flatV A B ok-A ok-B f ok-x) (flatV A' B' ok-A' ok-B' g ok-y) =
      dispatch (A ≟-ObjTerm A') (B ≟-ObjTerm B')
      where
        dispatch : _ → _ → Maybe (x ≡ y)
        dispatch (yes refl) (yes refl) = compare (f ≟-mor g)
          where
            compare : _ → Maybe (x ≡ y)
            compare (yes p) =
              just (trans (sym ok-x)
                   (trans (cong (λ z → subst₂ FlatGen ok-A ok-B (flat z)) p)
                          (trans (help-subst-eq ok-A ok-A' ok-B ok-B' (flat g))
                                 ok-y)))
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

    -- `map J.vlab ys ≡ map H.vlab xs` from `ys ≡ map φ xs` and
    -- `J.vlab (φ i) ≡ H.vlab i` (turns ψ-ein/ψ-eout + φ-lab into atom-ein/-eout).
    deriveAtomEq
      : (φ : Fin H.nV → Fin J.nV)
      → (∀ i → J.vlab (φ i) ≡ H.vlab i)
      → ∀ (xs : List (Fin H.nV)) (ys : List (Fin J.nV))
      → ys ≡ map φ xs
      → map J.vlab ys ≡ map H.vlab xs
    deriveAtomEq φ φ-lab xs ys p =
      trans (cong (map J.vlab) p)
      (trans (sym (map-∘ xs))
             (map-cong φ-lab xs))

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
        with ∀F? (λ i → dec→maybe (φ⁻¹ (φ i) ≟F i))
           | ∀F? (λ j → dec→maybe (φ (φ⁻¹ j) ≟F j))
           | ∀F? (λ e → dec→maybe (ψ⁻¹ (ψ e) ≟F e))
           | ∀F? (λ k → dec→maybe (ψ (ψ⁻¹ k) ≟F k))
           | ∀F? (λ i → dec→maybe (J.vlab (φ i) ≟X H.vlab i))
           | ∀F? (λ e → dec→maybe (J.ein  (ψ e) ≟LF-J map φ (H.ein  e)))
           | ∀F? (λ e → dec→maybe (J.eout (ψ e) ≟LF-J map φ (H.eout e)))
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
                     (deriveAtomEq φ φ-lab (H.ein  e) (J.ein  (ψ e)) (ψ-ein  e))
                     (deriveAtomEq φ φ-lab (H.eout e) (J.eout (ψ e)) (ψ-eout e))
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
                ; atom-ein  = λ e → deriveAtomEq φ φ-lab (H.ein  e) (J.ein  (ψ e)) (ψ-ein  e)
                ; atom-eout = λ e → deriveAtomEq φ φ-lab (H.eout e) (J.eout (ψ e)) (ψ-eout e)
                ; ψ-elab    = ψ-elab
                }
