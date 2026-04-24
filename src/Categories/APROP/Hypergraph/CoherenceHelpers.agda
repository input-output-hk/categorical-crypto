{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Shared helper lemmas for hypergraph coherence proofs
-- (Triangle, Pentagon, AlphaCommSound, and future hexagon/ρ-nat/σ-nat).
--
-- All proofs are one-line pattern matches on `refl` — pure subst₂/cong
-- bookkeeping.  The actual coherence content lives in the per-axiom
-- modules; this module exists only so that those modules don't each
-- reprove (or inline) the same trivial lemmas.
--
-- Contents:
--
--   * `subst₂-cancel-sym-l`, `subst₂-cancel-sym-r`, `subst₂-trans-cod`
--     — fully polymorphic in the indexed type `P`.
--
--   * `hTensor-subst₂-left`, `hTensor-subst₂-right` — push/pull subst₂
--     through the boundaries of `hTensor`.
--
--   * `hComposeP-cod-subst` — pull a cod-side subst₂ out of `hComposeP`.
--
--   * `Unique-subst₂-dom` — transport `Unique` across a subst₂ on the dom.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.CoherenceHelpers (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; hTensor)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP)

open import Data.List using (List; _++_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst₂)

--------------------------------------------------------------------------------
-- Polymorphic subst₂ bookkeeping.

-- `subst₂ (sym p) refl (subst₂ p q G) ≡ subst₂ refl q G`
subst₂-cancel-sym-l
  : ∀ {Y : Set} {P : List Y → List Y → Set}
      {As As' Bs Bs' : List Y}
      (p : As ≡ As') (q : Bs ≡ Bs')
      (G : P As Bs)
  → subst₂ P (sym p) refl (subst₂ P p q G) ≡ subst₂ P refl q G
subst₂-cancel-sym-l refl refl G = refl

-- `subst₂ p refl (subst₂ (sym p) refl X) ≡ X`
subst₂-cancel-sym-r
  : ∀ {Y : Set} {P : List Y → List Y → Set}
      {As As' Bs : List Y}
      (p : As ≡ As') (X : P As' Bs)
  → subst₂ P p refl (subst₂ P (sym p) refl X) ≡ X
subst₂-cancel-sym-r refl X = refl

-- Collapse two nested `subst₂ refl _` on the cod into a single `trans`.
subst₂-trans-cod
  : ∀ {Y : Set} {P : List Y → List Y → Set}
      {As Bs Bs' Bs'' : List Y}
      (p : Bs ≡ Bs') (q : Bs' ≡ Bs'')
      (G : P As Bs)
  → subst₂ P refl q (subst₂ P refl p G)
  ≡ subst₂ P refl (trans p q) G
subst₂-trans-cod refl refl G = refl

-- General form: collapse two nested `subst₂` on both axes simultaneously.
-- `subst₂-trans-cod` is the `p₀ = p₀' = refl` specialisation.
subst₂-trans
  : ∀ {a b} {A : Set a} {B : Set b} {P : A → B → Set}
      {x₁ x₂ x₃ : A} {y₁ y₂ y₃ : B}
      (p : x₁ ≡ x₂) (p' : x₂ ≡ x₃)
      (q : y₁ ≡ y₂) (q' : y₂ ≡ y₃)
      (z : P x₁ y₁)
  → subst₂ P p' q' (subst₂ P p q z)
  ≡ subst₂ P (trans p p') (trans q q') z
subst₂-trans refl refl refl refl _ = refl

-- Cancel a `subst₂ (sym p) (sym q)` after `subst₂ p q`.  Subsumes
-- `subst₂-cancel-sym-l` and `subst₂-cancel-sym-r` by cancelling both
-- axes in one step.
subst₂-sym-subst₂
  : ∀ {a b} {A : Set a} {B : Set b} {P : A → B → Set}
      {x x' : A} {y y' : B}
      (p : x ≡ x') (q : y ≡ y') (z : P x y)
  → subst₂ P (sym p) (sym q) (subst₂ P p q z) ≡ z
subst₂-sym-subst₂ refl refl _ = refl

-- `subst₂ P refl refl x ≡ x` — actually definitional, but named for
-- expository use in proof chains.
subst₂-refl
  : ∀ {a b} {A : Set a} {B : Set b} {P : A → B → Set}
      {x : A} {y : B} (z : P x y)
  → subst₂ P refl refl z ≡ z
subst₂-refl _ = refl

-- `trans p refl ≡ p`.  The `trans refl eq ≡ eq` direction is
-- definitional; the right-reflexive case needs a pattern match.
trans-reflʳ
  : ∀ {a} {A : Set a} {x y : A} (p : x ≡ y) → trans p refl ≡ p
trans-reflʳ refl = refl

--------------------------------------------------------------------------------
-- Hypergraph-specific subst₂ bookkeeping.

-- `hTensor` factors a subst₂ out of its left argument's boundaries.
hTensor-subst₂-left
  : ∀ {As As' Bs Bs' Cs Ds : List X}
      (p : As ≡ As') (q : Bs ≡ Bs')
      (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
  → hTensor (subst₂ (Hypergraph FlatGen) p q X₀) Y₀
  ≡ subst₂ (Hypergraph FlatGen) (cong (_++ Cs) p) (cong (_++ Ds) q)
           (hTensor X₀ Y₀)
hTensor-subst₂-left refl refl X₀ Y₀ = refl

-- `hTensor` factors a subst₂ out of its right argument's boundaries.
hTensor-subst₂-right
  : ∀ {As Bs Cs Cs' Ds Ds' : List X}
      (p : Cs ≡ Cs') (q : Ds ≡ Ds')
      (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
  → hTensor X₀ (subst₂ (Hypergraph FlatGen) p q Y₀)
  ≡ subst₂ (Hypergraph FlatGen) (cong (As ++_) p) (cong (Bs ++_) q)
           (hTensor X₀ Y₀)
hTensor-subst₂-right refl refl X₀ Y₀ = refl

-- `hComposeP` factors a `subst₂ refl _` out of its right argument.
hComposeP-cod-subst
  : ∀ {As Bs Cs Cs' : List X}
      (eq : Cs ≡ Cs')
      (G : Hypergraph FlatGen As Bs) (K : Hypergraph FlatGen Bs Cs)
  → hComposeP G (subst₂ (Hypergraph FlatGen) refl eq K)
  ≡ subst₂ (Hypergraph FlatGen) refl eq (hComposeP G K)
hComposeP-cod-subst refl G K = refl

-- Transport `Unique` across a subst₂ on the dom.
Unique-subst₂-dom
  : ∀ {As Bs As' Bs' : List X}
      (eq₁ : As ≡ As') (eq₂ : Bs ≡ Bs')
      (G : Hypergraph FlatGen As Bs)
  → Unique (Hypergraph.dom G)
  → Unique (Hypergraph.dom (subst₂ (Hypergraph FlatGen) eq₁ eq₂ G))
Unique-subst₂-dom refl refl G p = p
