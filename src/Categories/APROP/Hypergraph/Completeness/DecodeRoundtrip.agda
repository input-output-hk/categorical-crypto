{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Phase 3.5f Step 5 — `decode-roundtrip` by induction on the term.
--
-- Given the constructive definition of `decode` (= `proj₁` of
-- `decode-attempt-Linear`, which is itself constructive by induction
-- on the term), we prove
--
--   decode-roundtrip : ∀ f → decode f ≈Term bridge f
--
-- by structural induction on `f`.  Each branch dispatches to a
-- *postulated* per-constructor lemma `decode-roundtrip-X` that
-- captures how `decode` commutes with the constructor `X` modulo the
-- `unflatten-flatten-≈` coherence iso.  The composite cases (`_∘_`,
-- `_⊗₁_`) take the inductive hypotheses as arguments, so future work
-- discharging the postulates retains the recursive structure for
-- free.
--
-- Each per-case postulate is the natural target of Step 4's
-- compositional analysis of `decode` on the corresponding smart
-- constructor of `FromAPROP`; discharging them is left for follow-up.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; bridge)

--------------------------------------------------------------------------------
-- Per-constructor roundtrip lemmas.  Each postulate captures one
-- branch of the eventual constructive proof.

postulate
  decode-roundtrip-Agen
    : ∀ {A B} (g : mor A B) → decode (Agen g) ≈Term bridge (Agen g)

  decode-roundtrip-id
    : ∀ {A} → decode (id {A}) ≈Term bridge (id {A})

  decode-roundtrip-∘
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decode g ≈Term bridge g
    → decode f ≈Term bridge f
    → decode (g ∘ f) ≈Term bridge (g ∘ f)

  decode-roundtrip-⊗₁
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decode f ≈Term bridge f
    → decode g ≈Term bridge g
    → decode (f ⊗₁ g) ≈Term bridge (f ⊗₁ g)

  decode-roundtrip-λ⇒
    : ∀ {A} → decode (λ⇒ {A}) ≈Term bridge (λ⇒ {A})

  decode-roundtrip-λ⇐
    : ∀ {A} → decode (λ⇐ {A}) ≈Term bridge (λ⇐ {A})

  decode-roundtrip-ρ⇒
    : ∀ {A} → decode (ρ⇒ {A}) ≈Term bridge (ρ⇒ {A})

  decode-roundtrip-ρ⇐
    : ∀ {A} → decode (ρ⇐ {A}) ≈Term bridge (ρ⇐ {A})

  decode-roundtrip-α⇒
    : ∀ {A B C} → decode (α⇒ {A} {B} {C}) ≈Term bridge (α⇒ {A} {B} {C})

  decode-roundtrip-α⇐
    : ∀ {A B C} → decode (α⇐ {A} {B} {C}) ≈Term bridge (α⇐ {A} {B} {C})

  decode-roundtrip-σ
    : ∀ {A B} ⦃ s : Symm ≤ Symm ⦄
    → decode (σ {A = A} {B = B} ⦃ s ⦄) ≈Term bridge (σ {A = A} {B = B} ⦃ s ⦄)

--------------------------------------------------------------------------------
-- The roundtrip proof, by induction on the term.

decode-roundtrip
  : ∀ {A B} (f : HomTerm A B) → decode f ≈Term bridge f
decode-roundtrip (Agen g)         = decode-roundtrip-Agen g
decode-roundtrip id               = decode-roundtrip-id
decode-roundtrip (g ∘ f)          =
  decode-roundtrip-∘ g f (decode-roundtrip g) (decode-roundtrip f)
decode-roundtrip (f ⊗₁ g)         =
  decode-roundtrip-⊗₁ f g (decode-roundtrip f) (decode-roundtrip g)
decode-roundtrip λ⇒               = decode-roundtrip-λ⇒
decode-roundtrip λ⇐               = decode-roundtrip-λ⇐
decode-roundtrip ρ⇒               = decode-roundtrip-ρ⇒
decode-roundtrip ρ⇐               = decode-roundtrip-ρ⇐
decode-roundtrip α⇒               = decode-roundtrip-α⇒
decode-roundtrip α⇐               = decode-roundtrip-α⇐
decode-roundtrip (σ ⦃ s ⦄)        = decode-roundtrip-σ ⦃ s ⦄
