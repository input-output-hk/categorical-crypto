{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive discharge of `bridge-α⇒-form-⊗-⊗` from
-- `Completeness/DecodeRoundtrip.agda` (lines 1411-1416).
--
-- Phase 4 inductive case: A₁ = A₁₁ ⊗ A₁₂.
--
-- Goal:
--   bridge α⇒_{(A₁₁⊗A₁₂)⊗A₂, B, C}
--   ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
--                       (flatten B) (flatten C)
--
-- Strategy: a single well-founded recursion (`Worker.work`) on the number
-- of `⊗₀` nodes (`sz`) of the first object index.  The compound case
-- `((A₁₁⊗A₁₂)⊗A₂)` applies `pentagon-rewrite` to the bridge, distributes
-- via `bridge-∘`/`bridge-⊗`, and recurses on the strictly-smaller-`sz`
-- objects `A₁₁⊗A₁₂` (three times) and `A₂`; the α⇐ factor is derived
-- non-recursively (`derive-⇐`).  The residual bottoms out in a pure
-- list-level Mac-Lane coherence (`list-collapse-gen`, induction on the
-- prefix list).  Fully constructive — NO postulates.
--
-- This file is `--safe --with-K`-clean.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.BridgeAlphaFormCompound
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using ( bridge-∘
        ; bridge-⊗
        ; bridge-id-is-id
        ; α⇒-form-list
        ; α⇐-form-list
        ; α⇒-α⇐-iso
        ; α⇐-α⇒-iso
        ; α⇒-λ⇐-collapse
        ; pentagon-rewrite
        ; α⇐-comm-top
        ; λ⇐-naturality
        ; bridge-α⇒-form-Var
        ; bridge-α⇒-form-unit
        ; F-unit⊗-collapse
        ; T-unit⊗-collapse
        ; F-Vx⊗-collapse
        ; T-Vx⊗-collapse
        ; ≡⇒≈Term
        )

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Category.Monoidal using (Monoidal)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (m≤m+n; m≤n+m; n<1+n; +-identityʳ; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction.WellFounded using (Acc; acc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Local helpers re-proven (avoid depending on non-`--safe`
-- DecodeRoundtrip.agda).

-- `f ≡ g → f ≈Term g` is `≡⇒≈Term` from DecodeRoundtripSafe.

-- λ-cancel: (λ⇒ ⊗ id) ∘ (λ⇐ ⊗ (id ⊗ id)) ≈ id.
private
  λ-cancel
    : ∀ {X Y Z} → (λ⇒ {X} ⊗₁ id {Y ⊗₀ Z})
                   ∘ (λ⇐ {X} ⊗₁ (id {Y} ⊗₁ id {Z}))
                ≈Term id
  λ-cancel = begin
    (λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ (id ⊗₁ id))
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (λ⇒ ∘ λ⇐) ⊗₁ (id ∘ (id ⊗₁ id))
      ≈⟨ ⊗-resp-≈ λ⇒∘λ⇐≈id idˡ ⟩
    id ⊗₁ (id ⊗₁ id)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

  -- collapse-α-VAB: (α⇒ ⊗ id) ∘ (α⇐ ⊗ id) ≈ id.
  collapse-α-iso-⊗id
    : ∀ {X Y Z W : ObjTerm}
    → α⇒ {X} {Y} {Z} ⊗₁ id {W} ∘ α⇐ {X} {Y} {Z} ⊗₁ id {W} ≈Term id
  collapse-α-iso-⊗id = begin
    α⇒ ⊗₁ id ∘ α⇐ ⊗₁ id
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (α⇒ ∘ α⇐) ⊗₁ (id ∘ id)
      ≈⟨ ⊗-resp-≈ α⇒∘α⇐≈id idˡ ⟩
    id ⊗₁ id
      ≈⟨ id⊗id≈id ⟩
    id ∎

--------------------------------------------------------------------------------
-- F-decomp lemmas (re-proven since DecodeRoundtripSafe doesn't ship them).

private
  -- F-((unit⊗A)⊗(B⊗C)) ≈ F-(A⊗(B⊗C)) ∘ (λ⇒ ⊗ id).
  F-decomp-unit
    : ∀ A B C
    → _≅_.from (unflatten-flatten-≈ ((unit ⊗₀ A) ⊗₀ (B ⊗₀ C)))
    ≈Term _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C)))
          ∘ (λ⇒ {A} ⊗₁ id {B ⊗₀ C})
  F-decomp-unit A B C = begin
    c-A,BC-to ∘ ((λ⇒ ∘ id ⊗₁ F-A) ⊗₁ F-BC)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ λ⇒∘id⊗f≈f∘λ⇒ ≈-Term-refl ⟩
    c-A,BC-to ∘ ((F-A ∘ λ⇒) ⊗₁ F-BC)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idʳ) ⟩
    c-A,BC-to ∘ ((F-A ∘ λ⇒) ⊗₁ (F-BC ∘ id))
      ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
    c-A,BC-to ∘ (F-A ⊗₁ F-BC) ∘ (λ⇒ ⊗₁ id)
      ≈⟨ FM.sym-assoc ⟩
    (c-A,BC-to ∘ F-A ⊗₁ F-BC) ∘ (λ⇒ ⊗₁ id) ∎
    where
      F-A     = _≅_.from (unflatten-flatten-≈ A)
      F-BC    = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
      c-A,BC-to = _≅_.to (unflatten-++-≅ (flatten A) (flatten B ++ flatten C))

  -- T-(((unit⊗A)⊗B)⊗C) ≈ ((λ⇐ ⊗ id) ⊗ id) ∘ T-((A⊗B)⊗C).
  T-decomp-unit
    : ∀ A B C
    → _≅_.to (unflatten-flatten-≈ (((unit ⊗₀ A) ⊗₀ B) ⊗₀ C))
    ≈Term ((λ⇐ {A} ⊗₁ id {B}) ⊗₁ id {C})
          ∘ _≅_.to (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
  T-decomp-unit A B C = begin
    (((id ⊗₁ T-A ∘ λ⇐) ⊗₁ T-B ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ (⊗-resp-≈ (≈-Term-sym (λ⇐-naturality T-A)) ≈-Term-refl ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    (((λ⇐ ∘ T-A) ⊗₁ T-B ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    (((λ⇐ ∘ T-A) ⊗₁ (id ∘ T-B) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ (⊗-∘-dist ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    ((((λ⇐ ⊗₁ id) ∘ (T-A ⊗₁ T-B)) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ FM.assoc ≈-Term-refl ⟩∘⟨refl ⟩
    (((λ⇐ ⊗₁ id) ∘ (T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl ⟩
    (((λ⇐ ⊗₁ id) ∘ (T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ (id ∘ T-C)) ∘ c-AB,C-from
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    (((λ⇐ ⊗₁ id) ⊗₁ id) ∘ (((T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ T-C)) ∘ c-AB,C-from
      ≈⟨ FM.assoc ⟩
    ((λ⇐ ⊗₁ id) ⊗₁ id) ∘ (((T-A ⊗₁ T-B) ∘ c-A,B-from) ⊗₁ T-C) ∘ c-AB,C-from ∎
    where
      T-A         = _≅_.to (unflatten-flatten-≈ A)
      T-B         = _≅_.to (unflatten-flatten-≈ B)
      T-C         = _≅_.to (unflatten-flatten-≈ C)
      c-A,B-from  = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))
      c-AB,C-from = _≅_.from (unflatten-++-≅ (flatten A ++ flatten B) (flatten C))

  -- F-((Var x ⊗ A)⊗(B⊗C)) ≈ (id ⊗ F-(A⊗(B⊗C))) ∘ α⇒_{Var x, A, B⊗C}.
  F-decomp-Var
    : ∀ x A B C
    → _≅_.from (unflatten-flatten-≈ ((Var x ⊗₀ A) ⊗₀ (B ⊗₀ C)))
    ≈Term (id {Var x} ⊗₁ _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C))))
          ∘ α⇒ {Var x} {A} {B ⊗₀ C}
  F-decomp-Var x A B C = begin
    ((id ⊗₁ c-A,BC-to) ∘ α⇒-flat) ∘ F-V⊗A ⊗₁ F-BC
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (F-Vx⊗-collapse x A) ≈-Term-refl ⟩
    ((id ⊗₁ c-A,BC-to) ∘ α⇒-flat) ∘ (id ⊗₁ F-A) ⊗₁ F-BC
      ≈⟨ FM.assoc ⟩
    (id ⊗₁ c-A,BC-to) ∘ α⇒-flat ∘ (id ⊗₁ F-A) ⊗₁ F-BC
      ≈⟨ refl⟩∘⟨ α-comm ⟩
    (id ⊗₁ c-A,BC-to) ∘ id ⊗₁ (F-A ⊗₁ F-BC) ∘ α⇒-struct
      ≈⟨ FM.sym-assoc ⟩
    ((id ⊗₁ c-A,BC-to) ∘ id ⊗₁ (F-A ⊗₁ F-BC)) ∘ α⇒-struct
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
    (id ∘ id) ⊗₁ (c-A,BC-to ∘ F-A ⊗₁ F-BC) ∘ α⇒-struct
      ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩∘⟨refl ⟩
    id ⊗₁ (c-A,BC-to ∘ F-A ⊗₁ F-BC) ∘ α⇒-struct ∎
    where
      F-A       = _≅_.from (unflatten-flatten-≈ A)
      F-BC      = _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
      F-V⊗A     = _≅_.from (unflatten-flatten-≈ (Var x ⊗₀ A))
      c-A,BC-to = _≅_.to   (unflatten-++-≅ (flatten A) (flatten B ++ flatten C))
      α⇒-flat   = α⇒ {Var x} {unflatten (flatten A)}
                    {unflatten (flatten B ++ flatten C)}
      α⇒-struct = α⇒ {Var x} {A} {B ⊗₀ C}

  -- T-(((Var x ⊗ A)⊗B)⊗C) ≈ (α⇐_{V,A,B} ⊗ id) ∘ α⇐_{V,A⊗B,C} ∘ (id ⊗ T-((A⊗B)⊗C)).
  T-decomp-Var
    : ∀ x A B C
    → _≅_.to (unflatten-flatten-≈ (((Var x ⊗₀ A) ⊗₀ B) ⊗₀ C))
    ≈Term (α⇐ {Var x} {A} {B} ⊗₁ id {C})
          ∘ α⇐ {Var x} {A ⊗₀ B} {C}
          ∘ (id {Var x} ⊗₁ _≅_.to (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C)))
  T-decomp-Var x A B C = begin
    ((((ρ⇒ ⊗₁ T-A) ∘ α⇐-fl0 ∘ id ⊗₁ λ⇐) ⊗₁ T-B ∘ α⇐-fl1 ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-resp-≈ (⊗-resp-≈ (T-Vx⊗-collapse x A) ≈-Term-refl
                    ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
    ((((id ⊗₁ T-A) ⊗₁ T-B ∘ α⇐-fl1 ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from)
      ≈⟨ ⊗-resp-≈ FM.sym-assoc ≈-Term-refl ⟩∘⟨refl ⟩
    ((((id ⊗₁ T-A) ⊗₁ T-B) ∘ α⇐-fl1) ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-resp-≈ (≈-Term-sym (α⇐-comm-top id T-A T-B) ⟩∘⟨refl)
                  ≈-Term-refl ⟩∘⟨refl ⟩
    ((α⇐-A,B ∘ id ⊗₁ (T-A ⊗₁ T-B)) ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-resp-≈ FM.assoc ≈-Term-refl ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ id ⊗₁ (T-A ⊗₁ T-B) ∘ id ⊗₁ c-A,B-from)
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-resp-≈ (refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist) ≈-Term-refl ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ (id ∘ id) ⊗₁ ((T-A ⊗₁ T-B) ∘ c-A,B-from))
       ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-resp-≈ (refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl)
                  ≈-Term-refl ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ id ⊗₁ T-A⊗B) ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩∘⟨refl ⟩
    (α⇐-A,B ∘ id ⊗₁ T-A⊗B) ⊗₁ (id ∘ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    ((α⇐-A,B ⊗₁ id) ∘ (id ⊗₁ T-A⊗B) ⊗₁ T-C) ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ FM.assoc ⟩
    (α⇐-A,B ⊗₁ id) ∘ (id ⊗₁ T-A⊗B) ⊗₁ T-C ∘ α⇐-fl2 ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    (α⇐-A,B ⊗₁ id) ∘ ((id ⊗₁ T-A⊗B) ⊗₁ T-C ∘ α⇐-fl2) ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ refl⟩∘⟨ ≈-Term-sym (α⇐-comm-top id T-A⊗B T-C) ⟩∘⟨refl ⟩
    (α⇐-A,B ⊗₁ id) ∘ (α⇐-AB,C ∘ id ⊗₁ (T-A⊗B ⊗₁ T-C)) ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    (α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ id ⊗₁ (T-A⊗B ⊗₁ T-C) ∘ id ⊗₁ c-A⊗B,C-from
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ∘ id) ⊗₁ ((T-A⊗B ⊗₁ T-C) ∘ c-A⊗B,C-from)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    (α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ id ⊗₁ T-AB⊗C ∎
    where
      T-A          = _≅_.to   (unflatten-flatten-≈ A)
      T-B          = _≅_.to   (unflatten-flatten-≈ B)
      T-C          = _≅_.to   (unflatten-flatten-≈ C)
      T-A⊗B        = _≅_.to   (unflatten-flatten-≈ (A ⊗₀ B))
      T-AB⊗C       = _≅_.to   (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
      α⇐-fl0       = α⇐ {Var x} {unit} {unflatten (flatten A)}
      α⇐-fl1       = α⇐ {Var x} {unflatten (flatten A)} {unflatten (flatten B)}
      α⇐-fl2       = α⇐ {Var x} {unflatten (flatten A ++ flatten B)}
                       {unflatten (flatten C)}
      α⇐-A,B       = α⇐ {Var x} {A} {B}
      α⇐-AB,C      = α⇐ {Var x} {A ⊗₀ B} {C}
      c-A,B-from   = _≅_.from (unflatten-++-≅ (flatten A) (flatten B))
      c-A⊗B,C-from = _≅_.from (unflatten-++-≅ (flatten A ++ flatten B) (flatten C))

--------------------------------------------------------------------------------
-- The main lemma: bridge α⇒_{(A₁₁⊗A₁₂)⊗A₂, B, C}.
--
-- We give a single-recursion implementation by structural induction on A₁₁.
-- The recursion measure is the depth of A₁₁.
--
-- Base cases (A₁₁ = unit, A₁₁ = Var x): we directly apply the F/T decomp
-- lemmas and use chain manipulation to reach the form
-- `bridge α⇒_{A₁₂ ⊗ A₂, B, C}` (where we recursively use the dispatcher).
--
-- Inductive case (A₁₁ = A₁₁₁ ⊗ A₁₁₂): we use the pentagon at the leftmost
-- α⇒ to shift the bracketing, then recurse on A₁₁₁ (which is
-- structurally smaller).
--
-- For the dispatcher on the residual `bridge α⇒_{A₁₂ ⊗ A₂, B, C}`, we
-- need to handle the case where A₁₂ is itself compound — recursing back
-- to `bridge-α⇒-form-⊗-⊗`.  Termination follows from a careful joint
-- measure (TBD).

--------------------------------------------------------------------------------
-- Well-founded recursion measure: the number of `⊗₀` nodes in an object.
--
-- Every recursive call made by the α⇒-form dispatcher (including the
-- compound `A₁₁⊗A₁₂` case via `pentagon-rewrite`, and the α⇐ factor it
-- introduces) targets an object with *strictly smaller* `sz`.  In
-- particular the pentagon-rewrite of `α⇒_{(A₁₁⊗A₁₂)⊗A₂,B,C}` yields
-- sub-`α⇒`'s whose first index is `A₁₁⊗A₁₂` (a proper subtree of
-- `(A₁₁⊗A₁₂)⊗A₂`) or `A₂`, both of strictly smaller `sz`.  So a single
-- well-founded recursion on `sz` of the first object index discharges
-- the whole dispatcher.

sz : ObjTerm → ℕ
sz unit       = 0
sz (Var _)    = 0
sz (A ⊗₀ B)   = suc (sz A + sz B)

-- The two `sz`-decrease facts needed in the compound case.
--   sz ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂)
--     = suc (sz (A₁₁ ⊗₀ A₁₂) + sz A₂)
--     = suc (suc (sz A₁₁ + sz A₁₂) + sz A₂)  (definitionally)
private
  -- sz (A₁₁ ⊗₀ A₁₂) < sz ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂)
  --   i.e.  suc (sz A₁₁ + sz A₁₂) < suc (suc (sz A₁₁ + sz A₁₂) + sz A₂)
  sz-left< : ∀ A₁₁ A₁₂ A₂
           → sz (A₁₁ ⊗₀ A₁₂) < sz ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂)
  sz-left< A₁₁ A₁₂ A₂ =
    s≤s (m≤m+n (sz (A₁₁ ⊗₀ A₁₂)) (sz A₂))

  -- sz A₂ < sz ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂)
  --   i.e.  sz A₂ < suc (sz (A₁₁ ⊗₀ A₁₂) + sz A₂)
  sz-right< : ∀ A₁₁ A₁₂ A₂
            → sz A₂ < sz ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂)
  sz-right< A₁₁ A₁₂ A₂ =
    s≤s (m≤n+m (sz A₂) (sz (A₁₁ ⊗₀ A₁₂)))

--------------------------------------------------------------------------------
-- `derive-⇐`: the α⇐-form derived from the α⇒-form result at the SAME
-- object, via the α⇒/α⇐ iso (mirrors `bridge-α⇐-form` in
-- DecodeRoundtrip.agda).  Non-recursive: it takes the α⇒ result as an
-- explicit argument so it stays *outside* the well-founded recursion.

private
  bridge-resp-≈Term
    : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → bridge f ≈Term bridge g
  bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

  derive-⇐
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
      ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)
    → bridge (α⇐ {A} {B} {C})
      ≈Term α⇐-form-list (flatten A) (flatten B) (flatten C)
  derive-⇐ A B C br-α⇒ = begin
    bridge (α⇐ {A} {B} {C})
      ≈⟨ ≈-Term-sym idʳ ⟩
    bridge (α⇐ {A} {B} {C}) ∘ id
      ≈⟨ refl⟩∘⟨ ≈-Term-sym (α⇒-α⇐-iso (flatten A) (flatten B) (flatten C)) ⟩
    bridge (α⇐ {A} {B} {C}) ∘ (α⇒-form-list (flatten A) (flatten B) (flatten C)
                                ∘ α⇐-form-list (flatten A) (flatten B) (flatten C))
      ≈⟨ FM.sym-assoc ⟩
    (bridge (α⇐ {A} {B} {C}) ∘ α⇒-form-list (flatten A) (flatten B) (flatten C))
     ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ (refl⟩∘⟨ ≈-Term-sym br-α⇒) ⟩∘⟨refl ⟩
    (bridge (α⇐ {A} {B} {C}) ∘ bridge (α⇒ {A} {B} {C}))
     ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ ≈-Term-sym (bridge-∘ α⇐ α⇒) ⟩∘⟨refl ⟩
    bridge (α⇐ {A} {B} {C} ∘ α⇒ {A} {B} {C})
     ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ bridge-resp-≈Term α⇐∘α⇒≈id ⟩∘⟨refl ⟩
    bridge (id {(A ⊗₀ B) ⊗₀ C}) ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ bridge-id-is-id ((A ⊗₀ B) ⊗₀ C) ⟩∘⟨refl ⟩
    id ∘ α⇐-form-list (flatten A) (flatten B) (flatten C)
      ≈⟨ idˡ ⟩
    α⇐-form-list (flatten A) (flatten B) (flatten C) ∎

--------------------------------------------------------------------------------
-- `list-collapse-gen`: the pure list-level Mac-Lane coherence that the
-- compound `pentagon-rewrite` decomposition bottoms out in.  Proven by
-- induction on the prefix list `p` (= flatten (A₁₁ ⊗₀ A₁₂)).  Every step is
-- a unitor/associator/`⊗-∘-dist` rewrite (σ-free, box-free).

private
  cto : (as bs : List X) → HomTerm (unflatten as ⊗₀ unflatten bs) (unflatten (as ++ bs))
  cto as bs = _≅_.to (unflatten-++-≅ as bs)

  cfrom : (as bs : List X) → HomTerm (unflatten (as ++ bs)) (unflatten as ⊗₀ unflatten bs)
  cfrom as bs = _≅_.from (unflatten-++-≅ as bs)

  list-collapse-gen
    : ∀ (p a b c : List X)
    → α⇐-form-list p a (b ++ c)
        ∘ ( cto p (a ++ b ++ c)
          ∘ (id ⊗₁ α⇒-form-list a b c)
          ∘ cfrom p ((a ++ b) ++ c) )
        ∘ α⇒-form-list p (a ++ b) c
        ∘ ( cto (p ++ a ++ b) c
          ∘ (α⇒-form-list p a b ⊗₁ id)
          ∘ cfrom ((p ++ a) ++ b) c )
      ≈Term α⇒-form-list (p ++ a) b c
  -- Base case p = []:  all `α…-form-list [] …` are `id`; `cto [] = λ⇒`,
  -- `cfrom [] = λ⇐`.  The two unitor frames cancel, leaving α⇒-form-list a b c.
  list-collapse-gen [] a b c = begin
    α⇐-form-list [] a (b ++ c)
      ∘ ( cto [] (a ++ b ++ c)
        ∘ (id ⊗₁ α⇒-form-list a b c)
        ∘ cfrom [] ((a ++ b) ++ c) )
      ∘ α⇒-form-list [] (a ++ b) c
      ∘ ( cto (a ++ b) c
        ∘ (α⇒-form-list [] a b ⊗₁ id {unflatten c})
        ∘ cfrom (a ++ b) c )
      ≈⟨ idˡ ⟩
    ( λ⇒ ∘ (id ⊗₁ α⇒-form-list a b c) ∘ λ⇐ )
      ∘ id
      ∘ ( cto (a ++ b) c
        ∘ (id {unflatten (a ++ b)} ⊗₁ id {unflatten c})
        ∘ cfrom (a ++ b) c )
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    ( λ⇒ ∘ (id ⊗₁ α⇒-form-list a b c) ∘ λ⇐ )
      ∘ ( cto (a ++ b) c
        ∘ (id ⊗₁ id)
        ∘ cfrom (a ++ b) c )
      ≈⟨ λ-collapse (α⇒-form-list a b c) ⟩∘⟨ (refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl) ⟩
    α⇒-form-list a b c ∘ ( cto (a ++ b) c ∘ id ∘ cfrom (a ++ b) c )
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ idˡ) ⟩
    α⇒-form-list a b c ∘ ( cto (a ++ b) c ∘ cfrom (a ++ b) c )
      ≈⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-++-≅ (a ++ b) c) ⟩
    α⇒-form-list a b c ∘ id
      ≈⟨ idʳ ⟩
    α⇒-form-list a b c ∎
    where
      -- λ⇒ ∘ (id ⊗ f) ∘ λ⇐ ≈ f  (λ-naturality cancellation).
      λ-collapse : ∀ {Y Y'} (f : HomTerm Y Y') → λ⇒ ∘ (id ⊗₁ f) ∘ λ⇐ ≈Term f
      λ-collapse f = begin
        λ⇒ ∘ (id ⊗₁ f) ∘ λ⇐
          ≈⟨ FM.sym-assoc ⟩
        (λ⇒ ∘ (id ⊗₁ f)) ∘ λ⇐
          ≈⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
        (f ∘ λ⇒) ∘ λ⇐
          ≈⟨ FM.assoc ⟩
        f ∘ λ⇒ ∘ λ⇐
          ≈⟨ refl⟩∘⟨ λ⇒∘λ⇐≈id ⟩
        f ∘ id
          ≈⟨ idʳ ⟩
        f ∎

  -- Cons case p = x ∷ p':  peel `id{Var x} ⊗ _` from every factor (the
  -- form-lists already have that shape; the two c-iso framed groups M1/M2
  -- acquire it after cancelling the `α⇒/α⇐` introduced by `cto/cfrom (x∷_)`
  -- via `α-comm`).  Then `⊗-∘-dist` collects them and the IH finishes.
  list-collapse-gen (x ∷ p') a b c = begin
    α⇐-form-list (x ∷ p') a (b ++ c)
      ∘ ( cto (x ∷ p') (a ++ b ++ c)
        ∘ (idₚ ⊗₁ α⇒-form-list a b c)
        ∘ cfrom (x ∷ p') ((a ++ b) ++ c) )
      ∘ α⇒-form-list (x ∷ p') (a ++ b) c
      ∘ ( cto ((x ∷ p') ++ a ++ b) c
        ∘ (α⇒-form-list (x ∷ p') a b ⊗₁ id {unflatten c})
        ∘ cfrom (((x ∷ p') ++ a) ++ b) c )
      -- peel M1 and M2 to `id{Var x} ⊗ _`.
      ≈⟨ refl⟩∘⟨ peel-M1 ⟩∘⟨ refl⟩∘⟨ peel-M2 ⟩
    (id {Var x} ⊗₁ α⇐-form-list p' a (b ++ c))
      ∘ (id {Var x} ⊗₁ M1')
      ∘ (id {Var x} ⊗₁ α⇒-form-list p' (a ++ b) c)
      ∘ (id {Var x} ⊗₁ M2')
      -- collect the four `id{Var x} ⊗ _` via ⊗-∘-dist.
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-∘-dist-id ⟩
    (id {Var x} ⊗₁ α⇐-form-list p' a (b ++ c))
      ∘ (id {Var x} ⊗₁ M1')
      ∘ (id {Var x} ⊗₁ (α⇒-form-list p' (a ++ b) c ∘ M2'))
      ≈⟨ refl⟩∘⟨ ⊗-∘-dist-id ⟩
    (id {Var x} ⊗₁ α⇐-form-list p' a (b ++ c))
      ∘ (id {Var x} ⊗₁ (M1' ∘ α⇒-form-list p' (a ++ b) c ∘ M2'))
      ≈⟨ ⊗-∘-dist-id ⟩
    id {Var x} ⊗₁ ( α⇐-form-list p' a (b ++ c)
                  ∘ M1'
                  ∘ α⇒-form-list p' (a ++ b) c
                  ∘ M2' )
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (list-collapse-gen p' a b c) ⟩
    id {Var x} ⊗₁ α⇒-form-list (p' ++ a) b c ∎
    where
      Vx  = Var x
      P'  = unflatten p'
      idₚ = id {Vx ⊗₀ P'}
      αfl-abc = α⇒-form-list a b c

      M1' M2' : _
      M1' = cto p' (a ++ b ++ c)
          ∘ (id ⊗₁ αfl-abc)
          ∘ cfrom p' ((a ++ b) ++ c)
      M2' = cto (p' ++ a ++ b) c
          ∘ (α⇒-form-list p' a b ⊗₁ id {unflatten c})
          ∘ cfrom ((p' ++ a) ++ b) c

      -- `(id{Vx} ⊗ g) ∘ (id{Vx} ⊗ f) ≈ id{Vx} ⊗ (g ∘ f)`.
      ⊗-∘-dist-id : ∀ {Y₁ Y₂ Y₃} {g : HomTerm Y₂ Y₃} {f : HomTerm Y₁ Y₂}
                  → (id {Vx} ⊗₁ g) ∘ (id {Vx} ⊗₁ f) ≈Term id {Vx} ⊗₁ (g ∘ f)
      ⊗-∘-dist-id {g = g} {f} = begin
        (id ⊗₁ g) ∘ (id ⊗₁ f)
          ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
        (id ∘ id) ⊗₁ (g ∘ f)
          ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
        id ⊗₁ (g ∘ f) ∎

      -- α⇒_{Vx,P',W'} ∘ (id{Vx⊗P'} ⊗ f) ∘ α⇐_{Vx,P',W} ≈ id{Vx} ⊗ (id{P'} ⊗ f).
      α-slide
        : ∀ {W W'} (f : HomTerm W W')
        → α⇒ {Vx} {P'} {W'} ∘ (idₚ ⊗₁ f) ∘ α⇐ {Vx} {P'} {W}
          ≈Term id {Vx} ⊗₁ (id {P'} ⊗₁ f)
      α-slide f = begin
        α⇒ ∘ (idₚ ⊗₁ f) ∘ α⇐
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym id⊗id≈id) ≈-Term-refl ⟩∘⟨refl ⟩
        α⇒ ∘ ((id ⊗₁ id) ⊗₁ f) ∘ α⇐
          ≈⟨ FM.sym-assoc ⟩
        (α⇒ ∘ ((id ⊗₁ id) ⊗₁ f)) ∘ α⇐
          ≈⟨ α-comm ⟩∘⟨refl ⟩
        (id ⊗₁ (id ⊗₁ f) ∘ α⇒) ∘ α⇐
          ≈⟨ FM.assoc ⟩
        id ⊗₁ (id ⊗₁ f) ∘ α⇒ ∘ α⇐
          ≈⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩
        id ⊗₁ (id ⊗₁ f) ∘ id
          ≈⟨ idʳ ⟩
        id ⊗₁ (id ⊗₁ f) ∎

      peel-M1
        : cto (x ∷ p') (a ++ b ++ c)
          ∘ (idₚ ⊗₁ αfl-abc)
          ∘ cfrom (x ∷ p') ((a ++ b) ++ c)
          ≈Term id {Vx} ⊗₁ M1'
      peel-M1 = begin
        ((id ⊗₁ cto p' (a ++ b ++ c)) ∘ α⇒)
          ∘ (idₚ ⊗₁ αfl-abc)
          ∘ (α⇐ ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c)))
          ≈⟨ FM.assoc ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ α⇒
          ∘ (idₚ ⊗₁ αfl-abc)
          ∘ (α⇐ ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c)))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ α⇒
          ∘ ((idₚ ⊗₁ αfl-abc) ∘ α⇐)
          ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ (α⇒ ∘ ((idₚ ⊗₁ αfl-abc) ∘ α⇐))
          ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩∘⟨refl ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ ((α⇒ ∘ (idₚ ⊗₁ αfl-abc)) ∘ α⇐)
          ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩∘⟨refl ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ (α⇒ ∘ (idₚ ⊗₁ αfl-abc) ∘ α⇐)
          ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c))
          ≈⟨ refl⟩∘⟨ α-slide αfl-abc ⟩∘⟨refl ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ (id ⊗₁ (id ⊗₁ αfl-abc))
          ∘ (id ⊗₁ cfrom p' ((a ++ b) ++ c))
          ≈⟨ refl⟩∘⟨ ⊗-∘-dist-id ⟩
        (id ⊗₁ cto p' (a ++ b ++ c))
          ∘ (id ⊗₁ ((id ⊗₁ αfl-abc) ∘ cfrom p' ((a ++ b) ++ c)))
          ≈⟨ ⊗-∘-dist-id ⟩
        id {Vx} ⊗₁ M1' ∎

      peel-M2
        : cto ((x ∷ p') ++ a ++ b) c
          ∘ (α⇒-form-list (x ∷ p') a b ⊗₁ id {unflatten c})
          ∘ cfrom (((x ∷ p') ++ a) ++ b) c
          ≈Term id {Vx} ⊗₁ M2'
      peel-M2 = begin
        ((id ⊗₁ cto (p' ++ a ++ b) c) ∘ α⇒)
          ∘ ((id {Vx} ⊗₁ α⇒-form-list p' a b) ⊗₁ id {unflatten c})
          ∘ (α⇐ ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ FM.assoc ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ α⇒
          ∘ ((id {Vx} ⊗₁ α⇒-form-list p' a b) ⊗₁ id {unflatten c})
          ∘ (α⇐ ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ (α⇒ ∘ ((id {Vx} ⊗₁ α⇒-form-list p' a b) ⊗₁ id))
          ∘ (α⇐ ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ ((id ⊗₁ (α⇒-form-list p' a b ⊗₁ id)) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ (id ⊗₁ (α⇒-form-list p' a b ⊗₁ id))
          ∘ (α⇒ ∘ α⇐ ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ (id ⊗₁ (α⇒-form-list p' a b ⊗₁ id))
          ∘ ((α⇒ ∘ α⇐) ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ (id ⊗₁ (α⇒-form-list p' a b ⊗₁ id))
          ∘ (id ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ (id ⊗₁ (α⇒-form-list p' a b ⊗₁ id))
          ∘ (id ⊗₁ cfrom ((p' ++ a) ++ b) c)
          ≈⟨ refl⟩∘⟨ ⊗-∘-dist-id ⟩
        (id ⊗₁ cto (p' ++ a ++ b) c)
          ∘ (id ⊗₁ ((α⇒-form-list p' a b ⊗₁ id) ∘ cfrom ((p' ++ a) ++ b) c))
          ≈⟨ ⊗-∘-dist-id ⟩
        id {Vx} ⊗₁ M2' ∎

--------------------------------------------------------------------------------
-- The well-founded worker.  `work A B C ac` proves the α⇒-form for the
-- object `A`, given accessibility evidence `ac : Acc _<_ (sz A)`.  The
-- α⇐-form factor needed by the compound case is derived (non-recursively)
-- from `work` at the SAME object via the α⇒-α⇐ iso.

module Worker where

  -- The single well-founded worker.  Pattern-matches `A` to a depth that
  -- exposes the prefix shape, so that ALL recursive calls supply a
  -- structurally-smaller `Acc` (no lateral same-`Acc` hops, which the
  -- termination checker rejects).
  work
    : ∀ A B C → Acc _<_ (sz A)
    → bridge (α⇒ {A} {B} {C})
    ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)

--------------------------------------------------------------------------------
-- Definitions (inside the Worker module).

  work unit    B C ac = bridge-α⇒-form-unit B C
  work (Var x) B C ac = bridge-α⇒-form-Var x B C

  -- A₁ = unit: bridge α⇒_{unit ⊗ A₂, B, C} reduces via λ-machinery to
  -- bridge α⇒_{A₂, B, C}.
  work (unit ⊗₀ A₂) B C (acc rs) = begin
    bridge (α⇒ {unit ⊗₀ A₂} {B} {C})
      ≈⟨ F-decomp-unit A₂ B C ⟩∘⟨ refl⟩∘⟨ T-decomp-unit A₂ B C ⟩
    (F-A₂BC ∘ (λ⇒ ⊗₁ id)) ∘ α⇒-uA₂ ∘ (((λ⇐ ⊗₁ id) ⊗₁ id) ∘ T-A₂BC)
      ≈⟨ FM.assoc ⟩
    F-A₂BC ∘ (λ⇒ ⊗₁ id) ∘ α⇒-uA₂ ∘ ((λ⇐ ⊗₁ id) ⊗₁ id) ∘ T-A₂BC
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    F-A₂BC ∘ (λ⇒ ⊗₁ id) ∘ (α⇒-uA₂ ∘ ((λ⇐ ⊗₁ id) ⊗₁ id)) ∘ T-A₂BC
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
    F-A₂BC ∘ (λ⇒ ⊗₁ id) ∘ ((λ⇐ ⊗₁ (id ⊗₁ id)) ∘ α⇒-A₂) ∘ T-A₂BC
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    F-A₂BC ∘ ((λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ (id ⊗₁ id)) ∘ α⇒-A₂) ∘ T-A₂BC
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩∘⟨refl ⟩
    F-A₂BC ∘ (((λ⇒ ⊗₁ id) ∘ (λ⇐ ⊗₁ (id ⊗₁ id))) ∘ α⇒-A₂) ∘ T-A₂BC
      ≈⟨ refl⟩∘⟨ λ-cancel ⟩∘⟨refl ⟩∘⟨refl ⟩
    F-A₂BC ∘ (id ∘ α⇒-A₂) ∘ T-A₂BC
      ≈⟨ refl⟩∘⟨ idˡ ⟩∘⟨refl ⟩
    F-A₂BC ∘ α⇒-A₂ ∘ T-A₂BC
      ≈⟨ work A₂ B C (rs (n<1+n (sz A₂))) ⟩
    α⇒-form-list (flatten A₂) (flatten B) (flatten C) ∎
    where
      F-A₂BC  = _≅_.from (unflatten-flatten-≈ (A₂ ⊗₀ (B ⊗₀ C)))
      T-A₂BC  = _≅_.to   (unflatten-flatten-≈ ((A₂ ⊗₀ B) ⊗₀ C))
      α⇒-uA₂  = α⇒ {unit ⊗₀ A₂} {B} {C}
      α⇒-A₂   = α⇒ {A₂} {B} {C}

  -- A₁ = Var x: similar, but with Var x prefix.
  work (Var x ⊗₀ A) B C (acc rs) = begin
    bridge (α⇒ {Var x ⊗₀ A} {B} {C})
      ≈⟨ F-decomp-Var x A B C ⟩∘⟨ refl⟩∘⟨ T-decomp-Var x A B C ⟩
    ((id ⊗₁ F-ABC) ∘ α⇒-V,A,BC) ∘ α⇒-V⊗A ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ FM.assoc ⟩
    (id ⊗₁ F-ABC) ∘ α⇒-V,A,BC ∘ α⇒-V⊗A ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    (id ⊗₁ F-ABC) ∘ (α⇒-V,A,BC ∘ α⇒-V⊗A) ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ refl⟩∘⟨ pentagon-V ⟩∘⟨refl ⟩
    (id ⊗₁ F-ABC) ∘ (id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id)
                   ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ refl⟩∘⟨ FM.assoc ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ (α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id)
                   ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id
                   ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘
      (α⇒-V,A,B ⊗₁ id ∘ (α⇐-A,B ⊗₁ id)) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ collapse-α-VAB ⟩∘⟨refl ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ id ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ (α⇒-V,AB,C ∘ α⇐-AB,C) ∘ (id ⊗₁ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ id ∘ (id ⊗₁ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ α⇒-A,B,C ∘ (id ⊗₁ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ⊗₁ F-ABC) ∘ (id ∘ id) ⊗₁ (α⇒-A,B,C ∘ T-AB⊗C)
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    (id ⊗₁ F-ABC) ∘ id ⊗₁ (α⇒-A,B,C ∘ T-AB⊗C)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C)
      ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    id ⊗₁ (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (work A B C (rs (n<1+n (sz A)))) ⟩
    id ⊗₁ α⇒-form-list (flatten A) (flatten B) (flatten C) ∎
    where
      F-ABC      = _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C)))
      T-AB⊗C     = _≅_.to   (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
      α⇒-V,A,BC  = α⇒ {Var x} {A} {B ⊗₀ C}
      α⇒-V⊗A     = α⇒ {Var x ⊗₀ A} {B} {C}
      α⇒-A,B,C   = α⇒ {A} {B} {C}
      α⇒-V,AB,C  = α⇒ {Var x} {A ⊗₀ B} {C}
      α⇒-V,A,B   = α⇒ {Var x} {A} {B}
      α⇐-A,B     = α⇐ {Var x} {A} {B}
      α⇐-AB,C    = α⇐ {Var x} {A ⊗₀ B} {C}

      -- The pentagon (from FreeMonoidal directly).
      pentagon-V : α⇒-V,A,BC ∘ α⇒-V⊗A
                 ≈Term id ⊗₁ α⇒-A,B,C ∘ α⇒-V,AB,C ∘ α⇒-V,A,B ⊗₁ id
      pentagon-V = ≈-Term-sym pentagon

      collapse-α-VAB
        : α⇒-V,A,B ⊗₁ id {C} ∘ α⇐-A,B ⊗₁ id {C} ≈Term id
      collapse-α-VAB = collapse-α-iso-⊗id

  -- A₁ = A₁₁ ⊗ A₁₂: the genuinely compound case, by `pentagon-rewrite` +
  -- `bridge-∘` + recursion on strictly-smaller-`sz` objects.
  work ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂) B C (acc rs) = compound-body
    where
      P  = A₁₁ ⊗₀ A₁₂
      p  = flatten A₁₁ ++ flatten A₁₂   -- = flatten P

      -- The four bridges produced by `pentagon-rewrite`.  Recursive calls
      -- pass the sub-accessibility evidence `rs (…)` INLINE so the
      -- termination checker sees them as structural sub-components of the
      -- input `acc rs`.
      br-⇐ : bridge (α⇐ {P} {A₂} {B ⊗₀ C})
           ≈Term α⇐-form-list p (flatten A₂) (flatten B ++ flatten C)
      br-⇐ = derive-⇐ P A₂ (B ⊗₀ C)
               (work P A₂ (B ⊗₀ C) (rs (sz-left< A₁₁ A₁₂ A₂)))

      br-mid : bridge (α⇒ {P} {A₂ ⊗₀ B} {C})
             ≈Term α⇒-form-list p (flatten A₂ ++ flatten B) (flatten C)
      br-mid = work P (A₂ ⊗₀ B) C (rs (sz-left< A₁₁ A₁₂ A₂))

      br-low : bridge (α⇒ {P} {A₂} {B})
             ≈Term α⇒-form-list p (flatten A₂) (flatten B)
      br-low = work P A₂ B (rs (sz-left< A₁₁ A₁₂ A₂))

      br-A₂ : bridge (α⇒ {A₂} {B} {C})
            ≈Term α⇒-form-list (flatten A₂) (flatten B) (flatten C)
      br-A₂ = work A₂ B C (rs (sz-right< A₁₁ A₁₂ A₂))

      compound-body
          : bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
          ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                              (flatten B) (flatten C)
      compound-body = begin
        bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
          ≈⟨ bridge-resp-≈Term pentagon-rewrite ⟩
        bridge ( α⇐ {P} {A₂} {B ⊗₀ C}
               ∘ id {P} ⊗₁ α⇒ {A₂} {B} {C}
               ∘ α⇒ {P} {A₂ ⊗₀ B} {C}
               ∘ α⇒ {P} {A₂} {B} ⊗₁ id {C} )
          ≈⟨ bridge-∘4 ⟩
        bridge (α⇐ {P} {A₂} {B ⊗₀ C})
          ∘ bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
          ∘ bridge (α⇒ {P} {A₂ ⊗₀ B} {C})
          ∘ bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
          ≈⟨ br-⇐ ⟩∘⟨ bx-mid ⟩∘⟨ br-mid ⟩∘⟨ bx-low ⟩
        α⇐-form-list p (flatten A₂) (flatten B ++ flatten C)
          ∘ ( c-to p (flatten A₂ ++ flatten B ++ flatten C)
            ∘ (id ⊗₁ α⇒-form-list (flatten A₂) (flatten B) (flatten C))
            ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C) )
          ∘ α⇒-form-list p (flatten A₂ ++ flatten B) (flatten C)
          ∘ ( c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
            ∘ (α⇒-form-list p (flatten A₂) (flatten B) ⊗₁ id)
            ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C) )
          ≈⟨ list-collapse ⟩
        α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                     (flatten B) (flatten C) ∎
        where
          c-to   = λ as bs → _≅_.to   (unflatten-++-≅ as bs)
          c-from = λ as bs → _≅_.from (unflatten-++-≅ as bs)

          -- bridge (id_P ⊗ α⇒_{A₂,B,C}) via bridge-⊗ + bridge-id + br-A₂.
          bx-mid
            : bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
            ≈Term c-to p (flatten A₂ ++ flatten B ++ flatten C)
                 ∘ (id ⊗₁ α⇒-form-list (flatten A₂) (flatten B) (flatten C))
                 ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C)
          bx-mid = begin
            bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
              ≈⟨ bridge-⊗ (id {P}) (α⇒ {A₂} {B} {C}) ⟩
            c-to p (flatten A₂ ++ flatten B ++ flatten C)
              ∘ (bridge (id {P}) ⊗₁ bridge (α⇒ {A₂} {B} {C}))
              ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C)
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (bridge-id-is-id P) br-A₂ ⟩∘⟨refl ⟩
            c-to p (flatten A₂ ++ flatten B ++ flatten C)
              ∘ (id ⊗₁ α⇒-form-list (flatten A₂) (flatten B) (flatten C))
              ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C) ∎

          -- bridge (α⇒_{P,A₂,B} ⊗ id_C) via bridge-⊗ + br-low + bridge-id.
          bx-low
            : bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
            ≈Term c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
                 ∘ (α⇒-form-list p (flatten A₂) (flatten B) ⊗₁ id)
                 ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C)
          bx-low = begin
            bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
              ≈⟨ bridge-⊗ (α⇒ {P} {A₂} {B}) (id {C}) ⟩
            c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
              ∘ (bridge (α⇒ {P} {A₂} {B}) ⊗₁ bridge (id {C}))
              ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C)
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ br-low (bridge-id-is-id C) ⟩∘⟨refl ⟩
            c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
              ∘ (α⇒-form-list p (flatten A₂) (flatten B) ⊗₁ id)
              ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C) ∎

          list-collapse
              : α⇐-form-list p (flatten A₂) (flatten B ++ flatten C)
                  ∘ ( c-to p (flatten A₂ ++ flatten B ++ flatten C)
                    ∘ (id ⊗₁ α⇒-form-list (flatten A₂) (flatten B) (flatten C))
                    ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C) )
                  ∘ α⇒-form-list p (flatten A₂ ++ flatten B) (flatten C)
                  ∘ ( c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
                    ∘ (α⇒-form-list p (flatten A₂) (flatten B) ⊗₁ id)
                    ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C) )
              ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                                  (flatten B) (flatten C)
          list-collapse = list-collapse-gen p (flatten A₂) (flatten B) (flatten C)

          -- bridge distributes over the 4-fold composite.
          bridge-∘4
            : bridge ( α⇐ {P} {A₂} {B ⊗₀ C}
                     ∘ id {P} ⊗₁ α⇒ {A₂} {B} {C}
                     ∘ α⇒ {P} {A₂ ⊗₀ B} {C}
                     ∘ α⇒ {P} {A₂} {B} ⊗₁ id {C} )
            ≈Term bridge (α⇐ {P} {A₂} {B ⊗₀ C})
                ∘ bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
                ∘ bridge (α⇒ {P} {A₂ ⊗₀ B} {C})
                ∘ bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
          bridge-∘4 = begin
            bridge (f0 ∘ f1 ∘ f2 ∘ f3)
              ≈⟨ bridge-∘ f0 (f1 ∘ f2 ∘ f3) ⟩
            bridge f0 ∘ bridge (f1 ∘ f2 ∘ f3)
              ≈⟨ refl⟩∘⟨ bridge-∘ f1 (f2 ∘ f3) ⟩
            bridge f0 ∘ bridge f1 ∘ bridge (f2 ∘ f3)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ bridge-∘ f2 f3 ⟩
            bridge f0 ∘ bridge f1 ∘ bridge f2 ∘ bridge f3 ∎
            where
              f0 = α⇐ {P} {A₂} {B ⊗₀ C}
              f1 = id {P} ⊗₁ α⇒ {A₂} {B} {C}
              f2 = α⇒ {P} {A₂ ⊗₀ B} {C}
              f3 = α⇒ {P} {A₂} {B} ⊗₁ id {C}

--------------------------------------------------------------------------------
-- Public entry point: discharge the original residual via `<-wellFounded`.

bridge-α⇒-form-⊗-⊗
  : ∀ A₁₁ A₁₂ A₂ B C
  → bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
  ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                      (flatten B) (flatten C)
bridge-α⇒-form-⊗-⊗ A₁₁ A₁₂ A₂ B C =
  Worker.work ((A₁₁ ⊗₀ A₁₂) ⊗₀ A₂) B C (<-wellFounded _)
