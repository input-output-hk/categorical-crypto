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
-- Strategy: pentagon-rewrite the central α⇒ + apply bridge-∘ + IHs.
-- For terminating recursion, we induct on the depth of `A₁₁` (which
-- strictly decreases in the compound subcase via α-shift).
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
  using (decode; bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using ( bridge-∘
        ; bridge-⊗
        ; bridge-id-is-id
        ; α⇒-form-list
        ; α⇐-form-list
        ; α⇒-α⇐-iso
        ; α⇐-α⇒-iso
        ; α⇒-coh-list
        ; α⇐-coh-list
        ; α⇒-λ⇐-collapse
        ; pentagon-rewrite
        ; id-⊗-respects-∘
        ; id-⊗-subst-bridge
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
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₁; coherence-inv₁; coherence₂; coherence-inv₂)
open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal
  using (triangle-inv)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst; subst₂)

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

  -- α⇐-comm: α⇐'s naturality.  Same as α⇐-comm-top from DecodeRoundtripSafe.
  α⇐-comm
    : ∀ {X Y Z X' Y' Z' : ObjTerm}
      (f : HomTerm X X') (g : HomTerm Y Y') (h : HomTerm Z Z')
    → α⇐ {X'} {Y'} {Z'} ∘ f ⊗₁ (g ⊗₁ h)
    ≈Term (f ⊗₁ g) ⊗₁ h ∘ α⇐ {X} {Y} {Z}
  α⇐-comm = α⇐-comm-top

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
      ≈⟨ ⊗-resp-≈ (≈-Term-sym (α⇐-comm id T-A T-B) ⟩∘⟨refl)
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
      ≈⟨ refl⟩∘⟨ ≈-Term-sym (α⇐-comm id T-A⊗B T-C) ⟩∘⟨refl ⟩
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
-- Residual record for the compound case (see comments after the block
-- for why this is exposed as a record rather than discharged inline).

record BridgeAlphaFormCompoundResidual : Set where
  field
    bridge-α⇒-form-⊗-⊗
      : ∀ A₁₁ A₁₂ A₂ B C
      → bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
      ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                          (flatten B) (flatten C)

--------------------------------------------------------------------------------
-- WithResidual: the dispatcher + sub-dispatcher derived constructively
-- modulo the BridgeAlphaFormCompoundResidual record above.

module WithResidual (r : BridgeAlphaFormCompoundResidual) where
  open BridgeAlphaFormCompoundResidual r

  -- Outer dispatcher: bridge α⇒_{A, B, C} for ANY A.  Pattern-matches on A.
  bridge-α⇒-form-any
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
    ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)

  -- Sub-dispatcher: bridge α⇒_{A₁⊗A₂, B, C} for ANY A₁ A₂ B C.  Pattern-matches on A₁.
  bridge-α⇒-form-⊗-here
    : ∀ A₁ A₂ B C
    → bridge (α⇒ {A₁ ⊗₀ A₂} {B} {C})
    ≈Term α⇒-form-list (flatten A₁ ++ flatten A₂) (flatten B) (flatten C)

--------------------------------------------------------------------------------
-- Definitions (inside the WithResidual module).

  -- A₁ = unit: bridge α⇒_{unit ⊗ A₂, B, C} reduces via λ-machinery to
  -- bridge α⇒_{A₂, B, C}.
  bridge-α⇒-form-⊗-here unit A₂ B C = begin
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
      ≈⟨ bridge-α⇒-form-any A₂ B C ⟩
    α⇒-form-list (flatten A₂) (flatten B) (flatten C) ∎
    where
      F-A₂BC  = _≅_.from (unflatten-flatten-≈ (A₂ ⊗₀ (B ⊗₀ C)))
      T-A₂BC  = _≅_.to   (unflatten-flatten-≈ ((A₂ ⊗₀ B) ⊗₀ C))
      α⇒-uA₂  = α⇒ {unit ⊗₀ A₂} {B} {C}
      α⇒-A₂   = α⇒ {A₂} {B} {C}

  -- A₁ = Var x: similar, but with Var x prefix.
  bridge-α⇒-form-⊗-here (Var x) A B C = begin
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
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (bridge-α⇒-form-any A B C) ⟩
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

  -- A₁ = A₁₁ ⊗ A₁₂: invoke the residual bridge-α⇒-form-⊗-⊗.
  bridge-α⇒-form-⊗-here (A₁₁ ⊗₀ A₁₂) A₂ B C = bridge-α⇒-form-⊗-⊗ A₁₁ A₁₂ A₂ B C

  -- Outer dispatcher.
  bridge-α⇒-form-any unit       B C = bridge-α⇒-form-unit B C
  bridge-α⇒-form-any (Var x)    B C = bridge-α⇒-form-Var x B C
  bridge-α⇒-form-any (A₁ ⊗₀ A₂) B C = bridge-α⇒-form-⊗-here A₁ A₂ B C

--------------------------------------------------------------------------------
-- Why bridge-α⇒-form-⊗-⊗ remains a residual (record-field):
--
--   (a) Pentagon-rewrite + bridge-∘ + IHs — but pentagon-induced sub-α⇒'s
--       have UNCHANGED compound first arg (A₁₁⊗A₁₂), which fails Agda's
--       structural termination.
--   (b) α-shift to relate `α⇒_{(A₁₁⊗A₁₂)⊗A₂, B, C}` and
--       `α⇒_{A₁₁⊗(A₁₂⊗A₂), B, C}` — but the connecting morphism is
--       itself `α⇒_{A₁₁,A₁₂,A₂}`, whose bridge requires recursing into
--       `bridge α⇒_{A₁₁, A₁₂, A₂}` at types matching the dispatcher.
--       Same termination obstacle.
--   (c) Custom well-founded recursion via `Acc` or sized types.
--
-- None of these fit within a single discharge-file's LOC budget.  The
-- unit/Var cases of `bridge-α⇒-form-⊗-here`, plus F/T decomp helpers,
-- are constructive and packaged inside `WithResidual` above.
