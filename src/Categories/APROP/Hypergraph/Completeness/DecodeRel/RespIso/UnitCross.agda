{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Unit-only atomic-cross-pair cases of `decode-rel-resp-≅ᴴ`.
--
-- At types involving only `unit`, `flatten T = []` and `unflatten [] =
-- unit`, so the `bridge` of an atomic constructor collapses to (a
-- chain ≈Term-equivalent to) `id`.  Each cross-pair of distinct atomic
-- constructors that has matching `HomTerm` types at unit-only
-- instantiations therefore reduces to `id ≈Term id`.
--
-- The iso hypothesis is unused; the conclusion holds unconditionally
-- by Kelly's coherence and the bridge-X-is-id lemmas in
-- DecodeRoundtrip.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.UnitCross
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; flatten; ⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅; unflatten-flatten-≈)

open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtrip sig
  using (bridge-id-is-id; bridge-λ⇒-is-id; bridge-λ⇐-is-id
       ; bridge-ρ⇒-form; bridge-ρ⇐-form)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₃; coherence-inv₃)
open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal
  using (module Symmetric)
open import Categories.Category.Monoidal.Braided.Properties
  (Symmetric.braided Symmetric-Monoidal)
  using (braiding-coherence)

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

--------------------------------------------------------------------------------
-- λ⇒ vs ρ⇒ at A = unit
--
-- Both have type `HomTerm (unit ⊗₀ unit) unit`.  bridge collapses both
-- to `id : HomTerm unit unit`.

-- bridge (ρ⇒ {unit}) ≈Term id, via the form lemma + coherence₃.
private
  bridge-ρ⇒-unit-is-id : bridge (ρ⇒ {unit}) ≈Term id
  bridge-ρ⇒-unit-is-id = begin
    bridge (ρ⇒ {unit})
      ≈⟨ bridge-ρ⇒-form unit ⟩
    ρ⇒ {unit} ∘ _≅_.from (unflatten-++-≅ [] [])
      ≈⟨ ≈-Term-sym coherence₃ ⟩∘⟨refl ⟩
    λ⇒ {unit} ∘ _≅_.from (unflatten-++-≅ [] [])
      ≈⟨ λ⇒∘λ⇐≈id ⟩
    id ∎

  bridge-ρ⇐-unit-is-id : bridge (ρ⇐ {unit}) ≈Term id
  bridge-ρ⇐-unit-is-id = begin
    bridge (ρ⇐ {unit})
      ≈⟨ bridge-ρ⇐-form unit ⟩
    _≅_.to (unflatten-++-≅ [] []) ∘ ρ⇐ {unit}
      ≈⟨ refl⟩∘⟨ ≈-Term-sym coherence-inv₃ ⟩
    _≅_.to (unflatten-++-≅ [] []) ∘ λ⇐ {unit}
      ≈⟨ λ⇒∘λ⇐≈id ⟩
    id ∎

decode-rel-resp-≅ᴴ-λ⇒-ρ⇒-unit
  : ⟪ λ⇒ {unit} ⟫ ≅ᴴ ⟪ ρ⇒ {unit} ⟫
  → decode-rel (λ⇒ {unit}) ≈Term decode-rel (ρ⇒ {unit})
decode-rel-resp-≅ᴴ-λ⇒-ρ⇒-unit _ = begin
  decode-rel (λ⇒ {unit})  ≈⟨ bridge-λ⇒-is-id unit ⟩
  id                      ≈⟨ bridge-ρ⇒-unit-is-id ⟨
  decode-rel (ρ⇒ {unit})  ∎

decode-rel-resp-≅ᴴ-ρ⇒-λ⇒-unit
  : ⟪ ρ⇒ {unit} ⟫ ≅ᴴ ⟪ λ⇒ {unit} ⟫
  → decode-rel (ρ⇒ {unit}) ≈Term decode-rel (λ⇒ {unit})
decode-rel-resp-≅ᴴ-ρ⇒-λ⇒-unit iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-λ⇒-ρ⇒-unit (sym-≅ᴴ iso))

--------------------------------------------------------------------------------
-- λ⇐ vs ρ⇐ at A = unit
--
-- Both have type `HomTerm unit (unit ⊗₀ unit)`.

decode-rel-resp-≅ᴴ-λ⇐-ρ⇐-unit
  : ⟪ λ⇐ {unit} ⟫ ≅ᴴ ⟪ ρ⇐ {unit} ⟫
  → decode-rel (λ⇐ {unit}) ≈Term decode-rel (ρ⇐ {unit})
decode-rel-resp-≅ᴴ-λ⇐-ρ⇐-unit _ = begin
  decode-rel (λ⇐ {unit})  ≈⟨ bridge-λ⇐-is-id unit ⟩
  id                      ≈⟨ bridge-ρ⇐-unit-is-id ⟨
  decode-rel (ρ⇐ {unit})  ∎

decode-rel-resp-≅ᴴ-ρ⇐-λ⇐-unit
  : ⟪ ρ⇐ {unit} ⟫ ≅ᴴ ⟪ λ⇐ {unit} ⟫
  → decode-rel (ρ⇐ {unit}) ≈Term decode-rel (λ⇐ {unit})
decode-rel-resp-≅ᴴ-ρ⇐-λ⇐-unit iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-λ⇐-ρ⇐-unit (sym-≅ᴴ iso))

--------------------------------------------------------------------------------
-- id vs σ at A = B = unit
--
-- Both have type `HomTerm (unit ⊗₀ unit) (unit ⊗₀ unit)`.
--
-- `bridge (id {unit ⊗₀ unit}) ≈Term id` via `bridge-id-is-id`.
-- `bridge (σ {unit}{unit}) ≈Term id` reduces — after using the
-- symmetric-monoidal coherence `σ {unit}{unit} ≈ id` (proved below) —
-- to `bridge (id) ≈Term id`.  The σ-collapse follows from Kelly's
-- `coherence₃ : λ⇒ ≈ ρ⇒` and the agda-categories
-- `braiding-coherence : λ⇒ ∘ σ ≈ ρ⇒` at unit, by cancelling the
-- iso λ⇒ on the left.

-- σ {unit}{unit} ≈Term id.  Proved from `braiding-coherence : λ⇒ ∘ σ ≈
-- ρ⇒` at unit, plus `coherence₃ : λ⇒ ≈ ρ⇒`, then cancelling λ⇒ on the
-- left.  Stated and proved at the default `v≤v` instance to match the
-- top-level `Symmetric-Monoidal` (also at `v≤v`); the parameterised
-- variant follows by `Symm≤Symm`-uniqueness (any two `s : Symm ≤ Symm`
-- are propositionally equal — they're all `v≤v`).
private
  σ-unit-unit-is-id-v≤v
    : σ {A = unit} {B = unit} ⦃ v≤v ⦄ ≈Term id
  σ-unit-unit-is-id-v≤v = begin
    σ {A = unit} {B = unit} ⦃ v≤v ⦄
      ≈⟨ idˡ ⟨
    id ∘ σ
      ≈⟨ ≈-Term-sym λ⇐∘λ⇒≈id ⟩∘⟨refl ⟩
    (λ⇐ ∘ λ⇒) ∘ σ
      ≈⟨ FM.assoc ⟩
    λ⇐ ∘ (λ⇒ ∘ σ)
      ≈⟨ refl⟩∘⟨ braiding-coherence ⟩
    λ⇐ ∘ ρ⇒
      ≈⟨ refl⟩∘⟨ ≈-Term-sym coherence₃ ⟩
    λ⇐ ∘ λ⇒
      ≈⟨ λ⇐∘λ⇒≈id ⟩
    id ∎

  -- Any `s : Symm ≤ Symm` is `v≤v`.
  Symm≤Symm-uniq : (s : Symm ≤ Symm) → s ≡ v≤v
  Symm≤Symm-uniq v≤v = refl

σ-unit-unit-is-id
  : ⦃ s : Symm ≤ Symm ⦄ → σ {A = unit} {B = unit} ⦃ s ⦄ ≈Term id
σ-unit-unit-is-id ⦃ s ⦄
  rewrite Symm≤Symm-uniq s = σ-unit-unit-is-id-v≤v

private
  bridge-σ-unit-is-id
    : ⦃ s : Symm ≤ Symm ⦄
    → bridge (σ {A = unit} {B = unit} ⦃ s ⦄) ≈Term id
  bridge-σ-unit-is-id ⦃ s ⦄ = begin
    bridge (σ {A = unit} {B = unit} ⦃ s ⦄)
      ≈⟨ refl⟩∘⟨ σ-unit-unit-is-id ⦃ s ⦄ ⟩∘⟨refl ⟩
    bridge (id {unit ⊗₀ unit})
      ≈⟨ bridge-id-is-id (unit ⊗₀ unit) ⟩
    id ∎

decode-rel-resp-≅ᴴ-id-σ-unit
  : ⦃ s : Symm ≤ Symm ⦄
  → ⟪ id {unit ⊗₀ unit} ⟫ ≅ᴴ ⟪ σ {A = unit} {B = unit} ⦃ s ⦄ ⟫
  → decode-rel (id {unit ⊗₀ unit})
  ≈Term decode-rel (σ {A = unit} {B = unit} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-id-σ-unit ⦃ s ⦄ _ = begin
  decode-rel (id {unit ⊗₀ unit})
    ≈⟨ bridge-id-is-id (unit ⊗₀ unit) ⟩
  id
    ≈⟨ bridge-σ-unit-is-id ⦃ s ⦄ ⟨
  decode-rel (σ {A = unit} {B = unit} ⦃ s ⦄)
    ∎

decode-rel-resp-≅ᴴ-σ-id-unit
  : ⦃ s : Symm ≤ Symm ⦄
  → ⟪ σ {A = unit} {B = unit} ⦃ s ⦄ ⟫ ≅ᴴ ⟪ id {unit ⊗₀ unit} ⟫
  → decode-rel (σ {A = unit} {B = unit} ⦃ s ⦄)
  ≈Term decode-rel (id {unit ⊗₀ unit})
decode-rel-resp-≅ᴴ-σ-id-unit ⦃ s ⦄ iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-id-σ-unit ⦃ s ⦄ (sym-≅ᴴ iso))
