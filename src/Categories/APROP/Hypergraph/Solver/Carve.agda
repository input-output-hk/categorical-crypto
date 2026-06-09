{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Context carving by term-level *focusing* (spike).
--
-- `rewriteH!` rewrites `lᵗ → rᵗ` inside the frame `post ∘ (id {k} ⊗ –) ∘ pre`.
-- This module *finds* that frame automatically for a single occurrence of the
-- redex inside a term `s`, by structural recursion to the redex subterm,
-- accumulating the surrounding context with explicit associator/unitor
-- insertions so the object types line up exactly.  All the up-to-SMC slack
-- (interchange, the α/λ noise we introduce) is absorbed by the downstream
-- `findIso` check — so `focusAt` is an *un*verified search, soundness still
-- resting solely on `findIso`/`rewriteH!`.
--
--     focusAt s lᵗ ≡ just (k , pre , post)
--   ⟹  s  is intended to satisfy  s ≈ post ∘ (id {k} ⊗ lᵗ) ∘ pre  (modulo SMC),
--       which a caller certifies with `findIso ⟪ s ⟫ ⟪ post ∘ (id{k}⊗lᵗ) ∘ pre ⟫`.
--
-- COVERAGE: handles a redex sitting under `∘` (either operand) and in either
-- factor of `⊗` — the right factor directly (`id ⊗ –`), the left factor by
-- routing the parallel wire past it with `σ`.  This is complete for redexes
-- *syntactically present* in `s` (with the rule's `P → Q` interface); redexes
-- hidden by global SMC rearrangement need the hypergraph (`subMatch`/`decode`)
-- route instead.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Carve (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟-ObjTerm_)
open import Categories.APROP using (module APROP)
open APROP sig

open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso sig-dec using (findIso)

--------------------------------------------------------------------------------
-- A focus result: the pad object `k` and the two context terms.

Foc : ObjTerm → ObjTerm → ObjTerm → ObjTerm → Set
Foc A B P Q = Σ ObjTerm λ k → HomTerm A (k ⊗₀ P) × HomTerm (k ⊗₀ Q) B

--------------------------------------------------------------------------------
-- Leaf: is the whole of `s` (up to hypergraph iso) the redex `lᵗ`?  If so the
-- frame is `λ⇒ ∘ (id {unit} ⊗ lᵗ) ∘ λ⇐` (pad `k = unit`).

leaf-try : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → Maybe (Foc A B P Q)
leaf-try {A} {B} {P} {Q} s lᵗ with A ≟-ObjTerm P | B ≟-ObjTerm Q
... | yes refl | yes refl with is-just (findIso ⟪ s ⟫ ⟪ lᵗ ⟫)
...   | true  = just (unit , λ⇐ , λ⇒)
...   | false = nothing
leaf-try _ _ | _ | _ = nothing

--------------------------------------------------------------------------------
-- Structural focusing.

focusAt : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → Maybe (Foc A B P Q)

-- Recurse into the two `∘` operands / the right `⊗` factor.
go : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → Maybe (Foc A B P Q)
go (g ∘ f) lᵗ with focusAt f lᵗ
... | just (k , pre , post) = just (k , pre , g ∘ post)        -- redex in f
... | nothing with focusAt g lᵗ
...   | just (k , pre , post) = just (k , pre ∘ f , post)      -- redex in g
...   | nothing               = nothing
go (_⊗₁_ {A₁} {_} {A₂} a b) lᵗ with focusAt b lᵗ
... | just (k , pre , post) =                                  -- redex in right factor
        just (A₁ ⊗₀ k , α⇐ ∘ (id {A₁} ⊗₁ pre) , (a ⊗₁ post) ∘ α⇒)
... | nothing with focusAt a lᵗ
...   | just (k , pre , post) =                                -- redex in left factor
          just ( k ⊗₀ A₂
               -- route A₂ (b's wire) left past P/Q with σ so lᵗ stays rightmost;
               -- `b` is absorbed into `post`.
               , α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ∘ (pre ⊗₁ id {A₂})
               , (post ⊗₁ b) ∘ α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ )
...   | nothing = nothing
go _ _ = nothing

focusAt s lᵗ with leaf-try s lᵗ
... | just r  = just r
... | nothing = go s lᵗ
