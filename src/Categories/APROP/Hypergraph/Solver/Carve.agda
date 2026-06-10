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
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc)
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
-- Enumerate *all* focus positions, in a fixed order: the whole-term (leaf)
-- match first, then — for `∘` — the right operand's positions before the left
-- operand's, and — for `⊗` — the right factor's before the left factor's.
-- The context-extension wrappers are exactly the per-position frame builders.

focusAll : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → List (Foc A B P Q)

go-all : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → List (Foc A B P Q)
go-all (g ∘ f) lᵗ =
     map (λ { (k , pre , post) → (k , pre , g ∘ post) }) (focusAll f lᵗ)   -- redex in f
  ++ map (λ { (k , pre , post) → (k , pre ∘ f , post) }) (focusAll g lᵗ)   -- redex in g
go-all (_⊗₁_ {A₁} {_} {A₂} a b) lᵗ =
     map (λ { (k , pre , post) →                                          -- right factor
            (A₁ ⊗₀ k , α⇐ ∘ (id {A₁} ⊗₁ pre) , (a ⊗₁ post) ∘ α⇒) })
         (focusAll b lᵗ)
  ++ map (λ { (k , pre , post) →                                          -- left factor
            -- route A₂ (b's wire) left past P/Q with σ so lᵗ stays rightmost;
            -- `b` is absorbed into `post`.
            ( k ⊗₀ A₂
            , α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ∘ (pre ⊗₁ id {A₂})
            , (post ⊗₁ b) ∘ α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ) })
         (focusAll a lᵗ)
go-all _ _ = []

focusAll s lᵗ with leaf-try s lᵗ
... | just r  = r ∷ go-all s lᵗ
... | nothing = go-all s lᵗ

--------------------------------------------------------------------------------
-- Indexed entry point: the `n`-th focus position (0-based, in the order above),
-- and `focusAt` as the first one.

lookupMaybe : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
lookupMaybe []       _       = nothing
lookupMaybe (x ∷ _)  zero    = just x
lookupMaybe (_ ∷ xs) (suc n) = lookupMaybe xs n

focusAtₙ : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → ℕ → Maybe (Foc A B P Q)
focusAtₙ s lᵗ n = lookupMaybe (focusAll s lᵗ) n

focusAt : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → Maybe (Foc A B P Q)
focusAt s lᵗ = focusAtₙ s lᵗ 0
