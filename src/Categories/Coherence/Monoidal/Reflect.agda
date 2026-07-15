{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A reflection  HomTerm → Diag  with soundness, for the free
-- monoidal-diagram normal form of `Categories.Coherence.Monoidal.Diagram`.
--
-- We work in the layered-composite wire fragment (M1): morphisms whose
-- source and target are already `wires`-shaped flat objects, built from
--   id, _∘_, var (box _), _⊗₁_,
-- captured by the inductive `WTerm n m` with embedding
-- `embed : WTerm n m → HomTerm (wires n) (wires m)`.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Reflect where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.FreeMonoidal
open import Categories.FreeStrictMonoidal
open import Categories.Coherence.Monoidal.Compare
open import Categories.Coherence.Monoidal.Normalize

module ReflectI {v : Variant} {X : Set} (E : WireEngine v) ⦃ _ : DecEq X ⦄ where

  open WireEngine E
  open DiagramI E
  open FreeMonoidalHelper v X using (ObjTerm; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor v X mor
  open ≈R

  open MonR Monoidal-FreeMonoidal using (_⟩⊗⟨_)

  --------------------------------------------------------------------------------
  -- M1 fragment: the wire-typed strict terms.
  --------------------------------------------------------------------------------
  -- `WTerm`/`boxʷ`/`idʷ`/`_∘ʷ_`/`_⊗ʷ_` are the free strict monoidal category on
  -- the wire generators `Mor`.
  open FreeStrictMonoidalHelper Mor public using (WTerm; boxʷ; idʷ; _∘ʷ_; _⊗ʷ_)

  embed : ∀ {n m} → WTerm n m → HomTerm (wires n) (wires m)
  embed (boxʷ g)  = ⟦ g ⟧ᵇ
  embed idʷ       = id
  embed (g ∘ʷ f)  = embed g ∘ embed f
  embed (_⊗ʷ_ {nl} {ml} s t) = merge ml ∘ (embed s ⊗₁ embed t) ∘ split nl

  --------------------------------------------------------------------------------
  -- Reflection of the wire fragment into Diag (M1).
  --
  --   id     →  empty diagram
  --   g ∘ f  →  reflect f ∘ᵈ reflect g
  --   box g  →  single-box layer
  --------------------------------------------------------------------------------

  reflect : ∀ {n m} → WTerm n m → Diag n m
  reflect idʷ      = []_ _
  reflect (g ∘ʷ f) = reflect f ∘ᵈ reflect g
  reflect (boxʷ g) = boxD g
  reflect (s ⊗ʷ t) = reflect s ⊗ᵈ reflect t

  -- soundness of the builders (`∘ᵈ-sound`/`boxSound`/`shiftL-sound`/
  -- `shiftR-sound`/`⊗ᵈ-sound`) is the `DiagSound` sub-module of `DiagramI`.
  open DiagSound

  --------------------------------------------------------------------------------
  -- THE REFLECTION SOUNDNESS THEOREM.
  --
  --   ⟦ reflect t ⟧  ≈Term  embed t
  --
  -- i.e. the reflected diagram equals the original wire-fragment morphism.
  -- Both endpoints are diagram indices, so the statement is cast-free.
  --------------------------------------------------------------------------------
  reflect-sound : ∀ {n m} (t : WTerm n m) → ⟦ reflect t ⟧ ≈Term embed t
  reflect-sound idʷ = ≈-Term-refl
  reflect-sound (g ∘ʷ f) = ∘ᵈ-sound (reflect f) (reflect g) ○ (reflect-sound g ⟩∘⟨ reflect-sound f)
  reflect-sound (boxʷ g) = boxSound g
  reflect-sound (s ⊗ʷ t) =
    ⊗ᵈ-sound (reflect s) (reflect t) ○ (refl⟩∘⟨ ((reflect-sound s ⟩⊗⟨ reflect-sound t) ⟩∘⟨refl))

--------------------------------------------------------------------------------
-- `DecideCore`: the shared wire-level DECISION ASSEMBLY.
--
-- Both front-ends' `decide?W`/`decideσ?` are byte-identical given a normalizer
-- `norm : ∀ {n m} (d : Diag n m) → Σ[ d' ] (⟦ d ⟧ ≈Term ⟦ d' ⟧)`: reflect both
-- sides to `Diag`, normalize each, decide normal-form equality, and chain the
-- reflect-soundness witnesses through the bridge.  The interface stays SEMANTIC
-- (the syntactic `_⤳D_` trace is discharged by `⤳D-sound` inside each
-- front-end's `norm`).  `norm` is passed as an ordinary FUNCTION
-- argument so the per-variant oracle (interchange / σσ-cancel / slides) stays in
-- each front-end's scope while the assembly lives here once.
--------------------------------------------------------------------------------
module DecideCore
  {v : Variant} {X : Set} (E : WireEngine v)
  ⦃ _ : DecEq X ⦄
  where

  open WireEngine E
  open DiagramI E
  open FreeMonoidalHelper.Mor v X mor
  open ≈R
  open ReflectI E
  open NormalizeI E
  open SortD
  open MR FreeMonoidal

  module SCmp = CompareI E

  -- the caller supplies decidable equality on the Σ-packaged generators
  -- (an instance, used only to build `_≟Diag_`) and a normalizer.
  module Decide
    ⦃ _ : DecEq SCmp.Gen ⦄
    (norm : ∀ {n m} (d : Diag n m) → Σ[ d' ∈ Diag n m ] (⟦ d ⟧ ≈Term ⟦ d' ⟧))
    where

    open SCmp.Decide

    -- reflect both sides, normalize each, decide normal-form equality; on a hit
    -- the two normal forms are equal (`≈NF⇒≡`), so the reflect-soundness and
    -- the normalizer's `≈Term` witnesses chain directly (no output casts).
    decideW : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideW {n} {m} f g with norm (reflect f) | norm (reflect g)
    ... | (df' , sndf) | (dg' , sndg) = case df' ≟Diag dg' of λ where
        (no  _)  → nothing
        (yes eq) → just (chain (≈NF⇒≡ eq))
      where
        chain : df' ≡ dg' → embed f ≈Term embed g
        chain refl = ⟺ (reflect-sound f) ○ sndf ○ ⟺ sndg ○ reflect-sound g
