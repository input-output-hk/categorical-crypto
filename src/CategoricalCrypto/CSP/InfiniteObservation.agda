{-# OPTIONS --safe --without-K --guardedness #-}

-- These are residual infinite FULL-LABEL streams, including τ. The finite weak
-- visible prefix and its residual run share an actual endpoint. This is strictly
-- more information than a set of ordinary infinite visible traces.
open import Data.Bool.Base
module CategoricalCrypto.CSP.InfiniteObservation (E B : Set) (sync : E → Bool) where

open import Data.Empty
open import Data.List.Base hiding (head; tail)
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.CSP.ExtensionalHiding as Extensional
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.Process as Core

module O = Operators E B sync
module L = Core E O.Index ⊤
module H = Extensional E B sync
open O
open L

record Labels : Set where
  coinductive
  field head : Label
        tail : Labels
open Labels

record Run (p : Tree) (u : Labels) : Set where
  coinductive
  field next : Tree
        step : p ─[ head u ]→ next
        rest : Run next (tail u)

Residual : Tree → List Visible → Labels → Set
Residual p xs u = Σ Tree (λ q → Executes p xs q × Run q u)

private variable
  p q hp hq t : Tree
  xs ys : List Visible
  u : Labels

module Mask (hide : E → Bool) where
  open H.Mask hide

  record AllSilent (u : Labels) : Set where
    coinductive
    field first : Silent (head u)
          later : AllSilent (tail u)

  record SourceStep (p hq : Tree) : Set where
    field label : Label
          next : Tree
          move : p ─[ label ]→ next
          related : Hides next hq
          silent-label : Silent label
  open SourceStep

  source-step : Hides p hp → hp ─[ τ ]→ hq → SourceStep p hq
  source-step rel step with silent-source rel step
  ... | old move next = record { label = τ; next = _; move = move; related = next; silent-label = tt }
  ... | concealed inside move next = record { label = visible (event _); next = _; move = move; related = next; silent-label = inside }

  labels : Hides p hp → Diverges hp → Labels
  head (labels rel d) = label (source-step rel (Diverges.step d))
  tail (labels rel d) = labels (related (source-step rel (Diverges.step d))) (Diverges.rest d)

  source-run : (rel : Hides p hp) (d : Diverges hp) → Run p (labels rel d)
  Run.next (source-run rel d) = next (source-step rel (Diverges.step d))
  Run.step (source-run rel d) = move (source-step rel (Diverges.step d))
  Run.rest (source-run rel d) = source-run (related (source-step rel (Diverges.step d))) (Diverges.rest d)

  source-silent : (rel : Hides p hp) (d : Diverges hp) → AllSilent (labels rel d)
  AllSilent.first (source-silent rel d) = silent-label (source-step rel (Diverges.step d))
  AllSilent.later (source-silent rel d) = source-silent (related (source-step rel (Diverges.step d))) (Diverges.rest d)

  silent-lift : ∀ {l} → Hides p hp → p ─[ l ]→ q → Silent l
    → Σ Tree (λ hq → hp ─[ τ ]→ hq × Hides q hq)
  silent-lift {l = τ} rel move inside = lift-silent rel move
  silent-lift {l = visible (event e)} rel move inside = proj₁ (lift-event rel move) inside
  silent-lift {l = visible (√ tt)} rel move ()

  hidden-run : Hides p hp → Run p u → AllSilent u → Diverges hp
  Diverges.next (hidden-run rel run all) = proj₁ (silent-lift rel (Run.step run) (AllSilent.first all))
  Diverges.step (hidden-run rel run all) = proj₁ (proj₂ (silent-lift rel (Run.step run) (AllSilent.first all)))
  Diverges.rest (hidden-run rel run all) = hidden-run
    (proj₂ (proj₂ (silent-lift rel (Run.step run) (AllSilent.first all))))
    (Run.rest run) (AllSilent.later all)

  divergences : (∀ {xs u} → Residual q xs u → Residual p xs u)
    → Divergence (Hide hide q) ys → Divergence (Hide hide p) ys
  divergences inclusion (t , path , d) with project hidden path
  ... | xs , q′ , source , eq , end with inclusion (q′ , source , source-run end d)
  ... | p′ , target , run with lift hidden target
  ... | hp′ , path′ , end′ = hp′ , subst (λ ys → Executes _ ys hp′) eq path′ , hidden-run end′ run (source-silent end d)

  residual-hiding : (∀ {xs} → Trace q xs → Trace p xs)
    → (∀ {xs X} → Failure q xs X → Failure p xs X)
    → (∀ {xs u} → Residual q xs u → Residual p xs u)
    → H.RawInclusion (Hide hide p) (Hide hide q)
  H.RawInclusion.traces (residual-hiding trace-inclusion failure-inclusion inclusion) = traces trace-inclusion
  H.RawInclusion.failures (residual-hiding trace-inclusion failure-inclusion inclusion) = failures failure-inclusion
  H.RawInclusion.divergences (residual-hiding trace-inclusion failure-inclusion inclusion) = divergences inclusion
