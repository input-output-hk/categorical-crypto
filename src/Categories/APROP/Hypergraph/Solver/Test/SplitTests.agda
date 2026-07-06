{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tests for the equation-splitting solver front-end `solveH!ˢ`
-- (`Categories.APROP.Hypergraph.Solver.Split`), in an arbitrary target SMC.
--
-- Signature: atoms a₀ a₁ a₂; generators p : a₀ → a₁, s : a₁ → a₂, and a
-- "context" generator w : a₂ ⊗₀ a₁ → a₂ ⊗₀ a₁ that composes on top of the
-- σ-naturality core  σ ∘ (p ⊗₁ s)  ≈  (s ⊗₁ p) ∘ σ  :  a₀ ⊗₀ a₁ → a₂ ⊗₀ a₁.
--
-- The tests exercise each path of the heuristic:
--   * pure refl peeling (syntactically equal sides; also a reassoc-only
--     variant where the sides differ just by `∘`-association),
--   * the wrapped benchmark shape (equal `w`-prefix peeled by congruence,
--     core solved by the fallback on the small window),
--   * a fallback-only goal (bare σ-naturality: the content crosses every
--     syntactic cut, so splitting cannot decompose it — the whole-term
--     solve must still discharge it).
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.APROP.Hypergraph.Solver.Test.SplitTests
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Product using (_×_; _,_)

open import Categories.APROP using (module APROP)
open import Categories.FreeMonoidal using (module FreeMonoidalHelper; Symm)
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSig
import Categories.APROP.Hypergraph.Solver.Frontend as Interp

private module C = SymmetricMonoidalCategory C

module SplitConfig (A₀ A₁ A₂ : C.Obj)
  (pᴹ : A₀ C.⇒ A₁) (sᴹ : A₁ C.⇒ A₂)
  (wᴹ : (A₂ C.⊗₀ A₁) C.⇒ (A₂ C.⊗₀ A₁))
  where

  open FreeMonoidalHelper Symm (Fin 3) using (ObjTerm; Var; _⊗₀_)

  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

  ⟦_⟧ᵖ₀ : Fin 3 → C.Obj
  ⟦ zero        ⟧ᵖ₀ = A₀
  ⟦ suc zero    ⟧ᵖ₀ = A₁
  ⟦ suc (suc _) ⟧ᵖ₀ = A₂

  -- p : a₀ → a₁, s : a₁ → a₂, w : a₂ ⊗₀ a₁ → a₂ ⊗₀ a₁.
  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = a₁ , a₂
  arity (suc (suc _)) = (a₂ ⊗₀ a₁) , (a₂ ⊗₀ a₁)

  module FS = FinSig _≟F_ arity
  module S = APROP FS.finSig
  module IM = Interp FS.finSigDec
  module OI = IM.ObjInterp C ⟦_⟧ᵖ₀

  ⟦gen⟧ : (i : Fin 3) → OI.⟦ FS.dom i ⟧₀ C.⇒ OI.⟦ FS.cod i ⟧₀
  ⟦gen⟧ zero          = pᴹ
  ⟦gen⟧ (suc zero)    = sᴹ
  ⟦gen⟧ (suc (suc _)) = wᴹ

  open IM using (module Solver)
  open Solver C ⟦_⟧ᵖ₀ (FS.genElim ⟦gen⟧)
  open Tgt

  private
    p s w : S.HomTerm _ _
    p = S.Agen (FS.gen zero)
    s = S.Agen (FS.gen (suc zero))
    w = S.Agen (FS.gen (suc (suc zero)))

    lhs-core rhs-core : S.HomTerm (a₀ S.⊗₀ a₁) (a₂ S.⊗₀ a₁)
    lhs-core = S.σ S.∘ (p S.⊗₁ s)
    rhs-core = (s S.⊗₁ p) S.∘ S.σ

  -- (a) Pure refl: both sides syntactically identical — discharged by
  -- `eq?` alone, no solver call.
  test-refl : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ σ ∘ (pᴹ ⊗₁ sᴹ)
  test-refl = solveH!ˢ lhs-core lhs-core

  -- (a') Refl after reassociation: the sides differ only in the nesting of
  -- `∘`; `reassoc` makes them syntactically equal, so again no solver call.
  test-reassoc-refl : (wᴹ ∘ σ) ∘ (pᴹ ⊗₁ sᴹ) ≈ wᴹ ∘ (σ ∘ (pᴹ ⊗₁ sᴹ))
  test-reassoc-refl = solveH!ˢ ((w S.∘ S.σ) S.∘ (p S.⊗₁ s))
                               (w S.∘ (S.σ S.∘ (p S.⊗₁ s)))

  -- (b) The benchmark shape: σ-naturality core under two equal `w`
  -- wrappers.  The wrappers are peeled by refl + `∘`-congruence; only the
  -- small core window reaches the hypergraph solver.
  test-wrapped : wᴹ ∘ (wᴹ ∘ (σ ∘ (pᴹ ⊗₁ sᴹ))) ≈ wᴹ ∘ (wᴹ ∘ ((sᴹ ⊗₁ pᴹ) ∘ σ))
  test-wrapped = solveH!ˢ (w S.∘ (w S.∘ lhs-core)) (w S.∘ (w S.∘ rhs-core))

  -- (c) Fallback-only: bare σ-naturality.  The two sides are `∘` with
  -- different middle objects (a₁ ⊗₀ a₂ vs a₁ ⊗₀ a₀), so splitting cannot
  -- decompose the goal; the whole-term fallback must solve it.
  test-fallback : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-fallback = solveH!ˢ lhs-core rhs-core
