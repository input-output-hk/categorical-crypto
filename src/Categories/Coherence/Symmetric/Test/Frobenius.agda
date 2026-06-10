{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Showcase: Frobenius algebras (TensorRocq §5, arXiv:2604.17592).
--
-- A Frobenius algebra is a monoid `m : a ⊗ a → a`, `u : unit → a` and a
-- comonoid `n : a → a ⊗ a`, `v : a → unit` on the same object, subject to the
-- Frobenius law relating them.  The law has three equivalent formulations:
--
--   (frob)   (1 ⊗ m) ∘ α⇒ ∘ (n ⊗ 1)  ≈  (m ⊗ 1) ∘ α⇐ ∘ (1 ⊗ n)
--   (frobL)  (1 ⊗ m) ∘ α⇒ ∘ (n ⊗ 1)  ≈  n ∘ m
--   (frobR)  (m ⊗ 1) ∘ α⇐ ∘ (1 ⊗ n)  ≈  n ∘ m
--
-- Taking (frob) plus the unit and associativity laws as hypotheses, we DERIVE
-- frobL and frobR — the paper's worked example, transcribed as a chain of
-- `rewriteDeep!` steps.  Each step rewrites one rule occurrence (located on
-- the hypergraph, so interchange/associativity placement is irrelevant) and
-- then re-states the result as a clean intermediate diagram via `solveH!` —
-- the paper's `srw …; smcat` rhythm.
--
-- The derivation of frobL, with wires drawn left → right (inputs x, y):
--
--   X  = (1⊗m) ∘ α⇒ ∘ (n⊗1)            n splits x; m merges (x₂, y)
--    ↑ unitL                            (step₁, applied right-to-left)
--   T₁ : u creates w; n splits x; out = (m(w,x₁) , m(x₂,y))
--    ↓ frob, right-to-left              (step₂: the (w,x)-subdiagram is
--   T₂ : n splits w;                     frob's RHS; replace by its LHS)
--        out = (w₁ , m(m(w₂,x),y))
--    ↓ assoc                            (step₃)
--   T₃ : out = (w₁ , m(w₂, m(x,y)))
--    ↓ frob, left-to-right              (step₄: now the (w, m(x,y))-
--   T₄ : z = m(x,y); n splits z;         subdiagram is frob's LHS)
--        out = (m(w,z₁) , z₂)
--    ↓ unitL                            (step₅: m(w,z₁) with w = u())
--   R  = n ∘ m
--
-- frobR is then one application of (frob) followed by frobL.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test.Frobenius
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Product using (_×_; _,_)

open import Categories.Coherence.Symmetric C

module FrobeniusAlgebra (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  (nᴹ : A C.⇒ (A C.⊗₀ A)) (vᴹ : A C.⇒ C.unit)
  where

  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ)

  a : ObjTerm
  a = Var zero

  ⟦_⟧ᵖ₀ : Fin 1 → C.Obj
  ⟦ _ ⟧ᵖ₀ = A

  arity : Fin 4 → ObjTerm × ObjTerm
  arity zero                = (a ⊗₀ a) , a        -- m
  arity (suc zero)          = unitᵗ , a           -- u
  arity (suc (suc zero))    = a , (a ⊗₀ a)        -- n
  arity (suc (suc (suc _))) = a , unitᵗ           -- v

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero                → mᴹ
    (suc zero)          → uᴹ
    (suc (suc zero))    → nᴹ
    (suc (suc (suc _))) → vᴹ)

  private
    m u n v : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))
    n = S.Agen (gen (suc (suc zero)))
    v = S.Agen (gen (suc (suc (suc zero))))

    -- The rules' free-SMC sides.
    unitLᵗ : S.HomTerm (unitᵗ S.⊗₀ a) a
    unitLᵗ = m S.∘ (u S.⊗₁ S.id)

    assocLᵗ assocRᵗ : S.HomTerm ((a S.⊗₀ a) S.⊗₀ a) a
    assocLᵗ = m S.∘ (m S.⊗₁ S.id)
    assocRᵗ = m S.∘ (S.id S.⊗₁ m) S.∘ S.α⇒

    Xᵗ Yᵗ : S.HomTerm (a S.⊗₀ a) (a S.⊗₀ a)
    Xᵗ = (S.id S.⊗₁ m) S.∘ S.α⇒ S.∘ (n S.⊗₁ S.id)
    Yᵗ = (m S.⊗₁ S.id) S.∘ S.α⇐ S.∘ (S.id S.⊗₁ n)

    -- The intermediate diagrams of the frobL derivation.
    T₁ T₂ T₃ T₄ : S.HomTerm (a S.⊗₀ a) (a S.⊗₀ a)
    T₁ = (m S.⊗₁ m) S.∘ S.α⇐ S.∘ (S.id S.⊗₁ S.α⇒)
           S.∘ (u S.⊗₁ (n S.⊗₁ S.id)) S.∘ S.λ⇐
    T₂ = (S.id S.⊗₁ m) S.∘ (S.id S.⊗₁ (m S.⊗₁ S.id)) S.∘ (S.id S.⊗₁ S.α⇐)
           S.∘ S.α⇒ S.∘ (n S.⊗₁ S.id) S.∘ (u S.⊗₁ S.id) S.∘ S.λ⇐
    T₃ = (S.id S.⊗₁ m) S.∘ (S.id S.⊗₁ (S.id S.⊗₁ m))
           S.∘ S.α⇒ S.∘ (n S.⊗₁ S.id) S.∘ (u S.⊗₁ S.id) S.∘ S.λ⇐
    T₄ = (m S.⊗₁ S.id) S.∘ S.α⇐ S.∘ (u S.⊗₁ n) S.∘ S.λ⇐ S.∘ m

  -- The Frobenius-algebra laws needed for the derivation, as hypotheses in
  -- `C`'s own vocabulary (`⟦_⟧₁` of the corresponding free terms,
  -- definitionally).
  module _
    (unitL  : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒)
    (assocH : mᴹ ∘ (mᴹ ⊗₁ id) ≈ mᴹ ∘ (id ⊗₁ mᴹ) ∘ α⇒)
    (frobH  : (id ⊗₁ mᴹ) ∘ α⇒ ∘ (nᴹ ⊗₁ id) ≈ (mᴹ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ nᴹ))
    where

    private
      -- One derivation step: fire a rule somewhere in `Tᵢ` (deep) and land
      -- directly on the stated clean diagram `Tᵢ₊₁` (`rewriteDeepTo!`).
      step₁ : ⟦ T₁ ⟧₁ C.≈ ⟦ Xᵗ ⟧₁
      step₁ = rewriteDeepTo! T₁ Xᵗ unitLᵗ S.λ⇒ 0 unitL

      step₂ : ⟦ T₁ ⟧₁ C.≈ ⟦ T₂ ⟧₁
      step₂ = rewriteDeepTo! T₁ T₂ Yᵗ Xᵗ 0 (C.Equiv.sym frobH)

      step₃ : ⟦ T₂ ⟧₁ C.≈ ⟦ T₃ ⟧₁
      step₃ = rewriteDeepTo! T₂ T₃ assocLᵗ assocRᵗ 0 assocH

      step₄ : ⟦ T₃ ⟧₁ C.≈ ⟦ T₄ ⟧₁
      step₄ = rewriteDeepTo! T₃ T₄ Xᵗ Yᵗ 0 frobH

      step₅ : ⟦ T₄ ⟧₁ C.≈ ⟦ n S.∘ m ⟧₁
      step₅ = rewriteDeepTo! T₄ (n S.∘ m) unitLᵗ S.λ⇒ 0 unitL

    frobL : (id ⊗₁ mᴹ) ∘ α⇒ ∘ (nᴹ ⊗₁ id) ≈ nᴹ ∘ mᴹ
    frobL =
      C.Equiv.trans (C.Equiv.sym step₁)
        (C.Equiv.trans step₂
          (C.Equiv.trans step₃
            (C.Equiv.trans step₄ step₅)))

    frobR : (mᴹ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ nᴹ) ≈ nᴹ ∘ mᴹ
    frobR = C.Equiv.trans (C.Equiv.sym frobH) frobL
