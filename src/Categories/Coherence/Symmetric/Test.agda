{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Tests for the symmetric-monoidal coherence solver, built on the reusable
-- interface `Categories.Coherence.Symmetric`.
--
-- The module is parameterised by a target SMC `C` alone.  Each *configuration*
-- of atoms and generators lives in its own sub-module, parameterised by the
-- objects and morphisms of `C` interpreting them:
--
--   * `Cycle3`    — generators f,g,h forming a 3-cycle; the category /
--                   monoidal structural laws.
--   * `Braiding`  — symmetry-heavy, non-trivial string-diagram equalities.
--   * `Crossings` — f, h (one in/out) and a merge g (two in, one out); one
--                   braided diagram `σ ∘ (h ⊗ g) ∘ α⇒ ∘ σ ∘ (f ⊗ id)`
--                   re-expressed along a ten-step `HomReasoning` chain in `C`
--                   (folding f into g by interchange, swapping g and h), then
--                   discharged by the solver in one line.
--
-- Each test states a genuine equation between morphisms of `C` (via `Tgt`);
-- no `⟦_⟧₁` appears, because each `Tgt`-expression is *definitionally* the
-- interpretation of the corresponding free-SMC term, and each free-SMC term
-- is written exactly once (`solveH!` finds the witnessing hypergraph iso).
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Product using (_×_; _,_)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning

open import Categories.Coherence.Symmetric C

--------------------------------------------------------------------------------
-- A ready-made three-atom alphabet a₀ a₁ a₂ and its interpretation A₀ A₁ A₂.

module Atoms3 (A₀ A₁ A₂ : C.Obj) where
  open FreeMonoidalHelper Symm (Fin 3) using (ObjTerm; Var) public

  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

  ⟦_⟧ᵖ₀ : Fin 3 → C.Obj
  ⟦ zero        ⟧ᵖ₀ = A₀
  ⟦ suc zero    ⟧ᵖ₀ = A₁
  ⟦ suc (suc _) ⟧ᵖ₀ = A₂

--------------------------------------------------------------------------------
-- Configuration 1: generators f,g,h forming the 3-cycle a₀ → a₁ → a₂ → a₀.
-- The category and monoidal structural laws.

module Cycle3 (A₀ A₁ A₂ : C.Obj)
  (fᴹ : A₀ C.⇒ A₁) (gᴹ : A₁ C.⇒ A₂) (hᴹ : A₂ C.⇒ A₀)
  where

  open Atoms3 A₀ A₁ A₂

  -- Generator arities (source , target): f : a₀ → a₁, g : a₁ → a₂, h : a₂ → a₀.
  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = a₁ , a₂
  arity (suc (suc _)) = a₂ , a₀

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → fᴹ
    (suc zero)    → gᴹ
    (suc (suc _)) → hᴹ)

  private
    f g h : S.HomTerm _ _
    f = S.Agen (gen zero)
    g = S.Agen (gen (suc zero))
    h = S.Agen (gen (suc (suc zero)))

  test-idˡ : id ∘ fᴹ ≈ fᴹ
  test-idˡ = solveH! (S.id S.∘ f) f

  test-assoc : (hᴹ ∘ gᴹ) ∘ fᴹ ≈ hᴹ ∘ (gᴹ ∘ fᴹ)
  test-assoc = solveH! ((h S.∘ g) S.∘ f) (h S.∘ (g S.∘ f))

  test-⊗-∘-dist : (gᴹ ∘ fᴹ) ⊗₁ (fᴹ ∘ hᴹ) ≈ (gᴹ ⊗₁ fᴹ) ∘ (fᴹ ⊗₁ hᴹ)
  test-⊗-∘-dist = solveH! ((g S.∘ f) S.⊗₁ (f S.∘ h)) ((g S.⊗₁ f) S.∘ (f S.⊗₁ h))

  test-triangle : (id ⊗₁ λ⇒) ∘ α⇒ ≈ ρ⇒ {A₀} ⊗₁ id {A₁}
  test-triangle = solveH! ((S.id S.⊗₁ S.λ⇒) S.∘ S.α⇒) (S.ρ⇒ {a₀} S.⊗₁ S.id {a₁})

--------------------------------------------------------------------------------
-- Configuration 2: two *parallel* generators p, q : a₀ → a₁ and s : a₁ → a₂.
-- Non-trivial string-diagram equalities involving the symmetry.

module Braiding (A₀ A₁ A₂ : C.Obj)
  (pᴹ qᴹ : A₀ C.⇒ A₁) (sᴹ : A₁ C.⇒ A₂)
  where

  open Atoms3 A₀ A₁ A₂

  -- p, q : a₀ → a₁ (parallel), s : a₁ → a₂.
  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = a₀ , a₁
  arity (suc (suc _)) = a₁ , a₂

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → pᴹ
    (suc zero)    → qᴹ
    (suc (suc _)) → sᴹ)

  private
    p q s : S.HomTerm _ _
    p = S.Agen (gen zero)
    q = S.Agen (gen (suc zero))
    s = S.Agen (gen (suc (suc zero)))

  test-σ-invol : σ ∘ σ ≈ id {A₀ ⊗₀ A₁}
  test-σ-invol = solveH! (S.σ S.∘ S.σ) (S.id {a₀ S.⊗₀ a₁})

  test-σ-nat : σ ∘ (pᴹ ⊗₁ sᴹ) ≈ (sᴹ ⊗₁ pᴹ) ∘ σ
  test-σ-nat = solveH! (S.σ S.∘ (p S.⊗₁ s)) ((s S.⊗₁ p) S.∘ S.σ)

  test-σ-conj : σ ∘ (pᴹ ⊗₁ qᴹ) ∘ σ ≈ qᴹ ⊗₁ pᴹ
  test-σ-conj = solveH! (S.σ S.∘ (p S.⊗₁ q) S.∘ S.σ) (q S.⊗₁ p)

  test-hexagon
    : id ⊗₁ σ ∘ α⇒ ∘ σ ⊗₁ id ≈ α⇒ ∘ σ ∘ α⇒ {A₀} {A₁} {A₂}
  test-hexagon = solveH! (S.id S.⊗₁ S.σ S.∘ S.α⇒ S.∘ S.σ S.⊗₁ S.id)
                         (S.α⇒ S.∘ S.σ S.∘ S.α⇒ {a₀} {a₁} {a₂})

  test-σ-slide
    : σ ∘ ((sᴹ ∘ pᴹ) ⊗₁ id {A₂}) ≈ (id {A₂} ⊗₁ (sᴹ ∘ pᴹ)) ∘ σ
  test-σ-slide = solveH! (S.σ S.∘ ((s S.∘ p) S.⊗₁ S.id {a₂}))
                         ((S.id {a₂} S.⊗₁ (s S.∘ p)) S.∘ S.σ)

--------------------------------------------------------------------------------
-- Configuration 3: f, g, h with g a merge (two inputs, one output).
--   f : a₀ → a₁          (one in, one out)
--   g : a₂ ⊗ a₁ → a₀     (two in, one out)
--   h : a₁ → a₂          (one in, one out)
--
-- The diagram (read left → right, input a₀ ⊗ (a₁ ⊗ a₂)):
--
--   a₀ ─[f]─ a₁ ╲                  ╱─ a₁ ─[h]─ a₂ ─╮
--               ╲                ╱                  ╲
--   a₁ ──────────╳──────────────                     ╳─ a₀
--               ╱ ╲                                 ╱
--   a₂ ────────╱   ╲─ a₂ ─┐                        ╱ ╲─ a₂
--                         ├─[ g ]─ a₀ ────────────╯
--             (f's a₁) ───┘   g : a₂ ⊗ a₁ → a₀
--
--   f acts on the top wire; its output a₁ is braided down past the other two;
--   h acts on the freed middle wire; the merge g consumes the bottom a₂ wire
--   together with f's a₁; finally the h- and g-outputs are braided.  As a term:
--   `σ ∘ (h ⊗ g) ∘ α⇒ ∘ σ ∘ (f ⊗ id)`.
--
-- `byHand` re-expresses it along a ten-step `HomReasoning` chain in `C`, every
-- intermediate form written out — sliding `f` past the braiding, pushing it
-- through the associator, *folding it into the merge* as `g ∘ (id ⊗ f)` (the
-- interchange law), and *swapping g and h* — while `auto` discharges the same
-- equation with a single call to the solver.

module Crossings (A₀ A₁ A₂ : C.Obj)
  (fᴹ : A₀ C.⇒ A₁) (gᴹ : (A₂ C.⊗₀ A₁) C.⇒ A₀) (hᴹ : A₁ C.⇒ A₂)
  where

  open Atoms3 A₀ A₁ A₂
  open FreeMonoidalHelper Symm (Fin 3) using (_⊗₀_)

  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = (a₂ ⊗₀ a₁) , a₀
  arity (suc (suc _)) = a₁ , a₂

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → fᴹ
    (suc zero)    → gᴹ
    (suc (suc _)) → hᴹ)

  private
    f g h : S.HomTerm _ _
    f = S.Agen (gen zero)
    g = S.Agen (gen (suc zero))
    h = S.Agen (gen (suc (suc zero)))

  private module MR = MonoidalReasoning C.monoidal
  open C.HomReasoning

  byHand : σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
       C.≈ (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ)
  byHand = begin
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ C.braiding.⇒.commute (fᴹ , C.id) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ (id {A₁ C.⊗₀ A₂} ⊗₁ fᴹ) ∘ σ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (MR.⊗-resp-≈ˡ (⟺ C.⊗.identity) ⟩∘⟨refl) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ ((id {A₁} ⊗₁ id {A₂}) ⊗₁ fᴹ) ∘ σ
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.sym-assoc ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ ((α⇒ ∘ ((id {A₁} ⊗₁ id {A₂}) ⊗₁ fᴹ)) ∘ σ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (C.assoc-commute-from ⟩∘⟨refl) ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ (((id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ)) ∘ α⇒) ∘ σ)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ C.assoc ⟩
      σ ∘ (hᴹ ⊗₁ gᴹ) ∘ ((id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ)) ∘ (α⇒ ∘ σ))
        ≈⟨ refl⟩∘⟨ C.sym-assoc ⟩
      σ ∘ ((hᴹ ⊗₁ gᴹ) ∘ (id {A₁} ⊗₁ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ)
        ≈⟨ refl⟩∘⟨ ((⟺ C.⊗.homomorphism) ⟩∘⟨refl) ⟩
      σ ∘ (((hᴹ ∘ id {A₁}) ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ))
        ≈⟨ refl⟩∘⟨ ((MR.⊗-resp-≈ˡ C.identityʳ) ⟩∘⟨refl) ⟩
      σ ∘ ((hᴹ ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ))) ∘ (α⇒ ∘ σ))
        ≈⟨ C.sym-assoc ⟩
      (σ ∘ (hᴹ ⊗₁ (gᴹ ∘ (id {A₂} ⊗₁ fᴹ)))) ∘ (α⇒ ∘ σ)
        ≈⟨ C.braiding.⇒.commute (hᴹ , gᴹ C.∘ (C.id C.⊗₁ fᴹ)) ⟩∘⟨refl ⟩
      (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ) ∎

  auto : σ ∘ (hᴹ ⊗₁ gᴹ) ∘ α⇒ ∘ σ ∘ (fᴹ ⊗₁ id {A₁ C.⊗₀ A₂})
     C.≈ (((gᴹ ∘ (id {A₂} ⊗₁ fᴹ)) ⊗₁ hᴹ) ∘ σ) ∘ (α⇒ ∘ σ)
  auto = solveH! (S.σ S.∘ (h S.⊗₁ g) S.∘ S.α⇒ S.∘ S.σ S.∘ (f S.⊗₁ S.id {a₁ S.⊗₀ a₂}))
                 ((((g S.∘ (S.id {a₂} S.⊗₁ f)) S.⊗₁ h) S.∘ S.σ) S.∘ (S.α⇒ S.∘ S.σ))

--------------------------------------------------------------------------------
-- Configuration 4: a monoid (m : a₀ ⊗ a₀ → a₀, u : unit → a₀) demonstrating
-- diagrammatic *rewriting* with `rewriteH!`.  Given the monoid's left-unit law
-- as a hypothesis (an equation in `C`, exactly the kind of "rule" a real client
-- already has a proof of), we rewrite the redex `m ∘ (u ⊗ id)` to `λ⇒` *inside*
-- a larger diagram — the soundness-only analogue of TensorRocq's `srw`/`zxrw`.
-- The rule fires at a position the caller pins down with two context terms;
-- `findIso` reconciles both endpoints to that frame up to SMC structure.

module MonoidRewrite (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ)

  a₀ : ObjTerm
  a₀ = Var zero

  ⟦_⟧ᵖ₀ : Fin 1 → C.Obj
  ⟦ _ ⟧ᵖ₀ = A

  -- m : a₀ ⊗ a₀ → a₀  (index 0),  u : unit → a₀  (index 1).
  arity : Fin 2 → ObjTerm × ObjTerm
  arity zero    = (a₀ ⊗₀ a₀) , a₀
  arity (suc _) = unitᵗ , a₀

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero    → mᴹ
    (suc _) → uᴹ)

  private
    m u : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))

  -- The monoid's left-unit law, stated in `C`'s own vocabulary — definitionally
  -- `⟦ m ∘ (u ⊗₁ id) ⟧₁ ≈ ⟦ λ⇒ ⟧₁`, i.e. exactly the `rule` `rewriteH!` wants.
  module _ (unitLawˡ : mᴹ ∘ (uᴹ ⊗₁ id {A}) ≈ λ⇒) where

    -- A single rewrite: replace the redex in the right tensor factor of
    -- `m ∘ (id ⊗ –)`.  Position: `pre = id`, `post = m`, pad `k = a₀`.
    test-unitˡ-in-context
      : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ mᴹ ∘ (id {A} ⊗₁ λ⇒)
    test-unitˡ-in-context =
      rewriteH!
        (m S.∘ (S.id {a₀} S.⊗₁ (m S.∘ (u S.⊗₁ S.id))))   -- s  (before)
        (m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒))                     -- t  (after)
        (S.id {a₀ S.⊗₀ (unitᵗ S.⊗₀ a₀)})                 -- pre  (input side)
        m                                                 -- post (output side)
        (m S.∘ (u S.⊗₁ S.id))                             -- lᵗ
        S.λ⇒                                              -- rᵗ
        unitLawˡ

    -- Fully automatic: `rewriteAuto!` *finds* the redex position itself (via
    -- `focusAt`), so the caller supplies only the term, the rule sides, and the
    -- rule proof — no `pre`/`post`.  The rewritten RHS is computed (`≈ _`).
    test-unitˡ-auto
      : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ _
    test-unitˡ-auto =
      rewriteAuto! (m S.∘ (S.id {a₀} S.⊗₁ (m S.∘ (u S.⊗₁ S.id))))
                   (m S.∘ (u S.⊗₁ S.id))   -- lᵗ (found automatically)
                   S.λ⇒                     -- rᵗ
                   unitLawˡ

    -- The same step composed with the coherence solver `solveH!` in a single
    -- `HomReasoning` chain: rewrite, then massage the result up to SMC structure.
    test-rewrite-then-coherence
      : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ (mᴹ ∘ (id {A} ⊗₁ λ⇒)) ∘ id
    test-rewrite-then-coherence = begin
      mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A})))
        ≈⟨ test-unitˡ-in-context ⟩
      mᴹ ∘ (id {A} ⊗₁ λ⇒)
        ≈⟨ solveH! (m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒))
                   ((m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒)) S.∘ S.id) ⟩
      (mᴹ ∘ (id {A} ⊗₁ λ⇒)) ∘ id ∎
      where open C.HomReasoning
