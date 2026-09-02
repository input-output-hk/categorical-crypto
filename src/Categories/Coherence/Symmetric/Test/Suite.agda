{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- THE SUITE.  One section per tool of `Categories.Coherence.Symmetric`, in the
-- palette order of `Categories.Coherence.Symmetric.Test`, which is the root
-- that checks this module:
--
--   1. `solveH!`               — `Cycle3`, `Braiding`, `Crossings` (+ `Atoms3`)
--   2. `rewriteH!`/`rewriteAuto(ₙ)!` — `MonoidRewrite`
--   3. `rewriteDeep(ₙ)!`/`rewriteDeepTo!` — `DeepRewrite`, `DeepArity`
--   4. `normalize(To)!`        — `MonoidNormalize`
--   5. the Frobenius showcase  — `FrobeniusAlgebra`
--
-- The sections are independent: each configuration sub-module is parameterised
-- by the objects and morphisms of `C` interpreting its own generators, and
-- nothing crosses a section boundary.  They share one preamble — the `C`
-- telescope, the `Fin`/`_≟F_` generator-index kit, `Coherence.Symmetric C` and
-- the two ready-made alphabets `Atoms3`/`Atom1` — which is the whole reason
-- they live in one file.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test.Suite
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Bool.Base using (false; true)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (is-just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning

open import Categories.Coherence.Symmetric C

--------------------------------------------------------------------------------
-- `solveH!` — discharging free-SMC *coherence* equations.
--
-- The entry-level tool: an equation between two morphism expressions of `C`
-- holds "for free" whenever the two sides have the same string diagram, i.e.
-- their free-SMC terms translate to isomorphic hypergraphs.  `solveH! f g`
-- finds that isomorphism at type-check time and transports it into `C`.
--
-- Each *configuration* below is a sub-module parameterised by the objects and
-- morphisms of `C` interpreting its generators:
--
--   * `Cycle3`    — generators f,g,h forming a 3-cycle; the category /
--                   monoidal structural laws.
--   * `Braiding`  — symmetry-heavy, non-trivial string-diagram equalities.
--   * `Crossings` — f, h (one in/out) and a merge g (two in, one out); one
--                   braided diagram `σ ∘ (h ⊗ g) ∘ α⇒ ∘ σ ∘ (f ⊗ id)`
--                   re-expressed along a ten-step `HomReasoning` chain in `C`
--                   (`byHand`), then discharged by the solver in one line
--                   (`auto`) — the motivating before/after comparison.
--
-- Each test states a genuine equation between morphisms of `C` (via `Tgt`);
-- no `⟦_⟧₁` appears, because each `Tgt`-expression is *definitionally* the
-- interpretation of the corresponding free-SMC term, and each free-SMC term
-- is written exactly once (`solveH!` finds the witnessing hypergraph iso).
--------------------------------------------------------------------------------

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
-- A ready-made one-atom alphabet `a` and its interpretation `A`, shared by the
-- four single-object configurations below.

module Atom1 (A : C.Obj) where
  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ) public

  a : ObjTerm
  a = Var zero

  ⟦_⟧ᵖ₀ : Fin 1 → C.Obj
  ⟦ _ ⟧ᵖ₀ = A

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
-- `rewriteH!` / `rewriteAuto!` / `rewriteAutoₙ!` — diagrammatic rewriting with
-- a *rule* as input (the soundness-only analogue of TensorRocq's `srw`).
--
-- A rule is an equation `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁` in `C` between the interpretations
-- of two free-SMC terms — definitionally, whatever raw `C`-equation the client
-- already has (here: a monoid's left-unit law, taken as a hypothesis).  The
-- tools differ in how the rewrite *position* is obtained:
--
--   * `rewriteH!`     — the caller pins it down with two context terms
--                       `pre`/`post` (frame `post ∘ (id {k} ⊗ –) ∘ pre`);
--   * `rewriteAuto!`  — the position is found by structural focusing
--                       (`focusAt`): the redex must be a *subterm* of `s`,
--                       though both the redex occurrence and the contexts are
--                       matched up to SMC structure;
--   * `rewriteAutoₙ!` — same, with an occurrence index `n` choosing among
--                       the positions `focusAll` enumerates (leaf first, then
--                       right operand/factor before left).
--
-- The probes at the end pin down the *semantics of occurrence enumeration*
-- and the up-to-SMC behaviour of the leaf test.  For redexes that are NOT
-- subterms of `s` as written (e.g. split across an interchange), see the
-- `rewriteDeep!` section below.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Configuration: a monoid object — m : a₀ ⊗ a₀ → a₀, u : unit → a₀ — with the
-- left-unit law as a hypothesis.

module MonoidRewrite (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open Atom1 A renaming (a to a₀)

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

    -- The rule's left-hand side as a free-SMC term.
    lᵗ : S.HomTerm (unitᵗ S.⊗₀ a₀) a₀
    lᵗ = m S.∘ (u S.⊗₁ S.id)

  -- The monoid's left-unit law, stated in `C`'s own vocabulary — definitionally
  -- `⟦ lᵗ ⟧₁ ≈ ⟦ λ⇒ ⟧₁`, i.e. exactly the `rule` the rewriting tools want.
  module _ (unitLawˡ : mᴹ ∘ (uᴹ ⊗₁ id {A}) ≈ λ⇒) where

    ----------------------------------------------------------------------------
    -- `rewriteH!`: manual position.  Replace the redex in the right tensor
    -- factor of `m ∘ (id ⊗ –)`.  Position: `pre = id`, `post = m`, pad `k = a₀`.
    test-unitˡ-in-context
      : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ mᴹ ∘ (id {A} ⊗₁ λ⇒)
    test-unitˡ-in-context =
      rewriteH!
        (m S.∘ (S.id {a₀} S.⊗₁ lᵗ))                       -- s  (before)
        (m S.∘ (S.id {a₀} S.⊗₁ S.λ⇒))                     -- t  (after)
        (S.id {a₀ S.⊗₀ (unitᵗ S.⊗₀ a₀)})                 -- pre  (input side)
        m                                                 -- post (output side)
        lᵗ S.λ⇒ unitLawˡ

    ----------------------------------------------------------------------------
    -- `rewriteAuto!`: the position is *found* (via `focusAt`); the caller
    -- supplies only the term, the rule sides, and the rule proof.  The
    -- rewritten RHS is computed (`≈ _`).
    test-unitˡ-auto
      : mᴹ ∘ (id {A} ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A}))) ≈ _
    test-unitˡ-auto =
      rewriteAuto! (m S.∘ (S.id {a₀} S.⊗₁ lᵗ)) lᵗ S.λ⇒ unitLawˡ

    -- Boundary case: the redex IS the whole term (the leaf frame, pad `unit`).
    test-unitˡ-at-root : mᴹ ∘ (uᴹ ⊗₁ id {A}) ≈ _
    test-unitˡ-at-root = rewriteAuto! lᵗ lᵗ S.λ⇒ unitLawˡ

    -- The leaf test is up-to-SMC (it certifies with `findIso`, not syntactic
    -- equality): a redex occurrence wrapped in structural noise — extra `id`s
    -- and a cancelling `σ ∘ σ` — is still found.  Only the rule's *interface
    -- objects* `P`, `Q` must coincide literally.
    test-unitˡ-noisy
      : (mᴹ ∘ (uᴹ ⊗₁ id {A}) ∘ id) ∘ (σ ∘ σ) ≈ _
    test-unitˡ-noisy =
      rewriteAuto! ((m S.∘ (u S.⊗₁ S.id) S.∘ S.id) S.∘ (S.σ S.∘ S.σ))
                   lᵗ S.λ⇒ unitLawˡ

    ----------------------------------------------------------------------------
    -- `rewriteAutoₙ!`: occurrence selection.  With two copies of the redex
    -- side by side, rewrite the chosen one (index 1, the left factor) and
    -- leave the other.
    test-unitˡ-auto-occ1
      : (mᴹ ∘ (uᴹ ⊗₁ id {A})) ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id {A})) ≈ _
    test-unitˡ-auto-occ1 =
      rewriteAutoₙ! (lᵗ S.⊗₁ lᵗ) lᵗ S.λ⇒ 1 unitLawˡ

    ----------------------------------------------------------------------------
    -- Composability: a positioned rewrite chained with a `solveH!` coherence
    -- step in a single `HomReasoning` chain.
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

  ------------------------------------------------------------------------------
  -- Occurrence-enumeration semantics (independent of any rule proof).

  -- `focusAll` enumerates exactly the syntactic occurrences: two here.
  occurrence-count : length (focusAll (lᵗ S.⊗₁ lᵗ) lᵗ) ≡ 2
  occurrence-count = refl

  -- An out-of-range index is rejected (the `found` obligation of
  -- `rewriteAutoₙ!` becomes unsatisfiable).
  out-of-range : is-just (focusAtₙ (lᵗ S.⊗₁ lᵗ) lᵗ 2) ≡ false
  out-of-range = refl

--------------------------------------------------------------------------------
-- `rewriteDeep!` — rewriting modulo diagram deformation.
--
-- `rewriteAuto!` (see `MonoidRewrite` above) requires the redex to be a
-- *subterm* of `s` as written.  `rewriteDeep!` drops that: the position is
-- found on the *hypergraph* `⟪ s ⟫` (sub-hypergraph matching → hole-carve →
-- decode), so the redex need only be a connected sub-diagram, however the
-- term was bracketed or interleaved.  The canonical case: a sequential rule
-- `w ∘ p` firing inside `(w ⊗ w) ∘ (p ⊗ q)`, where interchange splits the
-- redex across the outer `∘`.
--
-- Each positive test is a full end-to-end rewrite in an arbitrary SMC `C`
-- (search, certification, and interpretation).  The KNOWN LIMITATION probes
-- state — in the frontend's own vocabulary, via the re-exported `deepFoc` —
-- exactly what the deep search declines, and why that is the correct
-- behaviour (or what the workaround is).  Soundness is never at stake: every
-- limitation is a *search* failing closed behind the `findIso` gate.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Configuration 1: parallel arrows p, q : a₀ → a₁ and w : a₁ → a₂, with a
-- rule on the *composite* `w ∘ p` (hypothesis `collapse`) and one on the
-- *parallel pair* `p ⊗ q` (hypothesis `commute`).

module DeepRewrite (A₀ A₁ A₂ : C.Obj)
  (pᴹ qᴹ : A₀ C.⇒ A₁) (wᴹ : A₁ C.⇒ A₂)
  where

  open FreeMonoidalHelper Symm (Fin 3) using (ObjTerm; Var)

  a₀ a₁ a₂ : ObjTerm
  a₀ = Var zero
  a₁ = Var (suc zero)
  a₂ = Var (suc (suc zero))

  ⟦_⟧ᵖ₀ : Fin 3 → C.Obj
  ⟦ zero        ⟧ᵖ₀ = A₀
  ⟦ suc zero    ⟧ᵖ₀ = A₁
  ⟦ suc (suc _) ⟧ᵖ₀ = A₂

  arity : Fin 3 → ObjTerm × ObjTerm
  arity zero          = a₀ , a₁
  arity (suc zero)    = a₀ , a₁
  arity (suc (suc _)) = a₁ , a₂

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero          → pᴹ
    (suc zero)    → qᴹ
    (suc (suc _)) → wᴹ)

  private
    p q w : S.HomTerm _ _
    p = S.Agen (gen zero)
    q = S.Agen (gen (suc zero))
    w = S.Agen (gen (suc (suc zero)))

  ------------------------------------------------------------------------------
  -- Negative control: the redex `w ∘ p` is NOT a subterm of
  -- `(w ⊗ w) ∘ (p ⊗ q)`, so structural focusing — hence `rewriteAuto!` —
  -- cannot fire.  (`rewriteDeep!` can: see `test-deep-rewrite`.)

  syntactic-fails
    : is-just (focusAt ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) (w S.∘ p)) ≡ false
  syntactic-fails = refl

  module _ (collapse : wᴹ ∘ pᴹ ≈ wᴹ ∘ qᴹ) where

    -- The canonical interchange case.  Note also that both `w`-edges in the
    -- target carry the same label, so the search must backtrack from the
    -- connectivity-inconsistent pairing.
    test-deep-rewrite : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ _
    test-deep-rewrite =
      rewriteDeep! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q))   -- s   (redex NOT a subterm)
                   (w S.∘ p)                      -- lᵗ
                   (w S.∘ q)                      -- rᵗ
                   collapse

    -- Redex across a *braiding*: `p` enters on the second wire and crosses
    -- the σ to feed the first `w`.  Connectivity through σ is pure wiring.
    test-deep-σ-crossing : (wᴹ ⊗₁ wᴹ) ∘ σ ∘ (qᴹ ⊗₁ pᴹ) ≈ _
    test-deep-σ-crossing =
      rewriteDeep! ((w S.⊗₁ w) S.∘ S.σ S.∘ (q S.⊗₁ p))
                   (w S.∘ p) (w S.∘ q) collapse

    -- Carve with a permuted boundary: a σ *below* the whole diagram, so the
    -- carved context's input interface is a nontrivial permutation.
    test-deep-permuted-boundary
      : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ∘ σ {A₀} {A₀} ≈ _
    test-deep-permuted-boundary =
      rewriteDeep! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q) S.∘ S.σ {a₀} {a₀})
                   (w S.∘ p) (w S.∘ q) collapse

    -- The practical idiom for multi-step derivations: a deep rewrite landing
    -- directly on a caller-stated CLEAN term (`rewriteDeepTo!`), so the
    -- carved frame never appears in any exposed type and steps chain by
    -- plain transitivity.  (Naming the frame with `deepFrame` and cleaning
    -- up with a separate `solveH!` also works, but makes the type-checker
    -- conversion-check two large frame terms — prohibitively slow.)
    test-deep-chain : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ (wᴹ ⊗₁ wᴹ) ∘ (qᴹ ⊗₁ qᴹ)
    test-deep-chain =
      rewriteDeepTo! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) ((w S.⊗₁ w) S.∘ (q S.⊗₁ q))
                     (w S.∘ p) (w S.∘ q) 0 collapse

  module _ (commute : pᴹ ⊗₁ qᴹ ≈ qᴹ ⊗₁ pᴹ) where

    -- Parallel (DISCONNECTED) redex: the rule's LHS `p ⊗ q` has two
    -- hypergraph components; the matcher binds them independently and the
    -- carve still yields a single convex hole.
    test-deep-parallel : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ _
    test-deep-parallel =
      rewriteDeep! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q))
                   (p S.⊗₁ q) (q S.⊗₁ p) commute

  ------------------------------------------------------------------------------
  -- KNOWN LIMITATIONS (each `deepFoc` failure is a search failing *closed*).

  -- Adjacent overlap rejected at *search* time: matching `p ⊗ w` against the
  -- sequential `w ∘ p` would need the redex's two boundary wires to map to
  -- the SAME vertex (p's output = w's input), and the vertex map of an
  -- embedding is injective.  (For occurrences rejected later, at the *carve*,
  -- see `deep-non-convex-rejected` in the `DeepArity` module below.)
  deep-overlap-rejected
    : is-just (deepFoc (w S.∘ p) (p S.⊗₁ w)) ≡ false
  deep-overlap-rejected = refl

  -- The stage discriminator for the claim above: it is the MATCH that refuses,
  -- before any carve is attempted.  (Contrast the `DeepArity` module's
  -- `deep-non-convex-match-succeeds`, where this same assertion holds with
  -- `true` and only the carve rejects — so `deepFoc … ≡ false` alone would
  -- not have distinguished the two limitations.)
  deep-overlap-match-rejected
    : is-just (subMatch ⟪ p S.⊗₁ w ⟫ ⟪ w S.∘ p ⟫) ≡ false
  deep-overlap-match-rejected = refl

  -- Purely structural rule LHS (`σ`, `id`, any coherence morphism): its
  -- hypergraph has NO edges, so there is nothing to match.  Such "rules"
  -- are free coherence facts — `solveH!`'s job, not a rewrite's.
  deep-structural-limitation
    : is-just (deepFoc (S.σ S.∘ (p S.⊗₁ q)) (S.σ {a₁} {a₁})) ≡ false
  deep-structural-limitation = refl

  ------------------------------------------------------------------------------
  -- PADDED RULES.  A rule LHS with a bare identity wire (`p ⊗ id`) is not
  -- edge-matchable as written; and since `⊗` is not faithful, a proof of the
  -- padded equation does NOT yield the unpadded one — the padded rule may be
  -- all the client has.  The engine strips the pad from the match query and
  -- threads a same-typed parallel wire of the context through the rule's
  -- vacuous slot (repadding), so the padded rule and its padded proof are
  -- used at their own types.  (v1: pads are syntactically outermost
  -- single-atom layers, `– ⊗ id {Var w}` / `id {Var w} ⊗ –`.)

  -- Right pad: the rule's spare wire is matched by `q`'s input wire.
  module _ (padded : pᴹ ⊗₁ id {A₀} ≈ qᴹ ⊗₁ id {A₀}) where

    test-deep-padded-rule : pᴹ ⊗₁ qᴹ ≈ _
    test-deep-padded-rule =
      rewriteDeep! (p S.⊗₁ q)
                   (p S.⊗₁ S.id {a₀}) (q S.⊗₁ S.id {a₀}) padded

  -- Left pad (the routing inserts a braiding), threaded through `w`'s
  -- input wire.
  module _ (paddedL : id {A₁} ⊗₁ pᴹ ≈ id {A₁} ⊗₁ qᴹ) where

    test-deep-padded-left : wᴹ ⊗₁ pᴹ ≈ _
    test-deep-padded-left =
      rewriteDeep! (w S.⊗₁ p)
                   (S.id {a₁} S.⊗₁ p) (S.id {a₁} S.⊗₁ q) paddedL

  -- Two stacked pad layers (state multi-wire pads as nested single-atom
  -- layers): the spare wires thread `q`'s and `w`'s input wires.
  module _ (padded² : (pᴹ ⊗₁ id {A₀}) ⊗₁ id {A₁} ≈ (qᴹ ⊗₁ id {A₀}) ⊗₁ id {A₁}) where

    test-deep-padded-two : (pᴹ ⊗₁ qᴹ) ⊗₁ wᴹ ≈ _
    test-deep-padded-two =
      rewriteDeep! ((p S.⊗₁ q) S.⊗₁ w)
                   ((p S.⊗₁ S.id {a₀}) S.⊗₁ S.id {a₁})
                   ((q S.⊗₁ S.id {a₀}) S.⊗₁ S.id {a₁}) padded²

--------------------------------------------------------------------------------
-- Configuration 2: `rewriteDeep!` on multi-arity generators, and the
-- convexity/retry story.  A merge
-- `m : a ⊗ a → a`, a split `e : a → a ⊗ a`, a unary `k : a → a`, and a
-- scalar-ish `u : unit → a`.

module DeepArity (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (eᴹ : A C.⇒ (A C.⊗₀ A))
  (kᴹ : A C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open Atom1 A

  arity : Fin 4 → ObjTerm × ObjTerm
  arity zero                = (a ⊗₀ a) , a
  arity (suc zero)          = a , (a ⊗₀ a)
  arity (suc (suc zero))    = a , a
  arity (suc (suc (suc _))) = unitᵗ , a

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero                → mᴹ
    (suc zero)          → eᴹ
    (suc (suc zero))    → kᴹ
    (suc (suc (suc _))) → uᴹ)

  private
    m sp k u : S.HomTerm _ _
    m  = S.Agen (gen zero)
    sp = S.Agen (gen (suc zero))
    k  = S.Agen (gen (suc (suc zero)))
    u  = S.Agen (gen (suc (suc (suc zero))))

  -- Multi-wire redex: the split-then-process composite `(k ⊗ k) ∘ e`,
  -- carved out from under the closing merge `m`.
  module _ (fuse : (kᴹ ⊗₁ kᴹ) ∘ eᴹ ≈ eᴹ) where

    test-deep-multiwire : mᴹ ∘ (kᴹ ⊗₁ kᴹ) ∘ eᴹ ≈ _
    test-deep-multiwire =
      rewriteDeep! (m S.∘ (k S.⊗₁ k) S.∘ sp)
                   ((k S.⊗₁ k) S.∘ sp) sp fuse

  -- Scalar redex: `u : unit → a` has an EMPTY input interface, so the carved
  -- hole has no inputs and the frame's `pre` context ends in a unit wire.
  module _ (grow : uᴹ ≈ kᴹ ∘ uᴹ) where

    test-deep-scalar : mᴹ ∘ (uᴹ ⊗₁ kᴹ) ≈ _
    test-deep-scalar =
      rewriteDeep! (m S.∘ (u S.⊗₁ k)) u (k S.∘ u) grow

  -- Swapped merge arguments: in `m ∘ σ ∘ (k ⊗ k)` the merge consumes the two
  -- `k` outputs in swapped order; matching the rule's `m ∘ (k ⊗ k)` forces
  -- the (identically labelled) `k`-edges to be paired crosswise.
  module _ (slide : mᴹ ∘ (kᴹ ⊗₁ kᴹ) ≈ kᴹ ∘ mᴹ) where

    test-deep-swapped-merge : mᴹ ∘ σ ∘ (kᴹ ⊗₁ kᴹ) ≈ _
    test-deep-swapped-merge =
      rewriteDeep! (m S.∘ S.σ S.∘ (k S.⊗₁ k))
                   (m S.∘ (k S.⊗₁ k)) (k S.∘ m) slide

  ------------------------------------------------------------------------------
  -- Convexity at the carve, and the match retry that makes it precise.

  -- TRUE non-convexity, rejected at the *carve*: in `k ∘ k ∘ k`, matching
  -- `k ⊗ k` on the two outer `k`s is injective — the search accepts it — but
  -- the middle `k` is a complement path from the redex's output back into its
  -- input, so the carved graph is cyclic through the hole and the topological
  -- ordering gets stuck.  No convex occurrence exists at all here, so the
  -- match retry exhausts and `deepFoc` correctly fails.  (Contrast with
  -- `deep-overlap-rejected` in `DeepRewrite`, which dies earlier,
  -- at the search's injectivity check.)
  deep-non-convex-rejected
    : is-just (deepFoc (k S.∘ k S.∘ k) (k S.⊗₁ k)) ≡ false
  deep-non-convex-rejected = refl

  -- The stage discriminator: here the MATCH succeeds (unlike
  -- `DeepRewrite.deep-overlap-match-rejected`, where the same assertion is
  -- `false`) — so the rejection above provably happens at the carve, not at
  -- the search.
  deep-non-convex-match-succeeds
    : is-just (subMatch ⟪ k S.⊗₁ k ⟫ ⟪ k S.∘ k S.∘ k ⟫) ≡ true
  deep-non-convex-match-succeeds = refl

  -- Match retry: in `(k ∘ k ∘ k) ⊗ k` the DFS's FIRST match for `k ⊗ k` is a
  -- non-convex outer pair as above, but convex pairings with the parallel
  -- fourth `k` exist; `deepFoc` walks past the non-convex matches to a
  -- carvable one.  (Before match enumeration + carve retry, this failed
  -- spuriously — the non-convex first match masked the others.)
  module _ (mix : kᴹ ⊗₁ kᴹ ≈ eᴹ ∘ mᴹ) where

    test-deep-retry : (kᴹ ∘ kᴹ ∘ kᴹ) ⊗₁ kᴹ ≈ _
    test-deep-retry =
      rewriteDeep! ((k S.∘ k S.∘ k) S.⊗₁ k) (k S.⊗₁ k) (sp S.∘ m) mix

--------------------------------------------------------------------------------
-- `normalize!` / `normalizeTo!` — rewrite DRIVERS.
--
-- A driver takes a LIST of oriented rules (each a `Rule`: free-SMC sides plus
-- the soundness proof in `C`) and fires the first applicable rule at its
-- first carvable deep position, repeatedly, until no rule applies or the
-- fuel runs out.  The search carries its own proof, so there are no
-- typecheck-time witnesses beyond `normalizeTo!`'s final reconciliation.
--
-- Because the driver re-searches from scratch after every firing, a
-- singleton rule list with sufficient fuel is "rewrite everywhere" — the
-- first test below fires the same rule at two occurrences.  The second test
-- normalises with a two-rule system, where firing one rule exposes the
-- other's redex.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Configuration: the monoid (m : a ⊗ a → a, u : unit → a), with both unit
-- laws as hypotheses.

module MonoidNormalize (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open Atom1 A

  arity : Fin 2 → ObjTerm × ObjTerm
  arity zero    = (a ⊗₀ a) , a
  arity (suc _) = unitᵗ , a

  open Setup _≟F_ arity ⟦_⟧ᵖ₀ (λ where
    zero    → mᴹ
    (suc _) → uᴹ)

  private
    m u : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))

  module _ (unitLawˡ : mᴹ ∘ (uᴹ ⊗₁ id) ≈ λ⇒)
           (unitLawʳ : mᴹ ∘ (id ⊗₁ uᴹ) ≈ ρ⇒)
    where

    private
      rules : List Rule
      rules = mkRule (m S.∘ (u S.⊗₁ S.id)) S.λ⇒ unitLawˡ
            ∷ mkRule (m S.∘ (S.id S.⊗₁ u)) S.ρ⇒ unitLawʳ
            ∷ []

    -- One rule, two occurrences: the driver re-searches after each firing,
    -- so both redexes are eliminated ("rewrite everywhere").  Extra fuel is
    -- harmless — the driver stops when no rule applies.
    test-normalize-pair
      : (mᴹ ∘ (uᴹ ⊗₁ id)) ⊗₁ (mᴹ ∘ (uᴹ ⊗₁ id)) ≈ λ⇒ ⊗₁ λ⇒
    test-normalize-pair =
      normalizeTo! ((m S.∘ (u S.⊗₁ S.id)) S.⊗₁ (m S.∘ (u S.⊗₁ S.id)))
                   (S.λ⇒ S.⊗₁ S.λ⇒)
                   rules 3

    -- Two rules interleaved: the outer redex is a `unitˡ` instance whose
    -- "second input" is the inner `unitʳ` redex; after the first firing the
    -- inner redex remains and the other rule picks it up.  The fully
    -- normalised diagram is pure wiring, stated as a coherence composite.
    test-normalize-both
      : mᴹ ∘ (uᴹ ⊗₁ (mᴹ ∘ (id ⊗₁ uᴹ))) ≈ λ⇒ ∘ (id ⊗₁ ρ⇒)
    test-normalize-both =
      normalizeTo! (m S.∘ (u S.⊗₁ (m S.∘ (S.id S.⊗₁ u))))
                   (S.λ⇒ S.∘ (S.id S.⊗₁ S.ρ⇒))
                   rules 3

    -- `normalize!`: land wherever the driver stops, with no stated target
    -- (the `≈ _` form).  Same rule system and fuel as the test above, so the
    -- two together pin the driver's stopping point from both sides.
    test-normalize-open : mᴹ ∘ (uᴹ ⊗₁ (mᴹ ∘ (id ⊗₁ uᴹ))) ≈ _
    test-normalize-open =
      normalize! rules 3 (m S.∘ (u S.⊗₁ (m S.∘ (S.id S.⊗₁ u))))

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
-- `rewriteDeepTo!` steps.  Each step rewrites one rule occurrence (located on
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

module FrobeniusAlgebra (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (uᴹ : C.unit C.⇒ A)
  (nᴹ : A C.⇒ (A C.⊗₀ A)) (vᴹ : A C.⇒ C.unit)
  where

  open Atom1 A

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
    -- (The counit `v`, generator 3, is in the signature — a comonoid has one —
    -- but no rule or diagram below mentions it, so it gets no free-term name.)
    m u n : S.HomTerm _ _
    m = S.Agen (gen zero)
    u = S.Agen (gen (suc zero))
    n = S.Agen (gen (suc (suc zero)))

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
