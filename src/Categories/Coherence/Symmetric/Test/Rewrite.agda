{-# OPTIONS --safe --without-K #-}

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
-- subterms of `s` as written (e.g. split across an interchange), see
-- `Test.Deep`.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test.Rewrite
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Bool.Base using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (is-just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Coherence.Symmetric C

--------------------------------------------------------------------------------
-- Configuration: a monoid object — m : a₀ ⊗ a₀ → a₀, u : unit → a₀ — with the
-- left-unit law as a hypothesis.

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
