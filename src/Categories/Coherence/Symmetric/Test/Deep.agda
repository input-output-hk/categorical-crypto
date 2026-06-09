{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `rewriteDeep!` — rewriting modulo diagram deformation.
--
-- `rewriteAuto!` (see `Test.Rewrite`) requires the redex to be a *subterm* of
-- `s` as written.  `rewriteDeep!` drops that requirement: the position is
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

open import Level using (Level)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

module Categories.Coherence.Symmetric.Test.Deep
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e) where

open import Data.Bool.Base using (true; false)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (is-just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Coherence.Symmetric C

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

    -- The practical idiom: the deep rewrite lands on the (gnarly) carved
    -- frame; one `solveH!` step lands it back on a CLEAN right-hand side.
    -- `deepFrame` names the intermediate term; its witness argument is `_`
    -- (it reduces to `tt` since the search concretely succeeds).
    test-deep-chain : (wᴹ ⊗₁ wᴹ) ∘ (pᴹ ⊗₁ qᴹ) ≈ (wᴹ ⊗₁ wᴹ) ∘ (qᴹ ⊗₁ qᴹ)
    test-deep-chain =
      C.Equiv.trans
        (rewriteDeep! ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) (w S.∘ p) (w S.∘ q) collapse)
        (solveH! (deepFrame ((w S.⊗₁ w) S.∘ (p S.⊗₁ q)) (w S.∘ p) (w S.∘ q) _)
                 ((w S.⊗₁ w) S.∘ (q S.⊗₁ q)))

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

  -- Non-convex occurrence rejected: in the sequential `w ∘ p` the
  -- disconnected redex `p ⊗ w` matches edge-wise, but the complement path
  -- leaves the redex and re-enters it, so the carved graph is cyclic through
  -- the hole.  A non-convex match has no pushout complement — there is no
  -- context to rewrite in — and the topological carve detects exactly this.
  deep-non-convex-rejected
    : is-just (deepFoc (w S.∘ p) (p S.⊗₁ w)) ≡ false
  deep-non-convex-rejected = refl

  -- Identity wires in a rule LHS: `⟪ p ⊗ id ⟫` has a bare wire vertex
  -- incident to no edge, which the edge-driven matcher can never bind.
  -- State the rule without the padding (`p`, not `p ⊗ id`) — the rewrite
  -- frame's own `id {k} ⊗ –` pad plays that role — or use `rewriteH!`.
  deep-id-wire-limitation
    : is-just (deepFoc (p S.⊗₁ q) (p S.⊗₁ S.id {a₀})) ≡ false
  deep-id-wire-limitation = refl

  -- Purely structural rule LHS (`σ`, `id`, any coherence morphism): its
  -- hypergraph has NO edges, so there is nothing to match.  Such "rules"
  -- are free coherence facts — `solveH!`'s job, not a rewrite's.
  deep-structural-limitation
    : is-just (deepFoc (S.σ S.∘ (p S.⊗₁ q)) (S.σ {a₁} {a₁})) ≡ false
  deep-structural-limitation = refl

--------------------------------------------------------------------------------
-- Configuration 2: multi-arity generators — a merge `m : a ⊗ a → a`, a split
-- `e : a → a ⊗ a`, a unary `k : a → a`, and a scalar-ish `u : unit → a`.

module DeepArity (A : C.Obj)
  (mᴹ : (A C.⊗₀ A) C.⇒ A) (eᴹ : A C.⇒ (A C.⊗₀ A))
  (kᴹ : A C.⇒ A) (uᴹ : C.unit C.⇒ A)
  where

  open FreeMonoidalHelper Symm (Fin 1) using (ObjTerm; Var; _⊗₀_)
    renaming (unit to unitᵗ)

  a : ObjTerm
  a = Var zero

  ⟦_⟧ᵖ₀ : Fin 1 → C.Obj
  ⟦ _ ⟧ᵖ₀ = A

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
