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
  -- see `deep-non-convex-rejected` in `Test.DeepArity`.)
  deep-overlap-rejected
    : is-just (deepFoc (w S.∘ p) (p S.⊗₁ w)) ≡ false
  deep-overlap-rejected = refl

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
