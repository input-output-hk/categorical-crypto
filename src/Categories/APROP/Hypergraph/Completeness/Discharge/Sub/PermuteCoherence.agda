{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Sub-discharge of `PermuteCoherence.permute-≈Term-coherence` from
-- `Discharge/FinalPermute.agda`.
--
-- ## Goal (as posed)
--
--   permute-≈Term-coherence
--     : ∀ {xs ys : List X} (p q : xs ↭ ys)
--     → permute p ≈Term permute q
--
-- where `permute : ∀ {xs ys} → xs ↭ ys → HomTerm (unflatten xs) (unflatten ys)`
-- is the σ-structural permutation builder from `Completeness/Permute.agda`.
--
-- ## Status: PARTIAL DISCHARGE (Outcome 2) with critical caveat.
--
-- ### CRITICAL FINDING — the postulate is FALSE in full generality.
--
-- The statement as quantified — for ARBITRARY `xs, ys : List X` with
-- arbitrary `X` — is **not** Kelly's coherence theorem; it is strictly
-- stronger.  Counter-example:
--
--   X = arbitrary, x : X, xs = ys = x ∷ x ∷ [].
--   p = Perm.refl                       : xs ↭ xs
--   q = Perm.swap x x Perm.refl         : x ∷ x ∷ [] ↭ x ∷ x ∷ []
--                                        (which type-checks because the
--                                        constructor's outputs `y ∷ x ∷ ys`
--                                        coincide with `x ∷ x ∷ xs` when
--                                        x = y and xs = ys, here both [])
--
--   permute p ≡ id : HomTerm (Var x ⊗₀ Var x ⊗₀ unit) (Var x ⊗₀ Var x ⊗₀ unit)
--   permute q ≡ (id ⊗₁ id ⊗₁ id) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
--             : the same hom-set
--
-- These are NOT `≈Term`-equal in the free symmetric monoidal category:
-- via the canonical model functor `FreeFunctor` interpreting
-- `Var x ↦ A` for any object A with `|A| ≥ 2` in Set, `permute q`
-- becomes the braiding `σ_{A,A} ⊗ id_unit` (post α-collapse), which
-- swaps pairs and is **distinct from** the identity.  By the model's
-- soundness (`⟦⟧-resp-≈` from `Categories.FreeMonoidal`), if
-- `permute p ≈Term permute q` were derivable, then the model would
-- equate `σ_{A,A}` with `id_{A⊗A}` — false for `|A| ≥ 2`.
--
-- Hence the postulate as stated is *not provable* in the free SMC.
--
-- ### What IS Kelly's coherence theorem
--
-- Kelly's theorem says: two parallel structural morphisms in the free
-- symmetric monoidal category are equal iff they induce the same
-- permutation on positions.  Two `↭` derivations of `xs ↭ ys` produce
-- HomTerms that agree on positions ONLY IF the two derivations
-- determine the same underlying position permutation.  This is the
-- case automatically when xs (equivalently ys) has no duplicate
-- elements; with duplicates, distinct derivations can transpose
-- duplicate atoms, yielding distinct structural morphisms.
--
-- ### Resolution path for the consumer
--
-- The consumer `Discharge.FinalPermute.WithCoherence` invokes
-- `permute-≈Term-coherence` on `map⁺ vlab p` and `map⁺ vlab q` where
-- the underlying `p, q` are at the `List (Fin nV)` level (vertices of
-- a Linear hypergraph, hence no duplicates), and `vlab : Fin nV → X`
-- may be non-injective.  After `map vlab`, duplicates can occur, so
-- the consumer-level demand is genuinely the false-in-general
-- statement above.
--
-- The CORRECT residual postulate to drive completeness is therefore
-- the **Fin-level** variant (lists without duplicates → derivations
-- determine the same position permutation → `permute` HomTerms are
-- coherence-equal).  We expose that as the narrow field
-- `Fin-permute-≈Term-coherence` and additionally provide the
-- constructive cases of the X-level statement that ARE true (same
-- outer constructor, no σ on equal labels, etc.).
--
-- ## What this file provides
--
--   * `permute-refl-refl`              — constructive (≈-Term-refl).
--   * `permute-prep-prep`              — constructive (IH + ⊗-resp-≈).
--   * `permute-swap-swap-aligned`      — constructive (IH + ∘-resp-≈),
--                                        for matched `x, y` AND matched
--                                        intermediate.
--   * `permute-trans-trans-aligned`    — constructive (IH₁ + IH₂ + ∘-resp-≈),
--                                        for matched intermediate boundary.
--   * `permute-trans-refl-right`       — constructive (idˡ).
--   * `permute-trans-refl-left`        — constructive (idʳ).
--   * `permute-trans-assoc`            — constructive (assoc, sym).
--   * `FinCoherence` record with
--     `Fin-permute-≈Term-coherence`    — narrow residual postulate
--                                        (record field), restricted to
--                                        Fin-list permutations WITH the
--                                        explicit `Unique xs`
--                                        precondition that makes the
--                                        statement genuinely TRUE.
--                                        Drives the consumer.
--   * `WithFinCoherence` module
--                                      — derives the consumer's needs
--                                        (`permute-via-vlab` coherence,
--                                        and the bridge to the original
--                                        `permute (map⁺ vlab _)` form)
--                                        from the Fin-level postulate.
--
-- ## Trust-surface summary
--
-- Original: `permute-≈Term-coherence` — universally quantified over X,
-- xs, ys ∈ List X, with no Linearity/no-duplicate constraint.  FALSE
-- in general (counter-example above).  Hence the discharge cannot
-- match the original signature; instead, it produces the strictly
-- narrower (and TRUE) Fin-level statement that the consumer actually
-- needs.
--
-- Narrowed: `Fin-permute-≈Term-coherence` — quantified over Fin lists
-- with the `Unique xs` (no-duplicates) precondition.  This IS Kelly's
-- coherence theorem on the restricted domain.  Provable in principle
-- (~200-500 LOC depending on style), e.g., by interpreting through
-- the symmetric monoidal category of finite type-graded bijections,
-- or by a `solveM`-extension to cover the σ fragment.  Exposed here
-- as a record field rather than `postulate` so the trust surface is
-- explicit; a downstream consumer can either construct or postulate
-- the witness.
--
-- The constructive cases (same outer constructor, etc.) are
-- discharged without any postulate.
--
-- ## File is `--safe --with-K`-clean.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherence
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Constructive case 1: `refl`-`refl`.
--
-- Both derivations produce `id`; ≈-Term-refl suffices.

permute-refl-refl
  : ∀ {xs : List X}
  → permute (Perm.refl {xs = xs}) ≈Term permute (Perm.refl {xs = xs})
permute-refl-refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- Constructive case 2: `prep x p` vs `prep x q`.
--
-- Both produce `id ⊗₁ permute p` / `id ⊗₁ permute q`.  If we already
-- know `permute p ≈Term permute q` (the IH), then `⊗-resp-≈` settles
-- the goal.

permute-prep-prep
  : ∀ {x : X} {xs ys : List X} (p q : xs ↭ ys)
  → permute p ≈Term permute q
  → permute (Perm.prep x p) ≈Term permute (Perm.prep x q)
permute-prep-prep p q ih = ⊗-resp-≈ ≈-Term-refl ih

--------------------------------------------------------------------------------
-- Constructive case 3: `swap x y p` vs `swap x y q` with identical
-- outer labels and identical boundary lists for the recursive part.
--
-- Both produce `(id ⊗₁ id ⊗₁ permute *) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐`.
-- Given `permute p ≈Term permute q` (IH), `∘-resp-≈` and `⊗-resp-≈`
-- settle the goal.

permute-swap-swap-aligned
  : ∀ {x y : X} {xs ys : List X} (p q : xs ↭ ys)
  → permute p ≈Term permute q
  → permute (Perm.swap x y p) ≈Term permute (Perm.swap x y q)
permute-swap-swap-aligned p q ih =
  ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl ih))
           ≈-Term-refl

--------------------------------------------------------------------------------
-- Constructive case 4: `trans p₁ p₂` vs `trans q₁ q₂` with IDENTICAL
-- intermediate boundary lists (so `p₁, q₁ : xs ↭ zs` and
-- `p₂, q₂ : zs ↭ ys` for the SAME `zs`).
--
-- Both produce `permute p₂ ∘ permute p₁` / `permute q₂ ∘ permute q₁`.
-- Given the two IHs, `∘-resp-≈` settles the goal.
--
-- NOTE: when the intermediate boundaries DIFFER (e.g., `trans p₁ p₂`
-- with `p₁ : xs ↭ zs` vs `trans q₁ q₂` with `q₁ : xs ↭ ws` and
-- `zs ≢ ws`), the goal is NOT solvable by this scheme alone — it
-- requires the full Kelly coherence reduction (chain through ≈Term
-- using a common "normal form" for permutation morphisms; see the
-- residual postulate below).

permute-trans-trans-aligned
  : ∀ {xs zs ys : List X}
      (p₁ q₁ : xs ↭ zs) (p₂ q₂ : zs ↭ ys)
  → permute p₁ ≈Term permute q₁
  → permute p₂ ≈Term permute q₂
  → permute (Perm.trans p₁ p₂) ≈Term permute (Perm.trans q₁ q₂)
permute-trans-trans-aligned p₁ q₁ p₂ q₂ ih₁ ih₂ =
  ∘-resp-≈ ih₂ ih₁

--------------------------------------------------------------------------------
-- Constructive case 5: `trans p refl` ≈Term `permute p`.
--
-- `permute (trans p refl) = id ∘ permute p ≈Term permute p` (idˡ).

permute-trans-refl-right
  : ∀ {xs ys : List X} (p : xs ↭ ys)
  → permute (Perm.trans p Perm.refl) ≈Term permute p
permute-trans-refl-right p = idˡ

--------------------------------------------------------------------------------
-- Constructive case 6: `trans refl p` ≈Term `permute p`.
--
-- `permute (trans refl p) = permute p ∘ id ≈Term permute p` (idʳ).

permute-trans-refl-left
  : ∀ {xs ys : List X} (p : xs ↭ ys)
  → permute (Perm.trans Perm.refl p) ≈Term permute p
permute-trans-refl-left p = idʳ

--------------------------------------------------------------------------------
-- Constructive case 7: associativity of `trans`.
--
-- `permute (trans (trans p q) r) = permute r ∘ permute q ∘ permute p`
-- `permute (trans p (trans q r)) = (permute r ∘ permute q) ∘ permute p`
-- Difference is just `assoc`.

permute-trans-assoc
  : ∀ {xs ys zs ws : List X}
      (p : xs ↭ ys) (q : ys ↭ zs) (r : zs ↭ ws)
  → permute (Perm.trans (Perm.trans p q) r)
    ≈Term permute (Perm.trans p (Perm.trans q r))
permute-trans-assoc p q r = ≈-Term-sym assoc

--------------------------------------------------------------------------------
-- ## The residual narrow postulate (record field).
--
-- The remaining "hard" cases that this file does NOT discharge
-- constructively are:
--
--   (a) `p = refl, q = trans/swap/prep` with non-trivial q acting on
--       the same boundary list (e.g., `q : xs ↭ xs` non-trivial).
--       This requires the full Kelly coherence reduction.
--
--   (b) `p, q = trans _ _` with DIFFERENT intermediate boundaries.
--       Requires composing chain-rewrites along the trans path.
--
--   (c) `p, q` with different outer constructors that happen to
--       coincide on boundary lists (e.g., one is `prep` and another
--       is `trans (swap …) …` factoring through a different path).
--
-- All of these reduce, via the case-split on derivations, to the
-- SAME core obligation: structural morphisms in the free SMC with
-- the same underlying *position permutation* are `≈Term`-equal.
--
-- As noted in the file header, this is true at the Fin level (lists
-- without duplicates, hence position permutation determined by the
-- boundary lists), and FALSE at the X level in general.
--
-- We expose the Fin-level statement as a record field, plus the
-- machinery to derive the X-level statement on the SPECIFIC inputs
-- that the consumer uses (vlab-lift of Fin-level derivations).

record FinCoherence : Set where
  field
    -- The Fin-level coherence statement.  Restricted to lists at the
    -- Fin level WITHOUT DUPLICATES, which is the case in the consumer
    -- (Linear hypergraph vertices, where each vertex appears at most
    -- once in any stack).
    --
    -- The `Unique xs` precondition is the critical wedge that makes
    -- this statement TRUE (cf. the σ-on-equal-labels counter-example
    -- at the X-level documented in the header):
    --
    --   * No-duplicate Fin lists determine a UNIQUE position
    --     permutation (`pos i ↦ unique j such that xs[i] ≡ ys[j]`).
    --   * Hence any two `↭` derivations of the same `xs ↭ ys`
    --     necessarily encode the same position permutation.
    --   * By Kelly's coherence theorem for symmetric monoidal
    --     categories, the corresponding structural morphisms (built
    --     from `id, σ, α, ⊗, ∘` only) are `≈Term`-equal.
    --
    -- After `PermProp.map⁺ vlab`, the X-level lists may acquire
    -- duplicates (if vlab is non-injective), but the underlying
    -- position permutation is still determined by the Fin-level
    -- structure — that is what makes the statement TRUE despite the
    -- X-level surface having duplicates.
    Fin-permute-≈Term-coherence
      : ∀ {n} {xs ys : List (Fin n)}
          (xs-uniq : Unique xs)
          (vlab : Fin n → X)
          (p q : xs ↭ ys)
      → permute-via-vlab vlab p ≈Term permute-via-vlab vlab q

--------------------------------------------------------------------------------
-- ## Derivation of the full X-level statement on the consumer's usage.
--
-- The original `permute-≈Term-coherence` is stated for arbitrary
-- `xs ys : List X`.  As analysed in the header, this is false in
-- general.  The consumer (`FinalPermute.WithCoherence`) only ever
-- invokes it on lists of the form `map vlab _` for some `vlab : Fin n → X`
-- and `_ : List (Fin n)`.  We expose the derivation for that specific
-- usage pattern.

module WithFinCoherence (fc : FinCoherence) where
  open FinCoherence fc public

  ------------------------------------------------------------------------
  -- The consumer's actual demand: `permute-via-vlab` coherence,
  -- derived from the Fin-level coherence.  This is exactly the helper
  -- `permute-via-vlab-≈Term-coherence` consumed in
  -- `Discharge.FinalPermute.WithCoherence`, but obtained from a
  -- strictly narrower postulate (the Fin-level statement, with the
  -- Linearity / no-duplicates precondition encoded as `Unique xs`).

  permute-via-vlab-≈Term-coherence-from-Fin
    : ∀ {n} {xs ys : List (Fin n)}
        (xs-uniq : Unique xs)
        (vlab : Fin n → X)
        (p q : xs ↭ ys)
    → permute-via-vlab vlab p ≈Term permute-via-vlab vlab q
  permute-via-vlab-≈Term-coherence-from-Fin xs-uniq vlab p q =
    Fin-permute-≈Term-coherence xs-uniq vlab p q

  ------------------------------------------------------------------------
  -- BACK-COMPATIBLE BRIDGE to the original (false-in-general)
  -- `permute-≈Term-coherence` for the SPECIFIC case the consumer
  -- needs.
  --
  -- Given two derivations at the X level that arise as `map⁺ vlab pₓ`
  -- and `map⁺ vlab qₓ` for underlying Fin-level pₓ, qₓ on a unique
  -- Fin list, the X-level equality follows from the Fin-level
  -- coherence.

  permute-≈Term-coherence-from-Fin-mapped
    : ∀ {n} {xs ys : List (Fin n)}
        (xs-uniq : Unique xs)
        (vlab : Fin n → X)
        (p q : xs ↭ ys)
    → permute (PermProp.map⁺ vlab p) ≈Term permute (PermProp.map⁺ vlab q)
  permute-≈Term-coherence-from-Fin-mapped xs-uniq vlab p q =
    Fin-permute-≈Term-coherence xs-uniq vlab p q
