{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- X-to-Fin lifting for permutations.
--
-- ## Goal
--
-- Given a permutation `r : map vlab is ↭ map vlab js` between two
-- mapped lists, produce a Fin-level pre-image permutation `r' : is ↭ js'`
-- such that the resulting `permute` HomTerms agree up to `≈Term`:
--
--   permute r ≈Term permute (PermProp.map⁺ vlab r')
--
-- where `js'` is determined by `r` (and `map vlab js' ≡ map vlab js`).
--
-- This is the missing piece that lets us reduce X-level permutation
-- coherence on mapped lists to Fin-level coherence (where `Unique` of
-- the underlying Fin list buys us full Kelly coherence).
--
-- ## Strategy
--
-- The stdlib provides `PermProp.↭-map-inv` which produces a Fin-level
-- pre-image of any X-level permutation between mapped lists:
--
--   ↭-map-inv : map vlab xs ↭ ys → ∃ ys'. ys ≡ map vlab ys' × xs ↭ ys'
--
-- We mirror its case analysis and prove the `permute`-preservation
-- equation by induction.  The non-trivial cases:
--
--   * `xs ≡ []`: any X-level perm of `[]` has `permute r ≈Term id`,
--     and the Fin pre-image is `↭-refl : [] ↭ []` with `permute refl = id`.
--   * `xs ≡ [k]`: similarly via the singleton lemma.
--   * `xs ≡ _ ∷ _ ∷ _`: structural induction on `r` mirrors the
--     constructor structure (refl, prep, swap, trans).
--
-- ## Why Unique is NOT needed for the basic lift
--
-- The basic lift `↭-from-map` does NOT require `Unique xs`.  The map
-- structure alone determines a Fin-level pre-image up to `permute`-
-- equality.  This is because:
--
--   * `prep _ ρ` and `swap _ _ ρ` only constrain X-level heads; the
--     Fin-level heads are recovered from `xs`'s structure (pattern
--     matching).
--   * `refl` lifts to `↭-refl`.
--   * `trans` lifts compositionally — each half is inverted independently.
--
-- `Unique` becomes relevant only when we want to SPECIALISE to the
-- self-loop case `is ↭ is`.  See `X-self-loop-lift-via-injective` below.
--
-- ## Self-loop residual
--
-- For `r : map vlab is ↭ map vlab is`, the basic lift gives
-- `r' : is ↭ ys''` with `map vlab is ≡ map vlab ys''`.  To strengthen
-- this to `r' : is ↭ is`, we need an EXTRA hypothesis: `vlab` injective
-- on `is`'s elements (in fact, on the union of `is` and `ys''`).
--
-- This is NOT free from `Unique is` alone — see the counter-example:
--   `is = [0, 1]`, `vlab 0 = vlab 1 = x`, `r = swap x x refl`.
--   Then `Unique is` holds, but `↭-map-inv r = (1 ∷ 0 ∷ [], refl, swap 0 1 refl)`,
--   which is NOT a self-loop on `is`.
--
-- We therefore expose two residuals:
--   * `↭-from-map` (basic lift, NO Unique needed): unconditional.
--   * `X-self-loop-lift-via-injective` (requires `vlab` injective on
--     the underlying Fin indices): constructive consequence of `↭-from-map`
--     plus a small injectivity bridge.
--
-- ## File is `--safe --with-K`-clean.  No new postulates.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.XToFinLift
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PermuteCoherenceFin sig
  using (SelfLoopPostulate; module SelfLoopPostulate)

open import Categories.Category using (Category)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; [_]; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open Perm using (_↭_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Product using (Σ; ∃; _×_; _,_; proj₁; proj₂; -,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Helper: any X-level perm on `[]` has `permute ≈Term id`.
--
-- This is the X-level analogue of `permute-empty-id-aux` in
-- `PermuteCoherenceFin.agda` (which is at the Fin level after `map⁺`).
-- We need the X-level version because `↭-map-inv` may collapse the
-- entire X-perm into `↭-refl` at the Fin level, and we need a way to
-- handle the "leftover" X-perm structure.

permute-empty-id-X
  : (r : ([] {A = X}) Perm.↭ [])
  → permute r ≈Term id
permute-empty-id-X Perm.refl = ≈-Term-refl
permute-empty-id-X (Perm.trans r₁ r₂)
  with PermProp.↭-empty-inv r₂
... | refl =
  let ih₁ = permute-empty-id-X r₁
      ih₂ = permute-empty-id-X r₂
  in begin
       permute r₂ ∘ permute r₁
         ≈⟨ ∘-resp-≈ ih₂ ih₁ ⟩
       id ∘ id
         ≈⟨ idˡ ⟩
       id
     ∎

--------------------------------------------------------------------------------
-- ## Helper: any X-level perm on `[x]` has `permute ≈Term id`.

permute-singleton-id-X
  : ∀ {x : X} (r : (x ∷ []) Perm.↭ (x ∷ []))
  → permute r ≈Term id
permute-singleton-id-X Perm.refl = ≈-Term-refl
permute-singleton-id-X (Perm.prep _ r') =
  -- r' : [] ↭ []  (head pattern-matched).
  let ih = permute-empty-id-X r'
  in begin
       id ⊗₁ permute r'
         ≈⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
       id ⊗₁ id
         ≈⟨ id⊗id≈id ⟩
       id
     ∎
permute-singleton-id-X (Perm.trans r₁ r₂)
  with PermProp.↭-singleton-inv r₂
... | refl =
  let ih₁ = permute-singleton-id-X r₁
      ih₂ = permute-singleton-id-X r₂
  in begin
       permute r₂ ∘ permute r₁
         ≈⟨ ∘-resp-≈ ih₂ ih₁ ⟩
       id ∘ id
         ≈⟨ idˡ ⟩
       id
     ∎

--------------------------------------------------------------------------------
-- ## The main lift: `↭-from-map`.
--
-- Given any `r : map vlab xs ↭ ys`, produce `(ys', refl, r')`
-- with `r' : xs ↭ ys'`, `ys ≡ map vlab ys'`, and
-- `permute r ≈Term permute (map⁺ vlab r')` (after refl-rewriting on
-- `ys ≡ map vlab ys'`).
--
-- This is the `permute`-preserving version of `PermProp.↭-map-inv`.
-- The case structure mirrors that of `↭-map-inv` exactly.

-- The result type, expressed via Σ for clarity.

LiftResult
  : ∀ {n} (vlab : Fin n → X) (xs : List (Fin n)) (ys : List X)
  → (r : map vlab xs Perm.↭ ys) → Set
LiftResult {n} vlab xs ys r =
  Σ (List (Fin n)) λ ys' →
  Σ (ys ≡ map vlab ys') λ ys-eq →
  Σ (xs Perm.↭ ys') λ r' →
    permute (subst (map vlab xs Perm.↭_) ys-eq r)
    ≈Term permute (PermProp.map⁺ vlab r')

↭-from-map
  : ∀ {n} (vlab : Fin n → X) (xs : List (Fin n)) {ys : List X}
  → (r : map vlab xs Perm.↭ ys)
  → LiftResult vlab xs ys r
↭-from-map vlab []        {ys} r =
  -- Any r : [] ↭ ys forces ys ≡ [].
  -- `permute r ≈Term id ≈Term permute (map⁺ vlab refl) = permute refl = id`.
  [] , ys-eq , Perm.refl , goal
  where
    ys-eq : ys ≡ []
    ys-eq = PermProp.↭-empty-inv (Perm.↭-sym r)

    goal : permute (subst (map vlab ([] {A = Fin _}) Perm.↭_) ys-eq r)
           ≈Term permute (PermProp.map⁺ vlab (Perm.refl {xs = []}))
    goal = permute-empty-id-X (subst (map vlab [] Perm.↭_) ys-eq r)
↭-from-map vlab (k ∷ [])  {ys} r =
  -- Any r : [vlab k] ↭ ys forces ys ≡ [vlab k].
  (k ∷ []) , ys-eq , Perm.refl , goal
  where
    ys-eq : ys ≡ map vlab (k ∷ [])
    ys-eq = PermProp.↭-singleton-inv (Perm.↭-sym r)

    goal : permute (subst (map vlab (k ∷ []) Perm.↭_) ys-eq r)
           ≈Term permute (PermProp.map⁺ vlab (Perm.refl {xs = k ∷ []}))
    goal = permute-singleton-id-X (subst (map vlab (k ∷ []) Perm.↭_) ys-eq r)
↭-from-map vlab (k₁ ∷ k₂ ∷ rest) {ys} Perm.refl =
  -- `r = refl : map vlab (k₁ ∷ k₂ ∷ rest) ↭ map vlab (k₁ ∷ k₂ ∷ rest)`.
  -- Fin pre-image: `refl : k₁ ∷ k₂ ∷ rest ↭ k₁ ∷ k₂ ∷ rest`.
  (k₁ ∷ k₂ ∷ rest) , refl , Perm.refl , ≈-Term-refl
↭-from-map vlab (k₁ ∷ k₂ ∷ rest) {ys} (Perm.prep _ ρ)
  with ↭-from-map vlab (k₂ ∷ rest) ρ
... | (ys'' , refl , ρ' , ih-eq) =
  -- ρ : map vlab (k₂ ∷ rest) ↭ ys'.  Inversion gives ρ' : k₂ ∷ rest ↭ ys''
  -- with ys' ≡ map vlab ys''.  After refl-matching on ys' ≡ map vlab ys'',
  -- ρ : map vlab (k₂ ∷ rest) ↭ map vlab ys'' (definitionally).
  -- Outer Fin perm: prep k₁ ρ'.  permute (prep _ ρ) = id ⊗ permute ρ.
  (k₁ ∷ ys'') , refl , Perm.prep k₁ ρ' , goal
  where
    goal : id ⊗₁ permute ρ
           ≈Term id ⊗₁ permute (PermProp.map⁺ vlab ρ')
    goal = ⊗-resp-≈ ≈-Term-refl ih-eq
↭-from-map vlab (k₁ ∷ k₂ ∷ rest) {ys} (Perm.swap _ _ ρ)
  with ↭-from-map vlab rest ρ
... | (ys'' , refl , ρ' , ih-eq) =
  -- ρ : map vlab rest ↭ ys'.  Inversion: ρ' : rest ↭ ys'' with ys' ≡ map vlab ys''.
  -- Outer Fin perm: swap k₁ k₂ ρ' : k₁ ∷ k₂ ∷ rest ↭ k₂ ∷ k₁ ∷ ys''.
  (k₂ ∷ k₁ ∷ ys'') , refl , Perm.swap k₁ k₂ ρ' , goal
  where
    goal : (id ⊗₁ (id ⊗₁ permute ρ)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
           ≈Term (id ⊗₁ (id ⊗₁ permute (PermProp.map⁺ vlab ρ'))) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
    goal = ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl ih-eq))
                    ≈-Term-refl
↭-from-map vlab (k₁ ∷ k₂ ∷ rest) {ys} (Perm.trans ρ₁ ρ₂)
  with ↭-from-map vlab (k₁ ∷ k₂ ∷ rest) ρ₁
... | (ys'' , refl , ρ₁' , ih-eq₁)
  with ↭-from-map vlab ys'' ρ₂
... | (ys''' , refl , ρ₂' , ih-eq₂) =
  -- ρ₁ : map vlab xs ↭ ys₁.  Inversion: ρ₁' : xs ↭ ys'' with ys₁ ≡ map vlab ys''.
  -- ρ₂ : ys₁ ↭ ys.  After ys₁ ≡ map vlab ys'' (refl-matched),
  --    ρ₂ : map vlab ys'' ↭ ys.  Inversion: ρ₂' : ys'' ↭ ys''' with ys ≡ map vlab ys'''.
  -- Outer Fin perm: trans ρ₁' ρ₂' : xs ↭ ys'''.
  ys''' , refl , Perm.trans ρ₁' ρ₂' , goal
  where
    goal : permute ρ₂ ∘ permute ρ₁
           ≈Term permute (PermProp.map⁺ vlab ρ₂') ∘ permute (PermProp.map⁺ vlab ρ₁')
    goal = ∘-resp-≈ ih-eq₂ ih-eq₁

--------------------------------------------------------------------------------
-- ## Specialisation to the self-loop case.
--
-- For `r : map vlab is ↭ map vlab is`, the basic lift gives a Fin perm
-- `r' : is ↭ ys''` with `map vlab is ≡ map vlab ys''`.  To strengthen
-- this to `r' : is ↭ is`, we need an additional hypothesis: the X-level
-- equality `map vlab is ≡ map vlab ys''` must force `is ≡ ys''`.
--
-- This holds when `vlab` is injective on the underlying Fin indices.

-- Helper: if `vlab` is injective and `map vlab xs ≡ map vlab ys`, then
-- `xs ≡ ys`.

private
  cong-head : ∀ {A : Set} {l₁ l₂ : List A} {a₁ a₂ : A}
            → a₁ ∷ l₁ ≡ a₂ ∷ l₂ → a₁ ≡ a₂
  cong-head refl = refl

  cong-tail : ∀ {A : Set} {l₁ l₂ : List A} {a₁ a₂ : A}
            → a₁ ∷ l₁ ≡ a₂ ∷ l₂ → l₁ ≡ l₂
  cong-tail refl = refl

  map-injective
    : ∀ {n} (vlab : Fin n → X)
    → (∀ {i j} → vlab i ≡ vlab j → i ≡ j)
    → ∀ (xs ys : List (Fin n))
    → map vlab xs ≡ map vlab ys
    → xs ≡ ys
  map-injective vlab inj []         []         _   = refl
  map-injective vlab inj []         (_ ∷ _)    ()
  map-injective vlab inj (_ ∷ _)    []         ()
  map-injective vlab inj (k₁ ∷ ks₁) (k₂ ∷ ks₂) eq
    with inj (cong-head eq) | map-injective vlab inj ks₁ ks₂ (cong-tail eq)
  ... | refl | refl = refl

-- UIP from --with-K.
private
  uip : ∀ {A : Set} {a b : A} (p q : a ≡ b) → p ≡ q
  uip refl refl = refl

-- The self-loop lift assuming injectivity.  This is constructive given
-- the basic `↭-from-map`.

X-self-loop-lift-via-injective
  : ∀ {n} (vlab : Fin n → X)
  → (vlab-inj : ∀ {i j} → vlab i ≡ vlab j → i ≡ j)
  → ∀ {is : List (Fin n)}
  → (r : map vlab is Perm.↭ map vlab is)
  → Σ (is Perm.↭ is) λ r' →
      permute r ≈Term permute (PermProp.map⁺ vlab r')
X-self-loop-lift-via-injective vlab vlab-inj {is} r
  with ↭-from-map vlab is r
... | (ys'' , ys-eq , r' , r-eq)
  with map-injective vlab vlab-inj is ys'' ys-eq
... | refl =
  -- After is ≡ ys'' (by map-injective), r' : is ↭ is and r-eq has the
  -- target form after we identify `ys-eq : map vlab is ≡ map vlab is`
  -- with `refl` (via UIP).
  r' , goal
  where
    ys-eq-is-refl : ys-eq ≡ refl
    ys-eq-is-refl = uip ys-eq refl

    -- `r-eq` has type:
    --   permute (subst (map vlab is ↭_) ys-eq r)
    --     ≈Term permute (map⁺ vlab r')
    -- After ys-eq ≡ refl, the subst collapses and r-eq's LHS becomes `permute r`.
    goal : permute r ≈Term permute (PermProp.map⁺ vlab r')
    goal = subst (λ eq → permute (subst (map vlab is Perm.↭_) eq r)
                          ≈Term permute (PermProp.map⁺ vlab r'))
                 ys-eq-is-refl
                 r-eq

--------------------------------------------------------------------------------
-- ## Bridging `Unique is` to `vlab`-injectivity on `is`'s elements.
--
-- The basic injectivity hypothesis `∀ {i j} → vlab i ≡ vlab j → i ≡ j`
-- (global injectivity) is STRONGER than what `Unique is` gives.  Under
-- `Unique is`, we only get the WEAKER claim that distinct indices in
-- `is` map to distinct X values — but that requires `vlab` to actually
-- distinguish them, which is the very claim we'd want.
--
-- Concretely, `Unique is` is structural (about `is`'s deduplication);
-- it does NOT preclude `vlab` collapsing different indices.
--
-- ⚠ Therefore: the consumer of `X-self-loop-lift-via-injective` must
-- supply `vlab-inj` from external context (e.g., from the
-- Hypergraph's source/target structure).
--
-- ## What's strictly narrower than X-permute-self-loop-id?
--
-- The original `X-permute-self-loop-id` is:
--   ∀ {xs : List X} (r : xs ↭ xs) → permute r ≈Term id
--
-- Via `X-self-loop-lift-via-injective`, we reduce this (for
-- mapped-list xs) to:
--   * `vlab`-injectivity (precondition).
--   * `permute (map⁺ vlab r') ≈Term id` for the Fin-level r' (which is
--     exactly the `Fin-permute-self-loop-id` of
--     `PermuteCoherenceFin.SelfLoopPostulate`).
--
-- The Fin-level claim with `Unique is` is the residual already
-- partially discharged in `Discharge/Sub/SelfLoop.agda`.

--------------------------------------------------------------------------------
-- ## Packaged reduction: from the Fin-level self-loop residual to the
--    X-level self-loop on mapped lists.

record InjectiveVlab {n} (vlab : Fin n → X) : Set where
  field
    vlab-injective : ∀ {i j : Fin n} → vlab i ≡ vlab j → i ≡ j

-- Given an injective vlab and the Fin-level self-loop postulate
-- (which is partially discharged in `Discharge/Sub/SelfLoop.agda`),
-- we can constructively close the X-level self-loop CASE on
-- mapped lists.
--
-- That is, the X-level claim
--   permute r ≈Term id
-- for `r : map vlab is ↭ map vlab is` follows from:
--   1. The basic lift `↭-from-map`.
--   2. The map-injectivity bridge `map-injective`.
--   3. The Fin-level self-loop `Fin-permute-self-loop-id` on `is`.
--
-- Crucially: `Unique is` is needed only for step 3 (the Fin-level
-- postulate), not for the lift itself.

X-self-loop-id-on-mapped
  : ∀ {n} (vlab : Fin n → X)
      (inj : InjectiveVlab vlab)
      (slp : SelfLoopPostulate)
      {is : List (Fin n)} (uniq : Unique is)
      (r : map vlab is Perm.↭ map vlab is)
  → permute r ≈Term id
X-self-loop-id-on-mapped vlab inj slp uniq r =
  let open InjectiveVlab inj
      open SelfLoopPostulate slp
      lift-result = X-self-loop-lift-via-injective vlab vlab-injective r
      r'   = proj₁ lift-result
      r-eq = proj₂ lift-result
      fin-id = Fin-permute-self-loop-id uniq vlab r'
  in begin
       permute r
         ≈⟨ r-eq ⟩
       permute (PermProp.map⁺ vlab r')
         ≈⟨ fin-id ⟩
       id
     ∎
