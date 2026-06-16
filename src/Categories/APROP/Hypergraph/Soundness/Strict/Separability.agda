{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- LEFT-frame separability of the strict decoder — what IS true.
--
-- Intended as the MIRROR of the RIGHT-frame `term-sepˢ` (in `Strict.Decoder`),
-- which fixes a SUFFIX `R` of the stack untouched (`xs ++ R`, frame on the
-- right via stdlib `++⁺ʳ`) and proves the run factors as `(run on xs) ⊗ˢ id`.
--
-- OBSTRUCTION (mathematical, NOT a proof-engineering gap; see the long note at
-- the foot of this file).  The TERM-LEVEL left frame
--   term-sepˢ-ˡ :
--     castˢ … (proj₂ (process-edgesˢ es (L ++ xs)))
--       ≈ˢ idˢ {map vl L} ⊗ˢ proj₂ (process-edgesˢ es xs)
-- is FALSE for any block that fires at least once.  The strict `edge-stepˢ`
-- PREPENDS the fired output `eout e` to the front of the residual: on `L ++ xs`
-- it produces stack `eout e ++ (L ++ rest)`, burying the untouched prefix `L`
-- AFTER `eout e`.  Hence `map vl L` is NOT a left prefix of the run's codomain,
-- so the `idˢ {map vl L} ⊗ˢ_` framing cannot even be TYPED (its codomain
-- coherence `Q` would equate two genuinely different lists).  The suffix `R`
-- survives in the right frame precisely because outputs prepend; the only
-- non-degenerate separability for this decoder is therefore the RIGHT frame
-- (`term-sepˢ`), already proven.
--
-- DELIVERED (all true, postulate-free, `--safe --without-K`):
--   * `permuteˢ-frameˡ` — the cast-kit `idˢ ⊗ˢ_`-frame for stdlib `++⁺ˡ`.
--     This IS a genuine mirror of `Perm′.permuteˢ-frame`: a PURE PERMUTATION
--     (no firing) preserves a left prefix, so the left frame holds for it.
--   * the LEFT-frame stack-search lemmas `extract-elem-++ˡ-left`,
--     `extract-prefix-++ˡ-left` (+ their `nothing`-mirrors): on `L ++ xs` with
--     `L` disjoint from the searched keys, the search skips `L` and returns
--     residual `L ++ rest` with the genuine swap-threaded derivation.  These
--     ARE the left mirrors of `SeparableStack`'s `extract-*-++ˡ` and remain
--     sound and reusable.
--
-- The `stack-sepˢ-ˡ` / `layer-sepˢ-ˡ` / `term-sepˢ-ˡ` of the original brief are
-- intentionally ABSENT: they are not theorems (see above).
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Separability
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (extract-prefix; extract-elem)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decoder sig _≟X_ public

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; map-++)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary.Decidable using (yes; no)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- The decoder fixes `H`; we work `vl`-relatively, re-using the `Perm′`
-- instance (at `Fin H.nV`/`H.vl`) and the full cast kit re-exported by
-- `Strict.Decoder`.
--------------------------------------------------------------------------------

module StrictSep (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  open StrictDecoder H public

  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (++⁺ˡ)

  ------------------------------------------------------------------------
  -- ## permuteˢ-frameˡ — the LEFT cast-kit frame.
  --
  -- Mirror of `Perm′.permuteˢ-frame`: the stdlib LEFT residual frame `++⁺ˡ L`
  -- factors through `idˢ {map vl L} ⊗ˢ_`.  Induction on `L`.

  -- the stdlib LEFT residual frame `++⁺ˡ L` factors through `idˢ ⊗ˢ_`
  permuteˢ-frameˡ
    : ∀ {xs ys : List (Fin H.nV)} (L : List (Fin H.nV)) (p : xs Perm.↭ ys)
    → castˢ (map-++ vl L xs) (map-++ vl L ys) (permuteˢ (++⁺ˡ L p))
      ≈ˢ idˢ {map vl L} ⊗ˢ permuteˢ p
  permuteˢ-frameˡ {xs} {ys} [] p =
    -- map-++ vl [] xs ≡ refl (both sides reduce to `map vl xs`), so the
    -- cast vanishes and we need `permuteˢ p ≈ˢ idˢ {[]} ⊗ˢ permuteˢ p`.
    ≈-trans (cast-id-frame p) (≈-sym (⊗-unitˡˢ (permuteˢ p)))
    where
      cast-id-frame
        : (p : xs Perm.↭ ys)
        → castˢ (map-++ vl [] xs) (map-++ vl [] ys) (permuteˢ p)
          ≈ˢ permuteˢ p
      cast-id-frame p = ≡⇒≈ˢ refl
  permuteˢ-frameˡ {xs} {ys} (v ∷ L) p =
    -- permuteˢ (++⁺ˡ (v∷L) p) = idˢ {vl v ∷ []} ⊗ˢ permuteˢ (++⁺ˡ L p);
    -- IH gives the cast of the inner frame = idˢ {map vl L} ⊗ˢ permuteˢ p;
    -- re-associate `idˢ {vl v ∷[]} ⊗ˢ (idˢ {map vl L} ⊗ˢ permuteˢ p)` to
    -- `(idˢ {vl v ∷[]} ⊗ˢ idˢ {map vl L}) ⊗ˢ permuteˢ p` and collapse the
    -- two ids with `⊗-id`.  Map of cons reduces, so the head frame is cast-free.
    ≈-trans
      (cast-⊗-frame (idˢ {vl v ∷ []})
        (map-++ vl L xs) (map-++ vl L ys) (permuteˢ (++⁺ˡ L p)) _ _)
      (≈-trans (⊗-resp ≈-refl (permuteˢ-frameˡ L p))
        (≈-trans (≈-sym (⊗-assocˢ (idˢ {vl v ∷ []}) (idˢ {map vl L})
                                  (permuteˢ p)))
          (≈-trans (cast-resp _ _ (⊗-resp ⊗-id ≈-refl))
            (cast-id-collapse))))
    where
      -- the residual `⊗-assocˢ` cast on `idˢ ⊗ˢ permuteˢ p` is identity-typed
      -- (its domain/codomain proofs are between definitionally-equal lists)
      cast-id-collapse
        : castˢ (++-assoc (vl v ∷ []) (map vl L) (map vl xs))
                (++-assoc (vl v ∷ []) (map vl L) (map vl ys))
            (idˢ {vl v ∷ map vl L} ⊗ˢ permuteˢ p)
          ≈ˢ idˢ {vl v ∷ map vl L} ⊗ˢ permuteˢ p
      cast-id-collapse =
        ≡⇒≈ˢ (cast-irrel _ refl _ refl (idˢ {vl v ∷ map vl L} ⊗ˢ permuteˢ p))

  ------------------------------------------------------------------------
  -- ## LEFT-frame stack lemmas.
  --
  -- On `L ++ xs`, when no input vertex of the edge block lives in `L`,
  -- `extract-elem`/`extract-prefix` walk past `L` (every cons in `L` is a
  -- `no`-skip) and find the prefix in `xs` with residual `L ++ rest`.  These
  -- lemmas pin the RESIDUAL LIST only (`proj₁`); the firing decision and
  -- residual are `(found-in-xs) framed by L on the left`.  The genuine
  -- `↭`-derivation differs from `++⁺ˡ L p` (it threads each `k` past all of
  -- `L` via swaps) and is handled separately at the term level.
  ------------------------------------------------------------------------

  -- The genuine `↭`-derivation `extract-elem k (L ++ xs)` produces when `k∉L`
  -- and `k` is found in `xs` with derivation `p : xs ↭ k ∷ rest`: at each
  -- `no`-skip layer of `L` it threads `k` past the head via `swap`.
  elemDerivˡ
    : ∀ (k : Fin H.nV) (L : List (Fin H.nV))
        {xs rest : List (Fin H.nV)}
    → xs Perm.↭ k ∷ rest
    → (L ++ xs) Perm.↭ k ∷ (L ++ rest)
  elemDerivˡ k []      p = p
  elemDerivˡ k (x ∷ L) p =
    Perm.trans (Perm.prep x (elemDerivˡ k L p)) (Perm.swap x k Perm.refl)

  -- `extract-elem k (L ++ xs)` finds `k` in `xs` with residual `L ++ rest`
  -- and derivation `elemDerivˡ k L p`.
  extract-elem-++ˡ-left
    : ∀ (k : Fin H.nV) (L xs : List (Fin H.nV))
        {rest : List (Fin H.nV)} {p : xs Perm.↭ k ∷ rest}
    → extract-elem k L ≡ nothing
    → extract-elem k xs ≡ just (rest , p)
    → extract-elem k (L ++ xs) ≡ just (L ++ rest , elemDerivˡ k L p)
  extract-elem-++ˡ-left k []       xs eqL eqxs = eqxs
  extract-elem-++ˡ-left k (x ∷ L) xs eqL eqxs with x ≟F k
  ... | yes refl with eqL
  ...   | ()
  extract-elem-++ˡ-left k (x ∷ L) xs eqL eqxs | no ¬q
    with extract-elem k L in eqL'
  ... | nothing
        rewrite extract-elem-++ˡ-left k L xs eqL' eqxs = refl

  -- `extract-prefix ks (L ++ xs)`, when `ks ∩ L = ∅` and `ks` is found in `xs`
  -- with residual `rest`, finds it with residual `L ++ rest` (the firing
  -- decision and residual list are `L`-framed).  We pin the FULL `just`-value;
  -- the derivation `D` is built recursively from `elemDerivˡ`/the IH and named
  -- via a `with`-abstraction, so the codomain matches `(k ∷ ks)`'s genuine
  -- recursion.  This is the LEFT mirror of `SeparableStack.extract-prefix-++ˡ`
  -- (whose derivation was the clean `prefix-++ˡ-perm ks (++⁺ʳ R p)`; here it is
  -- the swap-threaded form, kept opaque and only consumed via `permuteˢ`).
  extract-prefix-++ˡ-left
    : ∀ (ks L xs : List (Fin H.nV))
        {rest : List (Fin H.nV)} {p : xs Perm.↭ ks ++ rest}
    → All (λ k → extract-elem k L ≡ nothing) ks
    → extract-prefix ks xs ≡ just (rest , p)
    → Σ[ D ∈ (L ++ xs) Perm.↭ ks ++ (L ++ rest) ]
        extract-prefix ks (L ++ xs) ≡ just (L ++ rest , D)
  extract-prefix-++ˡ-left []       L xs {rest} {p} dis eq with eq
  ... | refl = Perm.refl , refl
  extract-prefix-++ˡ-left (k ∷ ks) L xs (dk ∷ dks) eq
    with extract-elem k xs in eqe
  extract-prefix-++ˡ-left (k ∷ ks) L xs (dk ∷ dks) eq | just (xs' , pe)
    with extract-prefix ks xs' in eqp
  extract-prefix-++ˡ-left (k ∷ ks) L xs {rest} {p} (dk ∷ dks) eq
    | just (xs' , pe) | just (rest' , pp) with eq
  ... | refl
        with extract-prefix-++ˡ-left ks L xs' dks eqp
  ...     | (D' , eqD')
            rewrite extract-elem-++ˡ-left k L xs dk eqe
                  | eqD' =
            ( Perm.trans (elemDerivˡ k L pe) (Perm.prep k D')
            , refl )

  -- NOTHING-mirror for `extract-elem` (LEFT prefix): `k ∉ L` and `k ∉ xs`
  -- ⇒ `k ∉ L ++ xs`.  Induction on `L`.
  extract-elem-++ˡ-left-nothing
    : ∀ (k : Fin H.nV) (L xs : List (Fin H.nV))
    → extract-elem k L ≡ nothing
    → extract-elem k xs ≡ nothing
    → extract-elem k (L ++ xs) ≡ nothing
  extract-elem-++ˡ-left-nothing k []       xs eqL eqxs = eqxs
  extract-elem-++ˡ-left-nothing k (x ∷ L) xs eqL eqxs with x ≟F k
  ... | yes refl with eqL
  ...   | ()
  extract-elem-++ˡ-left-nothing k (x ∷ L) xs eqL eqxs | no ¬q
    with extract-elem k L in eqL'
  ... | nothing
        rewrite extract-elem-++ˡ-left-nothing k L xs eqL' eqxs = refl

  -- NOTHING-mirror for `extract-prefix` (LEFT prefix): `ks ∩ L = ∅` and `ks`
  -- not found in `xs` ⇒ not found in `L ++ xs`.  Mirror of
  -- `SeparableStack.extract-prefix-++ˡ-nothing`.
  extract-prefix-++ˡ-left-nothing
    : ∀ (ks L xs : List (Fin H.nV))
    → All (λ j → extract-elem j L ≡ nothing) ks
    → extract-prefix ks xs ≡ nothing
    → extract-prefix ks (L ++ xs) ≡ nothing
  extract-prefix-++ˡ-left-nothing []       L xs _          ()
  extract-prefix-++ˡ-left-nothing (k ∷ ks) L xs (dk ∷ dks) eqn
    with extract-elem k xs in eqe
  -- head not found in `xs`: by disjointness not in `L`, so not in `L ++ xs`.
  ... | nothing
        rewrite extract-elem-++ˡ-left-nothing k L xs dk eqe = refl
  -- head found in `xs` with residual `xs'`: tail must fail; recurse on `ks`
  -- over `xs'`, re-locating `k` in `L ++ xs` (`extract-elem-++ˡ-left`).
  ... | just (xs' , pe)
        with extract-prefix ks xs' in eqp
  ...     | nothing
            rewrite extract-elem-++ˡ-left k L xs dk eqe
                  | extract-prefix-++ˡ-left-nothing ks L xs' dks eqp = refl
  ...     | just (_ , _) with eqn
  ...       | ()

  ------------------------------------------------------------------------
  -- ## OBSTRUCTION NOTE — why there is no `term-sepˢ-ˡ` for firing blocks.
  --
  -- Goal would be:
  --   term-sepˢ-ˡ : block-disjointˡ es L
  --     → (Q : map vl (proj₁ (process-edgesˢ es (L ++ xs)))
  --            ≡ map vl L ++ map vl (proj₁ (process-edgesˢ es xs)))
  --     → castˢ (map-++ vl L xs) Q (proj₂ (process-edgesˢ es (L ++ xs)))
  --       ≈ˢ idˢ {map vl L} ⊗ˢ proj₂ (process-edgesˢ es xs)
  --
  -- This fails ALREADY at the hypothesis `Q`, for any `es` that fires once.
  --
  -- Take `es = e ∷ []`, `xs` such that `extract-prefix (H.ein e) xs
  -- ≡ just (rest , p)`, and `L` disjoint from `H.ein e`.  Then:
  --   * RIGHT frame (`Strict.Decoder`): `edge-stepˢ` on `xs ++ R` gives stack
  --     `H.eout e ++ (rest ++ R) = (H.eout e ++ rest) ++ R`.  The untouched
  --     `R` is at the END, the prepended output `H.eout e` lands BEFORE it, so
  --     `R` remains a suffix and `… ⊗ˢ idˢ {map vl R}` types.
  --   * LEFT frame (here): `extract-prefix-++ˡ-left` gives residual `L ++ rest`,
  --     so `edge-stepˢ` on `L ++ xs` produces stack
  --         H.eout e ++ (L ++ rest)
  --     The prepended output `H.eout e` lands BEFORE the untouched `L`, so `L`
  --     is NO LONGER a left prefix of the codomain stack.  Concretely
  --         proj₁ (process-edgesˢ (e ∷ []) (L ++ xs)) = H.eout e ++ (L ++ rest)
  --     whereas
  --         L ++ proj₁ (process-edgesˢ (e ∷ []) xs)   = L ++ (H.eout e ++ rest)
  --     and `H.eout e ++ (L ++ rest) ≢ L ++ (H.eout e ++ rest)` whenever
  --     `H.eout e` and `L` are non-empty and distinct — so the codomain
  --     coherence `Q` of the proposed `term-sepˢ-ˡ` cannot be supplied, and the
  --     `idˢ {map vl L} ⊗ˢ_` form is ill-typed.  No `≈ˢ`/cast manoeuvre repairs
  --     this: it is a list-equality mismatch, not a coherence gap.
  --
  -- The asymmetry is intrinsic to the decoder's "prepend the output" rule: the
  -- only region preserved across firings is a SUFFIX, captured by the RIGHT
  -- frame.  A LEFT-frame factorization of a firing block would require sliding
  -- `H.eout e` back past `L` via the symmetry `σ`, yielding a BRAIDED form, not
  -- the clean `idˢ {map vl L} ⊗ˢ_` the brief requested.
  --
  -- What survives on the left is exactly `permuteˢ-frameˡ` above: a pure
  -- permutation prepends nothing, so it preserves a left prefix, and its left
  -- frame holds verbatim as the mirror of `Perm′.permuteˢ-frame`.
  ------------------------------------------------------------------------

