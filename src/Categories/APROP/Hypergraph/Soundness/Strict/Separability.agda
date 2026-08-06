{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- LEFT-frame separability of the strict decoder — what IS true.
--
-- Intended as the MIRROR of the RIGHT-frame `term-sepˢ` (in
-- `Strict.Decode.Decoder`),
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
-- What IS true on the left is the STACK-SEARCH level: on `L ++ xs` with `L`
-- disjoint from the searched keys, the search skips `L` and returns residual
-- `L ++ rest`.  Those two lemmas are `SeparableStack.extract-prefix-++ʳ` and
-- `extract-prefix-++ʳ-nothing` — term-free and generic in `n`, so this module
-- re-exports them rather than re-proving them at `Fin H.nV`.  The pure-permutation
-- left frame (`idˢ ⊗ˢ_` for stdlib `++⁺ˡ`) lives in `FreeStrictSMC.Restrict` as
-- `permuteᵛ-frameˡ`.
--
-- The `stack-sepˢ-ˡ` / `layer-sepˢ-ˡ` / `term-sepˢ-ˡ` of the original brief are
-- intentionally ABSENT: they are not theorems (see above).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Strict.Separability
  (sig : APROPSignature)
  where

open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SeparableStack sig
  using (extract-prefix-++ʳ; extract-prefix-++ʳ-nothing) public

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
--   * RIGHT frame (`Strict.Decode.Decoder`): `edge-stepˢ` on `xs ++ R` gives
--     stack `H.eout e ++ (rest ++ R) = (H.eout e ++ rest) ++ R`.  The untouched
--     `R` is at the END, the prepended output `H.eout e` lands BEFORE it, so
--     `R` remains a suffix and `… ⊗ˢ idˢ {map vl R}` types.
--   * LEFT frame (here): `extract-prefix-++ʳ` gives residual `L ++ rest`,
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
-- What survives on the left is exactly `Restrict.permuteᵛ-frameˡ`: a pure
-- permutation prepends nothing, so it preserves a left prefix, and its left
-- frame holds verbatim as the mirror of `Perm′.permuteˢ-frame`.
------------------------------------------------------------------------
