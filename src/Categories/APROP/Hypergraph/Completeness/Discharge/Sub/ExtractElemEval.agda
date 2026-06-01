{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Eval-faithfulness of `extract-elem-found`'s located permutation, and the
-- discharge of `ResidualRecon.located-fixes-0`.
--
-- ## KEY FINDING (machine-verified counterexample).
--
-- `ResidualRecon.located-fixes-0` AS LITERALLY STATED (no `Unique` hypothesis)
-- is **FALSE** for duplicate input lists.  Concrete counterexample (verified by
-- normalising `eval-↭ r ⟨$⟩ʳ 0F` to `1F`):
--
--   xs = k ∷ k ∷ []      over Fin 1,    rest₀ = k ∷ []
--   perm-in = swap k k refl              -- sends cod-0 to dom-position 1
--   mem = ∈-resp-↭ (↭-sym perm-in) (here refl) = there (here refl)  -- position 1
--   q   = extract-elem-found k xs mem    -- but `x ≟ k = yes` MATCHES THE HEAD,
--                                        -- so q bubbles position 0, not 1.
--   r   = ↭-trans (↭-sym q) perm-in
--   ⇒ eval-↭ r ⟨$⟩ʳ 0F  =  1F  ≠  0F.
--
-- The flaw is that `extract-elem-found y (x ∷ xs) (there mem)` with `x ≟ y =
-- yes` returns the HEAD-extraction perm (position 0), regardless of where `mem`
-- points.  When `y` occurs twice, the bubbled position need not be the one
-- `perm-in` maps to cod-0, so the composite need not fix 0.  Hence the head
-- permutation `q` does NOT in general route `eval q ⟨$⟩ˡ 0F` to `index mem`.
--
-- ## What IS true and provable.
--
-- The intended statement holds once the **codomain** `k ∷ rest₀` is `Unique`
-- (no duplicate elements) — which is exactly the situation at the
-- `residual-recon` call site (decoder Fin-index vertex stacks ARE `Unique`).
-- Under `Unique (k ∷ rest₀)` the proof is *purely* `Rigid.lookup-sound` +
-- lookup-injectivity; it does NOT even need the `extract-elem-found`
-- structure or `Any-resp-↭` — uniqueness of the codomain forces the bubbled
-- position regardless of which equal element the extractor happened to pick.
--
-- We also prove the genuinely-true (uniqueness-FREE) value-faithfulness of the
-- head permutation `q : xs ↭ k ∷ rest`: the position `q` bubbles to the front
-- holds the value `k`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ExtractElemEval
  (sig : APROPSignature) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F)
open import Data.Nat.Base using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_; length; lookup)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)

import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

import Data.Fin.Permutation as P
open P using (_⟨$⟩ʳ_; _⟨$⟩ˡ_)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

-- The extractor we are reconciling against.
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-elem-found)

-- PermuteCoherence machinery.
open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness using (eval-↭-sym)
open import Categories.PermuteCoherence.Rigid using (lookup-sound; eval-rigid)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  Lookup-injectivity on `Unique` lists.  (Re-derived; the copy in
--     `Rigid.agda` is `private`.)

private
  All-lookup : ∀ {p} {A : Set} {Q : A → Set p} {xs : List A}
             → All Q xs → (i : Fin (length xs)) → Q (lookup xs i)
  All-lookup (q ∷ _)  zero    = q
  All-lookup (_ ∷ qs) (suc i) = All-lookup qs i

  lookup-inj
    : ∀ {A : Set} {xs : List A}
    → Unique xs → (i j : Fin (length xs))
    → lookup xs i ≡ lookup xs j
    → i ≡ j
  lookup-inj (_  ∷ _ ) zero    zero    _  = refl
  lookup-inj (x≢ ∷ _ ) zero    (suc j) eq = ⊥-elim (All-lookup x≢ j eq)
  lookup-inj (x≢ ∷ _ ) (suc i) zero    eq = ⊥-elim (All-lookup x≢ i (sym eq))
  lookup-inj (_  ∷ uq) (suc i) (suc j) eq = cong suc (lookup-inj uq i j eq)

--------------------------------------------------------------------------------
-- 1.  VALUE-faithfulness of the head permutation (uniqueness-FREE).
--
-- For ANY `q : xs ↭ k ∷ rest`, the position `q` bubbles to the front,
-- `eval-↭ q ⟨$⟩ˡ 0F`, holds the value `k`.  This is the genuinely-true core of
-- "`extract-elem-found` extracts a `k`": it is purely `lookup-sound` (the
-- located permutation does NOT matter beyond having codomain head `k`).
--
-- This is the eval-faithfulness lemma about `extract-elem-found`'s output that
-- IS true without uniqueness; we state it for the `extract-elem-found` perm
-- directly below (`extract-elem-found-bubbles-k`).

bubbles-value
  : ∀ {m} {k : Fin m} {xs rest : List (Fin m)} (q : xs Perm.↭ k ∷ rest)
  → lookup xs (eval-↭ q ⟨$⟩ˡ 0F) ≡ k
bubbles-value {k = k} {xs} {rest} q =
  trans (sym (lookup-sound q (eval-↭ q ⟨$⟩ˡ 0F)))
        (cong (lookup (k ∷ rest)) (P.inverseʳ (eval-↭ q)))

-- Specialised to `extract-elem-found`'s output perm.
extract-elem-found-bubbles-k
  : ∀ {m} (k : Fin m) (xs : List (Fin m)) (mem : k ∈ xs)
  → let q = proj₁ (proj₂ (extract-elem-found k xs mem)) in
    lookup xs (eval-↭ q ⟨$⟩ˡ 0F) ≡ k
extract-elem-found-bubbles-k k xs mem =
  bubbles-value (proj₁ (proj₂ (extract-elem-found k xs mem)))

--------------------------------------------------------------------------------
-- 2.  POSITION-faithfulness under a `Unique` codomain.
--
-- THE lemma that closes `located-fixes-0`.  For ANY `q : xs ↭ k ∷ rest` and any
-- `perm-in : xs ↭ k ∷ rest₀`, IF `k ∷ rest₀` is `Unique`, the composite
-- `r = ↭-trans (↭-sym q) perm-in : (k ∷ rest) ↭ (k ∷ rest₀)` fixes position 0.
--
-- Proof: `lookup-sound r 0F` says `eval r ⟨$⟩ʳ 0F` is a position of `k ∷ rest₀`
-- holding `lookup (k ∷ rest) 0F = k = lookup (k ∷ rest₀) 0F`; injectivity of
-- lookup on the `Unique` codomain forces it to be `0F`.  Note this is robust to
-- duplicate INPUTS / arbitrary `q`; only the codomain `k ∷ rest₀` need be
-- `Unique` — which is precisely why the no-`Unique` form is unsound.

located-fixes-0-unique
  : ∀ {m} (k : Fin m) {rest rest₀ : List (Fin m)}
      (q : (k ∷ rest) Perm.↭ (k ∷ rest₀))
  → Unique (k ∷ rest₀)
  → eval-↭ q ⟨$⟩ʳ 0F ≡ 0F
located-fixes-0-unique {m} k {rest} {rest₀} q uniq =
  lookup-inj uniq (eval-↭ q ⟨$⟩ʳ 0F) 0F (lookup-sound q 0F)

-- The form matching `ResidualRecon.located-fixes-0`'s GOAL exactly: the
-- composite `↭-trans (↭-sym q) perm-in` for the `extract-elem-found` head perm.
located-fixes-0
  : ∀ {m} (k : Fin m) (xs : List (Fin m)) {rest₀ : List (Fin m)}
      (perm-in : xs Perm.↭ k ∷ rest₀)
  → Unique (k ∷ rest₀)
  → let mem = PermProp.∈-resp-↭ (Perm.↭-sym perm-in) (here refl)
        q   = proj₁ (proj₂ (extract-elem-found k xs mem))
    in eval-↭ (Perm.↭-trans (Perm.↭-sym q) perm-in) ⟨$⟩ʳ 0F ≡ 0F
located-fixes-0 k xs {rest₀} perm-in uniq =
  located-fixes-0-unique k
    (Perm.↭-trans (Perm.↭-sym q) perm-in) uniq
  where
    mem = PermProp.∈-resp-↭ (Perm.↭-sym perm-in) (here refl)
    q   = proj₁ (proj₂ (extract-elem-found k xs mem))

--------------------------------------------------------------------------------
-- 3.  `BlockNFVoutCoh.{coh-in,coh-out}` — provability VERDICT (a usable form).
--
-- `coh-in`/`coh-out` are NOT instances of the `extract-elem-found`
-- eval-faithfulness above.  They compare TWO list-permutations with the SAME
-- domain and the SAME codomain (the located frames `loc₁` vs `trans loc₂
-- app-swap`, both `sp ↭ (ein e ++ ein e') ++ Rlist`; dually `trans vl₁ rstk`
-- vs `trans (app-swap) vl₂`, both `(eout e ++ eout e') ++ Rlist ↭ eout e ++
-- r₁'`), then lift the resulting `≅↭` through `map⁺ vlab`.
--
-- Two perms with a common `Unique` codomain evaluate to the SAME bijection by
-- `Rigid.eval-rigid` — NO `extract-elem-found` / `Any-resp-↭` is involved.
-- So `coh-in`/`coh-out` reduce to:
--
--    (i)  `eval-rigid uniq p q`            -- Fin-index `≅↭`, codomain `Unique`
--    (ii) `StackEquivariance.map⁺-lift-≅↭` -- lift through `map⁺ vlab`.
--
-- (ii) already exists in `StackEquivariance.agda`.  (i) is supplied here, in
-- the exact `≅↭` shape both `coh` hypotheses want.  The ONE extra ingredient
-- they need beyond what I prove is the `Unique` witness for the Fin-index
-- codomain `(ein e ++ ein e') ++ Rlist` (resp. `eout e ++ r₁'`); that is a
-- decoder-stack uniqueness fact threaded from `Comb.sim-loc`'s construction,
-- NOT a property of a single `extract-elem-found`.

-- The Fin-index `≅↭` underlying BOTH `coh-in` and `coh-out`: any two perms with
-- the same `Unique` codomain are `≅↭`.
coh-fin-rigid
  : ∀ {m} {xs ys : List (Fin m)} (p q : xs Perm.↭ ys)
  → Unique ys
  → p ≅↭ q
coh-fin-rigid p q uniq = eval-rigid uniq p q
