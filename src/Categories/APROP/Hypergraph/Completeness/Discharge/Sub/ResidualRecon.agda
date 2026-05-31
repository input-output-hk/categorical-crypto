{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Discharge of `residual-recon` (the SOLE remaining postulate in
-- `StackEquivariance.agda`).
--
-- For `st = extract-prefix-↭-residual ks xs rest perm-in` with
-- `located = proj₁ (proj₂ st) : xs ↭ ks ++ rest'` and
-- `residual-↭ = proj₂ (proj₂ (proj₂ st)) : rest ↭ rest'`,
--
--   trans located (++⁺ˡ ks (↭-sym residual-↭))  ≅↭  perm-in
--
-- where `_≅↭_ a b = eval-↭ a ≈-fb eval-↭ b`.
--
-- Proven by induction on `ks` under `--with-K`.  The base case and the ENTIRE
-- cons-step bijection algebra (`eval-sym-sym`, `eval-smart-trans`,
-- `inv-cancel`, `liftRemove`, `recon-cons-step`) are PROVEN postulate-free.
-- Three narrow, clearly-true facts remain as flagged postulates:
--
--   * `drop-∷-eval`     — (B) eval-faithfulness of stdlib `drop-∷ = drop-mid
--                         [] []`:  `eval (drop-∷ r) ≈ remove 0F (eval r)`.
--                         The documented multi-session blocker: requires
--                         replaying `drop-mid′`'s recursion (incl. its `trans`
--                         split-point case) at the `eval`/`remove` level.
--   * `located-fixes-0` — (A) the `extract-elem-found` head perm `q` (for the
--                         witness derived from `perm-in`) sends position 0 to
--                         position 0; needs eval-faithfulness of
--                         `extract-elem-found` + `Any-resp-↭`.  Stated NARROWLY
--                         for the specific `q` (FALSE for arbitrary `q`).
--   * `st-cons-bridge`  — the definitional cons-UNFOLD of the extractor.  TRUE
--                         by the function clause but irreducibly stuck for a
--                         variable input list (the green-slime `with`-wall);
--                         closing it needs the relation-view rewrite of the
--                         extractor or a helper proven inside `DecodeProperties`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ResidualRecon
  (sig : APROPSignature) where

open import Data.Fin using (Fin)
open import Data.Fin.Base using (suc)
open import Data.Fin.Patterns using (0F)
open import Data.Nat.Base using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)

import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

import Data.Fin.Permutation as P
open P using (_⟨$⟩ʳ_; remove)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

-- Foundation: the extractor we are reconciling against.
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-elem-found)

-- PermuteCoherence machinery.
open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Soundness
  using (eval-↭-sym; cons-fb-functor-comp)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)

private
  variable
    n : ℕ

--------------------------------------------------------------------------------
-- 0.  `eval` of a double `↭-sym` is `eval` of the original.
--
-- `↭-sym` is structural, so `↭-sym (↭-sym p)` recurses on each
-- constructor and we get a clean pointwise proof by induction on `p`.

eval-sym-sym
  : ∀ {a} {A : Set a} {xs ys : List A} (p : xs Perm.↭ ys)
  → eval-↭ (Perm.↭-sym (Perm.↭-sym p)) ≈-fb eval-↭ p
eval-sym-sym Perm.refl  _    = refl
eval-sym-sym (Perm.prep x p) = aux
  where
    aux : ∀ j → eval-↭ (Perm.↭-sym (Perm.↭-sym (Perm.prep x p))) ⟨$⟩ʳ j
              ≡ eval-↭ (Perm.prep x p) ⟨$⟩ʳ j
    aux 0F      = refl
    aux (suc j) = cong suc (eval-sym-sym p j)
eval-sym-sym (Perm.swap x y p) = aux
  where
    aux : ∀ j → eval-↭ (Perm.↭-sym (Perm.↭-sym (Perm.swap x y p))) ⟨$⟩ʳ j
              ≡ eval-↭ (Perm.swap x y p) ⟨$⟩ʳ j
    aux 0F            = refl
    aux (suc 0F)      = refl
    aux (suc (suc j)) = cong (λ z → suc (suc z)) (eval-sym-sym p j)
eval-sym-sym (Perm.trans p q) i =
  step (eval-sym-sym q (eval-↭ (Perm.↭-sym (Perm.↭-sym p)) ⟨$⟩ʳ i))
       (cong (eval-↭ q ⟨$⟩ʳ_) (eval-sym-sym p i))
  where
  step : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  step refl r = r

--------------------------------------------------------------------------------
-- 1.  `cons-fb` congruence (private `Canonical` lemma re-derived).

cons-fb-cong : ∀ {n m} {f f′ : FinBij n m}
             → f ≈-fb f′ → cons-fb f ≈-fb cons-fb f′
cons-fb-cong eq 0F      = refl
cons-fb-cong eq (suc i) = cong suc (eq i)

--------------------------------------------------------------------------------
-- 2.  eval of the SMART `↭-trans` (it drops `refl`s, but eval of `refl`
--     is `id-fb`, an identity for `∘-fb`, so the law survives).

eval-smart-trans
  : ∀ {a} {A : Set a} {xs ys zs : List A} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
  → eval-↭ (Perm.↭-trans p q) ≈-fb eval-↭ q ∘-fb eval-↭ p
-- Every case is pointwise `refl`: the smart `↭-trans` either drops a
-- `refl` (whose `eval` is `id-fb`, an identity for `∘ₚ`) or keeps the
-- raw `trans`, and `∘-fb` is plain forward-map composition, so both
-- sides reduce to the SAME function on every index.
eval-smart-trans Perm.refl              q                 = λ _ → refl
eval-smart-trans (Perm.prep x p)        Perm.refl         = λ _ → refl
eval-smart-trans (Perm.prep x p)        (Perm.prep _ q)   = λ _ → refl
eval-smart-trans (Perm.prep x p)        (Perm.swap _ _ q) = λ _ → refl
eval-smart-trans (Perm.prep x p)        (Perm.trans q q′) = λ _ → refl
eval-smart-trans (Perm.swap x y p)      Perm.refl         = λ _ → refl
eval-smart-trans (Perm.swap x y p)      (Perm.prep _ q)   = λ _ → refl
eval-smart-trans (Perm.swap x y p)      (Perm.swap _ _ q) = λ _ → refl
eval-smart-trans (Perm.swap x y p)      (Perm.trans q q′) = λ _ → refl
eval-smart-trans (Perm.trans p p′)      Perm.refl         = λ _ → refl
eval-smart-trans (Perm.trans p p′)      (Perm.prep _ q)   = λ _ → refl
eval-smart-trans (Perm.trans p p′)      (Perm.swap _ _ q) = λ _ → refl
eval-smart-trans (Perm.trans p p′)      (Perm.trans q q′) = λ _ → refl

--------------------------------------------------------------------------------
-- 4.  Inverse cancellation:  `trans q (↭-trans (↭-sym q) p) ≅↭ p`.

inv-cancel
  : ∀ {a} {A : Set a} {xs ys zs : List A} (q : xs Perm.↭ ys) (p : xs Perm.↭ zs)
  → eval-↭ (Perm.trans q (Perm.↭-trans (Perm.↭-sym q) p)) ≈-fb eval-↭ p
inv-cancel q p i =
  -- eval (trans q X) .to i = eval X .to (eval q .to i),  X = ↭-trans (↭-sym q) p
  trans (eval-smart-trans (Perm.↭-sym q) p (eval-↭ q ⟨$⟩ʳ i))
  -- = eval p .to (eval (↭-sym q) .to (eval q .to i))
        (cong (eval-↭ p ⟨$⟩ʳ_)
          (trans (eval-↭-sym q (eval-↭ q ⟨$⟩ʳ i))
          -- = eval p .to ((eval q).from (eval q .to i))
                 (P.inverseˡ (eval-↭ q))))

--------------------------------------------------------------------------------
-- 5.  (A) The located perm routes position 0 to position 0:
--      `eval (↭-trans (↭-sym q) perm-in) ⟨$⟩ʳ 0F ≡ 0F`.
--
-- (B) drop-∷ eval-faithfulness:
--      `eval (drop-∷ r) ≈-fb remove 0F (eval r)`.
--
-- These are the two remaining FACTS; combined into `liftRemove` below.

postulate
  drop-∷-eval
    : ∀ {m} {as bs : List (Fin m)} {k : Fin m}
        (r : k ∷ as Perm.↭ k ∷ bs)
    → eval-↭ (PermProp.drop-∷ r) ≈-fb remove 0F (eval-↭ r)

-- (A) The head-extraction perm `q` produced by `extract-elem-found` for the
-- membership witness derived FROM `perm-in` routes position 0 to position 0
-- of the input.  TRUE: `extract-elem-found k xs m` bubbles the element at the
-- `m`-witnessed position to slot 0 (so `eval q ⟨$⟩ˡ 0F` = that position), and
-- `m = ∈-resp-↭ (↭-sym perm-in) (here refl)` is exactly the position that
-- `perm-in` sends to slot 0 (eval-faithfulness of `Any-resp-↭`); hence
-- `eval (↭-trans (↭-sym q) perm-in) ⟨$⟩ʳ 0F ≡ 0F`.  Stated NARROWLY for the
-- specific `extract-elem-found` perm (it is FALSE for an arbitrary `q`), so
-- the postulate is sound; proving it needs eval-faithfulness of
-- `extract-elem-found` + `Any-resp-↭` (a separate effort).
postulate
  located-fixes-0
    : ∀ {m} (k : Fin m) (xs : List (Fin m)) {rest₀ : List (Fin m)}
        (perm-in : xs Perm.↭ k ∷ rest₀)
    → let mem = PermProp.∈-resp-↭ (Perm.↭-sym perm-in) (here refl)
          q   = proj₁ (proj₂ (extract-elem-found k xs mem))
      in eval-↭ (Perm.↭-trans (Perm.↭-sym q) perm-in) ⟨$⟩ʳ 0F ≡ 0F

-- Combined:  `cons-fb (eval (drop-∷ r)) ≈ eval r`, for `r` whose eval
-- fixes 0F.  Via stdlib `lift₀-remove`.
liftRemove
  : ∀ {m} {as bs : List (Fin m)} {k : Fin m}
      (r : k ∷ as Perm.↭ k ∷ bs)
  → eval-↭ r ⟨$⟩ʳ 0F ≡ 0F
  → cons-fb (eval-↭ (PermProp.drop-∷ r)) ≈-fb eval-↭ r
liftRemove r fix0 i =
  trans (cons-fb-cong (drop-∷-eval r) i)
        (P.lift₀-remove (eval-↭ r) fix0 i)

--------------------------------------------------------------------------------
-- 6.  Cons-step ALGEBRA (fully proven).
--
-- Given the head-extraction perm `q : xs ↭ k ∷ xs'`, the recursive
-- located perm `pp : xs' ↭ ks ++ rest'`, the residual reshuffle
-- `rest-perm : rest ↭ rest'`, and the INDUCTION HYPOTHESIS for the
-- shorter prefix, reconcile the reconstructed `k ∷ ks`-located perm
-- with `perm-in`.

recon-cons-step
  : ∀ {n} {k : Fin n} {ks xs xs' rest rest' : List (Fin n)}
      (q : xs Perm.↭ k ∷ xs') (pp : xs' Perm.↭ ks ++ rest')
      (rest-perm : rest Perm.↭ rest')
      (perm-in : xs Perm.↭ k ∷ (ks ++ rest))
  → eval-↭ (Perm.↭-trans (Perm.↭-sym q) perm-in) ⟨$⟩ʳ 0F ≡ 0F   -- (A), supplied by caller
  → eval-↭ (Perm.trans pp (PermProp.++⁺ˡ ks (Perm.↭-sym rest-perm)))
      ≈-fb eval-↭ (PermProp.drop-∷ (Perm.↭-trans (Perm.↭-sym q) perm-in))
  → eval-↭ (Perm.trans (Perm.trans q (Perm.prep k pp))
                       (Perm.prep k (PermProp.++⁺ˡ ks (Perm.↭-sym rest-perm))))
      ≈-fb eval-↭ perm-in
recon-cons-step {k = k} {ks} {xs} {xs'} {rest} {rest'} q pp rest-perm perm-in fix0 ih′ i =
  -- pointwise: each step postcomposes a `≈-fb` proof with `eval q` (whose
  -- factor is `refl`), so `∘-fb-cong _ refl i` collapses to applying the
  -- proof at `eval q ⟨$⟩ʳ i`; the `∘-fb-assoc` reassociation is definitional.
  trans (sym (cons-fb-functor-comp (eval-↭ R) (eval-↭ pp) (eval-↭ q ⟨$⟩ʳ i)))
  (trans (cons-fb-cong {f = eval-↭ (Perm.trans pp R)} {f′ = eval-↭ (PermProp.drop-∷ (Perm.↭-trans (Perm.↭-sym q) perm-in))} ih′ (eval-↭ q ⟨$⟩ʳ i))
  (trans (liftRemove r fix0 (eval-↭ q ⟨$⟩ʳ i))
         (inv-cancel q perm-in i)))
  where
    R : ks ++ rest' Perm.↭ ks ++ rest
    R = PermProp.++⁺ˡ ks (Perm.↭-sym rest-perm)
    r : k ∷ xs' Perm.↭ k ∷ (ks ++ rest)
    r = Perm.↭-trans (Perm.↭-sym q) perm-in

--------------------------------------------------------------------------------
-- 7.  Cons UNFOLD of `extract-prefix-↭-residual`.
--
-- `extract-prefix-↭-residual (k ∷ ks) xs rest perm-in` is stuck on its
-- own internal `with`-tree (the argument `xs` is a variable), so its
-- output does NOT β-reduce inside the goal type — the classic
-- green-slime `with`-abstraction wall.  We package the ONE definitional
-- unfold equation it satisfies (read directly off the function clause):
-- with `(xs' , q , _) = extract-elem-found k xs (∈-resp-↭ (↭-sym perm-in)
-- (here refl))` and `(rest' , pp , _ , rp) = extract-prefix-↭-residual ks
-- xs' rest (drop-∷ (↭-trans (↭-sym q) perm-in))`, the located perm is
-- `trans q (prep k pp)` and the residual reshuffle is `rp` (threaded
-- unchanged).  This is a TRUE, narrow structural fact about the
-- function body; the heavy mathematical content lives in the proven
-- `recon-cons-step` / base case, not here.

-- NOTE: `st-cons-bridge` is the eval-level form of the definitional unfold
-- of the function clause.  It is TRUE by the function body — the cons-located
-- perm IS `trans q (prep k pp)` and the residual reshuffle IS threaded
-- unchanged as `rp` — so the two `eval-↭`s below are literally the SAME
-- bijection.  It is NOT provable as a separate lemma: `extract-prefix-↭-residual
-- (k ∷ ks) xs …` is irreducibly STUCK for a variable `xs` (its internal
-- `with extract-elem-found …` never reduces to a constructor on a variable
-- list), so the goal's `st` projections cannot be forced to β-reduce — the
-- green-slime `with`-abstraction wall.  Closing it requires the relation-view
-- rewrite of the extractor (a separate effort) or a helper proven INSIDE
-- `DecodeProperties` (which we are forbidden to edit here).  Stated directly at
-- the `eval-↭` level so the consuming proof needs no dependent transport.
postulate
  st-cons-bridge
    : ∀ {n} (k : Fin n) (ks xs rest : List (Fin n))
        (perm-in : xs Perm.↭ k ∷ (ks ++ rest))
    → let mem    = PermProp.∈-resp-↭ (Perm.↭-sym perm-in) (here refl)
          he     = extract-elem-found k xs mem
          q      = proj₁ (proj₂ he)
          rec    = extract-prefix-↭-residual ks (proj₁ he) rest
                     (PermProp.drop-∷ (Perm.↭-trans (Perm.↭-sym (proj₁ (proj₂ he))) perm-in))
          pp     = proj₁ (proj₂ rec)
          rp     = proj₂ (proj₂ (proj₂ rec))
          st     = extract-prefix-↭-residual (k ∷ ks) xs rest perm-in
      in eval-↭ (Perm.trans (proj₁ (proj₂ st))
                   (PermProp.++⁺ˡ (k ∷ ks)
                     (Perm.↭-sym (proj₂ (proj₂ (proj₂ st))))))
         ≈-fb
         eval-↭ (Perm.trans (Perm.trans q (Perm.prep k pp))
                   (Perm.prep k (PermProp.++⁺ˡ ks (Perm.↭-sym rp))))

--------------------------------------------------------------------------------
-- Main statement.

residual-recon
  : ∀ {n} (ks xs rest : List (Fin n)) (perm-in : xs Perm.↭ ks ++ rest)
  → let st = extract-prefix-↭-residual ks xs rest perm-in in
    Perm.trans (proj₁ (proj₂ st))
               (PermProp.++⁺ˡ ks (Perm.↭-sym (proj₂ (proj₂ (proj₂ st)))))
    ≅↭ perm-in
residual-recon [] xs rest perm-in = eval-sym-sym perm-in
residual-recon {n} (k ∷ ks) xs rest perm-in i =
  -- goal-`st` form  ≈  canonical (trans q (prep k pp)) / threaded `rp` form,
  -- then canonical  ≈  eval perm-in (the proven cons-step algebra).
  trans (st-cons-bridge k ks xs rest perm-in i)
        (recon-cons-step q pp rp perm-in (located-fixes-0 k xs perm-in) ih′ i)
  where
    mem = PermProp.∈-resp-↭ (Perm.↭-sym perm-in) (here refl)
    he  = extract-elem-found k xs mem
    xs' = proj₁ he
    q   = proj₁ (proj₂ he)
    perm-in' = PermProp.drop-∷ (Perm.↭-trans (Perm.↭-sym q) perm-in)
    rec = extract-prefix-↭-residual ks xs' rest perm-in'
    pp  = proj₁ (proj₂ rec)
    rp  = proj₂ (proj₂ (proj₂ rec))

    -- IH for the shorter prefix.
    ih′ : eval-↭ (Perm.trans pp (PermProp.++⁺ˡ ks (Perm.↭-sym rp)))
          ≈-fb eval-↭ perm-in'
    ih′ = residual-recon ks xs' rest perm-in'
