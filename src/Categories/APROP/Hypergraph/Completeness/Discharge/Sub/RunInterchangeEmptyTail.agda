{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- The EMPTY-TAIL two-edge interchange core `run-interchange₀`.
--
-- This module constructs the `SwapStep.FrontSwap.RunInterchange` value for
-- the EMPTY tail `qs = []` — the genuine two-edge symmetric-monoidal
-- interchange at a single swap.  It is the substantive base case that
-- `Sub/RunInterchangeTail.run-interchange-tail` lifts to an arbitrary
-- suffix `qs`.
--
-- ## Statement
--
--   run-interchange₀ ps inc : RunInterchange ps [] inc
--
-- where `RunInterchange ps [] inc` packages (with `sp = pe-stack ps dom`,
-- `fs₁ = pe-stack (e ∷ e' ∷ []) sp`, `fs₂ = pe-stack (e' ∷ e ∷ []) sp`):
--
--   reshuffle : fs₁ ↭ fs₂
--   run-eq    : pe-term (e' ∷ e ∷ []) sp
--                 ≈Term permute-via-vlab vlab reshuffle ∘ pe-term (e ∷ e' ∷ []) sp
--
-- ## Structure of the proof
--
-- We case-split the firing decisions of the two front edges over the
-- `EdgeStepRelation` view (`EdgeStepR`, `edge-step-graph`), exactly
-- mirroring `SwapValidity.two-edge-swap-stack-↭`'s four-way firing
-- split — but at the TERM level (not just the stack level).  Matching the
-- `EdgeStepR` constructors refines the (otherwise stuck) `edge-step`
-- redexes embedded in `pe-stack`/`pe-term` to `id` / `fire-term` WITHOUT
-- abstracting them in a dependent position, so no green-slime /
-- ill-typed-with-abstraction arises.  The trailing `id` of
-- `process-edges []` is stripped by `idˡ`.
--
-- The `RunInterchange` record's `reshuffle` and `run-eq` are built TOGETHER
-- per case (the reshuffle is whatever that case naturally yields), so NO
-- global Kelly-reconciliation of two reshuffle witnesses is needed — and in
-- particular no `Unique (pe-stack …)` hypothesis (which we do not have).
--
--   1. BOTH-SKIP    — both runs are `(id ∘ id) ∘ id`; `reshuffle = refl`;
--                     `run-eq` collapses via `idˡ` (`permute refl ≡ id`).
--   2. e FIRES, e' SKIPS — single layer `fire-term e` in both orders;
--                     `reshuffle = refl`; `run-eq` collapses via `idˡ`/`idʳ`.
--   3. e SKIPS, e' FIRES — symmetric to (2), single layer `fire-term e'`.
--   4. BOTH-FIRE    — THE genuine content: the two framed boxes
--                     `(Agen-edge ⊗ id)` on DISJOINT blocks commute via σ.
--                     Isolated as the SINGLE residual
--                     `fire-mid-interchange` (see below).
--
-- The impossible mixed firing cases (one order fires both edges, the other
-- only one) are ruled out by FIRING-STABILITY (`Linear` + `Incomp`),
-- exactly as in `SwapValidity.two-edge-swap-stack-↭`.  Because the
-- relevant stability lemmas (`e'-fires-stable` / `e'-skips-stable`) live in
-- a `private` block of `SwapValidity.PerHG`, they are re-derived here
-- verbatim (copies of the proven, postulate-free originals); they depend on
-- the count/disjointness combinatorics, also copied from `SwapValidity`'s
-- top-level `private` block.
--
-- ## The single residual — `fire-mid-interchange` (M)
--
-- BOTH-FIRE reduces, after stripping the trailing `id`s and factoring each
-- fire layer via `EdgeStepRelation.fire-term = fire-mid ∘ permute`, to the
-- commutation of the two framed boxes `fire-mid e _` and `fire-mid e' _`
-- on DISJOINT wire blocks.  The hypergraph-free, K-free kernel
--
--   box-interchange f g : g ⊗₁ f ≈Term σ ∘ ((f ⊗₁ g) ∘ σ)
--
-- is ALREADY PROVEN in `SwapStep.FrontSwap` (the literal σ-naturality
-- application).  Transporting it through the two `fire-mid` boxes'
-- `box-of`/`unflatten-++-≅`/`subst₂` bracketing and the four locating
-- permutes is the genuine Mac-Lane chase that EVEN THE `--with-K`
-- development leaves open (`Sub/SwapAtomAligned.swap-mac-lane-residual`,
-- `Sub/AllFireEdgeSwap.agda`).  We DO NOT close it; we isolate it as a
-- SINGLE residual, stated over the UNPACKED fire data (no `Hypergraph`
-- record matching, no `with extract-prefix`, no `cod`, no final permute),
-- bundling the reshuffle existentially — exactly the posture of
-- `Sub/SwapAtomAligned.swap-mac-lane-residual` and the sibling
-- `Sub/StackEquivariance.fire-mid-equivariant`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeEmptyTail
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear; count; count-++; consumedList)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeStepRelation sig
  using (EdgeStepR; skipR; fireR; fire-term; fire-mid; edge-step-graph; edge-step-sound)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchange sig as FMI
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map; concat)
open import Data.List.Base using (tabulate)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

--------------------------------------------------------------------------------
-- ≈Term plumbing.

private
  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

  nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  nothing≢just ()

------------------------------------------------------------------------
-- Generic `count` / `extract-prefix` combinatorics (H-agnostic), copied
-- VERBATIM from `SwapValidity.agda`'s top-level `private` block (they are
-- inaccessible there).  All over `List (Fin n)`, all `--without-K`-clean.
------------------------------------------------------------------------

private
  variable
    n : ℕ

  count-cons-yes : (v : Fin n) (xs : List (Fin n))
                 → count v (v ∷ xs) ≡ suc (count v xs)
  count-cons-yes v xs with v ≟ v
  ... | yes _ = refl
  ... | no  q = ⊥-elim (q refl)

  count-cons-no : (v x : Fin n) (xs : List (Fin n)) → ¬ (v ≡ x)
                → count v (x ∷ xs) ≡ count v xs
  count-cons-no v x xs v≢x with v ≟ x
  ... | yes p = ⊥-elim (v≢x p)
  ... | no  _ = refl

  ∈→count-pos : ∀ {v : Fin n} {xs} → v ∈ xs → 0 <ⁿ count v xs
  ∈→count-pos {v = v} {x ∷ xs} (here refl)  rewrite count-cons-yes v xs = s≤sⁿ z≤nⁿ
  ∈→count-pos {v = v} {x ∷ xs} (there v∈xs) with v ≟ x
  ... | yes _ = s≤sⁿ z≤nⁿ
  ... | no  _ = ∈→count-pos v∈xs

  count-pos→∈ : ∀ {v : Fin n} {xs} → 0 <ⁿ count v xs → v ∈ xs
  count-pos→∈ {v = v} {[]}     ()
  count-pos→∈ {v = v} {x ∷ xs} c with v ≟ x
  ... | yes refl = here refl
  ... | no  _    = there (count-pos→∈ c)

  ↭⇒count : {xs ys : List (Fin n)} → xs Perm.↭ ys → ∀ v → count v xs ≡ count v ys
  ↭⇒count Perm.refl                       v = refl
  ↭⇒count (Perm.prep x p)                 v with v ≟ x
  ... | yes _ = cong suc (↭⇒count p v)
  ... | no  _ = ↭⇒count p v
  ↭⇒count (Perm.swap {xs = xs} {ys = ys} x y p) v = swap-case (v ≟ x) (v ≟ y)
    where
      swap-case : _ → _ → count v (x ∷ y ∷ xs) ≡ count v (y ∷ x ∷ ys)
      swap-case (yes refl) (yes refl) =
        trans (count-cons-yes v (v ∷ xs))
        (trans (cong suc (count-cons-yes v xs))
        (trans (cong suc (cong suc (↭⇒count p v)))
        (trans (cong suc (sym (count-cons-yes v ys)))
               (sym (count-cons-yes v (v ∷ ys))))))
      swap-case (yes refl) (no  q) =
        trans (count-cons-yes v (y ∷ xs))
        (trans (cong suc (count-cons-no v y xs q))
        (trans (cong suc (↭⇒count p v))
        (trans (sym (count-cons-yes v ys))
               (sym (count-cons-no v y (v ∷ ys) q)))))
      swap-case (no  q) (yes refl) =
        trans (count-cons-no v x (v ∷ xs) q)
        (trans (count-cons-yes v xs)
        (trans (cong suc (↭⇒count p v))
        (trans (cong suc (sym (count-cons-no v x ys q)))
               (sym (count-cons-yes v (x ∷ ys))))))
      swap-case (no  q₁) (no  q₂) =
        trans (count-cons-no v x (y ∷ xs) q₁)
        (trans (count-cons-no v y xs q₂)
        (trans (↭⇒count p v)
        (trans (sym (count-cons-no v x ys q₁))
               (sym (count-cons-no v y (x ∷ ys) q₂)))))
  ↭⇒count (Perm.trans p₁ p₂)              v = trans (↭⇒count p₁ v) (↭⇒count p₂ v)

  extract-prefix-just→count-≤
    : (ks xs rest : List (Fin n)) (p : xs Perm.↭ ks ++ rest)
    → ∀ v → count v ks ≤ⁿ count v xs
  extract-prefix-just→count-≤ ks xs rest p v =
    Nat.≤-trans (Nat.m≤m+n (count v ks) (count v rest))
                (Nat.≤-reflexive (trans (sym (count-++ v ks rest))
                                        (sym (↭⇒count p v))))

  count-pos→extract-elem
    : (k : Fin n) (xs : List (Fin n)) → 0 <ⁿ count k xs
    → Σ[ rest ∈ List (Fin n) ] Σ[ p ∈ xs Perm.↭ k ∷ rest ]
        extract-elem k xs ≡ just (rest , p)
  count-pos→extract-elem k []       ()
  count-pos→extract-elem k (x ∷ xs) c with x ≟ k
  ... | yes refl = xs , _ , refl
  ... | no  x≢k  with count-pos→extract-elem k xs
                      (subst (0 <ⁿ_) (count-cons-no k x xs (λ e → x≢k (sym e))) c)
  ...   | rest , p , eq rewrite eq = x ∷ rest , _ , refl

  count-≤→extract-prefix
    : (ks xs : List (Fin n)) → (∀ v → count v ks ≤ⁿ count v xs)
    → Σ[ rest ∈ List (Fin n) ] Σ[ p ∈ xs Perm.↭ ks ++ rest ]
        extract-prefix ks xs ≡ just (rest , p)
  count-≤→extract-prefix []       xs h = xs , Perm.refl , refl
  count-≤→extract-prefix (k ∷ ks) xs h
    with count-pos→extract-elem k xs
           (Nat.<-≤-trans (s≤sⁿ z≤nⁿ)
             (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks))) (h k)))
  ... | xs' , p , eq-elem
      with count-≤→extract-prefix ks xs' h-rest
    where
      h-rest : ∀ v → count v ks ≤ⁿ count v xs'
      h-rest v with v ≟ k
      ... | yes refl =
            s≤s⁻¹
              (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks)))
              (Nat.≤-trans (h k)
                           (Nat.≤-reflexive
                             (trans (↭⇒count p k) (count-cons-yes k xs')))))
      ... | no  v≢k =
            Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-no v k ks v≢k)))
            (Nat.≤-trans (h v)
                         (Nat.≤-reflexive
                           (trans (↭⇒count p v) (count-cons-no v k xs' v≢k))))
  ...   | rest , q , eq-rest rewrite eq-elem | eq-rest =
          rest , _ , refl

  count-concat-tabulate-≤
    : ∀ {nE} (f : Fin nE → List (Fin n)) (e : Fin nE) (v : Fin n)
    → count v (f e) ≤ⁿ count v (concat (tabulate f))
  count-concat-tabulate-≤ f zero    v =
    Nat.≤-trans (Nat.m≤m+n _ _)
                (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
  count-concat-tabulate-≤ f (suc e) v =
    Nat.≤-trans (count-concat-tabulate-≤ (λ i → f (suc i)) e v)
                (Nat.≤-trans (Nat.m≤n+m _ _)
                             (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

  count-concat-tabulate-pair-≤
    : ∀ {nE} (f : Fin nE → List (Fin n)) (e e' : Fin nE) → ¬ (e ≡ e')
    → (v : Fin n)
    → count v (f e) + count v (f e') ≤ⁿ count v (concat (tabulate f))
  count-concat-tabulate-pair-≤ f zero    zero     e≢e' v = ⊥-elim (e≢e' refl)
  count-concat-tabulate-pair-≤ f zero    (suc e') e≢e' v =
    Nat.≤-trans
      (Nat.+-monoʳ-≤ (count v (f zero))
                     (count-concat-tabulate-≤ (λ i → f (suc i)) e' v))
      (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
  count-concat-tabulate-pair-≤ f (suc e) zero     e≢e' v =
    Nat.≤-trans
      (Nat.≤-reflexive (Nat.+-comm (count v (f (suc e))) (count v (f zero))))
      (Nat.≤-trans
        (Nat.+-monoʳ-≤ (count v (f zero))
                       (count-concat-tabulate-≤ (λ i → f (suc i)) e v))
        (Nat.≤-reflexive (sym (count-++ v (f zero) _))))
  count-concat-tabulate-pair-≤ f (suc e) (suc e')  e≢e' v =
    Nat.≤-trans
      (count-concat-tabulate-pair-≤ (λ i → f (suc i)) e e'
        (λ eq → e≢e' (cong suc eq)) v)
      (Nat.≤-trans (Nat.m≤n+m _ _)
                   (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open SS.PerHG H dih
    using (Order; Incomp; pe-stack; pe-term; ++-stack)
  open SS.FrontSwap H dih K uniq-cod using (RunInterchange; box-interchange)

  ----------------------------------------------------------------------
  -- ## Reachable-stack uniqueness, sourced from the `Linear`-backed
  -- reservoir invariant.
  --
  -- `FireMidInterchange.fire-mid-interchange` now needs two `Unique`
  -- witnesses (`Unique sp` and `Unique` of the e'-first run's final stack
  -- `eout e ++ r₁'`) to discharge the eval-coincidence residuals
  -- `coh-in`/`coh-out` via `eval-rigid`.  Both are instances of "every
  -- stack reachable by `process-edges … H.dom` is `Unique`" — the
  -- reservoir/freshness invariant of the decoder run
  -- (`StackUniqueReach.pe-stack-Unique`), specialised to a mid-run order.
  --
  -- The reservoir over `H.dom` for an order `o` is the *bound* half of
  -- `Linear H` (`proj₂ lin`) specialised to `o` — TRUE precisely when `o`
  -- is duplicate-free (a permutation of `range nE`), which holds for every
  -- order the downstream `swap-≈` consumes (all `↝*`-reachable from
  -- `range nE`).  `StackUniqueReach.dom-reservoir-prov` PROVES the reservoir
  -- from that `↭ range` provenance + the `Linear` bound, and
  -- `reservoir-prefix` descends it to a PREFIX order; NO false-as-stated
  -- `∀ o` reservoir postulate is used.  This (transitively) supplies the
  -- two `Unique` witnesses `fire-mid-interchange` needs, so the two `≅↭`
  -- eval-coincidence residuals `coh-in`/`coh-out` are THEOREMS.

  -- Every stack reachable by running an order `o` from `H.dom` is `Unique`,
  -- GIVEN the reservoir invariant for `o` (which is sourced from the
  -- swap-site `↭ range` provenance, possibly via a prefix drop).
  reached-Unique-from
    : ∀ (o : Order) → SUR.Reservoir≤1 H o H.dom → Unique (pe-stack o H.dom)
  reached-Unique-from o inv =
    SUR.Reservoir≤1⇒Unique H [] (pe-stack o H.dom)
      (SUR.reservoir-split H o [] H.dom
        (subst (λ z → SUR.Reservoir≤1 H z H.dom) (sym (++-identityʳ o)) inv))

  ----------------------------------------------------------------------
  -- FIRING STABILITY (Linear + Incomp), re-derived verbatim from the
  -- `private` blocks of `SwapValidity.PerHG`.
  ----------------------------------------------------------------------

  private
    consume-bnd : ∀ (v : Fin H.nV) → count v (consumedList H) ≤ⁿ 1
    consume-bnd v = subst (_≤ⁿ 1) (proj₁ lin v) (proj₂ lin v)

    ein-concat-bnd : ∀ (v : Fin H.nV)
                   → count v (concat (tabulate H.ein)) ≤ⁿ 1
    ein-concat-bnd v =
      Nat.≤-trans
        (Nat.≤-trans (Nat.m≤n+m _ (count v H.cod))
                     (Nat.≤-reflexive (sym (count-++ v H.cod _))))
        (consume-bnd v)

    ein-ein-disjoint
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → (v : Fin H.nV)
      → 0 <ⁿ count v (H.ein e) → count v (H.ein e') ≡ 0
    ein-ein-disjoint {e} {e'} e≢e' v v∈ein-e =
      Nat.n≤0⇒n≡0
        (s≤s⁻¹
          (Nat.≤-trans
            (Nat.+-monoˡ-≤ (count v (H.ein e')) v∈ein-e)
            (Nat.≤-trans (count-concat-tabulate-pair-≤ H.ein e e' e≢e' v)
                         (ein-concat-bnd v))))

    eout-ein-disjoint
      : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e') → (v : Fin H.nV)
      → 0 <ⁿ count v (H.ein e') → count v (H.eout e) ≡ 0
    eout-ein-disjoint {e} {e'} ¬dep v v∈ein-e' =
      Nat.n≤0⇒n≡0
        (Nat.≮⇒≥ λ v∈eout-e →
          ¬dep (v , count-pos→∈ v∈eout-e , count-pos→∈ v∈ein-e'))

    count-ein'-pres
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → (v : Fin H.nV) → 0 <ⁿ count v (H.ein e')
      → count v s ≡ count v (H.eout e ++ r₁)
    count-ein'-pres {e} {e'} e≢e' ¬dep r₁ s p v v∈ein-e' =
      trans (↭⇒count p v)
      (trans (count-++ v (H.ein e) r₁)
      (trans (cong (_+ count v r₁)
                   (ein-ein-disjoint (λ eq → e≢e' (sym eq)) v v∈ein-e'))
      (sym (trans (count-++ v (H.eout e) r₁)
                  (cong (_+ count v r₁) (eout-ein-disjoint ¬dep v v∈ein-e'))))))

    count-zero-or-pos : (e' : Fin H.nE) (v : Fin H.nV)
                      → (count v (H.ein e') ≡ 0) ⊎ (0 <ⁿ count v (H.ein e'))
    count-zero-or-pos e' v with count v (H.ein e')
    ... | zero  = inj₁ refl
    ... | suc _ = inj₂ (s≤sⁿ z≤nⁿ)

    ein'-≤-fwd
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → (∀ v → count v (H.ein e') ≤ⁿ count v s)
      → (∀ v → count v (H.ein e') ≤ⁿ count v (H.eout e ++ r₁))
    ein'-≤-fwd {e} {e'} e≢e' ¬dep r₁ s p h v with count-zero-or-pos e' v
    ... | inj₁ z   = subst (_≤ⁿ count v (H.eout e ++ r₁)) (sym z) z≤nⁿ
    ... | inj₂ pos =
          subst (count v (H.ein e') ≤ⁿ_) (count-ein'-pres e≢e' ¬dep r₁ s p v pos) (h v)

    ein'-≤-bwd
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → (∀ v → count v (H.ein e') ≤ⁿ count v (H.eout e ++ r₁))
      → (∀ v → count v (H.ein e') ≤ⁿ count v s)
    ein'-≤-bwd {e} {e'} e≢e' ¬dep r₁ s p h v with count-zero-or-pos e' v
    ... | inj₁ z   = subst (_≤ⁿ count v s) (sym z) z≤nⁿ
    ... | inj₂ pos =
          subst (count v (H.ein e') ≤ⁿ_) (sym (count-ein'-pres e≢e' ¬dep r₁ s p v pos)) (h v)

    -- If `e'` fires from `s`, it fires from `eout e ++ r₁` too.
    e'-fires-stable
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → ∀ {r₂' p₂'} → extract-prefix (H.ein e') s ≡ just (r₂' , p₂')
      → Σ[ r ∈ List (Fin H.nV) ] Σ[ q ∈ _ ]
          extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ just (r , q)
    e'-fires-stable {e} {e'} e≢e' ¬dep r₁ s p {r₂'} {p₂'} eqe' =
      count-≤→extract-prefix (H.ein e') (H.eout e ++ r₁)
        (ein'-≤-fwd e≢e' ¬dep r₁ s p
          (extract-prefix-just→count-≤ (H.ein e') s r₂' p₂'))

    -- If `e'` skips from `s`, it skips from `eout e ++ r₁` too.
    e'-skips-stable
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → extract-prefix (H.ein e') s ≡ nothing
      → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ nothing
    e'-skips-stable {e} {e'} e≢e' ¬dep r₁ s p eqe' =
      go (extract-prefix (H.ein e') (H.eout e ++ r₁)) refl
      where
        go : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ]
                           H.eout e ++ r₁ Perm.↭ H.ein e' ++ r))
           → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ m
           → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ nothing
        go nothing      eq  = eq
        go (just (r , q)) eq =
          ⊥-elim (nothing≢just (trans (sym eqe')
            (proj₂ (proj₂ (count-≤→extract-prefix (H.ein e') s
              (ein'-≤-bwd e≢e' ¬dep r₁ s p
                (extract-prefix-just→count-≤ (H.ein e') (H.eout e ++ r₁) r q)))))))

  ----------------------------------------------------------------------
  -- THE SINGLE RESIDUAL (M) — `fire-mid-interchange`.
  --
  -- Both edges FIRE in both orders.  Unpacking the four `EdgeStepR`
  -- fire-witnesses, the two runs (after `idˡ` strips the trailing `id`)
  -- factor as composites of `fire-term`s.  The genuine content — the two
  -- framed boxes `(Agen-edge ⊗ id)` on DISJOINT blocks commute via σ
  -- (`box-interchange`), transported through the `fire-mid`/`box-of`/
  -- `unflatten-++-≅`/`subst₂` bracketing and the locating permutes — is
  -- isolated here, with the reshuffle bundled existentially.
  --
  -- This is the SMALLEST true statement closing BOTH-FIRE: it mentions
  -- NEITHER `cod` NOR the final permute, only the four unpacked fire
  -- witnesses and the two front runs.  It is the EXACT analogue of
  --   * `Sub/SwapAtomAligned.swap-mac-lane-residual` (the whole two-edge
  --     `ProcessEdges↭Goal` obligation, unpacked, that the `--with-K`
  --     development leaves open), and
  --   * `Sub/StackEquivariance.fire-mid-equivariant` (a per-edge box
  --     residual of the same disjoint-block / σ-naturality flavour).
  -- TRUE because, the two edges being `Incomp` (DISJOINT wire blocks),
  -- the boxes commute by the bifunctor/σ-naturality interchange axiom
  -- `σ ∘ (f ⊗ g) ≈ (g ⊗ f) ∘ σ` (= `box-interchange`).
  ----------------------------------------------------------------------

  -- Reduced (no longer a free postulate here): discharged by the standalone
  -- `Sub/FireMidInterchange.agda`, which PROVES the σ-interchange + permute
  -- reconciliation around a single isolated `block-nf` residual (the pure
  -- Mac-Lane block-normal-form `unflatten-++-≅`/`subst₂` bracketing — the part
  -- even the --with-K development leaves open).
  -- Now carries the two `Unique` witnesses `FMI.fire-mid-interchange`
  -- needs (`Unique sp` and `Unique (eout e ++ r₁')`) — its eval-coincidence
  -- residuals `coh-in`/`coh-out` are discharged by `eval-rigid` on those
  -- `Unique` codomains.  Both are supplied at the call site below from the
  -- `Linear`-backed reservoir invariant (`reached-Unique`).
  fire-mid-interchange
      : ∀ {e e' : Fin H.nE} (inc : Incomp e e')
          (sp : List (Fin H.nV))
          (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
          (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
          (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
          (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
          (us-sp : Unique sp)
          (us-mid₁ : Unique (H.eout e ++ r₁)) (us-mid₂ : Unique (H.eout e' ++ r₂'))
          (us-cod : Unique (H.eout e ++ r₁'))
      → Σ[ r ∈ (H.eout e' ++ r₂) Perm.↭ (H.eout e ++ r₁') ]
          ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
              ∘ fire-term H e' sp r₂' p₂' )
          ≈Term permute-via-vlab H.vlab r
                  ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                        ∘ fire-term H e sp r₁ p₁ )
  fire-mid-interchange = FMI.fire-mid-interchange H dih K uniq-cod lin

  ----------------------------------------------------------------------
  -- The EMPTY-TAIL interchange core.
  ----------------------------------------------------------------------

  ----------------------------------------------------------------------
  -- The EMPTY-TAIL interchange core.
  --
  -- The four-way firing split is performed by the helper `build`, whose
  -- four `EdgeStepR` arguments carry FRESH index variables for the
  -- post-edge stacks/terms; matching their `skipR`/`fireR` constructors
  -- refines those variables to `id` / `fire-term` and to `s` /
  -- `eout e ++ rest` respectively, with NO unification against the stuck
  -- `edge-step` redex (this is the `Sub/StackEquivariance.edge-step-equivariant`
  -- idiom that dodges the green-slime with-abstraction wall).  At the
  -- call site the fresh indices specialise back to the `proj₁/proj₂
  -- (edge-step …)` forms inside `pe-stack`/`pe-term`, so `build`'s output
  -- has exactly the `RunInterchange` field types.
  ----------------------------------------------------------------------

  -- `run-interchange₀` takes the EMPTY-TAIL swap-order reservoir
  -- `Reservoir≤1 H (ps ++ e' ∷ e ∷ []) H.dom` (sourced upstream from the
  -- full swap-order `↭ range` provenance via a prefix drop).  From it the
  -- two `Unique` witnesses `fire-mid-interchange` needs are derived:
  --   * `Unique (pe-stack ps H.dom)`              (prefix drop `e' ∷ e ∷ []`)
  --   * `Unique (pe-stack (ps ++ e' ∷ e ∷ []) H.dom)`  (the reservoir itself)
  run-interchange₀
    : ∀ (ps : Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ []) H.dom
    → RunInterchange ps [] inc
  run-interchange₀ ps {e} {e'} inc res with e ≟ e'
  -- e ≡ e': the two orders are literally the same composition.
  ... | yes refl =
        record { reshuffle = Perm.refl ; run-eq = ≈-Term-sym idˡ }
  ... | no  e≢e' =
        record { reshuffle = proj₁ Σr ; run-eq = proj₂ Σr }
    where
      sp : List (Fin H.nV)
      sp = pe-stack ps H.dom

      -- Reservoir for the prefix `ps`, by dropping `e' ∷ e ∷ []`.
      res-ps : SUR.Reservoir≤1 H ps H.dom
      res-ps = SUR.reservoir-prefix H ps (e' ∷ e ∷ []) H.dom res

      -- Reservoir for the e'-first INTERMEDIATE order `ps ++ e' ∷ []`, by
      -- dropping the suffix `e ∷ []` from the full swap order (a prefix drop,
      -- after re-associating `(ps ++ e' ∷ []) ++ e ∷ [] ≡ ps ++ e' ∷ e ∷ []`).
      res-e' : SUR.Reservoir≤1 H (ps ++ e' ∷ []) H.dom
      res-e' =
        SUR.reservoir-prefix H (ps ++ e' ∷ []) (e ∷ []) H.dom
          (subst (λ z → SUR.Reservoir≤1 H z H.dom)
                 (sym (++-assoc ps (e' ∷ []) (e ∷ [])))
                 res)

      -- Reservoir for the e-first INTERMEDIATE order `ps ++ e ∷ []`.  The
      -- swap order `ps ++ e' ∷ e ∷ []` is multiset-equal to `ps ++ e ∷ e' ∷ []`
      -- (swap the last two edges; `reservoir-resp-↭`), from which `e' ∷ []` is
      -- dropped as a suffix (re-associate, then `reservoir-prefix`).
      res-e : SUR.Reservoir≤1 H (ps ++ e ∷ []) H.dom
      res-e =
        SUR.reservoir-prefix H (ps ++ e ∷ []) (e' ∷ []) H.dom
          (subst (λ z → SUR.Reservoir≤1 H z H.dom)
                 (sym (++-assoc ps (e ∷ []) (e' ∷ [])))
                 (SUR.reservoir-resp-↭ H H.dom
                   (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl))
                   res))

      ¬dep-ee' : ¬ (Dep H e e')
      ¬dep-ee' = proj₁ inc
      ¬dep-e'e : ¬ (Dep H e' e)
      ¬dep-e'e = proj₂ inc

      just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
      just-inj refl = refl

      --------------------------------------------------------------
      -- The abstract-index four-way build.  `we`/`we'` are the firing
      -- witnesses of the `e ∷ e'` run (e from sp, e' from the post-e
      -- stack `s1`); `ue`/`ue'` of the `e' ∷ e` run (e' from sp, e from
      -- the post-e' stack `u1`).  The returned `Σ` is exactly
      -- `run₂ ≈Term permute r ∘ run₁` with the trailing `id`s in place,
      -- over the abstract stacks/terms.
      --------------------------------------------------------------
      -- `us-u2 : Unique u2` — the e'-first run's FINAL-stack uniqueness,
      -- used ONLY in the both-fire branch (where it refines to
      -- `Unique (eout e ++ r₁')`) to supply `fire-mid-interchange`'s
      -- `coh-out` `Unique`-codomain witness.  Supplied at the `Σr` call
      -- from `reached-Unique`.
      -- `us-s1 : Unique s1` / `us-u1 : Unique u1` — the e-first / e'-first
      -- INTERMEDIATE-stack uniqueness, used ONLY in the both-fire branch
      -- (where they refine to `Unique (eout e ++ r₁)` / `Unique (eout e' ++ r₂')`)
      -- to supply `fire-mid-interchange`'s two `us-mid` `q-second`-codomain
      -- witnesses.  Supplied at the `Σr` call from `reached-Unique`.
      build
        : ∀ {s1 t1} (we  : EdgeStepR H sp e  s1 t1)
            {s2 t2} (we' : EdgeStepR H s1 e' s2 t2)
            {u1 v1} (ue  : EdgeStepR H sp e' u1 v1)
            {u2 w2} (ue' : EdgeStepR H u1 e  u2 w2)
            (us-s1 : Unique s1) (us-u1 : Unique u1) (us-u2 : Unique u2)
        → Σ[ r ∈ s2 Perm.↭ u2 ]
            ((id ∘ w2) ∘ v1)
            ≈Term permute-via-vlab H.vlab r ∘ ((id ∘ t2) ∘ t1)

      ------------------------------------------------------------
      -- (1) e SKIPS sp.
      ------------------------------------------------------------
      -- BOTH-SKIP: t1=id,t2=id,v1=id,w2=id; s2=sp=u2; reshuffle refl.
      build (skipR eqe) (skipR eqe') (skipR _) (skipR _) _ _ _ =
        Perm.refl , ≈-Term-sym idˡ
      -- e skips sp, e' skips sp (e-run), but the e'-run FIRES e' from sp:
      -- contradiction (`we'` says e' skips sp; `ue` says e' fires sp).
      build (skipR eqe) (skipR eqe') (fireR ur₂' up₂' ueqe') _ _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe') ueqe'))
      -- e skips sp, e' skips sp, e' skips sp (e'-run ⇒ u1 = sp), but the
      -- e'-run FIRES e from sp: contradiction (`eqe` says e skips sp).
      build (skipR eqe) (skipR eqe') (skipR ueqe') (fireR ur₁ up₁ ueqe1) _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe) ueqe1))
      -- e skips sp but e' (after e skip ⇒ from sp) fires, yet the e'-run
      -- has e' SKIP from sp: contradiction (e' fires sp here, skips there).
      build (skipR eqe) (fireR r₂' p₂' eqe') (skipR eqe'-bad) _ _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe'-bad) eqe'))
      -- e skips sp, e' fires sp; the e'-run fires e' (residual r₂') then
      -- decides e on the post-e' stack `eout e' ++ r₂'`.
      build (skipR eqe) (fireR r₂' p₂' eqe') (fireR ur₂' up₂' ueqe')
            (fireR r₁' p₁' eqe1) _ _ _ =
        -- e fires the post-e' stack — IMPOSSIBLE (e skips sp; stability).
        ⊥-elim (nothing≢just
          (trans (sym (e'-skips-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e
                         ur₂' sp up₂' eqe)) eqe1))
      build (skipR eqe) (fireR r₂' p₂' eqe') (fireR ur₂' up₂' ueqe')
            (skipR eqe1) _ _ _ =
        -- run₁ ≡ (id ∘ fire-term e' sp …) ∘ id ; run₂ ≡ (id ∘ id) ∘ fire-term e' sp …
        -- The two `fire-term e' sp` agree once (ur₂',up₂') ≡ (r₂',p₂').
        pin (just-inj (trans (sym ueqe') eqe'))
        where
          pin : (ur₂' , up₂') ≡ (r₂' , p₂') → _
          pin refl =
            Perm.refl ,
            ≈-Term-trans
              (∘-resp-≈ idˡ ≈-Term-refl)   -- (id∘id)∘F ≈ id∘F
              (≈-Term-trans idˡ            -- id∘F ≈ F
                (≈-Term-sym
                  (≈-Term-trans idˡ        -- id∘run₁ ≈ run₁
                    (≈-Term-trans (∘-resp-≈ idˡ ≈-Term-refl) idʳ))))
                    -- run₁ = (id∘F)∘id ≈ F∘id ≈ F

      ------------------------------------------------------------
      -- (2) e FIRES sp (residual r₁).
      ------------------------------------------------------------
      -- e' skips the post-e stack; the e'-run has e' fire from sp:
      -- IMPOSSIBLE by stability (e' fires sp ⇒ e' fires post-e).
      build (fireR r₁ p₁ eqe) (skipR eqe2) (fireR ur₂' up₂' ueqe') _ _ _ _ =
        ⊥-elim (nothing≢just
          (trans (sym eqe2)
            (proj₂ (proj₂ (e'-fires-stable e≢e' ¬dep-ee' r₁ sp p₁ ueqe')))))
      -- e fires sp, e' skips post-e, e' also skips sp; the e'-run then
      -- fires e from sp (residual ur₁ ≡ r₁).
      build (fireR r₁ p₁ eqe) (skipR eqe2) (skipR eqe'n) (skipR eqe-bad) _ _ _ =
        -- e skips sp in the e'-run — contradicts `eqe`.
        ⊥-elim (nothing≢just (trans (sym eqe-bad) eqe))
      build (fireR r₁ p₁ eqe) (skipR eqe2) (skipR eqe'n)
            (fireR ur₁ up₁ ueqe) _ _ _ =
        -- run₁ ≡ (id ∘ id) ∘ fire-term e sp r₁ p₁
        -- run₂ ≡ (id ∘ fire-term e sp ur₁ up₁) ∘ id, (ur₁,up₁) ≡ (r₁,p₁).
        pin (just-inj (trans (sym ueqe) eqe))
        where
          pin : (ur₁ , up₁) ≡ (r₁ , p₁) → _
          pin refl =
            Perm.refl ,
            ≈-Term-trans
              (∘-resp-≈ idˡ ≈-Term-refl)   -- (id∘F)∘id ≈ F∘id
              (≈-Term-trans idʳ            -- F∘id ≈ F
                (≈-Term-sym
                  (≈-Term-trans idˡ        -- id∘run₁ ≈ run₁
                    (≈-Term-trans (∘-resp-≈ idˡ ≈-Term-refl) idˡ))))
                    -- run₁ = (id∘id)∘F ≈ id∘F ≈ F
      -- e fires sp, e' fires post-e; the e'-run has e' skip sp:
      -- IMPOSSIBLE by stability (e' fires post-e ⇒ e' fires sp).
      build (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2) (skipR eqe'n) _ _ _ _ =
        ⊥-elim (nothing≢just
          (trans (sym (e'-skips-stable e≢e' ¬dep-ee' r₁ sp p₁ eqe'n)) eqe2))
      -- e fires sp, e' fires post-e, e' fires sp, but e SKIPS post-e':
      -- IMPOSSIBLE by stability (e fires sp ⇒ e fires post-e').
      build (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2) (fireR r₂' p₂' eqe')
            (skipR eqe1) _ _ _ =
        ⊥-elim (nothing≢just
          (trans (sym eqe1)
            (proj₂ (proj₂
              (e'-fires-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e
                r₂' sp p₂' eqe)))))
      -- BOTH-FIRE — the genuine content, closed by the residual.
      build (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2) (fireR r₂' p₂' eqe')
            (fireR r₁' p₁' eqe1) us-s1 us-u1 us-u2 =
        r ,
        -- run₂ = (id ∘ uH') ∘ uH
        --      ≈ uH' ∘ uH                              [idˡ]
        --      ≈ permute r ∘ (tH' ∘ tH)                [box-eq]
        --      ≈ permute r ∘ ((id ∘ tH') ∘ tH)         [≈-sym idˡ inside]
        --      = permute r ∘ run₁.
        ≈-Term-trans
          (∘-resp-≈ idˡ ≈-Term-refl)
          (≈-Term-trans box-eq
            (∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl)))
        where
          -- The two INTERMEDIATE-stack `Unique`s `fire-mid-interchange` now
          -- needs: `us-mid₁ = Unique (eout e ++ r₁)` is the e-first
          -- intermediate `s1` (`we = fireR r₁ p₁ eqe`'s post-stack);
          -- `us-mid₂ = Unique (eout e' ++ r₂')` is the e'-first intermediate
          -- `u1` (`ue = fireR r₂' p₂' eqe'`'s post-stack).
          RI = fire-mid-interchange inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
                 (reached-Unique-from ps res-ps) us-s1 us-u1 us-u2
          r  = proj₁ RI
          box-eq
            : ( fire-term H e (H.eout e' ++ r₂') r₁' p₁'
                  ∘ fire-term H e' sp r₂' p₂' )
              ≈Term permute-via-vlab H.vlab r
                      ∘ ( fire-term H e' (H.eout e ++ r₁) r₂ p₂
                            ∘ fire-term H e sp r₁ p₁ )
          box-eq = proj₂ RI

      --------------------------------------------------------------
      -- Assemble the record by feeding the four `edge-step-graph`
      -- witnesses; their indices specialise `build`'s fresh variables
      -- to the `proj₁/proj₂ (edge-step …)` forms of `pe-stack`/`pe-term`.
      --------------------------------------------------------------
      Σr : Σ[ r ∈ pe-stack (e ∷ e' ∷ []) sp Perm.↭ pe-stack (e' ∷ e ∷ []) sp ]
             pe-term (e' ∷ e ∷ []) sp
             ≈Term permute-via-vlab H.vlab r ∘ pe-term (e ∷ e' ∷ []) sp
      Σr = build (edge-step-graph H sp e)
                 (edge-step-graph H (proj₁ (edge-step H sp e)) e')
                 (edge-step-graph H sp e')
                 (edge-step-graph H (proj₁ (edge-step H sp e')) e)
                 -- `s1 = pe-stack (e ∷ []) sp` (definitionally `proj₁ (edge-step
                 -- H sp e)`); its uniqueness is `reached-Unique` of the e-first
                 -- intermediate order `ps ++ e ∷ []`, transported across `++-stack`.
                 (subst Unique (++-stack ps (e ∷ []) H.dom)
                        (reached-Unique-from (ps ++ e ∷ []) res-e))
                 -- `u1 = pe-stack (e' ∷ []) sp` — the e'-first intermediate;
                 -- `reached-Unique` of `ps ++ e' ∷ []`, transported across `++-stack`.
                 (subst Unique (++-stack ps (e' ∷ []) H.dom)
                        (reached-Unique-from (ps ++ e' ∷ []) res-e'))
                 -- `u2 = pe-stack (e' ∷ e ∷ []) sp` (definitionally); its
                 -- uniqueness is `reached-Unique` of the combined order
                 -- `ps ++ e' ∷ e ∷ []`, transported across `++-stack`.
                 (subst Unique (++-stack ps (e' ∷ e ∷ []) H.dom)
                        (reached-Unique-from (ps ++ e' ∷ e ∷ []) res))
