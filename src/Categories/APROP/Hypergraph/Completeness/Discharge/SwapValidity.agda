-- Discharge of the `swap-validity` postulate of `IsoInvarianceWiring.agda`'s
-- `PerHG` module (§(II) of the informal completeness proof).
--
--   swap-validity : ∀ {o₁ o₂} → o₁ ↝ o₂ → Valid o₁ → Valid o₂
--
-- where `Valid o = proj₁ (process-edges H o dom) Perm.↭ cod` and a step
-- `o₁ ↝ o₂` is `swap-step ps qs (inc : Incomp (Dep H) e e')` swapping an
-- adjacent `Dep`-incomparable pair after a prefix `ps`.
--
-- ## Route (WiringLemmas.agda Lemma 1)
--
-- The final live-wire multiset (`finalStack o = proj₁ (process-edges o dom)`)
-- is order-independent for a swap of `Dep`-incomparable adjacent edges.
-- Concretely we prove
--
--   finalStack-↭ : finalStack o₁  Perm.↭  finalStack o₂
--
-- and then transport `Valid` by
--
--   Valid o₂  =  ↭-trans (↭-sym finalStack-↭) (Valid o₁).
--
-- ## Decomposition
--
--   (1) `++-stack` (= `process-edges-++-stack`, imported, REAL): the final
--       stack of `ps ++ rest` from `dom` is that of `rest` from the
--       post-`ps` stack `sp = pe-stack ps dom`.  This reduces the general
--       swap to a FRONT swap (`ps = []`) on the shared post-prefix stack.
--
--   (2) `front-swap-stack-↭` — the front-of-stack two-edge stack
--       permutation, for `Dep`-INCOMPARABLE `e , e'`.  CONSTRUCTIVELY
--       reduced (via `pe-stack-resp-↭`) to the two-edge head bridge
--       `two-edge-swap-stack-↭`, which case-splits the four `extract-prefix`
--       firing outcomes:
--         * BOTH-SKIP — `Perm.refl` (both final stacks are `s`);
--         * BOTH-FIRE — closed by `post-swap-stack-↭` (the genuine
--           order-independent multiset content, ported from
--           `Sub/AllFireEdgeSwap.agda`; pure `_↭_` reasoning);
--         * FIRING-DIVERGENCE (one ordering fires both edges, the other
--           only one) — now FULLY DISCHARGED (no postulate) from the
--           `Linear H` premise, via firing-stability (below).
--
--       The divergence case is FALSE under `Incomp` ALONE (which constrains
--       only `eout`-vs-`ein` overlaps, NOT `ein`-vs-`ein`): on a non-linear
--       `H` two `Incomp` edges sharing an INPUT wire give different final
--       stacks in the two orders.  But `PerHG` now TAKES `lin : Linear H`,
--       and under `Linear` the two `ein` multisets of DISTINCT edges are
--       count-disjoint (each vertex consumed ≤ 1 globally).  Together with
--       `Incomp` (`eout e` disjoint from `ein e'`) this makes the firing
--       decision of `e'` STABLE between the pre-`e` and post-`e` stacks —
--       so the divergence cases reduce to equal stacks or are impossible.
--
--   (3) `swap-validity` — assembled from (1) + (2) + `Perm.↭`-transitivity;
--       it now takes `lin : Linear H` (supplied downstream as the REAL proof
--       `DecodeAttemptLinearP.⟪⟫-LinearP`, never a postulate).
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.SwapValidity
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Completeness.DecodeProperties sig
  using (extract-prefix-↭-residual; extract-prefix-↭-nothing)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear; count; count-++; consumedList)

-- The chain we discharge against, imported read-only: `PH.Valid`, `PH.↝`,
-- `PH.Order`, and the LinExt instantiation (`Incomp`, `swap-step`).
import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (process-edges-++-stack)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map; concat)
open import Data.List.Base using (tabulate)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; Σ-syntax; ∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

------------------------------------------------------------------------
-- Generic `count` / `extract-prefix` combinatorics (H-agnostic).
--
-- These discharge the divergence residual: under `Linear` the two `ein`
-- multisets of distinct edges are count-disjoint, and under `Incomp`
-- `eout e` is count-disjoint from `ein e'`.  Together they make the
-- firing decision of `e'` STABLE between the pre-`e` stack `s` and the
-- post-`e` stack `eout e ++ r₁` — so no order can fire an edge the other
-- order skips.  All lemmas are over `List (Fin n)`.
--
-- The core lemmas live in the shared `CountCombinatorics` leaf; the
-- specialised helpers (`extract-prefix-just→count-≤`,
-- `count-concat-tabulate-≤`, …) are kept local.
------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.CountCombinatorics sig
  using ( count-cons-yes; count-cons-no; ∈→count-pos; count-pos→∈
        ; ↭⇒count; count-pos→extract-elem; count-≤→extract-prefix; ++-cancelˡ)

private
  variable
    n : ℕ

  -- (P1) A successful `extract-prefix` certifies the sub-multiset bound.
  extract-prefix-just→count-≤
    : (ks xs rest : List (Fin n)) (p : xs Perm.↭ ks ++ rest)
    → ∀ v → count v ks ≤ⁿ count v xs
  extract-prefix-just→count-≤ ks xs rest p v =
    Nat.≤-trans (Nat.m≤m+n (count v ks) (count v rest))
                (Nat.≤-reflexive (trans (sym (count-++ v ks rest))
                                        (sym (↭⇒count p v))))

  -- count distributes over a single `tabulate`/`concat` summand: every
  -- edge's `ein`-count is ≤ the total concat-count.
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

  -- Two DISTINCT edges contribute disjointly to the concat-count.
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

------------------------------------------------------------------------
-- Per-hypergraph: fix `H` and a `Dep`-irreflexivity witness `dih`, and
-- open the existing `PerHG` machinery.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H) where
  private module H = Hypergraph H

  -- The existing per-hypergraph module from the chain (read-only).  We
  -- match its `Order`, `Valid`, `_↝_` definitionally so the result can
  -- replace the postulate verbatim.
  module PH = IW.PerHG H dih

  -- `Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)` and the swap-step
  -- constructor, both from the LinExt instantiation `PH.L`.
  open PH.L public using (Incomp; swap-step)

  ------------------------------------------------------------------------
  -- (Linearity + Incomp ⇒ firing-stability) The two count-disjointness
  -- facts that kill the divergence cases.
  ------------------------------------------------------------------------

  private
    -- From `Linear`, the total consumption count of any vertex is ≤ 1.
    consume-bnd : ∀ (v : Fin H.nV) → count v (consumedList H) ≤ⁿ 1
    consume-bnd v = subst (_≤ⁿ 1) (proj₁ lin v) (proj₂ lin v)

    -- Hence the count of `v` across ALL `ein`s (`concat (tabulate ein)`)
    -- is ≤ 1.
    ein-concat-bnd : ∀ (v : Fin H.nV)
                   → count v (concat (tabulate H.ein)) ≤ⁿ 1
    ein-concat-bnd v =
      Nat.≤-trans
        (Nat.≤-trans (Nat.m≤n+m _ (count v H.cod))
                     (Nat.≤-reflexive (sym (count-++ v H.cod _))))
        (consume-bnd v)

    -- (Linearity) Two DISTINCT edges' `ein`s are count-disjoint: no
    -- vertex is consumed by both.  `1 + count v (ein e') ≤ count v (ein e)
    -- + count v (ein e') ≤ 1`, so `count v (ein e') ≡ 0`.
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

    -- (Incomp) `eout e` is count-disjoint from `ein e'`: no vertex
    -- produced by `e` is consumed by `e'`.
    eout-ein-disjoint
      : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e') → (v : Fin H.nV)
      → 0 <ⁿ count v (H.ein e') → count v (H.eout e) ≡ 0
    eout-ein-disjoint {e} {e'} ¬dep v v∈ein-e' =
      Nat.n≤0⇒n≡0
        (Nat.≮⇒≥ λ v∈eout-e →
          ¬dep (v , count-pos→∈ v∈eout-e , count-pos→∈ v∈ein-e'))

  ------------------------------------------------------------------------
  -- The final stack of running an order from a stack.
  ------------------------------------------------------------------------

  -- `finalStack o = proj₁ (process-edges o dom)` (the `Valid`-relevant
  -- projection); generalised here to an arbitrary starting stack `s`.
  pe-stack : PH.Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = proj₁ (process-edges H o s)

  finalStack : PH.Order → List (Fin H.nV)
  finalStack o = pe-stack o H.dom

  -- The stack `_++_`-factoring (imported, REAL): the final stack of
  -- `ps ++ rest` from `s` is that of `rest` from the post-`ps` stack.
  ++-stack
    : ∀ (ps rest : PH.Order) (s : List (Fin H.nV))
    → pe-stack (ps ++ rest) s ≡ pe-stack rest (pe-stack ps s)
  ++-stack = process-edges-++-stack H

  ------------------------------------------------------------------------
  -- (2) THE ANALYTIC CORE — front-of-stack two-edge stack permutation.
  --
  -- For `Dep`-INCOMPARABLE `e , e'` (neither produces a wire the other
  -- consumes), running `e ∷ e' ∷ qs` from a stack `s` reaches a final
  -- stack that is a `Perm.↭`-permutation of the one reached by running
  -- the swapped order `e' ∷ e ∷ qs` from `s`.
  --
  -- ## What is CONSTRUCTIVE here (no postulate)
  --
  --   * `edge-step-stack-resp-↭` / `pe-stack-resp-↭` — the final-stack
  --     PROJECTION of `process-edges` is `Perm.↭`-respecting in the
  --     starting stack.  (Via `extract-prefix-↭-{residual,nothing}`:
  --     a permutation of the input makes every edge fire/skip the same
  --     way, with the residual stack staying `↭`.)
  --
  --   * `post-swap-stack-↭` (ported from `Sub/AllFireEdgeSwap.agda`,
  --     ~190 LOC of pure `_↭_` reasoning, NO Linearity / signature
  --     decidability used) — the BOTH-FIRE multiset content is order
  --     independent.
  --
  --   * `front-swap-stack-↭` itself is REDUCED constructively to the
  --     two-edge head bridge `two-edge-swap-stack-↭` (below) by pushing
  --     the shared tail `qs` through `pe-stack-resp-↭`; that bridge in
  --     turn case-splits the four firing outcomes and discharges
  --     ALL of them CONSTRUCTIVELY (both-skip / both-fire directly; the
  --     firing-divergence cases via firing-stability — see below).
  --
  -- ## The former residual `two-edge-swap-diverge` — now DISCHARGED
  --
  -- `Incomp` (= `¬ Dep e e' × ¬ Dep e' e`) gives only:
  --     (i)  `ein e'` is disjoint from `eout e`,  and
  --     (ii) `ein e`  is disjoint from `eout e'`.
  -- It says NOTHING about `ein e` vs `ein e'`.  When the two edges share
  -- an INPUT wire, the two firing orders can produce genuinely different
  -- final stacks.  Concrete counter-example (nV ≥ 3, distinct v,w,u):
  --
  --     ein e  = [v]   eout e  = [w]
  --     ein e' = [v]   eout e' = [u]      s = [v]
  --
  --   * order `e ∷ e'`:  e fires, stack → [w];  e' skips;  final = [w].
  --   * order `e' ∷ e`:  e' fires, stack → [u];  e  skips;  final = [u].
  --   * `[w] Perm.↭ [u]` is FALSE.
  --
  -- So the divergence is FALSE under `Incomp` ALONE.  But this counter-
  -- example is NON-LINEAR: `v` is consumed by BOTH `ein e` and `ein e'`.
  -- `PerHG` now takes `lin : Linear H`, under which every vertex is
  -- consumed ≤ 1 time globally, so the `ein`s of DISTINCT edges are
  -- count-disjoint (`ein-ein-disjoint`).  Combined with `Incomp`'s
  -- `eout`-vs-`ein` disjointness, removing `ein e` and adding `eout e`
  -- (the `s ↝ eout e ++ r₁` step) leaves the count of every `ein e'`
  -- vertex UNCHANGED (`count-ein'-pres`).  Hence `e'`'s firing decision
  -- is STABLE across the step (`e'-fires-stable` / `e'-skips-stable`), so
  -- the divergence branches either collapse to equal stacks or are
  -- outright impossible.  The discharge is FULLY CONSTRUCTIVE given `lin`.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- `edge-step` projects to `s` (skip) or `eout e ++ rest` (fire); both
  -- are `Perm.↭`-stable under a permutation of the input stack.
  ------------------------------------------------------------------------

  -- `proj₁ (edge-step H s e)` characterised by the `extract-prefix`
  -- outcome (so we can reason about it without unfolding `edge-step`'s
  -- internal `with`).  Mirrors `AllFireNatural.AllFire-edge-step-stack`
  -- but covers BOTH branches.
  step-stack-skip
    : ∀ (e : Fin H.nE) (s : List (Fin H.nV))
    → extract-prefix (H.ein e) s ≡ nothing
    → proj₁ (edge-step H s e) ≡ s
  step-stack-skip e s eq with extract-prefix (H.ein e) s
  ... | nothing = refl

  step-stack-fire
    : ∀ (e : Fin H.nE) (s rest : List (Fin H.nV))
        (p : s Perm.↭ H.ein e ++ rest)
    → extract-prefix (H.ein e) s ≡ just (rest , p)
    → proj₁ (edge-step H s e) ≡ H.eout e ++ rest
  step-stack-fire e s rest p eq with extract-prefix (H.ein e) s
  ... | just _ = cong (λ x → H.eout e ++ proj₁ x) (just-inj eq)
    where
      just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
      just-inj refl = refl

  -- Case on `extract-prefix (H.ein e) a` WITHOUT abstracting the goal
  -- (so `proj₁ (edge-step H a e)` stays literal and the `step-stack-*`
  -- equations apply).
  edge-step-stack-resp-↭
    : ∀ {a b : List (Fin H.nV)} (e : Fin H.nE)
    → a Perm.↭ b
    → proj₁ (edge-step H a e) Perm.↭ proj₁ (edge-step H b e)
  edge-step-stack-resp-↭ {a} {b} e a↭b =
    go (extract-prefix (H.ein e) a) refl
    where
      go : (m : Maybe (Σ[ rest ∈ List (Fin H.nV) ] a Perm.↭ H.ein e ++ rest))
         → extract-prefix (H.ein e) a ≡ m
         → proj₁ (edge-step H a e) Perm.↭ proj₁ (edge-step H b e)
      go nothing eqa =
        -- `a` skips ⇒ `b` skips (decision stable under ↭).
        let eqb-nothing = extract-prefix-↭-nothing (H.ein e) a b a↭b eqa
        in subst₂ Perm._↭_
                  (sym (step-stack-skip e a eqa))
                  (sym (step-stack-skip e b eqb-nothing))
                  a↭b
      go (just (ra , pa)) eqa =
        -- `a` fires with residual `ra` (a ↭ ein e ++ ra).  Then b ↭
        -- ein e ++ ra, so b fires with residual rb ↭ ra, and the
        -- projected stacks `eout e ++ ra` ↭ `eout e ++ rb`.
        let stepb = extract-prefix-↭-residual (H.ein e) b ra
                      (Perm.↭-trans (Perm.↭-sym a↭b) pa)
            rb    = proj₁ stepb
            pb    = proj₁ (proj₂ stepb)
            eqb   = proj₁ (proj₂ (proj₂ stepb))
            ra↭rb = proj₂ (proj₂ (proj₂ stepb))
        in subst₂ Perm._↭_
                  (sym (step-stack-fire e a ra pa eqa))
                  (sym (step-stack-fire e b rb pb eqb))
                  (PermProp.++⁺ˡ (H.eout e) ra↭rb)

  ------------------------------------------------------------------------
  -- The final-stack projection of `process-edges` respects `Perm.↭`
  -- of the starting stack.
  ------------------------------------------------------------------------

  pe-stack-resp-↭
    : ∀ (qs : PH.Order) {a b : List (Fin H.nV)}
    → a Perm.↭ b
    → pe-stack qs a Perm.↭ pe-stack qs b
  pe-stack-resp-↭ []       a↭b = a↭b
  pe-stack-resp-↭ (e ∷ qs) {a} {b} a↭b =
    pe-stack-resp-↭ qs (edge-step-stack-resp-↭ e a↭b)

  ------------------------------------------------------------------------
  -- BOTH-FIRE multiset bridge (ported verbatim from
  -- `Sub/AllFireEdgeSwap.post-swap-stack-↭`; pure `_↭_` reasoning).
  ------------------------------------------------------------------------

  post-swap-stack-↭
    : ∀ (e₁ e₂ : Fin H.nE)
        (s r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : s Perm.↭ H.ein e₁ ++ r₁)
        (p₂  : H.eout e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂)
        (p₂' : s Perm.↭ H.ein e₂ ++ r₂')
        (p₁' : H.eout e₂ ++ r₂' Perm.↭ H.ein e₁ ++ r₁')
    → H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
  post-swap-stack-↭ e₁ e₂ s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁' = cancelled
    where
      open Perm.PermutationReasoning

      r₁-r₂' : H.ein e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂'
      r₁-r₂' = Perm.↭-trans (Perm.↭-sym p₁) p₂'

      step-A
        : H.eout e₂ ++ H.eout e₁ ++ r₁
        Perm.↭ H.eout e₂ ++ H.ein e₂ ++ r₂
      step-A = PermProp.++⁺ˡ (H.eout e₂) p₂

      step-B
        : H.eout e₂ ++ H.ein e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂
      step-B = begin
        H.eout e₂ ++ H.ein e₂ ++ r₂
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₂) r₂) ⟩
        (H.eout e₂ ++ H.ein e₂) ++ r₂
          ↭⟨ PermProp.++⁺ʳ r₂ (PermProp.++-comm (H.eout e₂) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₂) ++ r₂
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₂) r₂ ⟩
        H.ein e₂ ++ H.eout e₂ ++ r₂
          ∎

      step-C
        : H.eout e₂ ++ H.eout e₁ ++ r₁
        Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂
      step-C = Perm.↭-trans step-A step-B

      step-A'
        : H.eout e₁ ++ H.eout e₂ ++ r₂'
        Perm.↭ H.eout e₁ ++ H.ein e₁ ++ r₁'
      step-A' = PermProp.++⁺ˡ (H.eout e₁) p₁'

      step-B'
        : H.eout e₁ ++ H.ein e₁ ++ r₁'
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      step-B' = begin
        H.eout e₁ ++ H.ein e₁ ++ r₁'
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₁) r₁') ⟩
        (H.eout e₁ ++ H.ein e₁) ++ r₁'
          ↭⟨ PermProp.++⁺ʳ r₁' (PermProp.++-comm (H.eout e₁) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₁) ++ r₁'
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₁) r₁' ⟩
        H.ein e₁ ++ H.eout e₁ ++ r₁'
          ∎

      step-C'
        : H.eout e₁ ++ H.eout e₂ ++ r₂'
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      step-C' = Perm.↭-trans step-A' step-B'

      mult-r₁-r₂'
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
        Perm.↭ H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
      mult-r₁-r₂' =
        PermProp.++⁺ˡ (H.eout e₁) (PermProp.++⁺ˡ (H.eout e₂) r₁-r₂')

      inner-lhs
        : H.eout e₁ ++ H.ein e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁
      inner-lhs = begin
        H.eout e₁ ++ H.ein e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₁) r₁) ⟩
        (H.eout e₁ ++ H.ein e₁) ++ r₁
          ↭⟨ PermProp.++⁺ʳ r₁ (PermProp.++-comm (H.eout e₁) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₁) ++ r₁
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₁) r₁ ⟩
        H.ein e₁ ++ H.eout e₁ ++ r₁
          ∎

      inner-lhs-2
        : H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
      inner-lhs-2 = begin
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₁) (H.eout e₁ ++ r₁)) ⟩
        (H.eout e₂ ++ H.ein e₁) ++ H.eout e₁ ++ r₁
          ↭⟨ PermProp.++⁺ʳ (H.eout e₁ ++ r₁)
                            (PermProp.++-comm (H.eout e₂) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₂) ++ H.eout e₁ ++ r₁
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₂) (H.eout e₁ ++ r₁) ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
          ∎

      lhs-rearrange
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
      lhs-rearrange = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₁) (H.eout e₂) (H.ein e₁ ++ r₁)) ⟩
        (H.eout e₁ ++ H.eout e₂) ++ H.ein e₁ ++ r₁
          ↭⟨ PermProp.++⁺ʳ (H.ein e₁ ++ r₁)
                            (PermProp.++-comm (H.eout e₁) (H.eout e₂)) ⟩
        (H.eout e₂ ++ H.eout e₁) ++ H.ein e₁ ++ r₁
          ≡⟨ ++-assoc (H.eout e₂) (H.eout e₁) (H.ein e₁ ++ r₁) ⟩
        H.eout e₂ ++ H.eout e₁ ++ H.ein e₁ ++ r₁
          ↭⟨ PermProp.++⁺ˡ (H.eout e₂) inner-lhs ⟩
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
          ↭⟨ inner-lhs-2 ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
          ↭⟨ PermProp.++⁺ˡ (H.ein e₁) step-C ⟩
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
          ∎

      inner-rhs-inner
        : H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂'
      inner-rhs-inner = begin
        H.eout e₂ ++ H.ein e₂ ++ r₂'
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₂) r₂') ⟩
        (H.eout e₂ ++ H.ein e₂) ++ r₂'
          ↭⟨ PermProp.++⁺ʳ r₂' (PermProp.++-comm (H.eout e₂) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₂) ++ r₂'
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₂) r₂' ⟩
        H.ein e₂ ++ H.eout e₂ ++ r₂'
          ∎

      inner-rhs-1
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
      inner-rhs-1 = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ˡ (H.eout e₁) inner-rhs-inner ⟩
        H.eout e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂'
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₂) (H.eout e₂ ++ r₂')) ⟩
        (H.eout e₁ ++ H.ein e₂) ++ H.eout e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ʳ (H.eout e₂ ++ r₂')
                            (PermProp.++-comm (H.eout e₁) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₁) ++ H.eout e₂ ++ r₂'
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₁) (H.eout e₂ ++ r₂') ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
          ∎

      rhs-rearrange
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      rhs-rearrange = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
          ↭⟨ inner-rhs-1 ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ˡ (H.ein e₂) step-C' ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
          ∎

      ein-aligned
        : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      ein-aligned =
        Perm.↭-trans (Perm.↭-sym lhs-rearrange)
        (Perm.↭-trans mult-r₁-r₂' rhs-rearrange)

      ein-comm
        : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
      ein-comm = begin
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
          ≡⟨ sym (++-assoc (H.ein e₁) (H.ein e₂) (H.eout e₂ ++ r₂)) ⟩
        (H.ein e₁ ++ H.ein e₂) ++ H.eout e₂ ++ r₂
          ↭⟨ PermProp.++⁺ʳ (H.eout e₂ ++ r₂) (PermProp.++-comm (H.ein e₁) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.ein e₁) ++ H.eout e₂ ++ r₂
          ≡⟨ ++-assoc (H.ein e₂) (H.ein e₁) (H.eout e₂ ++ r₂) ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
          ∎

      common
        : H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      common = Perm.↭-trans (Perm.↭-sym ein-comm) ein-aligned

      cancelled-1
        : H.ein e₁ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      cancelled-1 = ++-cancelˡ (H.ein e₂) common

      cancelled
        : H.eout e₂ ++ r₂
        Perm.↭ H.eout e₁ ++ r₁'
      cancelled = ++-cancelˡ (H.ein e₁) cancelled-1

  ------------------------------------------------------------------------
  -- The two-edge head bridge.  After an `e ≟ e'` split (`e ≡ e'` ⇒ the two
  -- orders are identical, `Perm.refl`), case-split the four `extract-prefix`
  -- firing outcomes.  ALL are now CONSTRUCTIVE (given `lin`):
  --
  --   * BOTH-SKIP:  `s12 = s = s21`  (`Perm.refl`).
  --   * BOTH-FIRE:  closed by `post-swap-stack-↭` (the genuine multiset
  --     content), after harvesting the four firing perms.
  --   * MIXED (one order fires both edges, the other only one): discharged
  --     via FIRING-STABILITY (`e'-fires-stable` / `e'-skips-stable`), which
  --     under `Linear` + `Incomp` forces the second edge's firing decision
  --     to agree across the step.  Two mixed sub-cases collapse to equal
  --     stacks; the other two are impossible (`⊥-elim`).  No postulate.
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- (FIRING STABILITY) The Linearity+Incomp content that DISCHARGES the
  -- former `two-edge-swap-diverge` postulate.
  --
  -- If `e` fires from `s` (`s ↭ ein e ++ r₁`), `¬ Dep e e'`, and `e ≢ e'`,
  -- then for every vertex CONSUMED by `e'` the count is unchanged between
  -- `s` and the post-`e` stack `eout e ++ r₁`:
  --   * `count v (ein e) ≡ 0`   (Linearity: ein's of distinct edges are
  --     count-disjoint), and
  --   * `count v (eout e) ≡ 0`  (Incomp: `¬ Dep e e'`),
  -- so `count v s ≡ count v (ein e) + count v r₁ ≡ count v r₁
  --                ≡ count v (eout e) + count v r₁ ≡ count v (eout e ++ r₁)`.
  ------------------------------------------------------------------------

  private
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

    -- A vertex is either consumed by `e'` (`0 < count`) or not (`count ≡ 0`).
    count-zero-or-pos : (e' : Fin H.nE) (v : Fin H.nV)
                      → (count v (H.ein e') ≡ 0) ⊎ (0 <ⁿ count v (H.ein e'))
    count-zero-or-pos e' v with count v (H.ein e')
    ... | zero  = inj₁ refl
    ... | suc _ = inj₂ (s≤sⁿ z≤nⁿ)

    -- `count-ein'-pres` lifts a sub-multiset bound on `ein e'` from `s`
    -- to the post-`e` stack and back (the count is equal on the relevant
    -- vertices, trivial on the rest).
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

    --------------------------------------------------------------------
    -- (FIRING STABILITY, final form) given `e` fires from `s` with
    -- residual `r₁`, `e ≢ e'`, and `¬ Dep e e'`, the firing decision of
    -- `e'` is the SAME on `s` and on the post-`e` stack `eout e ++ r₁`.
    --------------------------------------------------------------------

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

    -- If `e'` skips from `s`, it skips from `eout e ++ r₁` too.  Proven by
    -- ruling out the `just` outcome: a successful prefix on the post-`e`
    -- stack would (via the backward count transport) force success on `s`.
    e'-skips-stable
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → extract-prefix (H.ein e') s ≡ nothing
      → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ nothing
    e'-skips-stable {e} {e'} e≢e' ¬dep r₁ s p eqe' =
      go (extract-prefix (H.ein e') (H.eout e ++ r₁)) refl
      where
        nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
        nothing≢just ()
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

  -- Both edges skip in BOTH orders ⇒ both final stacks are `s`.
  two-edge-swap-both-skip
    : ∀ {e e' : Fin H.nE} (s : List (Fin H.nV))
    → extract-prefix (H.ein e ) s ≡ nothing
    → extract-prefix (H.ein e') s ≡ nothing
    → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
      Perm.↭
      proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
  two-edge-swap-both-skip {e} {e'} s eqe eqe' =
    -- step s e skips ⇒ s; then step s e' skips ⇒ s.  Symmetrically for
    -- the swapped order.  Both sides reduce to `s`.
    subst₂ Perm._↭_
      (sym lhs≡s) (sym rhs≡s) Perm.refl
    where
      s-e≡s  : proj₁ (edge-step H s e ) ≡ s
      s-e≡s  = step-stack-skip e s eqe
      s-e'≡s : proj₁ (edge-step H s e') ≡ s
      s-e'≡s = step-stack-skip e' s eqe'
      lhs≡s : proj₁ (edge-step H (proj₁ (edge-step H s e )) e') ≡ s
      lhs≡s = trans (cong (λ x → proj₁ (edge-step H x e')) s-e≡s)
                    (step-stack-skip e' s eqe')
      rhs≡s : proj₁ (edge-step H (proj₁ (edge-step H s e')) e ) ≡ s
      rhs≡s = trans (cong (λ x → proj₁ (edge-step H x e )) s-e'≡s)
                    (step-stack-skip e s eqe)

  -- Both edges fire in BOTH orders ⇒ `post-swap-stack-↭` closes it.
  two-edge-swap-both-fire
    : ∀ {e e' : Fin H.nE} (s r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : s Perm.↭ H.ein e ++ r₁)
        (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (p₂' : s Perm.↭ H.ein e' ++ r₂')
        (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    → extract-prefix (H.ein e ) s ≡ just (r₁ , p₁)
    → extract-prefix (H.ein e') (H.eout e  ++ r₁ ) ≡ just (r₂  , p₂ )
    → extract-prefix (H.ein e') s ≡ just (r₂' , p₂')
    → extract-prefix (H.ein e ) (H.eout e' ++ r₂') ≡ just (r₁' , p₁')
    → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
      Perm.↭
      proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
  two-edge-swap-both-fire {e} {e'} s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'
                          eqe eqe2 eqe' eqe1 =
    subst₂ Perm._↭_ (sym lhs≡) (sym rhs≡)
      (post-swap-stack-↭ e e' s r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁')
    where
      -- LHS: step s e fires ⇒ eout e ++ r₁; step (eout e ++ r₁) e' fires
      -- ⇒ eout e' ++ r₂.
      lhs≡ : proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
           ≡ H.eout e' ++ r₂
      lhs≡ = trans (cong (λ x → proj₁ (edge-step H x e'))
                         (step-stack-fire e s r₁ p₁ eqe))
                   (step-stack-fire e' (H.eout e ++ r₁) r₂ p₂ eqe2)
      -- RHS: step s e' fires ⇒ eout e' ++ r₂'; step (eout e' ++ r₂') e
      -- fires ⇒ eout e ++ r₁'.
      rhs≡ : proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
           ≡ H.eout e ++ r₁'
      rhs≡ = trans (cong (λ x → proj₁ (edge-step H x e ))
                         (step-stack-fire e' s r₂' p₂' eqe'))
                   (step-stack-fire e (H.eout e' ++ r₂') r₁' p₁' eqe1)

  two-edge-swap-stack-↭
    : ∀ {e e' : Fin H.nE} (inc : Incomp e e') (s : List (Fin H.nV))
    → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
      Perm.↭
      proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
  two-edge-swap-stack-↭ {e} {e'} inc s with e ≟ e'
  -- e ≡ e': the two orders are identical compositions, so `Perm.refl`.
  ... | yes refl = Perm.refl
  ... | no  e≢e' =
    -- Decide all four firing outcomes.  Each "divergence" outcome is now
    -- DISCHARGED via firing-stability (Linearity + Incomp): the two
    -- mixed cases reduce to equal stacks, and the two genuinely-divergent
    -- cases are IMPOSSIBLE (a `just`/`nothing` contradiction).
    decide-e (extract-prefix (H.ein e) s) refl
    where
      ¬dep-ee' : ¬ (Dep H e e')
      ¬dep-ee' = proj₁ inc
      ¬dep-e'e : ¬ (Dep H e' e)
      ¬dep-e'e = proj₂ inc

      decide-e
        : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e ++ r))
        → extract-prefix (H.ein e) s ≡ m
        → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
          Perm.↭
          proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
      -- e SKIPS from s.  Decide e' from s.
      decide-e nothing eqe =
        decide-e'-after-eskip (extract-prefix (H.ein e') s) refl
        where
          decide-e'-after-eskip
            : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e' ++ r))
            → extract-prefix (H.ein e') s ≡ m
            → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
              Perm.↭
              proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
          decide-e'-after-eskip nothing eqe' =
            two-edge-swap-both-skip s eqe eqe'         -- both skip
          decide-e'-after-eskip (just (r₂' , p₂')) eqe' =
            -- e skips, e' fires from s.  By firing-stability e skips from
            -- the post-e' stack too, so both orders end at `eout e' ++ r₂'`.
            subst₂ Perm._↭_ (sym lhs≡) (sym rhs≡) Perm.refl
            where
              e-skips-post : extract-prefix (H.ein e) (H.eout e' ++ r₂') ≡ nothing
              e-skips-post =
                e'-skips-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e r₂' s p₂' eqe
              lhs≡ : proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
                   ≡ H.eout e' ++ r₂'
              lhs≡ = trans (cong (λ x → proj₁ (edge-step H x e'))
                                 (step-stack-skip e s eqe))
                           (step-stack-fire e' s r₂' p₂' eqe')
              rhs≡ : proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
                   ≡ H.eout e' ++ r₂'
              rhs≡ = trans (cong (λ x → proj₁ (edge-step H x e ))
                                 (step-stack-fire e' s r₂' p₂' eqe'))
                           (step-stack-skip e (H.eout e' ++ r₂') e-skips-post)
      -- e FIRES from s with residual r₁.
      decide-e (just (r₁ , p₁)) eqe =
        decide-e'-fire (extract-prefix (H.ein e') (H.eout e ++ r₁)) refl
        where
          decide-e'-fire
            : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ]
                            H.eout e ++ r₁ Perm.↭ H.ein e' ++ r))
            → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ m
            → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
              Perm.↭
              proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
          -- e fires, e' SKIPS from the post-e stack.  By firing-stability
          -- e' skips from s too, so both orders end at `eout e ++ r₁`.
          decide-e'-fire nothing eqe2 =
            decide-e'-from-s-skip (extract-prefix (H.ein e') s) refl
            where
              decide-e'-from-s-skip
                : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e' ++ r))
                → extract-prefix (H.ein e') s ≡ m
                → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
                  Perm.↭
                  proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
              decide-e'-from-s-skip nothing eqe'n =
                subst₂ Perm._↭_ (sym lhs≡) (sym rhs≡) Perm.refl
                where
                  lhs≡ : proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
                       ≡ H.eout e ++ r₁
                  lhs≡ = trans (cong (λ x → proj₁ (edge-step H x e'))
                                     (step-stack-fire e s r₁ p₁ eqe))
                               (step-stack-skip e' (H.eout e ++ r₁) eqe2)
                  rhs≡ : proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
                       ≡ H.eout e ++ r₁
                  rhs≡ = trans (cong (λ x → proj₁ (edge-step H x e ))
                                     (step-stack-skip e' s eqe'n))
                               (step-stack-fire e s r₁ p₁ eqe)
              -- e' fires from s but skips post-e — IMPOSSIBLE by stability.
              decide-e'-from-s-skip (just (r₂' , p₂')) eqe'j =
                ⊥-elim (nothing≢just
                  (trans (sym eqe2)
                    (proj₂ (proj₂ (e'-fires-stable e≢e' ¬dep-ee' r₁ s p₁ eqe'j)))))
                where
                  nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
                  nothing≢just ()
          decide-e'-fire (just (r₂ , p₂)) eqe2 =
            decide-e'-from-s (extract-prefix (H.ein e') s) refl
            where
              decide-e'-from-s
                : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ] s Perm.↭ H.ein e' ++ r))
                → extract-prefix (H.ein e') s ≡ m
                → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
                  Perm.↭
                  proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
              -- e' fires post-e but skips from s — IMPOSSIBLE by stability.
              decide-e'-from-s nothing eqe'n =
                ⊥-elim (nothing≢just
                  (trans (sym (e'-skips-stable e≢e' ¬dep-ee' r₁ s p₁ eqe'n)) eqe2))
                where
                  nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
                  nothing≢just ()
              decide-e'-from-s (just (r₂' , p₂')) eqe' =
                decide-e-after-e'
                  (extract-prefix (H.ein e) (H.eout e' ++ r₂')) refl
                where
                  decide-e-after-e'
                    : (m : Maybe (Σ[ r ∈ List (Fin H.nV) ]
                                    H.eout e' ++ r₂' Perm.↭ H.ein e ++ r))
                    → extract-prefix (H.ein e) (H.eout e' ++ r₂') ≡ m
                    → proj₁ (edge-step H (proj₁ (edge-step H s e )) e')
                      Perm.↭
                      proj₁ (edge-step H (proj₁ (edge-step H s e')) e )
                  decide-e-after-e' (just (r₁' , p₁')) eqe1 =   -- both fire
                    two-edge-swap-both-fire s r₁ r₂ r₁' r₂'
                      p₁ p₂ p₂' p₁' eqe eqe2 eqe' eqe1
                  -- e' fires from s, e fires post-e — yet e SKIPS post-e':
                  -- IMPOSSIBLE by stability (e fires from s, so it fires
                  -- from the post-e' stack too).
                  decide-e-after-e' nothing eqe1 =
                    ⊥-elim (nothing≢just
                      (trans (sym eqe1)
                        (proj₂ (proj₂
                          (e'-fires-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e
                            r₂' s p₂' eqe)))))
                    where
                      nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
                      nothing≢just ()

  ------------------------------------------------------------------------
  -- `front-swap-stack-↭` — CONSTRUCTIVELY reduced to the two-edge head
  -- bridge by threading the shared tail `qs` through `pe-stack-resp-↭`.
  ------------------------------------------------------------------------

  front-swap-stack-↭
    : ∀ (qs : PH.Order) {e e' : Fin H.nE}
        (inc : Incomp e e') (s : List (Fin H.nV))
    → pe-stack (e ∷ e' ∷ qs) s  Perm.↭  pe-stack (e' ∷ e ∷ qs) s
  front-swap-stack-↭ qs {e} {e'} inc s =
    pe-stack-resp-↭ qs (two-edge-swap-stack-↭ inc s)

  ------------------------------------------------------------------------
  -- (general swap) `finalStack`-↭ for a swap after an arbitrary prefix.
  --
  -- Reduce to the front swap via `++-stack`, then apply
  -- `front-swap-stack-↭` at the shared post-prefix stack.
  ------------------------------------------------------------------------

  swap-stack-↭
    : ∀ (ps qs : PH.Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → pe-stack (ps ++ e ∷ e' ∷ qs) H.dom
      Perm.↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom
  swap-stack-↭ ps qs {e} {e'} inc =
    subst (Perm._↭ pe-stack (ps ++ e' ∷ e ∷ qs) H.dom)
          (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
      (subst (pe-stack (e ∷ e' ∷ qs) (pe-stack ps H.dom) Perm.↭_)
             (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
        (front-swap-stack-↭ qs inc (pe-stack ps H.dom)))

  ------------------------------------------------------------------------
  -- (3) `swap-validity`: transport `Valid` along `swap-stack-↭`.
  --
  --   Valid o = finalStack o Perm.↭ cod
  --
  -- so `Valid o₂ = ↭-trans (↭-sym (finalStack o₁ ↭ finalStack o₂))
  --                        (Valid o₁)`.
  ------------------------------------------------------------------------

  swap-validity : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂ → PH.Valid o₁ → PH.Valid o₂
  swap-validity (swap-step ps qs inc) p₁ =
    Perm.↭-trans (Perm.↭-sym (swap-stack-↭ ps qs inc)) p₁
