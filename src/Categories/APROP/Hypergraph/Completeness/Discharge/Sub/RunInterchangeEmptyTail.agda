{-# OPTIONS --safe --without-K #-}

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
-- `EdgeStepRelation` view (`EdgeStepR`, `edge-step-graph`) at the TERM
-- level.  Matching the `EdgeStepR` constructors refines the (otherwise
-- stuck) `edge-step` redexes to `id` / `fire-term` WITHOUT abstracting them
-- in a dependent position, so no green-slime arises.
--
-- The `RunInterchange` record's `reshuffle` and `run-eq` are built TOGETHER
-- per case, so NO global Kelly-reconciliation of two reshuffle witnesses is
-- needed — in particular no `Unique (pe-stack …)` hypothesis.
--
--   1. BOTH-SKIP / 2. e FIRES,e' SKIPS / 3. e SKIPS,e' FIRES — `reshuffle =
--      refl`; `run-eq` collapses via `idˡ`/`idʳ`.
--   4. BOTH-FIRE — THE genuine content: the two framed boxes on DISJOINT
--      blocks commute via σ.  Isolated as `fire-mid-interchange`.
--
-- The impossible mixed firing cases are ruled out by FIRING-STABILITY
-- (`Linear` + `Incomp`).  The stability lemmas (`e'-fires-stable` /
-- `e'-skips-stable`) live in a `private` block of `SwapValidity.PerHG`, so
-- they are re-derived here (postulate-free).
--
-- ## The single residual — `fire-mid-interchange` (M)
--
-- BOTH-FIRE reduces to the commutation of two framed boxes on DISJOINT wire
-- blocks.  The K-free kernel `box-interchange f g : g ⊗₁ f ≈Term σ ∘ ((f ⊗₁
-- g) ∘ σ)` is proven in `SwapStep.FrontSwap`; transporting it through the
-- `fire-mid` bracketing and the four locating permutes is the Mac-Lane
-- chase, isolated as `fire-mid-interchange` (the same posture as
-- `Sub/SwapAtomAligned.swap-mac-lane-residual`).  Discharged by
-- `Sub/FireMidInterchange.agda`.
--------------------------------------------------------------------------------

open import Categories.APROP

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeEmptyTail
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

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
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchange sig _≟X_ as FMI
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
-- Generic `count` / `extract-prefix` combinatorics (H-agnostic).
-- The core lemmas live in the shared `CountCombinatorics` leaf; the few
-- specialised helpers below are kept local.
------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.CountCombinatorics sig
  using (↭⇒count; count-pos→∈; count-≤→extract-prefix)

private
  variable
    n : ℕ

  extract-prefix-just→count-≤
    : (ks xs rest : List (Fin n)) (p : xs Perm.↭ ks ++ rest)
    → ∀ v → count v ks ≤ⁿ count v xs
  extract-prefix-just→count-≤ ks xs rest p v =
    Nat.≤-trans (Nat.m≤m+n (count v ks) (count v rest))
                (Nat.≤-reflexive (trans (sym (count-++ v ks rest))
                                        (sym (↭⇒count p v))))

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
  -- `fire-mid-interchange` needs `Unique` witnesses to discharge its
  -- eval-coincidence residuals via `eval-rigid`.  These are instances of
  -- "every stack reachable by `process-edges … H.dom` is `Unique`" — the
  -- reservoir invariant of the decoder run, derived from the swap-site
  -- `↭ range` provenance + the `Linear` bound (NO false-as-stated `∀ o`
  -- reservoir postulate is used).
  reached-Unique-from
    : ∀ (o : Order) → SUR.Reservoir≤1 H o H.dom → Unique (pe-stack o H.dom)
  reached-Unique-from o inv =
    SUR.Reservoir≤1⇒Unique H [] (pe-stack o H.dom)
      (SUR.reservoir-split H o [] H.dom
        (subst (λ z → SUR.Reservoir≤1 H z H.dom) (sym (++-identityʳ o)) inv))

  ----------------------------------------------------------------------
  -- FIRING STABILITY (Linear + Incomp), re-derived from the
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
  -- BOTH-FIRE: the two framed boxes on DISJOINT blocks commute via σ
  -- (`box-interchange`), transported through the `fire-mid` bracketing and
  -- the locating permutes, with the reshuffle bundled existentially.  This
  -- is the smallest true statement closing BOTH-FIRE: it mentions NEITHER
  -- `cod` NOR the final permute, only the four unpacked fire witnesses.
  -- TRUE because the two `Incomp` edges have DISJOINT wire blocks.
  --
  -- Discharged by `Sub/FireMidInterchange.agda`.  Carries the `Unique`
  -- witnesses its eval-coincidence residuals need (supplied at the call site
  -- from the `Linear`-backed reservoir invariant).
  ----------------------------------------------------------------------
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
  --
  -- The four-way firing split is performed by `build`, whose four
  -- `EdgeStepR` arguments carry FRESH index variables; matching their
  -- `skipR`/`fireR` constructors refines those variables with NO unification
  -- against the stuck `edge-step` redex (dodging the green-slime
  -- with-abstraction wall).  At the call site the fresh indices specialise
  -- back to the `pe-stack`/`pe-term` forms.
  ----------------------------------------------------------------------

  -- `run-interchange₀` takes the swap-order reservoir; from it the `Unique`
  -- witnesses `fire-mid-interchange` needs are derived (prefix drops + the
  -- reservoir itself).
  run-interchange₀
    : ∀ (ps : Order) {e e' : Fin H.nE} (inc : Incomp e e')
    → SUR.Reservoir≤1 H (ps ++ e' ∷ e ∷ []) H.dom
    → RunInterchange ps [] inc
  run-interchange₀ ps {e} {e'} inc res with e ≟ e'
  -- e ≡ e': the two orders are the same composition.
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
      -- dropping the suffix `e ∷ []` from the full swap order.
      res-e' : SUR.Reservoir≤1 H (ps ++ e' ∷ []) H.dom
      res-e' =
        SUR.reservoir-prefix H (ps ++ e' ∷ []) (e ∷ []) H.dom
          (subst (λ z → SUR.Reservoir≤1 H z H.dom)
                 (sym (++-assoc ps (e' ∷ []) (e ∷ [])))
                 res)

      -- Reservoir for the e-first INTERMEDIATE order `ps ++ e ∷ []`.  Swap the
      -- last two edges (`reservoir-resp-↭`), then drop `e' ∷ []` as a suffix.
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
      -- witnesses of the `e ∷ e'` run; `ue`/`ue'` of the `e' ∷ e` run.  The
      -- returned `Σ` is `run₂ ≈Term permute r ∘ run₁` with the trailing `id`s
      -- in place, over the abstract stacks/terms.  The three `Unique`
      -- arguments are used ONLY in the both-fire branch, supplying
      -- `fire-mid-interchange`'s `us-mid`/`us-cod` witnesses.
      --------------------------------------------------------------
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
      -- BOTH-SKIP.
      build (skipR eqe) (skipR eqe') (skipR _) (skipR _) _ _ _ =
        Perm.refl , ≈-Term-sym idˡ
      -- impossible: `we'` says e' skips sp, `ue` says e' fires sp.
      build (skipR eqe) (skipR eqe') (fireR ur₂' up₂' ueqe') _ _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe') ueqe'))
      -- impossible: `eqe` says e skips sp, `ueqe1` says e fires sp.
      build (skipR eqe) (skipR eqe') (skipR ueqe') (fireR ur₁ up₁ ueqe1) _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe) ueqe1))
      -- impossible: e' fires sp here, skips there.
      build (skipR eqe) (fireR r₂' p₂' eqe') (skipR eqe'-bad) _ _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe'-bad) eqe'))
      -- impossible: e skips sp, so by stability e skips the post-e' stack.
      build (skipR eqe) (fireR r₂' p₂' eqe') (fireR ur₂' up₂' ueqe')
            (fireR r₁' p₁' eqe1) _ _ _ =
        ⊥-elim (nothing≢just
          (trans (sym (e'-skips-stable (λ eq → e≢e' (sym eq)) ¬dep-e'e
                         ur₂' sp up₂' eqe)) eqe1))
      -- single layer `fire-term e' sp`, once (ur₂',up₂') ≡ (r₂',p₂').
      build (skipR eqe) (fireR r₂' p₂' eqe') (fireR ur₂' up₂' ueqe')
            (skipR eqe1) _ _ _ =
        pin (just-inj (trans (sym ueqe') eqe'))
        where
          pin : (ur₂' , up₂') ≡ (r₂' , p₂') → _
          pin refl =
            Perm.refl ,
            ≈-Term-trans
              (∘-resp-≈ idˡ ≈-Term-refl)
              (≈-Term-trans idˡ
                (≈-Term-sym
                  (≈-Term-trans idˡ
                    (≈-Term-trans (∘-resp-≈ idˡ ≈-Term-refl) idʳ))))

      ------------------------------------------------------------
      -- (2) e FIRES sp (residual r₁).
      ------------------------------------------------------------
      -- impossible by stability: e' fires sp ⇒ e' fires post-e.
      build (fireR r₁ p₁ eqe) (skipR eqe2) (fireR ur₂' up₂' ueqe') _ _ _ _ =
        ⊥-elim (nothing≢just
          (trans (sym eqe2)
            (proj₂ (proj₂ (e'-fires-stable e≢e' ¬dep-ee' r₁ sp p₁ ueqe')))))
      -- impossible: e skips sp in the e'-run, contradicts `eqe`.
      build (fireR r₁ p₁ eqe) (skipR eqe2) (skipR eqe'n) (skipR eqe-bad) _ _ _ =
        ⊥-elim (nothing≢just (trans (sym eqe-bad) eqe))
      -- single layer `fire-term e sp`, once (ur₁,up₁) ≡ (r₁,p₁).
      build (fireR r₁ p₁ eqe) (skipR eqe2) (skipR eqe'n)
            (fireR ur₁ up₁ ueqe) _ _ _ =
        pin (just-inj (trans (sym ueqe) eqe))
        where
          pin : (ur₁ , up₁) ≡ (r₁ , p₁) → _
          pin refl =
            Perm.refl ,
            ≈-Term-trans
              (∘-resp-≈ idˡ ≈-Term-refl)
              (≈-Term-trans idʳ
                (≈-Term-sym
                  (≈-Term-trans idˡ
                    (≈-Term-trans (∘-resp-≈ idˡ ≈-Term-refl) idˡ))))
      -- impossible by stability: e' fires post-e ⇒ e' fires sp.
      build (fireR r₁ p₁ eqe) (fireR r₂ p₂ eqe2) (skipR eqe'n) _ _ _ _ =
        ⊥-elim (nothing≢just
          (trans (sym (e'-skips-stable e≢e' ¬dep-ee' r₁ sp p₁ eqe'n)) eqe2))
      -- impossible by stability: e fires sp ⇒ e fires post-e'.
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
        ≈-Term-trans
          (∘-resp-≈ idˡ ≈-Term-refl)
          (≈-Term-trans box-eq
            (∘-resp-≈ ≈-Term-refl
              (∘-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl)))
        where
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

      -- Assemble the record by feeding the four `edge-step-graph` witnesses;
      -- their indices specialise `build`'s fresh variables to the
      -- `pe-stack`/`pe-term` forms.
      Σr : Σ[ r ∈ pe-stack (e ∷ e' ∷ []) sp Perm.↭ pe-stack (e' ∷ e ∷ []) sp ]
             pe-term (e' ∷ e ∷ []) sp
             ≈Term permute-via-vlab H.vlab r ∘ pe-term (e ∷ e' ∷ []) sp
      Σr = build (edge-step-graph H sp e)
                 (edge-step-graph H (proj₁ (edge-step H sp e)) e')
                 (edge-step-graph H sp e')
                 (edge-step-graph H (proj₁ (edge-step H sp e')) e)
                 -- `Unique s1` (e-first intermediate `ps ++ e ∷ []`).
                 (subst Unique (++-stack ps (e ∷ []) H.dom)
                        (reached-Unique-from (ps ++ e ∷ []) res-e))
                 -- `Unique u1` (e'-first intermediate `ps ++ e' ∷ []`).
                 (subst Unique (++-stack ps (e' ∷ []) H.dom)
                        (reached-Unique-from (ps ++ e' ∷ []) res-e'))
                 -- `Unique u2` (the combined order `ps ++ e' ∷ e ∷ []`).
                 (subst Unique (++-stack ps (e' ∷ e ∷ []) H.dom)
                        (reached-Unique-from (ps ++ e' ∷ e ∷ []) res))
