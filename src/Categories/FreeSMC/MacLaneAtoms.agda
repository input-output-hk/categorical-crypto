{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- `SMCMacLaneAtoms` — VALIDATION build.
--
-- The three σ-fragment atoms are CONSTRUCTIVE DEFINITIONS, derived from
-- residual `field`s.  A clean typecheck validates that this lemma set
-- SUFFICES to discharge the atoms.
--
-- Already discharged outside this record (NOT fields):
--   * `Steps.fire-clean`        — fire = splitJoin ∘ permute (definitional).
--   * `StackPerm.swap-stack-↭`  — atom (1)'s stack-permutation Σ-component.
--   * `Hypergraph.FinalStackPerm` — its carrier-generic core.
--
-- Residual fields (the remaining proof obligations):
--   * `permute-faithfulness`    — symmetric-group coherence on `permute`
--                                 (the genuine Kelly/XSL residual); target
--                                 for discharging the `≈Term` term-fields.
--   * `swap-term`               — atom (1)'s `≈Term`, stack-witness fixed
--                                 to `swap-stack-↭`.  Subst₂-free (via
--                                 `splitJoin`/`fire-clean`).  To be closed
--                                 by `BraidBlock.braid-natural` + faithfulness.
--   * `swap-rest-stack` / `swap-rest-term` — atom (2)'s two halves.
--   * `bridge-term`             — atom (4) (a single `≈Term`, no Σ).
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.MacLaneAtoms
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d
open import Categories.FreeSMC.Steps d
import Categories.FreeSMC.StackPerm d as SP
import Categories.FreeSMC.ProcessFinal d as PF
import Categories.FreeSMC.PermuteInverse d as PI
import Categories.PermuteCoherence.Faithfulness d as Faith

open import Categories.Category using (Category)
private
  module FM = Category FreeMonoidal
open FM.HomReasoning

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst₂)

record SMCMacLaneAtoms : Set where
  field
    -- The genuine residual: symmetric-group coherence on permute terms.
    permute-faithfulness : Faith.FaithfulnessResidual

    --------------------------------------------------------------------
    -- atom (2) reduces to the GENERAL "process-steps respects an
    -- edge-permutation" lemma.  The stack half is now DISCHARGED
    -- (`ProcessFinal.process-steps-final-↭`, via the net-multiset
    -- invariant); only the `≈Term` half remains a residual, and
    -- `swap-rest-stack` / `swap-rest-term` are thin instances at the
    -- swap-with-tail edge-permutation `Perm.swap e₁ e₂ rest-↭`.

    process-steps-↭-term
      : ∀ (n : ℕ) (vlab : Fin n → X)
          (es es' : Steps n vlab) (s : List (Fin n))
          (es-↭ : es Perm.↭ es')
          (af : AllFire n vlab es s) (af' : AllFire n vlab es' s)
      → proj₂ (process-steps n vlab es s af)
        ≈Term
        permute-via-vlab vlab
          (Perm.↭-sym (PF.process-steps-final-↭ n vlab es es' s es-↭ af af'))
          ∘ proj₂ (process-steps n vlab es' s af')

    --------------------------------------------------------------------
    -- atom (1)'s residual, with the INPUT permute `pvv p1` factored OUT
    -- (the domain is the inputs-arranged stack `a₁ ++ r₁`, and the input
    -- permute is the composite `trans (↭-sym p1) p2`).  This is the bare
    -- two-generator interchange — the genuine 2-generator σ-coherence —
    -- strictly cleaner than `swap-core` (no leading `pvv p1`).  `swap-core`
    -- is DERIVED from it below by cancelling `pvv p1` via the proved
    -- `PermuteInverse.pvv-inverse-left`.
    swap-gens
      : ∀ (n : ℕ) (vlab : Fin n → X)
          (a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ : List (Fin n))
          (f : HomTerm (unflatten (map vlab a₁)) (unflatten (map vlab b₁)))
          (g : HomTerm (unflatten (map vlab a₂)) (unflatten (map vlab b₂)))
          (p12 : b₁ ++ r₁ Perm.↭ a₂ ++ r₁₂)
          (qin : (a₁ ++ r₁) Perm.↭ (a₂ ++ r₂))
          (p21 : b₂ ++ r₂ Perm.↭ a₁ ++ r₂₁)
          (stk : b₂ ++ r₁₂ Perm.↭ b₁ ++ r₂₁)
      → splitJoin n vlab {a₂} {b₂} g r₁₂ ∘ permute-via-vlab vlab p12
          ∘ splitJoin n vlab {a₁} {b₁} f r₁
        ≈Term
        permute-via-vlab vlab (Perm.↭-sym stk)
          ∘ (splitJoin n vlab {a₁} {b₁} f r₂₁ ∘ permute-via-vlab vlab p21
              ∘ splitJoin n vlab {a₂} {b₂} g r₂ ∘ permute-via-vlab vlab qin)

    --------------------------------------------------------------------
    -- atom (4) factors through f's natural processing `proj₂ ps-f` into:
    --
    --   * `bridge-cross`   — f's vs g's natural processing across the two
    --                        vertex spaces, mediated by `dom-eq` + `stack-↭`.
    --                        The IRREDUCIBLE iso-bridge content (no clean
    --                        vertex bijection exists — cf. the
    --                        `BoundaryRespectsIso` pruning blocker), so the
    --                        label-level permutes are taken as given.
    --
    --   * `bridge-reorder` — f-natural vs f-ψF-reordered, an edge
    --                        permutation in a SINGLE vertex space.  Same
    --                        family as `process-steps-↭-term` (the Maybe
    --                        variant).

    bridge-cross
      : ∀ (n-f n-g : ℕ)
          (vlab-f : Fin n-f → X) (vlab-g : Fin n-g → X)
          (steps-f : Steps n-f vlab-f) (steps-g : Steps n-g vlab-g)
          (dom-f : List (Fin n-f)) (dom-g : List (Fin n-g))
          (dom-eq : map vlab-g dom-g ≡ map vlab-f dom-f)
          (stack-↭ :
            map vlab-f (proj₁ (process-steps-maybe n-f vlab-f steps-f dom-f))
            Perm.↭
            map vlab-g (proj₁ (process-steps-maybe n-g vlab-g steps-g dom-g)))
      → proj₂ (process-steps-maybe n-f vlab-f steps-f dom-f)
        ≈Term
        permute (Perm.↭-sym stack-↭)
          ∘ subst₂ HomTerm (cong unflatten dom-eq) refl
              (proj₂ (process-steps-maybe n-g vlab-g steps-g dom-g))

    bridge-reorder
      : ∀ (n-f : ℕ) (vlab-f : Fin n-f → X)
          (steps-f steps-f-reordered : Steps n-f vlab-f)
          (dom-f : List (Fin n-f))
          (b-stack-↭ :
            proj₁ (process-steps-maybe n-f vlab-f steps-f           dom-f)
            Perm.↭
            proj₁ (process-steps-maybe n-f vlab-f steps-f-reordered dom-f))
      → proj₂ (process-steps-maybe n-f vlab-f steps-f dom-f)
        ≈Term
        permute-via-vlab vlab-f (Perm.↭-sym b-stack-↭)
          ∘ proj₂ (process-steps-maybe n-f vlab-f steps-f-reordered dom-f)

  --------------------------------------------------------------------
  -- atom (1)'s core, DERIVED from `swap-gens` by factoring the input
  -- permute `pvv p1` and cancelling it via `PermuteInverse.pvv-inverse-left`
  -- (the input perm of `swap-gens` is `trans (↭-sym p1) p2`, and
  --  `pvv (trans (↭-sym p1) p2) ∘ pvv p1 = pvv p2 ∘ (pvv (↭-sym p1) ∘ pvv p1)
  --   ≈ pvv p2 ∘ id ≈ pvv p2`).
  swap-core
    : ∀ (n : ℕ) (vlab : Fin n → X)
        (a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ s : List (Fin n))
        (f : HomTerm (unflatten (map vlab a₁)) (unflatten (map vlab b₁)))
        (g : HomTerm (unflatten (map vlab a₂)) (unflatten (map vlab b₂)))
        (p1  : s Perm.↭ a₁ ++ r₁)  (p12 : b₁ ++ r₁ Perm.↭ a₂ ++ r₁₂)
        (p2  : s Perm.↭ a₂ ++ r₂)  (p21 : b₂ ++ r₂ Perm.↭ a₁ ++ r₂₁)
        (stk : b₂ ++ r₁₂ Perm.↭ b₁ ++ r₂₁)
    → splitJoin n vlab {a₂} {b₂} g r₁₂ ∘ permute-via-vlab vlab p12
        ∘ splitJoin n vlab {a₁} {b₁} f r₁ ∘ permute-via-vlab vlab p1
      ≈Term
      permute-via-vlab vlab (Perm.↭-sym stk)
        ∘ (splitJoin n vlab {a₁} {b₁} f r₂₁ ∘ permute-via-vlab vlab p21
            ∘ splitJoin n vlab {a₂} {b₂} g r₂ ∘ permute-via-vlab vlab p2)
  swap-core n vlab a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ s f g p1 p12 p2 p21 stk =
    begin
      SJg r₁₂ ∘ pv p12 ∘ SJf r₁ ∘ pv p1
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      SJg r₁₂ ∘ ((pv p12 ∘ SJf r₁) ∘ pv p1)
        ≈⟨ ≈-Term-sym assoc ⟩
      (SJg r₁₂ ∘ (pv p12 ∘ SJf r₁)) ∘ pv p1
        ≈⟨ ∘-resp-≈ gens ≈-Term-refl ⟩
      (pv (Perm.↭-sym stk)
         ∘ (SJf r₂₁ ∘ pv p21 ∘ SJg r₂ ∘ pv (Perm.trans (Perm.↭-sym p1) p2)))
        ∘ pv p1
        ≈⟨ assoc ⟩
      pv (Perm.↭-sym stk)
        ∘ ((SJf r₂₁ ∘ pv p21 ∘ SJg r₂ ∘ pv (Perm.trans (Perm.↭-sym p1) p2)) ∘ pv p1)
        ≈⟨ ∘-resp-≈ ≈-Term-refl tail-eq ⟩
      pv (Perm.↭-sym stk)
        ∘ (SJf r₂₁ ∘ pv p21 ∘ SJg r₂ ∘ pv p2)
    ∎
    where
      SJf : ∀ (rest : List (Fin n))
          → HomTerm (unflatten (map vlab (a₁ ++ rest))) (unflatten (map vlab (b₁ ++ rest)))
      SJf rest = splitJoin n vlab {a₁} {b₁} f rest
      SJg : ∀ (rest : List (Fin n))
          → HomTerm (unflatten (map vlab (a₂ ++ rest))) (unflatten (map vlab (b₂ ++ rest)))
      SJg rest = splitJoin n vlab {a₂} {b₂} g rest
      pv : ∀ {xs ys : List (Fin n)} → xs Perm.↭ ys
         → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
      pv p = permute-via-vlab vlab p
      gens = swap-gens n vlab a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ f g
               p12 (Perm.trans (Perm.↭-sym p1) p2) p21 stk
      -- `pv (trans (↭-sym p1) p2) ∘ pv p1 ≈ pv p2` (the input-perm cancel);
      -- `pv (trans (↭-sym p1) p2) = pv p2 ∘ pv (↭-sym p1)` holds definitionally.
      cancel
        : pv (Perm.trans (Perm.↭-sym p1) p2) ∘ pv p1 ≈Term pv p2
      cancel =
        ≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl (PI.pvv-inverse-left vlab p1)) idʳ)
      tail-eq
        : (SJf r₂₁ ∘ pv p21 ∘ SJg r₂ ∘ pv (Perm.trans (Perm.↭-sym p1) p2)) ∘ pv p1
          ≈Term
          SJf r₂₁ ∘ pv p21 ∘ SJg r₂ ∘ pv p2
      tail-eq =
        ≈-Term-trans assoc
          (∘-resp-≈ ≈-Term-refl
            (≈-Term-trans assoc
              (∘-resp-≈ ≈-Term-refl
                (≈-Term-trans assoc
                  (∘-resp-≈ ≈-Term-refl cancel)))))

  --------------------------------------------------------------------
  -- atom (1)'s `≈Term` half (stack witness = `swap-stack-↭`, done).
  swap-term
    : ∀ (n : ℕ) (vlab : Fin n → X)
        (e₁ e₂ : Step n vlab) (s : List (Fin n))
        (indep : IndependentSwap n vlab e₁ e₂ s)
    → proj₂ (process-steps n vlab (e₁ ∷ e₂ ∷ []) s (proj₁ indep))
      ≈Term
      permute-via-vlab vlab (Perm.↭-sym (SP.swap-stack-↭ n vlab e₁ e₂ s indep))
        ∘ proj₂ (process-steps n vlab (e₂ ∷ e₁ ∷ []) s (proj₂ indep))
  swap-term n vlab (a₁ , b₁ , f) (a₂ , b₂ , g) s
    indep@((r₁ , p1 , (r₁₂ , p12 , _)) , (r₂ , p2 , (r₂₁ , p21 , _))) =
    ≈-Term-trans massage-lhs (≈-Term-trans core massage-rhs)
    where
      stk = SP.swap-stack-↭ n vlab (a₁ , b₁ , f) (a₂ , b₂ , g) s indep

      SJf₁ = splitJoin n vlab {a₁} {b₁} f r₁
      SJg₁ = splitJoin n vlab {a₂} {b₂} g r₁₂
      SJg₂ = splitJoin n vlab {a₂} {b₂} g r₂
      SJf₂ = splitJoin n vlab {a₁} {b₁} f r₂₁

      -- LHS of the goal (process-steps, with the spurious `id ∘`) ≈ core LHS.
      massage-lhs
        : (id ∘ (SJg₁ ∘ permute-via-vlab vlab p12)) ∘ (SJf₁ ∘ permute-via-vlab vlab p1)
          ≈Term
          SJg₁ ∘ permute-via-vlab vlab p12 ∘ SJf₁ ∘ permute-via-vlab vlab p1
      massage-lhs =
        ≈-Term-trans (∘-resp-≈ idˡ ≈-Term-refl) assoc

      core
        : SJg₁ ∘ permute-via-vlab vlab p12 ∘ SJf₁ ∘ permute-via-vlab vlab p1
          ≈Term
          permute-via-vlab vlab (Perm.↭-sym stk)
            ∘ (SJf₂ ∘ permute-via-vlab vlab p21 ∘ SJg₂ ∘ permute-via-vlab vlab p2)
      core = swap-core n vlab a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ s f g p1 p12 p2 p21 stk

      -- core RHS ≈ RHS of the goal (re-introduce the `id ∘`).
      massage-rhs
        : permute-via-vlab vlab (Perm.↭-sym stk)
            ∘ (SJf₂ ∘ permute-via-vlab vlab p21 ∘ SJg₂ ∘ permute-via-vlab vlab p2)
          ≈Term
          permute-via-vlab vlab (Perm.↭-sym stk)
            ∘ ((id ∘ (SJf₂ ∘ permute-via-vlab vlab p21)) ∘ (SJg₂ ∘ permute-via-vlab vlab p2))
      massage-rhs =
        ∘-resp-≈ ≈-Term-refl
          (≈-Term-sym (≈-Term-trans (∘-resp-≈ idˡ ≈-Term-refl) assoc))

  --------------------------------------------------------------------
  -- (1) Mac Lane / Kelly atom on two adjacent independent steps.
  -- DERIVED: stack witness (done) paired with the `swap-term` field.

  swap-atom-aligned
    : ∀ (n : ℕ) (vlab : Fin n → X)
        (e₁ e₂ : Step n vlab) (s : List (Fin n))
        (indep : IndependentSwap n vlab e₁ e₂ s)
    → ProcessEdges↭Goal n vlab
        (e₁ ∷ e₂ ∷ []) (e₂ ∷ e₁ ∷ [])
        s (proj₁ indep) (proj₂ indep)
  swap-atom-aligned n vlab e₁ e₂ s indep =
    SP.swap-stack-↭ n vlab e₁ e₂ s indep
    , swap-term n vlab e₁ e₂ s indep

  --------------------------------------------------------------------
  -- atom (2)'s two halves, DERIVED as instances of the general lemma
  -- at the swap-with-tail edge-permutation `Perm.swap e₁ e₂ rest-↭`.

  swap-rest-stack
    : ∀ (n : ℕ) (vlab : Fin n → X)
        (e₁ e₂ : Step n vlab) (xs ys : Steps n vlab) (s : List (Fin n))
        (rest-↭ : xs Perm.↭ ys)
        (af₁ : AllFire n vlab (e₁ ∷ e₂ ∷ xs) s)
        (af₂ : AllFire n vlab (e₂ ∷ e₁ ∷ ys) s)
    → proj₁ (process-steps n vlab (e₁ ∷ e₂ ∷ xs) s af₁)
      Perm.↭
      proj₁ (process-steps n vlab (e₂ ∷ e₁ ∷ ys) s af₂)
  swap-rest-stack n vlab e₁ e₂ xs ys s rest-↭ af₁ af₂ =
    PF.process-steps-final-↭ n vlab (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys) s
      (Perm.swap e₁ e₂ rest-↭) af₁ af₂

  swap-rest-term
    : ∀ (n : ℕ) (vlab : Fin n → X)
        (e₁ e₂ : Step n vlab) (xs ys : Steps n vlab) (s : List (Fin n))
        (rest-↭ : xs Perm.↭ ys)
        (af₁ : AllFire n vlab (e₁ ∷ e₂ ∷ xs) s)
        (af₂ : AllFire n vlab (e₂ ∷ e₁ ∷ ys) s)
    → proj₂ (process-steps n vlab (e₁ ∷ e₂ ∷ xs) s af₁)
      ≈Term
      permute-via-vlab vlab
        (Perm.↭-sym (swap-rest-stack n vlab e₁ e₂ xs ys s rest-↭ af₁ af₂))
        ∘ proj₂ (process-steps n vlab (e₂ ∷ e₁ ∷ ys) s af₂)
  swap-rest-term n vlab e₁ e₂ xs ys s rest-↭ af₁ af₂ =
    process-steps-↭-term n vlab (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys) s
      (Perm.swap e₁ e₂ rest-↭) af₁ af₂

  --------------------------------------------------------------------
  -- (2) Single swap with a non-trivial rest list of steps.
  -- DERIVED: the two residual halves.

  swap-with-rest-aligned
    : ∀ (n : ℕ) (vlab : Fin n → X)
        (e₁ e₂ : Step n vlab) (xs ys : Steps n vlab) (s : List (Fin n))
        (rest-↭ : xs Perm.↭ ys)
        (af₁ : AllFire n vlab (e₁ ∷ e₂ ∷ xs) s)
        (af₂ : AllFire n vlab (e₂ ∷ e₁ ∷ ys) s)
    → ProcessEdges↭Goal n vlab
        (e₁ ∷ e₂ ∷ xs) (e₂ ∷ e₁ ∷ ys)
        s af₁ af₂
  swap-with-rest-aligned n vlab e₁ e₂ xs ys s rest-↭ af₁ af₂ =
    swap-rest-stack n vlab e₁ e₂ xs ys s rest-↭ af₁ af₂
    , swap-rest-term n vlab e₁ e₂ xs ys s rest-↭ af₁ af₂

  --------------------------------------------------------------------
  -- atom (4)'s `≈Term`, DERIVED by routing through `proj₂ ps-f`:
  --   (sym bridge-cross) : LHS ≈ proj₂ ps-f
  --   bridge-reorder     : proj₂ ps-f ≈ RHS
  bridge-term
    : ∀ (n-f n-g : ℕ)
        (vlab-f : Fin n-f → X) (vlab-g : Fin n-g → X)
        (steps-f steps-f-reordered : Steps n-f vlab-f)
        (steps-g : Steps n-g vlab-g)
        (dom-f : List (Fin n-f)) (dom-g : List (Fin n-g))
        (dom-eq : map vlab-g dom-g ≡ map vlab-f dom-f)
        (stack-↭ :
          map vlab-f (proj₁ (process-steps-maybe n-f vlab-f steps-f dom-f))
          Perm.↭
          map vlab-g (proj₁ (process-steps-maybe n-g vlab-g steps-g dom-g)))
        (b-stack-↭ :
          proj₁ (process-steps-maybe n-f vlab-f steps-f           dom-f)
          Perm.↭
          proj₁ (process-steps-maybe n-f vlab-f steps-f-reordered dom-f))
    → permute (Perm.↭-sym stack-↭)
      ∘ subst₂ HomTerm (cong unflatten dom-eq) refl
          (proj₂ (process-steps-maybe n-g vlab-g steps-g dom-g))
      ≈Term
      permute-via-vlab vlab-f (Perm.↭-sym b-stack-↭)
        ∘ proj₂ (process-steps-maybe n-f vlab-f steps-f-reordered dom-f)
  bridge-term n-f n-g vlab-f vlab-g steps-f steps-f-reordered steps-g
              dom-f dom-g dom-eq stack-↭ b-stack-↭ =
    ≈-Term-trans
      (≈-Term-sym
        (bridge-cross n-f n-g vlab-f vlab-g steps-f steps-g
          dom-f dom-g dom-eq stack-↭))
      (bridge-reorder n-f vlab-f steps-f steps-f-reordered dom-f b-stack-↭)

  --------------------------------------------------------------------
  -- (4) Bridge.  DERIVED: directly the `bridge-term` value.

  bridge-to-g-permute
    : ∀ (n-f n-g : ℕ)
        (vlab-f : Fin n-f → X) (vlab-g : Fin n-g → X)
        (steps-f steps-f-reordered : Steps n-f vlab-f)
        (steps-g : Steps n-g vlab-g)
        (dom-f : List (Fin n-f)) (dom-g : List (Fin n-g))
        (dom-eq : map vlab-g dom-g ≡ map vlab-f dom-f)
        (stack-↭ :
          map vlab-f (proj₁ (process-steps-maybe n-f vlab-f steps-f dom-f))
          Perm.↭
          map vlab-g (proj₁ (process-steps-maybe n-g vlab-g steps-g dom-g)))
        (b-stack-↭ :
          proj₁ (process-steps-maybe n-f vlab-f steps-f           dom-f)
          Perm.↭
          proj₁ (process-steps-maybe n-f vlab-f steps-f-reordered dom-f))
    → permute (Perm.↭-sym stack-↭)
      ∘ subst₂ HomTerm (cong unflatten dom-eq) refl
          (proj₂ (process-steps-maybe n-g vlab-g steps-g dom-g))
      ≈Term
      permute-via-vlab vlab-f (Perm.↭-sym b-stack-↭)
        ∘ proj₂ (process-steps-maybe n-f vlab-f steps-f-reordered dom-f)
  bridge-to-g-permute = bridge-term
