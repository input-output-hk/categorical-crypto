-- Discharges the `swap-≈` obligation of `IsoInvarianceWiring`'s `PerHG`
-- (§II of the soundness proof) down to two isolated bottom axioms:
--
--   (N)  symmetric-monoidal interchange `σ ∘ (p ⊗ q) ≈ (q ⊗ p) ∘ σ`
--        (the `σ∘[f⊗g]≈[g⊗f]∘σ` constructor), applied to the two opaque
--        edge boxes `(Agen-edge ⊗ id)` on DISJOINT wire blocks;
--   (K)  permutation coherence `FaithfulnessResidual.permute-resp-≅↭` —
--        two `permute-via-vlab` reshuffles realising the SAME bijection
--        are `≈Term`-equal.
--
-- The plumbing between `swap-≈` and {N,K} is proved here:
--   * `process-edges-++-≈`  — factors `process-edges` over `_++_`,
--     reducing a general swap (after prefix `ps`) to a FRONT swap.
--   * `decodeOrd-factor` — exposes the prefix term as a right factor and
--     the validity-carried final `permute-via-vlab` as a left factor.
--   * `front-swap-≈` — the front-of-stack two-edge swap for INDEPENDENT
--     (`Incomp`) edges; the locus where N and K are invoked.
--
-- `front-swap-≈` is a THEOREM, derived from:
--   * (K) `final-permute-coh` — the final-permute reconciliation: two
--     validity witnesses `va : a-stk ↭ cod`, `vb : b-stk ↭ cod` bridged
--     by `r : a-stk ↭ b-stk` give `permute va ≈ permute vb ∘ permute r`,
--     since both `va` and `trans r vb` evaluate to the same FinBij on the
--     `Unique (cod H)` codomain, and K closes the gap.
--   * (N) `RunInterchange` — the sole remaining residual (record
--     parameter): the reshuffle `r : fs₁ ↭ fs₂` plus the run-level
--     interchange `run₂ ≈ permute r ∘ run₁`.  Mentions neither the final
--     permute nor `cod`, so it is exactly the interchange-axiom content.
--
-- `uniq-cod` is the VERTEX-level `Unique (cod H)` (dischargeable from
-- `⟪_⟫-cod-unique`), NOT the X-level `Unique (map vlab cod)` (which is
-- FALSE when boundary atoms repeat).
{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.SwapStep
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Soundness.Decode sig
  using (process-edges; edge-step; Agen-edge)
open import Categories.APROP.Hypergraph.Soundness.Permute sig
  using (permute-via-vlab)

import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt sig
  using (process-edges-++-stack)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep)

open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)

open import Categories.PermuteCoherence.Rigid using (eval-rigid)
open import Categories.PermuteCoherence.Map using (eval-map⁺; subst₂-FinBij-≈)

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Patterns using (0F)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using () renaming (_∷_ to _∷ᵘ_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
import Data.Fin.Permutation as P
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H` and a `Dep`-irreflexivity witness `dih`.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e)) where
  private module H = Hypergraph H

  -- The per-hypergraph module from the chain whose `swap-≈` we discharge;
  -- we match its `Order`, `Valid`, `_↝_`, `decodeOrd` definitionally.
  module PH = IW.PerHG H dih

  -- `Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)`: the two edges are
  -- INDEPENDENT (neither produces a wire the other consumes).
  open PH.L public using (Incomp; swap-step)

  Order : Set
  Order = PH.Order

  Valid : Order → Set
  Valid = PH.Valid

  decodeOrd : (o : Order) → Valid o
            → HomTerm (unflatten (domL H)) (unflatten (codL H))
  decodeOrd = PH.decodeOrd

  --------------------------------------------------------------------
  -- Abbreviations for the two `process-edges` projections.

  pe-stack : Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = proj₁ (process-edges H o s)

  pe-term : (o : Order) (s : List (Fin H.nV))
          → HomTerm (unflatten (map H.vlab s))
                    (unflatten (map H.vlab (pe-stack o s)))
  pe-term o s = proj₂ (process-edges H o s)

  ------------------------------------------------------------------------
  -- Codomain transport: re-index a `HomTerm`'s codomain along a stack
  -- equality.  The `_++_`-factoring of the stack (`process-edges-++-stack`)
  -- is only PROPOSITIONAL (it inducts under `with edge-step`, blocking
  -- definitional reduction), so we transport terms across it explicitly.
  ------------------------------------------------------------------------

  coe-cod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s))
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s'))
  coe-cod {d} eq = subst (λ z → HomTerm (unflatten (map H.vlab d))
                                         (unflatten (map H.vlab z)))
                          eq

  -- The stack `_++_`-factoring: the final stack of `ps ++ rest` from `s`
  -- is that of `rest` from the post-`ps` stack.
  ++-stack
    : ∀ (ps rest : Order) (s : List (Fin H.nV))
    → pe-stack (ps ++ rest) s ≡ pe-stack rest (pe-stack ps s)
  ++-stack = process-edges-++-stack H

  ------------------------------------------------------------------------
  -- PLUMBING 1 — term-level factoring of `process-edges` over `_++_`.
  --
  -- Running `ps ++ rest` from `s` is, on the term level, running `rest`
  -- from the post-`ps` stack, precomposed with running `ps` from `s` —
  -- modulo the codomain transport `coe-cod (++-stack …)`.  Proven by
  -- induction on `ps` using `assoc`; the codomain `subst` is threaded by
  -- a `subst`-naturality step at each cons.
  ------------------------------------------------------------------------

  process-edges-++-≈
    : ∀ (ps rest : Order) (s : List (Fin H.nV))
    → pe-term (ps ++ rest) s
      ≈Term coe-cod (sym (++-stack ps rest s))
              (pe-term rest (pe-stack ps s) ∘ pe-term ps s)
  process-edges-++-≈ []         rest s = ≈-Term-sym idʳ
  process-edges-++-≈ (e ∷ ps)   rest s
    with edge-step H s e
  ... | s' , t =
    ≈-Term-trans
      (∘-resp-≈ (process-edges-++-≈ ps rest s') ≈-Term-refl)
      (coe-cod-assoc (sym (++-stack ps rest s'))
                     (pe-term rest (pe-stack ps s')) (pe-term ps s') t)
    where
      -- Re-bracket the codomain-transported composite past the prefix
      -- edge term `t0`: `coe (g ∘ f) ∘ t0 ≈ coe (g ∘ (f ∘ t0))`.  At
      -- `eq = refl` this is `assoc`.
      coe-cod-assoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomTerm (unflatten (map H.vlab (pe-stack ps s')))
                         (unflatten (map H.vlab a)))
            (f : HomTerm (unflatten (map H.vlab s'))
                         (unflatten (map H.vlab (pe-stack ps s'))))
            (t0 : HomTerm (unflatten (map H.vlab s))
                          (unflatten (map H.vlab s')))
        → coe-cod eq (g ∘ f) ∘ t0
          ≈Term coe-cod eq (g ∘ (f ∘ t0))
      coe-cod-assoc refl g f t0 = assoc

  ------------------------------------------------------------------------
  -- PLUMBING 2 — `decodeOrd` over a prefixed order factors so the prefix
  -- term sits as a right factor.
  --
  --   decodeOrd (ps ++ rest) p
  --     = permute-via-vlab vlab p ∘ pe-term (ps ++ rest) dom
  --     ≈ (permute-via-vlab vlab p ∘ coe-cod (sym ++-stack) (pe-term rest sp))
  --         ∘ pe-term ps dom
  --
  -- where `sp = pe-stack ps dom`.  The codomain transport on `pe-term rest`
  -- is absorbed into the left factor (its codomain is `unflatten (codL H)`
  -- regardless, fixed by the validity witness `p`).
  ------------------------------------------------------------------------

  decodeOrd-factor
    : ∀ (ps rest : Order) (p : Valid (ps ++ rest))
    → decodeOrd (ps ++ rest) p
      ≈Term ( permute-via-vlab H.vlab p
                ∘ coe-cod (sym (++-stack ps rest H.dom))
                          (pe-term rest (pe-stack ps H.dom)) )
              ∘ pe-term ps H.dom
  decodeOrd-factor ps rest p =
    -- Rewrite the right operand by `process-edges-++-≈`, push `coe-cod`
    -- into the left factor (`coe-cod-∘`), then re-associate.
    ≈-Term-trans
      (∘-resp-≈ ≈-Term-refl (process-edges-++-≈ ps rest H.dom))
      (≈-Term-trans
        (∘-resp-≈ ≈-Term-refl
          (coe-cod-∘ (sym (++-stack ps rest H.dom))
                     (pe-term rest (pe-stack ps H.dom))
                     (pe-term ps H.dom)))
        (≈-Term-sym assoc))
    where
      -- `coe-cod` only touches the codomain, which lives in the left
      -- factor, so it commutes out of a composition (subst-naturality).
      coe-cod-∘
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomTerm (unflatten (map H.vlab (pe-stack ps H.dom)))
                         (unflatten (map H.vlab a)))
            (f : HomTerm (unflatten (map H.vlab H.dom))
                         (unflatten (map H.vlab (pe-stack ps H.dom))))
        → coe-cod eq (g ∘ f) ≈Term coe-cod eq g ∘ f
      coe-cod-∘ refl g f = ≈-Term-refl

------------------------------------------------------------------------
-- The front-of-stack swap.
--
-- Fix an INDEPENDENT pair of edges `e e'` at the front of `e ∷ e' ∷ qs`
-- vs `e' ∷ e ∷ qs`, both run from the same stack `sp`.  As factors of
-- `decodeOrd` the two runs are wrapped between the shared prefix term
-- (right) and the validity-carried final `permute-via-vlab` (left).
--
-- INDEPENDENCE (`Incomp`) means the two opaque boxes `(Agen-edge ⊗ id)`
-- act on DISJOINT blocks, so they commute by (N); the surrounding
-- `permute-via-vlab` reshuffles realise the SAME bijection and are
-- reconciled by (K).  The K-half is proven here (`final-permute-coh`);
-- the N-half is the `RunInterchange` residual.  `front-swap-≈` is stated
-- at the `decodeOrd`-factor level so it plugs into `swap-≈` directly.
------------------------------------------------------------------------

-- `FrontSwap` is parameterised by the Kelly residual `K` and the
-- VERTEX-level `Unique (cod H)` (dischargeable downstream at `H = ⟪f⟫`
-- via `⟪_⟫-cod-unique`; NOT the X-level `Unique (map vlab cod)`, which is
-- FALSE when boundary atoms repeat).
module FrontSwap (H : Hypergraph FlatGen)
                 (dih : ∀ {e} → ¬ (Dep H e e))
                 (K : FaithfulnessResidual)
                 (uniq-cod : Unique (Hypergraph.cod H))
                 where
  private module H = Hypergraph H
  open PerHG H dih
  open FaithfulnessResidual K

  --------------------------------------------------------------------
  -- (K)  THE FINAL-PERMUTE RECONCILIATION — proven given K.
  --
  -- For `r : a-stk ↭ b-stk`, `va : a-stk ↭ cod`, `vb : b-stk ↭ cod`:
  --     permute-via-vlab va  ≈  permute-via-vlab vb ∘ permute-via-vlab r
  -- because both `va` and `trans r vb` are derivations into the SAME
  -- `Unique` codomain `cod`, so their `map⁺ vlab` liftings evaluate to
  -- the same FinBij (`eval-rigid`), i.e. are `≅↭`-equal, and K closes it.
  --------------------------------------------------------------------

  private
    -- `≅↭`-equality of the two map-lifted derivations into `map vlab cod`.
    permute-bridge-≅↭
      : ∀ {a-stk b-stk : List (Fin H.nV)}
          (r  : a-stk Perm.↭ b-stk)
          (va : a-stk Perm.↭ H.cod)
          (vb : b-stk Perm.↭ H.cod)
      → eval-↭ (PermProp.map⁺ H.vlab va)
        ≈-fb eval-↭ (PermProp.map⁺ H.vlab (Perm.trans r vb))
    permute-bridge-≅↭ {a-stk} {b-stk} r va vb =
      -- `eval-rigid` on the VERTEX-level `va`/`trans r vb` against
      -- `Unique (cod H)`, transported through `map⁺ vlab` by `eval-map⁺`
      -- + `subst₂-FinBij-≈` (so no X-level uniqueness is needed).
      subst (λ z → z ≈-fb eval-↭ (PermProp.map⁺ H.vlab (Perm.trans r vb)))
            (sym (eval-map⁺ H.vlab va))
        (subst (λ z → subst₂ FinBij (sym (length-map H.vlab a-stk))
                                    (sym (length-map H.vlab H.cod)) (eval-↭ va)
                      ≈-fb z)
               (sym (eval-map⁺ H.vlab (Perm.trans r vb)))
          (subst₂-FinBij-≈ (sym (length-map H.vlab a-stk))
                           (sym (length-map H.vlab H.cod))
            (eval-rigid uniq-cod va (Perm.trans r vb))))

  final-permute-coh
    : ∀ {a-stk b-stk : List (Fin H.nV)}
        (r  : a-stk Perm.↭ b-stk)
        (va : a-stk Perm.↭ H.cod)
        (vb : b-stk Perm.↭ H.cod)
    → permute-via-vlab H.vlab va
      ≈Term permute-via-vlab H.vlab vb ∘ permute-via-vlab H.vlab r
  final-permute-coh r va vb =
    permute-resp-≅↭
      (PermProp.map⁺ H.vlab va)
      (PermProp.map⁺ H.vlab (Perm.trans r vb))
      (permute-bridge-≅↭ r va vb)

  --------------------------------------------------------------------
  -- (N)  THE INTERCHANGE KERNEL — the literal σ-naturality application.
  --
  -- The interchange axiom in σ-conjugation form `g ⊗₁ f ≈ σ ∘ (f ⊗₁ g) ∘ σ`
  -- (two boxes on disjoint blocks commute), from `σ∘[f⊗g]≈[g⊗f]∘σ` (N) and
  -- `σ∘σ≈id`.  The N-axiom enters the front swap ONLY through here.  The
  -- `RunInterchange.run-eq` residual below is this kernel transported
  -- through the two boxes' `unflatten-++-≅` bookkeeping plus the tail
  -- recursion (the part `Incomp` alone does not give).
  --------------------------------------------------------------------

  box-interchange
    : ∀ {A B C D : ObjTerm}
        (f : HomTerm A B) (g : HomTerm C D)
    → g ⊗₁ f ≈Term σ ∘ ((f ⊗₁ g) ∘ σ)
  box-interchange f g =
    ≈-Term-sym
      (≈-Term-trans
        (≈-Term-trans
          (≈-Term-sym assoc)
          (∘-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ ≈-Term-refl))
        (≈-Term-trans assoc
          (≈-Term-trans (∘-resp-≈ ≈-Term-refl σ∘σ≈id) idʳ)))

  record RunInterchange (ps qs : Order) {e e' : Fin H.nE}
                        (inc : Incomp e e') : Set where
    private
      sp  = pe-stack ps H.dom
      fs₁ = pe-stack (e ∷ e' ∷ qs) sp
      fs₂ = pe-stack (e' ∷ e ∷ qs) sp
    field
      -- The reshuffle between the two post-front stacks.
      reshuffle : fs₁ Perm.↭ fs₂
      -- (N): the `e' ∷ e` run equals the `e ∷ e'` run followed by the
      -- reshuffle's permute.
      run-eq
        : pe-term (e' ∷ e ∷ qs) sp
          ≈Term permute-via-vlab H.vlab reshuffle ∘ pe-term (e ∷ e' ∷ qs) sp

  --------------------------------------------------------------------
  -- (N + K) FRONT SWAP — assembled from the N-residual `RI` and the
  -- proven K-coherence.  Stated at the shape `decodeOrd-factor` produces,
  -- so it plugs into `swap-≈`'s `∘-resp-≈`.
  --------------------------------------------------------------------

  front-swap-≈
    : ∀ (ps qs : Order) {e e' : Fin H.nE}
        (inc : Incomp e e')
        (RI : RunInterchange ps qs inc)
        (p₁ : Valid (ps ++ e ∷ e' ∷ qs))
        (p₂ : Valid (ps ++ e' ∷ e ∷ qs))
    → ( permute-via-vlab H.vlab p₁
          ∘ coe-cod (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
                    (pe-term (e ∷ e' ∷ qs) (pe-stack ps H.dom)) )
      ≈Term
      ( permute-via-vlab H.vlab p₂
          ∘ coe-cod (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
                    (pe-term (e' ∷ e ∷ qs) (pe-stack ps H.dom)) )
  front-swap-≈ ps qs {e} {e'} inc RI p₁ p₂ =
    -- Both `coe-cod` transports vanish to the un-transported `fs` level
    -- (`coe-vanish`), once `p₁,p₂` are re-expressed at the `fs` level.
    ≈-Term-trans (coe-vanish (++-stack ps (e ∷ e' ∷ qs) H.dom) p₁
                             (pe-term (e ∷ e' ∷ qs) sp))
      (≈-Term-trans assembled
        (≈-Term-sym (coe-vanish (++-stack ps (e' ∷ e ∷ qs) H.dom) p₂
                                (pe-term (e' ∷ e ∷ qs) sp))))
    where
      open RunInterchange RI

      sp  = pe-stack ps H.dom
      fs₁ = pe-stack (e ∷ e' ∷ qs) sp
      fs₂ = pe-stack (e' ∷ e ∷ qs) sp

      run₁ = pe-term (e ∷ e' ∷ qs) sp
      run₂ = pe-term (e' ∷ e ∷ qs) sp

      -- Re-express the validity witnesses at the `fs` level.
      p₁' : fs₁ Perm.↭ H.cod
      p₁' = subst (Perm._↭ H.cod) (++-stack ps (e ∷ e' ∷ qs) H.dom) p₁
      p₂' : fs₂ Perm.↭ H.cod
      p₂' = subst (Perm._↭ H.cod) (++-stack ps (e' ∷ e ∷ qs) H.dom) p₂

      -- `coe-vanish`: with the stack-equality matched at `refl`, the two
      -- codomain `subst`s compose to the un-transported composite.  `FS`
      -- is generalised to a variable so the `refl` split is not
      -- unification-stuck under `--without-K`.
      coe-vanish
        : ∀ {FS B : List (Fin H.nV)} (eq : FS ≡ B)
            (pv : FS Perm.↭ H.cod)
            (run : HomTerm (unflatten (map H.vlab sp))
                           (unflatten (map H.vlab B)))
        → permute-via-vlab H.vlab pv ∘ coe-cod (sym eq) run
          ≈Term permute-via-vlab H.vlab (subst (Perm._↭ H.cod) eq pv) ∘ run
      coe-vanish refl pv run = ≈-Term-refl

      -- The core assembly at the `fs` level, via K (`final-permute-coh`),
      -- `assoc`, and N (`run-eq`).
      assembled
        : permute-via-vlab H.vlab p₁' ∘ run₁
          ≈Term permute-via-vlab H.vlab p₂' ∘ run₂
      assembled =
        ≈-Term-trans
          (∘-resp-≈ (final-permute-coh reshuffle p₁' p₂') ≈-Term-refl)
          (≈-Term-trans assoc
            (∘-resp-≈ ≈-Term-refl (≈-Term-sym run-eq)))

------------------------------------------------------------------------
-- Assembly of `swap-≈`: `decodeOrd-factor` on each side, then
-- `front-swap-≈` on the front runs (carrying the shared prefix
-- `pe-term ps dom` through `∘-resp-≈`).  Parameterised by K, the
-- `Unique` codomain witness, and the per-swap `run-interchange` (N).
------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (K : FaithfulnessResidual)
         (uniq-cod : Unique (Hypergraph.cod H))
         where
  open PerHG H dih
  module FS = FrontSwap H dih K uniq-cod
  open FS using (front-swap-≈; RunInterchange)

  -- `run-interchange` carries the swap-site provenance `ps ++ e' ∷ e ∷ qs
  -- ↭ range nE` — the sound side condition under which the reservoir bound
  -- holds (every edge appears once, so `eout` is not over-counted).
  module _ (run-interchange
              : ∀ (ps qs : Order) {e e' : Fin (Hypergraph.nE H)} (inc : Incomp e e')
              → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
              → RunInterchange ps qs inc) where

    swap-≈
      : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂
      → o₁ Perm.↭ range (Hypergraph.nE H)
      → (p₁ : PH.Valid o₁) (p₂ : PH.Valid o₂)
      → PH.decodeOrd o₁ p₁ ≈Term PH.decodeOrd o₂ p₂
    swap-≈ (swap-step ps {e} {e'} qs inc) o₁↭range p₁ p₂ =
      ≈-Term-trans
        (decodeOrd-factor ps (_ ∷ _ ∷ qs) p₁)
        (≈-Term-trans
          (∘-resp-≈ (front-swap-≈ ps qs inc
                       (run-interchange ps qs inc o₂↭range) p₁ p₂)
                    ≈-Term-refl)
          (≈-Term-sym (decodeOrd-factor ps (_ ∷ _ ∷ qs) p₂)))
      where
        -- `o₂ ↭ o₁` (adjacent transposition under `ps`), hence `↭ range`.
        o₂↭range : (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
        o₂↭range =
          Perm.↭-trans
            (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl))
            o₁↭range
