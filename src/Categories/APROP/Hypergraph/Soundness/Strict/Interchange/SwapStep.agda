{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- STRICT per-swap analytic step `swap-≈ˢ`.
--
-- Two strict order-indexed decodings whose orders differ by ONE adjacent
-- incomparable swap are `≈ˢ`-equal.  The chain mirrors the non-strict one,
-- with the Mac-Lane `permute-via-vlab`/`unflatten`/`subst₂ HomTerm` mass
-- collapsing to the vertex-level `permuteˢ` + the UIP-trivial `castˢ` kit
-- (`castˢ refl refl = subst₂ HomS refl refl` reduces DEFINITIONALLY, so the
-- non-strict `coe-cod`/`coe-vanish` `refl`-pattern tricks port verbatim):
--   * `pe-term-++ˢ`           — factors `process-edgesˢ` over `_++_` (the ONE
--     kernel, re-exported from `DecodeCompose.RunBlocks`);
--   * `decodeOrdˢ-factor`     — exposes the prefix term as a right factor;
--   * `front-swap-≈ˢ`         — the front-of-stack two-edge swap (the locus of
--     the (N) `RunInterchangeˢ` residual and the (K) `perm-rigidˢ`);
--   * `swap-≈ˢ`               — the assembled per-swap step.
--
-- The order-theory spine (`Order`/`_↝_`/`swap-step`/`connectivity`/`NoInv`)
-- is REUSED VERBATIM from the term-free non-strict wiring; `Validˢ o =
-- pe-stackˢ o dom ↭ cod` is DEFINITIONALLY the non-strict `Valid o`, so
-- `swap-validityˢ` IS `SwapValidity.swap-validity`.  The (N) residual
-- is `RunInterchangeˢ`; the (K) reconciliation is `perm-rigidˢ`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapStep
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen; range)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)
import Categories.APROP.Hypergraph.Soundness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Soundness.Discharge.SwapValidity sig as SV
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique sig using (Linear⇒cod-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig _≟X_ as SC
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
  using (module EquivStep; module RunBlocks)
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig _≟X_
  using (RunInterchangeˢ)

open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H`, `dih`, `lin`.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             where
  private module H = Hypergraph H

  -- `EquivStep H` re-exports (via `open Run`/`open StrictDecoder`/`open
  -- Perm′`) everything we need: `vl`, `permuteˢ`, `pe-stackˢ`, `pe-termˢ`,
  -- `++-stackˢ` — no separate `open StrictDecoder` (which
  -- would duplicate `permuteˢ`).
  open EquivStep H using (vl; permuteˢ; pe-stackˢ; pe-termˢ; ++-stackˢ)

  -- The order-theory spine, reused verbatim from the non-strict wiring
  -- (`connectivity` pre-applied to this hypergraph's acyclicity `dih`).
  module PH = IW.PerHG H
  open PH public using (Order; _↝_; _↝*_; NoInv; swap-step)

  connectivity : ∀ {L M : Order} → L Perm.↭ M → NoInv L → NoInv M → L ↝* M
  connectivity = PH.connectivity dih

  Incompˢ = SC.Incomp H

  -- The (N) residual as a NAMED telescope: for any orders `ps`/`qs` and any
  -- incomparable adjacent pair carrying the `↭ range nE` provenance, the
  -- strict run-interchange.  `swap-≈ˢ` below, `Iso.IsoTransport` (twice) and
  -- `PartII`'s plug all state this socket BY NAME, so it cannot drift.
  RunInterchangeAt : Set
  RunInterchangeAt =
    ∀ (ps qs : Order) {e e' : Fin H.nE} (inc : Incompˢ e e')
    → (ps ++ e' ∷ e ∷ qs) Perm.↭ range H.nE
    → RunInterchangeˢ H lin ps qs inc

  -- The rigidity discharge `SwapCore` states at this vertex set.
  perm-rigidˢ = SC.perm-rigidˢ H

  --------------------------------------------------------------------
  -- STRICT validity + the strict order-indexed decoder.  `Validˢ o`
  -- is the strict run's final-stack permutation onto `cod` — the very
  -- proposition `PH.Valid o` states, since the two stacks are one term.
  --------------------------------------------------------------------

  Validˢ : Order → Set
  Validˢ o = pe-stackˢ o H.dom Perm.↭ H.cod

  decodeOrdˢ : (o : Order) → Validˢ o → HomS (map vl H.dom) (map vl H.cod)
  decodeOrdˢ o p = permuteˢ p ∘ˢ pe-termˢ o H.dom

  --------------------------------------------------------------------
  -- Validity is preserved by an adjacent-independent swap.  `Validˢ o`
  -- IS `PH.Valid o` (the strict run's stack is the non-strict one by
  -- definition), so the non-strict lemma applies with no bridge.
  swap-validityˢ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Validˢ o₁ → Validˢ o₂
  swap-validityˢ {o₁} {o₂} s p = SV.PerHG.swap-validity H lin s p

  -- PLUMBING 1 — the cod-only stack transport `coeCod` and the term-level
  -- factoring of `process-edgesˢ` over `_++_` (`pe-term-++ˢ`), both from the
  -- strict `DecodeCompose` run blocks: `pe-term-++ˢ` IS this cluster's
  -- `process-edges-++-≈ˢ` face, once `++-stackˢ` is the shared stack kernel.
  open RunBlocks H using (coeCod; pe-term-++ˢ) public

  ------------------------------------------------------------------------
  -- PLUMBING 2 — `decodeOrdˢ` over a prefixed order factors so the prefix
  -- term sits as a right factor.
  ------------------------------------------------------------------------

  decodeOrdˢ-factor
    : ∀ (ps rest : Order) (p : Validˢ (ps ++ rest))
    → decodeOrdˢ (ps ++ rest) p
      ≈ˢ ( permuteˢ p
            ∘ˢ coeCod (sym (++-stackˢ ps rest H.dom))
                       (pe-termˢ rest (pe-stackˢ ps H.dom)) )
          ∘ˢ pe-termˢ ps H.dom
  decodeOrdˢ-factor ps rest p =
    ≈-trans
      (∘-resp ≈-refl (pe-term-++ˢ ps rest H.dom))
      (≈-trans
        (∘-resp ≈-refl
          (coeCod-∘ (sym (++-stackˢ ps rest H.dom))
                     (pe-termˢ rest (pe-stackˢ ps H.dom))
                     (pe-termˢ ps H.dom)))
        (≈-sym assocˢ))
    where
      coeCod-∘
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomS (map vl (pe-stackˢ ps H.dom)) (map vl a))
            (f : HomS (map vl H.dom) (map vl (pe-stackˢ ps H.dom)))
        → coeCod eq (g ∘ˢ f) ≈ˢ coeCod eq g ∘ˢ f
      coeCod-∘ refl g f = ≈-refl

------------------------------------------------------------------------
-- The front-of-stack swap.  Fix an INDEPENDENT pair `e e'`; the two runs
-- of `e ∷ e' ∷ qs` vs `e' ∷ e ∷ qs` from `sp = pe-stackˢ ps dom`, wrapped
-- between the shared prefix term and the validity-carried final permute,
-- are `≈ˢ`-equal.  (K) `final-permute-cohˢ` = `perm-rigidˢ`; (N) is the
-- `RunInterchangeˢ` residual.
------------------------------------------------------------------------

module FrontSwap (H : Hypergraph FlatGen)
                 (dih : ∀ {e} → ¬ (Dep H e e))
                 (lin : Linear H)
                 where
  private module H = Hypergraph H
  open PerHG H dih lin
  open EquivStep H using (vl; permuteˢ; pe-stackˢ; pe-termˢ; ++-stackˢ)

  --------------------------------------------------------------------
  -- (K)  THE FINAL-PERMUTE RECONCILIATION.  For `r : a-stk ↭ b-stk`,
  -- `va : a-stk ↭ cod`, `vb : b-stk ↭ cod`:
  --     permuteˢ va  ≈ˢ  permuteˢ vb ∘ˢ permuteˢ r
  -- because `va` and `trans r vb` both derive into the `Unique` codomain
  -- `cod` (`Unique` because `H` is `Linear`), identified by `perm-rigidˢ`
  -- (vertex-level; no `map⁺`-lift).
  --------------------------------------------------------------------

  final-permute-cohˢ
    : ∀ {a-stk b-stk : List (Fin H.nV)}
        (r  : a-stk Perm.↭ b-stk)
        (va : a-stk Perm.↭ H.cod)
        (vb : b-stk Perm.↭ H.cod)
    → permuteˢ va ≈ˢ permuteˢ vb ∘ˢ permuteˢ r
  final-permute-cohˢ r va vb =
    -- `permuteˢ (trans r vb) = permuteˢ vb ∘ˢ permuteˢ r` is DEFINITIONAL
    -- (`pvv-transˢ` is `≈-refl`), so `perm-rigidˢ` closes directly.
    perm-rigidˢ (Linear⇒cod-Unique H lin) va (Perm.trans r vb)

  --------------------------------------------------------------------
  -- (N + K) FRONT SWAP — assembled from the `RunInterchangeˢ` residual `RI`
  -- and the (K) coherence.  Stated at the shape `decodeOrdˢ-factor`
  -- produces, so it plugs into `swap-≈ˢ`'s `∘-resp`.
  --------------------------------------------------------------------

  front-swap-≈ˢ
    : ∀ (ps qs : Order) {e e' : Fin H.nE}
        (inc : Incompˢ e e')
        (RI : RunInterchangeˢ H lin ps qs inc)
        (p₁ : Validˢ (ps ++ e ∷ e' ∷ qs))
        (p₂ : Validˢ (ps ++ e' ∷ e ∷ qs))
    → ( permuteˢ p₁
          ∘ˢ coeCod (sym (++-stackˢ ps (e ∷ e' ∷ qs) H.dom))
                     (pe-termˢ (e ∷ e' ∷ qs) (pe-stackˢ ps H.dom)) )
      ≈ˢ
      ( permuteˢ p₂
          ∘ˢ coeCod (sym (++-stackˢ ps (e' ∷ e ∷ qs) H.dom))
                     (pe-termˢ (e' ∷ e ∷ qs) (pe-stackˢ ps H.dom)) )
  front-swap-≈ˢ ps qs {e} {e'} inc RI p₁ p₂ =
    ≈-trans (coe-vanish (++-stackˢ ps (e ∷ e' ∷ qs) H.dom) p₁ run₁)
      (≈-trans assembled
        (≈-sym (coe-vanish (++-stackˢ ps (e' ∷ e ∷ qs) H.dom) p₂ run₂)))
    where
      open RunInterchangeˢ RI

      sp  = pe-stackˢ ps H.dom
      run₁ = pe-termˢ (e ∷ e' ∷ qs) sp
      run₂ = pe-termˢ (e' ∷ e ∷ qs) sp

      -- Re-express the validity witnesses at the `fs` level.
      p₁' : pe-stackˢ (e ∷ e' ∷ qs) sp Perm.↭ H.cod
      p₁' = subst (Perm._↭ H.cod) (++-stackˢ ps (e ∷ e' ∷ qs) H.dom) p₁
      p₂' : pe-stackˢ (e' ∷ e ∷ qs) sp Perm.↭ H.cod
      p₂' = subst (Perm._↭ H.cod) (++-stackˢ ps (e' ∷ e ∷ qs) H.dom) p₂

      -- `coe-vanish`: with the stack-equality matched at `refl`, the
      -- codomain `coeCod` collapses onto the un-transported run.
      coe-vanish
        : ∀ {FS B : List (Fin H.nV)} (eq : FS ≡ B)
            (pv : FS Perm.↭ H.cod)
            (run : HomS (map vl sp) (map vl B))
        → permuteˢ pv ∘ˢ coeCod (sym eq) run
          ≈ˢ permuteˢ (subst (Perm._↭ H.cod) eq pv) ∘ˢ run
      coe-vanish refl pv run = ≈-refl

      -- The core assembly at the `fs` level, via (K), `assocˢ`, and (N).
      assembled : permuteˢ p₁' ∘ˢ run₁ ≈ˢ permuteˢ p₂' ∘ˢ run₂
      assembled =
        ≈-trans
          (∘-resp (final-permute-cohˢ reshuffle p₁' p₂') ≈-refl)
          (≈-trans assocˢ
            (∘-resp ≈-refl (≈-sym run-eq)))

------------------------------------------------------------------------
-- Assembly of `swap-≈ˢ`.
------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  open PerHG H dih lin
  module FS = FrontSwap H dih lin
  open FS using (front-swap-≈ˢ)

  module _ (run-interchange : RunInterchangeAt) where

    swap-≈ˢ
      : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂
      → o₁ Perm.↭ range (Hypergraph.nE H)
      → (p₁ : Validˢ o₁) (p₂ : Validˢ o₂)
      → decodeOrdˢ o₁ p₁ ≈ˢ decodeOrdˢ o₂ p₂
    swap-≈ˢ (swap-step ps {e} {e'} qs inc) o₁↭range p₁ p₂ =
      ≈-trans
        (decodeOrdˢ-factor ps (e ∷ e' ∷ qs) p₁)
        (≈-trans
          (∘-resp (front-swap-≈ˢ ps qs inc
                     (run-interchange ps qs inc o₂↭range) p₁ p₂)
                  ≈-refl)
          (≈-sym (decodeOrdˢ-factor ps (e' ∷ e ∷ qs) p₂)))
      where
        o₂↭range : (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
        o₂↭range = Perm.↭-trans (PermProp.++⁺ˡ ps (Perm.swap e' e Perm.refl)) o₁↭range
