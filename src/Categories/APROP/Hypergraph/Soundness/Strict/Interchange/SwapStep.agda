{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- STRICT per-swap analytic step `swap-≈ˢ` (strict twin of
-- `Discharge.SwapStep`).
--
-- Two strict order-indexed decodings whose orders differ by ONE adjacent
-- incomparable swap are `≈ˢ`-equal.  The chain mirrors the non-strict one,
-- with the Mac-Lane `permute-via-vlab`/`unflatten`/`subst₂ HomTerm` mass
-- collapsing to the vertex-level `permuteˢ` + the UIP-trivial `castˢ` kit
-- (`castˢ refl refl = subst₂ HomS refl refl` reduces DEFINITIONALLY, so the
-- non-strict `coe-cod`/`coe-vanish` `refl`-pattern tricks port verbatim):
--   * `process-edges-++-≈ˢ`  — factors `process-edgesˢ` over `_++_`;
--   * `decodeOrdˢ-factor`     — exposes the prefix term as a right factor;
--   * `front-swap-≈ˢ`         — the front-of-stack two-edge swap (the locus of
--     the (N) `RunInterchangeˢ` residual and the (K) `perm-rigidˢ`);
--   * `swap-≈ˢ`               — the assembled per-swap step.
--
-- The order-theory spine (`Order`/`_↝_`/`swap-step`/`connectivity`/`NoInv`)
-- is REUSED VERBATIM from the term-free non-strict wiring; `Validˢ o =
-- pe-stackˢ o dom ↭ cod` is the strict run's validity (the same proposition
-- as the non-strict `Valid` modulo `stacks-agree`), so `swap-validityˢ`
-- transports the non-strict `SwapValidity.swap-validity`.  The (N) residual
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

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.SwapCore sig _≟X_ as SC
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
  using (module EquivStep)
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.RunInterchangeTail sig _≟X_
  using (RunInterchangeˢ)

import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H`, `dih`, `lin`.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e))
             (lin : Linear H)
             where
  private module H = Hypergraph H

  -- `EquivStep H` re-exports (via `open Run`/`open StrictDecoder`/`open
  -- Perm′`) everything we need: `vl`, `edge-stepˢ`, `permuteˢ`, `pe-stackˢ`,
  -- `pe-termˢ`, `stacks-agree` — no separate `open StrictDecoder` (which
  -- would duplicate `permuteˢ`).
  open EquivStep H using (vl; edge-stepˢ; stacks-agree; permuteˢ; pe-stackˢ; pe-termˢ)

  -- The order-theory spine, reused verbatim from the non-strict wiring
  -- (`connectivity` pre-applied to this hypergraph's acyclicity `dih`).
  module PH = IW.PerHG H
  open PH public using (Order; _↝_; _↝*_; NoInv)
  open IW.PerHG.L H public using (swap-step)

  connectivity : ∀ {L M : Order} → L Perm.↭ M → NoInv L → NoInv M → L ↝* M
  connectivity = PH.connectivity dih

  Incompˢ : Fin H.nE → Fin H.nE → Set
  Incompˢ = SC.Incomp H

  -- The concrete strict Kelly residual at this vertex set.
  private
    permˢ-K : Support.PermK (Fin H.nV) vl
    permˢ-K = PK.permˢ-K (Fin H.nV) _≟F_ vl

  perm-rigidˢ : ∀ {xs ys : List (Fin H.nV)} → Unique ys
              → (p q : xs Perm.↭ ys) → permuteˢ p ≈ˢ permuteˢ q
  perm-rigidˢ = Support.perm-rigidˢ (Fin H.nV) vl permˢ-K

  --------------------------------------------------------------------
  -- STRICT validity + the strict order-indexed decoder.  `Validˢ o`
  -- is the strict run's final-stack permutation onto `cod` (the same
  -- proposition the non-strict `Valid` states, modulo `stacks-agree`).
  --------------------------------------------------------------------

  Validˢ : Order → Set
  Validˢ o = pe-stackˢ o H.dom Perm.↭ H.cod

  decodeOrdˢ : (o : Order) → Validˢ o → HomS (map vl H.dom) (map vl H.cod)
  decodeOrdˢ o p = permuteˢ p ∘ˢ pe-termˢ o H.dom

  -- Bridge `Validˢ`↔`PH.Valid` along `stacks-agree`.
  to-PHValid : ∀ o → Validˢ o → PH.Valid o
  to-PHValid o p = subst (Perm._↭ H.cod) (stacks-agree o H.dom) p

  of-PHValid : ∀ o → PH.Valid o → Validˢ o
  of-PHValid o p = subst (Perm._↭ H.cod) (sym (stacks-agree o H.dom)) p

  --------------------------------------------------------------------
  -- Validity is preserved by an adjacent-independent swap.
  swap-validityˢ : ∀ {o₁ o₂ : Order} → o₁ ↝ o₂ → Validˢ o₁ → Validˢ o₂
  swap-validityˢ {o₁} {o₂} s p =
    of-PHValid o₂ (SV.PerHG.swap-validity H dih lin s (to-PHValid o₁ p))

  --------------------------------------------------------------------
  -- The stack `_++_`-factoring, proven DIRECTLY on `process-edgesˢ` (the
  -- strict run recurses on the prefix exactly like `process-edges`), so the
  -- `[]` case is `refl` and `coe-cod (sym (++-stack [] …))` collapses
  -- definitionally — the strict counterpart of `process-edges-++-stack`.
  ++-stack
    : ∀ (ps rest : Order) (s : List (Fin H.nV))
    → pe-stackˢ (ps ++ rest) s ≡ pe-stackˢ rest (pe-stackˢ ps s)
  ++-stack []       rest s = refl
  ++-stack (e ∷ ps) rest s = ++-stack ps rest (proj₁ (edge-stepˢ s e))

  -- cod-only stack transport (strict twin of `coe-cod`; `castˢ refl refl`
  -- reduces definitionally).
  coe-cod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomS (map vl d) (map vl s) → HomS (map vl d) (map vl s')
  coe-cod eq = castˢ refl (cong (map vl) eq)

  ------------------------------------------------------------------------
  -- PLUMBING 1 — term-level factoring of `process-edgesˢ` over `_++_`.
  ------------------------------------------------------------------------

  process-edges-++-≈ˢ
    : ∀ (ps rest : Order) (s : List (Fin H.nV))
    → pe-termˢ (ps ++ rest) s
      ≈ˢ coe-cod (sym (++-stack ps rest s))
              (pe-termˢ rest (pe-stackˢ ps s) ∘ˢ pe-termˢ ps s)
  process-edges-++-≈ˢ []         rest s = ≈-sym idʳ
  process-edges-++-≈ˢ (e ∷ ps)   rest s =
    ≈-trans
      (∘-resp (process-edges-++-≈ˢ ps rest s') ≈-refl)
      (coe-cod-assoc (sym (++-stack ps rest s'))
                     (pe-termˢ rest (pe-stackˢ ps s'))
                     (pe-termˢ ps s')
                     t)
    where
      s' = proj₁ (edge-stepˢ s e)
      t  = proj₂ (edge-stepˢ s e)

      coe-cod-assoc
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomS (map vl (pe-stackˢ ps s')) (map vl a))
            (f : HomS (map vl s') (map vl (pe-stackˢ ps s')))
            (t0 : HomS (map vl s) (map vl s'))
        → coe-cod eq (g ∘ˢ f) ∘ˢ t0 ≈ˢ coe-cod eq (g ∘ˢ (f ∘ˢ t0))
      coe-cod-assoc refl g f t0 = assocˢ

  ------------------------------------------------------------------------
  -- PLUMBING 2 — `decodeOrdˢ` over a prefixed order factors so the prefix
  -- term sits as a right factor.
  ------------------------------------------------------------------------

  decodeOrdˢ-factor
    : ∀ (ps rest : Order) (p : Validˢ (ps ++ rest))
    → decodeOrdˢ (ps ++ rest) p
      ≈ˢ ( permuteˢ p
            ∘ˢ coe-cod (sym (++-stack ps rest H.dom))
                       (pe-termˢ rest (pe-stackˢ ps H.dom)) )
          ∘ˢ pe-termˢ ps H.dom
  decodeOrdˢ-factor ps rest p =
    ≈-trans
      (∘-resp ≈-refl (process-edges-++-≈ˢ ps rest H.dom))
      (≈-trans
        (∘-resp ≈-refl
          (coe-cod-∘ (sym (++-stack ps rest H.dom))
                     (pe-termˢ rest (pe-stackˢ ps H.dom))
                     (pe-termˢ ps H.dom)))
        (≈-sym assocˢ))
    where
      coe-cod-∘
        : ∀ {a b : List (Fin H.nV)} (eq : a ≡ b)
            (g : HomS (map vl (pe-stackˢ ps H.dom)) (map vl a))
            (f : HomS (map vl H.dom) (map vl (pe-stackˢ ps H.dom)))
        → coe-cod eq (g ∘ˢ f) ≈ˢ coe-cod eq g ∘ˢ f
      coe-cod-∘ refl g f = ≈-refl

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
                 (uniq-cod : Unique (Hypergraph.cod H))
                 where
  private module H = Hypergraph H
  open PerHG H dih lin
  open EquivStep H using (vl; permuteˢ; pe-stackˢ; pe-termˢ)

  --------------------------------------------------------------------
  -- (K)  THE FINAL-PERMUTE RECONCILIATION.  For `r : a-stk ↭ b-stk`,
  -- `va : a-stk ↭ cod`, `vb : b-stk ↭ cod`:
  --     permuteˢ va  ≈ˢ  permuteˢ vb ∘ˢ permuteˢ r
  -- because `va` and `trans r vb` both derive into the `Unique` codomain
  -- `cod`, identified by `perm-rigidˢ` (vertex-level; no `map⁺`-lift).
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
    perm-rigidˢ uniq-cod va (Perm.trans r vb)

  --------------------------------------------------------------------
  -- (N + K) FRONT SWAP — assembled from the `RunInterchangeˢ` residual `RI`
  -- and the (K) coherence.  Stated at the shape `decodeOrdˢ-factor`
  -- produces, so it plugs into `swap-≈ˢ`'s `∘-resp`.
  --------------------------------------------------------------------

  front-swap-≈ˢ
    : ∀ (ps qs : Order) {e e' : Fin H.nE}
        (inc : Incompˢ e e')
        (RI : RunInterchangeˢ H dih lin ps qs inc)
        (p₁ : Validˢ (ps ++ e ∷ e' ∷ qs))
        (p₂ : Validˢ (ps ++ e' ∷ e ∷ qs))
    → ( permuteˢ p₁
          ∘ˢ coe-cod (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
                     (pe-termˢ (e ∷ e' ∷ qs) (pe-stackˢ ps H.dom)) )
      ≈ˢ
      ( permuteˢ p₂
          ∘ˢ coe-cod (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
                     (pe-termˢ (e' ∷ e ∷ qs) (pe-stackˢ ps H.dom)) )
  front-swap-≈ˢ ps qs {e} {e'} inc RI p₁ p₂ =
    ≈-trans (coe-vanish (++-stack ps (e ∷ e' ∷ qs) H.dom) p₁ run₁)
      (≈-trans assembled
        (≈-sym (coe-vanish (++-stack ps (e' ∷ e ∷ qs) H.dom) p₂ run₂)))
    where
      open RunInterchangeˢ RI

      sp  = pe-stackˢ ps H.dom
      run₁ = pe-termˢ (e ∷ e' ∷ qs) sp
      run₂ = pe-termˢ (e' ∷ e ∷ qs) sp

      -- Re-express the validity witnesses at the `fs` level.
      p₁' : pe-stackˢ (e ∷ e' ∷ qs) sp Perm.↭ H.cod
      p₁' = subst (Perm._↭ H.cod) (++-stack ps (e ∷ e' ∷ qs) H.dom) p₁
      p₂' : pe-stackˢ (e' ∷ e ∷ qs) sp Perm.↭ H.cod
      p₂' = subst (Perm._↭ H.cod) (++-stack ps (e' ∷ e ∷ qs) H.dom) p₂

      -- `coe-vanish`: with the stack-equality matched at `refl`, the
      -- codomain `coe-cod` collapses onto the un-transported run.
      coe-vanish
        : ∀ {FS B : List (Fin H.nV)} (eq : FS ≡ B)
            (pv : FS Perm.↭ H.cod)
            (run : HomS (map vl sp) (map vl B))
        → permuteˢ pv ∘ˢ coe-cod (sym eq) run
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
         (uniq-cod : Unique (Hypergraph.cod H))
         where
  open PerHG H dih lin
  module FS = FrontSwap H dih lin uniq-cod
  open FS using (front-swap-≈ˢ)

  module _ (run-interchange
              : ∀ (ps qs : Order) {e e' : Fin (Hypergraph.nE H)} (inc : Incompˢ e e')
              → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE H)
              → RunInterchangeˢ H dih lin ps qs inc) where

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
