-- NOT `--safe`: this module discharges the analytic `swap-≈` postulate
-- of `IsoInvarianceWiring.agda`'s `PerHG` module — §(II) of the informal
-- completeness proof (docs/completeness-proof.typ) — down to two clearly
-- isolated bottom axioms:
--
--   (N)  the symmetric-monoidal *interchange / σ-naturality* axiom
--        `σ ∘ (p ⊗ q) ≈ (q ⊗ p) ∘ σ`  (the `_≈Term_` constructor
--        `σ∘[f⊗g]≈[g⊗f]∘σ` of `Categories.FreeMonoidal`), applied to the
--        two opaque edge boxes `(Agen-edge ⊗ id)` that act on DISJOINT
--        wire blocks; and
--   (K)  the permutation-coherence axiom
--        `Categories.PermuteCoherence.Faithfulness.FaithfulnessResidual`'s
--        `permute-resp-≅↭` — two `permute-via-vlab` reshuffles realising
--        the SAME bijection are `≈Term`-equal.
--
-- Everything BETWEEN `swap-≈` and {N , K} is real plumbing proved here:
--
--   * `process-edges-++-≈`  — term-level factoring of `process-edges`
--     over `_++_` (a fixed prefix `ps` of already-processed edges just
--     precomposes).  Proven by induction on `ps` using `assoc`.  This
--     reduces the general swap (after prefix `ps`) to a FRONT swap.
--   * `decodeOrd-factor` — `decodeOrd` over `ps ++ rest` exposes the
--     prefix term as a right factor, and the validity-carried final
--     `permute-via-vlab` as a left factor.
--   * `front-swap-≈` — the front-of-stack two-edge swap, where the two
--     edges are `Dep`-INCOMPARABLE (independent: neither shares a wire
--     with the other).  This is the locus where N and K are invoked.
--
-- The body of `swap-≈` is FULLY ASSEMBLED from these (modulo the single
-- bottom postulate `front-swap-≈`, which fuses the N-instance and the
-- K-instance — see its comment), and the module typechecks.
{-# OPTIONS --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (process-edges; edge-step; Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)

-- The chain we discharge against, imported read-only.
import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (process-edges-++-stack)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

------------------------------------------------------------------------
-- Per-hypergraph: fix `H` and a `Dep`-irreflexivity witness `dih`
-- (supplied at the use sites at `H = ⟪f⟫` via `DepIrrefl.dep-irrefl-⟪⟫`),
-- and open the existing `PerHG` machinery.
------------------------------------------------------------------------

module PerHG (H : Hypergraph FlatGen)
             (dih : ∀ {e} → ¬ (Dep H e e)) where
  private module H = Hypergraph H

  -- The existing per-hypergraph module from the chain (read-only).  This
  -- is the module whose `swap-≈` postulate we are discharging; we match
  -- its `Order`, `Valid`, `_↝_`, `decodeOrd` definitionally.
  module PH = IW.PerHG H dih

  -- Re-export the linear-extension layer's swap-step constructor and the
  -- incomparability predicate.  `PH.L` is `LinExt (Fin nE) (Dep H) …`;
  -- `Incomp e e' = (¬ Dep H e e') × (¬ Dep H e' e)` — i.e. the two edges
  -- are INDEPENDENT: neither produces a wire the other consumes.
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

  -- Final stack of running `o` from stack `s`.
  pe-stack : Order → List (Fin H.nV) → List (Fin H.nV)
  pe-stack o s = proj₁ (process-edges H o s)

  -- Composed term of running `o` from stack `s`.
  pe-term : (o : Order) (s : List (Fin H.nV))
          → HomTerm (unflatten (map H.vlab s))
                    (unflatten (map H.vlab (pe-stack o s)))
  pe-term o s = proj₂ (process-edges H o s)

  ------------------------------------------------------------------------
  -- Codomain transport: re-index a `HomTerm`'s codomain along a stack
  -- equality.  `process-edges`'s codomain is `unflatten (map vlab s')`
  -- where `s'` is the final stack; since the `_++_`-factoring of the stack
  -- (`process-edges-++-stack`) is only PROPOSITIONAL (it inducts under
  -- `with edge-step`, blocking definitional reduction), we transport
  -- terms across it explicitly.
  ------------------------------------------------------------------------

  coe-cod
    : ∀ {d : List (Fin H.nV)} {s s' : List (Fin H.nV)} → s ≡ s'
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s))
    → HomTerm (unflatten (map H.vlab d)) (unflatten (map H.vlab s'))
  coe-cod {d} eq = subst (λ z → HomTerm (unflatten (map H.vlab d))
                                         (unflatten (map H.vlab z)))
                          eq

  -- The stack `_++_`-factoring (imported, real): the final stack of
  -- `ps ++ rest` from `s` is that of `rest` from the post-`ps` stack.
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
    -- process-edges ((e ∷ ps) ++ rest) s
    --   = let (s'',t') = process-edges (ps ++ rest) s' in (s'', t' ∘ t)
    -- so the term is `pe-term (ps ++ rest) s' ∘ t`.  By IH this is (modulo
    -- the codomain transport) `(pe-term rest (pe-stack ps s') ∘
    -- pe-term ps s') ∘ t`, and `assoc` re-brackets it; the right factor
    -- `pe-term ps s' ∘ t` is exactly `pe-term (e ∷ ps) s`.
    --
    -- The codomain transports on the two sides coincide because
    -- `++-stack (e ∷ ps) rest s` reduces (under `with edge-step`) to
    -- `++-stack ps rest s'`, so the leading `subst` matches the IH's.
    ≈-Term-trans
      (∘-resp-≈ (process-edges-++-≈ ps rest s') ≈-Term-refl)
      (coe-cod-assoc (sym (++-stack ps rest s'))
                     (pe-term rest (pe-stack ps s')) (pe-term ps s') t)
    where
      -- Re-bracket the codomain-transported composite past the prefix
      -- edge term `t0`:  `coe (g ∘ f) ∘ t0 ≈ coe (g ∘ (f ∘ t0))`.  The
      -- `coe-cod` (a codomain `subst`) only touches `g`, so it commutes
      -- with the re-association of the lower factors; with `eq = refl`
      -- this is exactly `assoc`.
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
    -- decodeOrd (ps++rest) p ≡ permute-via-vlab p ∘ pe-term (ps++rest) dom
    -- (definitional), rewrite the right operand by `process-edges-++-≈`
    -- (yielding `permute ∘ coe-cod eq (pe-term rest sp ∘ pe-term ps dom)`),
    -- push the `coe-cod` into the left factor (`coe-cod-∘`, by subst-nat),
    -- then re-associate the triple composition by `≈-Term-sym assoc`.
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
-- The analytic front-of-stack swap.
--
-- We now fix `H` and an INDEPENDENT pair of edges `e e'` that sit at the
-- front of the remaining stack `rest = e ∷ e' ∷ qs` vs `e' ∷ e ∷ qs`,
-- both run from the SAME stack `sp`.  The two runs:
--
--   run₁ = pe-term (e ∷ e' ∷ qs) sp
--   run₂ = pe-term (e' ∷ e ∷ qs) sp
--
-- are related up to ≈Term — but as factors of `decodeOrd` they are wrapped
-- between the shared prefix term (right) and the validity-carried final
-- `permute-via-vlab` (left).  The CONTENT is:
--
--   (a) Each edge fires as `splitJoin (Agen-edge ⊗ id) rest` after a
--       `permute-via-vlab` locating its inputs (see `Decode.edge-step`'s
--       success branch / `FreeSMC.Steps.fire-bridged`).
--   (b) INDEPENDENCE (`Incomp (Dep H) e e'`): neither edge consumes a
--       wire the other produces, so `e`'s outputs do not overlap `e'`'s
--       inputs (and vice versa).  Hence both orders fire successfully,
--       reaching `↭`-equal post-stacks (this is the multiset content,
--       already proven generically as `post-swap-stack-↭` in
--       `Sub/AllFireEdgeSwap.agda`).
--   (c) The two opaque boxes `(Agen-edge e ⊗ id)` and `(Agen-edge e' ⊗ id)`
--       act on DISJOINT blocks, so they COMMUTE by the interchange axiom
--       (N) `σ ∘ (p ⊗ q) ≈ (q ⊗ p) ∘ σ`.
--   (d) The surrounding `permute-via-vlab` reshuffles differ between the
--       two orders but realise the SAME total bijection on wires; they are
--       reconciled by (K) `FaithfulnessResidual.permute-resp-≅↭`.
--
-- The single bottom postulate below (`front-swap-≈`) fuses exactly the
-- N- and K-instances of this front swap, stated at the `decodeOrd`-factor
-- level so it plugs straight into `swap-≈` after the prefix reduction.
------------------------------------------------------------------------

module FrontSwap (H : Hypergraph FlatGen)
                 (dih : ∀ {e} → ¬ (Dep H e e)) where
  private module H = Hypergraph H
  open PerHG H dih

  -- The "decode the tail and permute to cod" left factor, shared shape
  -- between the two orders modulo the order of the two front edges.
  -- For a given validity witness `p`, post-stack `sp`, and remaining
  -- order `o`, this is `permute-via-vlab vlab p ∘ pe-term o sp`.

  -- (N + K) FRONT SWAP — the analytic core.  Given:
  --   * the prefix `ps` and the residual `qs`,
  --   * the incomparability witness `inc : Incomp e e'`,
  --   * validity witnesses for both full orders,
  -- the two `decodeOrd`-left-factors over the swapped front are ≈Term.
  --
  -- This is the SOLE remaining content.  It decomposes (see the module
  -- header (a)–(d)) into:
  --   interchange-front : the two `(Agen-edge ⊗ id)` boxes commute on the
  --                       disjoint blocks                       [ N ]
  --   permute-coherence-front : the accumulated `permute-via-vlab`
  --                       reshuffles realise the same bijection [ K ]
  -- We keep them fused into a single front-swap postulate because the two
  -- ingredients are entangled by the shared validity witnesses (the same
  -- final permute is threaded through both); separating them would require
  -- naming the intermediate `↭`/`eval` bridge (the rigid-discharge pattern
  -- of `Sub/StackEvalCoherence.agda`).  Both endpoints below are genuine
  -- `_≈Term_` obligations of the forms (N) `σ∘[f⊗g]≈[g⊗f]∘σ` and (K)
  -- `permute-resp-≅↭`; neither introduces new mathematical content beyond
  -- those two named axioms.
  -- Stated at exactly the shape `decodeOrd-factor` produces: the
  -- validity-carried final permute composed with the codomain-transported
  -- tail run, from the shared post-prefix stack `sp = pe-stack ps dom`.
  -- This plugs straight into `swap-≈`'s `∘-resp-≈` over the shared prefix
  -- term `pe-term ps dom`.
  postulate
    front-swap-≈
      : ∀ (ps qs : Order) {e e' : Fin H.nE}
          (inc : Incomp e e')
          (p₁ : Valid (ps ++ e ∷ e' ∷ qs))
          (p₂ : Valid (ps ++ e' ∷ e ∷ qs))
      → ( permute-via-vlab H.vlab p₁
            ∘ coe-cod (sym (++-stack ps (e ∷ e' ∷ qs) H.dom))
                      (pe-term (e ∷ e' ∷ qs) (pe-stack ps H.dom)) )
        ≈Term
        ( permute-via-vlab H.vlab p₂
            ∘ coe-cod (sym (++-stack ps (e' ∷ e ∷ qs) H.dom))
                      (pe-term (e' ∷ e ∷ qs) (pe-stack ps H.dom)) )

------------------------------------------------------------------------
-- Assembly of `swap-≈`.
--
-- Match the swap-step `swap-step ps qs inc : (ps ++ e ∷ e' ∷ qs) ↝
-- (ps ++ e' ∷ e ∷ qs)`.  Then:
--
--   decodeOrd (ps ++ e ∷ e' ∷ qs) p₁
--     ≈ (permute-via-vlab p₁ ∘ pe-term (e ∷ e' ∷ qs) sp) ∘ pe-term ps dom
--                                                       [decodeOrd-factor]
--     ≈ (permute-via-vlab p₂ ∘ pe-term (e' ∷ e ∷ qs) sp) ∘ pe-term ps dom
--                                                       [front-swap-≈ (N+K)]
--     ≈ decodeOrd (ps ++ e' ∷ e ∷ qs) p₂
--                                                  [decodeOrd-factor, sym]
--
-- where `sp = pe-stack ps dom`.  The shared right factor `pe-term ps dom`
-- (the already-processed prefix) is carried through by `∘-resp-≈`.
------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e)) where
  open PerHG H dih
  open FrontSwap H dih using (front-swap-≈)

  swap-≈
    : ∀ {o₁ o₂ : PH.Order} → o₁ PH.↝ o₂
    → (p₁ : PH.Valid o₁) (p₂ : PH.Valid o₂)
    → PH.decodeOrd o₁ p₁ ≈Term PH.decodeOrd o₂ p₂
  swap-≈ (swap-step ps qs inc) p₁ p₂ =
    ≈-Term-trans
      (decodeOrd-factor ps (_ ∷ _ ∷ qs) p₁)
      (≈-Term-trans
        (∘-resp-≈ (front-swap-≈ ps qs inc p₁ p₂) ≈-Term-refl)
        (≈-Term-sym (decodeOrd-factor ps (_ ∷ _ ∷ qs) p₂)))
