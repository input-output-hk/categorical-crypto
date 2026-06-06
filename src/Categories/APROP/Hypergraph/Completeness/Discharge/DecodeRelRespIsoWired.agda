-- NOT `--safe` (has postulates), but now contains NO FALSE postulate.
--
-- This connects the order-theory wiring (`IsoInvarianceWiring`) to the
-- ACTUAL completeness lemma `decode-rel-resp-iso`, consuming the real
-- PRUNED iso `⟪f⟫ ≅ᴴ ⟪g⟫` NATIVELY.  The previous version needed a
-- false bridge `iso-T⇒F : ⟪f⟫ ≅ᴴ ⟪g⟫ → ⟪f⟫F ≅ᴴ ⟪g⟫F` because the
-- decoder ran on the unpruned `⟪f⟫F`.  That is now GONE: we decode the
-- PRUNED graph via `decode-attempt-LinearP` (totality on `Translation.⟪_⟫`,
-- proven postulate-free in `DecodeAttemptLinearP`), so the wiring is
-- instantiated at `⟪f⟫` and the hypothesis applies directly.
--
--   iso : ⟪f⟫ ≅ᴴ ⟪g⟫
--     ─(Lemma A)→ connectivity ─→ order-invariance
--     ─→ decodeOrd iso-invariance       [IsoInvarianceWiring, at ⟪f⟫]
--     ─(boundary bridge)→ decodeP iso-invariance
--     ─(F-agreement)→ decode-rel iso-invariance
--
-- `decodeP` is the genuine pruned decoder (uses `decode-attempt-LinearP`).
--
-- The CONCRETE order decoder `IW.PerHG.decodeOrd` is genuinely
-- load-bearing here: `decodeP f` *is* `decodeOrd ⟪f⟫ (range nE)` modulo
-- the boundary `subst₂` (the `decodeP-≡-decodeOrd-range` lemma is a real
-- proof, via the algorithm-reduction extraction lemma).  The former
-- standalone postulate `wiring⇒decodeP-resp-iso` is GONE: `decodeP-resp-iso`
-- is now a REAL PROOF consuming `IW.decode-ord-resp-iso` directly (with the
-- validity witness threaded from totality), leaving only the single,
-- clearly isolated `decodeOrd-boundary-resp-≈` residual — pure
-- `subst₂`-transport algebra plus the `permute`-proof-irrelevance (the
-- TRUE Kelly faithfulness residual that gates the final-permute throughout
-- this development).
{-# OPTIONS --with-K #-}

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)
open import Categories.FreeMonoidal using (Symm)

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelRespIsoWired
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig)) where

open APROP sig
open import Categories.APROP.Hypergraph.Completeness.Discharge.ObjUIP

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (decode-attempt; process-edges; process-all-edges; extract-exact)
open import Categories.APROP.Hypergraph.Completeness.Permute sig
  using (permute-via-vlab)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP; ⟪⟫-LinearP)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW
import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceConcrete sig as IC
import Categories.APROP.Hypergraph.Completeness.Discharge.SwapStep sig as SS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeTail sig as RIT
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeEmptyTail sig as RET
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
open import Categories.APROP.Hypergraph.HomTermInvariant sig using (⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)
open import Categories.APROP.Hypergraph.Completeness.Discharge.FinOrderNoInv sig
  using (fin-order-NoInv-⟪⟫)

-- The Kelly faithfulness residual type, from `PermuteCoherence.Faithfulness`.
-- We postulate a fresh value of it (the explicit Kelly axiom).  This module is
-- now `--with-K` (the completeness chain was switched off the `--without-K`
-- discipline, which bought nothing for the already-`--with-K` top theorem
-- `CompletenessFull` and only forced K-free re-derivation of the `--with-K`
-- coherence machinery via co-infectivity).
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Nullary using (¬_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂)

import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeOrdBoundary sig as DOB
import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelDecodeP sig as DRDP

------------------------------------------------------------------------
-- The pruned decoder.  Genuinely built from the (postulate-free) pruned
-- totality `decode-attempt-LinearP`, with the boundary `subst₂` to the
-- user-facing type, exactly as the existing `decode` does for the
-- unpruned graph.
------------------------------------------------------------------------

decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
         (proj₁ (decode-attempt-LinearP f))

------------------------------------------------------------------------
-- Algorithm-reduction extraction.  From a successful `decode-attempt H`,
-- recover (a) a validity witness `v : Valid H (range nE)` and (b) the
-- propositional fact that the returned term *is* `decodeOrd H (range nE)
-- v`.  This is `decode-attempt-perm-from-just` strengthened to also
-- expose the term equality, via the SAME `with`-reduction of the
-- algorithm — so no `permute`-proof-irrelevance is needed: the perm
-- witness `v` is literally the one the algorithm computed.
--
-- `decodeOrd H (range nE) v = permute-via-vlab vlab v ∘
--    proj₂ (process-edges H (range nE) dom)`, and
--    `process-edges H (range nE) = process-all-edges H` definitionally;
-- `decode-attempt H` returns `permute-via-vlab vlab perm ∘ process-term`
-- with `process-term = proj₂ (process-all-edges H dom)` and `perm` the
-- `extract-exact` result.  Choosing `v = perm` makes the two equal.
------------------------------------------------------------------------

decode-attempt⇒decodeOrd-range
  : (H : Hypergraph FlatGen)
  → (dih : ∀ {e} → ¬ (Dep H e e))
  → (t : HomTerm (unflatten (domL H)) (unflatten (codL H)))
  → decode-attempt H ≡ just t
  → Σ[ v ∈ IW.PerHG.Valid H dih (range (Hypergraph.nE H)) ]
       t ≡ IW.PerHG.decodeOrd H dih (range (Hypergraph.nE H)) v
decode-attempt⇒decodeOrd-range H dih t eq
    with process-all-edges H (Hypergraph.dom H)
... | s_final , process-term
    with extract-exact (Hypergraph.cod H) s_final
...    | just perm
       with eq
...       | refl = perm , refl
decode-attempt⇒decodeOrd-range H dih t eq
    | s_final , process-term | nothing with eq
... | ()

------------------------------------------------------------------------
-- `decodeP f` *is* `decodeOrd ⟪f⟫ (range nE)` modulo the boundary
-- `subst₂`.  Real proof: `decodeP f` is the `subst₂`-transport of
-- `proj₁ (decode-attempt-LinearP f)`, and the extraction lemma above
-- rewrites that to `decodeOrd ⟪f⟫ (range nE) (vrange f)`.
------------------------------------------------------------------------

-- The validity witness for `f`'s natural order, extracted from totality.
-- The `Dep`-irreflexivity witness for `⟪f⟫` is the proven
-- `DepIrrefl.dep-irrefl-⟪⟫ f`.
vrange : ∀ {A B} (f : HomTerm A B)
       → IW.PerHG.Valid ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫))
vrange f =
  proj₁ (decode-attempt⇒decodeOrd-range ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
           (proj₁ (decode-attempt-LinearP f))
           (proj₂ (decode-attempt-LinearP f)))

decodeP-≡-decodeOrd-range
  : ∀ {A B} (f : HomTerm A B)
  → decodeP f
    ≡ subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
             (IW.PerHG.decodeOrd ⟪ f ⟫ (dep-irrefl-⟪⟫ f) (range (Hypergraph.nE ⟪ f ⟫)) (vrange f))
decodeP-≡-decodeOrd-range f =
  cong (subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f)))
       (proj₂ (decode-attempt⇒decodeOrd-range ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
                 (proj₁ (decode-attempt-LinearP f))
                 (proj₂ (decode-attempt-LinearP f))))

------------------------------------------------------------------------
-- The two honest bridging postulates (both TRUE).
------------------------------------------------------------------------

-- (F) Structural ↔ pruned-algorithmic decoder agreement.  The pruned
-- analogue of the existing `decode-rel-≈-decode` Build field: the
-- dispatcher proven in `Discharge.DecodeRelDecodeP` (constructive induction
-- on `f` via `DecoderAgreementSafe.WithAssumptions` + the pruned/unpruned
-- shape bridge).  `DRDP.decodeP f` is DEFINITIONALLY identical to the local
-- `decodeP f` (both are the `subst₂`-transport of
-- `proj₁ (decode-attempt-LinearP f)`), so the result has exactly the type
-- below.
-- `DRDP.decode-rel-≈-decodeP` is parameterised by the two shared K-inputs
-- (`objUIP` + the Kelly `FaithfulnessResidual`): the unpruned shape
-- residuals it consumes are the lemmas
-- `Sub.DecodeComposeShape.decode-∘-shape-inner` /
-- `Sub.DecodeTensorShape.decode-⊗-shape-inner`, both of which take those
-- two inputs.  We supply our own `objUIP`/`K-faithfulness` below (the
-- binding is placed after they enter scope), exactly as
-- `run-interchange-⟪⟫`/`decodeP-resp-iso` thread them.

-- (decoder-boundary bridge) `Discharge.DecodeOrdBoundary` discharges the
-- decoder-boundary obligation GIVEN the TWO explicit K-inputs below:
--   * `K-faithfulness : FaithfulnessResidual` — the TRUE Kelly residual
--     that gates the final permute throughout this development (a value of
--     the `--without-K` record, postulated fresh here — NOT the `--with-K`
--     `KellyCoherence`);
--   * `objUIP` — uniqueness-of-identity-proofs on `ObjTerm`.
-- `DecodeOrdBoundary.decodeOrd-boundary-resp-≈` discharges everything else
-- (the two same-↭ final permutes agree via `eval-rigid` + K; the boundary
-- transport is pure `subst₂` algebra under UIP).
postulate
  K-faithfulness : FaithfulnessResidual

-- objUIP: UIP on `ObjTerm` from `DecidableEquality X` (Hedberg), via
-- `Discharge.ObjUIP`.  (`ObjTerm` does not depend on the variant, so
-- `{Symm}` is given explicitly.)
objUIP : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
objUIP = ObjUIP.objUIP′ {Symm} _≟X_

-- (F) Structural ↔ pruned-algorithmic decoder agreement, with the two
-- shared K-inputs threaded in (mirrors how `run-interchange-⟪⟫` /
-- `decodeP-resp-iso` below supply `objUIP`/`K-faithfulness`).  `DRDP.decodeP
-- f` is DEFINITIONALLY identical to the local `decodeP f`.
decode-rel-≈-decodeP : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP = DRDP.decode-rel-≈-decodeP objUIP K-faithfulness

-- (N / interchange residual) The per-swap `RunInterchange` witness that
-- `SwapStep.swap-≈` consumes: for an adjacent INDEPENDENT pair of front
-- edges, running them in the swapped order equals running them in the
-- original order followed by a reshuffle.  This is the genuine
-- symmetric-monoidal interchange-axiom content (`σ ∘ (f ⊗ g) ≈ (g ⊗ f) ∘ σ`
-- on the two disjoint edge boxes).  Supplied at `H = ⟪f⟫` with the TRUE
-- Kelly residual and the VERTEX-level `Unique (cod ⟪f⟫)` (from
-- `⟪_⟫-cod-unique`).
--
-- SPLIT into two ORTHOGONAL obligations (per the informal proof, §"The
-- per-swap step in detail"):
--
--   * `run-interchange₀-⟪⟫`    — the EMPTY-TAIL core (`qs := []`): the
--     genuine two-edge interchange at a single swap.  This is the
--     substantive Mac-Lane / `box-interchange` content (the block normal
--     form `A_e ⊗ A_e' ⊗ R`).
--   * `run-interchange-tail-⟪⟫` — the ORTHOGONAL tail extension: lifting
--     the empty-tail swap to an arbitrary suffix `qs`.  This is pure
--     decoder equivariance under stack permutation — no box / associator
--     content (see `Sub/StackEquivariance.agda`), via
--     `Sub/RunInterchangeTail.agda`'s `process-edges-equivariant`.
--
-- The general witness `run-interchange-⟪⟫` that the chain consumes is their
-- composite.
--
-- The EMPTY-TAIL core instantiates the generic
-- `RunInterchangeEmptyTail.run-interchange₀` (the 4-case firing split —
-- three cases trivial, both-fire reduced to the single box-M residual
-- `fire-mid-interchange`) at `H = ⟪f⟫`, with `Linear ⟪f⟫` supplied by
-- `⟪⟫-LinearP f`.  It bottoms out in the small box-M residuals
-- `fire-mid-interchange`, `fire-mid-equivariant`, `fire-locate-coherent`.
-- soundness: the EMPTY-TAIL core is fed the empty-tail swap-order reservoir
-- `Reservoir≤1 ⟪f⟫ (ps ++ e' ∷ e ∷ []) dom` (sourced below from the full
-- swap-order `↭ range` provenance via a prefix drop).
run-interchange₀-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
      (ps : SS.PerHG.Order ⟪ f ⟫ (dep-irrefl-⟪⟫ f))
      {e e' : Fin (Hypergraph.nE ⟪ f ⟫)}
      (inc : SS.PerHG.Incomp ⟪ f ⟫ (dep-irrefl-⟪⟫ f) e e')
  → SUR.Reservoir≤1 ⟪ f ⟫ (ps ++ e' ∷ e ∷ []) (Hypergraph.dom ⟪ f ⟫)
  → SS.FrontSwap.RunInterchange ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
      K-faithfulness (⟪ f ⟫-cod-unique) ps [] inc
run-interchange₀-⟪⟫ f ps inc res =
  RET.run-interchange₀ ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
    K-faithfulness (⟪ f ⟫-cod-unique) (⟪⟫-LinearP f) ps inc res

-- The tail extension instantiates the generic
-- `RunInterchangeTail.run-interchange-tail` (decoder stack-equivariance) at
-- `H = ⟪f⟫`, fed the full swap-order `↭ range` provenance.
run-interchange-tail-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
      (ps qs : SS.PerHG.Order ⟪ f ⟫ (dep-irrefl-⟪⟫ f))
      {e e' : Fin (Hypergraph.nE ⟪ f ⟫)}
      (inc : SS.PerHG.Incomp ⟪ f ⟫ (dep-irrefl-⟪⟫ f) e e')
  → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE ⟪ f ⟫)
  → SS.FrontSwap.RunInterchange ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
      K-faithfulness (⟪ f ⟫-cod-unique) ps [] inc
  → SS.FrontSwap.RunInterchange ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
      K-faithfulness (⟪ f ⟫-cod-unique) ps qs inc
run-interchange-tail-⟪⟫ f ps qs inc prov =
  RIT.run-interchange-tail ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
    K-faithfulness (⟪ f ⟫-cod-unique) (⟪⟫-LinearP f) ps qs inc prov

-- The general witness the chain consumes: now carries the SWAP-SITE
-- PROVENANCE `(ps ++ e' ∷ e ∷ qs) ↭ range nE`.  The full swap-order
-- reservoir is PROVEN from it by `StackUniqueReach.dom-reservoir-prov`
-- (with the `Linear ⟪f⟫` bound from `⟪⟫-LinearP f`); the EMPTY-TAIL
-- reservoir is the prefix-drop of that (the `++-assoc` re-bracketing of
-- `ps ++ e' ∷ e ∷ qs ≡ (ps ++ e' ∷ e ∷ []) ++ qs`).  NO false-as-stated
-- `∀ o` reservoir postulate is used anywhere on this path.
run-interchange-⟪⟫
  : ∀ {A B} (f : HomTerm A B)
      (ps qs : SS.PerHG.Order ⟪ f ⟫ (dep-irrefl-⟪⟫ f))
      {e e' : Fin (Hypergraph.nE ⟪ f ⟫)}
      (inc : SS.PerHG.Incomp ⟪ f ⟫ (dep-irrefl-⟪⟫ f) e e')
  → (ps ++ e' ∷ e ∷ qs) Perm.↭ range (Hypergraph.nE ⟪ f ⟫)
  → SS.FrontSwap.RunInterchange ⟪ f ⟫ (dep-irrefl-⟪⟫ f)
      K-faithfulness (⟪ f ⟫-cod-unique) ps qs inc
run-interchange-⟪⟫ f ps qs {e} {e'} inc prov =
  run-interchange-tail-⟪⟫ f ps qs inc prov
    (run-interchange₀-⟪⟫ f ps inc res-empty-tail)
  where
    -- Full swap-order reservoir, PROVEN from the `↭ range` provenance.
    res-full : SUR.Reservoir≤1 ⟪ f ⟫ (ps ++ e' ∷ e ∷ qs) (Hypergraph.dom ⟪ f ⟫)
    res-full =
      SUR.dom-reservoir-prov ⟪ f ⟫ (proj₂ (⟪⟫-LinearP f))
        (ps ++ e' ∷ e ∷ qs) prov

    -- Empty-tail reservoir = prefix drop of `qs`, after re-bracketing
    -- `ps ++ e' ∷ e ∷ qs ≡ (ps ++ e' ∷ e ∷ []) ++ qs`.
    res-empty-tail
      : SUR.Reservoir≤1 ⟪ f ⟫ (ps ++ e' ∷ e ∷ []) (Hypergraph.dom ⟪ f ⟫)
    res-empty-tail =
      SUR.reservoir-prefix ⟪ f ⟫ (ps ++ e' ∷ e ∷ []) qs (Hypergraph.dom ⟪ f ⟫)
        (subst (λ z → SUR.Reservoir≤1 ⟪ f ⟫ z (Hypergraph.dom ⟪ f ⟫))
               (assoc-eq) res-full)
      where
        assoc-eq : ps ++ e' ∷ e ∷ qs ≡ (ps ++ e' ∷ e ∷ []) ++ qs
        assoc-eq = sym (++-assoc ps (e' ∷ e ∷ []) qs)

------------------------------------------------------------------------
-- Iso-invariance of the pruned decoder, consuming the real pruned iso.
-- The wiring is genuinely load-bearing: `IW.decode-ord-resp-iso`
-- (= `↝*⇒≈ (connectivity …)` under the hood) appears in the proof term,
-- applied DIRECTLY to the hypothesis `iso : ⟪f⟫ ≅ᴴ ⟪g⟫`, with the
-- validity witness `vrange g` threaded from the totality lemma.  The
-- `decodeP ↔ decodeOrd` boundary equalities are the REAL lemma
-- `decodeP-≡-decodeOrd-range`; only `decodeOrd-boundary-resp-≈` remains
-- postulated.
------------------------------------------------------------------------

decodeP-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decodeP f ≈Term decodeP g
decodeP-resp-iso f g iso =
  subst₂ (λ a b → a ≈Term b)
         (sym (decodeP-≡-decodeOrd-range f))
         (sym (decodeP-≡-decodeOrd-range g))
         (DOB.decodeOrd-boundary-resp-≈ K-faithfulness objUIP
            f g iso (vrange f) (vrange g) vH wiring≈)
  where
    -- The wiring's iso-invariance, fed J = ⟪g⟫'s natural-order validity,
    -- the two `Dep`-irreflexivity witnesses (`dep-irrefl-⟪⟫`) and the two
    -- natural-order no-inversion witnesses (`fin-order-NoInv-⟪⟫`).  Sourced
    -- from `IsoInvarianceConcrete` (which feeds the real `SwapStep.swap-≈`,
    -- `SwapValidity.swap-validity`, `WiringLemmas.NoInv-τ`,
    -- `FinOrderNoInv.fin-order-NoInv-⟪⟫`, `IsoTransport.iso-transport`).
    res = IC.decode-ord-resp-iso iso
            (dep-irrefl-⟪⟫ f) (dep-irrefl-⟪⟫ g)
            (⟪⟫-LinearP f)
            K-faithfulness (⟪ f ⟫-cod-unique) (⟪ g ⟫-cod-unique)
            objUIP
            (run-interchange-⟪⟫ f)
            (fin-order-NoInv-⟪⟫ f) (fin-order-NoInv-⟪⟫ g)
            (vrange g)
    vH  = proj₁ res
    wiring≈ = proj₂ res

------------------------------------------------------------------------
-- The ACTUAL `decode-rel-resp-iso` (Translation-iso hypothesis, the type
-- consumed by `CompletenessFull`/`WithAssumptions`), now wired to the
-- order-theory core through `IsoInvarianceWiring` — with NO false
-- postulate.  (`decode-rel` is translation-agnostic, so no edit to the
-- existing decoder/cluster is required.)
------------------------------------------------------------------------

decode-rel-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decode-rel f ≈Term decode-rel g
decode-rel-resp-iso f g iso =
  ≈-Term-trans (decode-rel-≈-decodeP f)
    (≈-Term-trans (decodeP-resp-iso f g iso)
                  (≈-Term-sym (decode-rel-≈-decodeP g)))
