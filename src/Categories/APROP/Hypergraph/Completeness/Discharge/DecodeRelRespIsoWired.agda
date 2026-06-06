-- Connects the order-theory wiring (`IsoInvarianceWiring`) to the
-- completeness lemma `decode-rel-resp-iso`, consuming the pruned iso
-- `⟪f⟫ ≅ᴴ ⟪g⟫` natively (the decoder runs on the pruned graph via
-- `decode-attempt-LinearP`):
--
--   iso : ⟪f⟫ ≅ᴴ ⟪g⟫
--     ─(Lemma A)→ connectivity ─→ order-invariance
--     ─→ decodeOrd iso-invariance       [IsoInvarianceWiring, at ⟪f⟫]
--     ─(boundary bridge)→ decodeP iso-invariance
--     ─(F-agreement)→ decode-rel iso-invariance
--
-- `decodeP f` is `decodeOrd ⟪f⟫ (range nE)` modulo the boundary `subst₂`
-- (the `decodeP-≡-decodeOrd-range` lemma).  The chain is axiom-free: the
-- Kelly residual `K-faithfulness` is the proven
-- `FaithfulnessInductive.faithfulness`.
{-# OPTIONS --safe --without-K #-}

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
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.RunInterchangeEmptyTail sig _≟X_ as RET
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.StackUniqueReach sig as SUR
open import Categories.APROP.Hypergraph.HomTermInvariant sig using (⟪_⟫-cod-unique)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DepIrrefl sig
  using (dep-irrefl-⟪⟫)
open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)
open import Categories.APROP.Hypergraph.Completeness.Discharge.FinOrderNoInv sig
  using (fin-order-NoInv-⟪⟫)

-- The Kelly faithfulness residual type and its proven value
-- (`FaithfulnessInductive.faithfulness`), bound as `K-faithfulness`.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)
open import Categories.PermuteCoherence.FaithfulnessInductive asFreeMonoidalData _≟X_
  using () renaming (faithfulness to K-faithfulness)

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
import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelDecodeP sig _≟X_ as DRDP

------------------------------------------------------------------------
-- The pruned decoder: the pruned totality `decode-attempt-LinearP` plus
-- the boundary `subst₂` to the user-facing type.
------------------------------------------------------------------------

decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
         (proj₁ (decode-attempt-LinearP f))

------------------------------------------------------------------------
-- Algorithm-reduction extraction.  From a successful `decode-attempt H`,
-- recover a validity witness `v : Valid H (range nE)` together with the
-- fact that the returned term IS `decodeOrd H (range nE) v` (taking `v`
-- to be the `extract-exact` result the algorithm computed, so no
-- proof-irrelevance is needed).
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
-- `decodeP f` is `decodeOrd ⟪f⟫ (range nE)` modulo the boundary `subst₂`.
------------------------------------------------------------------------

-- The validity witness for `f`'s natural order, extracted from totality.
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
-- The two bridging inputs: `decode-rel-≈-decodeP` (decoder agreement)
-- and `run-interchange-⟪⟫` (the interchange residual).
------------------------------------------------------------------------

-- objUIP: UIP on `ObjTerm` from `DecidableEquality X` (Hedberg).
objUIP : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
objUIP = ObjUIP.objUIP′ {Symm} _≟X_

-- (F) Structural ↔ pruned-algorithmic decoder agreement.  `DRDP.decodeP f`
-- is definitionally the local `decodeP f`.
decode-rel-≈-decodeP : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP = DRDP.decode-rel-≈-decodeP objUIP K-faithfulness

-- (N) The per-swap `RunInterchange` witness `SwapStep.swap-≈` consumes —
-- the interchange axiom on the two disjoint edge boxes.  Split into two
-- orthogonal parts whose composite is `run-interchange-⟪⟫`:
--   * `run-interchange₀-⟪⟫` — the EMPTY-TAIL core (`qs := []`): the
--     substantive two-edge box-M interchange.
--   * `run-interchange-tail-⟪⟫` — the tail extension to a suffix `qs`,
--     pure decoder equivariance (no box content).
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

-- The tail extension, fed the full swap-order `↭ range` provenance.
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

-- The general witness the chain consumes, carrying the swap-site
-- provenance `(ps ++ e' ∷ e ∷ qs) ↭ range nE`.  The full swap-order
-- reservoir is proven from it (`dom-reservoir-prov`); the empty-tail
-- reservoir is its prefix drop.
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
    res-full : SUR.Reservoir≤1 ⟪ f ⟫ (ps ++ e' ∷ e ∷ qs) (Hypergraph.dom ⟪ f ⟫)
    res-full =
      SUR.dom-reservoir-prov ⟪ f ⟫ (proj₂ (⟪⟫-LinearP f))
        (ps ++ e' ∷ e ∷ qs) prov

    -- Prefix drop of `qs`, after re-bracketing.
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
-- Iso-invariance of the pruned decoder.  `IW.decode-ord-resp-iso` is
-- applied directly to `iso`, with the boundary equalities supplied by
-- `decodeP-≡-decodeOrd-range` and `DecodeOrdBoundary.decodeOrd-boundary-resp-≈`.
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
    -- The wiring's iso-invariance (from `IsoInvarianceConcrete`), fed
    -- `vrange g`, the two `dep-irrefl-⟪⟫` and `fin-order-NoInv-⟪⟫` witnesses.
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
-- `decode-rel-resp-iso` (the type consumed by `CompletenessFull`),
-- wired to the order-theory core via `decode-rel-≈-decodeP` + `decodeP-resp-iso`.
------------------------------------------------------------------------

decode-rel-resp-iso
  : ∀ {A B} (f g : HomTerm A B) → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → decode-rel f ≈Term decode-rel g
decode-rel-resp-iso f g iso =
  ≈-Term-trans (decode-rel-≈-decodeP f)
    (≈-Term-trans (decodeP-resp-iso f g iso)
                  (≈-Term-sym (decode-rel-≈-decodeP g)))
