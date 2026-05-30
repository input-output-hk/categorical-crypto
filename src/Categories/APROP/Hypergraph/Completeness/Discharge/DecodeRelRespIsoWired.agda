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
{-# OPTIONS --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelRespIsoWired
  (sig : APROPSignature) where

open APROP sig

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
  using (decode-attempt-LinearP)

import Categories.APROP.Hypergraph.Completeness.Discharge.IsoInvarianceWiring sig as IW

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂)

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
  → (t : HomTerm (unflatten (domL H)) (unflatten (codL H)))
  → decode-attempt H ≡ just t
  → Σ[ v ∈ IW.PerHG.Valid H (range (Hypergraph.nE H)) ]
       t ≡ IW.PerHG.decodeOrd H (range (Hypergraph.nE H)) v
decode-attempt⇒decodeOrd-range H t eq
    with process-all-edges H (Hypergraph.dom H)
... | s_final , process-term
    with extract-exact (Hypergraph.cod H) s_final
...    | just perm
       with eq
...       | refl = perm , refl
decode-attempt⇒decodeOrd-range H t eq
    | s_final , process-term | nothing with eq
... | ()

------------------------------------------------------------------------
-- `decodeP f` *is* `decodeOrd ⟪f⟫ (range nE)` modulo the boundary
-- `subst₂`.  Real proof: `decodeP f` is the `subst₂`-transport of
-- `proj₁ (decode-attempt-LinearP f)`, and the extraction lemma above
-- rewrites that to `decodeOrd ⟪f⟫ (range nE) (vrange f)`.
------------------------------------------------------------------------

-- The validity witness for `f`'s natural order, extracted from totality.
vrange : ∀ {A B} (f : HomTerm A B) → IW.PerHG.Valid ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫))
vrange f =
  proj₁ (decode-attempt⇒decodeOrd-range ⟪ f ⟫
           (proj₁ (decode-attempt-LinearP f))
           (proj₂ (decode-attempt-LinearP f)))

decodeP-≡-decodeOrd-range
  : ∀ {A B} (f : HomTerm A B)
  → decodeP f
    ≡ subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
             (IW.PerHG.decodeOrd ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫)) (vrange f))
decodeP-≡-decodeOrd-range f =
  cong (subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f)))
       (proj₂ (decode-attempt⇒decodeOrd-range ⟪ f ⟫
                 (proj₁ (decode-attempt-LinearP f))
                 (proj₂ (decode-attempt-LinearP f))))

------------------------------------------------------------------------
-- The two honest bridging postulates (both TRUE).
------------------------------------------------------------------------

-- (F) Structural ↔ pruned-algorithmic decoder agreement.  The pruned
-- analogue of the existing `decode-rel-≈-decode` Build field; true,
-- postulated here.
postulate
  decode-rel-≈-decodeP : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f

-- (decoder-boundary bridge, RESIDUAL) The only remaining gap, now stated
-- PURELY at the `decodeOrd` level (no `decodeP`): it relates the two
-- decodings of ⟪f⟫ in its natural order under DIFFERENT validity
-- witnesses (`vH` from the wiring's `order-invariant`, `vrange f` from
-- the totality lemma), then transports the boundary `subst₂` from the
-- wiring's iso-boundary (`IW.domL-iso`/`IW.codL-iso`, equating ⟪f⟫'s and
-- ⟪g⟫'s boundaries) to the user-facing one (`⟪⟫-domL`/`⟪⟫-codL`,
-- equating to `flatten`).  The two validity witnesses are PROOFS of the
-- SAME `↭`, so their final permutes agree only up to the TRUE Kelly
-- faithfulness residual `permute-≈Term-coherence` that gates the
-- final-permute throughout this development; combined with pure
-- `subst₂`-transport algebra, this is the entire content.
postulate
  decodeOrd-boundary-resp-≈
    : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
        (vH : IW.PerHG.Valid ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫)))
    → ( subst₂ HomTerm (cong unflatten (IW.domL-iso iso)) (cong unflatten (IW.codL-iso iso))
          (IW.PerHG.decodeOrd ⟪ g ⟫ (range (Hypergraph.nE ⟪ g ⟫)) (vrange g))
        ≈Term
        IW.PerHG.decodeOrd ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫)) vH )
    → ( subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
          (IW.PerHG.decodeOrd ⟪ f ⟫ (range (Hypergraph.nE ⟪ f ⟫)) (vrange f))
        ≈Term
        subst₂ HomTerm (cong unflatten (⟪⟫-domL g)) (cong unflatten (⟪⟫-codL g))
          (IW.PerHG.decodeOrd ⟪ g ⟫ (range (Hypergraph.nE ⟪ g ⟫)) (vrange g)) )

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
         (decodeOrd-boundary-resp-≈ f g iso vH wiring≈)
  where
    -- The wiring's iso-invariance, fed J = ⟪g⟫'s natural-order validity.
    res = IW.decode-ord-resp-iso iso (vrange g)
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
