{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Part (I) of the completeness proof: the structural ↔ pruned-algorithmic
-- decoder NORMAL-FORM agreement
--
--     decode-rel-≈-decodeP : ∀ {A B} (f : HomTerm A B)
--                          → decode-rel f ≈Term decodeP f
--
-- currently postulated wholesale (field `decode-rel-≈-decodeP`) in
-- `Discharge.DecodeRelRespIsoWired`.  This module proves it from a
-- STRICTLY-NARROWER residual surface, by *importing the existing
-- `--with-K` reduction machinery* for the UNPRUNED decoder `decode`
-- (previously walled off while this module was `--without-K`).
--
-- ## The reduction (the whole point of this module)
--
-- The key observation — verified by Agda, see `decodeP-≈-decode` below —
-- is that for EVERY ATOMIC constructor X (Agen, σ, id, λ⇒, λ⇐, ρ⇒, ρ⇐,
-- α⇒, α⇐):
--
--     decodeP X  ≡  decode X     (DEFINITIONALLY, by `refl`)
--
-- because the pruned translation `Translation.⟪_⟫` and the unpruned
-- `FromAPROP.⟪_⟫` are byte-for-byte identical on every HomTerm
-- constructor EXCEPT `∘` (pruning removes only vertices, never edges; it
-- only changes the `∘` case, `hComposeP` vs `hCompose`).  Consequently
-- `decode-attempt-LinearP X ≡ decode-attempt-Linear X` and the boundary
-- proofs `⟪⟫-{dom,cod}L X` agree on the nose for all non-`∘` X, so the
-- whole `subst₂`-transport `decodeP X` and `decode X` coincide.
--
-- This collapses the ENTIRE pruned residual surface to:
--
--   (U)  the UNPRUNED dispatcher `decode-rel-≈-decode`, assembled here
--        from the *shared* `--with-K` residual records
--        (`DecodeShapeResiduals`, `RhoShapeResidual`,
--        `DecodeRoundtripAgenSigma.Residuals`) + the two α atomics — the
--        SAME residual surface that the unpruned completeness proof
--        (`FromAssumptions.DecodeRelDecode`) and the interchange chain
--        already depend on; AND
--
--   (B)  the pruned-vs-unpruned BRIDGE on the two recursive constructors:
--          `decodeP-≈-decode-∘ : decodeP (g ∘ f) ≈Term decode (g ∘ f)`
--          `decodeP-≈-decode-⊗ : decodeP (f ⊗₁ g) ≈Term decode (f ⊗₁ g)`
--        These are the ONLY genuinely-new pruned obligations; every
--        ATOMIC case of the bridge is `refl` (see `decodeP-≈-decode`).
--
-- The dispatcher is then a one-liner:
--
--     decode-rel-≈-decodeP f
--       = decode-rel f  ≈⟨ decode-rel-≈-decode f ⟩  decode f
--                       ≈⟨ sym (decodeP-≈-decode f) ⟩  decodeP f
--
-- ## The bridge bottoms out in `swap-atom-aligned`
--
-- `decodeP-≈-decode-⊗ f g` relates `decode-attempt-hTensor ⟪f⟫ₚ ⟪g⟫ₚ`
-- to `decode-attempt-hTensor ⟪f⟫ ⟪g⟫` — the SAME `decode-attempt-hTensor`
-- function applied to the pruned vs unpruned sub-translations (tensor is
-- NOT pruned: `⟪ f ⊗₁ g ⟫ₚ = hTensor ⟪f⟫ₚ ⟪g⟫ₚ`, same `hTensor` as the
-- unpruned side).  Modulo the recursive sub-bridges, its term-level
-- content is `decode-attempt-hTensor`'s decomposition of the disjoint
-- G-edges-then-K-edges block back into the tensor `decode f ⊗₁ decode g`
-- — i.e. a reordering of INDEPENDENT (disjoint-stack) edges through the
-- `unflatten-++-≅` wrappers.  That is exactly the per-swap independent-
-- edge Mac-Lane chase isolated as `swap-atom-aligned`
-- (`ProcessTermAligned2Residual.swap-atom-aligned`), the SAME kernel as
-- the interchange side's `block-nf`/`swap-atom-aligned` residual.  The
-- mechanized reduction of `decodeP-≈-decode-⊗` to `swap-atom-aligned`
-- needs the still-missing term-tracking variants of the
-- `process-edges-↑ˡ-on-mixed` / `process-edges-↑ʳ-on-perm` helpers in
-- `DecodeAttempt.agda` (see `DecodeShape.agda`, Section 4), which this
-- module must not edit; hence `decodeP-≈-decode-⊗` is left as a residual.
--
-- `decodeP-≈-decode-∘` is the pruned `∘` bridge: `hComposeP` vs
-- `hCompose`.  Its constructive content is the `pe-term-++`-style
-- block-decomposition of `process-edges` on `hComposeP`, parallel to the
-- unpruned `decode-∘-shape-inner` (`DecodeShape.agda`).
--
-- ## Final residual surface of `decode-rel-≈-decodeP` (transitive)
--
--   * (U) `DecodeShapeResiduals`         — NO LONGER A POSTULATE.  Now a
--         DEFINITION (`Wired.decodeShapeResiduals`) consuming the two
--         PROVEN, postulate-free shape lemmas
--         `Sub.DecodeComposeShape.decode-∘-shape-inner` /
--         `Sub.DecodeTensorShape.decode-⊗-shape-inner` (parameterised by
--         `objUIP` + `K : FaithfulnessResidual`, threaded from
--         `DecodeRelRespIsoWired`'s discharged `objUIP` / postulated
--         `K-faithfulness`).
--   * (U) `RhoShapeResidual`             — PROVEN (postulate-free)
--   * (U) `DecodeRoundtripAgenSigma.Residuals` (K) — `decode-{Agen,σ}-collapse`
--   * (U) `decode-rel-≈-decode-α{⇒,⇐}`   — NO LONGER POSTULATES.  Now
--         DEFINITIONS (`Wired.decode-rel-≈-decode-α{⇒,⇐}`) consuming the
--         PROVEN, postulate-free collapses
--         `Sub.DecodeAgenSigmaShape.decode-α{⇒,⇐}-collapse objUIP K`.
--   * (B) `decodeP-≈-decode-∘`           — pruned `∘` bridge
--   * (B) `decodeP-≈-decode-⊗`           — pruned `⊗` bridge
--
-- All of (U) is the SHARED unpruned/interchange residual surface (no new
-- trust beyond what the `decode`-side proof already assumes).  The two (B)
-- bridges are factored through `decodePShapeResiduals`, which is NO LONGER
-- A POSTULATE: it is now a DEFINITION (`Wired.decodePShapeResiduals`)
-- consuming the two PROVEN, postulate-free PRUNED shape lemmas
-- `Sub.DecodeComposePruned.decodeP-∘-shape` /
-- `Sub.DecodeTensorPruned.decodeP-⊗-shape` (the `decodeP` mirrors of the
-- PROVEN unpruned `decode-{∘,⊗}-shape-inner`, parameterised by
-- `objUIP` + `K`).  The pruned ⊗-shape reuses the SAME `hTensor` block
-- machinery as the unpruned proof (tensor is not pruned), so it consumes
-- NO `nf-bracket` / `swap-atom-aligned` kernel.
--
-- LIVE postulates in THIS module: NONE.  The postulate block is EMPTY.
-- (`decodeShapeResiduals`, `agenSigmaResiduals`, `decodePShapeResiduals`
-- AND the two α atomics `decode-rel-≈-decode-α{⇒,⇐}` are ALL now
-- DEFINITIONS in `module Wired`, consuming the proven, postulate-free
-- shape / single-edge-collapse / α-collapse / pruned-shape lemmas.)  The
-- transitive live trust surface of part (I) is thus {K-faithfulness,
-- nf-bracket}.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelDecodeP
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; domL-hId; codL-hId)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeAttemptLinearP sig
  using (decode-attempt-LinearP)

-- The unpruned algorithmic decoder and the `--with-K` reduction
-- machinery for it (previously walled off; importable now that this
-- module is `--with-K`).
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (decode; decode-attempt-hId)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using ( DecoderAgreementAssumptions; module WithAssumptions
        ; Ty-Agen; Ty-σ; Ty-id; Ty-λ⇒; Ty-λ⇐; Ty-ρ⇒; Ty-ρ⇐; Ty-α⇒; Ty-α⇐
        ; Ty-∘-shape; Ty-⊗-shape
        ; unapply-Agen; unapply-σ; unapply-α⇒; unapply-α⇐
        ; unapply-∘-shape; unapply-⊗-shape )
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeShape sig
  using (DecodeShapeResiduals; module DecodeShapeResiduals)
-- The two PROVEN, postulate-free shape lemmas (the ∘-side and the ⊗-side),
-- each in a top-level `module _ (objUIP)(Kf)`.  We consume them below to
-- turn `decodeShapeResiduals` from a postulate into a DEFINITION.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposeShape sig as DCS
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorShape sig as DTS
-- The two PROVEN, postulate-free PRUNED shape lemmas (the ∘-side and the
-- ⊗-side), each in a top-level `module _ (objUIP)(Kf)`.  We consume them
-- below to turn `decodePShapeResiduals` from a postulate into a DEFINITION.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeComposePruned sig as DCP
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeTensorPruned sig as DTP
-- The PROVEN, postulate-free single-edge collapses `decode-{Agen,σ}-collapse`
-- (also in a top-level `module _ (objUIP)(Kf)`).  Consumed below to turn
-- `agenSigmaResiduals` from a postulate into a DEFINITION.
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.DecodeAgenSigmaShape sig as DAS
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho as Rho
module Rho-sig = Rho sig
open Rho-sig using (RhoShapeResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma sig
  using (Residuals; module Residuals)
-- The pruned shape residuals + factoring assemblers (this module's
-- `decodeP` and the new module's `decodeP` are DEFINITIONALLY identical;
-- see §(B) below).
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.ProcessEdgesTermShape sig
  using (DecodePShapeResiduals; module Assemble)

-- The Kelly faithfulness residual type, threaded (together with `objUIP`)
-- from `DecodeRelRespIsoWired` down to the two proven shape lemmas.
open import Categories.PermuteCoherence.Faithfulness asFreeMonoidalData
  using (FaithfulnessResidual)

open import Categories.Category using (Category)
open import Data.Product using (proj₁)
open import Data.List using (List)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; subst₂)

--------------------------------------------------------------------------------
-- The pruned decoder `decodeP`, re-stated here *verbatim* from
-- `Discharge.DecodeRelRespIsoWired.decodeP` (same definition: the boundary
-- `subst₂`-transport of `proj₁ (decode-attempt-LinearP f)`, using the
-- pruned translation's `⟪⟫-{dom,cod}L`).  We replicate the definition
-- rather than importing it because the host module
-- `DecodeRelRespIsoWired` transitively depends on `FinOrderNoInv`, which
-- currently does not typecheck on this branch (a pre-existing error
-- unrelated to part (I)); `decodeP` itself only needs
-- `decode-attempt-LinearP` and the boundary lemmas, none of which touch
-- `FinOrderNoInv`.  The statement below is therefore identical to the
-- target postulate `DecodeRelRespIsoWired.decode-rel-≈-decodeP`.
--------------------------------------------------------------------------------

decodeP : ∀ {A B} (f : HomTerm A B)
        → HomTerm (unflatten (flatten A)) (unflatten (flatten B))
decodeP {A} {B} f =
  subst₂ HomTerm (cong unflatten (⟪⟫-domL f)) (cong unflatten (⟪⟫-codL f))
         (proj₁ (decode-attempt-LinearP f))

private
  module FM = Category FreeMonoidal

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- ## (U) The shared UNPRUNED residual surface.
--
-- `decode-rel-≈-decode` (the unpruned dispatcher) is assembled below from
-- the SAME `--with-K` residual records the unpruned completeness proof
-- (`FromAssumptions.DecodeRelDecode`) and the interchange chain depend
-- on.  We surface those records (plus the two α atomics) as top-level
-- `postulate`s so that `decode-rel-≈-decodeP` is a TOP-LEVEL definition
-- with the expected parameter-free signature (ready to wire into
-- `DecodeRelRespIsoWired`), while keeping the trust surface explicitly
-- the shared unpruned one.
--
-- (These are NOT new trust: each is one of the residual records already
-- assumed by the `decode`-side proof.  `decode-rel-≈-decode-α{⇒,⇐}` are
-- the two atomic associator obligations passed as parameters of
-- `FromAssumptions.DecodeRelDecode.decode-rel-≈-decode-impl`.)
--------------------------------------------------------------------------------

-- (U/M) The two atomic associator obligations are NO LONGER POSTULATES.
-- They are now DEFINITIONS in `module Wired` below, derived from the
-- PROVEN, postulate-free single-edge-style collapses
-- `DAS.decode-α{⇒,⇐}-collapse objUIP K` (Sub.DecodeAgenSigmaShape):
-- `decode-rel (α⇒) = bridge (α⇒)` DEFINITIONALLY (DecodeRel.agda), so
-- each is `≈-Term-sym (decode-α{⇒,⇐}-collapse …)`.  This empties the
-- DecodeRelDecodeP postulate block entirely; the live trust surface of
-- the whole part-(I) chain is now exactly {K-faithfulness, nf-bracket}.

--------------------------------------------------------------------------------
-- ## (U/M) `rhoShapeResidual` — PROVEN (postulate-free).
--
-- `RhoShapeResidual` packages two PROPOSITIONAL `_≡_` characterisations:
--
--     decode-ρ⇒-shape A : decode (ρ⇒ {A})
--       ≡ subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
--                (decode (id {A ⊗₀ unit}))
--     decode-ρ⇐-shape A : decode (ρ⇐ {A})
--       ≡ subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
--                (decode (id {A ⊗₀ unit}))
--
-- These are PURE boundary-`subst₂` ALGEBRA, NOT process-edges content:
-- `⟪ ρ⇒ {A} ⟫ = hId (A ⊗₀ unit) = ⟪ id {A ⊗₀ unit} ⟫`, so
-- `decode-attempt-Linear (ρ⇒ {A})` and `decode-attempt-Linear (id {A ⊗₀ unit})`
-- are DEFINITIONALLY the SAME `decode-attempt-hId (A ⊗₀ unit)`.  The two
-- decoders therefore share the SAME inner term `proj₁ (…hId (A ⊗₀ unit))`
-- and differ ONLY in the boundary equations supplied to `decode`'s
-- `subst₂`.  For ρ⇒ those are
--
--     dom : ⟪⟫-domL (ρ⇒ {A}) = domL-hId (A ⊗₀ unit)              -- vs id: same
--     cod : ⟪⟫-codL (ρ⇒ {A}) = trans (codL-hId (A ⊗₀ unit)) r    -- vs id: codL-hId only
--
-- where `r = ++-identityʳ (flatten A)`.  The identity then follows from
-- the generic `subst₂`-over-`trans` split below, which is `--with-K`
-- (proved by `refl`-pattern, hence TRUE for ALL instances of its type;
-- no side condition needed — it is a UIP-level transport fact, not a
-- quantified hypergraph claim).
--------------------------------------------------------------------------------

private
  -- Generic: a `subst₂` whose cod equation factors as `trans q r`
  -- splits as the outer `r`-transport of the inner `q`-transport.
  -- (`--with-K`; TRUE for every `p`, `q`, `r`, `x`.)
  subst₂-cod-trans
    : ∀ {as as' bs bs' bs'' : List X}
        (p : as ≡ as') (q : bs ≡ bs') (r : bs' ≡ bs'')
        (x : HomTerm (unflatten as) (unflatten bs))
    → subst₂ HomTerm (cong unflatten p) (cong unflatten (trans q r)) x
      ≡ subst₂ HomTerm refl (cong unflatten r)
               (subst₂ HomTerm (cong unflatten p) (cong unflatten q) x)
  subst₂-cod-trans refl refl refl x = refl

  -- Symmetric: a `subst₂` whose dom equation factors as `trans q r`.
  subst₂-dom-trans
    : ∀ {as as' as'' bs bs' : List X}
        (q : as ≡ as') (r : as' ≡ as'') (p : bs ≡ bs')
        (x : HomTerm (unflatten as) (unflatten bs))
    → subst₂ HomTerm (cong unflatten (trans q r)) (cong unflatten p) x
      ≡ subst₂ HomTerm (cong unflatten r) refl
               (subst₂ HomTerm (cong unflatten q) (cong unflatten p) x)
  subst₂-dom-trans refl refl refl x = refl

  -- ρ⇒ shape.  `decode (ρ⇒ {A})` and `decode (id {A ⊗₀ unit})` reduce
  -- to `subst₂ … (proj₁ (decode-attempt-hId (A ⊗₀ unit)))` with the
  -- SAME inner term; only the cod equation differs by the trailing
  -- `++-identityʳ`.  `subst₂-cod-trans` peels exactly that.
  rho⇒-shape
    : ∀ A → decode (ρ⇒ {A})
         ≡ subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A)))
                  (decode (id {A ⊗₀ unit}))
  rho⇒-shape A =
    subst₂-cod-trans (domL-hId (A ⊗₀ unit)) (codL-hId (A ⊗₀ unit))
                     (++-identityʳ (flatten A))
                     (proj₁ (decode-attempt-hId (A ⊗₀ unit)))

  rho⇐-shape
    : ∀ A → decode (ρ⇐ {A})
         ≡ subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl
                  (decode (id {A ⊗₀ unit}))
  rho⇐-shape A =
    subst₂-dom-trans (domL-hId (A ⊗₀ unit)) (++-identityʳ (flatten A))
                     (codL-hId (A ⊗₀ unit))
                     (proj₁ (decode-attempt-hId (A ⊗₀ unit)))

rhoShapeResidual : RhoShapeResidual
rhoShapeResidual = record
  { decode-ρ⇒-shape = rho⇒-shape
  ; decode-ρ⇐-shape = rho⇐-shape
  }

--------------------------------------------------------------------------------
-- ## (B) The pruned-vs-unpruned BRIDGE, factored through PRUNED shapes.
--
-- The two recursive constructors are the only places `decodeP X` and
-- `decode X` can differ (every ATOMIC `decodeP X ≡ decode X`
-- definitionally — verified by `refl` in `decodeP-≈-decode` below).
--
-- We no longer postulate the two bridges directly.  Instead each is
-- FACTORED through a PRUNED shape lemma + the structural recursion + the
-- ALREADY-TRUSTED unpruned shape (`Shape.decode-{∘,⊗}-shape-inner`):
--
--     decodeP (g∘f) ≈⟨ pruned ∘ shape ⟩ decodeP g ∘ decodeP f
--                   ≈⟨ rec g , rec f  ⟩ decode  g ∘ decode  f
--                   ≈⟨ sym (unpruned ∘ shape) ⟩ decode (g∘f)
--
-- (and dually for `⊗`).  The assembler `Assemble.decodeP-≈-decode-∘-from`
-- (in `Sub.ProcessEdgesTermShape`) performs the chain; we supply `decode`,
-- the unpruned shapes from `Shape`, the pruned shapes from the residual
-- record below, and `decodeP-≈-decode` itself as the recursion `rec`.
--
-- The SOLE remaining pruning-specific trust is therefore
-- `decodePShapeResiduals : DecodePShapeResiduals` — its two fields are
-- the PRUNED mirror of `decode-{∘,⊗}-shape-inner` (`decode` → `decodeP`),
-- i.e. NO new conceptual trust beyond the shared shape obligation; for
-- the `⊗` field the term-level content is confirmedly the
-- `swap-atom-aligned` / `nf-bracket` kernel (see
-- `Sub.ProcessEdgesTermShape` `decodeP-⊗-shape` doc).
--
-- The new module's `decodeP` is DEFINITIONALLY identical to this
-- module's (`subst₂ HomTerm … (proj₁ (decode-attempt-LinearP f))`), so
-- the `Assemble` results have exactly the bridge postulate types.
--
-- `decodePShapeResiduals` is NO LONGER A POSTULATE.  It is now a DEFINITION
-- (`Wired.decodePShapeResiduals`) consuming the two PROVEN, postulate-free
-- PRUNED shape lemmas `Sub.DecodeComposePruned.decodeP-∘-shape` /
-- `Sub.DecodeTensorPruned.decodeP-⊗-shape` (each parameterised by `objUIP`
-- + `K : FaithfulnessResidual`, threaded from `DecodeRelRespIsoWired`).
-- The ⊗-side is the `decodeP` mirror of the PROVEN unpruned
-- `decode-⊗-shape-inner` (tensor is NOT pruned, so the SAME `hTensor`
-- block machinery applies); it does NOT consume any `nf-bracket` kernel.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ## Threading `objUIP` + `K : FaithfulnessResidual`.
--
-- The two unpruned shape residuals `decode-{∘,⊗}-shape-inner` are now
-- DEFINITIONS (postulate-free) in `Sub.DecodeComposeShape` /
-- `Sub.DecodeTensorShape`, each parameterised by `objUIP` + a Kelly
-- `FaithfulnessResidual`.  These are exactly the two K-inputs the rest of
-- the completeness chain threads: `DecodeRelRespIsoWired` postulates a
-- fresh `K-faithfulness` and DISCHARGES `objUIP` (Hedberg, via
-- `Discharge.ObjUIP`), then supplies BOTH to `run-interchange-⟪⟫` /
-- `decodeP-resp-iso`.  We mirror that here: everything that consumes the
-- shape residuals is parameterised by `(objUIP)(K)`, and
-- `DecodeRelRespIsoWired` passes its own `objUIP`/`K-faithfulness` at the
-- consume site (`decode-rel-≈-decodeP = DRDP.decode-rel-≈-decodeP objUIP
-- K-faithfulness`).  The α atomics / the pruned `decodePShapeResiduals`
-- stay parameter-free postulates; `agenSigmaResiduals` is now also a
-- `(objUIP)(K)`-parameterised DEFINITION (consuming `DAS`).
--------------------------------------------------------------------------------

module Wired
  (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
  (K : FaithfulnessResidual)
  where

  -- `decodeShapeResiduals` is now a DEFINITION consuming the two proven,
  -- postulate-free shape lemmas (no longer a postulate).
  decodeShapeResiduals : DecodeShapeResiduals
  decodeShapeResiduals = record
    { decode-∘-shape-inner = DCS.decode-∘-shape-inner objUIP K
    ; decode-⊗-shape-inner = DTS.decode-⊗-shape-inner objUIP K
    }

  -- `agenSigmaResiduals` is now a DEFINITION consuming the two proven,
  -- postulate-free single-edge collapses `decode-{Agen,σ}-collapse`
  -- (`Sub.DecodeAgenSigmaShape`, each in a top-level `module _ (objUIP)(Kf)`).
  -- The field types match `Residuals` exactly — no adapter needed.
  agenSigmaResiduals : Residuals
  agenSigmaResiduals = record
    { decode-Agen-collapse = λ {A} {B} g → DAS.decode-Agen-collapse objUIP K g
    ; decode-σ-collapse    = λ {A} {B} ⦃ s ⦄ → DAS.decode-σ-collapse objUIP K ⦃ s ⦄
    }

  -- The two atomic associator obligations, now DEFINITIONS (no longer
  -- postulates).  `decode-rel (α{⇒,⇐}) = bridge (α{⇒,⇐})` DEFINITIONALLY
  -- (DecodeRel.agda), so each is `≈-Term-sym` of the PROVEN, postulate-free
  -- collapse `DAS.decode-α{⇒,⇐}-collapse objUIP K` (Sub.DecodeAgenSigmaShape).
  decode-rel-≈-decode-α⇒
    : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})
  decode-rel-≈-decode-α⇒ {A} {B} {C} =
    ≈-Term-sym (DAS.decode-α⇒-collapse objUIP K {A} {B} {C})

  decode-rel-≈-decode-α⇐
    : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})
  decode-rel-≈-decode-α⇐ {A} {B} {C} =
    ≈-Term-sym (DAS.decode-α⇐-collapse objUIP K {A} {B} {C})

  -- `decodePShapeResiduals` is now a DEFINITION consuming the two proven,
  -- postulate-free PRUNED shape lemmas (no longer a postulate).  The field
  -- types match `DecodePShapeResiduals` exactly — no adapter needed.  The
  -- ⊗-field is the `decodeP` mirror of the PROVEN `decode-⊗-shape-inner`
  -- (tensor is not pruned), so NO `nf-bracket` kernel is consumed.
  decodePShapeResiduals : DecodePShapeResiduals
  decodePShapeResiduals = record
    { decodeP-∘-shape = λ {A} {B} {C} g f → DCP.decodeP-∘-shape objUIP K g f
    ; decodeP-⊗-shape = λ {A} {B} {C} {D} f g → DTP.decodeP-⊗-shape objUIP K f g
    }

  -- Assemble the unpruned `DecoderAgreementAssumptions` from the residual
  -- records (mirrors `FromAssumptions.DecodeRelDecode`, but inline with
  -- `sig` only — the Agen/σ wiring `≈-Term-sym (decode-{Agen,σ}-collapse)`
  -- is `sig`-level so we do not need `sig-dec`).
  private
    module Shape = DecodeShapeResiduals decodeShapeResiduals
    module AS    = Residuals agenSigmaResiduals

    ty-⊗-shape : Ty-⊗-shape
    ty-⊗-shape = unapply-⊗-shape (λ {A} {B} {C} {D} f g → Shape.decode-⊗-shape-inner f g)

    ty-∘-shape : Ty-∘-shape
    ty-∘-shape = unapply-∘-shape (λ {A} {B} {C} g f → Shape.decode-∘-shape-inner g f)

    module CasesShape = Cases-sig.FromShape ty-⊗-shape
    module RhoShape   = Rho-sig.FromShape ty-⊗-shape rhoShapeResidual

    ty-Agen : Ty-Agen
    ty-Agen = unapply-Agen (λ {A} {B} g → ≈-Term-sym (AS.decode-Agen-collapse g))

    ty-σ : Ty-σ
    ty-σ = unapply-σ (λ {A} {B} ⦃ s ⦄ → ≈-Term-sym (AS.decode-σ-collapse ⦃ s ⦄))

    ty-α⇒ : Ty-α⇒
    ty-α⇒ = unapply-α⇒ (λ {A} {B} {C} → decode-rel-≈-decode-α⇒ {A} {B} {C})

    ty-α⇐ : Ty-α⇐
    ty-α⇐ = unapply-α⇐ (λ {A} {B} {C} → decode-rel-≈-decode-α⇐ {A} {B} {C})

    unprunedAssumptions : DecoderAgreementAssumptions
    unprunedAssumptions = record
      { decode-rel-≈-decode-Agen-T = ty-Agen
      ; decode-rel-≈-decode-σ-T    = ty-σ
      ; decode-rel-≈-decode-id-T   = CasesShape.ty-id
      ; decode-rel-≈-decode-λ⇒-T  = CasesShape.ty-λ⇒
      ; decode-rel-≈-decode-λ⇐-T  = CasesShape.ty-λ⇐
      ; decode-rel-≈-decode-ρ⇒-T  = RhoShape.ty-ρ⇒
      ; decode-rel-≈-decode-ρ⇐-T  = RhoShape.ty-ρ⇐
      ; decode-rel-≈-decode-α⇒-T  = ty-α⇒
      ; decode-rel-≈-decode-α⇐-T  = ty-α⇐
      ; decode-∘-shape-T           = ty-∘-shape
      ; decode-⊗-shape-T           = ty-⊗-shape
      }

  -- The unpruned dispatcher, derived constructively (induction on `f`) from
  -- the assembled assumptions via `DecoderAgreementSafe.WithAssumptions`.
  decode-rel-≈-decode
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decode f
  decode-rel-≈-decode = WithAssumptions.decode-rel-≈-decode unprunedAssumptions

  private
    -- The factoring assembler, instantiated with `decode`, the unpruned
    -- shape residuals, and the pruned shape residuals.
    module Asm = Assemble decode
                   (λ {A} {B} {C} g f → Shape.decode-∘-shape-inner g f)
                   (λ {A} {B} {C} {D} f g → Shape.decode-⊗-shape-inner f g)
                   decodePShapeResiduals

  -- The full pruned-vs-unpruned bridge, polymorphic in `f`.  ATOMIC cases:
  -- `refl` (each `decodeP X ≡ decode X` definitionally).  Recursive cases:
  -- the factoring assemblers, fed the recursion RESULTS on the
  -- structurally-smaller sub-terms (so termination is visible).
  decodeP-≈-decode : ∀ {A B} (f : HomTerm A B) → decodeP f ≈Term decode f
  decodeP-≈-decode (Agen g)  = ≡⇒≈Term refl
  decodeP-≈-decode (σ ⦃ s ⦄) = ≡⇒≈Term refl
  decodeP-≈-decode id        = ≡⇒≈Term refl
  decodeP-≈-decode λ⇒        = ≡⇒≈Term refl
  decodeP-≈-decode λ⇐        = ≡⇒≈Term refl
  decodeP-≈-decode ρ⇒        = ≡⇒≈Term refl
  decodeP-≈-decode ρ⇐        = ≡⇒≈Term refl
  decodeP-≈-decode α⇒        = ≡⇒≈Term refl
  decodeP-≈-decode α⇐        = ≡⇒≈Term refl
  decodeP-≈-decode (g ∘ f)   =
    Asm.decodeP-≈-decode-∘-from g f (decodeP-≈-decode g) (decodeP-≈-decode f)
  decodeP-≈-decode (f ⊗₁ g)  =
    Asm.decodeP-≈-decode-⊗-from f g (decodeP-≈-decode f) (decodeP-≈-decode g)

  -- The two bridge interfaces (same types as the old postulates), now
  -- DERIVED.  Kept as named values so consumers that referenced the old
  -- postulate names can still cite them directly.
  decodeP-≈-decode-∘
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP (g ∘ f) ≈Term decode (g ∘ f)
  decodeP-≈-decode-∘ g f = decodeP-≈-decode (g ∘ f)

  decodeP-≈-decode-⊗
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g) ≈Term decode (f ⊗₁ g)
  decodeP-≈-decode-⊗ f g = decodeP-≈-decode (f ⊗₁ g)

  --------------------------------------------------------------------------------
  -- ## The dispatcher (public interface).
  --
  --     decode-rel f ≈⟨ decode-rel-≈-decode f ⟩ decode f
  --                  ≈⟨ sym (decodeP-≈-decode f) ⟩ decodeP f
  --
  -- This is the value wired into `DecodeRelRespIsoWired` in place of the
  -- wholesale postulate.
  --------------------------------------------------------------------------------

  decode-rel-≈-decodeP
    : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
  decode-rel-≈-decodeP f =
    ≈-Term-trans (decode-rel-≈-decode f) (≈-Term-sym (decodeP-≈-decode f))

--------------------------------------------------------------------------------
-- Top-level re-export: the dispatcher as a function of the two K-inputs.
-- `DecodeRelRespIsoWired` applies it to its own `objUIP`/`K-faithfulness`.
--------------------------------------------------------------------------------

decode-rel-≈-decodeP
  : (objUIP : ∀ {A B : ObjTerm} (p q : A ≡ B) → p ≡ q)
    (K : FaithfulnessResidual)
  → ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP objUIP K = Wired.decode-rel-≈-decodeP objUIP K
