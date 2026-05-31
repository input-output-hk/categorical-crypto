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
--   * (U) `DecodeShapeResiduals`         — 2 fields: `decode-{∘,⊗}-shape-inner`
--   * (U) `RhoShapeResidual`             — 2 fields: `decode-{ρ⇒,ρ⇐}-shape`
--   * (U) `DecodeRoundtripAgenSigma.Residuals` (K) — `decode-{Agen,σ}-collapse`
--   * (U) `decode-rel-≈-decode-α{⇒,⇐}`   — 2 atomic associator obligations
--   * (B) `decodeP-≈-decode-∘`           — pruned `∘` bridge
--   * (B) `decodeP-≈-decode-⊗`           — pruned `⊗` bridge (→ swap-atom-aligned)
--
-- All of (U) is the SHARED unpruned/interchange residual surface (no new
-- trust beyond what the `decode`-side proof already assumes).  The only
-- pruning-specific new trust is the two (B) bridges.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelDecodeP
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten)
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
  using (decode)
open import Categories.APROP.Hypergraph.Completeness.DecoderAgreementSafe sig
  using ( DecoderAgreementAssumptions; module WithAssumptions
        ; Ty-Agen; Ty-σ; Ty-id; Ty-λ⇒; Ty-λ⇐; Ty-ρ⇒; Ty-ρ⇐; Ty-α⇒; Ty-α⇐
        ; Ty-∘-shape; Ty-⊗-shape
        ; unapply-Agen; unapply-σ; unapply-α⇒; unapply-α⇐
        ; unapply-∘-shape; unapply-⊗-shape )
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeShape sig
  using (DecodeShapeResiduals; module DecodeShapeResiduals)
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementCases as Cases
module Cases-sig = Cases sig
import Categories.APROP.Hypergraph.Completeness.Discharge.DecoderAgreementRho as Rho
module Rho-sig = Rho sig
open Rho-sig using (RhoShapeResidual)
open import Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRoundtripAgenSigma sig
  using (Residuals; module Residuals)

open import Categories.Category using (Category)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst₂)

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

postulate
  -- (U/S) the unpruned shape residuals: `decode-{∘,⊗}-shape-inner`.
  decodeShapeResiduals : DecodeShapeResiduals
  -- (U/M) the unpruned right-unitor shape residuals: `decode-{ρ⇒,ρ⇐}-shape`.
  rhoShapeResidual     : RhoShapeResidual
  -- (U/K) the unpruned single-edge collapses: `decode-{Agen,σ}-collapse`.
  agenSigmaResiduals   : Residuals
  -- (U/M) the two atomic associator obligations (bare params upstream too).
  decode-rel-≈-decode-α⇒
    : ∀ {A B C} → decode-rel (α⇒ {A} {B} {C}) ≈Term decode (α⇒ {A} {B} {C})
  decode-rel-≈-decode-α⇐
    : ∀ {A B C} → decode-rel (α⇐ {A} {B} {C}) ≈Term decode (α⇐ {A} {B} {C})

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

--------------------------------------------------------------------------------
-- ## (B) The pruned-vs-unpruned BRIDGE.
--
-- The ONLY genuinely-new pruned obligations: the bridge on the two
-- recursive constructors.  Every ATOMIC case is `refl` (verified below),
-- since `decodeP X ≡ decode X` definitionally for non-`∘` X.
--------------------------------------------------------------------------------

postulate
  -- (B/∘) pruned `∘` bridge: `hComposeP` vs `hCompose`.  Constructive
  -- content = `pe-term-++`-style block-decomposition of `process-edges`
  -- on `hComposeP` (parallel to the unpruned `decode-∘-shape-inner`).
  decodeP-≈-decode-∘
    : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
    → decodeP (g ∘ f) ≈Term decode (g ∘ f)

  -- (B/⊗) pruned `⊗` bridge.  Tensor is NOT pruned, so this relates two
  -- `decode-attempt-hTensor` applications differing only in their
  -- sub-translations; modulo the recursive sub-bridges its term-level
  -- content is the independent-block reordering = `swap-atom-aligned`
  -- (the SAME Mac-Lane kernel as the interchange side).  See module
  -- header.
  decodeP-≈-decode-⊗
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
    → decodeP (f ⊗₁ g) ≈Term decode (f ⊗₁ g)

-- The full pruned-vs-unpruned bridge, polymorphic in `f`.  ATOMIC cases:
-- `refl` (each `decodeP X ≡ decode X` definitionally).  Recursive cases:
-- the two (B) residuals above.
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
decodeP-≈-decode (g ∘ f)   = decodeP-≈-decode-∘ g f
decodeP-≈-decode (f ⊗₁ g)  = decodeP-≈-decode-⊗ f g

--------------------------------------------------------------------------------
-- ## The dispatcher (public interface).
--
--     decode-rel f ≈⟨ decode-rel-≈-decode f ⟩ decode f
--                  ≈⟨ sym (decodeP-≈-decode f) ⟩ decodeP f
--
-- This is the value to wire into `DecodeRelRespIsoWired` in place of the
-- wholesale postulate.
--------------------------------------------------------------------------------

decode-rel-≈-decodeP
  : ∀ {A B} (f : HomTerm A B) → decode-rel f ≈Term decodeP f
decode-rel-≈-decodeP f =
  ≈-Term-trans (decode-rel-≈-decode f) (≈-Term-sym (decodeP-≈-decode f))
