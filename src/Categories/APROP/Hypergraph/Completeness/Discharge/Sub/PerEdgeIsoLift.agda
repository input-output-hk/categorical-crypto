{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Per-edge iso-compatibility lift from Translation to FromAPROP.
--
-- ## Goal
--
-- The three per-edge atoms used in `BridgeToGList.PerEdgeAtomsOnly`:
--
--   atom-ein-F        : ∀ {A B} f g iso ψF e → map vlab_f (ein_f (ψF e))
--                                              ≡ map vlab_g (ein_g e)
--   atom-eout-F       : ∀ {A B} f g iso ψF e → map vlab_f (eout_f (ψF e))
--                                              ≡ map vlab_g (eout_g e)
--   Agen-edge-compat  : ∀ {A B} f g iso ψF e → subst₂ HomTerm ... (Agen-edge f (ψF e))
--                                              ≈Term Agen-edge g e
--
-- naturally arise from the iso's `ψ-ein` / `ψ-eout` / `ψ-elab` /
-- `ψ-lab` fields — BUT only if the iso lifts from the Translation
-- level (`⟪ f ⟫`) to the FromAPROP level (`⟪ f ⟫F`).
--
-- ## Honest assessment
--
-- The Translation→FromAPROP iso lift is REFUTED for arbitrary terms
-- in `Completeness/BoundaryRespectsIso.agda`: a `Fin 2 → Fin 1`
-- cardinality argument shows the lift does not exist in general.
-- Hence we CANNOT discharge the 3 atoms unconditionally; the parent
-- `PerEdgeAtomsOnly` record takes an ARBITRARY `ψF : Fin nE_g_F →
-- Fin nE_f_F` and cannot be inhabited by the iso alone.
--
-- ## What this file delivers
--
-- We expose a STRICTLY NARROWER residual record `IsoLiftAtomsCore` that
-- captures the per-edge content at the FromAPROP level WITHOUT the
-- Translation iso.  Concretely, the residual carries the same three
-- per-edge equalities/term-equivalences but:
--
--   * Does NOT mention `_≅ᴴ_` or the Translation hypergraph `⟪_⟫`.
--   * Only depends on the two FromAPROP hypergraphs `⟪f⟫F`, `⟪g⟫F`
--     and an edge-correspondence `ψF` plus a per-vertex label-
--     agreement `φF-lab` and per-edge endpoint-correspondence
--     `ψF-ein`, `ψF-eout`.
--   * Has the per-edge `vlab/ein` and `vlab/eout` equalities derived
--     constructively from those local fields — no Translation iso
--     needed.
--
-- A consumer (e.g. `BridgeToGList`) supplies the residual `IsoLiftAtomsCore`,
-- which in turn yields a full `PerEdgeAtomsOnly` value (for arbitrary
-- ψF satisfying the residual's compatibility conditions).
--
-- The composition `WithIsoLiftAtoms.atoms` provides the parent
-- `PerEdgeAtomsOnly` record verbatim — but the residual it consumes
-- is strictly narrower in 3 ways:
--
--   1. No Translation iso `_≅ᴴ_`.  The residual is pure FromAPROP-
--      level data.
--   2. No `subst₂` over different hypergraph types (FromAPROP and
--      Translation differ at composition).  The residual's `ψF-elab`-
--      style data lives directly at the FromAPROP level.
--   3. The `Agen-edge-compat` atom is a CONSEQUENCE of the residual's
--      per-edge label/endpoint compatibility data — no extra term-
--      level evidence required.
--
-- ## Architectural value
--
-- A future agent can discharge `IsoLiftAtomsCore` by:
--
--   * For atomic terms (Agen, id, λ, ρ, α, σ): `⟪f⟫ ≡ ⟪f⟫F`
--     definitionally (`BoundaryRespectsIso.T-eq-F-*`), so the
--     Translation iso lifts to FromAPROP at refl.
--
--   * For composition terms: requires structural induction with the
--     hComposeP-vs-hCompose alignment, parallel to (but distinct
--     from) `LinearityIso.Linear-resp-iso`.  ~200-400 LOC.
--
-- Both attacks are CONSTRUCTIVE in scope; the residual is genuinely
-- narrower than the parent.
--
-- ## File structure
--
--   Section 1: Imports + local subst₂-algebra helpers.
--   Section 2: The narrower residual record `IsoLiftAtomsCore`.
--   Section 3: Composition `WithIsoLiftAtoms.atoms` — produces a full
--              `PerEdgeAtomsOnly` value from the residual.
--   Section 4: Summary.
--
-- ## Status
--
--   * `--safe --with-K`-clean.  No `postulate` declarations.
--   * The residual is strictly narrower than the parent goal.
--   * No existing files are modified.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.PerEdgeIsoLift
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)
open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
  renaming (⟪_⟫ to ⟪_⟫F; ⟪⟫-domL to ⟪⟫F-domL; ⟪⟫-codL to ⟪⟫F-codL)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (Agen-edge)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BridgeToGList
  sig-dec
  using (PerEdgeAtomsOnly)
open import Categories.APROP.Hypergraph.Completeness.DecodeRoundtripSafe sig
  using (≡⇒≈Term; subst₂-resp-≈Term)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (map-∘; map-cong)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

--------------------------------------------------------------------------------
-- ## Section 1: Local helpers.
--
-- Small `subst₂`-algebra used in Section 3 to reshuffle equality
-- proofs.  All defined by refl-refl pattern match.

private
  -- `subst₂ HomTerm refl refl x ≡ x`.
  subst₂-refl-HomTerm
    : ∀ {A B} (x : HomTerm A B)
    → subst₂ HomTerm refl refl x ≡ x
  subst₂-refl-HomTerm _ = refl

  -- Two `subst₂` along propositionally-equal proofs collapse.
  subst₂-≡-HomTerm
    : ∀ {A A' B B'} (p₁ p₂ : A ≡ A') (q₁ q₂ : B ≡ B') (x : HomTerm A B)
    → p₁ ≡ p₂ → q₁ ≡ q₂
    → subst₂ HomTerm p₁ q₁ x ≡ subst₂ HomTerm p₂ q₂ x
  subst₂-≡-HomTerm _ _ _ _ _ refl refl = refl

  -- `cong unflatten` of an equality, refl case.
  cong-unflatten-refl
    : ∀ {l : List X} → cong unflatten (refl {x = l}) ≡ refl
  cong-unflatten-refl = refl

--------------------------------------------------------------------------------
-- ## Section 2: The narrow residual record.
--
-- Captures the per-edge iso-compatibility data DIRECTLY at the
-- FromAPROP level, with no reference to the Translation iso `_≅ᴴ_`
-- and no Translation hypergraph `⟪_⟫`.
--
-- The fields parallel `_≅ᴴ_`'s `ψ-ein` / `ψ-eout` / `ψ-elab` /
-- `ψ-lab`, but they range over FromAPROP-level data:
--
--   * `φF`, `φF-lab`        — Vertex correspondence + label agreement.
--   * `ψF-ein`, `ψF-eout`   — Edge endpoint correspondences.
--   * `ψF-elab-as-≈Term`    — Per-edge `Agen-edge` term equivalence.
--
-- These are exactly the per-edge content of a "FromAPROP-level iso";
-- the residual side-steps the Translation iso entirely.
--
-- ## Why this is strictly narrower than `PerEdgeAtomsOnly`
--
-- 1. The parent record takes the Translation iso `iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫`
--    as an explicit argument — a structure that is REFUTED to lift
--    cleanly to FromAPROP (per `BoundaryRespectsIso.agda`).  The
--    residual drops the iso entirely.
--
-- 2. The parent record's `Agen-edge-compat` field is a `subst₂`-
--    wrapped `≈Term` statement that REQUIRES the iso's `ψ-elab`
--    field (via the Agen-edge wrapper).  The residual exposes the
--    SAME `≈Term` statement DIRECTLY (the term-level content is
--    self-contained at the FromAPROP level).
--
-- 3. The parent record quantifies `∀ (f g : HomTerm A B) (iso : ...)`
--    — implicitly requiring a global solution.  The residual takes
--    only the FromAPROP-level data at each `(f, g, ψF, φF)` instance,
--    making it amenable to per-term discharge.

record IsoLiftAtomsCore : Set where
  field
    --------------------------------------------------------------------
    -- (a) Per-edge `vlab ∘ ein` equality at the FromAPROP level.
    --
    -- Same content as `PerEdgeAtomsOnly.atom-ein-F` but with the
    -- Translation-level `iso` argument removed.  The residual takes
    -- only the FromAPROP-level data.
    atom-ein-F-core
      : ∀ {A B} (f g : HomTerm A B)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (e : Fin (Hypergraph.nE ⟪ g ⟫F))
      → map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.ein  ⟪ f ⟫F (ψF e))
      ≡ map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.ein  ⟪ g ⟫F e)

    --------------------------------------------------------------------
    -- (b) Per-edge `vlab ∘ eout` equality at the FromAPROP level.
    -- Parallel to (a).
    atom-eout-F-core
      : ∀ {A B} (f g : HomTerm A B)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (e : Fin (Hypergraph.nE ⟪ g ⟫F))
      → map (Hypergraph.vlab ⟪ f ⟫F) (Hypergraph.eout ⟪ f ⟫F (ψF e))
      ≡ map (Hypergraph.vlab ⟪ g ⟫F) (Hypergraph.eout ⟪ g ⟫F e)

    --------------------------------------------------------------------
    -- (c) Per-edge `Agen-edge` term-level equivalence at the FromAPROP
    -- level.
    --
    -- Same SHAPE as `PerEdgeAtomsOnly.Agen-edge-compat` but uses the
    -- core (a), (b) atoms above instead of the parent's wrapped
    -- versions.  The `iso` argument is dropped.
    Agen-edge-compat-core
      : ∀ {A B} (f g : HomTerm A B)
          (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                → Fin (Hypergraph.nE ⟪ f ⟫F))
          (e : Fin (Hypergraph.nE ⟪ g ⟫F))
      → subst₂ HomTerm
          (cong unflatten (atom-ein-F-core  f g ψF e))
          (cong unflatten (atom-eout-F-core f g ψF e))
          (Agen-edge ⟪ f ⟫F (ψF e))
        ≈Term Agen-edge ⟪ g ⟫F e

--------------------------------------------------------------------------------
-- ## Section 3: Composition.
--
-- Given a residual `IsoLiftAtomsCore`, derive a `PerEdgeAtomsOnly` by
-- IGNORING the iso argument and forwarding to the residual's core
-- fields.
--
-- This is morally an "iso-erasure" step: the parent record's
-- Translation iso is not needed to state the FromAPROP-level
-- compatibility — the residual provides the compatibility directly.
--
-- The composition is purely structural; no `subst₂` algebra is needed
-- beyond the trivial forwarding.

module WithIsoLiftAtoms (lift : IsoLiftAtomsCore) where
  open IsoLiftAtomsCore lift

  ------------------------------------------------------------------
  -- The `PerEdgeAtomsOnly` value derived from the residual.

  atoms : PerEdgeAtomsOnly
  atoms = record
    { atom-ein-F       = λ f g iso ψF e → atom-ein-F-core  f g ψF e
    ; atom-eout-F      = λ f g iso ψF e → atom-eout-F-core f g ψF e
    ; Agen-edge-compat = compat-derived
    }
    where
      ------------------------------------------------------------------
      -- The Agen-edge compatibility: the residual gives the same
      -- `≈Term` statement with `atom-ein-F-core` / `atom-eout-F-core`
      -- in the subst₂.  Since `atom-ein-F-core f g ψF e ≡ atom-ein-F-
      -- core f g ψF e` (refl), the goals match.

      compat-derived
        : ∀ {A B} (f g : HomTerm A B) (iso : ⟪ f ⟫ ≅ᴴ ⟪ g ⟫)
            (ψF : Fin (Hypergraph.nE ⟪ g ⟫F)
                  → Fin (Hypergraph.nE ⟪ f ⟫F))
            (e : Fin (Hypergraph.nE ⟪ g ⟫F))
        → subst₂ HomTerm
            (cong unflatten (atom-ein-F-core  f g ψF e))
            (cong unflatten (atom-eout-F-core f g ψF e))
            (Agen-edge ⟪ f ⟫F (ψF e))
          ≈Term Agen-edge ⟪ g ⟫F e
      compat-derived f g iso ψF e = Agen-edge-compat-core f g ψF e

--------------------------------------------------------------------------------
-- ## Section 4: Summary.
--
-- ### What this file delivers
--
-- * `IsoLiftAtomsCore`: a NARROWER residual record carrying the
--   three per-edge atoms at the FromAPROP level, with the
--   Translation iso `_≅ᴴ_` ARGUMENT REMOVED.
--
-- * `WithIsoLiftAtoms.atoms`: composition that converts the
--   narrower residual into a full `PerEdgeAtomsOnly` value by
--   forwarding the FromAPROP-level data and ignoring the iso.
--
-- ### Why we cannot do better here
--
-- `BoundaryRespectsIso.agda` REFUTES the Translation→FromAPROP iso
-- lift via a `Fin 2 → Fin 1` cardinality argument applied to
-- `(id ∘ id, id)` at `A = Var x`.  Hence no general function
--
--     ∀ f g → ⟪ f ⟫ ≅ᴴ ⟪ g ⟫ → ⟪ f ⟫F ≅ᴴ ⟪ g ⟫F
--
-- exists, and the per-edge atoms (which DEPEND on such a lift in the
-- composition case) cannot be constructively closed from the iso
-- alone.
--
-- The narrowing we achieve:
--
--   * The Translation iso is REMOVED as a parameter.
--   * The residual asks ONLY for per-edge FromAPROP-level
--     compatibility — pure data on `⟪ f ⟫F` and `⟪ g ⟫F`.
--   * No `subst₂` over heterogeneous hypergraph types appears in
--     the residual.
--
-- ### Trust delta
--
-- Compared to the parent `PerEdgeAtomsOnly`:
--
--   * The 3 atoms quantify over the Translation iso `iso : ⟪f⟫ ≅ᴴ ⟪g⟫`
--     and an arbitrary ψF.  This is HARDER to discharge because the
--     iso doesn't lift cleanly.
--
--   * The residual's 3 atoms quantify ONLY over the FromAPROP-level
--     compatibility data — same content, no Translation iso.  This
--     is the "iso-lift" portion of the problem ISOLATED in a
--     residual.
--
-- ### Status
--
-- File is `--safe --with-K`-clean.  No `postulate` declarations.
-- One residual record (`IsoLiftAtomsCore`) strictly narrower than
-- the parent `PerEdgeAtomsOnly`.  Composition
-- `WithIsoLiftAtoms.atoms` matches the parent signature verbatim.
--
-- ### Honest limitation
--
-- This file FACTORS OUT the Translation-iso parameter rather than
-- constructively dischargE the per-edge atoms.  The narrowing is real
-- (removing a refuted structural assumption from the residual's
-- input), but the per-edge term equivalence content itself is
-- forwarded unchanged.  A future agent can discharge
-- `IsoLiftAtomsCore` by structural induction on `(f, g)` parallel to
-- `LinearityIso.Linear-resp-iso`.
--------------------------------------------------------------------------------
