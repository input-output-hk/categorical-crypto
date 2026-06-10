{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- THE `≈M → ≅ᴴ` BRIDGE SOLVER.
--
-- This is the *matrix-equivalence* drop-in for `findIsoᴮ` (Solver.MatrixBridge).
-- The architectural point (see `docs/smc-solver-performance.md`, "the ≈M → ≅ᴴ
-- bridge decision is measurably cheaper"): the PER-USE decision should be the
-- CHEAP matrix-equivalence check `canonMat H ≡ canonMat J`, and should AVOID the
-- two expensive deciders `decBijLaws` + `decCanonMatch` that `findIsoᴮ` runs.
--
-- The pieces, mirroring the task spec:
--
--   * `CanonData`         — a LABEL-AWARE canonical matrix: the canonically-
--                           ordered vertex labels, edge codes, and reindexed
--                           incidence (`ein`/`eout`/`dom`/`cod` as canonical
--                           ranks).  Two isomorphic hypergraphs yield EQUAL
--                           `CanonData`.  (`hg→mat` alone is Bool/connectivity
--                           only — it loses `vlab`/`elab`, so it can't imply
--                           `≅ᴴ`; `CanonData` records exactly the missing data.)
--   * `canonMat`          — compute the `CanonData` of a hypergraph.
--   * `matrixEquiv H J`   — `canonMat H ≡ canonMat J` (the cheap proposition).
--   * `decideMatrixEquiv` — decide it by a flat structural compare.  THIS is the
--                           cheap per-use decision.
--   * `matEquiv→hgIso`    — `matrixEquiv → H ≅ᴴ J`, made `opaque`.  Built via the
--                           existing postulate-free `matIso→hgIso`; the residual
--                           faithfulness is a clearly-marked `postulate` (it is
--                           `opaque`, so it NEVER reaches the per-use path or the
--                           profile — the profile stays valid).
--   * `findIsoᴹ`          — `nV`/`nE` equality, then `decideMatrixEquiv`, then
--                           `matEquiv→hgIso`.
--
-- Drops `--safe` (matrix world); the hypergraph modules stay `--safe`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.MatrixBridgeM
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; X; _≟X_)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

-- The canonical-labelling machinery + the postulate-free `matIso→hgIso`.
open import Categories.APROP.Hypergraph.Solver.MatrixBridge sig-dec
  using ( align'; Alignment
        ; BijLaws; CanonMatch; matIso→hgIso )
-- `Canon` is a parameterised sub-module, accessed qualified as `MB.Canon`.
import Categories.APROP.Hypergraph.Solver.MatrixBridge sig-dec as MB

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

private
  variable
    H J : Hypergraph FlatGen

--------------------------------------------------------------------------------
-- §1.  `posIn` — position of a `Fin` in a `Fin`-list, as a ℕ.  (A private copy
-- of `MatrixBridge`'s `posIn`, which is not exported; the public canonical
-- orders are read via `Canon.canonV`/`Canon.canonE`.)

private
  posIn : ∀ {n} → List (Fin n) → Fin n → ℕ
  posIn []       _ = 0
  posIn (x ∷ xs) v with x ≟F v
  ... | yes _ = 0
  ... | no  _ = suc (posIn xs v)

  -- Reindex a list of vertices to their canonical ranks under `order`.
  ranks : ∀ {n} → List (Fin n) → List (Fin n) → List ℕ
  ranks order = map (posIn order)

--------------------------------------------------------------------------------
-- §2.  `CanonData` — the LABEL-AWARE canonical matrix.
--
-- Recorded ENTIRELY in canonical order (the topological-peel orders `canonV`
-- / `canonE`).  This is the data that determines `≅ᴴ`:
--
--   * `nV` / `nE`            : the two counts (type alignment).
--   * `vlabs`                : `map vlab` of the canonical vertex order — the
--                              vertex labels read in canonical slot order.
--   * `ecodes`               : `ecode` of the canonical edge order — the
--                              edge generator codes in canonical slot order.
--   * `eins` / `eouts`       : for each canonical edge, its `ein`/`eout`
--                              vertices reindexed to CANONICAL VERTEX RANKS.
--   * `domR` / `codR`        : the boundary `dom`/`cod` reindexed to canonical
--                              vertex ranks.
--
-- Two isomorphic hypergraphs (same diagram, possibly different raw `Fin`
-- layout) produce EQUAL `CanonData`: the canonical orders factor out the
-- layout, and every recorded datum is layout-independent (labels, codes, and
-- ranks-within-the-canonical-order).
--
-- NB: this is genuinely a "matrix" in the sense of §1's `hg→mat`, but
-- POSITIONALLY indexed by canonical rank and ENRICHED with the labels/codes
-- the Bool/connectivity matrix dropped.  Comparing `CanonData`s is the flat
-- structural compare the task asks for.

record CanonData : Set where
  field
    nV    : ℕ
    nE    : ℕ
    vlabs : List X        -- canonical-order vertex labels
    ecodes : List ℕ       -- canonical-order edge codes
    eins  : List (List ℕ) -- canonical-order edge inputs, as canonical ranks
    eouts : List (List ℕ) -- canonical-order edge outputs, as canonical ranks
    domR  : List ℕ        -- dom as canonical ranks
    codR  : List ℕ        -- cod as canonical ranks

-- Compute the canonical matrix of a hypergraph, at a per-edge generator code.
canonMat : (G : Hypergraph FlatGen)
         → (ecode : Fin (Hypergraph.nE G) → ℕ)
         → CanonData
canonMat G ecode = record
  { nV    = G.nV
  ; nE    = G.nE
  ; vlabs = map G.vlab cV
  ; ecodes = map ecode cE
  ; eins  = map (λ e → ranks cV (G.ein  e)) cE
  ; eouts = map (λ e → ranks cV (G.eout e)) cE
  ; domR  = ranks cV G.dom
  ; codR  = ranks cV G.cod
  }
  where
    module G = Hypergraph G
    cV : List (Fin G.nV)
    cV = MB.Canon.canonV G ecode
    cE : List (Fin G.nE)
    cE = MB.Canon.canonE G ecode

--------------------------------------------------------------------------------
-- §3.  `matrixEquiv` — the cheap equivalence proposition, and its decider.
--
-- `matrixEquiv H J ecodeH ecodeJ` := `canonMat H ecodeH ≡ canonMat J ecodeJ`.
-- THIS is the per-use decision: build both canonical matrices and compare them
-- structurally (flat list/ℕ/label equality).  No `decBijLaws`, no
-- `decCanonMatch` — that is precisely the cost we are eliminating.

matrixEquiv : (H J : Hypergraph FlatGen)
            → (ecodeH : Fin (Hypergraph.nE H) → ℕ)
            → (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
            → Set
matrixEquiv H J ecodeH ecodeJ = canonMat H ecodeH ≡ canonMat J ecodeJ

-- Component deciders.
private
  _≟LX_ : DecidableEquality (List X)
  _≟LX_ = ≡-dec _≟X_

  _≟Lℕ_ : DecidableEquality (List ℕ)
  _≟Lℕ_ = ≡-dec _≟ℕ_

  _≟LLℕ_ : DecidableEquality (List (List ℕ))
  _≟LLℕ_ = ≡-dec _≟Lℕ_

  -- Decide `CanonData` equality by deciding each field and assembling.  A
  -- record is equal iff all fields are; we decide them in turn.
  decCanonData : DecidableEquality CanonData
  decCanonData c d
    with CanonData.nV c ≟ℕ CanonData.nV d
       | CanonData.nE c ≟ℕ CanonData.nE d
       | CanonData.vlabs c ≟LX CanonData.vlabs d
       | CanonData.ecodes c ≟Lℕ CanonData.ecodes d
       | CanonData.eins c ≟LLℕ CanonData.eins d
       | CanonData.eouts c ≟LLℕ CanonData.eouts d
       | CanonData.domR c ≟Lℕ CanonData.domR d
       | CanonData.codR c ≟Lℕ CanonData.codR d
  ... | no ¬p | _ | _ | _ | _ | _ | _ | _ =
        no λ eq → ¬p (cong CanonData.nV eq)
  ... | _ | no ¬p | _ | _ | _ | _ | _ | _ =
        no λ eq → ¬p (cong CanonData.nE eq)
  ... | _ | _ | no ¬p | _ | _ | _ | _ | _ =
        no λ eq → ¬p (cong CanonData.vlabs eq)
  ... | _ | _ | _ | no ¬p | _ | _ | _ | _ =
        no λ eq → ¬p (cong CanonData.ecodes eq)
  ... | _ | _ | _ | _ | no ¬p | _ | _ | _ =
        no λ eq → ¬p (cong CanonData.eins eq)
  ... | _ | _ | _ | _ | _ | no ¬p | _ | _ =
        no λ eq → ¬p (cong CanonData.eouts eq)
  ... | _ | _ | _ | _ | _ | _ | no ¬p | _ =
        no λ eq → ¬p (cong CanonData.domR eq)
  ... | _ | _ | _ | _ | _ | _ | _ | no ¬p =
        no λ eq → ¬p (cong CanonData.codR eq)
  ... | yes pV | yes pE | yes pl | yes pc | yes pi | yes po | yes pd | yes pcd =
        yes (assemble pV pE pl pc pi po pd pcd)
    where
      assemble :
          CanonData.nV c ≡ CanonData.nV d
        → CanonData.nE c ≡ CanonData.nE d
        → CanonData.vlabs c ≡ CanonData.vlabs d
        → CanonData.ecodes c ≡ CanonData.ecodes d
        → CanonData.eins c ≡ CanonData.eins d
        → CanonData.eouts c ≡ CanonData.eouts d
        → CanonData.domR c ≡ CanonData.domR d
        → CanonData.codR c ≡ CanonData.codR d
        → c ≡ d
      assemble refl refl refl refl refl refl refl refl = refl

-- THE CHEAP PER-USE DECISION: compute both canonical matrices and compare.
decideMatrixEquiv : (H J : Hypergraph FlatGen)
                  → (ecodeH : Fin (Hypergraph.nE H) → ℕ)
                  → (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
                  → Maybe (matrixEquiv H J ecodeH ecodeJ)
decideMatrixEquiv H J ecodeH ecodeJ
  with decCanonData (canonMat H ecodeH) (canonMat J ecodeJ)
... | yes p = just p
... | no  _ = nothing

--------------------------------------------------------------------------------
-- §4.  `matEquiv→hgIso` — the OPAQUE faithfulness.
--
-- From `matrixEquiv H J` we must produce `H ≅ᴴ J`.  We reuse the existing,
-- POSTULATE-FREE `matIso→hgIso al bij match`, which assembles a fully-proven
-- `≅ᴴ` from:
--
--   * `al`    : the canonical alignment `align' H J ecodeH ecodeJ pV pE`
--               (the orders carry the layout; no `decBijLaws` needed);
--   * `bij`   : `BijLaws al`     — the four bijection round-trips;
--   * `match` : `CanonMatch al`  — the eight incidence/label fields.
--
-- THE PROOF OBLIGATION (recovering `bij` and `match` from a *single* matrix
-- equality `canonMat H ≡ canonMat J`) is the faithfulness of the encoding.
-- Per the task this whole map is `opaque`, so whatever proof status it has
-- (proven or postulated) NEVER reaches the per-use decision path nor the
-- profile — `decideMatrixEquiv` is the only thing that runs per use.
--
-- We make as much of the chain CONCRETE as is feasible:
--
--   * The TYPE ALIGNMENT `nV H ≡ nV J`, `nE H ≡ nE J` is RECOVERED from the
--     matrix equality (`cong CanonData.nV`/`nE`) — PROVEN.  This drops
--     `align'`'s `Fin` defaults.
--   * `al := align' H J ecodeH ecodeJ pV pE` is then a concrete alignment.
--   * `BijLaws al` and `CanonMatch al` are the genuine faithfulness residual,
--     split into TWO clearly-marked `postulate`s below (`align'-bijLaws` and
--     `matrixEquiv→canonMatch`), consumed ONLY inside this `opaque` block.

-- The residual faithfulness, split into its TWO genuinely-distinct halves so
-- the proof obligations are crisp (see the report for effort estimates):
--
--   (1) `align'-bijLaws` — the BIJECTION half.  The canonical orders `canonV`/
--       `canonE` are PERMUTATIONS of their index spaces (`Complete` +
--       `Distinct`, the topological peel emits each vertex/edge once), so the
--       `posIn`/`lookupD` composites that `align'` reads off are mutually
--       inverse.  This is the `MatrixBridge.align-bijLaws` argument (proven, via
--       the abstract `Composite` lemma) adapted to `align'`'s default-free
--       form, fed a `CanonPerm`.  It does NOT depend on `matrixEquiv` at all —
--       it is a per-hypergraph permutation fact.  Crucially this is the route
--       the task mandates: bijectivity comes from `CanonPerm`, NOT `decBijLaws`.
--
--   (2) `matrixEquiv→canonMatch` — the INCIDENCE half.  The eight
--       incidence/label/boundary fields, RECOVERED from the single canonical-
--       matrix equality `canonMat H ≡ canonMat J`: the equal `vlabs`/`ecodes`/
--       `eins`/`eouts`/`domR`/`codR` (read at canonical ranks) reconstruct
--       `J.vlab (φ i) ≡ H.vlab i`, `J.ein (ψ e) ≡ map φ (H.ein e)`, etc. at
--       `align'`'s canonical `φ`/`ψ`.  This is the encoding-correspondence
--       residual (no coherence content); see the report for the recovery
--       chain.
private
  postulate
    align'-bijLaws :
      (H J : Hypergraph FlatGen)
      (ecodeH : Fin (Hypergraph.nE H) → ℕ)
      (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
      (pV : Hypergraph.nV H ≡ Hypergraph.nV J)
      (pE : Hypergraph.nE H ≡ Hypergraph.nE J)
      → BijLaws (align' H J ecodeH ecodeJ pV pE)

    matrixEquiv→canonMatch :
      (H J : Hypergraph FlatGen)
      (ecodeH : Fin (Hypergraph.nE H) → ℕ)
      (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
      (pV : Hypergraph.nV H ≡ Hypergraph.nV J)
      (pE : Hypergraph.nE H ≡ Hypergraph.nE J)
      → matrixEquiv H J ecodeH ecodeJ
      → CanonMatch (align' H J ecodeH ecodeJ pV pE)

opaque
  matEquiv→hgIso :
    (H J : Hypergraph FlatGen)
    (ecodeH : Fin (Hypergraph.nE H) → ℕ)
    (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
    → matrixEquiv H J ecodeH ecodeJ
    → H ≅ᴴ J
  matEquiv→hgIso H J ecodeH ecodeJ meq =
    let pV : Hypergraph.nV H ≡ Hypergraph.nV J
        pV = cong CanonData.nV meq          -- PROVEN from the matrix equality
        pE : Hypergraph.nE H ≡ Hypergraph.nE J
        pE = cong CanonData.nE meq          -- PROVEN from the matrix equality
        al = align' H J ecodeH ecodeJ pV pE
        bij  = align'-bijLaws       H J ecodeH ecodeJ pV pE      -- (1)
        mtch = matrixEquiv→canonMatch H J ecodeH ecodeJ pV pE meq -- (2)
    in matIso→hgIso al bij mtch

--------------------------------------------------------------------------------
-- §5.  `findIsoᴹ` — the matrix-bridge iso finder.
--
-- `nV`/`nE` equality check up front (a bijection is impossible otherwise), then
-- the CHEAP `decideMatrixEquiv` decision, then the OPAQUE `matEquiv→hgIso`.
-- The per-use cost is the `decideMatrixEquiv` matrix compare ONLY — the opaque
-- iso construction never reduces during the implicit-witness discharge.

findIsoᴹ : (H J : Hypergraph FlatGen)
         → (ecodeH : Fin (Hypergraph.nE H) → ℕ)
         → (ecodeJ : Fin (Hypergraph.nE J) → ℕ)
         → Maybe (H ≅ᴴ J)
findIsoᴹ H J ecodeH ecodeJ =
  decideMatrixEquiv H J ecodeH ecodeJ >>= λ meq →
  just (matEquiv→hgIso H J ecodeH ecodeJ meq)
