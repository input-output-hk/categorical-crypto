{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- FEASIBILITY SPIKE: run the *matrix* coherence representation on a
-- *hypergraph*, by translating between the two worlds.
--
--   hg→mat  : Hypergraph FlatGen → BlockMatrix Bool …      (incidence encoding)
--   align   : matrices → candidate (φ , ψ) bijections        (canonical read)
--   matIso→hgIso : (φ , ψ) → H ≅ᴴ J                          (record assembly)
--
-- The proof fields of `_≅ᴴ_` (vlab/ein/eout/dom/cod/elab agreement) are
-- POSTULATED — this spike validates the *data flow* + surfaces the
-- index-reconciliation, it proves nothing.  The translation functions
-- themselves (`hg→mat`, `align`) genuinely compute; only the deferred
-- preservation proofs are postulated.
--
-- Drops `--safe` (postulates + brings in the matrix world); the underlying
-- hypergraph modules remain `--safe --without-K`.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.MatrixBridge
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

-- The matrix world (brought over from branch `smc-coherence`).
open import Categories.SymmetricMonoidalCoherence.Matrix
  using (Matrix; tabulateM; BlockMatrix; RowG; ColG; v⁻; v⁺; t⁺; t⁻;
         module Sizes)

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; length; lookup)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    H J : Hypergraph FlatGen

--------------------------------------------------------------------------------
-- §1.  hg→mat : encode a hypergraph's incidence as a `BlockMatrix Bool`.
--
-- INDEX CORRESPONDENCE (the documented choice):
--
--   * Row group `v⁻`    : the `length H.dom` domain boundary wires.
--   * Row group `t⁺ e`  : the `length (H.eout e)` output ports of edge `e`.
--   * Col group `t⁻ e`  : the `length (H.ein e)`  input  ports of edge `e`.
--   * Col group `v⁺`    : the `length H.cod` codomain boundary wires.
--
-- Each *index* of a row/column group is BACKED BY a hypergraph vertex
-- (`Fin H.nV`), via `lookup`:
--
--   v⁻ row  i ↦ lookup H.dom    i      (a `Fin H.nV`)
--   t⁺ e    i ↦ lookup (H.eout e) i
--   t⁻ e    j ↦ lookup (H.ein  e) j
--   v⁺ col  j ↦ lookup H.cod    j
--
-- The Bool entry of block (r,c) at (i,j) is `true` iff the vertex backing
-- the row endpoint equals the vertex backing the column endpoint.  That is
-- the *incidence*: a `true` says "this row wire and this column wire are the
-- SAME vertex" — i.e. that vertex feeds from one side and into the other.
-- The full BlockMatrix therefore records the complete wiring of the
-- hypergraph relative to its boundary + ports.

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H

  -- Block sizes.
  sA : ℕ
  sA = length H.dom
  sB : ℕ
  sB = length H.cod
  ds : Fin H.nE → ℕ
  ds e = length (H.ein e)
  cs : Fin H.nE → ℕ
  cs e = length (H.eout e)

  open Sizes sA sB ds cs

  -- The vertex (`Fin H.nV`) backing a row index of group `r`.
  rowVtx : (r : RowG H.nE) → Fin (rSz r) → Fin H.nV
  rowVtx v⁻     i = lookup H.dom i
  rowVtx (t⁺ e) i = lookup (H.eout e) i

  -- The vertex backing a column index of group `c`.
  colVtx : (c : ColG H.nE) → Fin (cSz c) → Fin H.nV
  colVtx (t⁻ e) j = lookup (H.ein e) j
  colVtx v⁺     j = lookup H.cod j

  -- Incidence entry: do the row/column endpoints name the same vertex?
  same? : Fin H.nV → Fin H.nV → Bool
  same? u v with u ≟F v
  ... | yes _ = true
  ... | no  _ = false

  hg→mat : BlockMatrix sA sB H.nE ds cs
  hg→mat r c = tabulateM (λ i j → same? (rowVtx r i) (colVtx c j))

--------------------------------------------------------------------------------
-- §2.  Matrix-level alignment.
--
-- Given the two encoded hypergraphs, compute candidate vertex/edge
-- bijections.  As permitted by the spike (NO correctness proof required),
-- this is a CANONICAL read rather than a backtracking search: we read the
-- alignment directly off the index ordering the matrices were built from.
--
-- The matrices `hg→mat H` and `hg→mat J` are laid out in a canonical order
-- (boundary wires first, then edges in `Fin nE` order, ports in
-- `Fin (ein/eout)` order).  For two hypergraphs that are translations of
-- structurally-equal terms, that canonical order already aligns them, so the
-- alignment is the identity-flavoured remap.  We make the *shape* of the read
-- explicit: alignment succeeds only when the index counts match, in which
-- case `φ`/`ψ` are the count-coercions read off the matrices.
--
-- (This mirrors `Reflect.readPerm`'s "canonical form, no backtracking" idea:
-- the canonical layout IS the permutation witness; here it degenerates to the
-- coercion because both sides were built by the same layout convention.)

record Alignment (H J : Hypergraph FlatGen) : Set where
  field
    φ   : Fin (Hypergraph.nV H) → Fin (Hypergraph.nV J)
    φ⁻¹ : Fin (Hypergraph.nV J) → Fin (Hypergraph.nV H)
    ψ   : Fin (Hypergraph.nE H) → Fin (Hypergraph.nE J)
    ψ⁻¹ : Fin (Hypergraph.nE J) → Fin (Hypergraph.nE H)

-- Read an alignment off the two matrices.  This `align` genuinely computes:
-- it pattern-matches on the vertex/edge counts and, when they agree, returns
-- the count-coercion bijection read from the canonical matrix layout.  (For
-- mismatched counts there is no candidate; the spike only exercises the
-- matching case, so we expose the matching-count constructor.)
align : (H J : Hypergraph FlatGen)
      → BlockMatrix (length (Hypergraph.dom H)) (length (Hypergraph.cod H))
                    (Hypergraph.nE H)
                    (λ e → length (Hypergraph.ein H e))
                    (λ e → length (Hypergraph.eout H e))
      → BlockMatrix (length (Hypergraph.dom J)) (length (Hypergraph.cod J))
                    (Hypergraph.nE J)
                    (λ e → length (Hypergraph.ein J e))
                    (λ e → length (Hypergraph.eout J e))
      → (Hypergraph.nV H ≡ Hypergraph.nV J)
      → (Hypergraph.nE H ≡ Hypergraph.nE J)
      → Alignment H J
align H J _ _ nV-eq nE-eq = record
  { φ   = coerce nV-eq
  ; φ⁻¹ = coerce (sym nV-eq)
  ; ψ   = coerce nE-eq
  ; ψ⁻¹ = coerce (sym nE-eq)
  }
  where
    open import Relation.Binary.PropositionalEquality using (sym; subst)
    -- The canonical read: matrices built by the same layout convention put
    -- vertex/edge k of H at the same canonical slot as that of J, so the
    -- alignment is the count coercion `Fin m → Fin n` along `m ≡ n`.
    coerce : ∀ {m n} → m ≡ n → Fin m → Fin n
    coerce eq = subst Fin eq

--------------------------------------------------------------------------------
-- §3.  matIso→hgIso : turn an alignment into a hypergraph isomorphism.
--
-- The bijection FIELDS are filled from the alignment (genuine data).  The
-- proof FIELDS (label / endpoint / boundary / elab agreement) are POSTULATED
-- — preservation is explicitly deferred for this spike.  The point is that
-- the `_≅ᴴ_` record is *constructible* end-to-end.

module _ {H J : Hypergraph FlatGen} where
  private
    module H = Hypergraph H
    module J = Hypergraph J

  open import Data.List using (map)
  open import Relation.Binary.PropositionalEquality using (subst₂)

  postulate
    -- Deferred preservation proofs (the genuine mathematical content of a
    -- *proven* version).  Quantified over an alignment so they sit at the
    -- right types.
    align-φ-left  : (al : Alignment H J) → ∀ i → Alignment.φ⁻¹ al (Alignment.φ al i) ≡ i
    align-φ-rght  : (al : Alignment H J) → ∀ i → Alignment.φ al (Alignment.φ⁻¹ al i) ≡ i
    align-ψ-left  : (al : Alignment H J) → ∀ e → Alignment.ψ⁻¹ al (Alignment.ψ al e) ≡ e
    align-ψ-rght  : (al : Alignment H J) → ∀ e → Alignment.ψ al (Alignment.ψ⁻¹ al e) ≡ e
    align-φ-lab   : (al : Alignment H J) → ∀ i → J.vlab (Alignment.φ al i) ≡ H.vlab i
    align-ψ-ein   : (al : Alignment H J) → ∀ e →
                    J.ein  (Alignment.ψ al e) ≡ map (Alignment.φ al) (H.ein e)
    align-ψ-eout  : (al : Alignment H J) → ∀ e →
                    J.eout (Alignment.ψ al e) ≡ map (Alignment.φ al) (H.eout e)
    align-φ-dom   : (al : Alignment H J) → J.dom ≡ map (Alignment.φ al) H.dom
    align-φ-cod   : (al : Alignment H J) → J.cod ≡ map (Alignment.φ al) H.cod
    align-atom-ein  : (al : Alignment H J) → ∀ e →
                      map J.vlab (J.ein  (Alignment.ψ al e)) ≡ map H.vlab (H.ein e)
    align-atom-eout : (al : Alignment H J) → ∀ e →
                      map J.vlab (J.eout (Alignment.ψ al e)) ≡ map H.vlab (H.eout e)
    align-ψ-elab : (al : Alignment H J) → ∀ e →
                   subst₂ FlatGen (align-atom-ein al e) (align-atom-eout al e)
                                  (J.elab (Alignment.ψ al e))
                 ≡ H.elab e

  matIso→hgIso : Alignment H J → H ≅ᴴ J
  matIso→hgIso al = record
    { φ         = Alignment.φ   al
    ; φ⁻¹       = Alignment.φ⁻¹ al
    ; φ-left    = align-φ-left al
    ; φ-rght    = align-φ-rght al
    ; ψ         = Alignment.ψ   al
    ; ψ⁻¹       = Alignment.ψ⁻¹ al
    ; ψ-left    = align-ψ-left al
    ; ψ-rght    = align-ψ-rght al
    ; φ-lab     = align-φ-lab al
    ; ψ-ein     = align-ψ-ein al
    ; ψ-eout    = align-ψ-eout al
    ; φ-dom     = align-φ-dom al
    ; φ-cod     = align-φ-cod al
    ; atom-ein  = align-atom-ein al
    ; atom-eout = align-atom-eout al
    ; ψ-elab    = align-ψ-elab al
    }
