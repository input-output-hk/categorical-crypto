{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Gate-only LEAN decode.
--
-- The term-building decoder used at the deep-rewrite search call site
-- (`Solver.Rewrite.Deep.tryEmb`, run over the EXTENDED signature `sig⁺`): from a
-- hypergraph it produces the `HomTerm` frame whose translation is handed to
-- the downstream `findIso`/`Verify` gate.
--
-- Relationship to `Soundness.Decode`.  `Decode` used to build this very
-- `HomTerm` alongside its stack, but Review-2 F2 (commit `d82a7be`) demoted it
-- to a bare-stack TOTALITY skeleton: its `edge-step`/`process-edges` now return
-- plain `List (Fin H.nV)` stacks and `decode-attempt` returns only a
-- `Maybe (↭)` totality witness.  `DecodeLean` is therefore the ONLY decoder
-- that still emits a term.  It reuses `Decode`'s shared search primitives
-- (`extract-prefix`, `extract-exact`) and its generic per-edge generator
-- (`Agen-edge-aux`), so its stack trajectory over `range H.nE` (in kahn order)
-- coincides definitionally with `Decode`'s bare-stack fold — that stack
-- agreement is exactly what makes `permOrId`'s list-equality guards below
-- (`s ≟ ein e ++ rest` at an edge step, `s_final ≟ H.cod` at the final
-- bridge) meaningful.
--
-- The identity-guard collapse: at each `permute-via-vlab` slot `DecodeLean`
-- adds a *decidable* identity pre-check.  When the running stack already
-- coincides (as a LIST, not merely as a multiset) with the target list —
-- `s ≟ ein e ++ rest` for an edge step, `s_final ≟ H.cod` for the final
-- permute — the locating permutation is the identity, so a naive full-permute
-- decoder would emit a `permute Perm.refl`-flavoured `id ⊗₁ (id ⊗₁ …)` tower
-- of `O(nV)` `id`s.  That tower translates (`⟪_⟫`) to edge-free `hId`s that are
-- *pruned* at the `hComposeP` seam, so dropping it leaves the translated
-- graph of the emitted frame IDENTICAL.
-- We therefore emit a single `id` (well-typed by the `refl` from the `≟`),
-- collapsing the bulk identity padding.  A *non*-identity permutation never
-- passes the `≟` guard, so it is never collapsed.
--
-- Because the identity-guard collapse keeps the translated graph identical,
-- the produced frame is iso-equivalent to the full-permute reference frame, so
-- this needs no `decode-lean ≈Term …` correctness proof: correctness comes
-- from the downstream `findIso ⟪ s ⟫ ⟪ frame ⟫` gate, which is decidable and
-- fails closed if a candidate is ever wrong.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Rewrite.DecodeLean (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flat-rec; range)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅; _≅_)
-- `permute` comes straight from `Categories.PermuteCoherence.Unflatten` (rather
-- than through any intermediate re-export) so the frame this decoder builds is
-- definitionally the generic-SMC one.
open import Categories.PermuteCoherence.Unflatten asFreeMonoidalData
  using (permute)

-- Shared search primitives from the soundness decoder: `extract-exact` (the
-- final exact-match search) and `extract-prefix`.  Reusing them keeps the edge
-- branching and the `nothing` discipline definitionally aligned with
-- `Decode`'s bare-stack fold.
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-exact; extract-prefix)

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (sym; cong; subst; subst₂)
open import Relation.Nullary using (yes; no)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- Apply an edge: recover the generator `g : mor A B` from a `FlatGen` record
-- (constructor `flat-rec`), then wrap with the unflatten-flatten coherence iso
-- on each side.  Top-level (not under the `H` module) so `Agen-edge` below can
-- be `cong`-rewritten along `elab` equations without an `H` argument.  This is
-- the ONLY term-emitting piece of the old decoder that survived the Review-2
-- demotion, and this is the only decoder that emits a term — so it lives here
-- rather than in the now-`List`-only `Soundness.Decode.Decode`.
Agen-edge-aux
  : ∀ {ins outs : List X} → FlatGen ins outs
  → HomTerm (unflatten ins) (unflatten outs)
Agen-edge-aux (flat-rec {A} {B} okA okB g) =
  subst₂ (λ a b → HomTerm (unflatten a) (unflatten b)) okA okB
    (_≅_.from (unflatten-flatten-≈ B) ∘ Agen g ∘ _≅_.to (unflatten-flatten-≈ A))

--------------------------------------------------------------------------------
-- A vertex-list permutation as a `HomTerm` on the unflattened tensor products,
-- indexed only by a labelling function.  (Its former home, the one-definition
-- `PermuteCoherence.Steps`, existed to share this with an APROP-side twin that
-- the weak-decoder demotion deleted — see `Soundness.Decode.Decode`'s NOTE.)

permute-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X)
  → xs Perm.↭ ys
  → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
permute-via-vlab vlab p = permute (PermProp.map⁺ vlab p)

--------------------------------------------------------------------------------
-- The cospan algorithm, with `H` fixed.  Same stack control flow as
-- `Decode`'s bare-stack fold, but building a `HomTerm` frame alongside the
-- stack; the two `permute-via-vlab` slots additionally carry an identity
-- guard.

module _ (H : Hypergraph FlatGen) where

  private
    module H = Hypergraph H

    _≟L_ : DecidableEquality (List (Fin H.nV))
    _≟L_ = ≡-dec _≟F_

  -- LEAN: the identity-guarded locating permutation, shared by the per-edge step
  -- and the final bridge.  Transporting with `subst` rather than matching `refl`
  -- is forced: `s` occurs in the result type via `map H.vlab s`, so it cannot be
  -- unified under the `with`-abstraction.
  permOrId
    : {s t : List (Fin H.nV)} → s Perm.↭ t
    → HomTerm (unflatten (map H.vlab s)) (unflatten (map H.vlab t))
  permOrId {s} {t} perm with s ≟L t
  ... | yes eq = subst (λ z → HomTerm (unflatten (map H.vlab s))
                                      (unflatten (map H.vlab z)))
                       eq id
  ... | no  _  = permute-via-vlab H.vlab perm

  Agen-edge
    : (e : Fin H.nE)
    → HomTerm (unflatten (map H.vlab (H.ein e)))
              (unflatten (map H.vlab (H.eout e)))
  Agen-edge e = Agen-edge-aux (H.elab e)

  --------------------------------------------------------------------
  -- Per-edge step.  Follows the same stack recurrence as `Decode.edge-step`
  -- (shared `extract-prefix` branching), but returns a `HomTerm` alongside the
  -- new stack; the locating permutation goes through `permOrId`.

  edge-step
    : (s : List (Fin H.nV)) (e : Fin H.nE)
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  edge-step s e with extract-prefix (H.ein e) s
  ... | nothing             = (s , id)
  ... | just (rest , perm)  = (H.eout e ++ rest , mid' ∘ permOrId perm)
    where
      ein-l  = map H.vlab (H.ein e)
      eout-l = map H.vlab (H.eout e)
      rest-l = map H.vlab rest

      -- Apply the edge generator at the front, identity on the rest.
      mid : HomTerm (unflatten (ein-l  ++ rest-l)) (unflatten (eout-l ++ rest-l))
      mid = _≅_.to   (unflatten-++-≅ eout-l rest-l)
            ∘ (Agen-edge e ⊗₁ id)
            ∘ _≅_.from (unflatten-++-≅ ein-l  rest-l)

      -- Bridge `map vlab (xs ++ ys) ≡ map vlab xs ++ map vlab ys` (`map-++`).
      mid' : HomTerm (unflatten (map H.vlab (H.ein e  ++ rest)))
                     (unflatten (map H.vlab (H.eout e ++ rest)))
      mid' = subst₂ HomTerm
              (cong unflatten (sym (map-++ H.vlab (H.ein  e) rest)))
              (cong unflatten (sym (map-++ H.vlab (H.eout e) rest)))
              mid

  --------------------------------------------------------------------
  -- Process all edges in natural Fin order; returns the final stack and a
  -- HomTerm from the original stack.  Same fold as `Decode.process-edges`,
  -- carrying the `HomTerm` that `Decode`'s bare-stack version drops.

  process-edges
    : List (Fin H.nE) → ∀ (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  process-edges []       s = (s , id)
  process-edges (e ∷ es) s =
    let (s'  , t)  = edge-step    s  e
        (s'' , t') = process-edges es s'
    in  (s'' , t' ∘ t)

  process-all-edges
    : ∀ (s : List (Fin H.nV))
    → Σ[ s' ∈ List (Fin H.nV) ]
        HomTerm (unflatten (map H.vlab s))
                (unflatten (map H.vlab s'))
  process-all-edges = process-edges (range H.nE)

  --------------------------------------------------------------------
  -- Run from `H.dom`, then bridge the final stack to `H.cod`.  LEAN: collapse
  -- the final permute when `s_final ≡ H.cod` as a list.

  decode-attempt : Maybe (HomTerm (unflatten (domL H)) (unflatten (codL H)))
  decode-attempt with process-all-edges H.dom
  ... | (s_final , process-term) with extract-exact H.cod s_final
  ...    | nothing   = nothing
  ...    | just perm = just (permOrId perm ∘ process-term)
