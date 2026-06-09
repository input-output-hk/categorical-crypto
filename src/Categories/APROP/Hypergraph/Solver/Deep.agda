{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Deep position search: the `subMatch → decode` bridge (Phases B+C).
--
-- `focusAt` only finds redexes that are *subterms* of the written syntax.
-- `deepFoc` finds a redex that is a connected sub-diagram of the hypergraph
-- `⟪ s ⟫`, however `s` was bracketed (e.g. an `l = b ∘ a` split across an
-- interchange `(b ⊗ d) ∘ (a ⊗ c)`).  Pipeline:
--
--   1. `subMatch ⟪lᵗ⟫ ⟪s⟫`            — locate the redex edges (embedding);
--   2. `holeGraph`                     — delete them, add ONE hole edge
--      `h : P → Q` over the extended signature `sig⁺ = sig + h`, emitting
--      edges in a Kahn topological order (failure ⇒ non-convex match);
--   3. `decode-attempt` (at `sig⁺`)    — hypergraph → term `ctx[h]`;
--   4. `focusAt ctx (Agen h)`          — the hole is a syntactic leaf, so
--      term-level focusing always frames it;
--   5. `retract` + coherence glue      — strip the hole signature from the
--      contexts and land back on `s`'s endpoint objects.
--
-- Everything here is *unverified* search: a wrong result simply fails the
-- caller's `findIso ⟪ s ⟫ ⟪ post ∘ (id ⊗ lᵗ) ∘ pre ⟫` certification.  Where a
-- propositional fact is needed to type a step (e.g. the hole edge's atom
-- lists), we *decide* it at run time instead of proving it, keeping the glue
-- dumb and robust.
--------------------------------------------------------------------------------

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Solver.Deep (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟X_; _≟-ObjTerm_)
open import Categories.APROP using (module APROP)
open APROP sig

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe.Base using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Base as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.SubMatch sig-dec
  using (subMatch; _↪ᴴ_)
open import Categories.APROP.Hypergraph.Solver.Carve sig-dec using (Foc)
open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-flatten-≈; _≅_)

import Categories.APROP.Hypergraph.Solver.ExtendSig
import Categories.APROP.Hypergraph.FromAPROP
import Categories.APROP.Hypergraph.Soundness.Decode
import Categories.APROP.Hypergraph.Soundness.Unflatten
import Categories.APROP.Hypergraph.Solver.Carve

private
  _≟LX_ = ≡-dec _≟X_

--------------------------------------------------------------------------------
-- All machinery at a fixed hole arity `P Q` (the rule's interface).

module At (P Q : ObjTerm) where

  module Ext = Categories.APROP.Hypergraph.Solver.ExtendSig sig-dec P Q
  open Ext using (old; hole!; sig⁺; sig⁺-dec; relabel; retract)

  module F⁺ = Categories.APROP.Hypergraph.FromAPROP sig⁺
  module D⁺ = Categories.APROP.Hypergraph.Soundness.Decode sig⁺
  module U⁺ = Categories.APROP.Hypergraph.Soundness.Unflatten sig⁺
  module C⁺ = Categories.APROP.Hypergraph.Solver.Carve sig⁺-dec

  open APROP sig⁺ using ()
    renaming (HomTerm to HomTerm⁺; Agen to Agen⁺)

  ------------------------------------------------------------------------------
  -- Carving (Phase B).  Parameterised by the matched embedding `L ↪ᴴ S`.

  module Build (L S : Hypergraph FlatGen) (emb : L ↪ᴴ S) where
    private
      module S = Hypergraph S
      open _↪ᴴ_ emb using (ψ⁻¹; boundary-dom; boundary-cod)

    -- An edge descriptor of the carved graph: endpoints in `S`'s vertex set,
    -- label over the extended signature.
    record Edge : Set where
      constructor edge
      field
        ins outs : List (Fin S.nV)
        lab      : F⁺.FlatGen (map S.vlab ins) (map S.vlab outs)

    -- The complement edges: those of `S` not in the match's `ψ`-image.
    complement : List Edge
    complement = keep (range S.nE)
      where
        keep : List (Fin S.nE) → List Edge
        keep []       = []
        keep (e ∷ es) with ψ⁻¹ e
        ... | just _  = keep es
        ... | nothing = edge (S.ein e) (S.eout e) (relabel (S.elab e)) ∷ keep es

    -- The hole edge `h : boundary-dom → boundary-cod`.  Its atom lists agree
    -- with `flatten P` / `flatten Q` because the embedding preserves labels;
    -- rather than prove it, decide it (a `no` cannot occur).
    holeEdge : Maybe Edge
    holeEdge
      with map S.vlab boundary-dom ≟LX F⁺.flatten P
         | map S.vlab boundary-cod ≟LX F⁺.flatten Q
    ... | yes p | yes q =
          just (edge boundary-dom boundary-cod
                     (subst₂ F⁺.FlatGen (sym p) (sym q) (F⁺.flat hole!)))
    ... | _ | _ = nothing

    -- Kahn topological ordering.  `decode` consumes edges in Fin order, each
    -- needing its inputs on the stack; emitting edges in dependency order
    -- guarantees that.  Greedy choice suffices on a DAG; if no edge is ready
    -- the match was non-convex (a path leaves and re-enters the redex through
    -- the hole) and we fail.
    private
      remove1 : Fin S.nV → List (Fin S.nV) → Maybe (List (Fin S.nV))
      remove1 v []       = nothing
      remove1 v (w ∷ ws) with v ≟F w
      ... | yes _ = just ws
      ... | no  _ = Maybe.map (w ∷_) (remove1 v ws)

      consume : List (Fin S.nV) → List (Fin S.nV) → Maybe (List (Fin S.nV))
      consume []       avail = just avail
      consume (v ∷ vs) avail = remove1 v avail >>= consume vs

      -- First pending edge whose inputs are all available; returns the new
      -- availability and the remaining pending list (order preserved).
      findReady : List (Fin S.nV) → List Edge
                → Maybe (Edge × List (Fin S.nV) × List Edge)
      findReady avail []       = nothing
      findReady avail (e ∷ es) with consume (Edge.ins e) avail
      ... | just avail' = just (e , avail' , es)
      ... | nothing     =
            Maybe.map (λ { (r , av , rest) → (r , av , e ∷ rest) })
                      (findReady avail es)

      kahn : ℕ → List (Fin S.nV) → List Edge → Maybe (List Edge)
      kahn _          _     []      = just []
      kahn zero       _     _       = nothing
      kahn (suc fuel) avail pending with findReady avail pending
      ... | nothing                 = nothing
      ... | just (e , avail' , rest) =
            Maybe.map (e ∷_) (kahn fuel (avail' ++ Edge.outs e) rest)

    -- Assemble a hypergraph from an ordered edge list (vertices, labels, and
    -- boundary unchanged from `S`).
    private
      assemble : List Edge → Hypergraph F⁺.FlatGen
      assemble es = record
        { nV   = S.nV
        ; vlab = S.vlab
        ; nE   = length es
        ; ein  = λ i → Edge.ins  (lookup es i)
        ; eout = λ i → Edge.outs (lookup es i)
        ; elab = λ i → Edge.lab  (lookup es i)
        ; dom  = S.dom
        ; cod  = S.cod
        }

    holeGraph : Maybe (Hypergraph F⁺.FlatGen)
    holeGraph = holeEdge >>= λ he →
      let pending = he ∷ complement
      in Maybe.map assemble (kahn (suc (length pending)) S.dom pending)

  ------------------------------------------------------------------------------
  -- The bridge (Phase C): match, carve, decode, focus the hole, retract, glue.

  deepFocAt : ∀ {A B} (s : HomTerm A B) (lᵗ : HomTerm P Q)
            → Maybe (Foc A B P Q)
  deepFocAt {A} {B} s lᵗ =
    subMatch ⟪ lᵗ ⟫ ⟪ s ⟫                      >>= λ emb →
    Build.holeGraph ⟪ lᵗ ⟫ ⟪ s ⟫ emb           >>= λ H' →
    D⁺.decode-attempt H'                       >>= λ ctx →
    C⁺.focusAtₙ ctx (Agen⁺ hole!) 0            >>= λ { (k , pre⁺ , post⁺) →
    retract pre⁺                               >>= λ pre₀ →
    retract post⁺                              >>= λ post₀ →
    -- Glue: `decode`'s endpoints are `unflatten⁺` of the carved boundary;
    -- decide that they coincide with `unflatten (flatten –)` of `s`'s
    -- endpoints and bridge with the `unflatten-flatten-≈` coherence isos.
    decide-≡ (U⁺.unflatten (domL H')) (unflatten (flatten A)) >>= λ p →
    decide-≡ (U⁺.unflatten (codL H')) (unflatten (flatten B)) >>= λ q →
    just ( k
         , pre₀ ∘ subst (HomTerm A) (sym p) (_≅_.from (unflatten-flatten-≈ A))
         , subst (λ Z → HomTerm Z B) (sym q) (_≅_.to (unflatten-flatten-≈ B))
             ∘ post₀ ) }
    where
      decide-≡ : (Z W : ObjTerm) → Maybe (Z ≡ W)
      decide-≡ Z W with Z ≟-ObjTerm W
      ... | yes p = just p
      ... | no  _ = nothing

--------------------------------------------------------------------------------
-- Top-level entry point.

deepFoc : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q)
        → Maybe (Foc A B P Q)
deepFoc {P = P} {Q = Q} = At.deepFocAt P Q
