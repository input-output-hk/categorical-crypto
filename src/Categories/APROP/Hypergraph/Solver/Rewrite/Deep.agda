{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Deep position search: the `subMatch → decode` bridge.
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

module Categories.APROP.Hypergraph.Solver.Rewrite.Deep (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec using (sig; _≟X_; _≟-ObjTerm_)
open import Categories.APROP using (module APROP)
open APROP sig

open import Data.Fin using (Fin)
open import Data.List.Base
  using (List; []; _∷_; _++_; map; mapMaybe; concatMap; length; lookup)
open import Data.List.Properties using (≡-dec)
open import Data.List.Properties.Ext using (lookupMaybe)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (dec⇒maybe)

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch sig-dec
  using (subMatchAll; _↪ᴴ_)
open import Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig-dec
  using (Foc)
open import Categories.APROP.Hypergraph.Solver.Rewrite.Kahn using (kahn)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; _≅_)

import Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig
import Categories.APROP.Hypergraph.Model.FromAPROP
import Categories.APROP.Hypergraph.Solver.Rewrite.DecodeLean
import Categories.APROP.Hypergraph.Soundness.Base.Unflatten
import Categories.APROP.Hypergraph.Solver.Rewrite.Carve

private
  _≟LX_ = ≡-dec _≟X_

--------------------------------------------------------------------------------
-- All machinery at a fixed hole arity `P Q` (the rule's interface).

module At (P Q : ObjTerm) where

  module Ext = Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig sig-dec P Q
  open Ext using (hole!; sig⁺; sig⁺-dec; relabel; retract)

  module F⁺ = Categories.APROP.Hypergraph.Model.FromAPROP sig⁺
  module DL⁺ = Categories.APROP.Hypergraph.Solver.Rewrite.DecodeLean sig⁺
  module U⁺ = Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig⁺
  module C⁺ = Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig⁺-dec

  open APROP sig⁺ using () renaming (Agen to Agen⁺)

  ------------------------------------------------------------------------------
  -- Carving.  Parameterised by the matched embedding `L ↪ᴴ S`.

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

    -- Kahn topological ordering (shared generic engine in `Rewrite.Kahn`,
    -- instantiated at `E = Edge`): emit edges in dependency order so `decode`
    -- always has each edge's inputs on the stack.  A non-convex match (a path
    -- leaves and re-enters the redex through the hole) leaves no edge ready
    -- and fails.

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
      Maybe.map assemble (kahn Edge.ins Edge.outs S.dom (he ∷ complement))

  ------------------------------------------------------------------------------
  -- The bridge: carve, decode, focus the hole, retract, glue —
  -- attempted per embedding.  A `nothing` here (non-convex occurrence, or any
  -- glue mismatch) sends the caller on to the NEXT match, so a bad first
  -- match cannot mask a rewritable later one.

  tryEmb : ∀ {A B} (s : HomTerm A B) (lᵗ : HomTerm P Q)
         → ⟪ lᵗ ⟫ ↪ᴴ ⟪ s ⟫ → Maybe (Foc A B P Q)
  tryEmb {A} {B} s lᵗ emb =
    Build.holeGraph ⟪ lᵗ ⟫ ⟪ s ⟫ emb           >>= λ H' →
    DL⁺.decode-attempt H'                      >>= λ ctx →
    C⁺.focusAtₙ ctx (Agen⁺ hole!) 0            >>= λ { (k , pre⁺ , post⁺) →
    retract pre⁺                               >>= λ pre₀ →
    retract post⁺                              >>= λ post₀ →
    -- Glue: `decode`'s endpoints are `U⁺.unflatten` of the carved boundary;
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
      decide-≡ Z W = dec⇒maybe (Z ≟-ObjTerm W)

  -- All carvable positions, one per successful embedding, in match order.
  deepFocAllAt : ∀ {A B} (s : HomTerm A B) (lᵗ : HomTerm P Q) → List (Foc A B P Q)
  deepFocAllAt s lᵗ = mapMaybe (tryEmb s lᵗ) (subMatchAll ⟪ lᵗ ⟫ ⟪ s ⟫)

--------------------------------------------------------------------------------
-- Pad handling.  A rule LHS with a bare identity wire (`x ⊗ id {Var w}` or
-- `id {Var w} ⊗ x`) is not edge-matchable as written — the wire's vertex is
-- incident to no edge.  But its soundness proof may be available ONLY at the
-- padded type (`⊗` is not faithful, so `f ⊗ id ≈ g ⊗ id` does not yield
-- `f ≈ g`).  We therefore strip the padding from the match QUERY only: find
-- positions of the stripped core, then REPAD each resulting frame — peel a
-- wire of matching atom type out of the pad object `k` and route it (by a
-- σ/α coherence term) to sit beside the core, so the frame can use the
-- original padded `lᵗ`/`rᵗ` and the original soundness proof at their own
-- types.  Any same-typed parallel wire works diagrammatically (the wire just
-- passes through the rule's vacuous slot); the downstream `findIso`
-- certificates remain the gate.
--
-- Scope: pad layers of shape `– ⊗ id {Var w}` / `id {Var w} ⊗ –`,
-- syntactically outermost, recursively (state multi-wire pads as nested
-- single-atom layers).

private
  -- Ways to extract one `w`-atom wire from `k`, routing it to the `place` slot
  -- of a parametric block `Xo` (and back: the contexts need both directions).
  Peel : (k : ObjTerm) (place : ObjTerm → ObjTerm) → Set
  Peel k place =
    Σ ObjTerm λ k₁ →
      (∀ Xo → HomTerm (k ⊗₀ Xo) (k₁ ⊗₀ place Xo))
      × (∀ Xo → HomTerm (k₁ ⊗₀ place Xo) (k ⊗₀ Xo))

  -- One recursion for both pad directions: it needs only the `Var`-leaf routing
  -- pair and the pair that moves `place` across a `⊗₀` (α on the right, σ left).
  module Peeler (w : X) (place : ObjTerm → ObjTerm)
                (leafD : ∀ Xo → HomTerm (Var w ⊗₀ Xo) (unit ⊗₀ place Xo))
                (leafU : ∀ Xo → HomTerm (unit ⊗₀ place Xo) (Var w ⊗₀ Xo))
                (bracD : ∀ {Y Z} → HomTerm (place (Y ⊗₀ Z)) (Y ⊗₀ place Z))
                (bracU : ∀ {Y Z} → HomTerm (Y ⊗₀ place Z) (place (Y ⊗₀ Z)))
                where
    peel : (k : ObjTerm) → List (Peel k place)
    peel unit       = []
    peel (Var w')   with w' ≟X w
    ... | yes refl = (unit , leafD , leafU) ∷ []
    ... | no  _    = []
    peel (kl ⊗₀ kr) = map liftL (peel kl) ++ map liftR (peel kr)
      where
        liftL : Peel kl place → Peel (kl ⊗₀ kr) place
        liftL (k₁ , r , u) = k₁ ⊗₀ kr
          , (λ Xo → α⇐ ∘ (id ⊗₁ bracD) ∘ r (kr ⊗₀ Xo) ∘ α⇒)
          , (λ Xo → α⇐ ∘ u (kr ⊗₀ Xo) ∘ (id ⊗₁ bracU) ∘ α⇒)
        liftR : Peel kr place → Peel (kl ⊗₀ kr) place
        liftR (k₁ , r , u) = kl ⊗₀ k₁
          , (λ Xo → α⇐ ∘ (id ⊗₁ r Xo) ∘ α⇒)
          , (λ Xo → α⇐ ∘ (id ⊗₁ u Xo) ∘ α⇒)

  -- Repad one frame for each peel candidate.
  repad : ∀ {A B P Q} (place : ObjTerm → ObjTerm)
        → (∀ k → List (Peel k place)) → Foc A B P Q
        → List (Foc A B (place P) (place Q))
  repad {P = P} {Q = Q} place peels (k , pre , post) =
    map (λ { (k₁ , r , u) → k₁ , r P ∘ pre , post ∘ u Q }) (peels k)

  repadR : ∀ {A B P Q} (w : X) → Foc A B P Q → List (Foc A B (P ⊗₀ Var w) (Q ⊗₀ Var w))
  repadR w = repad (λ Xo → Xo ⊗₀ Var w)
                   (Peeler.peel w _ (λ _ → λ⇐ ∘ σ) (λ _ → σ ∘ λ⇒) α⇒ α⇐)

  repadL : ∀ {A B P Q} (w : X) → Foc A B P Q → List (Foc A B (Var w ⊗₀ P) (Var w ⊗₀ Q))
  repadL w = repad (λ Xo → Var w ⊗₀ Xo)
                   (Peeler.peel w _ (λ _ → λ⇐) (λ _ → λ⇒)
                                (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))

--------------------------------------------------------------------------------
-- Top-level entry points (pad-aware).

deepFocAll : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) → List (Foc A B P Q)
deepFocAll s (x ⊗₁ id {Var w}) = concatMap (repadR w) (deepFocAll s x)
deepFocAll s (id {Var w} ⊗₁ x) = concatMap (repadL w) (deepFocAll s x)
deepFocAll {P = P} {Q = Q} s lᵗ = At.deepFocAllAt P Q s lᵗ

deepFocₙ : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) → ℕ → Maybe (Foc A B P Q)
deepFocₙ s lᵗ n = lookupMaybe (deepFocAll s lᵗ) n

deepFoc : ∀ {A B P Q} (s : HomTerm A B) (lᵗ : HomTerm P Q) → Maybe (Foc A B P Q)
deepFoc s lᵗ = deepFocₙ s lᵗ 0
