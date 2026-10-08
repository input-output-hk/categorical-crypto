{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Deep focusing finds carvable (convex), possibly disconnected sub-diagrams
-- independent of term bracketing.
-- Carve an embedding into one hole edge, decode over the extended signature,
-- focus the hole, then retract the contexts. Candidates are certified by
-- the caller's isomorphism gate, not by this search.
--
-- Identity padding: tensor is not faithful, so a padded rule's proof need not
-- hold for its core. Outermost single-atom pads `– ⊗ id {Var w}` and
-- `id {Var w} ⊗ –` are stripped from the match query only; each pad is then
-- bound to a distinct same-labelled context wire outside the core, and the
-- hole carries the full padded interface, so the rule keeps its own type.
-- Occurrences are ordered by core match, then by binding, lexicographically
-- along the rule's input interface (each pad by ascending vertex).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Rewrite.Deep (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
import Categories.APROP.Hypergraph.Model.FromAPROP
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Model.Translation sig
import Categories.APROP.Hypergraph.Solver.Rewrite.Carve
open import Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig
import Categories.APROP.Hypergraph.Solver.Rewrite.DecodeLean
import Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Kahn
open import Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch sig
import Categories.APROP.Hypergraph.Soundness.Base.Unflatten
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; _≅_)

open import Data.Fin hiding (_+_; splitAt)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat
open import Data.Product using (Σ; _×_; _,_; uncurry′)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (dec⇒maybe)

open APROP sig
open FreeMonoidalHelper Symm X using (flatten)

private
  variable
    A B P Q P₀ Q₀ : ObjTerm

  _≟LX_ = ≡-dec _≟X_

module At (P Q : ObjTerm) where

  module Ext = Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig sig P Q
  open Ext using (hole!; sig⁺; relabel; retract)

  module F⁺ = Categories.APROP.Hypergraph.Model.FromAPROP sig⁺
  module DL⁺ = Categories.APROP.Hypergraph.Solver.Rewrite.DecodeLean sig⁺
  module U⁺ = Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig⁺
  module C⁺ = Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig⁺

  open APROP sig⁺ using () renaming (Agen to Agen⁺)

  module Build (L S : Hypergraph FlatGen) (emb : L ↪ᴴ S) where
    private
      module L = Hypergraph L
      module S = Hypergraph S
      open _↪ᴴ_ emb using (φ; ψ⁻¹; boundary-dom; boundary-cod)

    record Edge : Set where
      constructor edge
      field ins outs : List (Fin S.nV)
            lab : F⁺.FlatGen (map S.vlab ins) (map S.vlab outs)

    complement : List Edge
    complement = keep (allFin S.nE)
      where
        keep : List (Fin S.nE) → List Edge
        keep []       = []
        keep (e ∷ es) with ψ⁻¹ e
        ... | just _  = keep es
        ... | nothing = edge (S.ein e) (S.eout e) (relabel (S.elab e)) ∷ keep es

    -- Decide the interface bridge at runtime; the embedding preserves labels.
    holeEdge : (ins outs : List (Fin S.nV)) → Maybe Edge
    holeEdge ins outs
      with map S.vlab ins ≟LX flatten P | map S.vlab outs ≟LX flatten Q
    ... | yes p | yes q = just (edge ins outs (F⁺.flat-rec (sym p) (sym q) hole!))
    ... | _     | _     = nothing

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
    holeGraph = holeEdge boundary-dom boundary-cod >>= λ he →
      Maybe.map assemble (kahn Edge.ins Edge.outs S.dom (he ∷ complement))

    -- Injective choices, one per pad, from that pad's same-labelled vertices
    -- outside the core image, lexicographic in the given order.
    bindings : List (List (Fin S.nV)) → List (List (Fin S.nV))
    bindings = choose (map φ (allFin L.nV))
      where
        choose : List (Fin S.nV) → List (List (Fin S.nV)) → List (List (Fin S.nV))
        choose used []         = [] ∷ []
        choose used (cs ∷ css) =
          concatMap (λ v → map (v ∷_) (choose (v ∷ used) css))
                    (filter (λ v → ¬? (any? (v ≟F_) used)) cs)

    -- Bound pad wires enter the hole's input and output. Kahn sees each one
    -- split: the hole consumes the old vertex and emits a fresh copy that the
    -- wire's consumer reads, so the binding schedules iff producer ≺ hole ≺
    -- consumer for every pad. The assembled graph keeps the vertex unsplit.
    private
      module Split (β : List (Fin S.nV)) where
        old copy : Fin S.nV → Fin (length β + S.nV)
        old    = length β ↑ʳ_
        copy v = Maybe.maybe′ (_↑ˡ S.nV) (old v) (findIndex (_≟F v) β)

        record Slot : Set where
          constructor slot
          field orig : Edge
                ins outs : List (Fin (length β + S.nV))

    holeGraphᵖ : List Edge → (βL βR : List (Fin S.nV))
               → Maybe (Hypergraph F⁺.FlatGen)
    holeGraphᵖ comp βL βR =
      holeEdge (βL ++ boundary-dom ++ βR) (βL ++ boundary-cod ++ βR) >>= λ he →
      Maybe.map (λ es → assemble (map Slot.orig es))
        (kahn Slot.ins Slot.outs (map old S.dom)
          (slot he (map old (Edge.ins he)) (map copy (Edge.outs he))
           ∷ map (λ e → slot e (map copy (Edge.ins e)) (map old (Edge.outs e)))
                 comp))
      where open Split (βL ++ βR)

  private
    focusHole : Hypergraph F⁺.FlatGen → Maybe (Foc A B P Q)
    focusHole {A} {B} H' =
      DL⁺.decode-attempt H'                      >>= λ ctx →
      C⁺.focusAtₙ ctx (Agen⁺ hole!) 0            >>= λ { (k , pre⁺ , post⁺) →
      retract pre⁺                               >>= λ pre₀ →
      retract post⁺                              >>= λ post₀ →
      decide-≡ (U⁺.unflatten (domL H')) (unflatten (flatten A)) >>= λ p →
      decide-≡ (U⁺.unflatten (codL H')) (unflatten (flatten B)) >>= λ q →
      just ( k
           , pre₀ ∘ subst (HomTerm A) (sym p) (_≅_.from (unflatten-flatten-≈ A))
           , subst (λ Z → HomTerm Z B) (sym q) (_≅_.to (unflatten-flatten-≈ B))
               ∘ post₀ ) }
      where
        decide-≡ : (Z W : ObjTerm) → Maybe (Z ≡ W)
        decide-≡ Z W = dec⇒maybe (Z ≟-ObjTerm W)

  -- Rejecting a non-convex occurrence must leave later embeddings available.

  tryEmb : (s : HomTerm A B) (core : HomTerm P₀ Q₀)
         → ⟪ core ⟫ ↪ᴴ ⟪ s ⟫ → Maybe (Foc A B P Q)
  tryEmb s core emb = Build.holeGraph ⟪ core ⟫ ⟪ s ⟫ emb >>= focusHole

  -- Per-embedding values are function arguments so that call-by-need
  -- evaluation shares them across bindings.
  private
    bindAll : {L S : Hypergraph FlatGen} (emb : L ↪ᴴ S)
            → ℕ → List (List (Fin (Hypergraph.nV S))) → List (Build.Edge L S emb)
            → List (Foc A B P Q)
    bindAll emb nL cands comp =
      mapMaybe (λ β → uncurry′ (Build.holeGraphᵖ _ _ emb comp) (splitAt nL β)
                        >>= focusHole)
               (Build.bindings _ _ emb cands)

    padded : {L S : Hypergraph FlatGen}
           → ℕ → List (List (Fin (Hypergraph.nV S))) → List (L ↪ᴴ S)
           → List (Foc A B P Q)
    padded nL cands =
      concatMap λ emb → bindAll emb nL cands (Build.complement _ _ emb)

  -- Peel the pads into `ls`/`rs`, in input-interface order around the core,
  -- then dispatch once: an unpadded rule takes the plain core search.
  deepFocAllAt : (s : HomTerm A B)
               → List X → HomTerm P₀ Q₀ → List X → List (Foc A B P Q)
  deepFocAllAt s ls (x ⊗₁ id {Var w}) rs = deepFocAllAt s ls x (w ∷ rs)
  deepFocAllAt s ls (id {Var w} ⊗₁ x) rs = deepFocAllAt s (ls ∷ʳ w) x rs
  deepFocAllAt s [] core [] = mapMaybe (tryEmb s core) (subMatchAll ⟪ core ⟫ ⟪ s ⟫)
  deepFocAllAt s ls core rs =
    padded (length ls)
           (map (λ w → filter (λ v → S.vlab v ≟X w) (allFin S.nV)) (ls ++ rs))
           (subMatchAll ⟪ core ⟫ ⟪ s ⟫)
    where module S = Hypergraph ⟪ s ⟫

--------------------------------------------------------------------------------
-- Focus enumeration
--------------------------------------------------------------------------------

deepFocAll : (s : HomTerm A B) (lᵗ : HomTerm P Q) → List (Foc A B P Q)
deepFocAll {P = P} {Q = Q} s lᵗ = At.deepFocAllAt P Q s [] lᵗ []

deepFocₙ : (s : HomTerm A B) (lᵗ : HomTerm P Q) → ℕ → Maybe (Foc A B P Q)
deepFocₙ s lᵗ n = lookupMaybe (deepFocAll s lᵗ) n

deepFoc : (s : HomTerm A B) (lᵗ : HomTerm P Q) → Maybe (Foc A B P Q)
deepFoc s lᵗ = deepFocₙ s lᵗ 0
