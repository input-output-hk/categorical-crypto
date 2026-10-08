{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruned boundary reindexing, not an unrestricted pushout of raw cospans.
-- Repeated K.dom vertices must correspond to equal G.cod vertices for the
-- seam equation: equality of boundary atom lists alone does not imply this.
-- Unique K.dom suffices; Unique G.cod instead supplies lookup-cod injectivity.
-- Keeping G's vertices and only K's non-boundary vertices aligns vertex
-- counts across the ≈Term laws on translated linear graphs.
--------------------------------------------------------------------------------

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Model.PrunedCompose (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Categories.APROP.Hypergraph.Util.Prune

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; splitAt; cast)
open import Data.Fin.Properties
open import Data.List.Properties
open import Data.List.Properties.Ext
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat
open import Data.Sum using ([_,_]′)

open APROP sig

module hComposeP-impl
  (G K : Hypergraph FlatGen)
  (bdy-eq : codL G ≡ domL K)
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K

  dom-cod-len : length K.dom ≡ length G.cod
  dom-cod-len =
    trans (sym (length-map K.vlab K.dom))
          (trans (cong length (sym bdy-eq))
                 (length-map G.vlab G.cod))

  -- Fin.cast avoids getting stuck on the specific length-equality proof.
  lookup-cod : Fin (length K.dom) → Fin G.nV
  lookup-cod i = lookup G.cod (cast dom-cod-len i)

  remapP : Fin K.nV → Fin (G.nV + count-non K.dom)
  remapP = remap K.dom lookup-cod

  nV-P : ℕ
  nV-P = G.nV + count-non K.dom

  λ-pruned : Fin (count-non K.dom) → X
  λ-pruned j = K.vlab (lookup (nonMem K.dom) j)

  vlab-P : Fin nV-P → X
  vlab-P v = [ G.vlab , λ-pruned ]′ (splitAt G.nV v)

  injL : Fin G.nV → Fin nV-P
  injL i = i ↑ˡ count-non K.dom

  SeamCompatible : Set
  SeamCompatible = ∀ i j → lookup K.dom i ≡ lookup K.dom j → lookup-cod i ≡ lookup-cod j

  seam-compatible-Unique : Unique K.dom → SeamCompatible
  seam-compatible-Unique unique i j eq =
    cong lookup-cod (lookup-injective-unique unique i j eq)

  remapP-seam : SeamCompatible → ∀ i → remapP (lookup K.dom i) ≡ injL (lookup-cod i)
  remapP-seam = remap-lookup-compatible K.dom lookup-cod

  vlab-injL : ∀ i → vlab-P (injL i) ≡ G.vlab i
  vlab-injL i = cong [ G.vlab , λ-pruned ]′ (splitAt-↑ˡ G.nV i (count-non K.dom))

  bdy-pt : ∀ i → K.vlab (lookup K.dom i) ≡ G.vlab (lookup-cod i)
  bdy-pt = lookup-boundary K.vlab G.vlab K.dom G.cod (sym bdy-eq)

  remapP-vlab : ∀ v → vlab-P (remapP v) ≡ K.vlab v
  remapP-vlab = remap-vlab K.dom lookup-cod K.vlab G.vlab bdy-pt

  map-via-remapP : (xs : List (Fin K.nV))
                 → map K.vlab xs ≡ map vlab-P (map remapP xs)
  map-via-remapP = map-via-remap K.dom lookup-cod K.vlab G.vlab bdy-pt

  open CoproductEdges G K nV-P vlab-P injL remapP
         (map-via vlab-injL) map-via-remapP public

hComposeP : (G K : Hypergraph FlatGen) → codL G ≡ domL K → Hypergraph FlatGen
hComposeP G K bdy-eq = record
  { nV = nV-P
  ; vlab = vlab-P
  ; nE = G.nE + K.nE
  ; ein = ein-c
  ; eout = eout-c
  ; elab = elab-c
  ; dom = map injL G.dom
  ; cod = map remapP K.cod
  }
  where
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K bdy-eq

domL-hComposeP : ∀ G K bdy-eq → domL (hComposeP G K bdy-eq) ≡ domL G
domL-hComposeP G K bdy-eq =
  sym (map-via (hComposeP-impl.vlab-injL G K bdy-eq) _)

codL-hComposeP : ∀ G K bdy-eq → codL (hComposeP G K bdy-eq) ≡ codL K
codL-hComposeP G K bdy-eq = sym (hComposeP-impl.map-via-remapP G K bdy-eq _)
