{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruned cospan composition.  The output's vertex count is
-- `G.nV + count-non K.dom` (pruned) rather than `G.nV + K.nV`: pruning
-- drops every K-side vertex in `K.dom`, since those positions are glued to
-- the corresponding `G.cod` entry and are unreferenced in the composite.
-- Relies on `Util.Prune.remap` and its label-preservation lemmas.
--
-- DESIGN: pruning lets the vertex counts line up so the ≈Term laws
-- (where the unpruned LHS would have strictly more vertices than the
-- RHS) become provable.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Model.PrunedCompose (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.APROP.Hypergraph.Util.Prune


open import Data.Fin using (Fin; zero; suc; _↑ˡ_; splitAt; cast)
open import Data.Fin.Properties
open import Data.List.Properties
open import Data.Nat
open import Data.Sum using ([_,_]′)


--------------------------------------------------------------------------------
-- "Boundary lookup" lemma: two lists with matching mapped images have
-- pointwise-agreeing lookups (up to `Fin.cast`).  Main ingredient for
-- `bdy-pt`.

private
  -- Length equality derived from an equality of mapped lists.
  len-match : ∀ {A B Y : Set} (f : A → Y) (g : B → Y)
              (xs : List A) (ys : List B) → map f xs ≡ map g ys
            → length xs ≡ length ys
  len-match f g xs ys eq =
    trans (sym (length-map f xs))
          (trans (cong length eq) (length-map g ys))

  lookup-boundary : ∀ {A B Y : Set} (f : A → Y) (g : B → Y)
                      (xs : List A) (ys : List B)
                      (eq : map f xs ≡ map g ys)
                      (i : Fin (length xs))
                    → f (lookup xs i)
                    ≡ g (lookup ys (cast (len-match f g xs ys eq) i))
  lookup-boundary f g (x ∷ xs) (y ∷ ys) eq zero    = proj₁ (∷-injective eq)
  lookup-boundary f g (x ∷ xs) (y ∷ ys) eq (suc i) =
    lookup-boundary f g xs ys (proj₂ (∷-injective eq)) i

--------------------------------------------------------------------------------
-- Module-parameterised construction (parallel to `FromAPROP.hTensor-impl`).

module hComposeP-impl
  (G K : Hypergraph FlatGen)
  (bdy-eq : codL G ≡ domL K)
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K

  -- K.dom and G.cod have the same length (both vertex-backings for Bs).
  dom-cod-len : length K.dom ≡ length G.cod
  dom-cod-len =
    trans (sym (length-map K.vlab K.dom))
          (trans (cong length (sym bdy-eq))
                 (length-map G.vlab G.cod))

  -- Lookup into G.cod indexed by a position in K.dom.  Uses `Fin.cast`
  -- (proof-irrelevant) to avoid getting stuck on specific proof terms.
  lookup-cod : Fin (length K.dom) → Fin G.nV
  lookup-cod i = lookup G.cod (cast dom-cod-len i)

  -- Pruning remap: K-side vertices → G-side positions (via `lookup-cod`)
  -- for members of K.dom, else a fresh pruned slot.
  remapP : Fin K.nV → Fin (G.nV + count-non K.dom)
  remapP = remap K.dom lookup-cod

  nV-P : ℕ
  nV-P = G.nV + count-non K.dom

  λ-pruned : Fin (count-non K.dom) → X
  λ-pruned j = K.vlab (lookup (nonMem K.dom) j)

  vlab-P : Fin nV-P → X
  vlab-P v = [ G.vlab , λ-pruned ]′ (splitAt G.nV v)

  -- Injection of G-side vertices into the pruned composite.
  injL : Fin G.nV → Fin nV-P
  injL i = i ↑ˡ count-non K.dom

  vlab-injL : ∀ i → vlab-P (injL i) ≡ G.vlab i
  vlab-injL i = cong [ G.vlab , λ-pruned ]′ (splitAt-↑ˡ G.nV i (count-non K.dom))

  --------------------------------------------------------------------------------
  -- Boundary agreement and the label lemma for remapP.

  -- Pointwise `K.vlab (K.dom[i]) ≡ G.vlab (lookup-cod i)`, from the
  -- boundary equation `bdy-eq`.
  bdy-pt : ∀ i → K.vlab (lookup K.dom i) ≡ G.vlab (lookup-cod i)
  bdy-pt = lookup-boundary K.vlab G.vlab K.dom G.cod (sym bdy-eq)

  remapP-vlab : ∀ v → vlab-P (remapP v) ≡ K.vlab v
  remapP-vlab = remap-vlab K.dom lookup-cod K.vlab G.vlab bdy-pt

  map-via-remapP : (xs : List (Fin K.nV))
                 → map K.vlab xs ≡ map vlab-P (map remapP xs)
  map-via-remapP = map-via-remap K.dom lookup-cod K.vlab G.vlab bdy-pt

  --------------------------------------------------------------------------------
  -- Edge structure: G-edges routed through `injL`, K-edges through `remapP` —
  -- `FromAPROP.CoproductEdges` at those two maps.

  open CoproductEdges G K nV-P vlab-P injL remapP
         (map-via vlab-injL) map-via-remapP public

--------------------------------------------------------------------------------
-- The pruned cospan composition.

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

--------------------------------------------------------------------------------
-- Boundary lemmas: `domL` of a pruned composition equals `domL G`, and
-- `codL` equals `codL K` (after applying remap).

domL-hComposeP : ∀ G K bdy-eq → domL (hComposeP G K bdy-eq) ≡ domL G
domL-hComposeP G K bdy-eq =
  sym (map-via (hComposeP-impl.vlab-injL G K bdy-eq) _)

codL-hComposeP : ∀ G K bdy-eq → codL (hComposeP G K bdy-eq) ≡ codL K
codL-hComposeP G K bdy-eq = sym (hComposeP-impl.map-via-remapP G K bdy-eq _)
