{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Pruned cospan composition (TODO.org Option A).
--
-- Identical to `FromAPROP.hCompose` except the output's vertex count is
--   G.nV + count-non K.dom       (pruned)
-- instead of
--   G.nV + K.nV                  (unpruned).
--
-- The pruning drops every K-side vertex that lives in `K.dom`, since those
-- positions have been "glued" to the corresponding `G.cod` entry and are
-- therefore unreferenced in the composite.
--
-- The construction relies on `Hypergraph.Prune.remap` plus its label-
-- preservation lemma `remap-vlab` / list-wise `map-via-remap`.
--
-- Usage downstream:
--   * Eventually `⟪ g ∘ f ⟫ = hComposeP ⟪ f ⟫ ⟪ g ⟫` (replaces the unpruned
--     version in `FromAPROP`).
--   * The group-(b)/(c) ≈Term axioms where LHS has strictly more vertices
--     than RHS become provable with `hComposeP`, because pruning lets the
--     vertex counts line up.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.PrunedCompose (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; map-via-inj)
open import Categories.APROP.Hypergraph.Prune
  using (count-non; nonMem; classify; remap; remap-vlab; map-via-remap)

open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; cast)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.List using (List; []; _∷_; length; map; lookup)
open import Data.List.Properties using (length-map; map-cong; map-∘)
open import Data.Nat using (ℕ; _+_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- Local helpers: "boundary lookup" lemma.
--
-- Given two lists with matching mapped images, their pointwise lookups agree
-- (up to `Fin.cast` across the length equality). This is the main ingredient
-- for `bdy-pt` below.

private
  ∷-head : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-head refl = refl

  ∷-tail : ∀ {A : Set} {x y : A} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-tail refl = refl

  -- Length equality derived from an equality of mapped lists.
  len-match : ∀ {A B Y : Set} (f : A → Y) (g : B → Y)
              (xs : List A) (ys : List B) → map f xs ≡ map g ys
            → length xs ≡ length ys
  len-match f g xs ys eq =
    trans (sym (length-map f xs))
          (trans (cong length eq) (length-map g ys))

  -- The boundary lookup lemma. Pointwise image agreement from list-wise
  -- image agreement: f (lookup xs i) ≡ g (lookup ys (cast ... i)).
  lookup-boundary : ∀ {A B Y : Set} (f : A → Y) (g : B → Y)
                      (xs : List A) (ys : List B)
                      (eq : map f xs ≡ map g ys)
                      (i : Fin (length xs))
                    → f (lookup xs i)
                    ≡ g (lookup ys (cast (len-match f g xs ys eq) i))
  lookup-boundary f g (x ∷ xs) (y ∷ ys) eq zero    = ∷-head eq
  lookup-boundary f g (x ∷ xs) (y ∷ ys) eq (suc i) =
    lookup-boundary f g xs ys (∷-tail eq) i

--------------------------------------------------------------------------------
-- Module-parameterised construction.
--
-- Parallel to `FromAPROP.hCompose-impl` but with pruning.

module hComposeP-impl
  (G K : Hypergraph FlatGen)
  (bdy-eq : codL G ≡ domL K)
  where

  private
    module G = Hypergraph G
    module K = Hypergraph K

  -- K.dom and G.cod have the same length: both are vertex-backings for Bs.
  dom-cod-len : length K.dom ≡ length G.cod
  dom-cod-len =
    trans (sym (length-map K.vlab K.dom))
          (trans (cong length (sym bdy-eq))
                 (length-map G.vlab G.cod))

  -- Lookup into G.cod indexed by a position in K.dom. Uses `Fin.cast`
  -- (proof-irrelevant) so we can reason equationally without getting
  -- stuck on specific proof terms.
  lookup-cod : Fin (length K.dom) → Fin G.nV
  lookup-cod i = lookup G.cod (cast dom-cod-len i)

  -- Pruning remap: K-side vertices → G-side positions (via `lookup-cod`)
  -- for members of K.dom, else a fresh pruned slot.
  remapP : Fin K.nV → Fin (G.nV + count-non K.dom)
  remapP = remap K.dom lookup-cod

  -- Pruned vertex count and labeling.
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
  -- Boundary agreement and the key label lemma for remapP.

  -- Pointwise `K.vlab (K.dom[i]) ≡ G.vlab (lookup-cod i)`, derived from
  -- the runtime boundary equation `bdy-eq : codL G ≡ domL K` (= `map G.vlab G.cod ≡ map K.vlab K.dom`).
  bdy-pt : ∀ i → K.vlab (lookup K.dom i) ≡ G.vlab (lookup-cod i)
  bdy-pt = lookup-boundary K.vlab G.vlab K.dom G.cod (sym bdy-eq)

  -- Label preservation for remapP.
  remapP-vlab : ∀ v → vlab-P (remapP v) ≡ K.vlab v
  remapP-vlab = remap-vlab K.dom lookup-cod K.vlab G.vlab bdy-pt

  -- List-wise label preservation.
  map-via-remapP : (xs : List (Fin K.nV))
                 → map K.vlab xs ≡ map vlab-P (map remapP xs)
  map-via-remapP = map-via-remap K.dom lookup-cod K.vlab G.vlab bdy-pt

  --------------------------------------------------------------------------------
  -- Edge structure of the composite.
  --
  -- Same shape as `FromAPROP.hCompose-impl`: G-edges routed through injL,
  -- K-edges routed through remapP.

  ein-c : Fin (G.nE + K.nE) → List (Fin nV-P)
  ein-c e = [ (λ eG → map injL (G.ein eG))
            , (λ eK → map remapP (K.ein eK))
            ]′ (splitAt G.nE e)

  eout-c : Fin (G.nE + K.nE) → List (Fin nV-P)
  eout-c e = [ (λ eG → map injL (G.eout eG))
             , (λ eK → map remapP (K.eout eK))
             ]′ (splitAt G.nE e)

  elab-c : (e : Fin (G.nE + K.nE))
         → FlatGen (map vlab-P (ein-c e)) (map vlab-P (eout-c e))
  elab-c e with splitAt G.nE e
  ... | inj₁ eG = subst₂ FlatGen
                    (map-via-inj vlab-injL (G.ein eG))
                    (map-via-inj vlab-injL (G.eout eG))
                    (G.elab eG)
  ... | inj₂ eK = subst₂ FlatGen
                    (map-via-remapP (K.ein eK))
                    (map-via-remapP (K.eout eK))
                    (K.elab eK)

  --------------------------------------------------------------------------------
  -- Reduction lemmas (same shape as `FromAPROP.hCompose-impl`).
  -- Callers (e.g. a future `hComposeP-resp-≅ᴴ` in a ported Congruence)
  -- use these to peel the internal `splitAt` in `ein-c`, `eout-c`, `elab-c`
  -- at inject+ / raise inputs.

  ein-c-inj₁-red : ∀ (eG : Fin G.nE)
                 → ein-c (eG ↑ˡ K.nE) ≡ map injL (G.ein eG)
  ein-c-inj₁-red eG with splitAt G.nE (eG ↑ˡ K.nE)
                         | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)      | refl = refl

  eout-c-inj₁-red : ∀ (eG : Fin G.nE)
                  → eout-c (eG ↑ˡ K.nE) ≡ map injL (G.eout eG)
  eout-c-inj₁-red eG with splitAt G.nE (eG ↑ˡ K.nE)
                          | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)       | refl = refl

  ein-c-inj₂-red : ∀ (eK : Fin K.nE)
                 → ein-c (G.nE ↑ʳ eK) ≡ map remapP (K.ein eK)
  ein-c-inj₂-red eK with splitAt G.nE (G.nE ↑ʳ eK)
                         | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)      | refl = refl

  eout-c-inj₂-red : ∀ (eK : Fin K.nE)
                  → eout-c (G.nE ↑ʳ eK) ≡ map remapP (K.eout eK)
  eout-c-inj₂-red eK with splitAt G.nE (G.nE ↑ʳ eK)
                          | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)       | refl = refl

  elab-c-inj₁ : ∀ (eG : Fin G.nE)
              → subst₂ FlatGen
                  (cong (map vlab-P) (ein-c-inj₁-red eG))
                  (cong (map vlab-P) (eout-c-inj₁-red eG))
                  (elab-c (eG ↑ˡ K.nE))
              ≡ subst₂ FlatGen
                  (map-via-inj vlab-injL (G.ein eG))
                  (map-via-inj vlab-injL (G.eout eG))
                  (G.elab eG)
  elab-c-inj₁ eG with splitAt G.nE (eG ↑ˡ K.nE)
                      | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG)   | refl = refl

  elab-c-inj₂ : ∀ (eK : Fin K.nE)
              → subst₂ FlatGen
                  (cong (map vlab-P) (ein-c-inj₂-red eK))
                  (cong (map vlab-P) (eout-c-inj₂-red eK))
                  (elab-c (G.nE ↑ʳ eK))
              ≡ subst₂ FlatGen
                  (map-via-remapP (K.ein eK))
                  (map-via-remapP (K.eout eK))
                  (K.elab eK)
  elab-c-inj₂ eK with splitAt G.nE (G.nE ↑ʳ eK)
                      | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK)   | refl = refl

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
-- hComposeP commutes with `subst₂` on the boundary types: any subst₂
-- transport applied to G's outer-As/middle-Bs and K's middle-Bs/outer-Cs
-- can be factored through a single subst₂ on the resulting composition.
--
-- Proved by refl-refl-refl pattern match on all three equalities.
-- For non-refl inputs the function is opaque, but the equality type is
-- still satisfied — the lemma serves as a type-correct bridge.
--
-- Used by the ρ/α soundness proofs to strip the `++-identityʳ` /
-- `++-assoc` substs out of `⟪ρ⇒⟫ / ⟪ρ⇐⟫ / ⟪α⇒⟫ / ⟪α⇐⟫` and reduce
-- the goal to `subst₂ _ (hComposeP (hId _) (hId _))`, which then
-- chains through `idˡ-sound (id _)` + a subst-elimination step.

-- DE-INDEXED REFACTOR: hComposeP-subst-both used to commute
-- `subst₂ (Hypergraph FlatGen)` past hComposeP.  Under de-indexing,
-- the type doesn't admit such substs at all, so the lemma is gone.

-- Boundary lemmas: `domL` of a pruned composition equals `domL G`,
-- and `codL` equals `codL K` (after applying remap).  These mirror
-- `FromAPROP.domL-hCompose` / `codL-hCompose`.

domL-hComposeP : ∀ G K bdy-eq → domL (hComposeP G K bdy-eq) ≡ domL G
domL-hComposeP G K bdy-eq =
  sym (map-via-inj (hComposeP-impl.vlab-injL G K bdy-eq) _)

codL-hComposeP : ∀ G K bdy-eq → codL (hComposeP G K bdy-eq) ≡ codL K
codL-hComposeP G K bdy-eq = sym (hComposeP-impl.map-via-remapP G K bdy-eq _)
