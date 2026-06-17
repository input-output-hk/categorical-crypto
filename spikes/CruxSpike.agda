{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- MILESTONE-0 CRUX SPIKE for proof-carrying Route A.
-- Scratch module. Does NOT edit Decode.agda. See /tmp/crux-spike/CRUX-NOTES.md.
--------------------------------------------------------------------------------

open import Categories.APROP

module CruxSpike (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range; hGen; hId; hTensor; hSwap; module hTensor-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫)
open import Categories.APROP.Hypergraph.Model.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Soundness.Discharge.LinearHComposeP sig
  using (map-remapP-K-dom)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP sig
  using (⟪⟫-LinearP)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Model.Invariant sig
  using (range-++)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (Agen-edge-aux)
open import Categories.APROP.Hypergraph.Soundness.Base.Permute sig
  using (permute; permute-via-vlab)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-++-≅; unflatten-flatten-≈; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (Agen-edge; edge-step; process-edges; process-all-edges; extract-prefix)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; ∃)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst; subst₂; trans)

--------------------------------------------------------------------------------
-- TARGET 1, atom (B): the underlying generator of a FlatGen, forgetting
-- boundary atom-lists.  subst₂ FlatGen on the boundaries cannot change it.

genOf : ∀ {ins outs} → FlatGen ins outs → Σ[ A ∈ ObjTerm ] Σ[ B ∈ ObjTerm ] mor A B
genOf (FlatGen.flat {A} {B} g) = A , B , g

-- subst₂ on the boundary lists leaves the underlying generator untouched.
genOf-subst₂
  : ∀ {ins outs ins' outs'} (p : ins ≡ ins') (q : outs ≡ outs')
      (fg : FlatGen ins outs)
  → genOf (subst₂ FlatGen p q fg) ≡ genOf fg
genOf-subst₂ refl refl fg = refl

--------------------------------------------------------------------------------
-- The in-order list of underlying generators carried by a hypergraph's edges.
-- This is the boundary-free, vertex-free shadow of `elab`.

Gen* : Set
Gen* = Σ[ A ∈ ObjTerm ] Σ[ B ∈ ObjTerm ] mor A B

genList : (H : Hypergraph FlatGen) → List Gen*
genList H = map (λ e → genOf (Hypergraph.elab H e)) (range (Hypergraph.nE H))

open import Data.Fin using (_↑ˡ_; _↑ʳ_; splitAt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.List.Properties using (map-++; map-∘; map-cong)

--------------------------------------------------------------------------------
-- Pointwise: the underlying generator of a composite edge is the underlying
-- generator of the originating G- (resp. K-) edge.  subst₂ FlatGen on the
-- boundaries is absorbed by `genOf-subst₂`.

module _ (G K : Hypergraph FlatGen) (eq : codL G ≡ domL K) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K eq using (elab-c)

  genOf-elab-c-inj₁ : ∀ (eG : Fin G.nE)
    → genOf (elab-c (eG ↑ˡ K.nE)) ≡ genOf (G.elab eG)
  genOf-elab-c-inj₁ eG with splitAt G.nE (eG ↑ˡ K.nE) | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG) | refl = genOf-subst₂ _ _ (G.elab eG)

  genOf-elab-c-inj₂ : ∀ (eK : Fin K.nE)
    → genOf (elab-c (G.nE ↑ʳ eK)) ≡ genOf (K.elab eK)
  genOf-elab-c-inj₂ eK with splitAt G.nE (G.nE ↑ʳ eK) | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK) | refl = genOf-subst₂ _ _ (K.elab eK)

  -- genList of the pruned composite = genList G ++ genList K (data-flow order).
  genList-hComposeP : genList (hComposeP G K eq) ≡ genList G ++ genList K
  genList-hComposeP =
    trans (cong (map (λ e → genOf (elab-c e))) (range-++ G.nE K.nE))
    (trans (map-++ (λ e → genOf (elab-c e))
                   (map (_↑ˡ K.nE) (range G.nE))
                   (map (G.nE ↑ʳ_) (range K.nE)))
    (cong₂ _++_ partG partK))
    where
      open import Relation.Binary.PropositionalEquality using (cong₂)
      partG : map (λ e → genOf (elab-c e)) (map (_↑ˡ K.nE) (range G.nE))
            ≡ genList G
      partG = trans (sym (map-∘ (range G.nE)))
                    (map-cong genOf-elab-c-inj₁ (range G.nE))
      partK : map (λ e → genOf (elab-c e)) (map (G.nE ↑ʳ_) (range K.nE))
            ≡ genList K
      partK = trans (sym (map-∘ (range K.nE)))
                    (map-cong genOf-elab-c-inj₂ (range K.nE))

--------------------------------------------------------------------------------
-- Same for hTensor (disjoint union).

module _ (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hTensor-impl G K using (elab-c)
  open import Relation.Binary.PropositionalEquality using (cong₂)

  genOf-Telab-c-inj₁ : ∀ (eG : Fin G.nE)
    → genOf (elab-c (eG ↑ˡ K.nE)) ≡ genOf (G.elab eG)
  genOf-Telab-c-inj₁ eG with splitAt G.nE (eG ↑ˡ K.nE) | splitAt-↑ˡ G.nE eG K.nE
  ... | .(inj₁ eG) | refl = genOf-subst₂ _ _ (G.elab eG)

  genOf-Telab-c-inj₂ : ∀ (eK : Fin K.nE)
    → genOf (elab-c (G.nE ↑ʳ eK)) ≡ genOf (K.elab eK)
  genOf-Telab-c-inj₂ eK with splitAt G.nE (G.nE ↑ʳ eK) | splitAt-↑ʳ G.nE K.nE eK
  ... | .(inj₂ eK) | refl = genOf-subst₂ _ _ (K.elab eK)

  genList-hTensor : genList (hTensor G K) ≡ genList G ++ genList K
  genList-hTensor =
    trans (cong (map (λ e → genOf (elab-c e))) (range-++ G.nE K.nE))
    (trans (map-++ (λ e → genOf (elab-c e))
                   (map (_↑ˡ K.nE) (range G.nE))
                   (map (G.nE ↑ʳ_) (range K.nE)))
    (cong₂ _++_
      (trans (sym (map-∘ (range G.nE))) (map-cong genOf-Telab-c-inj₁ (range G.nE)))
      (trans (sym (map-∘ (range K.nE))) (map-cong genOf-Telab-c-inj₂ (range K.nE)))))

--------------------------------------------------------------------------------
-- Atomic leaves.

-- A single generator: genList ⟪ Agen g ⟫ = [ (A , B , g) ].
genList-Agen : ∀ {A B} (g : mor A B) → genList ⟪ Agen g ⟫ ≡ (A , B , g) ∷ []
genList-Agen g = cong (_∷ []) (genOf-subst₂ _ _ (FlatGen.flat g))

-- 0-edge coherence translations contribute nothing.
-- hId unit/Var have nE 0; hId (A⊗B) = hTensor (hId A)(hId B).
genList-hId : ∀ A → genList (hId A) ≡ []
genList-hId unit     = refl
genList-hId (Var x)  = refl
genList-hId (A ⊗₀ B) =
  trans (genList-hTensor (hId A) (hId B))
        (trans (cong (_++ genList (hId B)) (genList-hId A)) (genList-hId B))

genList-id : ∀ {A} → genList ⟪ id {A} ⟫ ≡ []
genList-id {A} = genList-hId A

-- hSwap has 0 edges definitionally.
genList-hSwap : ∀ A B → genList (hSwap A B) ≡ []
genList-hSwap A B = refl

--------------------------------------------------------------------------------
-- MASTER LABEL-PRESERVATION THEOREM (fully general, all HomTerms).
-- termGens t = the in-order list of the leaf generators of t.

termGens : ∀ {A B} → HomTerm A B → List Gen*
termGens (Agen {A} {B} g) = (A , B , g) ∷ []
termGens id               = []
termGens (g ∘ f)          = termGens f ++ termGens g  -- ⟪g∘f⟫ = hComposeP ⟪f⟫ ⟪g⟫
termGens (f ⊗₁ g)         = termGens f ++ termGens g
termGens λ⇒               = []
termGens λ⇐               = []
termGens ρ⇒               = []
termGens ρ⇐               = []
termGens α⇒               = []
termGens α⇐               = []
termGens σ                = []

-- THE THEOREM: the generator labels carried by the translated hypergraph's
-- edges, in edge order, are EXACTLY the term's leaf generators in data-flow
-- order.  No vertices, no boundaries — purely the labels and their order.
genList-⟪⟫ : ∀ {A B} (t : HomTerm A B) → genList ⟪ t ⟫ ≡ termGens t
genList-⟪⟫ (Agen g)  = genList-Agen g
genList-⟪⟫ (id {A})  = genList-hId A
genList-⟪⟫ (g ∘ f)   =
  trans (genList-hComposeP ⟪ f ⟫ ⟪ g ⟫ _)
        (cong₂ _++_ (genList-⟪⟫ f) (genList-⟪⟫ g))
  where open import Relation.Binary.PropositionalEquality using (cong₂)
genList-⟪⟫ (f ⊗₁ g)  =
  trans (genList-hTensor ⟪ f ⟫ ⟪ g ⟫)
        (cong₂ _++_ (genList-⟪⟫ f) (genList-⟪⟫ g))
  where open import Relation.Binary.PropositionalEquality using (cong₂)
genList-⟪⟫ (λ⇒ {A})  = genList-hId A
genList-⟪⟫ (λ⇐ {A})  = genList-hId A
genList-⟪⟫ (ρ⇒ {A})  = genList-hId (A ⊗₀ unit)
genList-⟪⟫ (ρ⇐ {A})  = genList-hId (A ⊗₀ unit)
genList-⟪⟫ (α⇒ {A}{B}{C}) = genList-hId ((A ⊗₀ B) ⊗₀ C)
genList-⟪⟫ (α⇐ {A}{B}{C}) = genList-hId ((A ⊗₀ B) ⊗₀ C)
genList-⟪⟫ (σ {A}{B}) = genList-hSwap A B

--------------------------------------------------------------------------------
-- TARGET 2 PROBE — endpoints.
--
-- Base case sanity: for a single generator, ⟪ Agen g ⟫ = hGen g, whose
-- unique edge (index `zero`) has ein/eout given DEFINITIONALLY by the term's
-- own wiring (the front-loaded range).  So at the LEAF there is a clean,
-- structural endpoint description with φ = identity-on-positions.  This is
-- the trivial base; the difficulty is the inductive remapP/injL cascade
-- through ∘ / ⊗, NOT the leaf.

open import Data.Fin using (_↑ˡ_; _↑ʳ_)

-- The single edge of ⟪ Agen g ⟫ has ein = the front |flatten A| positions.
endpoint-Agen-ein
  : ∀ {A B} (g : mor A B)
  → Hypergraph.ein ⟪ Agen g ⟫ zero
    ≡ map (Data.Fin._↑ˡ length (flatten B)) (range (length (flatten A)))
endpoint-Agen-ein g = refl

endpoint-Agen-eout
  : ∀ {A B} (g : mor A B)
  → Hypergraph.eout ⟪ Agen g ⟫ zero
    ≡ map (length (flatten A) Data.Fin.↑ʳ_) (range (length (flatten B)))
endpoint-Agen-eout g = refl

--------------------------------------------------------------------------------
-- INDUCTIVE STEP PROBE: endpoint of a composite edge = vertex-map of the
-- sub-edge endpoint.  This is the endpoint analogue of genList-hComposeP.
-- The vertex map is injL on the G side and remapP on the K side — the
-- boundary-dependent relay.  If THIS goes through cleanly, the endpoint
-- induction has the same shape as the label induction (good GO signal).

module EndpointStep (G K : Hypergraph FlatGen) (eq : codL G ≡ domL K) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    open hComposeP-impl G K eq using (ein-c; eout-c; injL; remapP)

  -- G-side inner edge: composite ein = map injL of G's ein.  (reuse red lemma)
  comp-ein-G : ∀ (eG : Fin G.nE)
    → Hypergraph.ein (hComposeP G K eq) (eG ↑ˡ K.nE) ≡ map injL (G.ein eG)
  comp-ein-G = hComposeP-impl.ein-c-inj₁-red G K eq

  -- K-side inner edge: composite ein = map remapP of K's ein.
  comp-ein-K : ∀ (eK : Fin K.nE)
    → Hypergraph.ein (hComposeP G K eq) (G.nE ↑ʳ eK) ≡ map remapP (K.ein eK)
  comp-ein-K = hComposeP-impl.ein-c-inj₂-red G K eq

--------------------------------------------------------------------------------
-- LEAF BOUNDARY PLACEMENT PROBE.
-- The decisive single-edge fact, decoupled from the global stack:
-- the unique edge of ⟪ Agen-edge-aux (flat g) ⟫ has its ein on the DOMAIN
-- interface and eout on the CODOMAIN interface of that hypergraph.
--
-- Agen-edge-aux (flat g) = from-iso ∘ Agen g ∘ to-iso, both isos 0-edge.
-- So ⟪ Agen-edge-aux ⟫ = hComposeP (hComposeP ⟪to⟫ (hGen g)) ⟪from⟫.
-- The single edge is the lone edge of (hGen g), routed K-side then K-side.

-- nE of ⟪ t ⟫ equals length (termGens t), via genList-⟪⟫ and
-- length (genList H) = nE H (range has length nE).
open import Data.Nat using (ℕ; zero; suc)

length-range : ∀ n → length (range n) ≡ n
length-range zero    = refl
length-range (suc n) =
  cong suc (trans (Data.List.Properties.length-map suc (range n))
                  (length-range n))

length-genList : (H : Hypergraph FlatGen) → length (genList H) ≡ Hypergraph.nE H
length-genList H =
  trans (Data.List.Properties.length-map _ (range (Hypergraph.nE H)))
        (length-range (Hypergraph.nE H))

nE-⟪⟫ : ∀ {A B} (t : HomTerm A B) → Hypergraph.nE ⟪ t ⟫ ≡ length (termGens t)
nE-⟪⟫ t = trans (sym (length-genList ⟪ t ⟫))
                (cong length (genList-⟪⟫ t))

--------------------------------------------------------------------------------
-- LEAF ENDPOINT = BOUNDARY (decisive, decoupled).
-- For the bare generator hypergraph hGen g = ⟪ Agen g ⟫, the lone edge's
-- ein/eout coincide DEFINITIONALLY with dom/cod.  So "edge sits on the
-- interface" is free at the leaf; the whole content is the cascade transport.

leaf-ein≡dom : ∀ {A B} (g : mor A B)
  → Hypergraph.ein ⟪ Agen g ⟫ zero ≡ Hypergraph.dom ⟪ Agen g ⟫
leaf-ein≡dom g = refl

leaf-eout≡cod : ∀ {A B} (g : mor A B)
  → Hypergraph.eout ⟪ Agen g ⟫ zero ≡ Hypergraph.cod ⟪ Agen g ⟫
leaf-eout≡cod g = refl

--------------------------------------------------------------------------------
-- ONE COMPOSITION LAYER: tensor with id (the `⊗₁ id` of edge-step's `mid`).
-- ⟪ Agen g ⊗₁ id{C} ⟫ = hTensor (hGen g) (hId C).  The lone user edge is the
-- G-side edge (index zero ↑ˡ (hId C).nE).  Probe: its ein equals
-- map injL (front-range), i.e. it still sits on the FRONT block = the
-- domain prefix corresponding to A, with the id-block appended after.

tensor-id-ein
  : ∀ {A B} (g : mor A B) (C : ObjTerm)
  → Hypergraph.ein (hTensor (hGen g) (hId C)) (zero ↑ˡ Hypergraph.nE (hId C))
    ≡ map (hTensor-impl.injL (hGen g) (hId C)) (Hypergraph.ein (hGen g) zero)
tensor-id-ein g C =
  hTensor-impl.ein-c-inj₁-red (hGen g) (hId C) zero

-- ... and that injL-block IS the FRONT of the tensor's dom interface:
-- dom (hTensor G K) = map injL G.dom ++ map injR K.dom, and the edge's ein
-- = map injL (G.ein zero) = map injL G.dom  (since G.ein zero ≡ G.dom for hGen).
-- Hence the edge reads precisely the A-prefix of the composite domain.
tensor-id-ein-is-dom-prefix
  : ∀ {A B} (g : mor A B) (C : ObjTerm)
  → Hypergraph.ein (hTensor (hGen g) (hId C)) (zero ↑ˡ Hypergraph.nE (hId C))
    ≡ map (hTensor-impl.injL (hGen g) (hId C)) (Hypergraph.dom (hGen g))
tensor-id-ein-is-dom-prefix g C =
  trans (tensor-id-ein g C)
        (cong (map (hTensor-impl.injL (hGen g) (hId C))) (leaf-ein≡dom g))

--------------------------------------------------------------------------------
-- SESSION 3 PROBE — the permute-vertex-action lemma (THE WALL).
--
-- `permute p : HomTerm (unflatten xs) (unflatten ys)` is a 0-edge term built
-- from id/⊗/σ/α.  ⟪ permute p ⟫ is a 0-edge cospan hypergraph whose ENTIRE
-- content is a dom↔cod vertex wiring.  THE LEMMA: that wiring realises `p`.
--
-- We probe the structure case-by-case to gauge LOC + find the wall.
--------------------------------------------------------------------------------

-- CASE refl: permute refl = id, so ⟪ permute refl ⟫ = hId (unflatten xs).
-- For hId, dom ≡ cod DEFINITIONALLY (same Fin nV list).  So the vertex action
-- is the identity, matching `refl : xs ↭ xs`.  Probe: dom ≡ cod.
-- First: hId's dom and cod coincide as Fin-nV lists.  NOT definitional — the
-- hTensor recursion builds dom = map injL G.dom ++ map injR K.dom and likewise
-- for cod, so we recurse.
hId-dom≡cod : ∀ A → Hypergraph.dom (hId A) ≡ Hypergraph.cod (hId A)
hId-dom≡cod unit    = refl
hId-dom≡cod (Var x) = refl
hId-dom≡cod (A ⊗₀ B) =
  cong₂ (λ u v → map (hTensor-impl.injL (hId A) (hId B)) u
              ++ map (hTensor-impl.injR (hId A) (hId B)) v)
        (hId-dom≡cod A) (hId-dom≡cod B)
  where open import Relation.Binary.PropositionalEquality using (cong₂)

permute-refl-dom≡cod
  : ∀ {xs : List X}
  → Hypergraph.dom ⟪ permute (Perm.refl {xs = xs}) ⟫
    ≡ Hypergraph.cod ⟪ permute (Perm.refl {xs = xs}) ⟫
permute-refl-dom≡cod {xs} = hId-dom≡cod (unflatten xs)

-- CASE prep: ⟪ permute (prep x p) ⟫ = hTensor (hId (Var x)) ⟪ permute p ⟫.
-- Probe the dom/cod block structure.  dom = map injL [the-one-vertex]
-- ++ map injR (dom ⟪permute p⟫); cod likewise with cod-sub.  The first block
-- (hId (Var x)) is identity; the recursion lives entirely in the injR block.
module _ {x : X} {xs ys : List X} (p : xs Perm.↭ ys) where
  private
    G = hId (Var x)
    K = ⟪ permute p ⟫
    open hTensor-impl G K using (injL; injR)

  prep-dom : Hypergraph.dom ⟪ permute (Perm.prep x p) ⟫
           ≡ map injL (Hypergraph.dom G) ++ map injR (Hypergraph.dom K)
  prep-dom = refl

  prep-cod : Hypergraph.cod ⟪ permute (Perm.prep x p) ⟫
           ≡ map injL (Hypergraph.cod G) ++ map injR (Hypergraph.cod K)
  prep-cod = refl

-- CASE swap: the hard one.  permute (swap x y p) =
--   (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐.
-- Translated: a 4-fold hComposeP nest of hId/hSwap/hTensor.  Each ∘ PRUNES
-- (changes nV).  Probe: can we even state dom/cod cleanly?  domL/codL are known
-- (boundary atom lists) but the Fin-nV-level dom/cod go through remapP cascades.
-- We just check the TOP-LEVEL boundary atom lists first (label level, free):
module _ {x y : X} {xs ys : List X} (p : xs Perm.↭ ys) where
  swap-domL : domL ⟪ permute (Perm.swap x y p) ⟫ ≡ flatten (unflatten (x ∷ y ∷ xs))
  swap-domL = ⟪⟫-domL (permute (Perm.swap x y p))

  swap-codL : codL ⟪ permute (Perm.swap x y p) ⟫ ≡ flatten (unflatten (y ∷ x ∷ ys))
  swap-codL = ⟪⟫-codL (permute (Perm.swap x y p))

-- VERTEX-INDEX PROBE for swap: try to expose the Fin-nV cod as a function of dom.
-- We do NOT yet know the shape; use a hole-free identity check to see whether the
-- cod is even definitionally a remapP of sub-pieces.  Start: is dom≡cod FALSE here
-- (it must be — swap genuinely reorders)?  We assert the NEGATION is not provable
-- by simply trying length/structure.  Instead: probe nV.
module _ {x y : X} {xs ys : List X} (p : xs Perm.↭ ys) where
  swap-nV-probe : Hypergraph.nV ⟪ permute (Perm.swap x y p) ⟫
                ≡ Hypergraph.nV ⟪ permute (Perm.swap x y p) ⟫
  swap-nV-probe = refl

-- CONCRETE smallest swap: x ∷ y ∷ [] ↭ y ∷ x ∷ [] via swap x y refl.
-- Force Agda to print nV by mismatching against 0.
module _ {x y : X} where
  swap2 : (x ∷ y ∷ []) Perm.↭ (y ∷ x ∷ [])
  swap2 = Perm.swap x y Perm.refl

  -- The pruning collapses the 4-layer composition nest's vertex count down to
  -- the 2 boundary atoms (x, y): nV ⟪permute swap2⟫ ≡ 2.  GOOD — confirms no
  -- vertex blow-up.  But dom/cod do NOT reduce to clean Fin-2 lists: they stay
  -- as nested map injL / map remapP cascades (hComposeP dom = map injL G.dom,
  -- cod = map remapP K.cod), so evaluating them needs remap-inj₁/₂ + classify
  -- reductions layer by layer.  THIS is the (bounded) hard part.
  swap2-nV : Hypergraph.nV ⟪ permute swap2 ⟫ ≡ 2
  swap2-nV = refl

--------------------------------------------------------------------------------
-- MILESTONE-1 CHUNK-1: THE PERMUTE-VERTEX-ACTION LEMMA.
--
-- `permVec p` is the POSITIONAL reorder realising `p : xs ↭ ys` on ANY list of
-- the right length (the same shuffle `permute p` performs, read off the ↭
-- derivation).  Defined to MIRROR `permute`'s recursion exactly so the proof is
-- a direct structural correspondence.
--
-- THE LEMMA: cod ⟪permute p⟫ ≡ permVec p (dom ⟪permute p⟫)  — at the VERTEX-INDEX
-- (Fin nV) level, NOT merely the label level.  This pins which interface vertex
-- each codomain position points at, which is exactly what the downstream
-- ψ-ein/ψ-eout (φ vertex correspondence) needs from `permute-via-vlab`.

permVec : ∀ {a} {Z : Set a} {xs ys : List X} → xs Perm.↭ ys → List Z → List Z
permVec Perm.refl         zs            = zs
permVec (Perm.prep x p)   (z ∷ zs)      = z ∷ permVec p zs
permVec (Perm.prep x p)   []            = []                 -- impossible (length)
permVec (Perm.swap x y p) (z ∷ w ∷ zs)  = w ∷ z ∷ permVec p zs
permVec (Perm.swap x y p) (z ∷ [])      = z ∷ []             -- impossible
permVec (Perm.swap x y p) []            = []                 -- impossible
permVec (Perm.trans p q)  zs            = permVec q (permVec p zs)

-- `permVec` is NATURAL in the carrier: it commutes with `map f` (it only ever
-- reorders / shares positions, never inspects elements).
permVec-map
  : ∀ {a b} {Z : Set a} {W : Set b} (f : Z → W) {xs ys : List X}
      (p : xs Perm.↭ ys) (zs : List Z)
  → permVec p (map f zs) ≡ map f (permVec p zs)
permVec-map f Perm.refl         zs            = refl
permVec-map f (Perm.prep x p)   []            = refl
permVec-map f (Perm.prep x p)   (z ∷ zs)      = cong (f z ∷_) (permVec-map f p zs)
permVec-map f (Perm.swap x y p) []            = refl
permVec-map f (Perm.swap x y p) (z ∷ [])      = refl
permVec-map f (Perm.swap x y p) (z ∷ w ∷ zs)  =
  cong (f w ∷_) (cong (f z ∷_) (permVec-map f p zs))
permVec-map f (Perm.trans p q)  zs            =
  trans (cong (permVec q) (permVec-map f p zs)) (permVec-map f q (permVec p zs))

--------------------------------------------------------------------------------
-- The lemma, stated at the vertex-index level.  `vAction p` : the codomain
-- interface of ⟪permute p⟫ is the `permVec p` reorder of its domain interface.

vAction : ∀ {xs ys : List X} (p : xs Perm.↭ ys) → Set
vAction {xs} {ys} p =
  Hypergraph.cod ⟪ permute p ⟫ ≡ permVec p (Hypergraph.dom ⟪ permute p ⟫)

--------------------------------------------------------------------------------
-- GENERIC hComposeP ACTION-COMPOSE.  A polymorphic, map-natural reorder `φ`
-- ("Reorder") abstracts what permVec/hId-shuffle/hSwap-shuffle all are: a
-- function on lists that only rearranges/shares positions.  If G has action
-- φG and K has action φK (cod ≡ φ (dom)), then the pruned composite
-- hComposeP G K eq has action "φG then φK".  This is the trans proof made
-- generic, and it is the single workhorse for BOTH the trans and swap cases.

record Reorder : Set₁ where
  field
    app     : ∀ {Z : Set} → List Z → List Z
    natural : ∀ {Z W : Set} (f : Z → W) (zs : List Z)
            → app (map f zs) ≡ map f (app zs)
open Reorder

-- A hypergraph "realises" reorder φ when its cod is φ of its dom.
HasAction : Hypergraph FlatGen → Reorder → Set
HasAction H φ = Hypergraph.cod H ≡ app φ (Hypergraph.dom H)

-- The composite of two reorders (apply φG first, then φK).
_then_ : Reorder → Reorder → Reorder
(φG then φK) .app zs       = app φK (app φG zs)
(φG then φK) .natural f zs =
  trans (cong (app φK) (natural φG f zs)) (natural φK f (app φG zs))

-- THE GENERIC COMPOSE LEMMA.
hComposeP-HasAction
  : ∀ (G K : Hypergraph FlatGen) (eq : codL G ≡ domL K)
      (lin-G : _) (lin-K : _) {φG φK : Reorder}
  → HasAction G φG → HasAction K φK
  → HasAction (hComposeP G K eq) (φG then φK)
hComposeP-HasAction G K eq lin-G lin-K {φG} {φK} haG haK =
  trans (cong (map remapP) haK)                              -- cod K = φK (dom K)
  (trans (sym (natural φK remapP (Hypergraph.dom K)))        -- pull φK out
  (trans (cong (app φK) crux)                                -- map remapP (dom K) = map injL (cod G)
  (trans (cong (λ w → app φK (map injL w)) haG)              -- cod G = φG (dom G)
         (cong (app φK) (sym (natural φG injL (Hypergraph.dom G)))))))
  where
    open hComposeP-impl G K eq using (injL; remapP)
    crux : map remapP (Hypergraph.dom K) ≡ map injL (Hypergraph.cod G)
    crux = map-remapP-K-dom G K eq lin-G lin-K

-- `permVec p` packaged as a Reorder.
permR : ∀ {xs ys : List X} → xs Perm.↭ ys → Reorder
permR p .app     = permVec p
permR p .natural = λ f zs → permVec-map f p zs

--------------------------------------------------------------------------------
-- Concrete Reorders used by the swap case.

-- identity reorder.
idR : Reorder
idR .app zs       = zs
idR .natural f zs = refl

-- swap the first two positions (identity below length 2).
swap2app : ∀ {Z : Set} → List Z → List Z
swap2app (z ∷ w ∷ rest) = w ∷ z ∷ rest
swap2app zs             = zs

swap2R : Reorder
swap2R .app = swap2app
swap2R .natural f []            = refl
swap2R .natural f (z ∷ [])      = refl
swap2R .natural f (z ∷ w ∷ rest) = refl

-- "keep head, then φ on the tail" reorder (the prep shape, generic).
consR : Reorder → Reorder
consR φ .app []        = []
consR φ .app (z ∷ zs)  = z ∷ app φ zs
consR φ .natural f []        = refl
consR φ .natural f (z ∷ zs)  = cong (f z ∷_) (natural φ f zs)

--------------------------------------------------------------------------------
-- HasAction for the primitive factors of the swap term.

-- hId has the identity action.
hId-HasAction : ∀ A → HasAction (hId A) idR
hId-HasAction A = sym (hId-dom≡cod A)

-- hTensor (hId (Var x)) K, with K realising φ, realises consR φ.
tensor-id-left-HasAction
  : ∀ {x : X} (K : Hypergraph FlatGen) {φ : Reorder}
  → HasAction K φ → HasAction (hTensor (hId (Var x)) K) (consR φ)
tensor-id-left-HasAction {x} K {φ} haK =
  cong (injL zero ∷_)
    (trans (cong (map injR) haK) (sym (natural φ injR (Hypergraph.dom K))))
  where open hTensor-impl (hId (Var x)) K using (injL; injR)

-- hTensor (hSwap (Var x) (Var y)) (hId C) realises swap2R (swap the first two
-- positions).  hSwap(Var x)(Var y) has dom = [a, b], cod = [b, a] (both Fin 2),
-- and tensoring with hId C (cod ≡ dom) just appends a common block; the result's
-- cod is the swap of the result's dom because only the first two (hSwap) slots move.
swap-tensor-id-HasAction
  : ∀ {x y : X} (C : ObjTerm)
  → HasAction (hTensor (hSwap (Var x) (Var y)) (hId C)) swap2R
swap-tensor-id-HasAction {x} {y} C =
  -- cod (hTensor S I) = map injL (cod S) ++ map injR (cod I)
  --                   = (injL b ∷ injL a ∷ []) ++ map injR (cod I)
  --                   = injL b ∷ injL a ∷ map injR (cod I)
  -- dom (hTensor S I) = (injL a ∷ injL b ∷ []) ++ map injR (dom I)
  --                   = injL a ∷ injL b ∷ map injR (dom I)
  -- swap2app dom      = injL b ∷ injL a ∷ map injR (dom I)
  -- and map injR (cod I) ≡ map injR (dom I) since cod I ≡ dom I (hId-dom≡cod).
  cong (λ w → injL b ∷ injL a ∷ map injR w) (sym (hId-dom≡cod C))
  where
    S = hSwap (Var x) (Var y)
    I = hId C
    open hTensor-impl S I using (injL; injR)
    a : Fin (Hypergraph.nV S)
    a = zero
    b : Fin (Hypergraph.nV S)
    b = suc zero

--------------------------------------------------------------------------------
-- CASE refl: ⟪permute refl⟫ = hId (unflatten xs), dom ≡ cod, permVec refl = id.

vAction-refl : ∀ {xs : List X} → vAction (Perm.refl {xs = xs})
vAction-refl {xs} = sym (hId-dom≡cod (unflatten xs))

--------------------------------------------------------------------------------
-- CASE prep: ⟪permute (prep x p)⟫ = hTensor (hId (Var x)) ⟪permute p⟫.
-- hId(Var x) has dom = cod = (zero ∷ []), nV = 1.  So:
--   dom = injL zero ∷ map injR (dom K)
--   cod = injL zero ∷ map injR (cod K)
-- and permVec (prep x p) (injL zero ∷ map injR (dom K))
--   = injL zero ∷ permVec p (map injR (dom K))
--   = injL zero ∷ map injR (permVec p (dom K))     [permVec-map]
--   = injL zero ∷ map injR (cod K)                 [IH: cod K ≡ permVec p (dom K)]
vAction-prep : ∀ {x : X} {xs ys : List X} (p : xs Perm.↭ ys)
             → vAction p → vAction (Perm.prep x p)
vAction-prep {x} p ih =
  cong (injL zero ∷_)
    (trans (cong (map injR) ih) (sym (permVec-map injR p (Hypergraph.dom K))))
  where
    G = hId (Var x)
    K = ⟪ permute p ⟫
    open hTensor-impl G K using (injL; injR)

--------------------------------------------------------------------------------
-- CASE trans: ⟪permute (trans p q)⟫ = hComposeP ⟪permute p⟫ ⟪permute q⟫ eq.
--   dom = map injL (dom P)                        [P = ⟪permute p⟫]
--   cod = map remapP (cod Q)                      [Q = ⟪permute q⟫]
-- Goal:  map remapP (cod Q) ≡ permVec q (permVec p (map injL (dom P)))
-- RHS  = permVec q (permVec p (map injL (dom P)))
--      = permVec q (map injL (permVec p (dom P)))          [permVec-map]
--      = permVec q (map injL (cod P))                      [IH p]
--      = map injL (permVec q (cod P))                      [permVec-map]
-- LHS  = map remapP (cod Q)
--      = map remapP (permVec q (dom Q))                    [IH q]
--      = permVec q (map remapP (dom Q))                    [permVec-map, sym]
--      = permVec q (map injL (cod P))                      [map-remapP-K-dom]
-- The crux remapP fact `map remapP (dom Q) ≡ map injL (cod P)` is exactly
-- `map-remapP-K-dom` (each member of K.dom routes to the matching G.cod via injL),
-- reusing the existing linearity layer (⟪⟫-LinearP supplies Linear P / Linear Q).
-- ⟪permute(trans p q)⟫ = hComposeP ⟪permute p⟫ ⟪permute q⟫ eq, and
-- permVec (trans p q) = (permR p then permR q).app DEFINITIONALLY, so the
-- generic compose lemma discharges trans directly.
vAction-trans
  : ∀ {xs ys zs : List X} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
  → vAction p → vAction q → vAction (Perm.trans p q)
vAction-trans {xs} {ys} {zs} p q ihp ihq =
  hComposeP-HasAction ⟪ permute p ⟫ ⟪ permute q ⟫
    (trans (⟪⟫-codL (permute p)) (sym (⟪⟫-domL (permute q))))
    (⟪⟫-LinearP (permute p)) (⟪⟫-LinearP (permute q))
    {permR p} {permR q} ihp ihq

--------------------------------------------------------------------------------
-- CASE swap: the 4-layer composition nest, dispatched by the generic compose
-- lemma applied to the three primitive HasActions above.
--
-- permute (swap x y p) = t4 ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐  (∘ right-assoc), so
-- ⟪permute (swap x y p)⟫ =
--   hComposeP (hComposeP (hComposeP ⟪α⇐⟫ ⟪σ⊗id⟫) ⟪α⇒⟫) ⟪t4⟫.
-- Layer actions: idR (α⇐), swap2R (σ⊗id), idR (α⇒), consR(consR(permR p)) (t4).
-- Composite app, applied to dom [d0,d1,rest]:
--   idR → [d0,d1,rest] → swap2 → [d1,d0,rest] → idR → [d1,d0,rest]
--   → consR(consR(permR p)) → [d1,d0, permVec p rest]
-- which is exactly permVec (swap x y p) [d0,d1,rest].  We prove that the
-- composite Reorder's app equals permVec (swap x y p) pointwise, then transport
-- the composite HasAction along it.

module _ {x y : X} {xs ys : List X} (p : xs Perm.↭ ys) (ih : vAction p) where
  private
    α⇐T = α⇐ {Var x} {Var y} {unflatten xs}
    σidT = σ {Var x} {Var y} ⊗₁ id {unflatten xs}
    α⇒T = α⇒ {Var y} {Var x} {unflatten xs}
    t4T = id {Var y} ⊗₁ (id {Var x} ⊗₁ permute p)

    -- inner composite α⇐ then σ⊗id
    eq1 : codL ⟪ α⇐T ⟫ ≡ domL ⟪ σidT ⟫
    eq1 = trans (⟪⟫-codL α⇐T) (sym (⟪⟫-domL σidT))
    H1 = hComposeP ⟪ α⇐T ⟫ ⟪ σidT ⟫ eq1
    eq2 : codL H1 ≡ domL ⟪ α⇒T ⟫
    eq2 = trans (⟪⟫-codL (σidT ∘ α⇐T)) (sym (⟪⟫-domL α⇒T))
    H2 = hComposeP H1 ⟪ α⇒T ⟫ eq2
    eq3 : codL H2 ≡ domL ⟪ t4T ⟫
    eq3 = trans (⟪⟫-codL (α⇒T ∘ σidT ∘ α⇐T)) (sym (⟪⟫-domL t4T))

    φ1 = idR
    φ2 = swap2R
    φ3 = idR
    φ4 = consR (consR (permR p))

    ha1 : HasAction ⟪ α⇐T ⟫ φ1
    ha1 = hId-HasAction ((Var x ⊗₀ Var y) ⊗₀ unflatten xs)
    ha2 : HasAction ⟪ σidT ⟫ φ2
    ha2 = swap-tensor-id-HasAction {x} {y} (unflatten xs)
    ha3 : HasAction ⟪ α⇒T ⟫ φ3
    ha3 = hId-HasAction ((Var y ⊗₀ Var x) ⊗₀ unflatten xs)
    ha4 : HasAction ⟪ t4T ⟫ φ4
    ha4 = tensor-id-left-HasAction {y} ⟪ id {Var x} ⊗₁ permute p ⟫
            {consR (permR p)}
            (tensor-id-left-HasAction {x} ⟪ permute p ⟫ {permR p} ih)

    haH1 : HasAction H1 (φ1 then φ2)
    haH1 = hComposeP-HasAction ⟪ α⇐T ⟫ ⟪ σidT ⟫ eq1
             (⟪⟫-LinearP α⇐T) (⟪⟫-LinearP σidT) {φ1} {φ2} ha1 ha2
    haH2 : HasAction H2 ((φ1 then φ2) then φ3)
    haH2 = hComposeP-HasAction H1 ⟪ α⇒T ⟫ eq2
             (⟪⟫-LinearP (σidT ∘ α⇐T)) (⟪⟫-LinearP α⇒T) {φ1 then φ2} {φ3} haH1 ha3
    haTop : HasAction (hComposeP H2 ⟪ t4T ⟫ eq3) (((φ1 then φ2) then φ3) then φ4)
    haTop = hComposeP-HasAction H2 ⟪ t4T ⟫ eq3
              (⟪⟫-LinearP (α⇒T ∘ σidT ∘ α⇐T)) (⟪⟫-LinearP t4T)
              {(φ1 then φ2) then φ3} {φ4} haH2 ha4

    -- The composite reorder's app equals permVec (swap x y p), pointwise.
    composite-app
      : ∀ {Z : Set} (zs : List Z)
      → app (((φ1 then φ2) then φ3) then φ4) zs
        ≡ permVec (Perm.swap x y p) zs
    composite-app []            = refl
    composite-app (z ∷ [])      = refl
    composite-app (z ∷ w ∷ rest) = refl

  vAction-swap : vAction (Perm.swap x y p)
  vAction-swap =
    trans haTop (composite-app (Hypergraph.dom (hComposeP H2 ⟪ t4T ⟫ eq3)))

--------------------------------------------------------------------------------
-- MASTER THEOREM: the permute-vertex-action lemma for ALL Perm constructors.
-- cod ⟪permute p⟫ ≡ permVec p (dom ⟪permute p⟫) — the codomain interface is the
-- `p`-reorder of the domain interface, at the VERTEX-INDEX level.  Zero
-- postulates, --safe --without-K.

permute-vertex-action : ∀ {xs ys : List X} (p : xs Perm.↭ ys) → vAction p
permute-vertex-action {xs} Perm.refl    = vAction-refl {xs}
permute-vertex-action (Perm.prep x p)   =
  vAction-prep {x} p (permute-vertex-action p)
permute-vertex-action (Perm.swap x y p) =
  vAction-swap {x} {y} p (permute-vertex-action p)
permute-vertex-action (Perm.trans p q)  =
  vAction-trans p q (permute-vertex-action p) (permute-vertex-action q)

-- `permute p` is a 0-edge coherence term: it carries NO generators, so
-- `termGens (permute p) ≡ []` (hence `nE ⟪permute p⟫ ≡ 0`).  Induction mirrors
-- `permute`'s recursion (refl=id, prep=id⊗·, swap=4-layer id/σ/α nest, trans=∘).
termGens-permute : ∀ {xs ys : List X} (p : xs Perm.↭ ys) → termGens (permute p) ≡ []
termGens-permute Perm.refl         = refl
termGens-permute (Perm.prep x p)   =
  -- permute (prep x p) = id ⊗₁ permute p ; termGens = [] ++ termGens(permute p)
  termGens-permute p
termGens-permute (Perm.swap x y p) =
  -- (id ⊗₁ (id ⊗₁ permute p)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ : every coherence factor's
  -- termGens is [], and the `[] ++ ·` prefixes collapse DEFINITIONALLY, leaving
  -- termGens (permute p).
  termGens-permute p
termGens-permute (Perm.trans p q)  =
  -- permute (trans p q) = permute q ∘ permute p ; termGens = termGens(permute p)
  -- ++ termGens(permute q) ; both [] by IH, [] ++ [] = [].
  cong₂ _++_ (termGens-permute p) (termGens-permute q)
  where open import Relation.Binary.PropositionalEquality using (cong₂)

nE-permute : ∀ {xs ys : List X} (p : xs Perm.↭ ys) → Hypergraph.nE ⟪ permute p ⟫ ≡ 0
nE-permute p = trans (nE-⟪⟫ (permute p)) (cong length (termGens-permute p))

nE-permute-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X) (p : xs Perm.↭ ys)
  → Hypergraph.nE ⟪ permute-via-vlab vlab p ⟫ ≡ 0
nE-permute-via-vlab vlab p = nE-permute (PermProp.map⁺ vlab p)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- CHUNK 2 (endpoint half): the single-edge endpoint invariant for `edge-step`,
-- lifted to `process-edges`.
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

open import Data.Fin using (_↑ˡ_ ) renaming (_↑ʳ_ to _↑ʳ′_)

--------------------------------------------------------------------------------
-- LAYER 1 — the `permute-via-vlab` vertex action.
--
-- `permute-via-vlab vlab p = permute (map⁺ vlab p)`, so CHUNK-1's
-- `permute-vertex-action` applies verbatim to the mapped ↭.  This states that
-- ⟪permute-via-vlab vlab p⟫'s codomain interface is the `permVec (map⁺ vlab p)`
-- reorder of its domain interface, at the VERTEX-INDEX level.

vAction-via-vlab
  : ∀ {n} {xs ys : List (Fin n)} (vlab : Fin n → X) (p : xs Perm.↭ ys)
  → Hypergraph.cod ⟪ permute-via-vlab vlab p ⟫
    ≡ permVec (PermProp.map⁺ vlab p) (Hypergraph.dom ⟪ permute-via-vlab vlab p ⟫)
vAction-via-vlab vlab p = permute-vertex-action (PermProp.map⁺ vlab p)

--------------------------------------------------------------------------------
-- LAYER 2 — `⟪_⟫`/`genList`/`nE` are stable under the boundary `subst₂ HomTerm`.
--
-- `mid'` in `edge-step` is `subst₂ HomTerm (cong unflatten r) (cong unflatten s)
-- mid`, where `r`,`s` are `sym (map-++ …)` — NOT refl, so neither `⟪mid'⟫` nor
-- `termGens mid'` reduce.  But the boundary transport only changes the term's
-- SOURCE/TARGET object; the underlying term (hence its edge labels and the
-- Fin-nV endpoint indices of its translation) is untouched.  Stated over a
-- universally-quantified pair of object equalities, this is `refl` after
-- matching both to `refl` (path induction): the transport is benign.

⟪⟫-subst₂
  : ∀ {A A' B B'} (eqA : A ≡ A') (eqB : B ≡ B') (t : HomTerm A B)
  → genList ⟪ subst₂ HomTerm eqA eqB t ⟫ ≡ genList ⟪ t ⟫
⟪⟫-subst₂ refl refl t = refl

nE-subst₂
  : ∀ {A A' B B'} (eqA : A ≡ A') (eqB : B ≡ B') (t : HomTerm A B)
  → Hypergraph.nE ⟪ subst₂ HomTerm eqA eqB t ⟫ ≡ Hypergraph.nE ⟪ t ⟫
nE-subst₂ refl refl t = refl

nV-subst₂
  : ∀ {A A' B B'} (eqA : A ≡ A') (eqB : B ≡ B') (t : HomTerm A B)
  → Hypergraph.nV ⟪ subst₂ HomTerm eqA eqB t ⟫ ≡ Hypergraph.nV ⟪ t ⟫
nV-subst₂ refl refl t = refl

--------------------------------------------------------------------------------
-- LAYER 3 — the edge-COUNT of one `edge-step`.
--
-- The count-side of the endpoint invariant: a successful `edge-step` contributes
-- EXACTLY ONE user edge (the lone `Agen-edge e`); a skipped one contributes none.

open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-identityʳ)

-- The `unflatten-++-≅ xs ys` bridge iso is also pure coherence.
termGens-bridge-to : ∀ (xs ys : List X)
  → termGens (_≅_.to (unflatten-++-≅ xs ys)) ≡ []
termGens-bridge-to []       ys = refl
termGens-bridge-to (x ∷ xs) ys = termGens-bridge-to xs ys

termGens-bridge-from : ∀ (xs ys : List X)
  → termGens (_≅_.from (unflatten-++-≅ xs ys)) ≡ []
termGens-bridge-from []       ys = refl
termGens-bridge-from (x ∷ xs) ys =
  cong₂ _++_ (termGens-bridge-from xs ys) refl
  where open import Relation.Binary.PropositionalEquality using (cong₂)

-- The `unflatten-flatten-≈` iso's `to`/`from` are pure monoidal coherence
-- (λ/ρ/α/σ/⊗/∘ only, no `Agen`), so they carry no generators: termGens ≡ [].
-- Proven by induction on the object, letting Agda reduce the library iso
-- combinators (≅.sym/trans, _⊗ᵢ_, unitorˡ/ʳ, associator) through `termGens`.
termGens-iso-to : ∀ A → termGens (_≅_.to (unflatten-flatten-≈ A)) ≡ []
termGens-iso-to unit     = refl
termGens-iso-to (Var x)  = refl
termGens-iso-to (A ⊗₀ B) =
  -- to (uf≈ (A⊗B)) = (to A ⊗₁ to B) ∘ bridge.from
  -- termGens = termGens(bridge.from) ++ (termGens(to A) ++ termGens(to B))
  cong₂ _++_ (termGens-bridge-from (flatten A) (flatten B))
             (cong₂ _++_ (termGens-iso-to A) (termGens-iso-to B))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

termGens-iso-from : ∀ A → termGens (_≅_.from (unflatten-flatten-≈ A)) ≡ []
termGens-iso-from unit     = refl
termGens-iso-from (Var x)  = refl
termGens-iso-from (A ⊗₀ B) =
  -- from (uf≈ (A⊗B)) = bridge.to ∘ (from A ⊗₁ from B)
  -- termGens = (termGens(from A) ++ termGens(from B)) ++ termGens(bridge.to)
  cong₂ _++_ (cong₂ _++_ (termGens-iso-from A) (termGens-iso-from B))
             (termGens-bridge-to (flatten A) (flatten B))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

-- The atom hypergraph of one edge generator has exactly one edge.
nE-Agen-edge-aux : ∀ {ins outs} (fg : FlatGen ins outs)
  → Hypergraph.nE ⟪ Agen-edge-aux fg ⟫ ≡ 1
nE-Agen-edge-aux (FlatGen.flat {A} {B} g) =
  -- Agen-edge-aux (flat g) = from ∘ Agen g ∘ to, both isos coherence ⇒ termGens [].
  -- nE ⟪·⟫ = length (termGens ·) = length (to ++ Agen g ++ from) = length [g] = 1.
  trans (nE-⟪⟫ (_≅_.from (unflatten-flatten-≈ B) ∘ Agen g
                ∘ _≅_.to (unflatten-flatten-≈ A)))
        (cong length
          (cong₂ _++_
            (cong₂ _++_ (termGens-iso-to A) refl)
            (termGens-iso-from B)))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

-- The user-edge count is invisible to the surrounding coherence wiring:
-- ⟪ Agen-edge e ⟫ has nE ≡ 1.
nE-Agen-edge : ∀ (H : Hypergraph FlatGen) (e : Fin (Hypergraph.nE H))
  → Hypergraph.nE ⟪ Agen-edge H e ⟫ ≡ 1
nE-Agen-edge H e = nE-Agen-edge-aux (Hypergraph.elab H e)

-- ... and its LONE edge's label (boundary-free generator) IS `genOf fg`: the
-- coherence iso scaffolding carries no generators, so `genList` is `[genOf fg]`.
genList-Agen-edge-aux : ∀ {ins outs} (fg : FlatGen ins outs)
  → genList ⟪ Agen-edge-aux fg ⟫ ≡ genOf fg ∷ []
genList-Agen-edge-aux (FlatGen.flat {A} {B} g) =
  trans (genList-⟪⟫ (_≅_.from (unflatten-flatten-≈ B) ∘ Agen g
                     ∘ _≅_.to (unflatten-flatten-≈ A)))
        (cong₂ _++_
          (cong₂ _++_ (termGens-iso-to A) refl)
          (termGens-iso-from B))
  where open import Relation.Binary.PropositionalEquality using (cong₂)

-- If `genList H` is the singleton `x ∷ []` then EVERY edge of `H` has label
-- shadow `x` (there is only one edge).  `genList H = map (genOf ∘ elab)
-- (range (nE H))`; a singleton image forces `nE H ≡ 1`, and the lone edge `zero`
-- maps to `x`.
genOf-of-singleton
  : ∀ (H : Hypergraph FlatGen) (x : Gen*)
  → genList H ≡ x ∷ []
  → (e : Fin (Hypergraph.nE H))
  → genOf (Hypergraph.elab H e) ≡ x
genOf-of-singleton H x glist e =
  aux (Hypergraph.nE H) (λ i → genOf (Hypergraph.elab H i)) glist e
  where
    open import Data.List.Properties using (∷-injectiveˡ)
    -- Phrase the per-edge label as a plain family `f : Fin N → Gen*` (= genOf ∘
    -- elab), dodging the dependent FlatGen boundary.  A singleton image `x ∷ []`
    -- of `map f (range N)` forces `N ≡ 1` (so `i ≡ zero`) with `f zero ≡ x`.
    aux : ∀ (N : ℕ) (f : Fin N → Gen*)
        → map f (range N) ≡ x ∷ []
        → (i : Fin N) → f i ≡ x
    aux (suc zero) f g1 zero = ∷-injectiveˡ g1

--------------------------------------------------------------------------------
-- LAYER 4 — the `mid` term's lone-edge ENDPOINT.
--
-- `mid = to(bridge eout rest) ∘ (Agen-edge-aux fg ⊗₁ id) ∘ from(bridge ein rest)`
-- (edge-step:113-115).  ⟪mid⟫ = hComposeP (hComposeP ⟪from⟫ ⟪Agen ⊗ id⟫) ⟪to⟫;
-- both bridges are 0-edge coherence (termGens-bridge-*).  We locate the lone
-- user edge and read off its endpoint as the front |dom-of-Agen| block of the
-- (Agen ⊗ id) factor's domain, threaded through the two K/G-side relays.
--
-- We work over a GENERIC `mid`-shaped term, with arbitrary `fg : FlatGen`,
-- residual list `rest`, to keep it independent of the algorithm's `H`/`e`/stack.

module MidEndpoint {ins outs : List X} (fg : FlatGen ins outs)
                   (rest : List X) where
  private
    toB   = _≅_.to   (unflatten-++-≅ outs rest)
    fromB = _≅_.from (unflatten-++-≅ ins  rest)
    Ag    = Agen-edge-aux fg

  -- The `mid` term (edge-step:111-115, with the residual `rest` explicit).
  midT : HomTerm (unflatten (ins ++ rest)) (unflatten (outs ++ rest))
  midT = toB ∘ (Ag ⊗₁ id {unflatten rest}) ∘ fromB

  -- ⟪midT⟫ has exactly one edge (the lone Agen-edge-aux generator).
  -- termGens midT = (termGens from ++ (termGens Ag ++ termGens id)) ++ termGens to
  -- with the three coherence factors contributing [].
  midT-nE : Hypergraph.nE ⟪ midT ⟫ ≡ 1
  midT-nE = trans (nE-⟪⟫ midT)
    (trans (cong length
      (cong₂ _++_
        (cong₂ _++_ (termGens-bridge-from ins rest)
                    (cong₂ _++_ refl (genList-id→termGens)))
        (termGens-bridge-to outs rest)))
      -- length (([] ++ (termGens Ag ++ [])) ++ []) = length (termGens Ag) = nE ⟪Ag⟫ = 1
      (trans (cong length (++-tidy (termGens Ag)))
             (trans (sym (nE-⟪⟫ Ag)) (nE-Agen-edge-aux fg))))
    where
      open import Relation.Binary.PropositionalEquality using (cong₂)
      open import Data.List.Properties using (++-identityʳ)
      -- termGens (id {unflatten rest}) ≡ [] (coherence)
      genList-id→termGens : termGens (id {unflatten rest}) ≡ []
      genList-id→termGens = refl
      -- (([] ++ (zs ++ [])) ++ []) ≡ zs
      ++-tidy : (zs : List Gen*) → (([] ++ (zs ++ [])) ++ []) ≡ zs
      ++-tidy zs = trans (++-identityʳ (zs ++ [])) (++-identityʳ zs)

--------------------------------------------------------------------------------
-- LAYER 5 — the `bridged`-composition edge relay (K-side).
--
-- `bridged = mid' ∘ permute-via-vlab vlab perm`, so
-- ⟪bridged⟫ = hComposeP ⟪permute-via-vlab vlab perm⟫ ⟪mid'⟫ eqb, and the user
-- edge lives entirely in the K-factor ⟪mid'⟫ (the permute factor is 0-edge).
-- Its endpoint in ⟪bridged⟫ is therefore `map remapP` of its endpoint in ⟪mid'⟫
-- — the standard hComposeP K-side relay (ein-c-inj₂-red).  This is fully general
-- in the permute factor `P`, the mid factor `M`, and the chosen mid-edge `eM`.

module BridgedRelay (P M : Hypergraph FlatGen) (eqb : codL P ≡ domL M) where
  private
    module P = Hypergraph P
    module M = Hypergraph M
    open hComposeP-impl P M eqb using (remapP)

  -- A K-side (mid-factor) edge's ein in the composite is `map remapP` of its
  -- ein in the mid factor.
  bridged-ein-K : ∀ (eM : Fin M.nE)
    → Hypergraph.ein (hComposeP P M eqb) (P.nE ↑ʳ eM) ≡ map remapP (M.ein eM)
  bridged-ein-K = hComposeP-impl.ein-c-inj₂-red P M eqb

  bridged-eout-K : ∀ (eM : Fin M.nE)
    → Hypergraph.eout (hComposeP P M eqb) (P.nE ↑ʳ eM) ≡ map remapP (M.eout eM)
  bridged-eout-K = hComposeP-impl.eout-c-inj₂-red P M eqb

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- CHUNK 3 — SINGLE-EDGE ENDPOINT CLOSED END-TO-END, then lifted across
-- process-edges.
--
-- The chunk-2 relays give every per-layer ein/eout reduction.  The remaining
-- work (this chunk) is to (a) NAME the lone user edge through the layered
-- ↑ˡ/↑ʳ index nesting and (b) COMPOSE the relays into one endpoint statement,
-- then (c) lift across process-edges.
--
-- KEY METHOD that dissolves the feared "index transport" wall: we never need
-- `nE ≡ 1` to NAME the edge.  Each layer of `⟪bridged⟫` is a `hComposeP` or
-- `hTensor`, and the user edge sits on a definite side; its index in that layer
-- is the literal `(inner-index) ↑ˡ _` or `_ ↑ʳ (inner-index)`.  We thread that
-- literal index up and compose the existing red-lemmas with `cong (map _)`.
-- The composite vertex map is a literal nesting of injL/injR/remapP — exactly
-- the φ-cascade the `_≅ᴴ_` endpoint field consumes.
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

open import Data.List.Properties using (map-∘)

--------------------------------------------------------------------------------
-- LAYER A — the leaf `Agen-edge-aux (flat g)` lone-edge endpoint.
--
-- ⟪ Agen-edge-aux (flat g) ⟫ = ⟪ from ∘ Agen g ∘ to ⟫
--   = hComposeP (hComposeP ⟪to⟫ (hGen g) eqI) ⟪from⟫ eqO
-- where ⟪to⟫, ⟪from⟫ are the (0-edge) unflatten-flatten-≈ isos.  The lone edge
-- is the unique edge of `hGen g` (index `zero`), routed K-side through the inner
-- hComposeP, then G-side through the outer hComposeP.  Its endpoint is therefore
-- map injL_outer (map remapP_inner (dom (hGen g))).

module AuxEndpoint {A B : ObjTerm} (g : mor A B) where
  private
    toI   = _≅_.to   (unflatten-flatten-≈ A)
    fromI = _≅_.from (unflatten-flatten-≈ B)
    Hto   = ⟪ toI ⟫
    Hg    = hGen g
    Hfrom = ⟪ fromI ⟫
    eqI : codL Hto ≡ domL Hg
    eqI = trans (⟪⟫-codL toI) (sym (⟪⟫-domL (Agen g)))
    Hin   = hComposeP Hto Hg eqI            -- = ⟪ Agen g ∘ to ⟫
    eqO : codL Hin ≡ domL Hfrom
    eqO = trans (⟪⟫-codL (Agen g ∘ toI)) (sym (⟪⟫-domL fromI))
    -- ⟪ Agen-edge-aux (flat g) ⟫ = hComposeP Hin Hfrom eqO  (definitionally)
    Haux  = hComposeP Hin Hfrom eqO
    open hComposeP-impl Hin Hfrom eqO using () renaming (injL to injL-O)
    open hComposeP-impl Hto Hg eqI   using () renaming (remapP to remapP-I)

    nE-to nE-g : ℕ
    nE-to = Hypergraph.nE Hto
    nE-g  = Hypergraph.nE Hg     -- definitionally 1

  -- The lone-edge index of ⟪ Agen-edge-aux (flat g) ⟫, named explicitly.
  -- Inner: K-side edge of `hGen g` = `nE-to ↑ʳ zero`.
  -- Outer: G-side (the inner composite) = that, `↑ˡ nE Hfrom`.
  auxEdge : Fin (Hypergraph.nE Haux)
  auxEdge = (nE-to ↑ʳ′ zero) ↑ˡ Hypergraph.nE Hfrom

  -- Its ein, as a double-mapped image of `dom (hGen g)`.
  auxφ-ein : List (Fin (Hypergraph.nV Haux))
  auxφ-ein = map injL-O (map remapP-I (Hypergraph.dom Hg))

  aux-ein : Hypergraph.ein ⟪ Agen-edge-aux (FlatGen.flat g) ⟫ auxEdge ≡ auxφ-ein
  aux-ein =
    trans (hComposeP-impl.ein-c-inj₁-red Hin Hfrom eqO (nE-to ↑ʳ′ zero))
          (cong (map injL-O)
            (trans (hComposeP-impl.ein-c-inj₂-red Hto Hg eqI zero)
                   (cong (map remapP-I) (leaf-ein≡dom g))))

  auxφ-eout : List (Fin (Hypergraph.nV Haux))
  auxφ-eout = map injL-O (map remapP-I (Hypergraph.cod Hg))

  aux-eout : Hypergraph.eout ⟪ Agen-edge-aux (FlatGen.flat g) ⟫ auxEdge ≡ auxφ-eout
  aux-eout =
    trans (hComposeP-impl.eout-c-inj₁-red Hin Hfrom eqO (nE-to ↑ʳ′ zero))
          (cong (map injL-O)
            (trans (hComposeP-impl.eout-c-inj₂-red Hto Hg eqI zero)
                   (cong (map remapP-I) (leaf-eout≡cod g))))

--------------------------------------------------------------------------------
-- LAYER B — the `mid` lone-edge endpoint (specialised to `fg = flat g`).
--
-- midT = toB ∘ (Agen-edge-aux (flat g) ⊗₁ id{rest}) ∘ fromB, so
-- ⟪midT⟫ = hComposeP (hComposeP ⟪fromB⟫ ⟪Ag ⊗₁ id⟫ eqM1) ⟪toB⟫ eqM2.
-- The user edge lives in ⟪Ag ⊗₁ id⟫ = hTensor ⟪Ag⟫ ⟪id⟫, on the G-(injL)-side,
-- at index `auxEdge ↑ˡ nE⟪id⟫`.  Routed K-side through the inner hComposeP (with
-- ⟪fromB⟫), then G-side through the outer (with ⟪toB⟫).

module MidEndpointG {A B : ObjTerm} (g : mor A B) (rest : List X) where
  private
    open AuxEndpoint g using (auxEdge; aux-ein; aux-eout)
    fg    = FlatGen.flat g
    ins   = flatten A
    outs  = flatten B
    toB   = _≅_.to   (unflatten-++-≅ outs rest)
    fromB = _≅_.from (unflatten-++-≅ ins  rest)
    Ag    = Agen-edge-aux fg
    AgId  = Ag ⊗₁ id {unflatten rest}
    HAgId = ⟪ AgId ⟫                          -- = hTensor ⟪Ag⟫ ⟪id rest⟫
    Hfb   = ⟪ fromB ⟫
    Htb   = ⟪ toB ⟫
    -- inner hComposeP ⟪fromB⟫ ⟪Ag ⊗₁ id⟫
    eqM1 : codL Hfb ≡ domL HAgId
    eqM1 = trans (⟪⟫-codL fromB) (sym (⟪⟫-domL AgId))
    Hm1  = hComposeP Hfb HAgId eqM1            -- = ⟪ (Ag ⊗₁ id) ∘ fromB ⟫
    eqM2 : codL Hm1 ≡ domL Htb
    eqM2 = trans (⟪⟫-codL (AgId ∘ fromB)) (sym (⟪⟫-domL toB))
    open hComposeP-impl Hm1 Htb eqM2 using () renaming (injL to injL-MO)
    open hComposeP-impl Hfb HAgId eqM1 using () renaming (remapP to remapP-MI)
    open hTensor-impl ⟪ Ag ⟫ ⟪ id {unflatten rest} ⟫ using () renaming (injL to injL-T)

    nE-fb : ℕ
    nE-fb = Hypergraph.nE Hfb
    nE-id : ℕ
    nE-id = Hypergraph.nE ⟪ id {unflatten rest} ⟫

  -- midT (the same term as MidEndpoint.midT, fg = flat g).
  midT : HomTerm (unflatten (ins ++ rest)) (unflatten (outs ++ rest))
  midT = toB ∘ AgId ∘ fromB

  -- The lone-edge index of ⟪midT⟫, named explicitly.
  -- Inner hTensor G-side : `auxEdge ↑ˡ nE-id`.
  -- Inner hComposeP K-side: `nE-fb ↑ʳ (that)`.
  -- Outer hComposeP G-side: `(that) ↑ˡ nE⟪toB⟫`.
  midEdge : Fin (Hypergraph.nE ⟪ midT ⟫)
  midEdge = (nE-fb ↑ʳ′ (auxEdge ↑ˡ nE-id)) ↑ˡ Hypergraph.nE Htb

  midφ-ein : List (Fin (Hypergraph.nV ⟪ midT ⟫))
  midφ-ein = map injL-MO (map remapP-MI
               (map injL-T (AuxEndpoint.auxφ-ein g)))

  mid-ein : Hypergraph.ein ⟪ midT ⟫ midEdge ≡ midφ-ein
  mid-ein =
    trans (hComposeP-impl.ein-c-inj₁-red Hm1 Htb eqM2 (nE-fb ↑ʳ′ (auxEdge ↑ˡ nE-id)))
      (cong (map injL-MO)
        (trans (hComposeP-impl.ein-c-inj₂-red Hfb HAgId eqM1 (auxEdge ↑ˡ nE-id))
          (cong (map remapP-MI)
            (trans (hTensor-impl.ein-c-inj₁-red ⟪ Ag ⟫ ⟪ id {unflatten rest} ⟫ auxEdge)
                   (cong (map injL-T) aux-ein)))))

  midφ-eout : List (Fin (Hypergraph.nV ⟪ midT ⟫))
  midφ-eout = map injL-MO (map remapP-MI
               (map injL-T (AuxEndpoint.auxφ-eout g)))

  mid-eout : Hypergraph.eout ⟪ midT ⟫ midEdge ≡ midφ-eout
  mid-eout =
    trans (hComposeP-impl.eout-c-inj₁-red Hm1 Htb eqM2 (nE-fb ↑ʳ′ (auxEdge ↑ˡ nE-id)))
      (cong (map injL-MO)
        (trans (hComposeP-impl.eout-c-inj₂-red Hfb HAgId eqM1 (auxEdge ↑ˡ nE-id))
          (cong (map remapP-MI)
            (trans (hTensor-impl.eout-c-inj₁-red ⟪ Ag ⟫ ⟪ id {unflatten rest} ⟫ auxEdge)
                   (cong (map injL-T) aux-eout)))))

--------------------------------------------------------------------------------
-- LAYER B′ — the GENERIC-`fg` `mid` endpoint.  Same statement as
-- `MidEndpointG.mid-ein/eout` but quantified over `fg : FlatGen ins outs` with
-- `ins outs` GENERIC VARIABLES, so matching `flat g` unifies `ins := flatten A`
-- against a bound variable (NO green-slime `UnificationStuck`).  `MidEndpoint.midT
-- (flat g) rest` is DEFINITIONALLY `MidEndpointG.midT g rest`, so we just delegate.
-- This is the key wrapper that lets us reach `dom (hGen g)` from `H.elab e`
-- (apply at `fg = H.elab e` — pure application, no matching at the use site).

-- One combined wrapper so the chosen edge `eM` is SHARED by both endpoints.
record MidGen {ins outs} (fg : FlatGen ins outs) (rest : List X) : Set where
  field
    eM     : Fin (Hypergraph.nE ⟪ MidEndpoint.midT fg rest ⟫)
    χ-ein  : List (Fin (Hypergraph.nV ⟪ MidEndpoint.midT fg rest ⟫))
    χ-eout : List (Fin (Hypergraph.nV ⟪ MidEndpoint.midT fg rest ⟫))
    mg-ein  : Hypergraph.ein  ⟪ MidEndpoint.midT fg rest ⟫ eM ≡ χ-ein
    mg-eout : Hypergraph.eout ⟪ MidEndpoint.midT fg rest ⟫ eM ≡ χ-eout

midGen
  : ∀ {ins outs} (fg : FlatGen ins outs) (rest : List X) → MidGen fg rest
midGen (FlatGen.flat g) rest = record
  { eM     = MidEndpointG.midEdge g rest
  ; χ-ein  = MidEndpointG.midφ-ein  g rest
  ; χ-eout = MidEndpointG.midφ-eout g rest
  ; mg-ein  = MidEndpointG.mid-ein  g rest
  ; mg-eout = MidEndpointG.mid-eout g rest
  }

-- The `mid` term's edge-label shadow: `genList ⟪MidEndpoint.midT fg rest⟫`
-- is `genOf fg ∷ []` (the lone Agen-edge-aux generator; bridges/id carry none).
-- Matching `flat g` under generic indices, then `genList-Agen-edge-aux`.
midGen-genList
  : ∀ {ins outs} (fg : FlatGen ins outs) (rest : List X)
  → genList ⟪ MidEndpoint.midT fg rest ⟫ ≡ genOf fg ∷ []
midGen-genList {ins} {outs} (FlatGen.flat g) rest =
  trans (genList-⟪⟫ (MidEndpoint.midT (FlatGen.flat g) rest))
    (cong₂ _++_
      (cong₂ _++_ (termGens-bridge-from ins rest)
                  (cong₂ _++_ termGens-Ag refl))
      (termGens-bridge-to outs rest))
  where
    open import Relation.Binary.PropositionalEquality using (cong₂)
    -- termGens (Agen-edge-aux (flat g)) ≡ genOf (flat g) ∷ [], via genList shadow.
    termGens-Ag : termGens (Agen-edge-aux (FlatGen.flat g)) ≡ genOf (FlatGen.flat g) ∷ []
    termGens-Ag = trans (sym (genList-⟪⟫ (Agen-edge-aux (FlatGen.flat g))))
                        (genList-Agen-edge-aux (FlatGen.flat g))

--------------------------------------------------------------------------------
-- LAYER C₀ — endpoint transport across the boundary `subst₂ HomTerm`.
--
-- `mid'` = `subst₂ HomTerm eqA eqB mid`.  Path-inducting on `eqA`,`eqB` makes
-- `⟪ subst₂ HomTerm eqA eqB t ⟫` reduce DEFINITIONALLY to `⟪ t ⟫`: so its `nE`,
-- and the `ein`/`eout` at any edge index, coincide with those of `⟪ t ⟫`.  The
-- index needs no transport because under refl the two hypergraphs are literally
-- the same term.

ein-subst₂
  : ∀ {A A' B B'} (eqA : A ≡ A') (eqB : B ≡ B') (t : HomTerm A B)
      (e : Fin (Hypergraph.nE ⟪ t ⟫))
  → subst (λ N → List (Fin N)) (nV-subst₂ eqA eqB t)
       (Hypergraph.ein ⟪ subst₂ HomTerm eqA eqB t ⟫
         (subst Fin (sym (nE-subst₂ eqA eqB t)) e))
    ≡ Hypergraph.ein ⟪ t ⟫ e
ein-subst₂ refl refl t e = refl

eout-subst₂
  : ∀ {A A' B B'} (eqA : A ≡ A') (eqB : B ≡ B') (t : HomTerm A B)
      (e : Fin (Hypergraph.nE ⟪ t ⟫))
  → subst (λ N → List (Fin N)) (nV-subst₂ eqA eqB t)
       (Hypergraph.eout ⟪ subst₂ HomTerm eqA eqB t ⟫
         (subst Fin (sym (nE-subst₂ eqA eqB t)) e))
    ≡ Hypergraph.eout ⟪ t ⟫ e
eout-subst₂ refl refl t e = refl

--------------------------------------------------------------------------------
-- LAYER C — the full single-edge `bridged` endpoint, EXACTLY as edge-step
-- builds it (just branch).  We reconstruct edge-step's local definitions over a
-- generic generator `g` (= the underlying mor of `H.elab e`, after matching
-- `flat g`), `vlab`, the vertex lists `einL`/`eoutL`/`rest0`, and the
-- extract-prefix permutation `perm`.
--
--   mid  = MidEndpointG.midT g (map vlab rest0)
--   mid' = subst₂ HomTerm (cong unflatten (sym (map-++ vlab einL  rest0)))
--                          (cong unflatten (sym (map-++ vlab eoutL rest0))) mid
--   bridged = mid' ∘ permute-via-vlab vlab perm
--
-- ⟪bridged⟫ = hComposeP ⟪permute-via-vlab vlab perm⟫ ⟪mid'⟫ eqb.  The user edge
-- is the K-factor (⟪mid'⟫) edge `mid'Edge`; routed K-side through the bridged
-- hComposeP.  Composing the K-side relay + LAYER C₀ + LAYER B closes ONE edge
-- end-to-end, with a literal composite vertex map.

module BridgedEndpoint
  {A B : ObjTerm} (g : mor A B)
  {n : ℕ} (vlab : Fin n → X)
  (einL eoutL rest0 : List (Fin n))
  {s : List (Fin n)} (perm : s Perm.↭ (einL ++ rest0))
  -- The boundaries of `mid` are fixed by `H.elab e = flat g`:
  --   flatten A ≡ map vlab einL ,  flatten B ≡ map vlab eoutL
  (eqAein  : flatten A ≡ map vlab einL)
  (eqBeout : flatten B ≡ map vlab eoutL)
  where
  private
    rest = map vlab rest0
    -- mid (LAYER B's term, with ins = flatten A, outs = flatten B):
    open MidEndpointG g rest using (midT; midEdge; mid-ein; mid-eout;
                                    midφ-ein; midφ-eout)
    -- the subst₂ that turns `mid` into `mid'` (exactly edge-step's):
    eqA : unflatten (flatten A ++ rest)
        ≡ unflatten (map vlab (einL ++ rest0))
    eqA = cong unflatten
            (trans (cong (_++ rest) eqAein) (sym (map-++ vlab einL rest0)))
    eqB : unflatten (flatten B ++ rest)
        ≡ unflatten (map vlab (eoutL ++ rest0))
    eqB = cong unflatten
            (trans (cong (_++ rest) eqBeout) (sym (map-++ vlab eoutL rest0)))

    mid' : HomTerm (unflatten (map vlab (einL ++ rest0)))
                   (unflatten (map vlab (eoutL ++ rest0)))
    mid' = subst₂ HomTerm eqA eqB midT

    P    = ⟪ permute-via-vlab vlab perm ⟫
    M    = ⟪ mid' ⟫
    eqb : codL P ≡ domL M
    eqb = trans (⟪⟫-codL (permute-via-vlab vlab perm)) (sym (⟪⟫-domL mid'))
    open hComposeP-impl P M eqb using () renaming (remapP to remapP-B)

  bridged : HomTerm (unflatten (map vlab s))
                    (unflatten (map vlab (eoutL ++ rest0)))
  bridged = mid' ∘ permute-via-vlab vlab perm

  -- The lone-edge index of ⟪mid'⟫: midEdge transported across the subst₂.
  mid'Edge : Fin (Hypergraph.nE M)
  mid'Edge = subst Fin (sym (nE-subst₂ eqA eqB midT)) midEdge

  -- The lone-edge index of ⟪bridged⟫: K-side of the bridged hComposeP.
  bridgedEdge : Fin (Hypergraph.nE ⟪ bridged ⟫)
  bridgedEdge = Hypergraph.nE P ↑ʳ′ mid'Edge

  -- `midφ-ein` lives in `Fin (nV ⟪midT⟫)`; transport to `Fin (nV M)` so
  -- `remapP-B` (expecting `Fin (nV M)`) can be mapped over it.  Under the
  -- subst₂ this transport is the identity (path induction), but it makes the
  -- types line up.
  private
    toM : List (Fin (Hypergraph.nV ⟪ midT ⟫)) → List (Fin (Hypergraph.nV M))
    toM = subst (λ N → List (Fin N)) (sym (nV-subst₂ eqA eqB midT))

    -- ein/eout of ⟪mid'⟫ at the transported edge equals `toM` of the LAYER-B
    -- endpoint.  Path induction on eqA/eqB collapses both sides.  `t = midT`
    -- is FIXED; we generalise only the subst₂'s TARGET objects + equalities.
    ein-mid' : Hypergraph.ein M mid'Edge ≡ toM midφ-ein
    ein-mid' = aux eqA eqB
      where
        aux : ∀ {A' B'} (eA : unflatten (flatten A ++ rest) ≡ A')
                        (eB : unflatten (flatten B ++ rest) ≡ B')
            → Hypergraph.ein ⟪ subst₂ HomTerm eA eB midT ⟫
                 (subst Fin (sym (nE-subst₂ eA eB midT)) midEdge)
              ≡ subst (λ N → List (Fin N)) (sym (nV-subst₂ eA eB midT)) midφ-ein
        aux refl refl = mid-ein
    eout-mid' : Hypergraph.eout M mid'Edge ≡ toM midφ-eout
    eout-mid' = aux eqA eqB
      where
        aux : ∀ {A' B'} (eA : unflatten (flatten A ++ rest) ≡ A')
                        (eB : unflatten (flatten B ++ rest) ≡ B')
            → Hypergraph.eout ⟪ subst₂ HomTerm eA eB midT ⟫
                 (subst Fin (sym (nE-subst₂ eA eB midT)) midEdge)
              ≡ subst (λ N → List (Fin N)) (sym (nV-subst₂ eA eB midT)) midφ-eout
        aux refl refl = mid-eout

  -- The composite vertex map of the single edge's ein, as a literal nesting.
  bridgedφ-ein : List (Fin (Hypergraph.nV ⟪ bridged ⟫))
  bridgedφ-ein = map remapP-B (toM midφ-ein)

  bridged-ein : Hypergraph.ein ⟪ bridged ⟫ bridgedEdge ≡ bridgedφ-ein
  bridged-ein =
    trans (hComposeP-impl.ein-c-inj₂-red P M eqb mid'Edge)
          (cong (map remapP-B) ein-mid')

  bridgedφ-eout : List (Fin (Hypergraph.nV ⟪ bridged ⟫))
  bridgedφ-eout = map remapP-B (toM midφ-eout)

  bridged-eout : Hypergraph.eout ⟪ bridged ⟫ bridgedEdge ≡ bridgedφ-eout
  bridged-eout =
    trans (hComposeP-impl.eout-c-inj₂-red P M eqb mid'Edge)
          (cong (map remapP-B) eout-mid')

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- LIFT to `process-edges`.
--
-- process-edges H (e ∷ es) s = (s'' , t' ∘ t)  where  t = edge-step H s e,
-- (s'' , t') = process-edges H es s'.  So
--   ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ = ⟪ t' ∘ t ⟫
--     = hComposeP ⟪ t ⟫ ⟪ t' ⟫ eqPE.
-- The HEAD edge-step's edges are the G-side; the TAIL's are the K-side.  So an
-- endpoint of the head edge-step (e.g. the single `bridged` edge proven above)
-- lifts to the whole process-edges term via `map injL` (G-side relay), and a
-- tail edge lifts via `map remapP` (K-side relay).  These are the per-edge
-- liftings; iterating them along the edge list yields the process-edges-level
-- endpoint invariant (each edge's endpoint = its edge-step endpoint pushed
-- through the cascade of injL/remapP for the edges processed after / wrapping it).
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

module ProcessEdgesLift (H : Hypergraph FlatGen) where
  private
    module H = Hypergraph H

  -- abbreviations for the head/tail terms of one process-edges unfolding.
  headTerm : (s : List (Fin H.nV)) (e : Fin H.nE)
           → HomTerm (unflatten (map H.vlab s))
                     (unflatten (map H.vlab (proj₁ (edge-step H s e))))
  headTerm s e = proj₂ (edge-step H s e)

  tailTerm : (es : List (Fin H.nE)) (s' : List (Fin H.nV))
           → HomTerm (unflatten (map H.vlab s'))
                     (unflatten (map H.vlab (proj₁ (process-edges H es s'))))
  tailTerm es s' = proj₂ (process-edges H es s')

  -- The translated process-edges term for a cons is the pruned composite of the
  -- head edge-step and the tail process-edges, DEFINITIONALLY.
  pe-cons-⟪⟫
    : (e : Fin H.nE) (es : List (Fin H.nE)) (s : List (Fin H.nV))
    → let s' = proj₁ (edge-step H s e) in
      ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫
      ≡ hComposeP ⟪ headTerm s e ⟫ ⟪ tailTerm es s' ⟫
          (trans (⟪⟫-codL (headTerm s e)) (sym (⟪⟫-domL (tailTerm es s'))))
  pe-cons-⟪⟫ e es s = refl

  -- HEAD-edge lift: an edge `eH` of the head edge-step's translation appears in
  -- the full process-edges term at `eH ↑ˡ (tail edge count)`, with ein/eout =
  -- `map injL` of its head ein/eout.  (G-side relay.)
  module _ (e : Fin H.nE) (es : List (Fin H.nE)) (s : List (Fin H.nV)) where
    private
      s'  = proj₁ (edge-step H s e)
      Hh  = ⟪ headTerm s e ⟫
      Ht  = ⟪ tailTerm es s' ⟫
      eqPE : codL Hh ≡ domL Ht
      eqPE = trans (⟪⟫-codL (headTerm s e)) (sym (⟪⟫-domL (tailTerm es s')))
      open hComposeP-impl Hh Ht eqPE using () renaming (injL to injL-PE; remapP to remapP-PE)

    head-edge-index : Fin (Hypergraph.nE Hh) → Fin (Hypergraph.nE ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫)
    head-edge-index eH = eH ↑ˡ Hypergraph.nE Ht

    head-ein-lift
      : ∀ (eH : Fin (Hypergraph.nE Hh))
      → Hypergraph.ein ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ (head-edge-index eH)
        ≡ map injL-PE (Hypergraph.ein Hh eH)
    head-ein-lift eH = hComposeP-impl.ein-c-inj₁-red Hh Ht eqPE eH

    head-eout-lift
      : ∀ (eH : Fin (Hypergraph.nE Hh))
      → Hypergraph.eout ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ (head-edge-index eH)
        ≡ map injL-PE (Hypergraph.eout Hh eH)
    head-eout-lift eH = hComposeP-impl.eout-c-inj₁-red Hh Ht eqPE eH

    -- TAIL-edge lift: an edge `eT` of the tail's translation appears at
    -- `(head edge count) ↑ʳ eT`, with ein/eout = `map remapP` of its tail value.
    tail-edge-index : Fin (Hypergraph.nE Ht) → Fin (Hypergraph.nE ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫)
    tail-edge-index eT = Hypergraph.nE Hh ↑ʳ′ eT

    tail-ein-lift
      : ∀ (eT : Fin (Hypergraph.nE Ht))
      → Hypergraph.ein ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ (tail-edge-index eT)
        ≡ map remapP-PE (Hypergraph.ein Ht eT)
    tail-ein-lift eT = hComposeP-impl.ein-c-inj₂-red Hh Ht eqPE eT

    tail-eout-lift
      : ∀ (eT : Fin (Hypergraph.nE Ht))
      → Hypergraph.eout ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ (tail-edge-index eT)
        ≡ map remapP-PE (Hypergraph.eout Ht eT)
    tail-eout-lift eT = hComposeP-impl.eout-c-inj₂-red Hh Ht eqPE eT

    -- LABEL lifts: the boundary-free generator of a head/tail edge is preserved
    -- by the process-edges hComposeP (the `genOf` shadow ignores the injL/remapP
    -- boundary substs — `genOf-elab-c-inj₁/₂`).
    head-lab-lift
      : ∀ (eH : Fin (Hypergraph.nE Hh))
      → genOf (Hypergraph.elab ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ (head-edge-index eH))
        ≡ genOf (Hypergraph.elab Hh eH)
    head-lab-lift eH = genOf-elab-c-inj₁ Hh Ht eqPE eH

    tail-lab-lift
      : ∀ (eT : Fin (Hypergraph.nE Ht))
      → genOf (Hypergraph.elab ⟪ proj₂ (process-edges H (e ∷ es) s) ⟫ (tail-edge-index eT))
        ≡ genOf (Hypergraph.elab Ht eT)
    tail-lab-lift eT = genOf-elab-c-inj₂ Hh Ht eqPE eT

  ------------------------------------------------------------------------------
  -- THE PROCESS-EDGES ENDPOINT INVARIANT (full induction on the edge list).
  --
  -- `EdgeTrace es s` is a structural address into `⟪process-edges es s⟫`'s edge
  -- set together with the SINGLE edge-step that contributes it and the vertex
  -- cascade map relating the two endpoints.  We prove EVERY edge of
  -- `⟪process-edges es s⟫` is reached by exactly such a trace, and that its
  -- ein/eout equal the cascade-image of that edge-step's ein/eout.  This is the
  -- process-edges-level endpoint invariant: endpoint preservation reduces,
  -- edge-by-edge, to the single edge-step endpoint (closed above).

  -- A trace = a point in some edge-step's term, plus the address of the
  -- process-edges edge it becomes, plus the cascade vertex map and the proof.
  record EdgeTrace (es : List (Fin H.nE)) (s : List (Fin H.nV)) : Set where
    field
      peEdge : Fin (Hypergraph.nE ⟪ proj₂ (process-edges H es s) ⟫)
      -- the edge-step (by its stack + edge) and its edge in that step's term
      step-s : List (Fin H.nV)
      step-e : Fin H.nE
      stepEdge : Fin (Hypergraph.nE ⟪ proj₂ (edge-step H step-s step-e) ⟫)
      -- the cascade vertex map and the endpoint agreements
      φ : Fin (Hypergraph.nV ⟪ proj₂ (edge-step H step-s step-e) ⟫)
        → Fin (Hypergraph.nV ⟪ proj₂ (process-edges H es s) ⟫)
      trace-ein
        : Hypergraph.ein ⟪ proj₂ (process-edges H es s) ⟫ peEdge
          ≡ map φ (Hypergraph.ein ⟪ proj₂ (edge-step H step-s step-e) ⟫ stepEdge)
      trace-eout
        : Hypergraph.eout ⟪ proj₂ (process-edges H es s) ⟫ peEdge
          ≡ map φ (Hypergraph.eout ⟪ proj₂ (edge-step H step-s step-e) ⟫ stepEdge)
      -- the LABEL of `peEdge` (its boundary-free generator) is that of the
      -- edge-step's `stepEdge`.
      trace-lab
        : genOf (Hypergraph.elab ⟪ proj₂ (process-edges H es s) ⟫ peEdge)
          ≡ genOf (Hypergraph.elab ⟪ proj₂ (edge-step H step-s step-e) ⟫ stepEdge)
  open EdgeTrace

  -- COMPLETENESS of the trace characterization: every edge of the process-edges
  -- term is reached by a trace.  By induction on the edge list, dispatching on
  -- the head/tail `splitAt` and re-using the per-composition lifts above.
  edge-has-trace
    : ∀ (es : List (Fin H.nE)) (s : List (Fin H.nV))
        (epe : Fin (Hypergraph.nE ⟪ proj₂ (process-edges H es s) ⟫))
    → Σ[ tr ∈ EdgeTrace es s ] peEdge tr ≡ epe
  edge-has-trace [] s epe =
    -- process-edges [] s = (s , id) ; ⟪ id ⟫ has 0 edges (nE-⟪⟫ id ≡ 0), so epe
    -- is an element of `Fin 0` after transport — eliminate.
    ⊥-elim (¬Fin0 (subst Fin (nE-⟪⟫ (id {unflatten (map H.vlab s)})) epe))
    where
      open import Data.Empty using (⊥; ⊥-elim)
      ¬Fin0 : Fin 0 → ⊥
      ¬Fin0 ()
  edge-has-trace (e ∷ es) s epe
    with splitAt (Hypergraph.nE ⟪ headTerm s e ⟫) epe
       in eqsplit
  ... | inj₁ eH =
        -- head edge: trace is the edge-step (s , e) itself at edge eH.
        record
          { peEdge   = head-edge-index e es s eH
          ; step-s   = s
          ; step-e   = e
          ; stepEdge = eH
          ; φ        = injL-PE
          ; trace-ein  = head-ein-lift  e es s eH
          ; trace-eout = head-eout-lift e es s eH
          ; trace-lab  = head-lab-lift  e es s eH
          }
        , Data.Fin.Properties.splitAt⁻¹-↑ˡ eqsplit
    where
      open hComposeP-impl ⟪ headTerm s e ⟫ ⟪ tailTerm es (proj₁ (edge-step H s e)) ⟫
        (trans (⟪⟫-codL (headTerm s e))
               (sym (⟪⟫-domL (tailTerm es (proj₁ (edge-step H s e))))))
        using () renaming (injL to injL-PE)
  ... | inj₂ eT =
        -- tail edge: recurse on `es` at the post-head stack, then relay K-side.
        let s'         = proj₁ (edge-step H s e)
            (trIH , p) = edge-has-trace es s' eT
        in record
             { peEdge   = tail-edge-index e es s (peEdge trIH)
             ; step-s   = step-s trIH
             ; step-e   = step-e trIH
             ; stepEdge = stepEdge trIH
             ; φ        = λ v → remapP-PE (φ trIH v)
             ; trace-ein  =
                 trans (tail-ein-lift e es s (peEdge trIH))
                   (trans (cong (map remapP-PE) (trace-ein trIH))
                          (sym (map-∘ _)))
             ; trace-eout =
                 trans (tail-eout-lift e es s (peEdge trIH))
                   (trans (cong (map remapP-PE) (trace-eout trIH))
                          (sym (map-∘ _)))
             ; trace-lab =
                 trans (tail-lab-lift e es s (peEdge trIH)) (trace-lab trIH)
             }
           , trans (cong (tail-edge-index e es s) p)
                   (Data.Fin.Properties.splitAt⁻¹-↑ʳ eqsplit)
    where
      open hComposeP-impl ⟪ headTerm s e ⟫ ⟪ tailTerm es (proj₁ (edge-step H s e)) ⟫
        (trans (⟪⟫-codL (headTerm s e))
               (sym (⟪⟫-domL (tailTerm es (proj₁ (edge-step H s e))))))
        using () renaming (remapP to remapP-PE)

  ------------------------------------------------------------------------------
  -- The two halves COMPOSE.  On the edge-step SUCCESS branch the edge-step term
  -- is DEFINITIONALLY `bridged = mid' ∘ permute-via-vlab vlab perm` (Decode:
  -- 104,127), i.e. exactly the `BridgedEndpoint.bridged` of CHUNK-3 LAYER C.  We
  -- state the composition over that SAME term `bridged` (the explicit edge-step
  -- output), so no abstraction over `edge-step`'s internal `with` is needed: the
  -- lone user edge sits in the K-factor `⟪mid'⟫` and its `ein`/`eout` are the
  -- literal `map remapP …` composite via the bridged hComposeP K-side relay.
  -- This shows the per-step endpoint `edge-has-trace` reduces to is the
  -- fully-closed CHUNK-3 composite — nothing abstract remains.

  module SuccessStep
    (s : List (Fin H.nV)) (e : Fin H.nE)
    (rest0 : List (Fin H.nV)) (perm : s Perm.↭ (H.ein e ++ rest0))
    where
    private
      open import Data.List.Properties using (map-++)
      ein-l  = map H.vlab (H.ein e)
      eout-l = map H.vlab (H.eout e)
      rest-l = map H.vlab rest0
      -- mid = MidEndpoint.midT (H.elab e) rest-l  (Agen-edge H e = Agen-edge-aux (elab e))
      midT-term : HomTerm (unflatten (ein-l ++ rest-l))
                          (unflatten (eout-l ++ rest-l))
      midT-term = MidEndpoint.midT (H.elab e) rest-l
      eqA0 = cong unflatten (sym (map-++ H.vlab (H.ein  e) rest0))
      eqB0 = cong unflatten (sym (map-++ H.vlab (H.eout e) rest0))
      mid'-term : HomTerm (unflatten (map H.vlab (H.ein e  ++ rest0)))
                          (unflatten (map H.vlab (H.eout e ++ rest0)))
      mid'-term = subst₂ HomTerm eqA0 eqB0 midT-term
      midEdge-term : Fin (Hypergraph.nE ⟪ midT-term ⟫)
      midEdge-term = subst Fin (sym (MidEndpoint.midT-nE (H.elab e) rest-l)) zero
      P  = ⟪ permute-via-vlab H.vlab perm ⟫
      M  = ⟪ mid'-term ⟫
      eqb : codL P ≡ domL M
      eqb = trans (⟪⟫-codL (permute-via-vlab H.vlab perm)) (sym (⟪⟫-domL mid'-term))
      module hc = hComposeP-impl P M eqb
      eM : Fin (Hypergraph.nE M)
      eM = subst Fin (sym (nE-subst₂ eqA0 eqB0 midT-term)) midEdge-term

    -- `bridged` is exactly the edge-step success-branch output term.
    bridged : HomTerm (unflatten (map H.vlab s))
                      (unflatten (map H.vlab (H.eout e ++ rest0)))
    bridged = mid'-term ∘ permute-via-vlab H.vlab perm

    -- the lone user edge index of ⟪bridged⟫ and its endpoint as a literal
    -- `map remapP` composite (the bridged hComposeP K-side relay).
    bridgedEdge : Fin (Hypergraph.nE ⟪ bridged ⟫)
    bridgedEdge = Hypergraph.nE P ↑ʳ′ eM

    bridged-ein : Hypergraph.ein ⟪ bridged ⟫ bridgedEdge
                ≡ map hc.remapP (Hypergraph.ein M eM)
    bridged-ein = hc.ein-c-inj₂-red eM

    bridged-eout : Hypergraph.eout ⟪ bridged ⟫ bridgedEdge
                 ≡ map hc.remapP (Hypergraph.eout M eM)
    bridged-eout = hc.eout-c-inj₂-red eM

  ------------------------------------------------------------------------------
  -- ISLAND CONNECTION (CLOSEOUT).  Wire the CHUNK-3 lone-edge endpoint (which
  -- bottoms out, through `midGen`, at `dom`/`cod (hGen g)` — the EXPLICIT
  -- `H.ein e`/`H.eout e` interface) to the EdgeTrace's `stepEdge` endpoint over
  -- `⟪ proj₂ (edge-step H step-s step-e) ⟫`.
  --
  -- The trick the prior sessions could not do directly (ill-typed `with`-
  -- abstraction over `edge-step`'s internal `with`, plus green-slime when
  -- matching `flat g` against the stuck index `FlatGen (map vlab (ein e)) …`):
  --   (a) the `flat g` match is pushed INSIDE the GENERIC-index wrapper `midGen`
  --       (`∀ {ins outs} (fg : FlatGen ins outs)` — `ins` is a bound variable, so
  --       `ins := flatten A` unifies cleanly, no UnificationStuck);
  --   (b) at the use site we only APPLY `midGen (H.elab e) …` (no matching), and
  --       `with extract-prefix (H.ein e) s` re-exposes the success branch so
  --       `proj₂ (edge-step H s e)` REDUCES to `Build.bridged-term`
  --       DEFINITIONALLY (`MidEndpoint.midT (H.elab e) (map vlab rest)` IS
  --       Decode's `mid`).  No abstraction over `edge-step`'s internal `with`.

  module EdgeStepSuccess (s : List (Fin H.nV)) (e : Fin H.nE) where
    open import Data.Empty using (⊥; ⊥-elim)

    -- We dispatch `with extract-prefix (H.ein e) s` (re-exposing the success
    -- branch so `edge-step` REDUCES to `bridged`).  On the `nothing` branch
    -- `nE ⟪edge-step⟫ ≡ 0`, so `se : Fin 0` is absurd.
    -- The reusable success-branch endpoint builder.  Given the exposed
    -- `extract-prefix` result `(rest , perm)`, `proj₂ (edge-step H s e)` REDUCES
    -- to Decode's `bridged = mid' ∘ permute-via-vlab vlab perm`, where
    --   mid' = subst₂ HomTerm eqA0 eqB0 (MidEndpoint.midT (H.elab e) (map vlab rest))
    -- (`MidEndpoint.midT (H.elab e) …` IS Decode's `mid`, definitionally).
    -- We build the lone-edge endpoint by: (the generic `midGen` mid endpoint at
    -- `fg = H.elab e`)  →  transport across the `subst₂` (`ein-subst₂`)  →  the
    -- bridged hComposeP K-side relay (`ein-c-inj₂-red`).  This reaches
    -- `dom`/`cod (hGen g)` = the EXPLICIT `H.ein e`/`H.eout e` interface — the
    -- island connection, done DEFINITIONALLY at the use site (no `flat`-match
    -- here; the match lives inside `midGen`, under generic indices).
    private
      module Build (rest : List (Fin H.nV)) (perm : s Perm.↭ (H.ein e ++ rest)) where
        open import Data.List.Properties using (map-++)
        rest-l = map H.vlab rest
        midT-term = MidEndpoint.midT (H.elab e) rest-l
        eqA0 = cong unflatten (sym (map-++ H.vlab (H.ein  e) rest))
        eqB0 = cong unflatten (sym (map-++ H.vlab (H.eout e) rest))
        mid'-term = subst₂ HomTerm eqA0 eqB0 midT-term
        P  = ⟪ permute-via-vlab H.vlab perm ⟫
        M  = ⟪ mid'-term ⟫
        eqb : codL P ≡ domL M
        eqb = trans (⟪⟫-codL (permute-via-vlab H.vlab perm)) (sym (⟪⟫-domL mid'-term))
        module hc = hComposeP-impl P M eqb
        -- `bridged` IS `proj₂ (edge-step H s e)` on the success branch
        -- (definitionally — see Decode.agda:104,127).
        bridged-term : HomTerm (unflatten (map H.vlab s))
                               (unflatten (map H.vlab (H.eout e ++ rest)))
        bridged-term = mid'-term ∘ permute-via-vlab H.vlab perm

        mg = midGen (H.elab e) rest-l
        -- the lone-edge index of ⟪mid'⟫: `midGen`'s edge, transported across subst₂.
        eM : Fin (Hypergraph.nE M)
        eM = subst Fin (sym (nE-subst₂ eqA0 eqB0 midT-term)) (MidGen.eM mg)
        bridgedEdge : Fin (Hypergraph.nE ⟪ bridged-term ⟫)
        bridgedEdge = Hypergraph.nE P ↑ʳ′ eM

        -- ein of ⟪mid'⟫ at `eM`: transport the `midGen` ein across the subst₂.
        ein-mid' : Hypergraph.ein M eM
                 ≡ subst (λ N → List (Fin N)) (sym (nV-subst₂ eqA0 eqB0 midT-term))
                     (MidGen.χ-ein mg)
        ein-mid' = auxE eqA0 eqB0
          where
            auxE : ∀ {A' B'} (eA : unflatten (map H.vlab (H.ein e) ++ rest-l) ≡ A')
                             (eB : unflatten (map H.vlab (H.eout e) ++ rest-l) ≡ B')
                 → Hypergraph.ein ⟪ subst₂ HomTerm eA eB midT-term ⟫
                      (subst Fin (sym (nE-subst₂ eA eB midT-term)) (MidGen.eM mg))
                   ≡ subst (λ N → List (Fin N)) (sym (nV-subst₂ eA eB midT-term))
                       (MidGen.χ-ein mg)
            auxE refl refl = MidGen.mg-ein mg

        eout-mid' : Hypergraph.eout M eM
                  ≡ subst (λ N → List (Fin N)) (sym (nV-subst₂ eqA0 eqB0 midT-term))
                      (MidGen.χ-eout mg)
        eout-mid' = auxO eqA0 eqB0
          where
            auxO : ∀ {A' B'} (eA : unflatten (map H.vlab (H.ein e) ++ rest-l) ≡ A')
                             (eB : unflatten (map H.vlab (H.eout e) ++ rest-l) ≡ B')
                 → Hypergraph.eout ⟪ subst₂ HomTerm eA eB midT-term ⟫
                      (subst Fin (sym (nE-subst₂ eA eB midT-term)) (MidGen.eM mg))
                   ≡ subst (λ N → List (Fin N)) (sym (nV-subst₂ eA eB midT-term))
                       (MidGen.χ-eout mg)
            auxO refl refl = MidGen.mg-eout mg

        bridged-ein : Hypergraph.ein ⟪ bridged-term ⟫ bridgedEdge
                    ≡ map hc.remapP (Hypergraph.ein M eM)
        bridged-ein = hc.ein-c-inj₂-red eM

        bridged-eout : Hypergraph.eout ⟪ bridged-term ⟫ bridgedEdge
                     ≡ map hc.remapP (Hypergraph.eout M eM)
        bridged-eout = hc.eout-c-inj₂-red eM

        -- ⟪bridged-term⟫ has exactly ONE edge, so any edge IS `bridgedEdge`.
        -- nE ⟪bridged⟫ = nE P + nE M DEFINITIONALLY (hComposeP), with nE P ≡ 0
        -- (P is the 0-edge permute coherence) and nE M ≡ 1 (lone mid edge through
        -- `nE-subst₂` + `midT-nE`).
        bridged-nE : Hypergraph.nE ⟪ bridged-term ⟫ ≡ 1
        bridged-nE = cong₂ Data.Nat._+_ nE-P≡0 nE-M≡1
          where
            open import Relation.Binary.PropositionalEquality using (cong₂)
            nE-P≡0 : Hypergraph.nE P ≡ 0
            nE-P≡0 = nE-permute-via-vlab H.vlab perm
            nE-M≡1 : Hypergraph.nE M ≡ 1
            nE-M≡1 = trans (nE-subst₂ eqA0 eqB0 midT-term) (MidEndpoint.midT-nE (H.elab e) rest-l)

        -- the LABEL shadow of ⟪bridged⟫: a singleton `genOf (H.elab e) ∷ []`.
        -- genList ⟪bridged⟫ = genList P ++ genList M ; genList P = [] (permute
        -- coherence), genList M = genList ⟪midT⟫ (subst₂-invariant) = genOf(elab e)∷[].
        bridged-genList : genList ⟪ bridged-term ⟫ ≡ genOf (H.elab e) ∷ []
        bridged-genList =
          trans (genList-hComposeP P M eqb)
          (trans (cong (_++ genList M) genList-P≡[])
                 genList-M)
          where
            genList-P≡[] : genList P ≡ []
            genList-P≡[] = trans (genList-⟪⟫ (permute-via-vlab H.vlab perm))
                                 (termGens-permute (PermProp.map⁺ H.vlab perm))
            genList-M : genList M ≡ genOf (H.elab e) ∷ []
            genList-M = trans (⟪⟫-subst₂ eqA0 eqB0 midT-term)
                              (midGen-genList (H.elab e) rest-l)

        bridged-lab : genOf (Hypergraph.elab ⟪ bridged-term ⟫ bridgedEdge)
                    ≡ genOf (H.elab e)
        bridged-lab = genOf-of-singleton ⟪ bridged-term ⟫ (genOf (H.elab e))
                        bridged-genList bridgedEdge

        -- any edge of the 1-edge ⟪bridged⟫ IS `bridgedEdge`: transport both to
        -- `Fin 1` (contractible), use irrelevance, transport back.
        se≡edge : (se : Fin (Hypergraph.nE ⟪ bridged-term ⟫)) → se ≡ bridgedEdge
        se≡edge se =
          trans (sym (subst-sym-subst bridged-nE {p = se}))
          (trans (cong (subst Fin (sym bridged-nE))
                       (fin1-irrelevant (subst Fin bridged-nE se)
                                        (subst Fin bridged-nE bridgedEdge)))
                 (subst-sym-subst bridged-nE {p = bridgedEdge}))
          where
            open import Relation.Binary.PropositionalEquality using (subst-sym-subst)
            fin1-irrelevant : (i j : Fin 1) → i ≡ j
            fin1-irrelevant zero zero = refl

    -- THE ISLAND CONNECTION.  For ANY edge `se` of ⟪ proj₂ (edge-step H s e) ⟫,
    -- produce a vertex-map cascade `χ` and the proof that the endpoint is `χ`.
    -- On the success branch `χ` is the `Build` composite, bottoming out (through
    -- `midGen`) at `dom`/`cod (hGen g)` = the EXPLICIT `H.ein e`/`H.eout e`
    -- interface.  On the `nothing` branch `nE ⟪edge-step⟫ ≡ 0` so `se` is absurd.
    connect-ein
      : (se : Fin (Hypergraph.nE ⟪ proj₂ (edge-step H s e) ⟫))
      → Σ[ χ ∈ List (Fin (Hypergraph.nV ⟪ proj₂ (edge-step H s e) ⟫)) ]
          Hypergraph.ein ⟪ proj₂ (edge-step H s e) ⟫ se ≡ χ
    connect-ein se with extract-prefix (H.ein e) s
    ... | nothing            =
          ⊥-elim (¬Fin0 (subst Fin (nE-⟪⟫ (id {unflatten (map H.vlab s)})) se))
      where ¬Fin0 : Fin 0 → ⊥
            ¬Fin0 ()
    ... | just (rest , perm) =
          map (Build.hc.remapP rest perm) (Hypergraph.ein (Build.M rest perm) (Build.eM rest perm))
          , trans (cong (Hypergraph.ein ⟪ Build.bridged-term rest perm ⟫) (Build.se≡edge rest perm se))
                  (Build.bridged-ein rest perm)

    connect-eout
      : (se : Fin (Hypergraph.nE ⟪ proj₂ (edge-step H s e) ⟫))
      → Σ[ χ ∈ List (Fin (Hypergraph.nV ⟪ proj₂ (edge-step H s e) ⟫)) ]
          Hypergraph.eout ⟪ proj₂ (edge-step H s e) ⟫ se ≡ χ
    connect-eout se with extract-prefix (H.ein e) s
    ... | nothing            =
          ⊥-elim (¬Fin0 (subst Fin (nE-⟪⟫ (id {unflatten (map H.vlab s)})) se))
      where ¬Fin0 : Fin 0 → ⊥
            ¬Fin0 ()
    ... | just (rest , perm) =
          map (Build.hc.remapP rest perm) (Hypergraph.eout (Build.M rest perm) (Build.eM rest perm))
          , trans (cong (Hypergraph.eout ⟪ Build.bridged-term rest perm ⟫) (Build.se≡edge rest perm se))
                  (Build.bridged-eout rest perm)

    -- THE LABEL half of the island connection: the boundary-free generator of
    -- ANY edge `se` of ⟪edge-step⟫ is `genOf (H.elab e)`.  On success this is
    -- `genOf-of-singleton` over the 1-edge ⟪bridged⟫; on failure `se` is absurd.
    connect-lab
      : (se : Fin (Hypergraph.nE ⟪ proj₂ (edge-step H s e) ⟫))
      → genOf (Hypergraph.elab ⟪ proj₂ (edge-step H s e) ⟫ se) ≡ genOf (H.elab e)
    connect-lab se with extract-prefix (H.ein e) s
    ... | nothing            =
          ⊥-elim (¬Fin0 (subst Fin (nE-⟪⟫ (id {unflatten (map H.vlab s)})) se))
      where ¬Fin0 : Fin 0 → ⊥
            ¬Fin0 ()
    ... | just (rest , perm) =
          genOf-of-singleton ⟪ Build.bridged-term rest perm ⟫ (genOf (H.elab e))
            (Build.bridged-genList rest perm) se

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  -- THE CAPSTONE — `decode-preserves-edges` (milestone-1 deliverable).
  --
  -- Both islands are now wired.  For EVERY edge `epe` of the decoded
  -- hypergraph `⟪ proj₂ (process-edges es s) ⟫`, we produce:
  --   * the ORIGINATING original edge `src-e : Fin H.nE` (= the edge-step that
  --     contributed it, from `edge-has-trace`),
  --   * a single vertex map `Φ : Fin H.nV-of-the-step → decode.nV`,
  --   * explicit endpoint lists `ψ-ein`/`ψ-eout` for `epe`, and
  --   * the EDGE-LABEL of `epe` = `genOf (H.elab src-e)` (`genList-⟪⟫` shadow),
  -- with the endpoint witnesses
  --     ein ⟪decode⟫ epe ≡ map Φ ψ-ein-step ,  eout ⟪decode⟫ epe ≡ map Φ ψ-eout-step
  -- where `ψ-ein-step`/`ψ-eout-step` are the lone-edge endpoints of `src-e`'s
  -- edge-step, which (on the success branch, via `EdgeStepSuccess.connect-*`)
  -- ARE the literal vertex-map cascade of `dom`/`cod (hGen g)` — i.e. of the
  -- EXPLICIT `H.ein src-e`/`H.eout src-e` interface.
  --
  -- This is exactly the per-edge data that milestone-5's `_≅ᴴ_` assembly
  -- consumes for its `ψ-ein`/`ψ-eout` (endpoints, here as `map Φ` composites)
  -- and `φ-lab` (labels) fields, with `G = H`, `K = ⟪decode⟫`, `ψ src-e = epe`.

  record EdgePreservation (es : List (Fin H.nE)) (s : List (Fin H.nV)) : Set where
    field
      -- the decode edge addressed and the original edge it comes from
      decEdge : Fin (Hypergraph.nE ⟪ proj₂ (process-edges H es s) ⟫)
      src-s   : List (Fin H.nV)
      src-e   : Fin H.nE
      -- vertex correspondence cascade (edge-step vertices → decode vertices)
      Φ : Fin (Hypergraph.nV ⟪ proj₂ (edge-step H src-s src-e) ⟫)
        → Fin (Hypergraph.nV ⟪ proj₂ (process-edges H es s) ⟫)
      -- the endpoint of `src-e`'s edge-step's lone user edge, as a vertex-map
      -- cascade of `dom`/`cod (hGen (H.elab src-e))` (the explicit interface).
      stepEdge : Fin (Hypergraph.nE ⟪ proj₂ (edge-step H src-s src-e) ⟫)
      χ-ein  : List (Fin (Hypergraph.nV ⟪ proj₂ (edge-step H src-s src-e) ⟫))
      χ-eout : List (Fin (Hypergraph.nV ⟪ proj₂ (edge-step H src-s src-e) ⟫))
      step-ein  : Hypergraph.ein  ⟪ proj₂ (edge-step H src-s src-e) ⟫ stepEdge ≡ χ-ein
      step-eout : Hypergraph.eout ⟪ proj₂ (edge-step H src-s src-e) ⟫ stepEdge ≡ χ-eout
      -- the decode edge's endpoints = `map Φ` of the edge-step endpoints.
      ψ-ein  : Hypergraph.ein  ⟪ proj₂ (process-edges H es s) ⟫ decEdge ≡ map Φ χ-ein
      ψ-eout : Hypergraph.eout ⟪ proj₂ (process-edges H es s) ⟫ decEdge ≡ map Φ χ-eout
      -- the decode edge's LABEL (boundary-free generator) = `genOf (H.elab src-e)`.
      φ-lab  : genOf (Hypergraph.elab ⟪ proj₂ (process-edges H es s) ⟫ decEdge)
             ≡ genOf (H.elab src-e)

  -- THE THEOREM: every decode edge enjoys an EdgePreservation, AND it addresses
  -- the requested edge `epe`.  Combines `edge-has-trace` (process-edges trace +
  -- cascade Φ) with `EdgeStepSuccess.connect-ein/eout` (the wired island: the
  -- per-step endpoint reaching the explicit `H.ein/eout` interface).
  decode-preserves-edges
    : ∀ (es : List (Fin H.nE)) (s : List (Fin H.nV))
        (epe : Fin (Hypergraph.nE ⟪ proj₂ (process-edges H es s) ⟫))
    → Σ[ ep ∈ EdgePreservation es s ] EdgePreservation.decEdge ep ≡ epe
  decode-preserves-edges es s epe =
    let (tr , p)        = edge-has-trace es s epe
        (χe , se-ein)   = EdgeStepSuccess.connect-ein  (EdgeTrace.step-s tr) (EdgeTrace.step-e tr) (EdgeTrace.stepEdge tr)
        (χo , se-eout)  = EdgeStepSuccess.connect-eout (EdgeTrace.step-s tr) (EdgeTrace.step-e tr) (EdgeTrace.stepEdge tr)
    in record
         { decEdge   = EdgeTrace.peEdge tr
         ; src-s     = EdgeTrace.step-s tr
         ; src-e     = EdgeTrace.step-e tr
         ; Φ         = EdgeTrace.φ tr
         ; stepEdge  = EdgeTrace.stepEdge tr
         ; χ-ein     = χe
         ; χ-eout    = χo
         ; step-ein  = se-ein
         ; step-eout = se-eout
         ; ψ-ein     = trans (EdgeTrace.trace-ein  tr) (cong (map (EdgeTrace.φ tr)) se-ein)
         ; ψ-eout    = trans (EdgeTrace.trace-eout tr) (cong (map (EdgeTrace.φ tr)) se-eout)
         ; φ-lab     = trans (EdgeTrace.trace-lab tr)
                             (EdgeStepSuccess.connect-lab (EdgeTrace.step-s tr) (EdgeTrace.step-e tr) (EdgeTrace.stepEdge tr))
         } , p

  -- Specialised to the ACTUAL decode (`process-all-edges H.dom`, ranging over
  -- ALL `H.nE` edges from the domain stack): every edge of the decoded
  -- hypergraph is endpoint-and-label preserved.
  decode-preserves-edges-all
    : ∀ (epe : Fin (Hypergraph.nE ⟪ proj₂ (process-all-edges H H.dom) ⟫))
    → Σ[ ep ∈ EdgePreservation (range H.nE) H.dom ] EdgePreservation.decEdge ep ≡ epe
  decode-preserves-edges-all epe = decode-preserves-edges (range H.nE) H.dom epe

