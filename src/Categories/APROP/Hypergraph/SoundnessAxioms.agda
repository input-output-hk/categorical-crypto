{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Per-axiom soundness proofs. Extracted from the Soundness catch-all
-- postulate as each axiom is discharged.
--
-- With the switch to hComposeP (pruned cospan composition), axioms where
-- LHS had strictly more vertices than RHS under the unpruned version now
-- have matching vertex counts (modulo +-identityʳ casts) and are
-- constructively provable.
--
-- Currently proved: ∅ (this file is a placeholder for now).
--
-- Strategy per axiom:
--   1. Identify LHS and RHS of the `⟪_⟫` translation.
--   2. Use `hId-count-non-dom ≡ 0` (or `⟪_⟫-dom-unique` for the count-non
--      of general ⟪f⟫.dom) to show the vertex counts match.
--   3. Construct the ≅ᴴ record field-by-field:
--      φ/φ⁻¹ via splitAt + case on the trivially-empty side.
--      ψ/ψ⁻¹ similarly (hId has no edges).
--      Labels, endpoints, elab: chase through the subst₂ + map-via-remapP
--      machinery.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SoundnessAxioms (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hGen; hEmpty; hVar; hSwap; range; module hTensor-impl)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig
open import Categories.APROP.Hypergraph.Invariant sig

open import Categories.APROP.Hypergraph.Prune
  using ( nonMem; count-non; AllIn; AllIn→count-non-zero
        ; classify; classify-lookup-Unique; remap; remap-inj₁)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; splitAt; cast)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ; cast-is-id)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup; tabulate; allFin)
open import Data.List.Properties
  using (map-∘; map-cong; map-id; tabulate-lookup; map-tabulate)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using ([_,_]′; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂; module ≡-Reasoning)

--------------------------------------------------------------------------------
-- `idˡ`: `id ∘ f ≈Term f`.
--
-- Translation:
--   ⟪ id ∘ f ⟫ = hComposeP ⟪f⟫ (hId B)
-- where B is the codomain of f.
--
-- Key facts used:
--   * `hId B` has no edges (hId-nE ≡ 0 by induction on B).
--   * `hId B`.dom covers all vertices (hId-dom-covers).
--   * Therefore `count-non (hId B).dom ≡ 0` (hId-count-non-dom).
--
-- Consequence: the composite's vertex count is `⟪f⟫.nV + 0` and the
-- edge count is `⟪f⟫.nE + 0`. The iso with `⟪f⟫` is essentially
-- identity on the G-side with trivial coverage of the empty K-side.

-- First, a helper fact: hId has no edges.
hId-nE : ∀ A → Hypergraph.nE (hId A) ≡ 0
hId-nE unit       = refl
hId-nE (Var x)    = refl
hId-nE (A ⊗₀ B)   = cong₂-+ (hId-nE A) (hId-nE B)
  where
    cong₂-+ : ∀ {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
    cong₂-+ refl refl = refl

-- Fin-zero absurdity: if n ≡ 0 then Fin n is empty.
private
  Fin-zero-absurd : ∀ {n : ℕ} → n ≡ 0 → Fin n → ⊥
  Fin-zero-absurd refl ()

--------------------------------------------------------------------------------
-- idˡ : `id ∘ f ≈Term f`. Proof skeleton.
--
-- The proof's vertex bijection is direct: `hComposeP ⟪f⟫ (hId B)` has
-- nV = ⟪f⟫.nV + count-non (hId B).dom, which reduces to ⟪f⟫.nV + 0 by
-- `hId-count-non-dom`. φ maps any vertex by splitAt, with the K-side
-- being impossible (Fin 0) via `Fin-zero-absurd`.
--
-- The edge bijection is similar: (hId B).nE ≡ 0 by `hId-nE`.
--
-- Label, boundary, and elab preservation follow from the pruned
-- composite's structure when K has no edges and K.dom covers everything.

-- Generic left-identity-composition iso: for any G with cod = flatten B,
-- `hComposeP G (hId B) ≅ᴴ G`. The original `idˡ-proof` only used G's
-- record fields (never f's structure), so it generalizes directly to
-- arbitrary hypergraphs in the appropriate type.

module hCompose-hId-R-proof
  {As : List X} {B : ObjTerm}
  (G : Hypergraph FlatGen As (flatten B))
  where
  private
    K = hId B
    C = hComposeP G K
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph C
    module hCP = hComposeP-impl G K

    open import Categories.APROP.Hypergraph.FromAPROP sig using (map-via-inj)

    -- Key facts.
    cn≡0 : count-non K.dom ≡ 0
    cn≡0 = hId-count-non-dom B

    nE≡0 : K.nE ≡ 0
    nE≡0 = hId-nE B

  φ : Fin C.nV → Fin G.nV
  φ v with splitAt G.nV v
  ... | inj₁ i = i
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ⁻¹ : Fin G.nV → Fin C.nV
  φ⁻¹ i = i ↑ˡ count-non K.dom

  ψ : Fin C.nE → Fin G.nE
  ψ e with splitAt G.nE e
  ... | inj₁ eG = eG
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ⁻¹ : Fin G.nE → Fin C.nE
  ψ⁻¹ e = e ↑ˡ K.nE

  ------------------------------------------------------------------------------
  -- Bijection laws.

  open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt G.nV v in eq
  ... | inj₁ i = splitAt⁻¹-↑ˡ eq
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i
  φ-rght i rewrite splitAt-↑ˡ G.nV i (count-non K.dom) = refl

  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e with splitAt G.nE e in eq
  ... | inj₁ eG = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e rewrite splitAt-↑ˡ G.nE e K.nE = refl

  ------------------------------------------------------------------------------
  -- Label preservation.
  --
  -- G.vlab (φ v) ≡ C.vlab v. On the inj₁ side, both reduce to G.vlab i.
  -- The inj₂ side is absurd.

  φ-lab : ∀ v → G.vlab (φ v) ≡ C.vlab v
  φ-lab v with splitAt G.nV v
  ... | inj₁ i = refl
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  ------------------------------------------------------------------------------
  -- Edge endpoint preservation.

  open import Data.List.Properties using (map-∘; map-cong; map-id)

  -- φ ∘ injL ≡ id on G-vertices.
  private
    φ-injL : ∀ i → φ (i ↑ˡ count-non K.dom) ≡ i
    φ-injL i rewrite splitAt-↑ˡ G.nV i (count-non K.dom) = refl

  ψ-ein : ∀ e → G.ein (ψ e) ≡ map φ (Hypergraph.ein C e)
  ψ-ein e with splitAt G.nE e
  ... | inj₁ eG = sym
    (trans (sym (map-∘ (G.ein eG)))
           (trans (map-cong φ-injL (G.ein eG))
                  (map-id (G.ein eG))))
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ-eout : ∀ e → G.eout (ψ e) ≡ map φ (Hypergraph.eout C e)
  ψ-eout e with splitAt G.nE e
  ... | inj₁ eG = sym
    (trans (sym (map-∘ (G.eout eG)))
           (trans (map-cong φ-injL (G.eout eG))
                  (map-id (G.eout eG))))
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ------------------------------------------------------------------------------
  -- Boundary preservation.

  -- C.dom = map injL G.dom. Need: G.dom ≡ map φ (map injL G.dom).
  φ-dom : G.dom ≡ map φ C.dom
  φ-dom = sym
    (trans (sym (map-∘ G.dom))
           (trans (map-cong φ-injL G.dom)
                  (map-id G.dom)))

  -- C.cod = map remapP K.cod. Need: G.cod ≡ map φ (map remapP K.cod).
  --
  -- Proof strategy via equational reasoning (avoiding subst chains):
  --   G.cod
  --     ≡⟨ sym (map-id G.cod) ⟩
  --   map id G.cod
  --     ≡⟨ sym (map-cong φ-rght G.cod) ⟩
  --   map (φ ∘ φ⁻¹) G.cod
  --     ≡⟨ map-∘ G.cod ⟩
  --   map φ (map φ⁻¹ G.cod)
  --     ≡⟨ cong (map φ) idˡ-cod-helper ⟩   -- hId-specific helper
  --   map φ C.cod
  --     ∎
  -- where `idˡ-cod-helper : map φ⁻¹ G.cod ≡ C.cod`.
  --
  -- The helper relies on the hId-specific facts that
  --   * K.cod ≡ K.dom        (hId-cod≡dom)       — dom and cod are the
  --     same list of Fin values for an identity.
  --   * Unique K.dom          (hId-dom-Unique)    — lets us use
  --     classify-lookup-Unique to reduce remapP on K.dom positions to
  --     `inject+ c ∘ lookup-cod`.
  -- Combined with a small suite of tabulate / allFin / cast lemmas, the
  -- helper reduces to a chain of `map-tabulate` + pointwise
  -- `classify-lookup-Unique` rewrites.

  -- Auxiliaries.
  private
    -- xs ≡ map (lookup xs) (allFin (length xs)).
    -- allFin n = tabulate id, so map f (allFin n) = tabulate f (via map-tabulate).
    map-lookup-allFin
      : ∀ {A : Set} (xs : List A)
      → map (lookup xs) (allFin (length xs)) ≡ xs
    map-lookup-allFin xs = trans (map-tabulate (λ i → i) (lookup xs)) (tabulate-lookup xs)

    -- map (cast eq) (allFin m) ≡ allFin n when eq : m ≡ n.
    -- Proved by pattern-matching on the proof and using cast-is-id.
    cast-allFin
      : ∀ {m n} (eq : m ≡ n) → map (cast eq) (allFin m) ≡ allFin n
    cast-allFin refl =
      trans (map-cong (λ i → cast-is-id refl i) (allFin _)) (map-id (allFin _))

  -- Pointwise reduction of `remapP` on K.dom[j].
  -- By Unique K.dom, `classify K.dom (lookup K.dom j) = inj₁ j`; hence
  -- `remapP = remap K.dom lookup-cod` reduces to
  -- `inject+ (count-non K.dom) (lookup-cod j)`.
  remapP-on-dom
    : ∀ (j : Fin (length K.dom))
    → hCP.remapP (lookup K.dom j)
    ≡ hCP.lookup-cod j ↑ˡ count-non K.dom
  remapP-on-dom j =
    remap-inj₁ K.dom hCP.lookup-cod (lookup K.dom j) j
      (classify-lookup-Unique K.dom (hId-dom-Unique B) j)

  -- Now the main equality.
  --
  -- map remapP K.cod
  --   ≡ map remapP K.dom                                 [hId-cod≡dom]
  --   ≡ map (remapP ∘ lookup K.dom) (allFin n)           [sym map-lookup-allFin]
  --   ≡ map (λ j → inject+ c (lookup-cod j)) (allFin n)  [remapP-on-dom pointwise]
  --   ≡ map (inject+ c ∘ lookup-cod) (allFin n)
  --   ≡ map (inject+ c) (map lookup-cod (allFin n))      [map-∘]
  --   ≡ map (inject+ c) (map (lookup G.cod ∘ cast _) (allFin n))  [def lookup-cod]
  --   ≡ map (inject+ c) (map (lookup G.cod) (map (cast _) (allFin n)))  [map-∘]
  --   ≡ map (inject+ c) (map (lookup G.cod) (allFin (length G.cod)))    [cast-allFin]
  --   ≡ map (inject+ c) G.cod                              [map-lookup-allFin]
  --
  -- Combined: map φ⁻¹ G.cod ≡ map remapP K.cod, i.e. `sym` of the above.

  idˡ-cod-helper : map φ⁻¹ G.cod ≡ C.cod
  idˡ-cod-helper = sym (begin
      map hCP.remapP K.cod
        ≡⟨ cong (map hCP.remapP) (hId-cod≡dom B) ⟩
      map hCP.remapP K.dom
        ≡⟨ cong (map hCP.remapP) (sym (map-lookup-allFin K.dom)) ⟩
      map hCP.remapP (map (lookup K.dom) (allFin (length K.dom)))
        ≡⟨ sym (map-∘ (allFin (length K.dom))) ⟩
      map (λ j → hCP.remapP (lookup K.dom j)) (allFin (length K.dom))
        ≡⟨ map-cong remapP-on-dom (allFin (length K.dom)) ⟩
      map (λ j → hCP.lookup-cod j ↑ˡ count-non K.dom)
          (allFin (length K.dom))
        ≡⟨ map-∘ (allFin (length K.dom)) ⟩
      map (_↑ˡ count-non K.dom)
          (map hCP.lookup-cod (allFin (length K.dom)))
        ≡⟨ cong (map (_↑ˡ count-non K.dom)) (map-∘ (allFin (length K.dom))) ⟩
      map (_↑ˡ count-non K.dom)
          (map (lookup G.cod) (map (cast hCP.dom-cod-len) (allFin (length K.dom))))
        ≡⟨ cong (λ xs → map (_↑ˡ count-non K.dom) (map (lookup G.cod) xs))
               (cast-allFin hCP.dom-cod-len) ⟩
      map (_↑ˡ count-non K.dom)
          (map (lookup G.cod) (allFin (length G.cod)))
        ≡⟨ cong (map (_↑ˡ count-non K.dom)) (map-lookup-allFin G.cod) ⟩
      map (_↑ˡ count-non K.dom) G.cod
        ∎)
    where open ≡-Reasoning

  φ-cod : G.cod ≡ map φ C.cod
  φ-cod =
    trans (sym (map-id G.cod))
    (trans (sym (map-cong φ-rght G.cod))
    (trans (map-∘ G.cod)
           (cong (map φ) idˡ-cod-helper)))

  ------------------------------------------------------------------------------
  -- Atom-list equalities.
  --
  -- KEY TECHNIQUE: instead of deriving atom-ein/atom-eout from ψ-ein/φ-lab
  -- (which would force ψ-elab to be a subst₂ chain relating two different
  -- proof terms of the same equality — untractable without UIP), we
  -- STRATEGICALLY choose atom-ein/atom-eout to MATCH the specific proof
  -- terms used inside hComposeP-impl.elab-c's subst₂. Then ψ-elab reduces
  -- to `refl` after the `with splitAt` match.

  atom-ein : ∀ e → map G.vlab (G.ein (ψ e)) ≡ map C.vlab (Hypergraph.ein C e)
  atom-ein e with splitAt G.nE e
  ... | inj₁ eG = map-via-inj hCP.vlab-injL (G.ein eG)
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  atom-eout : ∀ e → map G.vlab (G.eout (ψ e)) ≡ map C.vlab (Hypergraph.eout C e)
  atom-eout e with splitAt G.nE e
  ... | inj₁ eG = map-via-inj hCP.vlab-injL (G.eout eG)
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ------------------------------------------------------------------------------
  -- Edge label compatibility.
  --
  -- With atom-ein/atom-eout matching `hCP.elab-c`'s internal subst₂ proofs
  -- (which both use `map-via-inj hCP.vlab-injL`), the LHS and RHS of
  -- ψ-elab's goal reduce to the SAME subst₂ application. Hence `refl`.

  ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (G.elab (ψ e))
               ≡ Hypergraph.elab C e
  ψ-elab e with splitAt G.nE e
  ... | inj₁ eG = refl
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ------------------------------------------------------------------------------
  -- The assembled ≅ᴴ record.

  hCompose-hId-R-iso : C ≅ᴴ G
  hCompose-hId-R-iso = record
    { φ         = φ
    ; φ⁻¹       = φ⁻¹
    ; φ-left    = φ-left
    ; φ-rght    = φ-rght
    ; ψ         = ψ
    ; ψ⁻¹       = ψ⁻¹
    ; ψ-left    = ψ-left
    ; ψ-rght    = ψ-rght
    ; φ-lab     = φ-lab
    ; ψ-ein     = ψ-ein
    ; ψ-eout    = ψ-eout
    ; φ-dom     = φ-dom
    ; φ-cod     = φ-cod
    ; atom-ein  = atom-ein
    ; atom-eout = atom-eout
    ; ψ-elab    = ψ-elab
    }

-- Export idˡ proof via the generic hCompose-hId-R-iso.
idˡ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫
idˡ-sound {B = B} f = hCompose-hId-R-proof.hCompose-hId-R-iso {B = B} ⟪ f ⟫

-- Also export the generic iso directly for future use (e.g. λ-nat,
-- triangle, and other axioms that compose with hId on the right).
hCompose-hId-R-iso-generic
  : ∀ {As : List X} (B : ObjTerm)
    (G : Hypergraph FlatGen As (flatten B))
  → hComposeP G (hId B) ≅ᴴ G
hCompose-hId-R-iso-generic B G = hCompose-hId-R-proof.hCompose-hId-R-iso {B = B} G

--------------------------------------------------------------------------------
-- Generic LEFT-identity-composition iso: for any K with dom = flatten A
-- and Unique K.dom, `hComposeP (hId A) K ≅ᴴ K`.
--
-- This is the "mirror" of hCompose-hId-R-iso. Structurally analogous
-- to σ∘σ-proof's classify-based bijection: since K.dom's length equals
-- `(hId A).nV` and K.dom is Unique, each vertex of K is classified
-- as either "in K.dom" (matching a hId A vertex) or "not in K.dom"
-- (a pruned-K-side vertex).

module hCompose-hId-L-proof
  {A : ObjTerm} {Bs : List X}
  (K : Hypergraph FlatGen (flatten A) Bs)
  (K-unique : Unique (Hypergraph.dom K))
  where
  private
    G = hId A
    C = hComposeP G K
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph C
    module hCP = hComposeP-impl G K

    open import Data.List.Properties using (length-map)
    open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
                                           cast-is-id; cast-trans;
                                           toℕ-cast; toℕ-injective)

    -- G has zero edges.
    G-nE≡0 : G.nE ≡ 0
    G-nE≡0 = hId-nE A

    -- Length of K.dom matches G.nV = (hId A).nV.
    len-dom : length K.dom ≡ G.nV
    len-dom =
      trans (sym (length-map K.vlab K.dom))
      (trans (cong length K.dom-ok)
             (sym (hId-nV≡len-flatten A)))

  ------------------------------------------------------------------------------
  -- Vertex bijection.
  --
  -- C.nV = G.nV + count-non K.dom.
  -- φ splits via splitAt G.nV:
  --   inj₁ k (k : Fin G.nV) ↦ lookup K.dom (cast (sym len-dom) k).
  --   inj₂ j (j : Fin (count-non K.dom)) ↦ lookup (nonMem K.dom) j.
  -- φ⁻¹ via classify K.dom:
  --   inj₁ i ↦ cast len-dom i ↑ˡ count-non K.dom.
  --   inj₂ j ↦ G.nV ↑ʳ j.

  φ : Fin C.nV → Fin K.nV
  φ v with splitAt G.nV v
  ... | inj₁ k = lookup K.dom (cast (sym len-dom) k)
  ... | inj₂ j = lookup (nonMem K.dom) j

  φ⁻¹ : Fin K.nV → Fin C.nV
  φ⁻¹ v with classify K.dom v
  ... | inj₁ i = cast len-dom i ↑ˡ count-non K.dom
  ... | inj₂ j = G.nV ↑ʳ j

  ------------------------------------------------------------------------------
  -- Bijection laws.

  open import Categories.APROP.Hypergraph.Prune
    using ( classify-inj₁-lookup; classify-inj₂-lookup
          ; classify-lookup-nonMem; lookup-≡-map-cast; remap-inj₂)

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt G.nV v in eq
  ... | inj₁ k
    rewrite classify-lookup-Unique K.dom K-unique (cast (sym len-dom) k)
    = trans (cong (_↑ˡ count-non K.dom)
                  (trans (cast-trans (sym len-dom) len-dom k)
                         (cast-is-id (trans (sym len-dom) len-dom) k)))
            (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ j
    rewrite classify-lookup-nonMem K.dom j
    = splitAt⁻¹-↑ʳ eq

  φ-rght : ∀ v → φ (φ⁻¹ v) ≡ v
  φ-rght v with classify K.dom v in eq
  ... | inj₁ i
    rewrite splitAt-↑ˡ G.nV (cast len-dom i) (count-non K.dom)
    = trans (cong (lookup K.dom)
                  (trans (cast-trans len-dom (sym len-dom) i)
                         (cast-is-id (trans len-dom (sym len-dom)) i)))
            (classify-inj₁-lookup K.dom v i eq)
  ... | inj₂ j
    rewrite splitAt-↑ʳ G.nV (count-non K.dom) j
    = classify-inj₂-lookup K.dom v j eq

  ------------------------------------------------------------------------------
  -- Edge bijection: G has no edges, so C.nE = 0 + K.nE = K.nE (only
  -- propositionally, since G.nE = (hId A).nE isn't def-0 for abstract A).
  -- We pattern-match on `splitAt G.nE e` with the inj₁ branch absurd.

  ψ : Fin C.nE → Fin K.nE
  ψ e with splitAt G.nE e
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = eK

  ψ⁻¹ : Fin K.nE → Fin C.nE
  ψ⁻¹ e = G.nE ↑ʳ e

  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e with splitAt G.nE e in eq
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = splitAt⁻¹-↑ʳ eq

  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e rewrite splitAt-↑ʳ G.nE K.nE e = refl
    where open import Data.Fin.Properties using (splitAt-↑ʳ)

  ------------------------------------------------------------------------------
  -- Label preservation.
  --
  -- For v with splitAt G.nV v = inj₁ k:
  --   C.vlab v = G.vlab k = (hId A).vlab k
  --   K.vlab (φ v) = K.vlab (lookup K.dom (cast (sym len-dom) k)).
  --   By K.dom-ok (pointwise): K.vlab (lookup K.dom j) ≡ lookup (flatten A) (cast _ j).
  --   By hId-vlab-lookup: (hId A).vlab k ≡ lookup (flatten A) (cast _ k).
  --   Both sides reduce to `lookup (flatten A) (cast _ k)` modulo toℕ-injective.
  --
  -- For v with splitAt G.nV v = inj₂ j:
  --   C.vlab v = K.vlab (lookup (nonMem K.dom) j) = K.vlab (φ v).  REFL.

  open import Data.Fin using (toℕ)

  -- Pointwise from K.dom-ok: K.vlab (lookup K.dom j) ≡ lookup (flatten A) (cast _ j).
  -- `lookup-≡-map-cast` gives us this in a specific cast form; we then use
  -- toℕ-injective to collapse that with `hId-vlab-lookup`'s cast.

  φ-lab : ∀ v → K.vlab (φ v) ≡ C.vlab v
  φ-lab v with splitAt G.nV v
  ... | inj₁ k =
    -- Goal: K.vlab (lookup K.dom (cast (sym len-dom) k)) ≡ G.vlab k
    -- RHS:  G.vlab k = (hId A).vlab k ≡ lookup (flatten A) (cast _ k)
    --       by hId-vlab-lookup.
    -- LHS:  K.vlab (lookup K.dom j)   ≡ lookup (flatten A) (cast _ j)
    --       by lookup-≡-map-cast K.vlab (sym K.dom-ok), with j = cast (sym len-dom) k.
    -- Both casts applied to k have toℕ = toℕ k, so equal by toℕ-injective.
    trans (sym (lookup-≡-map-cast K.vlab (sym K.dom-ok) (cast (sym len-dom) k)))
    (trans (cong (lookup (flatten A)) same-cast-at-k)
           (sym (hId-vlab-lookup A k)))
    where
      open import Data.Fin using (cast)

      -- The two distinct Fin values (from the two casts) both have
      -- toℕ = toℕ k, hence they're equal by toℕ-injective.
      same-cast-at-k
        : cast (sym (trans (cong length (sym K.dom-ok)) (length-map K.vlab K.dom)))
               (cast (sym len-dom) k)
        ≡ cast (hId-nV≡len-flatten A) k
      same-cast-at-k = toℕ-injective
        (trans (toℕ-cast _ (cast (sym len-dom) k))
        (trans (toℕ-cast _ k)
               (sym (toℕ-cast _ k))))
  ... | inj₂ j = refl

  ------------------------------------------------------------------------------
  -- Edge endpoints via `φ ∘ remapP = id on K.nV`.

  private
    -- φ composed with remapP is the identity on K.nV.
    -- For v ∈ K.dom: classify → inj₁ i. remapP v = inject+ _ (lookup-cod i).
    --   φ (inject+ _ k) via splitAt inj₁ → lookup K.dom (cast (sym len-dom) k).
    --   With k = lookup-cod i and appropriate toℕ reasoning, this = v.
    -- For v ∉ K.dom: classify → inj₂ j. remapP v = raise G.nV j.
    --   φ (raise G.nV j) via splitAt inj₂ → lookup (nonMem K.dom) j = v.

    -- toℕ (lookup G.cod j) ≡ toℕ j for G = hId A.
    -- Transport via hId-cod≡range: use subst to replace G.cod with
    -- range G.nV in the quantified statement, then apply lookup-range.
    toℕ-lookup-GCod
      : ∀ (j : Fin (length G.cod)) → toℕ (lookup G.cod j) ≡ toℕ j
    toℕ-lookup-GCod =
      subst (λ l → ∀ (k : Fin (length l)) → toℕ (lookup l k) ≡ toℕ k)
            (sym (hId-cod≡range A))
            (lookup-range G.nV)

    -- lookup-cod on G = hId A at toℕ-level: equals the input toℕ.
    toℕ-lookup-cod
      : ∀ (i : Fin (length K.dom))
      → toℕ (hCP.lookup-cod i) ≡ toℕ i
    toℕ-lookup-cod i =
      trans (toℕ-lookup-GCod (cast hCP.dom-cod-len i))
            (toℕ-cast hCP.dom-cod-len i)
      where open import Data.Fin using (cast)

    φ-remapP-id : ∀ v → φ (hCP.remapP v) ≡ v
    φ-remapP-id v with classify K.dom v in eq
    ... | inj₁ i
      rewrite splitAt-↑ˡ G.nV (hCP.lookup-cod i) (count-non K.dom)
      = trans (cong (lookup K.dom) cast-eq)
              (classify-inj₁-lookup K.dom v i eq)
      where
        open import Data.Fin using (cast)
        cast-eq : cast (sym len-dom) (hCP.lookup-cod i) ≡ i
        cast-eq = toℕ-injective
          (trans (toℕ-cast (sym len-dom) (hCP.lookup-cod i))
                 (toℕ-lookup-cod i))
    ... | inj₂ j
      rewrite splitAt-↑ʳ G.nV (count-non K.dom) j
      = classify-inj₂-lookup K.dom v j eq

  open import Data.List.Properties using (map-∘; map-cong; map-id)

  ψ-ein : ∀ e → K.ein (ψ e) ≡ map φ (C.ein e)
  ψ-ein e with splitAt G.nE e
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = sym
    (trans (sym (map-∘ (K.ein eK)))
    (trans (map-cong φ-remapP-id (K.ein eK))
           (map-id (K.ein eK))))

  ψ-eout : ∀ e → K.eout (ψ e) ≡ map φ (C.eout e)
  ψ-eout e with splitAt G.nE e
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = sym
    (trans (sym (map-∘ (K.eout eK)))
    (trans (map-cong φ-remapP-id (K.eout eK))
           (map-id (K.eout eK))))

  ------------------------------------------------------------------------------
  -- Boundary preservation.
  --
  -- C.dom = map injL G.dom = map injL (hId A).dom.
  -- We need K.dom ≡ map φ C.dom.
  --
  -- Via hId-dom≡range: (hId A).dom ≡ range G.nV.
  -- Via range≡allFin-pub: range G.nV ≡ allFin G.nV.
  -- Pointwise reduction: φ ∘ injL → lookup K.dom ∘ cast (sym len-dom).
  -- Combined with tabulate-lookup identities, reduces to K.dom.
  --
  -- C.cod = map remapP K.cod. Via φ-remapP-id and map-∘/map-id,
  -- map φ (map remapP K.cod) = map id K.cod = K.cod.

  private
    φ-injL-eq : ∀ k → φ (hCP.injL k) ≡ lookup K.dom (cast (sym len-dom) k)
    φ-injL-eq k rewrite splitAt-↑ˡ G.nV k (count-non K.dom) = refl

  open import Data.List using (_++_; tabulate; allFin)
  open import Data.List.Properties using (tabulate-lookup; map-tabulate)

  φ-dom : K.dom ≡ map φ C.dom
  φ-dom =
    -- K.dom ≡ map (lookup K.dom) (allFin (length K.dom))
    -- ≡ map (lookup K.dom) (range (length K.dom))
    -- ≡ map (λ k → lookup K.dom (cast (sym len-dom) k)) (range G.nV)
    -- ≡ map (φ ∘ injL) G.dom   (via hId-dom≡range + φ-injL-eq pointwise)
    -- ≡ map φ (map injL G.dom) = map φ C.dom   (map-∘).
    trans (sym (map-lookup-allFin K.dom))
    (trans (cong (map (lookup K.dom)) (sym range≡allFin-len))
    (trans map-via-cast
    (trans (cong (λ l → map (λ k → lookup K.dom (cast (sym len-dom) k)) l)
                 (sym (hId-dom≡range A)))
    (trans (map-cong (λ k → sym (φ-injL-eq k)) G.dom)
           (map-∘ G.dom)))))
    where
      open import Data.Fin using (cast)
      open import Data.List using (lookup)
      -- xs ≡ map (lookup xs) (allFin (length xs))
      map-lookup-allFin
        : ∀ {A : Set} (xs : List A)
        → map (lookup xs) (allFin (length xs)) ≡ xs
      map-lookup-allFin xs =
        trans (map-tabulate (λ i → i) (lookup xs)) (tabulate-lookup xs)

      -- range (length K.dom) ≡ allFin (length K.dom).
      range≡allFin-len : range (length K.dom) ≡ allFin (length K.dom)
      range≡allFin-len = range≡allFin-pub (length K.dom)

      -- map (lookup K.dom) (range (length K.dom))
      -- ≡ map (lookup K.dom ∘ cast (sym len-dom)) (range G.nV)
      -- via map-cast-range + map-∘.
      map-via-cast
        : map (lookup K.dom) (range (length K.dom))
        ≡ map (λ k → lookup K.dom (cast (sym len-dom) k)) (range G.nV)
      map-via-cast =
        trans (cong (map (lookup K.dom)) (sym (map-cast-range (sym len-dom))))
              (sym (map-∘ (range G.nV)))

  φ-cod : K.cod ≡ map φ C.cod
  φ-cod = sym
    (trans (sym (map-∘ K.cod))
    (trans (map-cong φ-remapP-id K.cod)
           (map-id K.cod)))

  ------------------------------------------------------------------------------
  -- Atom-list equalities, chosen to match `elab-c`'s internal subst₂ proofs.

  atom-ein : ∀ e → map K.vlab (K.ein (ψ e)) ≡ map C.vlab (C.ein e)
  atom-ein e with splitAt G.nE e
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = hCP.map-via-remapP (K.ein eK)

  atom-eout : ∀ e → map K.vlab (K.eout (ψ e)) ≡ map C.vlab (C.eout e)
  atom-eout e with splitAt G.nE e
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = hCP.map-via-remapP (K.eout eK)

  ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (K.elab (ψ e))
               ≡ C.elab e
  ψ-elab e with splitAt G.nE e
  ... | inj₁ eG = ⊥-elim (Fin-zero-absurd G-nE≡0 eG)
  ... | inj₂ eK = refl

  ------------------------------------------------------------------------------
  -- The assembled ≅ᴴ record.

  hCompose-hId-L-iso : C ≅ᴴ K
  hCompose-hId-L-iso = record
    { φ         = φ
    ; φ⁻¹       = φ⁻¹
    ; φ-left    = φ-left
    ; φ-rght    = φ-rght
    ; ψ         = ψ
    ; ψ⁻¹       = ψ⁻¹
    ; ψ-left    = ψ-left
    ; ψ-rght    = ψ-rght
    ; φ-lab     = φ-lab
    ; ψ-ein     = ψ-ein
    ; ψ-eout    = ψ-eout
    ; φ-dom     = φ-dom
    ; φ-cod     = φ-cod
    ; atom-ein  = atom-ein
    ; atom-eout = atom-eout
    ; ψ-elab    = ψ-elab
    }

-- Public export. `A` is passed explicitly because `flatten` is not
-- injective (different ObjTerms can produce the same atom list, so
-- Agda cannot infer `A` from `flatten A`).
hCompose-hId-L-iso-generic
  : ∀ (A : ObjTerm) {Bs : List X}
    (K : Hypergraph FlatGen (flatten A) Bs)
  → Unique (Hypergraph.dom K)
  → hComposeP (hId A) K ≅ᴴ K
hCompose-hId-L-iso-generic A K K-unique =
  hCompose-hId-L-proof.hCompose-hId-L-iso {A = A} K K-unique

--------------------------------------------------------------------------------
-- idʳ : `f ∘ id ≈Term f`. Direct application of hCompose-hId-L-iso-generic
-- to ⟪f⟫ (with the `Unique ⟪f⟫.dom` side condition supplied by
-- HomTermInvariant.⟪_⟫-dom-unique).

open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)

idʳ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ f ∘ id ⟫ ≅ᴴ ⟪ f ⟫
idʳ-sound {A = A} f = hCompose-hId-L-iso-generic A ⟪ f ⟫ (⟪_⟫-dom-unique f)

-- λ⇒∘id⊗f≈f∘λ⇒ (λ-naturality) is defined below, after
-- hTensor-hEmpty-G-iso is in scope.

--------------------------------------------------------------------------------
-- Other group-(b) axioms that reduce to idˡ or require similar
-- constructions. For axioms `λ⇐∘λ⇒`, `λ⇒∘λ⇐`, `ρ⇐∘ρ⇒`, `ρ⇒∘ρ⇐`,
-- the LHS is `hComposeP (hId A) (hId A)` at a specific boundary
-- (with type-level subst for ρ cases), and the RHS is a specific
-- hId at a ⊗-unit type. They reduce to idˡ-sound applied to `id`.

--------------------------------------------------------------------------------
-- λ⇐∘λ⇒≈id: `λ⇐ ∘ λ⇒ ≈Term id`.
--
-- ⟪ λ⇐ ∘ λ⇒ ⟫ = hComposeP ⟪λ⇒⟫ ⟪λ⇐⟫ = hComposeP (hId A) (hId A).
-- ⟪ id ⟫ = hId (unit ⊗₀ A) = hTensor hEmpty (hId A) (by hId's recursive
--           definition on ⊗₀).
--
-- Using idˡ-sound (id {A}): hComposeP (hId A) (hId A) ≅ᴴ hId A.
-- Then need: hId A ≅ᴴ hTensor hEmpty (hId A). This hId-vs-hTensor iso
-- would be `hEmpty-id-unit-iso` — postulated as its own lemma since it
-- requires chasing through the tensor construction with nV = 0 + n = n.

-- Generic: `hTensor hEmpty G ≅ᴴ G` for any G. The hId specialization
-- (needed for λ-axioms) is a direct corollary below.
--
-- Key facts:
--   * (hTensor hEmpty G).nV = 0 + G.nV = G.nV             (def).
--   * (hTensor hEmpty G).nE = 0 + G.nE = G.nE             (def).
--   * splitAt 0 always gives inj₂, so vlab, ein, eout, elab all
--     reduce to the "K-side" branch with K = G and injR = 0 ↑ʳ_ = id.
--   * `0 ↑ʳ j = j` definitionally, so `map injR xs ≡ xs` up to map-id.
--
-- The "strategic atom-ein" trick: choose
-- `atom-ein = map-via-raise vlab-injR (G.ein e)` (matching the internal
-- subst₂ proof inside hTensor-impl.elab-c's inj₂ branch), making ψ-elab
-- reduce to `refl` after the implicit splitAt 0 reduction.

hTensor-hEmpty-G-iso
  : ∀ {As Bs : List X} (G : Hypergraph FlatGen As Bs)
  → hTensor hEmpty G ≅ᴴ G
hTensor-hEmpty-G-iso {As} {Bs} G = record
  { φ         = λ i → i
  ; φ⁻¹       = λ i → i
  ; φ-left    = λ _ → refl
  ; φ-rght    = λ _ → refl
  ; ψ         = λ e → e
  ; ψ⁻¹       = λ e → e
  ; ψ-left    = λ _ → refl
  ; ψ-rght    = λ _ → refl
  ; φ-lab     = λ _ → refl
  ; ψ-ein     = ein-eq
  ; ψ-eout    = eout-eq
  ; φ-dom     = dom-eq
  ; φ-cod     = cod-eq
  ; atom-ein  = atom-ein-eq
  ; atom-eout = atom-eout-eq
  ; ψ-elab    = elab-eq
  }
  where
    open import Data.List.Properties using (map-id; map-cong)
    open import Categories.APROP.Hypergraph.FromAPROP sig
      using (map-via-raise)
    module G′ = Hypergraph G
    module hT = hTensor-impl hEmpty G

    -- (hTensor hEmpty G).ein e = map injR (G.ein e) (via splitAt 0 = inj₂).
    -- injR = 0 ↑ʳ_ = id def, so map injR ≡ map id ≡ id propositionally.
    ein-eq : ∀ e → G′.ein e ≡ map (λ i → i) (Hypergraph.ein (hTensor hEmpty G) e)
    ein-eq e = sym (trans (map-id (Hypergraph.ein (hTensor hEmpty G) e))
                          (trans (map-cong (λ _ → refl) (G′.ein e))
                                 (map-id (G′.ein e))))

    eout-eq : ∀ e → G′.eout e ≡ map (λ i → i) (Hypergraph.eout (hTensor hEmpty G) e)
    eout-eq e = sym (trans (map-id (Hypergraph.eout (hTensor hEmpty G) e))
                           (trans (map-cong (λ _ → refl) (G′.eout e))
                                  (map-id (G′.eout e))))

    -- (hTensor hEmpty G).dom = [] ++ map injR G.dom = map injR G.dom.
    dom-eq : G′.dom ≡ map (λ i → i) (Hypergraph.dom (hTensor hEmpty G))
    dom-eq = sym (trans (map-id (Hypergraph.dom (hTensor hEmpty G)))
                        (trans (map-cong (λ _ → refl) G′.dom)
                               (map-id G′.dom)))

    cod-eq : G′.cod ≡ map (λ i → i) (Hypergraph.cod (hTensor hEmpty G))
    cod-eq = sym (trans (map-id (Hypergraph.cod (hTensor hEmpty G)))
                        (trans (map-cong (λ _ → refl) G′.cod)
                               (map-id G′.cod)))

    -- atom-ein: `map G.vlab (G.ein e) ≡ map vlab-c (map injR (G.ein e))`.
    -- This is exactly hT.map-via-raise vlab-injR applied to G.ein e.
    atom-ein-eq : ∀ e → map G′.vlab (G′.ein e)
                      ≡ map (Hypergraph.vlab (hTensor hEmpty G))
                            (Hypergraph.ein (hTensor hEmpty G) e)
    atom-ein-eq e = map-via-raise hT.vlab-injR (G′.ein e)

    atom-eout-eq : ∀ e → map G′.vlab (G′.eout e)
                       ≡ map (Hypergraph.vlab (hTensor hEmpty G))
                             (Hypergraph.eout (hTensor hEmpty G) e)
    atom-eout-eq e = map-via-raise hT.vlab-injR (G′.eout e)

    -- ψ-elab: `subst₂ atom-ein atom-eout (G.elab e) ≡ (hTensor hEmpty G).elab e`.
    -- With our atom-ein/atom-eout matching the specific subst₂ proofs used
    -- internally in `elab-c`'s inj₂ branch (after splitAt 0 e = inj₂ e),
    -- both sides become the same subst₂ application.
    elab-eq : ∀ e → subst₂ FlatGen (atom-ein-eq e) (atom-eout-eq e) (G′.elab e)
                  ≡ Hypergraph.elab (hTensor hEmpty G) e
    elab-eq e = refl

-- Specialization for hId A.
hTensor-hEmpty-hId-iso : ∀ (A : ObjTerm) → hTensor hEmpty (hId A) ≅ᴴ hId A
hTensor-hEmpty-hId-iso A = hTensor-hEmpty-G-iso (hId A)

--------------------------------------------------------------------------------
-- "+0 RIGHT-cancel" iso: for any G, the boundary-subst'd
-- `hTensor G hEmpty` is ≅ᴴ to G.  Mirror of `hTensor-hEmpty-G-iso`
-- but the subst₂ around the result is non-trivial: `As ++ [] ≢ As`
-- and `Bs ++ [] ≢ Bs` definitionally (unlike `[] ++ As = As`).
--
-- The construction would go field-by-field through the subst₂ field
-- projections (`nV-subst₂`, `vlab-subst₂`, `dom-subst₂`, `cod-subst₂`,
-- plus `ein-subst₂`, `eout-subst₂`, `elab-subst₂` — not yet added).
-- Since subst₂ with the non-refl `++-identityʳ` doesn't reduce, each
-- field requires explicit cast bookkeeping via `subst-subst-sym` and
-- `splitAt-↑ˡ`.
--
-- For now we postulate the iso as a single focused lemma (replacing
-- three catch-all postulates for ρ⇒∘ρ⇐, α⇒∘α⇐, ρ-nat).  A future pass
-- can discharge this with the field-subst₂ technique used for idˡ +
-- σ∘σ.

open import Data.List.Properties using (++-identityʳ; ++-assoc)

postulate
  hTensor-G-hEmpty-iso-substed
    : ∀ {As Bs : List X} (G : Hypergraph FlatGen As Bs)
    → subst₂ (Hypergraph FlatGen)
             (++-identityʳ As) (++-identityʳ Bs)
             (hTensor G hEmpty)
    ≅ᴴ G

-- Specialization: for hId A, this gives `subst₂ _ p p (hId (A⊗unit)) ≅ᴴ hId A`
-- because `hId (A⊗unit) = hTensor (hId A) hEmpty`.
subst₂-hId-cancel
  : ∀ (A : ObjTerm)
  → subst₂ (Hypergraph FlatGen)
           (++-identityʳ (flatten A)) (++-identityʳ (flatten A))
           (hId (A ⊗₀ unit))
  ≅ᴴ hId A
subst₂-hId-cancel A = hTensor-G-hEmpty-iso-substed (hId A)

--------------------------------------------------------------------------------
-- λ⇒∘id⊗f≈f∘λ⇒ (λ-naturality). Chain via:
--   ⟪ λ⇒ ∘ id⊗f ⟫ = hComposeP (hTensor hEmpty ⟪f⟫) (hId B)
--                  ≅ᴴ hTensor hEmpty ⟪f⟫   [hCompose-hId-R-iso-generic B]
--                  ≅ᴴ ⟪f⟫                   [hTensor-hEmpty-G-iso]
--   ⟪ f ∘ λ⇒ ⟫    = hComposeP (hId A) ⟪f⟫
--                  ≅ᴴ ⟪f⟫                   [hCompose-hId-L-iso-generic]
-- Combine with trans-≅ᴴ / sym-≅ᴴ.

λ⇒∘id⊗f≈f∘λ⇒-sound
  : ∀ {A B} {f : HomTerm A B}
  → ⟪ λ⇒ {B} ∘ (id {unit} ⊗₁ f) ⟫ ≅ᴴ ⟪ f ∘ λ⇒ {A} ⟫
λ⇒∘id⊗f≈f∘λ⇒-sound {A = A} {B = B} {f = f} =
  trans-≅ᴴ
    (trans-≅ᴴ (hCompose-hId-R-iso-generic B (hTensor hEmpty ⟪ f ⟫))
              (hTensor-hEmpty-G-iso ⟪ f ⟫))
    (sym-≅ᴴ (hCompose-hId-L-iso-generic A ⟪ f ⟫ (⟪_⟫-dom-unique f)))

λ⇐∘λ⇒-sound : ∀ {A} → ⟪ λ⇐ {A} ∘ λ⇒ {A} ⟫ ≅ᴴ ⟪ id {unit ⊗₀ A} ⟫
λ⇐∘λ⇒-sound {A} = trans-≅ᴴ (idˡ-sound (id {A})) (sym-≅ᴴ (hTensor-hEmpty-hId-iso A))

λ⇒∘λ⇐-sound : ∀ {A} → ⟪ λ⇒ {A} ∘ λ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫
λ⇒∘λ⇐-sound {A} = idˡ-sound (id {A})

--------------------------------------------------------------------------------
-- ρ⇐∘ρ⇒≈id: `⟪ρ⇐ ∘ ρ⇒⟫ = hComposeP ⟪ρ⇒⟫ ⟪ρ⇐⟫` reduces to
-- `hComposeP (hId (A⊗unit)) (hId (A⊗unit))` via `hComposeP-subst-both`
-- (the outer boundaries of both sides are flatten A ++ [] so the
-- subst₂s on eq₁ and eq₃ are refl, and only the middle eq₂ =
-- ++-identityʳ is non-trivial).  After that reduction, `idˡ-sound
-- (id {A⊗unit})` closes the iso.

-- To avoid a ~100k ms conversion-check blowup, we use `cong₂ hComposeP`
-- applied to *abstract* arg-level equalities. With the refl proofs hidden
-- behind `abstract`, Agda can't reduce the `cong₂` application, so the
-- resulting equality proof stays structural and the `subst` below never
-- forces a deep comparison of the two `hComposeP ...` records.
ρ⇐∘ρ⇒-sound : ∀ {A} → ⟪ ρ⇐ {A} ∘ ρ⇒ {A} ⟫ ≅ᴴ ⟪ id {A ⊗₀ unit} ⟫
ρ⇐∘ρ⇒-sound {A} =
  subst (_≅ᴴ hId (A ⊗₀ unit)) (sym full-eq)
        (idˡ-sound (id {A ⊗₀ unit}))
  where
    open import Data.List.Properties using (++-identityʳ)
    eq = ++-identityʳ (flatten A)
    abstract
      arg1 : ⟪ ρ⇒ {A} ⟫
           ≡ subst₂ (Hypergraph FlatGen) refl eq (hId (A ⊗₀ unit))
      arg1 = refl
      arg2 : ⟪ ρ⇐ {A} ⟫
           ≡ subst₂ (Hypergraph FlatGen) eq refl (hId (A ⊗₀ unit))
      arg2 = refl
    full-eq : ⟪ ρ⇐ {A} ∘ ρ⇒ {A} ⟫
            ≡ hComposeP (hId (A ⊗₀ unit)) (hId (A ⊗₀ unit))
    full-eq = trans (cong₂ hComposeP arg1 arg2)
                    (hComposeP-subst-both refl eq refl
                                          (hId (A ⊗₀ unit)) (hId (A ⊗₀ unit)))

-- α⇐∘α⇒≈id: same pattern as ρ⇐∘ρ⇒ — outer boundaries on both sides
-- are `flatten ((A⊗B)⊗C) = (flatten A ++ flatten B) ++ flatten C`,
-- so `hComposeP-subst-both` with eq₁ = eq₃ = refl, eq₂ = ++-assoc
-- strips the subst₂ cleanly, and `idˡ-sound (id {(A⊗B)⊗C})` closes.

α⇐∘α⇒-sound : ∀ {A B C} → ⟪ α⇐ {A}{B}{C} ∘ α⇒ {A}{B}{C} ⟫ ≅ᴴ ⟪ id {(A ⊗₀ B) ⊗₀ C} ⟫
α⇐∘α⇒-sound {A} {B} {C} =
  subst (_≅ᴴ hId ((A ⊗₀ B) ⊗₀ C)) (sym full-eq)
        (idˡ-sound (id {(A ⊗₀ B) ⊗₀ C}))
  where
    open import Data.List.Properties using (++-assoc)
    eq = ++-assoc (flatten A) (flatten B) (flatten C)
    abstract
      arg1 : ⟪ α⇒ {A}{B}{C} ⟫
           ≡ subst₂ (Hypergraph FlatGen) refl eq (hId ((A ⊗₀ B) ⊗₀ C))
      arg1 = refl
      arg2 : ⟪ α⇐ {A}{B}{C} ⟫
           ≡ subst₂ (Hypergraph FlatGen) eq refl (hId ((A ⊗₀ B) ⊗₀ C))
      arg2 = refl
    full-eq : ⟪ α⇐ {A}{B}{C} ∘ α⇒ {A}{B}{C} ⟫
            ≡ hComposeP (hId ((A ⊗₀ B) ⊗₀ C)) (hId ((A ⊗₀ B) ⊗₀ C))
    full-eq = trans (cong₂ hComposeP arg1 arg2)
                    (hComposeP-subst-both refl eq refl
                                          (hId ((A ⊗₀ B) ⊗₀ C))
                                          (hId ((A ⊗₀ B) ⊗₀ C)))

-- ρ⇒∘ρ⇐≈id: "asymmetric" direction. Chain via hComposeP-subst-both
-- to reduce to `subst₂ _ eq eq (hComposeP (hId _) (hId _))`, then
-- subst₂-resp-≅ᴴ + idˡ-sound + subst₂-hId-cancel.

ρ⇒∘ρ⇐-sound : ∀ {A} → ⟪ ρ⇒ {A} ∘ ρ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫
ρ⇒∘ρ⇐-sound {A} =
  subst (_≅ᴴ hId A) (sym full-eq)
    (trans-≅ᴴ (subst₂-resp-≅ᴴ eq eq (idˡ-sound (id {A ⊗₀ unit})))
              (subst₂-hId-cancel A))
  where
    eq = ++-identityʳ (flatten A)
    abstract
      arg1 : ⟪ ρ⇐ {A} ⟫ ≡ subst₂ (Hypergraph FlatGen) eq refl (hId (A ⊗₀ unit))
      arg1 = refl
      arg2 : ⟪ ρ⇒ {A} ⟫ ≡ subst₂ (Hypergraph FlatGen) refl eq (hId (A ⊗₀ unit))
      arg2 = refl
    full-eq : ⟪ ρ⇒ {A} ∘ ρ⇐ {A} ⟫
            ≡ subst₂ (Hypergraph FlatGen) eq eq
                     (hComposeP (hId (A ⊗₀ unit)) (hId (A ⊗₀ unit)))
    full-eq = trans (cong₂ hComposeP arg1 arg2)
                    (hComposeP-subst-both eq refl eq
                                          (hId (A ⊗₀ unit)) (hId (A ⊗₀ unit)))

-- α⇒∘α⇐≈id: analogous pattern with ++-assoc.  Needs a variant of the
-- "hId-cancel" iso: `subst₂ _ (++-assoc _) (++-assoc _) (hId ((A⊗B)⊗C))
-- ≅ᴴ hId (A⊗(B⊗C))`. This is a structural iso on hId that reassociates
-- the tensor structure — not derivable from `hTensor-G-hEmpty-iso-substed`
-- (which is about `++-identityʳ`, not `++-assoc`).  Postulated here as
-- a focused lemma; dispatching α⇒∘α⇐ uses it analogously to ρ⇒∘ρ⇐'s
-- use of `subst₂-hId-cancel`.
postulate
  subst₂-hId-assoc-cancel
    : ∀ (A B C : ObjTerm)
    → subst₂ (Hypergraph FlatGen)
             (++-assoc (flatten A) (flatten B) (flatten C))
             (++-assoc (flatten A) (flatten B) (flatten C))
             (hId ((A ⊗₀ B) ⊗₀ C))
    ≅ᴴ hId (A ⊗₀ (B ⊗₀ C))

α⇒∘α⇐-sound : ∀ {A B C} → ⟪ α⇒ {A}{B}{C} ∘ α⇐ {A}{B}{C} ⟫ ≅ᴴ ⟪ id {A ⊗₀ (B ⊗₀ C)} ⟫
α⇒∘α⇐-sound {A} {B} {C} =
  subst (_≅ᴴ hId (A ⊗₀ (B ⊗₀ C))) (sym full-eq)
    (trans-≅ᴴ (subst₂-resp-≅ᴴ eq eq (idˡ-sound (id {(A ⊗₀ B) ⊗₀ C})))
              (subst₂-hId-assoc-cancel A B C))
  where
    eq = ++-assoc (flatten A) (flatten B) (flatten C)
    abstract
      arg1 : ⟪ α⇐ {A}{B}{C} ⟫
           ≡ subst₂ (Hypergraph FlatGen) eq refl (hId ((A ⊗₀ B) ⊗₀ C))
      arg1 = refl
      arg2 : ⟪ α⇒ {A}{B}{C} ⟫
           ≡ subst₂ (Hypergraph FlatGen) refl eq (hId ((A ⊗₀ B) ⊗₀ C))
      arg2 = refl
    full-eq : ⟪ α⇒ {A}{B}{C} ∘ α⇐ {A}{B}{C} ⟫
            ≡ subst₂ (Hypergraph FlatGen) eq eq
                     (hComposeP (hId ((A ⊗₀ B) ⊗₀ C))
                                (hId ((A ⊗₀ B) ⊗₀ C)))
    full-eq = trans (cong₂ hComposeP arg1 arg2)
                    (hComposeP-subst-both eq refl eq
                                          (hId ((A ⊗₀ B) ⊗₀ C))
                                          (hId ((A ⊗₀ B) ⊗₀ C)))

--------------------------------------------------------------------------------
-- σ∘σ≈id: the braiding is self-inverse.
--
-- ⟪ σ ∘ σ ⟫ = hComposeP (hSwap A B) (hSwap B A).
-- ⟪ id {A ⊗₀ B} ⟫ = hId (A ⊗₀ B) = hTensor (hId A) (hId B).
--
-- Structural ingredients (all proved in Invariant):
--   * hSwap-count-non-dom: count-non K.dom ≡ 0 (K = hSwap B A covers).
--   * hSwap-nE:            hSwap has no edges.
--   * hId-vlab-lookup:     (hId A).vlab i ≡ lookup (flatten A) (cast _ i).
--   * hId-dom≡range:       (hId A).dom ≡ range (hId A).nV.
--   * hId-cod≡range:       (hId A).cod ≡ range (hId A).nV.
--   * splitAt-cast:        splitAt m' (cast (cong₂ _+_ eq-m eq-n) i)
--                          commutes with splitAt m i.
--   * hId-nV≡len-flatten:  (hId A).nV ≡ length (flatten A).

module σ∘σ-proof (A B : ObjTerm) where
  private
    nA  = length (flatten A)
    nB  = length (flatten B)

    G = hSwap A B
    K = hSwap B A
    C = hComposeP G K
    R = hTensor (hId A) (hId B)  -- = hId (A ⊗₀ B)

    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph C
    module R = Hypergraph R
    module hCP = hComposeP-impl G K

    -- Key structural facts.
    cn≡0 : count-non K.dom ≡ 0
    cn≡0 = hSwap-count-non-dom B A

    C-nE≡0 : C.nE ≡ 0
    C-nE≡0 = refl   -- G.nE + K.nE = 0 + 0 = 0

    R-nE≡0 : R.nE ≡ 0
    R-nE≡0 = hId-nE (A ⊗₀ B)   -- induction on A ⊗₀ B

    -- Vertex count: C.nV = (nA + nB) + count-non K.dom.  R.nV = nA-id + nB-id.
    -- After reducing count-non via cn≡0, both are propositionally equal.
    eq-A : nA ≡ Hypergraph.nV (hId A)
    eq-A = sym (hId-nV≡len-flatten A)

    eq-B : nB ≡ Hypergraph.nV (hId B)
    eq-B = sym (hId-nV≡len-flatten B)

    eq-nV-GR : nA + nB ≡ R.nV
    eq-nV-GR = cong₂ _+_ eq-A eq-B

  ------------------------------------------------------------------------------
  -- Vertex bijection.

  -- C.nV = G.nV + count-non K.dom = (nA + nB) + count-non K.dom.
  -- We split v by splitAt G.nV = splitAt (nA + nB), with the K-pruned
  -- side absurd (cn≡0).
  φ : Fin C.nV → Fin R.nV
  φ v with splitAt G.nV v
  ... | inj₁ i = cast eq-nV-GR i
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ⁻¹ : Fin R.nV → Fin C.nV
  φ⁻¹ i = cast (sym eq-nV-GR) i ↑ˡ count-non K.dom

  open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; cast-is-id; cast-trans)

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt G.nV v in eq
  ... | inj₁ i =
    -- φ⁻¹ (cast eq-nV-GR i) = cast (sym eq-nV-GR) (cast eq-nV-GR i) ↑ˡ _
    --                      = i ↑ˡ _  (by cast-is-id + cast-trans)
    --                      = v  (by splitAt⁻¹-↑ˡ eq)
    trans (cong (_↑ˡ count-non K.dom)
                (trans (cast-trans eq-nV-GR (sym eq-nV-GR) i)
                       (cast-is-id (trans eq-nV-GR (sym eq-nV-GR)) i)))
          (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i
  φ-rght i
    rewrite splitAt-↑ˡ G.nV (cast (sym eq-nV-GR) i) (count-non K.dom)
    = trans (cast-trans (sym eq-nV-GR) eq-nV-GR i)
            (cast-is-id (trans (sym eq-nV-GR) eq-nV-GR) i)

  ------------------------------------------------------------------------------
  -- Edge bijection: both sides have no edges. All absurd.

  absurd-CE : ∀ {ℓ} {X : Set ℓ} → Fin C.nE → X
  absurd-CE e = ⊥-elim (Fin-zero-absurd C-nE≡0 e)

  absurd-RE : ∀ {ℓ} {X : Set ℓ} → Fin R.nE → X
  absurd-RE e = ⊥-elim (Fin-zero-absurd R-nE≡0 e)

  ψ : Fin C.nE → Fin R.nE
  ψ e = absurd-CE e

  ψ⁻¹ : Fin R.nE → Fin C.nE
  ψ⁻¹ e = absurd-RE e

  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e = absurd-CE e

  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e = absurd-RE e

  ------------------------------------------------------------------------------
  -- Label preservation.
  --
  -- For v with splitAt G.nV v = inj₁ i:
  --   C.vlab v = G.vlab i = (hSwap A B).vlab i
  --            = [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt nA i)
  --   R.vlab (φ v) = R.vlab (cast eq-nV-GR i)
  --                = [ (hId A).vlab , (hId B).vlab ]′
  --                     (splitAt (hId A).nV (cast eq-nV-GR i))
  -- Using `splitAt-cast` we relate splitAt (hId A).nV (cast _ i) to
  -- `splitAt nA i` with casts on each branch. Then `hId-vlab-lookup`
  -- on each branch closes the gap.

  ------------------------------------------------------------------------------
  -- Label preservation. For v with splitAt G.nV v = inj₁ i:
  --   C.vlab v = G.vlab i
  --            = [ lookup (flatten A), lookup (flatten B) ]′ (splitAt nA i)
  --   R.vlab (φ v) = R.vlab (cast _ i)
  --                = [ (hId A).vlab, (hId B).vlab ]′ (splitAt (hId A).nV (cast _ i))
  -- Using `splitAt-cast` the latter's splitAt reduces to
  --   [ inj₁ ∘ cast eq-A , inj₂ ∘ cast eq-B ]′ (splitAt nA i).
  -- Then `hId-vlab-lookup` on each branch + `cast-trans` + `cast-is-id`
  -- collapses each side to `lookup (flatten _) a` or `lookup (flatten _) b`.

  -- Transport (hId A).vlab (cast eq-A a) to G's `lookup (flatten A) a`.
  -- Uses hId-vlab-lookup + cast-trans + cast-is-id.
  vlab-via-hId
    : ∀ (X : ObjTerm) (a : Fin (length (flatten X)))
    → Hypergraph.vlab (hId X)
        (cast (sym (hId-nV≡len-flatten X)) a)
    ≡ lookup (flatten X) a
  vlab-via-hId X a =
    trans (hId-vlab-lookup X (cast (sym (hId-nV≡len-flatten X)) a))
    (cong (lookup (flatten X))
      (trans (cast-trans (sym (hId-nV≡len-flatten X)) (hId-nV≡len-flatten X) a)
             (cast-is-id (trans (sym (hId-nV≡len-flatten X)) (hId-nV≡len-flatten X)) a)))

  φ-lab-done : ∀ v → R.vlab (φ v) ≡ C.vlab v
  φ-lab-done v with splitAt G.nV v in eq
  ... | inj₁ i = body
    where
      -- R.vlab (cast _ i): first splitAt (hId A).nV on it, which via
      -- splitAt-cast reduces to cases on splitAt nA i.
      body : R.vlab (cast eq-nV-GR i) ≡ G.vlab i
      body
        rewrite splitAt-cast {nA} {Hypergraph.nV (hId A)}
                             {nB} {Hypergraph.nV (hId B)}
                             eq-A eq-B i
        with splitAt nA i
      ... | inj₁ a = vlab-via-hId A a
      ... | inj₂ b = vlab-via-hId B b
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  ------------------------------------------------------------------------------
  -- φ-dom, φ-cod: list-wise chase through `cast` + `inject+` / `raise` +
  -- `hId-dom≡range` / `hId-cod≡range`.
  --
  -- map φ C.dom  = map (cast eq-nV-GR) G.dom  (since φ ∘ injL = cast eq-nV-GR).
  -- G.dom        = map (inject+ nB) (range nA) ++ map (raise nA) (range nB).
  -- Pushing cast through inject+/raise via `cast-inject+-cong₂` /
  -- `cast-raise-cong₂` yields
  --   map (inject+ (hId B).nV) (map (cast eq-A) (range nA))
  -- ++ map (raise (hId A).nV)  (map (cast eq-B) (range nB))
  -- where `map (cast eq-A) (range nA) ≡ range (hId A).nV ≡ (hId A).dom`
  -- via `map-cast-range` + `hId-dom≡range`.

  open import Data.List using (_++_)
  open import Data.List.Properties using (map-++; map-∘; map-cong; map-id)
  open import Data.Fin.Properties renaming (cast-is-id to Fin-cast-is-id)

  private
    -- φ collapses on the injL side to `cast eq-nV-GR`.
    φ-injL-red : ∀ (x : Fin G.nV) → φ (hCP.injL x) ≡ cast eq-nV-GR x
    φ-injL-red x
      rewrite splitAt-↑ˡ G.nV x (count-non K.dom) = refl

    -- List-wise version: map φ C.dom ≡ map (cast eq-nV-GR) G.dom.
    map-φ-injL : map φ C.dom ≡ map (cast eq-nV-GR) G.dom
    map-φ-injL =
      trans (sym (map-∘ G.dom))
            (map-cong φ-injL-red G.dom)

    -- List-wise version for C.cod = map hCP.remapP K.cod.
    -- We need a map-via-remapP analog that collapses on the K-dom-covers
    -- case. Since K.dom covers and K.cod ≡ K.dom (for hSwap-like K's
    -- with dom=cod? not in general for hSwap — here we DO NOT have
    -- K.cod ≡ K.dom; hSwap B A has cod ≠ dom). TODO.

  φ-dom : R.dom ≡ map φ C.dom
  φ-dom = sym
    (trans map-φ-injL
    -- map (cast _) (map injL nA ++ map raise nB) = map (cast ∘ injL) nA ++ map (cast ∘ raise) nB
    (trans (map-++ (cast eq-nV-GR)
                   (map (_↑ˡ nB) (range nA))
                   (map (nA ↑ʳ_) (range nB)))
    -- Push cast through inject+ on LHS, raise on RHS.
    (cong₂ _++_
      -- First half: map (cast ∘ (_↑ˡ nB)) (range nA) = map (_↑ˡ (hId B).nV) (map (cast eq-A) (range nA))
      (trans (sym (map-∘ (range nA)))
      (trans (map-cong (cast-inject+-cong₂ eq-A eq-B) (range nA))
      (trans (map-∘ (range nA))
             (cong (map (_↑ˡ Hypergraph.nV (hId B)))
                   (trans (map-cast-range eq-A) (sym (hId-dom≡range A)))))))
      -- Second half: map (cast ∘ (nA ↑ʳ_)) (range nB) = map ((hId A).nV ↑ʳ_) (map (cast eq-B) (range nB))
      (trans (sym (map-∘ (range nB)))
      (trans (map-cong (cast-raise-cong₂ eq-A eq-B) (range nB))
      (trans (map-∘ (range nB))
             (cong (map (Hypergraph.nV (hId A) ↑ʳ_))
                   (trans (map-cast-range eq-B) (sym (hId-dom≡range B))))))))))

  ------------------------------------------------------------------------------
  -- φ-cod: similar shape to φ-dom, but C.cod goes through `remapP`
  -- rather than the simpler `injL`. For the hSwap B A source, each
  -- element of K.cod belongs to K.dom at a specific position, so
  -- `remapP` reduces via `classify-lookup-Unique` to
  --   `inject+ c (lookup-cod (position-in-K.dom))`.
  --
  -- The bookkeeping is:
  --   * raise nB x ∈ K.cod at pos x (x : Fin nA) lives in K.dom at pos (nB + x).
  --   * inject+ nA y ∈ K.cod at pos (nA + y) lives in K.dom at pos y.
  --   * Then `lookup-cod` into G.cod at those positions recovers
  --     G.cod's own structure — yielding `inject+ nB x` / `raise nA y`.
  --
  -- We isolate the two reductions as postulated helpers; once proved,
  -- φ-cod follows the exact same map-arithmetic as φ-dom.
  --
  -- Proof strategy for both:
  --   1. Construct `v∈K-dom` explicitly:
  --      - raise nB x ∈ K.dom
  --          = ∈-++⁺ʳ (map (inject+ nA) (range nB))
  --                   (∈-map⁺ (raise nB) (range-covers nA x))
  --      - inject+ nA y ∈ K.dom
  --          = ∈-++⁺ˡ (∈-map⁺ (inject+ nA) (range-covers nB y))
  --   2. Let `j = index v∈K-dom : Fin (length K.dom)`.
  --      By `classify-lookup-Unique K.dom (hSwap-dom-Unique B A) j`
  --      combined with `lookup-index v∈K-dom : lookup K.dom j ≡ v`
  --      (via `cong (classify K.dom) (sym lookup-index)` + trans), we get
  --          classify K.dom v ≡ inj₁ j.
  --   3. Apply `remap-inj₁` to get
  --          remapP v ≡ inject+ c (lookup-cod j).
  --   4. Prove `lookup-cod j ≡ inject+ nB x` (resp. `raise nA y`).
  --      `lookup-cod j = lookup G.cod (cast dom-cod-len j)`. For G.cod's
  --      ++ structure (for G = hSwap A B), at "position nB + x" we get
  --      `inject+ nB x`. The position-matching uses `index (∈-++⁺ʳ ...)
  --      ≡ cast (length-++) (raise (length first) (index rest))` via a
  --      stdlib lemma (or ad-hoc chain of `lookup-++-rai` / `lookup-map`
  --      reductions).
  --
  -- Steps 1–3 (classify → remap-inj₁) are clean; step 4 (lookup-cod)
  -- is the bottleneck. We implement steps 1–3 as a reusable private
  -- helper `remapP-via-member` that reduces the two goals to just
  -- `lookup-cod (index v∈K-dom) ≡ <expected-G.cod-value>`.

  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Membership.Propositional.Properties
    using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
  open import Data.List.Relation.Unary.Any using (index)
  open import Data.List.Relation.Unary.Any.Properties using (lookup-index)

  private
    K-unique : Unique K.dom
    K-unique = hSwap-dom-Unique B A

    -- Given a membership witness v∈K-dom, `remapP v` collapses to
    -- `lookup-cod (index v∈K-dom) ↑ˡ c`.
    remapP-via-member
      : ∀ {v : Fin K.nV} (v∈K-dom : v ∈ K.dom)
      → hCP.remapP v ≡ hCP.lookup-cod (index v∈K-dom) ↑ˡ count-non K.dom
    remapP-via-member {v} v∈K-dom =
      remap-inj₁ K.dom hCP.lookup-cod v (index v∈K-dom) classify-eq
      where
        -- `lookup-index v∈K-dom : v ≡ lookup K.dom (index v∈K-dom)`
        -- (because `_∈_` uses the `(v ≡_)` predicate).
        classify-eq : classify K.dom v ≡ inj₁ (index v∈K-dom)
        classify-eq = trans (cong (classify K.dom) (lookup-index v∈K-dom))
                            (classify-lookup-Unique K.dom K-unique (index v∈K-dom))

  -- Step 4: discharge the `lookup-cod` obligations via a "mirror
  -- witness" in G.cod + `toℕ-injective`. Each side's index has the
  -- same toℕ value (computed via `toℕ-index-++⁺{ˡ,ʳ}` +
  -- `∈-map⁺-index-cast` + `toℕ-index-range-covers`), so the Fin
  -- values are equal; then `lookup-index` on the G.cod witness
  -- gives the result.

  open import Data.Fin using (toℕ)
  open import Data.Fin.Properties using (toℕ-cast)
    renaming (toℕ-injective to Fin-toℕ-injective)
  open import Categories.APROP.Hypergraph.Prune using (∈-map⁺-index-cast)
  -- toℕ-index-++⁺ˡ / ʳ / range-covers are imported at the module top via
  -- `Categories.APROP.Hypergraph.Invariant sig`.

  -- For y : Fin nB, inject+ nA y is in the FIRST half of K.dom
  -- (map (inject+ nA) (range nB) ++ ...). Its G.cod mirror is
  -- raise nA y in the FIRST half of G.cod
  -- (map (raise nA) (range nB) ++ ...).
  lookup-cod-inject+-nA
    : ∀ (y : Fin nB)
    → hCP.lookup-cod (index (∈-++⁺ˡ {ys = map (nB ↑ʳ_) (range nA)}
                                    (∈-map⁺ (_↑ˡ nA) (range-covers nB y))))
    ≡ nA ↑ʳ y
  lookup-cod-inject+-nA y =
    -- Goal: lookup G.cod (cast _ k-idx) ≡ nA ↑ʳ y.
    -- Where k-idx : Fin (length K.dom).
    --
    -- Construct a mirror witness in G.cod: nA ↑ʳ y ∈ G.cod.
    -- Then lookup G.cod (index mirror) ≡ nA ↑ʳ y via lookup-index.
    -- Show cast _ k-idx ≡ index mirror via toℕ-injective.
    trans (cong (lookup G.cod) cast-k≡mirror)
          (sym (lookup-index mirror-in-G))
    where
      -- K-side witness.
      k-witness : y ↑ˡ nA ∈ K.dom
      k-witness = ∈-++⁺ˡ {ys = map (nB ↑ʳ_) (range nA)}
                         (∈-map⁺ (_↑ˡ nA) (range-covers nB y))

      -- G-side mirror witness.
      mirror-in-G : nA ↑ʳ y ∈ G.cod
      mirror-in-G = ∈-++⁺ˡ {ys = map (_↑ˡ nB) (range nA)}
                           (∈-map⁺ (nA ↑ʳ_) (range-covers nB y))

      k-idx : Fin (length K.dom)
      k-idx = index k-witness

      -- cast k-idx to Fin (length G.cod).
      g-idx : Fin (length G.cod)
      g-idx = cast hCP.dom-cod-len k-idx

      -- Both `g-idx` and `index mirror-in-G` have toℕ ≡ toℕ y.
      k-side-toℕ : toℕ g-idx ≡ toℕ y
      k-side-toℕ = trans (toℕ-cast _ k-idx)
                    (trans (toℕ-index-++⁺ˡ (∈-map⁺ (_↑ˡ nA) (range-covers nB y)))
                    (trans (cong toℕ (∈-map⁺-index-cast (_↑ˡ nA)
                                                       (inject+-inj _)
                                                       (range-covers nB y)))
                    (trans (toℕ-cast _ _)
                           (toℕ-index-range-covers nB y))))

      g-side-toℕ : toℕ (index mirror-in-G) ≡ toℕ y
      g-side-toℕ = trans (toℕ-index-++⁺ˡ (∈-map⁺ (nA ↑ʳ_) (range-covers nB y)))
                   (trans (cong toℕ (∈-map⁺-index-cast (nA ↑ʳ_)
                                                       (raise-inj _)
                                                       (range-covers nB y)))
                   (trans (toℕ-cast _ _)
                          (toℕ-index-range-covers nB y)))

      cast-k≡mirror : g-idx ≡ index mirror-in-G
      cast-k≡mirror = Fin-toℕ-injective (trans k-side-toℕ (sym g-side-toℕ))

  -- Analogous for raise nB x ∈ K.cod (second half of K.dom → second
  -- half of G.cod).
  lookup-cod-raise-nB
    : ∀ (x : Fin nA)
    → hCP.lookup-cod (index (∈-++⁺ʳ (map (_↑ˡ nA) (range nB))
                                    (∈-map⁺ (nB ↑ʳ_) (range-covers nA x))))
    ≡ x ↑ˡ nB
  lookup-cod-raise-nB x =
    trans (cong (lookup G.cod) cast-k≡mirror)
          (sym (lookup-index mirror-in-G))
    where
      k-witness : nB ↑ʳ x ∈ K.dom
      k-witness = ∈-++⁺ʳ (map (_↑ˡ nA) (range nB))
                         (∈-map⁺ (nB ↑ʳ_) (range-covers nA x))

      mirror-in-G : x ↑ˡ nB ∈ G.cod
      mirror-in-G = ∈-++⁺ʳ (map (nA ↑ʳ_) (range nB))
                           (∈-map⁺ (_↑ˡ nB) (range-covers nA x))

      k-idx : Fin (length K.dom)
      k-idx = index k-witness

      g-idx : Fin (length G.cod)
      g-idx = cast hCP.dom-cod-len k-idx

      -- Both indices have toℕ ≡ nB + toℕ x.
      open import Data.List.Properties using (length-map)

      k-side-toℕ : toℕ g-idx ≡ length (map (_↑ˡ nA) (range nB)) + toℕ x
      k-side-toℕ = trans (toℕ-cast _ k-idx)
                    (trans (toℕ-index-++⁺ʳ (map (_↑ˡ nA) (range nB))
                              (∈-map⁺ (nB ↑ʳ_) (range-covers nA x)))
                    (cong (length (map (_↑ˡ nA) (range nB)) +_)
                          (trans (cong toℕ (∈-map⁺-index-cast (nB ↑ʳ_)
                                                              (raise-inj _)
                                                              (range-covers nA x)))
                          (trans (toℕ-cast _ _)
                                 (toℕ-index-range-covers nA x)))))

      g-side-toℕ : toℕ (index mirror-in-G) ≡ length (map (nA ↑ʳ_) (range nB)) + toℕ x
      g-side-toℕ = trans (toℕ-index-++⁺ʳ (map (nA ↑ʳ_) (range nB))
                           (∈-map⁺ (_↑ˡ nB) (range-covers nA x)))
                   (cong (length (map (nA ↑ʳ_) (range nB)) +_)
                         (trans (cong toℕ (∈-map⁺-index-cast (_↑ˡ nB)
                                                             (inject+-inj _)
                                                             (range-covers nA x)))
                         (trans (toℕ-cast _ _)
                                (toℕ-index-range-covers nA x))))

      -- The two lengths coincide (both nB).
      len-eq : length (map (_↑ˡ nA) (range nB)) ≡ length (map (nA ↑ʳ_) (range nB))
      len-eq = trans (length-map (_↑ˡ nA) (range nB))
                     (sym (length-map (nA ↑ʳ_) (range nB)))

      cast-k≡mirror : g-idx ≡ index mirror-in-G
      cast-k≡mirror = Fin-toℕ-injective
        (trans k-side-toℕ (trans (cong (_+ toℕ x) len-eq) (sym g-side-toℕ)))

  remapP-kcod-raise-nB
    : ∀ (x : Fin nA)
    → hCP.remapP (nB ↑ʳ x) ≡ (x ↑ˡ nB) ↑ˡ count-non K.dom
  remapP-kcod-raise-nB x =
    trans (remapP-via-member v∈K-dom)
          (cong (_↑ˡ count-non K.dom) (lookup-cod-raise-nB x))
    where
      v∈K-dom : nB ↑ʳ x ∈ K.dom
      v∈K-dom = ∈-++⁺ʳ (map (_↑ˡ nA) (range nB))
                       (∈-map⁺ (nB ↑ʳ_) (range-covers nA x))

  remapP-kcod-inject+-nA
    : ∀ (y : Fin nB)
    → hCP.remapP (y ↑ˡ nA) ≡ (nA ↑ʳ y) ↑ˡ count-non K.dom
  remapP-kcod-inject+-nA y =
    trans (remapP-via-member v∈K-dom)
          (cong (_↑ˡ count-non K.dom) (lookup-cod-inject+-nA y))
    where
      v∈K-dom : y ↑ˡ nA ∈ K.dom
      v∈K-dom = ∈-++⁺ˡ {ys = map (nB ↑ʳ_) (range nA)}
                      (∈-map⁺ (_↑ˡ nA) (range-covers nB y))

  -- With the per-element reductions, φ-cod is a direct map-chase
  -- analogous to φ-dom.
  φ-cod : R.cod ≡ map φ C.cod
  φ-cod = sym
    (trans
      -- Unfold C.cod = map remapP K.cod.  K.cod = raise-half ++ inject+-half.
      (trans (sym (map-∘ K.cod))
             (map-++ (λ v → φ (hCP.remapP v))
                     (map (nB ↑ʳ_) (range nA))
                     (map (_↑ˡ nA) (range nB))))
    -- Left half: nB ↑ʳ x ↦ cast eq-A x ↑ˡ (hId B).nV after all reductions.
    (cong₂ _++_
      (trans (sym (map-∘ (range nA)))
      (trans (map-cong
                (λ x → trans (cong φ (remapP-kcod-raise-nB x))
                             (φ-injL-red (x ↑ˡ nB)))
                (range nA))
      (trans (map-cong (cast-inject+-cong₂ eq-A eq-B) (range nA))
      (trans (map-∘ (range nA))
             (cong (map (_↑ˡ Hypergraph.nV (hId B)))
                   (trans (map-cast-range eq-A) (sym (hId-cod≡range A))))))))
      -- Right half: y ↑ˡ nA ↦ (hId A).nV ↑ʳ cast eq-B y.
      (trans (sym (map-∘ (range nB)))
      (trans (map-cong
                (λ y → trans (cong φ (remapP-kcod-inject+-nA y))
                             (φ-injL-red (nA ↑ʳ y)))
                (range nB))
      (trans (map-cong (cast-raise-cong₂ eq-A eq-B) (range nB))
      (trans (map-∘ (range nB))
             (cong (map (Hypergraph.nV (hId A) ↑ʳ_))
                   (trans (map-cast-range eq-B) (sym (hId-cod≡range B))))))))))

  ψ-ein  : ∀ e → R.ein  (ψ e) ≡ map φ (C.ein  e)
  ψ-ein  e = absurd-CE e
  ψ-eout : ∀ e → R.eout (ψ e) ≡ map φ (C.eout e)
  ψ-eout e = absurd-CE e

  atom-ein  : ∀ e → map R.vlab (R.ein  (ψ e)) ≡ map C.vlab (C.ein  e)
  atom-ein  e = absurd-CE e
  atom-eout : ∀ e → map R.vlab (R.eout (ψ e)) ≡ map C.vlab (C.eout e)
  atom-eout e = absurd-CE e

  ψ-elab
    : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (R.elab (ψ e))
          ≡ C.elab e
  ψ-elab e = absurd-CE e

  ------------------------------------------------------------------------------
  -- Assembled iso.

  σ∘σ-iso : C ≅ᴴ R
  σ∘σ-iso = record
    { φ         = φ
    ; φ⁻¹       = φ⁻¹
    ; φ-left    = φ-left
    ; φ-rght    = φ-rght
    ; ψ         = ψ
    ; ψ⁻¹       = ψ⁻¹
    ; ψ-left    = ψ-left
    ; ψ-rght    = ψ-rght
    ; φ-lab     = φ-lab-done
    ; ψ-ein     = ψ-ein
    ; ψ-eout    = ψ-eout
    ; φ-dom     = φ-dom
    ; φ-cod     = φ-cod
    ; atom-ein  = atom-ein
    ; atom-eout = atom-eout
    ; ψ-elab    = ψ-elab
    }

σ∘σ-sound : ∀ {A B} → ⟪ σ {B} {A} ∘ σ {A} {B} ⟫ ≅ᴴ ⟪ id {A ⊗₀ B} ⟫
σ∘σ-sound {A} {B} = σ∘σ-proof.σ∘σ-iso A B

--------------------------------------------------------------------------------
-- Remaining axioms (8): ρ-nat, α-comm, σ-nat, triangle, pentagon,
-- hexagon, assoc, ⊗-∘-dist.  Each is postulated as a focused lemma
-- per the `≈Term` constructor it discharges.  Together they replace
-- the omnibus `soundness-axiom` catch-all in `Soundness.agda`,
-- giving each unfinished axiom its own named stub for future work.
--
-- Complexity classification (from TODO.org Step 6):
--
--   ρ-nat, α-comm: analogous to λ-nat (done in Step 4), but with
--     added `subst₂` bookkeeping because ⟪ρ⇒⟫ / ⟪α⇒⟫ carry a
--     `++-identityʳ` / `++-assoc` cast.  Conceptually reducible to
--     Step 1–5 machinery; left as an exercise.
--
--   σ-nat (`σ∘(f⊗g) ≈ (g⊗f)∘σ`): like σ∘σ-proof, classify-based
--     bijection against (hSwap C D).dom.
--
--   triangle: α/λ/ρ coherence on (A⊗unit)⊗B.  Should chain via
--     Step-2 helpers + hComposeP-subst-both.
--
--   pentagon: five-α coherence.  Needs triple-classify bijection
--     or a tactic.
--
--   hexagon: three-α/three-σ coherence.
--
--   assoc: (h∘g)∘f ≈ h∘(g∘f).  Triple-classify; vertex counts
--     match modulo `+`-associativity.
--
--   ⊗-∘-dist: (f₁⊗g₁)∘(f₂⊗g₂) ≈ (f₁∘f₂)⊗(g₁∘g₂).  Tensor/compose
--     interchange; cross-reasoning on vertex reshuffle.
--
-- Per TODO.org, each is estimated at 5–10 h of custom structural
-- proof; deferred to a future session or the Phase-4 `smcat`
-- reflection tactic.

-- α-comm-sound: proved constructively in `AlphaCommSound`.
-- Dispatched in Soundness.agda by importing both this file and
-- AlphaCommSound (not re-exported here to avoid a circular import;
-- AlphaCommSound depends on `hCompose-hId-R-iso-generic` etc. which live here).

postulate
  -- ρ⇒ ∘ f⊗id ≈ f ∘ ρ⇒  (unitorʳ-commute)
  ρ⇒∘f⊗id≈f∘ρ⇒-sound
    : ∀ {A B} {f : HomTerm A B}
    → ⟪ ρ⇒ {B} ∘ f ⊗₁ id {unit} ⟫ ≅ᴴ ⟪ f ∘ ρ⇒ {A} ⟫

  -- NOTE: `triangle-sound` and `α-comm-sound` are now proved
  -- constructively in their own modules:
  --   * `Categories.APROP.Hypergraph.Triangle`
  --   * `Categories.APROP.Hypergraph.AlphaCommSound`
  -- Soundness.agda imports them from there directly, so no postulates
  -- are needed in this module.

  -- pentagon: id⊗α⇒ ∘ α⇒ ∘ α⇒⊗id ≈ α⇒ ∘ α⇒{A⊗B,C,D}
  pentagon-sound
    : ∀ {A B C D}
    → ⟪ id {A} ⊗₁ α⇒ {B} {C} {D} ∘ α⇒ {A} {B ⊗₀ C} {D} ∘ α⇒ {A} {B} {C} ⊗₁ id {D} ⟫
    ≅ᴴ ⟪ α⇒ {A} {B} {C ⊗₀ D} ∘ α⇒ {A ⊗₀ B} {C} {D} ⟫

  -- NOTE: `σ∘[f⊗g]≈[g⊗f]∘σ-sound` has been moved to `Hypergraph.SigmaNat`.
  -- That module constructs the iso as a record with explicit φ / ψ
  -- bijections (vertex/edge swap permutations) and postulates the 7
  -- remaining coherence fields internally for future discharge.
  -- Soundness.agda imports it from SigmaNat directly.

  -- hexagon: id⊗σ ∘ α⇒ ∘ σ⊗id ≈ α⇒ ∘ σ ∘ α⇒ (symmetric hexagon)
  hexagon-sound
    : ∀ {A B C}
    → ⟪ id {B} ⊗₁ σ {A} {C} ∘ α⇒ {B} {A} {C} ∘ σ {A} {B} ⊗₁ id {C} ⟫
    ≅ᴴ ⟪ α⇒ {B} {C} {A} ∘ σ {A} {B ⊗₀ C} ∘ α⇒ {A} {B} {C} ⟫

  -- assoc: (h∘g)∘f ≈ h∘(g∘f)  (composition associativity)
  assoc-sound
    : ∀ {A B C D} {f : HomTerm A B} {g : HomTerm B C} {h : HomTerm C D}
    → ⟪ (h ∘ g) ∘ f ⟫ ≅ᴴ ⟪ h ∘ (g ∘ f) ⟫

  -- ⊗-∘-dist: (g∘f)⊗(g'∘f') ≈ (g⊗g')∘(f⊗f')  (tensor/compose interchange)
  ⊗-∘-dist-sound
    : ∀ {A B C A' B' C'}
        {f : HomTerm A B} {g : HomTerm B C}
        {f' : HomTerm A' B'} {g' : HomTerm B' C'}
    → ⟪ (g ∘ f) ⊗₁ (g' ∘ f') ⟫ ≅ᴴ ⟪ (g ⊗₁ g') ∘ (f ⊗₁ f') ⟫

--------------------------------------------------------------------------------
-- Dispatch: replace soundness-axiom calls that match these axioms
-- with the proved versions. (Soundness.agda will import this module
-- and use these lemmas in its per-axiom clauses.)
