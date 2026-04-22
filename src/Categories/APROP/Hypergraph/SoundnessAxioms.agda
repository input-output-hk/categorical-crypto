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
  using (FlatGen; flatten; hId; hTensor; hGen; hEmpty; hVar; hSwap; range)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig
open import Categories.APROP.Hypergraph.Invariant sig

open import Categories.APROP.Hypergraph.Prune
  using ( nonMem; count-non; AllIn; AllIn→count-non-zero
        ; classify; classify-lookup-Unique; remap; remap-inj₁)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt; cast)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise; cast-is-id)
open import Data.List using (List; []; _∷_; map; length; lookup; tabulate; allFin)
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

-- Scaffolding for the full proof:
module idˡ-proof {A B : ObjTerm} (f : HomTerm A B) where
  private
    G = ⟪ f ⟫
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
  φ⁻¹ i = inject+ (count-non K.dom) i

  ψ : Fin C.nE → Fin G.nE
  ψ e with splitAt G.nE e
  ... | inj₁ eG = eG
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ⁻¹ : Fin G.nE → Fin C.nE
  ψ⁻¹ e = inject+ K.nE e

  ------------------------------------------------------------------------------
  -- Bijection laws.

  open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt G.nV v in eq
  ... | inj₁ i = splitAt⁻¹-↑ˡ eq
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i
  φ-rght i rewrite splitAt-inject+ G.nV (count-non K.dom) i = refl

  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e with splitAt G.nE e in eq
  ... | inj₁ eG = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e rewrite splitAt-inject+ G.nE K.nE e = refl

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
    φ-injL : ∀ i → φ (inject+ (count-non K.dom) i) ≡ i
    φ-injL i rewrite splitAt-inject+ G.nV (count-non K.dom) i = refl

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
    ≡ inject+ (count-non K.dom) (hCP.lookup-cod j)
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
      map (λ j → inject+ (count-non K.dom) (hCP.lookup-cod j))
          (allFin (length K.dom))
        ≡⟨ map-∘ (allFin (length K.dom)) ⟩
      map (inject+ (count-non K.dom))
          (map hCP.lookup-cod (allFin (length K.dom)))
        ≡⟨ cong (map (inject+ (count-non K.dom))) (map-∘ (allFin (length K.dom))) ⟩
      map (inject+ (count-non K.dom))
          (map (lookup G.cod) (map (cast hCP.dom-cod-len) (allFin (length K.dom))))
        ≡⟨ cong (λ xs → map (inject+ (count-non K.dom)) (map (lookup G.cod) xs))
               (cast-allFin hCP.dom-cod-len) ⟩
      map (inject+ (count-non K.dom))
          (map (lookup G.cod) (allFin (length G.cod)))
        ≡⟨ cong (map (inject+ (count-non K.dom))) (map-lookup-allFin G.cod) ⟩
      map (inject+ (count-non K.dom)) G.cod
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

  idˡ-iso : C ≅ᴴ G
  idˡ-iso = record
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

-- Export idˡ proof.
idˡ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫
idˡ-sound f = idˡ-proof.idˡ-iso f

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

-- Helper: hTensor hEmpty (hId A) ≅ᴴ hId A.
--
-- hTensor hEmpty G has nV = 0 + G.nV = G.nV (def), vlab pointwise
-- identical to G (via splitAt 0 = inj₂), and dom/cod differ only by
-- `map (raise 0)` which reduces to identity on lists (raise 0 i = i
-- definitionally). The bijection is identity at the Fin level; the
-- record-field equalities are `refl` or `map-id`-based.

hTensor-hEmpty-hId-iso : ∀ (A : ObjTerm) → hTensor hEmpty (hId A) ≅ᴴ hId A
hTensor-hEmpty-hId-iso A = record
  { φ         = λ i → i
  ; φ⁻¹       = λ i → i
  ; φ-left    = λ _ → refl
  ; φ-rght    = λ _ → refl
  ; ψ         = absurd-E
  ; ψ⁻¹       = absurd-E
  ; ψ-left    = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  ; ψ-rght    = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  ; φ-lab     = λ _ → refl
  ; ψ-ein     = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  ; ψ-eout    = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  ; φ-dom     = dom-eq
  ; φ-cod     = cod-eq
  ; atom-ein  = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  ; atom-eout = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  ; ψ-elab    = λ e → ⊥-elim (Fin-zero-absurd (hId-nE A) e)
  }
  where
    open import Data.List.Properties using (map-id; map-cong)

    absurd-E : ∀ {ℓ} {X : Set ℓ} → Fin (Hypergraph.nE (hId A)) → X
    absurd-E e = ⊥-elim (Fin-zero-absurd (hId-nE A) e)

    -- `(hTensor hEmpty G).dom = [] ++ map (raise 0) G.dom = map (raise 0) G.dom`.
    -- And `raise 0 i = i` def, so `map (raise 0) xs ≡ xs` via map-cong + map-id.
    -- The outer `map id` from φ = id collapses via map-id.
    dom-eq : Hypergraph.dom (hId A)
           ≡ map (λ i → i) (Hypergraph.dom (hTensor hEmpty (hId A)))
    dom-eq = sym (trans (map-id (Hypergraph.dom (hTensor hEmpty (hId A))))
                        (trans (map-cong (λ _ → refl) (Hypergraph.dom (hId A)))
                               (map-id (Hypergraph.dom (hId A)))))

    cod-eq : Hypergraph.cod (hId A)
           ≡ map (λ i → i) (Hypergraph.cod (hTensor hEmpty (hId A)))
    cod-eq = sym (trans (map-id (Hypergraph.cod (hTensor hEmpty (hId A))))
                        (trans (map-cong (λ _ → refl) (Hypergraph.cod (hId A)))
                               (map-id (Hypergraph.cod (hId A)))))

λ⇐∘λ⇒-sound : ∀ {A} → ⟪ λ⇐ {A} ∘ λ⇒ {A} ⟫ ≅ᴴ ⟪ id {unit ⊗₀ A} ⟫
λ⇐∘λ⇒-sound {A} = trans-≅ᴴ (idˡ-sound (id {A})) (sym-≅ᴴ (hTensor-hEmpty-hId-iso A))

λ⇒∘λ⇐-sound : ∀ {A} → ⟪ λ⇒ {A} ∘ λ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫
λ⇒∘λ⇐-sound {A} = idˡ-sound (id {A})

--------------------------------------------------------------------------------
-- ρ⇐∘ρ⇒, ρ⇒∘ρ⇐, α⇐∘α⇒, α⇒∘α⇐ — all similar pattern: composition of two
-- hId-based constructions gives hId. The subst-wrapped cases (ρ, α) need
-- additional subst manipulation.

postulate
  ρ⇐∘ρ⇒-sound : ∀ {A} → ⟪ ρ⇐ {A} ∘ ρ⇒ {A} ⟫ ≅ᴴ ⟪ id {A ⊗₀ unit} ⟫
  ρ⇒∘ρ⇐-sound : ∀ {A} → ⟪ ρ⇒ {A} ∘ ρ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫

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
  φ⁻¹ i = inject+ (count-non K.dom) (cast (sym eq-nV-GR) i)

  open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; cast-is-id; cast-trans)

  φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
  φ-left v with splitAt G.nV v in eq
  ... | inj₁ i =
    -- φ⁻¹ (cast eq-nV-GR i) = inject+ _ (cast (sym eq-nV-GR) (cast eq-nV-GR i))
    --                      = inject+ _ i  (by cast-is-id + cast-trans)
    --                      = v  (by splitAt⁻¹-↑ˡ eq)
    trans (cong (inject+ (count-non K.dom))
                (trans (cast-trans eq-nV-GR (sym eq-nV-GR) i)
                       (cast-is-id (trans eq-nV-GR (sym eq-nV-GR)) i)))
          (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

  φ-rght : ∀ i → φ (φ⁻¹ i) ≡ i
  φ-rght i
    rewrite splitAt-inject+ G.nV (count-non K.dom) (cast (sym eq-nV-GR) i)
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
  open import Data.Fin.Properties using (splitAt-inject+) renaming (cast-is-id to Fin-cast-is-id)

  private
    -- φ collapses on the injL side to `cast eq-nV-GR`.
    φ-injL-red : ∀ (x : Fin G.nV) → φ (hCP.injL x) ≡ cast eq-nV-GR x
    φ-injL-red x
      rewrite splitAt-inject+ G.nV (count-non K.dom) x = refl

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
                   (map (inject+ nB) (range nA))
                   (map (raise nA) (range nB)))
    -- Push cast through inject+ on LHS, raise on RHS.
    (cong₂ _++_
      -- First half: map (cast ∘ inject+ nB) (range nA) = map (inject+ (hId B).nV) (map (cast eq-A) (range nA))
      (trans (sym (map-∘ (range nA)))
      (trans (map-cong (cast-inject+-cong₂ eq-A eq-B) (range nA))
      (trans (map-∘ (range nA))
             (cong (map (inject+ (Hypergraph.nV (hId B))))
                   (trans (map-cast-range eq-A) (sym (hId-dom≡range A)))))))
      -- Second half: map (cast ∘ raise nA) (range nB) = map (raise (hId A).nV) (map (cast eq-B) (range nB))
      (trans (sym (map-∘ (range nB)))
      (trans (map-cong (cast-raise-cong₂ eq-A eq-B) (range nB))
      (trans (map-∘ (range nB))
             (cong (map (raise (Hypergraph.nV (hId A))))
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
  postulate
    remapP-kcod-raise-nB
      : ∀ (x : Fin nA)
      → hCP.remapP (raise nB x) ≡ inject+ (count-non K.dom) (inject+ nB x)
    remapP-kcod-inject+-nA
      : ∀ (y : Fin nB)
      → hCP.remapP (inject+ nA y) ≡ inject+ (count-non K.dom) (raise nA y)

  -- With the per-element reductions, φ-cod is a direct map-chase
  -- analogous to φ-dom.
  φ-cod : R.cod ≡ map φ C.cod
  φ-cod = sym
    (trans
      -- Unfold C.cod = map remapP K.cod.  K.cod = raise-half ++ inject+-half.
      (trans (sym (map-∘ K.cod))
             (map-++ (λ v → φ (hCP.remapP v))
                     (map (raise nB) (range nA))
                     (map (inject+ nA) (range nB))))
    -- Left half: raise nB x ↦ inject+ (hId B).nV (cast eq-A x) after all reductions.
    (cong₂ _++_
      (trans (sym (map-∘ (range nA)))
      (trans (map-cong
                (λ x → trans (cong φ (remapP-kcod-raise-nB x))
                             (φ-injL-red (inject+ nB x)))
                (range nA))
      (trans (map-cong (cast-inject+-cong₂ eq-A eq-B) (range nA))
      (trans (map-∘ (range nA))
             (cong (map (inject+ (Hypergraph.nV (hId B))))
                   (trans (map-cast-range eq-A) (sym (hId-cod≡range A))))))))
      -- Right half: inject+ nA y ↦ raise (hId A).nV (cast eq-B y).
      (trans (sym (map-∘ (range nB)))
      (trans (map-cong
                (λ y → trans (cong φ (remapP-kcod-inject+-nA y))
                             (φ-injL-red (raise nA y)))
                (range nB))
      (trans (map-cong (cast-raise-cong₂ eq-A eq-B) (range nB))
      (trans (map-∘ (range nB))
             (cong (map (raise (Hypergraph.nV (hId A))))
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
-- Dispatch: replace soundness-axiom calls that match these axioms
-- with the proved versions. (Soundness.agda will import this module
-- and use these lemmas in its per-axiom clauses.)
