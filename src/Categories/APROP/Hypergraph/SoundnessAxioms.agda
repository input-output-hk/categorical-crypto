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
  using (FlatGen; flatten; hId; hTensor; hGen; hEmpty; hVar; hSwap)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.PrunedCompose sig
open import Categories.APROP.Hypergraph.Invariant sig

open import Categories.APROP.Hypergraph.Prune
  using (nonMem; count-non; AllIn; AllIn→count-non-zero)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; inject+; raise; splitAt)
open import Data.Fin.Properties using (splitAt-inject+; splitAt-raise)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using ([_,_]′; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

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
  -- Since K = hId B, K.cod is structured. For remapP on K.cod, every
  -- K.cod vertex is in K.dom (hId-cod-covers), so remapP sends to
  -- inject+ of lookup-cod. Then φ strips to the G-side.
  -- Tricky — requires `classify (hId A).dom v ≡ inj₁ (...)` reasoning
  -- and a lemma about G.cod recovery. Postulated.
  postulate
    φ-cod : G.cod ≡ map φ C.cod

  ------------------------------------------------------------------------------
  -- Atom-list equalities.
  --
  -- atom-ein e : map G.vlab (G.ein (ψ e)) ≡ map C.vlab (C.ein e).
  -- Follows from ψ-ein + φ-lab.

  atom-ein : ∀ e → map G.vlab (G.ein (ψ e)) ≡ map C.vlab (Hypergraph.ein C e)
  atom-ein e =
    trans (cong (map G.vlab) (ψ-ein e))
    (trans (sym (map-∘ (Hypergraph.ein C e)))
           (map-cong φ-lab (Hypergraph.ein C e)))

  atom-eout : ∀ e → map G.vlab (G.eout (ψ e)) ≡ map C.vlab (Hypergraph.eout C e)
  atom-eout e =
    trans (cong (map G.vlab) (ψ-eout e))
    (trans (sym (map-∘ (Hypergraph.eout C e)))
           (map-cong φ-lab (Hypergraph.eout C e)))

  ------------------------------------------------------------------------------
  -- Edge label compatibility.
  --
  -- subst₂ FlatGen (atom-ein e) (atom-eout e) (G.elab (ψ e)) ≡ C.elab e.
  -- For e = inj₁ eG: C.elab e = subst₂ ... (G.elab eG) via elab-c-inj₁,
  -- so the two subst₂'s of G.elab eG with different proof chains give
  -- the same result (subst₂-uniqueness). For inj₂ eK: absurd.
  -- Postulated for now — requires unfolding the elab-c-inj₁ reduction
  -- and chaining the subst₂ proofs.
  postulate
    ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (G.elab (ψ e))
                 ≡ Hypergraph.elab C e

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
-- The iso construction requires showing that `hSwap` composed with its
-- reverse gives identity. Non-trivial: involves reasoning about remapP
-- on hSwap.dom = map injL range-A ++ map injR range-B.

postulate
  σ∘σ-sound : ∀ {A B} → ⟪ σ {B} {A} ∘ σ {A} {B} ⟫ ≅ᴴ ⟪ id {A ⊗₀ B} ⟫

--------------------------------------------------------------------------------
-- Dispatch: replace soundness-axiom calls that match these axioms
-- with the proved versions. (Soundness.agda will import this module
-- and use these lemmas in its per-axiom clauses.)
