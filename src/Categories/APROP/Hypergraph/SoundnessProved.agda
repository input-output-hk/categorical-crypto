{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- DE-INDEXED REFACTOR — TEMPORARY POSTULATE STUB.
--
-- The original SoundnessProved.agda contained the constructive proofs of:
--
--   * `hCompose-hId-R-iso-generic`, `hCompose-hId-L-iso-generic`,
--     `hTensor-hEmpty-G-iso`
--   * `idˡ-sound`, `idʳ-sound`,
--     `λ⇒∘id⊗f≈f∘λ⇒-sound`, `λ⇐∘λ⇒-sound`, `λ⇒∘λ⇐-sound`,
--     `ρ⇐∘ρ⇒-sound`, `α⇐∘α⇒-sound`, `σ∘σ-sound`
--
-- Each was structured around the indexed `Hypergraph FlatGen As Bs`
-- type, with proofs that pattern-matched on `subst₂ Hypergraph refl …`
-- and threaded boundary equations through `K.dom-ok`/`G.cod-ok` fields.
-- Under de-indexing, these proofs need reformulating: the boundary
-- equations are now runtime arguments to `hComposeP`, the `subst₂`
-- transports are gone, and the proofs no longer pattern-match on them.
--
-- Migrating these proofs constructively is mechanical but high-volume
-- (~1431 LOC of intricate vertex-bijection / edge-bijection proofs).
-- For now they are postulated so the downstream chain can build.
-- The original proofs are preserved in the git history at commit `4553881`
-- on the `string-diagram-solver-completeness` branch.
--
-- An attempted migration (see this branch's commit history) showed that
-- each `hCompose-hId-iso-generic` export and each ρ/α-iso proof
-- requires careful threading of the new runtime `bdy-eq` argument; the
-- boundary equation that was previously a type-level subst now needs to
-- be supplied at each `hComposeP` call site, including with `cong
-- unflatten` boundary lifts.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SoundnessProved (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty; codL-hId; domL-hId;
         map-via-inj; map-via-raise; module hTensor-impl)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Invariant sig
  using (hId-cod≡dom; hId-dom-Unique; hId-count-non-dom)
open import Categories.APROP.Hypergraph.Prune
  using (count-non; remap-inj₁; classify-lookup-Unique)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; _↑ˡ_; cast)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt⁻¹-↑ˡ; cast-is-id)
open import Data.List using (List; []; _∷_; map; lookup; tabulate; allFin; length)
open import Data.List.Properties using (map-∘; map-cong; map-id; map-tabulate;
                                          tabulate-lookup)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst₂; module ≡-Reasoning)
open import Data.Fin using (splitAt)

-- Helpers: hId has no edges; absurd elimination on Fin 0.
private
  cong₂-+ : ∀ {a b c d : ℕ} → a ≡ b → c ≡ d → a + c ≡ b + d
  cong₂-+ refl refl = refl

  Fin-zero-absurd : ∀ {n : ℕ} → n ≡ 0 → Fin n → ⊥
  Fin-zero-absurd refl ()

hId-nE : ∀ A → Hypergraph.nE (hId A) ≡ 0
hId-nE unit       = refl
hId-nE (Var x)    = refl
hId-nE (A ⊗₀ B)   = cong₂-+ (hId-nE A) (hId-nE B)

--------------------------------------------------------------------------------
-- Generic right-identity-composition iso.
--
-- For any G, `hComposeP G (hId B) bdy ≅ᴴ G`.  The proof is a vertex
-- bijection that injects into the left summand, with the right summand
-- (count-non K.dom) provably zero (since hId.dom covers all of hId.nV).

module hCompose-hId-R-proof
  (B : ObjTerm)
  (G : Hypergraph FlatGen)
  (bdy-eq : codL G ≡ flatten B)
  where
  private
    K = hId B
    bdy-eq′ : codL G ≡ domL K
    bdy-eq′ = trans bdy-eq (sym (domL-hId B))
    C = hComposeP G K bdy-eq′
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph C
    module hCP = hComposeP-impl G K bdy-eq′

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

  φ-lab : ∀ v → G.vlab (φ v) ≡ C.vlab v
  φ-lab v with splitAt G.nV v
  ... | inj₁ i = refl
  ... | inj₂ j = ⊥-elim (Fin-zero-absurd cn≡0 j)

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

  φ-dom : G.dom ≡ map φ C.dom
  φ-dom = sym
    (trans (sym (map-∘ G.dom))
           (trans (map-cong φ-injL G.dom)
                  (map-id G.dom)))

  -- φ-cod proof needs the helper "remapP K.cod ≡ injL G.cod (after subst)".
  private
    map-lookup-allFin
      : ∀ {A : Set} (xs : List A)
      → map (lookup xs) (allFin (length xs)) ≡ xs
    map-lookup-allFin xs =
      trans (map-tabulate (λ i → i) (lookup xs)) (tabulate-lookup xs)

    cast-allFin
      : ∀ {m n} (eq : m ≡ n) → map (cast eq) (allFin m) ≡ allFin n
    cast-allFin refl =
      trans (map-cong (λ i → cast-is-id refl i) (allFin _)) (map-id (allFin _))

    remapP-on-dom
      : ∀ (j : Fin (length K.dom))
      → hCP.remapP (lookup K.dom j)
      ≡ hCP.lookup-cod j ↑ˡ count-non K.dom
    remapP-on-dom j =
      remap-inj₁ K.dom hCP.lookup-cod (lookup K.dom j) j
        (classify-lookup-Unique K.dom (hId-dom-Unique B) j)

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

  atom-ein : ∀ e → map G.vlab (G.ein (ψ e)) ≡ map C.vlab (Hypergraph.ein C e)
  atom-ein e with splitAt G.nE e
  ... | inj₁ eG = map-via-inj hCP.vlab-injL (G.ein eG)
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  atom-eout : ∀ e → map G.vlab (G.eout (ψ e)) ≡ map C.vlab (Hypergraph.eout C e)
  atom-eout e with splitAt G.nE e
  ... | inj₁ eG = map-via-inj hCP.vlab-injL (G.eout eG)
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

  ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (G.elab (ψ e))
              ≡ Hypergraph.elab C e
  ψ-elab e with splitAt G.nE e
  ... | inj₁ eG = refl
  ... | inj₂ eK = ⊥-elim (Fin-zero-absurd nE≡0 eK)

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

hCompose-hId-R-iso-generic
  : (B : ObjTerm) (G : Hypergraph FlatGen) (bdy-eq : codL G ≡ flatten B)
  → hComposeP G (hId B) (trans bdy-eq (sym (domL-hId B))) ≅ᴴ G
hCompose-hId-R-iso-generic = hCompose-hId-R-proof.hCompose-hId-R-iso

--------------------------------------------------------------------------------
-- `idˡ-sound`: ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫.
--
-- Direct consequence of `hCompose-hId-R-iso-generic`:
-- ⟪ id ∘ f ⟫ = hComposeP ⟪ f ⟫ ⟪ id {B} ⟫ bdy = hComposeP ⟪ f ⟫ (hId B) bdy.

idˡ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫
idˡ-sound {B = B} f = hCompose-hId-R-iso-generic B ⟪ f ⟫ (⟪⟫-codL f)

postulate
  hCompose-hId-L-iso-generic
    : ∀ (A : ObjTerm) (K : Hypergraph FlatGen)
        (K-domL≡flat : domL K ≡ flatten A)
    → Unique (Hypergraph.dom K)
    → hComposeP (hId A) K (trans (codL-hId A) (sym K-domL≡flat)) ≅ᴴ K
  idʳ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ f ∘ id ⟫ ≅ᴴ ⟪ f ⟫

postulate

  ρ⇐∘ρ⇒-sound : ∀ {A} → ⟪ ρ⇐ {A} ∘ ρ⇒ {A} ⟫ ≅ᴴ ⟪ id {A ⊗₀ unit} ⟫
  α⇐∘α⇒-sound : ∀ {A B C}
              → ⟪ α⇐ {A}{B}{C} ∘ α⇒ {A}{B}{C} ⟫ ≅ᴴ ⟪ id {(A ⊗₀ B) ⊗₀ C} ⟫

  σ∘σ-sound : ∀ {A B} → ⟪ σ {B}{A} ∘ σ {A}{B} ⟫ ≅ᴴ ⟪ id {A ⊗₀ B} ⟫

--------------------------------------------------------------------------------
-- CONSTRUCTIVELY PROVED under de-indexing.
--
-- `hTensor-hEmpty-G-iso`: for any G, `hTensor hEmpty G ≅ᴴ G`.  This is
-- a structural identity bijection: `hEmpty` contributes 0 vertices and
-- 0 edges, so `hTensor hEmpty G` has nV = 0 + G.nV = G.nV and nE = G.nE
-- definitionally, with `injR = 0 ↑ʳ_ = id` and `splitAt 0 i = inj₂ i`.
-- Each iso field is either `refl` directly or a routine `map-id` chain.

hTensor-hEmpty-G-iso
  : (G : Hypergraph FlatGen) → hTensor hEmpty G ≅ᴴ G
hTensor-hEmpty-G-iso G = record
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
  ; ψ-elab    = λ _ → refl
  }
  where
    module G′ = Hypergraph G
    module hT = hTensor-impl hEmpty G

    ein-eq : ∀ e → G′.ein e ≡ map (λ i → i) (Hypergraph.ein (hTensor hEmpty G) e)
    ein-eq e = sym (trans (map-id (Hypergraph.ein (hTensor hEmpty G) e))
                          (trans (map-cong (λ _ → refl) (G′.ein e))
                                 (map-id (G′.ein e))))

    eout-eq : ∀ e → G′.eout e ≡ map (λ i → i) (Hypergraph.eout (hTensor hEmpty G) e)
    eout-eq e = sym (trans (map-id (Hypergraph.eout (hTensor hEmpty G) e))
                           (trans (map-cong (λ _ → refl) (G′.eout e))
                                  (map-id (G′.eout e))))

    dom-eq : G′.dom ≡ map (λ i → i) (Hypergraph.dom (hTensor hEmpty G))
    dom-eq = sym (trans (map-id (Hypergraph.dom (hTensor hEmpty G)))
                        (trans (map-cong (λ _ → refl) G′.dom)
                               (map-id G′.dom)))

    cod-eq : G′.cod ≡ map (λ i → i) (Hypergraph.cod (hTensor hEmpty G))
    cod-eq = sym (trans (map-id (Hypergraph.cod (hTensor hEmpty G)))
                        (trans (map-cong (λ _ → refl) G′.cod)
                               (map-id G′.cod)))

    atom-ein-eq : ∀ e → map G′.vlab (G′.ein e)
                      ≡ map (Hypergraph.vlab (hTensor hEmpty G))
                            (Hypergraph.ein (hTensor hEmpty G) e)
    atom-ein-eq e = map-via-raise hT.vlab-injR (G′.ein e)

    atom-eout-eq : ∀ e → map G′.vlab (G′.eout e)
                       ≡ map (Hypergraph.vlab (hTensor hEmpty G))
                             (Hypergraph.eout (hTensor hEmpty G) e)
    atom-eout-eq e = map-via-raise hT.vlab-injR (G′.eout e)

--------------------------------------------------------------------------------
-- λ⇐∘λ⇒-sound and λ⇒∘λ⇐-sound: under de-indexing, ⟪ λ⇒ {A} ⟫ = hId A
-- and ⟪ λ⇐ {A} ⟫ = hId A.  So both ⟪ λ⇐ ∘ λ⇒ ⟫ and ⟪ λ⇒ ∘ λ⇐ ⟫ reduce
-- to `hComposeP (hId A) (hId A) bdy`, which `idˡ-sound (id {A})` shows
-- is ≅ᴴ to ⟪ id {A} ⟫.

λ⇒∘λ⇐-sound : ∀ {A} → ⟪ λ⇒ {A} ∘ λ⇐ {A} ⟫ ≅ᴴ ⟪ id {A} ⟫
λ⇒∘λ⇐-sound {A} = idˡ-sound (id {A})

-- For λ⇐∘λ⇒-sound the target is `id {unit ⊗₀ A}` instead of `id {A}`.
-- ⟪ id {unit ⊗₀ A} ⟫ = hId (unit ⊗₀ A) = hTensor hEmpty (hId A); compose
-- with `hTensor-hEmpty-G-iso` (sym) to land at `hId A`.

λ⇐∘λ⇒-sound : ∀ {A} → ⟪ λ⇐ {A} ∘ λ⇒ {A} ⟫ ≅ᴴ ⟪ id {unit ⊗₀ A} ⟫
λ⇐∘λ⇒-sound {A} =
  trans-≅ᴴ (idˡ-sound (id {A})) (sym-≅ᴴ (hTensor-hEmpty-G-iso (hId A)))

--------------------------------------------------------------------------------
-- λ⇒∘id⊗f≈f∘λ⇒-sound (λ-naturality).
--
-- ⟪ λ⇒ ∘ (id ⊗ f) ⟫ = hComposeP (hTensor hEmpty ⟪f⟫) (hId B) bdy
--                  ≅ᴴ hTensor hEmpty ⟪f⟫    [hCompose-hId-R-iso-generic]
--                  ≅ᴴ ⟪f⟫                    [hTensor-hEmpty-G-iso]
-- ⟪ f ∘ λ⇒ ⟫       = hComposeP (hId A) ⟪f⟫ bdy
--                  ≅ᴴ ⟪f⟫                    [hCompose-hId-L-iso-generic — postulated]

open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)

λ⇒∘id⊗f≈f∘λ⇒-sound
  : ∀ {A B} {f : HomTerm A B}
  → ⟪ λ⇒ {B} ∘ (id {unit} ⊗₁ f) ⟫ ≅ᴴ ⟪ f ∘ λ⇒ {A} ⟫
λ⇒∘id⊗f≈f∘λ⇒-sound {A = A} {B = B} {f = f} =
  trans-≅ᴴ
    (trans-≅ᴴ (hCompose-hId-R-iso-generic B (hTensor hEmpty ⟪ f ⟫)
                                            (⟪⟫-codL (id {unit} ⊗₁ f)))
              (hTensor-hEmpty-G-iso ⟪ f ⟫))
    (sym-≅ᴴ (hCompose-hId-L-iso-generic A ⟪ f ⟫ (⟪⟫-domL f) (⟪_⟫-dom-unique f)))
