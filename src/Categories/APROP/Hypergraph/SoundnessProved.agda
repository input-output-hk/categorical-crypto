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
         map-via-inj; map-via-raise; module hTensor-impl; range)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Invariant sig
open import Categories.APROP.Hypergraph.Prune

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; cast)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ;
                                        splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
                                        cast-is-id; cast-trans;
                                        toℕ-cast; toℕ-injective)
open import Data.List using (List; []; _∷_; map; lookup; tabulate; allFin; length)
open import Data.List.Properties using (map-∘; map-cong; map-id; map-tabulate;
                                          tabulate-lookup)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong; subst; subst₂; module ≡-Reasoning)
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
  (bdy-eq′ : codL G ≡ domL (hId B))
  where
  private
    K = hId B
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
hCompose-hId-R-iso-generic B G bdy-eq =
  hCompose-hId-R-proof.hCompose-hId-R-iso B G (trans bdy-eq (sym (domL-hId B)))

-- Flexible variant: takes the boundary equation as `codL G ≡ domL (hId B)`
-- directly, without going through `flatten B`.  Useful when the bdy proof
-- doesn't factor through `flatten B` (e.g. for `ρ⇐∘ρ⇒-sound` where the
-- bdy is built from the de-indexed `⟪⟫-codL`/`⟪⟫-domL` invariants).
hCompose-hId-R-iso-flex
  : (B : ObjTerm) (G : Hypergraph FlatGen) (bdy : codL G ≡ domL (hId B))
  → hComposeP G (hId B) bdy ≅ᴴ G
hCompose-hId-R-iso-flex = hCompose-hId-R-proof.hCompose-hId-R-iso

--------------------------------------------------------------------------------
-- `idˡ-sound`: ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫.
--
-- Direct consequence of `hCompose-hId-R-iso-generic`:
-- ⟪ id ∘ f ⟫ = hComposeP ⟪ f ⟫ ⟪ id {B} ⟫ bdy = hComposeP ⟪ f ⟫ (hId B) bdy.

idˡ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ id ∘ f ⟫ ≅ᴴ ⟪ f ⟫
idˡ-sound {B = B} f = hCompose-hId-R-iso-generic B ⟪ f ⟫ (⟪⟫-codL f)

--------------------------------------------------------------------------------
-- Generic LEFT-identity-composition iso.  Symmetric to the R proof,
-- with the bijection `classify`-based.

module hCompose-hId-L-proof
  (A : ObjTerm)
  (K : Hypergraph FlatGen) (K-domL≡flat : domL K ≡ flatten A)
  (K-unique : Unique (Hypergraph.dom K))
  where
  private
    G = hId A
    bdy-eq : codL G ≡ domL K
    bdy-eq = trans (codL-hId A) (sym K-domL≡flat)
    C = hComposeP G K bdy-eq
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph C
    module hCP = hComposeP-impl G K bdy-eq

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
      (trans (cong length K-domL≡flat)
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
  --   By K-domL≡flat (pointwise): K.vlab (lookup K.dom j) ≡ lookup (flatten A) (cast _ j).
  --   By hId-vlab-lookup: (hId A).vlab k ≡ lookup (flatten A) (cast _ k).
  --   Both sides reduce to `lookup (flatten A) (cast _ k)` modulo toℕ-injective.
  --
  -- For v with splitAt G.nV v = inj₂ j:
  --   C.vlab v = K.vlab (lookup (nonMem K.dom) j) = K.vlab (φ v).  REFL.

  open import Data.Fin using (toℕ)

  -- Pointwise from K-domL≡flat: K.vlab (lookup K.dom j) ≡ lookup (flatten A) (cast _ j).
  -- `lookup-≡-map-cast` gives us this in a specific cast form; we then use
  -- toℕ-injective to collapse that with `hId-vlab-lookup`'s cast.

  φ-lab : ∀ v → K.vlab (φ v) ≡ C.vlab v
  φ-lab v with splitAt G.nV v
  ... | inj₁ k =
    -- Goal: K.vlab (lookup K.dom (cast (sym len-dom) k)) ≡ G.vlab k
    -- RHS:  G.vlab k = (hId A).vlab k ≡ lookup (flatten A) (cast _ k)
    --       by hId-vlab-lookup.
    -- LHS:  K.vlab (lookup K.dom j)   ≡ lookup (flatten A) (cast _ j)
    --       by lookup-≡-map-cast K.vlab (sym K-domL≡flat), with j = cast (sym len-dom) k.
    -- Both casts applied to k have toℕ = toℕ k, so equal by toℕ-injective.
    trans (sym (lookup-≡-map-cast K.vlab (sym K-domL≡flat) (cast (sym len-dom) k)))
    (trans (cong (lookup (flatten A)) same-cast-at-k)
           (sym (hId-vlab-lookup A k)))
    where
      open import Data.Fin using (cast)

      -- The two distinct Fin values (from the two casts) both have
      -- toℕ = toℕ k, hence they're equal by toℕ-injective.
      same-cast-at-k
        : cast (sym (trans (cong length (sym K-domL≡flat)) (length-map K.vlab K.dom)))
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


hCompose-hId-L-iso-generic
  : ∀ (A : ObjTerm) (K : Hypergraph FlatGen)
      (K-domL≡flat : domL K ≡ flatten A)
  → Unique (Hypergraph.dom K)
  → hComposeP (hId A) K (trans (codL-hId A) (sym K-domL≡flat)) ≅ᴴ K
hCompose-hId-L-iso-generic = hCompose-hId-L-proof.hCompose-hId-L-iso

idʳ-sound : ∀ {A B} (f : HomTerm A B) → ⟪ f ∘ id ⟫ ≅ᴴ ⟪ f ⟫
idʳ-sound {A = A} f =
  hCompose-hId-L-iso-generic A ⟪ f ⟫ (⟪⟫-domL f)
    (Categories.APROP.Hypergraph.HomTermInvariant.⟪_⟫-dom-unique sig f)
  where import Categories.APROP.Hypergraph.HomTermInvariant


postulate

  σ∘σ-sound : ∀ {A B} → ⟪ σ {B}{A} ∘ σ {A}{B} ⟫ ≅ᴴ ⟪ id {A ⊗₀ B} ⟫

--------------------------------------------------------------------------------
-- ρ⇐∘ρ⇒ and α⇐∘α⇒: under de-indexing, ⟪ ρ⇒/ρ⇐ ⟫ are both hId (A ⊗ unit)
-- and ⟪ α⇒/α⇐ ⟫ are both hId ((A ⊗ B) ⊗ C).  We apply
-- `hCompose-hId-R-iso-flex`, which accepts an arbitrary boundary
-- equation `codL G ≡ domL (hId B)` (rather than the rigid
-- `trans bdy (sym (domL-hId B))` form `hCompose-hId-R-iso-generic`
-- requires).  The bdy from `⟪ g ∘ f ⟫` factors through `flatten A`
-- (intermediate object), not `flatten (A ⊗ unit)`, so the flex variant
-- is the right tool here.

ρ⇐∘ρ⇒-sound : ∀ {A} → ⟪ ρ⇐ {A} ∘ ρ⇒ {A} ⟫ ≅ᴴ ⟪ id {A ⊗₀ unit} ⟫
ρ⇐∘ρ⇒-sound {A} =
  hCompose-hId-R-iso-flex (A ⊗₀ unit) (hId (A ⊗₀ unit))
    (trans (⟪⟫-codL (ρ⇒ {A})) (sym (⟪⟫-domL (ρ⇐ {A}))))

α⇐∘α⇒-sound : ∀ {A B C}
            → ⟪ α⇐ {A}{B}{C} ∘ α⇒ {A}{B}{C} ⟫ ≅ᴴ ⟪ id {(A ⊗₀ B) ⊗₀ C} ⟫
α⇐∘α⇒-sound {A}{B}{C} =
  hCompose-hId-R-iso-flex ((A ⊗₀ B) ⊗₀ C) (hId ((A ⊗₀ B) ⊗₀ C))
    (trans (⟪⟫-codL (α⇒ {A}{B}{C})) (sym (⟪⟫-domL (α⇐ {A}{B}{C}))))

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
-- `hTensor-G-hEmpty-iso`: for any G, `hTensor G hEmpty ≅ᴴ G`.  Right-unit
-- counterpart to `hTensor-hEmpty-G-iso`.  Unlike the left-unit case where
-- `0 + n` reduces to `n` definitionally and `splitAt 0 v = inj₂ v`, here
-- `n + 0` doesn't reduce, so vertex/edge bijections are spelled out via
-- explicit `splitAt G.nV` case-splits with the inj₂ branches absurd
-- (since `Fin 0` has no inhabitants).

hTensor-G-hEmpty-iso
  : (G : Hypergraph FlatGen) → hTensor G hEmpty ≅ᴴ G
hTensor-G-hEmpty-iso G = record
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
  where
    module G′ = Hypergraph G
    H = hTensor G hEmpty
    module H′ = Hypergraph H
    module hT = hTensor-impl G hEmpty

    φ : Fin H′.nV → Fin G′.nV
    φ v with splitAt G′.nV v
    ... | inj₁ k = k
    ... | inj₂ ()

    φ⁻¹ : Fin G′.nV → Fin H′.nV
    φ⁻¹ k = k ↑ˡ 0

    φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
    φ-left v with splitAt G′.nV v in eq
    ... | inj₁ k = splitAt⁻¹-↑ˡ eq
    ... | inj₂ ()

    φ-rght : ∀ k → φ (φ⁻¹ k) ≡ k
    φ-rght k rewrite splitAt-↑ˡ G′.nV k 0 = refl

    ψ : Fin H′.nE → Fin G′.nE
    ψ e with splitAt G′.nE e
    ... | inj₁ eG = eG
    ... | inj₂ ()

    ψ⁻¹ : Fin G′.nE → Fin H′.nE
    ψ⁻¹ e = e ↑ˡ 0

    ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
    ψ-left e with splitAt G′.nE e in eq
    ... | inj₁ eG = splitAt⁻¹-↑ˡ eq
    ... | inj₂ ()

    ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
    ψ-rght e rewrite splitAt-↑ˡ G′.nE e 0 = refl

    φ-lab : ∀ v → G′.vlab (φ v) ≡ H′.vlab v
    φ-lab v with splitAt G′.nV v
    ... | inj₁ k = refl
    ... | inj₂ ()

    φ-injL : ∀ k → φ (k ↑ˡ 0) ≡ k
    φ-injL k rewrite splitAt-↑ˡ G′.nV k 0 = refl

    -- `H.dom` and `H.cod` have an explicit trailing `map injR [] = []`
    -- because `hEmpty.dom = hEmpty.cod = []`.  Strip via `++-identityʳ`
    -- in `φ-dom`/`φ-cod`.
    open import Data.List.Properties using (++-identityʳ)

    ψ-ein : ∀ e → G′.ein (ψ e) ≡ map φ (H′.ein e)
    ψ-ein e with splitAt G′.nE e
    ... | inj₁ eG = sym
      (trans (sym (map-∘ (G′.ein eG)))
             (trans (map-cong φ-injL (G′.ein eG))
                    (map-id (G′.ein eG))))
    ... | inj₂ ()

    ψ-eout : ∀ e → G′.eout (ψ e) ≡ map φ (H′.eout e)
    ψ-eout e with splitAt G′.nE e
    ... | inj₁ eG = sym
      (trans (sym (map-∘ (G′.eout eG)))
             (trans (map-cong φ-injL (G′.eout eG))
                    (map-id (G′.eout eG))))
    ... | inj₂ ()

    φ-dom : G′.dom ≡ map φ H′.dom
    φ-dom = sym
      (trans (cong (map φ) (++-identityʳ (map hT.injL G′.dom)))
      (trans (sym (map-∘ G′.dom))
      (trans (map-cong φ-injL G′.dom)
             (map-id G′.dom))))

    φ-cod : G′.cod ≡ map φ H′.cod
    φ-cod = sym
      (trans (cong (map φ) (++-identityʳ (map hT.injL G′.cod)))
      (trans (sym (map-∘ G′.cod))
      (trans (map-cong φ-injL G′.cod)
             (map-id G′.cod))))

    atom-ein : ∀ e → map G′.vlab (G′.ein (ψ e)) ≡ map H′.vlab (H′.ein e)
    atom-ein e with splitAt G′.nE e
    ... | inj₁ eG = map-via-inj hT.vlab-injL (G′.ein eG)
    ... | inj₂ ()

    atom-eout : ∀ e → map G′.vlab (G′.eout (ψ e)) ≡ map H′.vlab (H′.eout e)
    atom-eout e with splitAt G′.nE e
    ... | inj₁ eG = map-via-inj hT.vlab-injL (G′.eout eG)
    ... | inj₂ ()

    ψ-elab : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e) (G′.elab (ψ e))
                 ≡ H′.elab e
    ψ-elab e with splitAt G′.nE e
    ... | inj₁ eG = refl
    ... | inj₂ ()

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
