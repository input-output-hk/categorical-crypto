{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- General-A `id`-vs-`σ` cases of `decode-rel-resp-≅ᴴ`.
--
-- Goal: prove `decode-rel (id {A ⊗₀ A}) ≈Term decode-rel (σ {A}{A})` (and
-- its symmetric variant) whenever the hypergraphs are iso.
--
-- Key observation:
--   `⟪ id {A ⊗₀ A} ⟫ = hTensor (hId A) (hId A)` has `dom ≡ cod`
--      (via `hId-cod≡dom`).
--   `⟪ σ {A}{A} ⟫ = hSwap A A` has `dom = (left half ++ right half)` and
--      `cod = (right half ++ left half)`.  When `length (flatten A) ≠ 0`,
--      the heads of `dom` and `cod` differ (toℕ `0` vs `length (flatten A)`),
--      so `K.dom ≢ K.cod`.
--
--   An iso `G ≅ᴴ K` with `G.dom ≡ G.cod` forces `K.dom = map φ G.dom =
--   map φ G.cod = K.cod`.  Combined with the above: such an iso exists
--   iff `flatten A ≡ []`.
--
-- Proof structure (both fully constructive, no postulates):
--   * Case `flatten A = _ ∷ _`: derive `⊥` from the iso, via the head
--     mismatch in `K.dom` vs `K.cod` against `G.dom ≡ G.cod`.
--   * Case `flatten A = []`: prove unconditionally via the helper
--     `σ-A-A-is-id-from-A≅unit` (which conjugates σ {A}{A} through the
--     coherence iso `A ≅ unit` to `σ {unit}{unit}`, which collapses to
--     `id` by `σ-unit-unit-is-id`).  The iso hypothesis is unused in
--     this branch — the conclusion holds by coherence alone.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.IdSigma
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; ⟪_⟫; hSwap)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Invariant sig using (hId-cod≡dom)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-flatten-≈)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.UnitCross sig
  using (σ-unit-unit-is-id)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; toℕ)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

--------------------------------------------------------------------------------
-- Unit-only case: `σ {A}{A} ≈Term id {A ⊗₀ A}` when `flatten A ≡ []`.
--
-- Strategy: when `flatten A ≡ []`, the coherence iso
-- `unflatten-flatten-≈ A : A ≅ unflatten (flatten A)` is `A ≅ unit`
-- (after substituting `flatten A = []`).  With γ : A ≅ unit, σ {A}{A}
-- is conjugate to σ {unit}{unit}, which is `id` by `σ-unit-unit-is-id`,
-- so σ {A}{A} ≈ id.
--
-- `A≅unit-from-flatten-empty` and `σ-flatten-empty-is-id` are exported
-- because the α-σ proofs reuse them.

private
  -- The conjugation chain σ {A}{A} ≈ id via an iso γ : A ≅ unit.
  --
  --   σ {A}{A}
  --   ≈ σ ∘ id                                                   [idʳ⁻¹]
  --   ≈ σ ∘ ((γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from))                [iso]
  --   ≈ (σ ∘ (γ.to ⊗₁ γ.to)) ∘ (γ.from ⊗₁ γ.from)                [assoc]
  --   ≈ ((γ.to ⊗₁ γ.to) ∘ σ {unit}{unit}) ∘ (γ.from ⊗₁ γ.from)   [σ-nat]
  --   ≈ ((γ.to ⊗₁ γ.to) ∘ id) ∘ (γ.from ⊗₁ γ.from)               [σ-unit]
  --   ≈ (γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from)                       [idʳ]
  --   ≈ (γ.to ∘ γ.from) ⊗₁ (γ.to ∘ γ.from)                        [⊗-∘-dist⁻¹]
  --   ≈ id ⊗₁ id                                                   [γ.isoˡ ×2]
  --   ≈ id                                                          [id⊗id]

  σ-A-A-is-id-from-A≅unit
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → (γ : A ≅ unit)
    → σ {A = A} {B = A} ⦃ s ⦄ ≈Term id
  σ-A-A-is-id-from-A≅unit {A} ⦃ s ⦄ γ = begin
    σ {A = A} {B = A} ⦃ s ⦄
      ≈⟨ idʳ ⟨
    σ {A = A} {B = A} ⦃ s ⦄ ∘ id
      ≈⟨ refl⟩∘⟨ id-A⊗A-via-iso ⟨
    σ {A = A} {B = A} ⦃ s ⦄ ∘ ((γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from))
      ≈⟨ FM.sym-assoc ⟩
    (σ {A = A} {B = A} ⦃ s ⦄ ∘ (γ.to ⊗₁ γ.to)) ∘ (γ.from ⊗₁ γ.from)
      ≈⟨ σ∘[f⊗g]≈[g⊗f]∘σ ⦃ s ⦄ ⟩∘⟨refl ⟩
    ((γ.to ⊗₁ γ.to) ∘ σ {A = unit} {B = unit} ⦃ s ⦄) ∘ (γ.from ⊗₁ γ.from)
      ≈⟨ (refl⟩∘⟨ σ-unit-unit-is-id ⦃ s ⦄) ⟩∘⟨refl ⟩
    ((γ.to ⊗₁ γ.to) ∘ id) ∘ (γ.from ⊗₁ γ.from)
      ≈⟨ idʳ ⟩∘⟨refl ⟩
    (γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from)
      ≈⟨ id-A⊗A-via-iso ⟩
    id ∎
    where
      module γ = _≅_ γ
      -- `(γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from) ≈Term id {A ⊗₀ A}`
      -- via ⊗-∘-dist⁻¹ + (γ.isoˡ ×2) + id⊗id≈id.
      id-A⊗A-via-iso
        : (γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from)
        ≈Term id {A ⊗₀ A}
      id-A⊗A-via-iso = begin
        (γ.to ⊗₁ γ.to) ∘ (γ.from ⊗₁ γ.from)       ≈⟨ ⊗-∘-dist ⟨
        (γ.to ∘ γ.from) ⊗₁ (γ.to ∘ γ.from)        ≈⟨ ⊗-resp-≈ (_≅_.isoˡ γ) (_≅_.isoˡ γ) ⟩
        id {A} ⊗₁ id {A}                          ≈⟨ id⊗id≈id ⟩
        id {A ⊗₀ A}                                ∎

-- Now obtain the iso γ : A ≅ unit from `flatten A ≡ []`.
A≅unit-from-flatten-empty
  : ∀ {A} → flatten A ≡ [] → A ≅ unit
A≅unit-from-flatten-empty {A} flat-eq =
  subst (A ≅_) (cong unflatten flat-eq) (unflatten-flatten-≈ A)

σ-flatten-empty-is-id
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → flatten A ≡ []
  → σ {A = A} {B = A} ⦃ s ⦄ ≈Term id
σ-flatten-empty-is-id {A} ⦃ s ⦄ flat-eq =
  σ-A-A-is-id-from-A≅unit ⦃ s ⦄ (A≅unit-from-flatten-empty {A} flat-eq)

private
  -- Bridge σ collapses to id (in the typed unflatten-flatten context)
  -- when flatten A ≡ [] — congruence with σ ≈ id under the bridge wrapper.
  bridge-σ-flatten-empty
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → flatten A ≡ []
    → bridge (σ {A = A} {B = A} ⦃ s ⦄) ≈Term bridge (id {A ⊗₀ A})
  bridge-σ-flatten-empty {A} ⦃ s ⦄ flat-eq =
    refl⟩∘⟨ σ-flatten-empty-is-id ⦃ s ⦄ flat-eq ⟩∘⟨refl

--------------------------------------------------------------------------------
-- Non-empty-`flatten` case: an iso forces a contradiction.

private
  ∷-headEq : ∀ {A : Set} {a b : A} {as bs : List A}
           → a ∷ as ≡ b ∷ bs → a ≡ b
  ∷-headEq refl = refl

  -- `0 ≡ suc m → ⊥` for natural numbers.
  0≢suc : ∀ {m : ℕ} → 0 ≡ suc m → ⊥
  0≢suc ()

  -- Core impossibility step: if `flatten A = x ∷ ys` and
  -- `(hSwap A A).dom ≡ (hSwap A A).cod`, derive `⊥`.
  --
  -- After `rewrite flat-eq`, `length (flatten A)` reduces to
  -- `suc (length ys)`, and the heads of dom/cod become
  -- `zero ↑ˡ (suc (length ys))` and `suc (length ys) ↑ʳ zero`
  -- respectively.  `toℕ` on these yields `0` and
  -- `suc (length ys) + 0 = suc _`, an immediate contradiction.
  flatten-non-empty-no-K-eq
    : ∀ {A} (x : X) (ys : List X)
    → flatten A ≡ x ∷ ys
    → Hypergraph.dom (hSwap A A) ≡ Hypergraph.cod (hSwap A A)
    → ⊥
  flatten-non-empty-no-K-eq {A} x ys flat-eq dom≡cod
    rewrite flat-eq
    = let
        nA = suc (length ys)
        head-eq : (zero {n = length ys} ↑ˡ nA) ≡ (nA ↑ʳ zero {n = length ys})
        head-eq = ∷-headEq dom≡cod

        toℕ-eq : toℕ (zero {n = length ys} ↑ˡ nA)
               ≡ toℕ (nA ↑ʳ zero {n = length ys})
        toℕ-eq = cong toℕ head-eq

        toℕ-L : toℕ (zero {n = length ys} ↑ˡ nA) ≡ 0
        toℕ-L = toℕ-↑ˡ (zero {n = length ys}) nA

        toℕ-R : toℕ (nA ↑ʳ zero {n = length ys}) ≡ nA + 0
        toℕ-R = toℕ-↑ʳ nA (zero {n = length ys})
      in 0≢suc (trans (sym toℕ-L) (trans toℕ-eq toℕ-R))

  -- From the iso, derive `K.dom ≡ K.cod`.  Uses `G.dom ≡ G.cod`
  -- (`hId-cod≡dom`) and the iso's `φ-dom`/`φ-cod`.
  iso→K-dom≡cod
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → ⟪ id {A ⊗₀ A} ⟫ ≅ᴴ ⟪ σ {A = A} {B = A} ⦃ s ⦄ ⟫
    → Hypergraph.dom (hSwap A A) ≡ Hypergraph.cod (hSwap A A)
  iso→K-dom≡cod {A} iso = trans φ-dom (trans
      (cong (map φ) (sym (hId-cod≡dom (A ⊗₀ A))))
      (sym φ-cod))
    where open _≅ᴴ_ iso

  iso→flatten-empty
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → ⟪ id {A ⊗₀ A} ⟫ ≅ᴴ ⟪ σ {A = A} {B = A} ⦃ s ⦄ ⟫
    → flatten A ≡ []
  iso→flatten-empty {A} ⦃ s ⦄ iso with flatten A in eq
  ... | []      = refl
  ... | x ∷ ys  =
    ⊥-elim (flatten-non-empty-no-K-eq {A = A} x ys eq
              (iso→K-dom≡cod {A = A} ⦃ s ⦄ iso))

--------------------------------------------------------------------------------
-- Main lemmas.
--
-- Combine: `iso→flatten-empty` extracts `flatten A ≡ []` from the iso,
-- then `bridge-σ-flatten-empty` collapses `bridge (σ {A}{A})` to
-- `bridge (id {A ⊗₀ A})` via congruence with `σ-flatten-empty-is-id`.

decode-rel-resp-≅ᴴ-id-σ-general
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ id {A ⊗₀ A} ⟫ ≅ᴴ ⟪ σ {A = A} {B = A} ⦃ s ⦄ ⟫
  → decode-rel (id {A ⊗₀ A})
  ≈Term decode-rel (σ {A = A} {B = A} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-id-σ-general {A} ⦃ s ⦄ iso =
  ≈-Term-sym (bridge-σ-flatten-empty {A = A} ⦃ s ⦄
                (iso→flatten-empty {A = A} ⦃ s ⦄ iso))

decode-rel-resp-≅ᴴ-σ-id-general
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ σ {A = A} {B = A} ⦃ s ⦄ ⟫ ≅ᴴ ⟪ id {A ⊗₀ A} ⟫
  → decode-rel (σ {A = A} {B = A} ⦃ s ⦄)
  ≈Term decode-rel (id {A ⊗₀ A})
decode-rel-resp-≅ᴴ-σ-id-general {A} ⦃ s ⦄ iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-id-σ-general {A = A} ⦃ s ⦄ (sym-≅ᴴ iso))
