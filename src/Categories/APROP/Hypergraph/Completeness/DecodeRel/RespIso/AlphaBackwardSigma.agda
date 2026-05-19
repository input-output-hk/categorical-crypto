{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- General-A `α⇐`-vs-`σ` cases of `decode-rel-resp-≅ᴴ`.
--
-- Goal: prove `decode-rel (α⇐ {A}{A}{A}) ≈Term decode-rel (σ {A}{A ⊗₀ A})`
-- (and its symmetric variant) whenever the hypergraphs are iso.
--
-- Key observation:
--   `⟪ α⇐ {A}{A}{A} ⟫ = hId ((A ⊗₀ A) ⊗₀ A)` has `dom ≡ cod`
--      (via `hId-cod≡dom`).
--   `⟪ σ {A}{A ⊗₀ A} ⟫ = hSwap A (A ⊗₀ A)` has
--      `dom ≡ (left-half ++ right-half)` and `cod ≡ (right-half ++ left-half)`.
--      When `flatten A ≠ []` the heads of `dom` and `cod` differ
--      (toℕ `0` vs `length (flatten A)`), so `K.dom ≢ K.cod`.
--
--   An iso `G ≅ᴴ K` with `G.dom ≡ G.cod` forces `K.dom = map φ G.dom =
--   map φ G.cod = K.cod`.  Combined with the above: such an iso exists
--   iff `flatten A ≡ []`.
--
-- Proof structure (mirrors `IdSigma.agda`):
--   * Case `flatten A = _ ∷ _`: derive `⊥` from the iso (handled here in
--     full).
--   * Case `flatten A = []`: reduce to a postulated narrow lemma
--     `decode-rel-resp-≅ᴴ-α⇐-σ-flatten-empty` (the iso is unused here;
--     the conclusion is purely about coherence and `α⇐`/`σ` collapsing
--     under unit-only `A`).
--
-- Derived from `IdSigma.agda` by adjusting:
--   * `hId (A ⊗₀ A)` → `hId ((A ⊗₀ A) ⊗₀ A)` (three-fold tensor).
--   * `hSwap A A`   → `hSwap A (A ⊗₀ A)` (B = A ⊗₀ A).
--   * The narrow unit-only postulate is `α⇐`/`σ`-shaped.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AlphaBackwardSigma
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; ⟪_⟫; hId; hSwap)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_; sym-≅ᴴ)
open import Categories.APROP.Hypergraph.Invariant sig using (hId-cod≡dom)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AlphaForwardSigma sig
  using (σ-α⇒-cancels)

open import Categories.Category using (Category)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; toℕ)
open import Data.Fin.Properties using (toℕ-↑ˡ; toℕ-↑ʳ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)

private
  module FM = Category FreeMonoidal
open FM.HomReasoning

--------------------------------------------------------------------------------
-- Unit-only case: `α⇐ {A}{A}{A} ≈Term σ {A}{A⊗A}` when `flatten A ≡ []`.
--
-- Strategy: `σ-α⇒-cancels` gives `σ {A}{A⊗A} ∘ α⇒ ≈ id`, and
-- `α⇐∘α⇒≈id`, `α⇒∘α⇐≈id` are axioms.  Both `σ {A}{A⊗A}` and `α⇐` are
-- left-inverses of `α⇒`; in a category whose `α⇒` has both a left- and
-- a right-inverse (here `α⇐`), the left-inverses are unique.
-- Concretely:
--   α⇐ ≈ id ∘ α⇐ ≈ (σ ∘ α⇒) ∘ α⇐ ≈ σ ∘ (α⇒ ∘ α⇐) ≈ σ ∘ id ≈ σ.
private
  α⇐-is-σ-from-flatten-empty
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → flatten A ≡ []
    → α⇐ {A}{A}{A}
    ≈Term σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄
  α⇐-is-σ-from-flatten-empty {A} ⦃ s ⦄ flat-eq = begin
    α⇐ {A}{A}{A}
      ≈⟨ idˡ ⟨
    id ∘ α⇐ {A}{A}{A}
      ≈⟨ σ-α⇒-cancels ⦃ s ⦄ flat-eq ⟩∘⟨refl ⟨
    (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A}) ∘ α⇐ {A}{A}{A}
      ≈⟨ FM.assoc ⟩
    σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ (α⇒ {A}{A}{A} ∘ α⇐ {A}{A}{A})
      ≈⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩
    σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ id
      ≈⟨ idʳ ⟩
    σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∎

decode-rel-resp-≅ᴴ-α⇐-σ-flatten-empty
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → flatten A ≡ []
  → decode-rel (α⇐ {A} {A} {A})
  ≈Term decode-rel (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-α⇐-σ-flatten-empty {A} ⦃ s ⦄ flat-eq =
  refl⟩∘⟨ α⇐-is-σ-from-flatten-empty ⦃ s ⦄ flat-eq ⟩∘⟨refl

--------------------------------------------------------------------------------
-- Non-empty case: an iso forces a contradiction.

private
  -- Cons-injectivity on the head.
  ∷-headEq : ∀ {A : Set} {a b : A} {as bs : List A}
           → a ∷ as ≡ b ∷ bs → a ≡ b
  ∷-headEq refl = refl

  -- `0 ≡ suc m → ⊥` for natural numbers.
  0≢suc : ∀ {m : ℕ} → 0 ≡ suc m → ⊥
  0≢suc ()

  -- Core impossibility step:
  -- If `flatten A = x ∷ ys` and we have `K.dom ≡ K.cod` where
  -- `K = hSwap A (A ⊗₀ A)`, derive `⊥`.
  --
  -- After `rewrite flat-eq`, `flatten A ↦ x ∷ ys`, so:
  --   * `nA = length (x ∷ ys) = suc (length ys)`
  --   * `nB' = length (flatten (A ⊗₀ A)) = length ((x ∷ ys) ++ (x ∷ ys))
  --          = suc (length (ys ++ x ∷ ys))`, hence `range nB'` is
  --     non-empty, starting with `zero`.
  -- The heads of `K.dom` and `K.cod` then are `zero ↑ˡ nB'` and
  -- `nA ↑ʳ zero`, with `toℕ` values `0` and `nA = suc (length ys)`.
  flatten-non-empty-no-K-eq
    : ∀ {A} (x : X) (ys : List X)
    → flatten A ≡ x ∷ ys
    → Hypergraph.dom (hSwap A (A ⊗₀ A)) ≡ Hypergraph.cod (hSwap A (A ⊗₀ A))
    → ⊥
  flatten-non-empty-no-K-eq {A} x ys flat-eq dom≡cod
    rewrite flat-eq
    = let
        nA  = suc (length ys)
        nB' = suc (length (ys ++ x ∷ ys))

        -- After rewrite, hSwap A (A ⊗₀ A) computes with:
        --   dom = (zero ↑ˡ nB') ∷ ...
        --       ++ map (nA ↑ʳ_) (range nB')
        --   cod = (nA ↑ʳ zero) ∷ ...
        --       ++ map (_↑ˡ nB') (range nA)
        --
        -- The head equality is `zero ↑ˡ nB' ≡ nA ↑ʳ zero`, which by `toℕ`
        -- gives `0 ≡ nA = suc (length ys)`, contradiction.

        head-eq : (zero {n = length ys} ↑ˡ nB')
                ≡ (nA ↑ʳ zero {n = length (ys ++ x ∷ ys)})
        head-eq = ∷-headEq dom≡cod

        toℕ-eq : toℕ (zero {n = length ys} ↑ˡ nB')
               ≡ toℕ (nA ↑ʳ zero {n = length (ys ++ x ∷ ys)})
        toℕ-eq = cong toℕ head-eq

        toℕ-L : toℕ (zero {n = length ys} ↑ˡ nB') ≡ 0
        toℕ-L = toℕ-↑ˡ (zero {n = length ys}) nB'

        toℕ-R : toℕ (nA ↑ʳ zero {n = length (ys ++ x ∷ ys)}) ≡ nA + 0
        toℕ-R = toℕ-↑ʳ nA (zero {n = length (ys ++ x ∷ ys)})
      in 0≢suc (trans (sym toℕ-L) (trans toℕ-eq toℕ-R))

  -- From the iso, derive `K.dom ≡ K.cod`.
  iso→K-dom≡cod
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → ⟪ α⇐ {A} {A} {A} ⟫ ≅ᴴ ⟪ σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ⟫
    → Hypergraph.dom (hSwap A (A ⊗₀ A))
    ≡ Hypergraph.cod (hSwap A (A ⊗₀ A))
  iso→K-dom≡cod {A} iso =
    let
      open _≅ᴴ_ iso
      -- G = hId ((A ⊗₀ A) ⊗₀ A) has G.dom ≡ G.cod (hId-cod≡dom).
      -- K = hSwap A (A ⊗₀ A); from φ-dom and φ-cod:
      --   K.dom ≡ map φ G.dom
      --   K.cod ≡ map φ G.cod ≡ map φ G.dom ≡ K.dom
      G-cod≡dom : Hypergraph.cod (hId ((A ⊗₀ A) ⊗₀ A))
                ≡ Hypergraph.dom (hId ((A ⊗₀ A) ⊗₀ A))
      G-cod≡dom = hId-cod≡dom ((A ⊗₀ A) ⊗₀ A)

      step₁ : Hypergraph.dom (hSwap A (A ⊗₀ A))
            ≡ map φ (Hypergraph.dom (hId ((A ⊗₀ A) ⊗₀ A)))
      step₁ = φ-dom

      step₂ : map φ (Hypergraph.dom (hId ((A ⊗₀ A) ⊗₀ A)))
            ≡ map φ (Hypergraph.cod (hId ((A ⊗₀ A) ⊗₀ A)))
      step₂ = cong (map φ) (sym G-cod≡dom)

      step₃ : map φ (Hypergraph.cod (hId ((A ⊗₀ A) ⊗₀ A)))
            ≡ Hypergraph.cod (hSwap A (A ⊗₀ A))
      step₃ = sym φ-cod
    in trans step₁ (trans step₂ step₃)

  -- Combining: an iso forces `flatten A ≡ []`.
  iso→flatten-empty
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → ⟪ α⇐ {A} {A} {A} ⟫ ≅ᴴ ⟪ σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ⟫
    → flatten A ≡ []
  iso→flatten-empty {A} ⦃ s ⦄ iso with flatten A in eq
  ... | []      = refl
  ... | x ∷ ys  =
    ⊥-elim (flatten-non-empty-no-K-eq {A = A} x ys eq
              (iso→K-dom≡cod {A = A} ⦃ s ⦄ iso))

--------------------------------------------------------------------------------
-- Main lemmas.

decode-rel-resp-≅ᴴ-α⇐-σ
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ α⇐ {A} {A} {A} ⟫ ≅ᴴ ⟪ σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ⟫
  → decode-rel (α⇐ {A} {A} {A})
  ≈Term decode-rel (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-α⇐-σ {A} ⦃ s ⦄ iso =
  decode-rel-resp-≅ᴴ-α⇐-σ-flatten-empty {A = A} ⦃ s ⦄
    (iso→flatten-empty {A = A} ⦃ s ⦄ iso)

decode-rel-resp-≅ᴴ-σ-α⇐
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ⟫ ≅ᴴ ⟪ α⇐ {A} {A} {A} ⟫
  → decode-rel (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄)
  ≈Term decode-rel (α⇐ {A} {A} {A})
decode-rel-resp-≅ᴴ-σ-α⇐ {A} ⦃ s ⦄ iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-α⇐-σ {A = A} ⦃ s ⦄ (sym-≅ᴴ iso))
