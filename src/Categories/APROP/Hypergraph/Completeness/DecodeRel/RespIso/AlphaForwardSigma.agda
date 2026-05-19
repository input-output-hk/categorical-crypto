{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- General-A `α⇒`-vs-`σ` cases of `decode-rel-resp-≅ᴴ`.
--
-- Goal: prove `decode-rel (α⇒ {A}{A}{A}) ≈Term decode-rel (σ {A⊗A}{A})`
-- (and its symmetric variant) whenever the hypergraphs are iso.
--
-- Key observation:
--   `⟪ α⇒ {A}{A}{A} ⟫ = hId ((A⊗A)⊗A)` has `dom ≡ cod` (`hId-cod≡dom`).
--   `⟪ σ {A⊗A}{A} ⟫ = hSwap (A⊗A) A` has dom = (left half ++ right half)
--      and cod = (right half ++ left half).  When `length (flatten A) ≠ 0`,
--      then `nA = length (flatten (A⊗A)) = 2 * length (flatten A) > 0` and
--      `nB = length (flatten A) > 0`; the heads of dom and cod differ
--      (toℕ `0` vs `nA`), so `K.dom ≢ K.cod`.
--
--   An iso `G ≅ᴴ K` with `G.dom ≡ G.cod` forces `K.dom = map φ G.dom =
--   map φ G.cod = K.cod`.  Combined with the above: such an iso exists
--   iff `flatten A ≡ []`.
--
-- Proof structure (mirrors `RespIso/IdSigma.agda`):
--   * Case `flatten A = _ ∷ _`: derive `⊥` from the iso (handled here in
--     full).
--   * Case `flatten A = []`: reduce to a postulated narrow lemma
--     `decode-rel-resp-≅ᴴ-α⇒-σ-flatten-empty` (the iso is unused; the
--     conclusion is purely about coherence and `α⇒`/`σ` collapsing under
--     unit-only `A`).  Discharging this remaining postulate amounts to
--     proving `α⇒ {A}{A}{A} ≈Term σ {A⊗A}{A}` whenever `flatten A ≡ []`,
--     which would follow from extending `σ-unit-unit-is-id` and
--     `bridge-α⇒-form unit` to arbitrary unit-only `A`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AlphaForwardSigma
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
open import Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.IdSigma sig
  using (σ-flatten-empty-is-id)

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
-- Unit-only case: `α⇒ {A}{A}{A} ≈Term σ {A⊗A}{A}` when `flatten A ≡ []`.
--
-- Strategy: combine `σ-flatten-empty-is-id` (`σ {A}{A} ≈ id` at unit-only A)
-- with the `hexagon` axiom (`id⊗σ ∘ α⇒ ∘ σ⊗id ≈ α⇒ ∘ σ ∘ α⇒`).  At
-- A=B=C the LHS of hexagon collapses to `α⇒` (via `σ {A}{A} ≈ id`),
-- so `α⇒ ≈ α⇒ ∘ σ{A}{A⊗A} ∘ α⇒`.  Cancelling `α⇒` on the left via
-- `α⇐∘α⇒≈id` yields `σ {A}{A⊗A} ∘ α⇒ ≈ id`, and combining with
-- `σ∘σ≈id` (σ {A⊗A}{A} ∘ σ {A}{A⊗A} ≈ id) yields `α⇒ ≈ σ {A⊗A}{A}`.

-- σ {A}{A⊗A} ∘ α⇒ {A}{A}{A} ≈ id at flatten A = [].  Public because the
-- backward direction (AlphaBackwardSigma) reuses it via α⇐ ≈ σ {A}{A⊗A}.
σ-α⇒-cancels
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → flatten A ≡ []
  → σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A} {A} {A} ≈Term id
σ-α⇒-cancels {A} ⦃ s ⦄ flat-eq = begin
  σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A}
    ≈⟨ idˡ ⟨
  id ∘ (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A})
    ≈⟨ α⇐∘α⇒≈id ⟩∘⟨refl ⟨
  (α⇐ {A}{A}{A} ∘ α⇒ {A}{A}{A}) ∘ (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A})
    ≈⟨ FM.assoc ⟩
  α⇐ {A}{A}{A} ∘ (α⇒ {A}{A}{A} ∘ (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A}))
    ≈⟨ refl⟩∘⟨ hexagon-LHS-collapse ⟩
  α⇐ {A}{A}{A} ∘ α⇒ {A}{A}{A}
    ≈⟨ α⇐∘α⇒≈id ⟩
  id ∎
  where
    -- hexagon at A=B=C=A says:
    --   (id ⊗ σ {A}{A}) ∘ α⇒ ∘ (σ {A}{A} ⊗ id)
    --   ≈ α⇒ ∘ σ {A}{A⊗A} ∘ α⇒.
    -- At flatten A = [], σ {A}{A} ≈ id collapses the LHS to α⇒.
    hexagon-LHS-collapse
      : α⇒ {A}{A}{A} ∘ (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A})
      ≈Term α⇒ {A}{A}{A}
    hexagon-LHS-collapse = begin
      α⇒ {A}{A}{A} ∘ (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A})
        ≈⟨ hexagon ⦃ s ⦄ ⟨
      (id ⊗₁ σ {A = A} {B = A} ⦃ s ⦄)
        ∘ α⇒ {A}{A}{A}
        ∘ (σ {A = A} {B = A} ⦃ s ⦄ ⊗₁ id)
        ≈⟨ ⊗-resp-≈ ≈-Term-refl (σ-flatten-empty-is-id ⦃ s ⦄ flat-eq)
            ⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ (σ-flatten-empty-is-id ⦃ s ⦄ flat-eq) ≈-Term-refl ⟩
      (id ⊗₁ id) ∘ α⇒ {A}{A}{A} ∘ (id ⊗₁ id)
        ≈⟨ id⊗id≈id ⟩∘⟨ refl⟩∘⟨ id⊗id≈id ⟩
      id ∘ α⇒ {A}{A}{A} ∘ id
        ≈⟨ idˡ ⟩
      α⇒ {A}{A}{A} ∘ id
        ≈⟨ idʳ ⟩
      α⇒ {A}{A}{A} ∎

private
  α⇒-is-σ-from-flatten-empty
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → flatten A ≡ []
    → α⇒ {A}{A}{A}
    ≈Term σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄
  α⇒-is-σ-from-flatten-empty {A} ⦃ s ⦄ flat-eq = begin
    α⇒ {A}{A}{A}
      ≈⟨ idˡ ⟨
    id ∘ α⇒ {A}{A}{A}
      ≈⟨ σ∘σ≈id ⦃ s ⦄ ⟩∘⟨refl ⟨
    (σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ∘ σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄)
      ∘ α⇒ {A}{A}{A}
      ≈⟨ FM.assoc ⟩
    σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄
      ∘ (σ {A = A} {B = A ⊗₀ A} ⦃ s ⦄ ∘ α⇒ {A}{A}{A})
      ≈⟨ refl⟩∘⟨ σ-α⇒-cancels ⦃ s ⦄ flat-eq ⟩
    σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ∘ id
      ≈⟨ idʳ ⟩
    σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ∎

decode-rel-resp-≅ᴴ-α⇒-σ-flatten-empty
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → flatten A ≡ []
  → decode-rel (α⇒ {A} {A} {A})
  ≈Term decode-rel (σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-α⇒-σ-flatten-empty {A} ⦃ s ⦄ flat-eq =
  refl⟩∘⟨ α⇒-is-σ-from-flatten-empty ⦃ s ⦄ flat-eq ⟩∘⟨refl

--------------------------------------------------------------------------------
-- Non-empty case: an iso forces a contradiction.

private
  -- Helpers shared with the `IdSigma` analogue.

  ∷-headEq : ∀ {A : Set} {a b : A} {as bs : List A}
           → a ∷ as ≡ b ∷ bs → a ≡ b
  ∷-headEq refl = refl

  0≢suc : ∀ {m : ℕ} → 0 ≡ suc m → ⊥
  0≢suc ()

  -- Core impossibility step:
  -- If `flatten A = x ∷ ys` and we have `K.dom ≡ K.cod` where
  -- `K = hSwap (A⊗A) A`, derive `⊥`.
  --
  -- After `rewrite flat-eq`, `flatten A` is replaced by `x ∷ ys`, so
  --   nA' = length ((x ∷ ys) ++ (x ∷ ys)) = suc (length (ys ++ x ∷ ys))
  --   nB' = length (x ∷ ys)             = suc (length ys)
  -- Both are `suc _`, so `range nA'` and `range nB'` are non-empty and
  -- start with `zero`.  The head-of-list comparison yields the
  -- impossible equation `zero ↑ˡ nB' ≡ nA' ↑ʳ zero` in `Fin (nA' + nB')`.
  flatten-non-empty-no-K-eq
    : ∀ {A} (x : X) (ys : List X)
    → flatten A ≡ x ∷ ys
    → Hypergraph.dom (hSwap (A ⊗₀ A) A) ≡ Hypergraph.cod (hSwap (A ⊗₀ A) A)
    → ⊥
  flatten-non-empty-no-K-eq {A} x ys flat-eq dom≡cod
    rewrite flat-eq
    = let
        -- After rewrite:
        --   nA' = length ((x∷ys) ++ (x∷ys)) = suc (length (ys ++ x ∷ ys))
        --   nB' = length (x∷ys)             = suc (length ys)
        m  : ℕ
        m  = length (ys ++ x ∷ ys)            -- nA' = suc m

        n  : ℕ
        n  = length ys                        -- nB' = suc n

        head-eq : (zero {n = m} ↑ˡ suc n)
                ≡ (suc m ↑ʳ zero {n = n})
        head-eq = ∷-headEq dom≡cod

        toℕ-eq : toℕ (zero {n = m} ↑ˡ suc n)
               ≡ toℕ (suc m ↑ʳ zero {n = n})
        toℕ-eq = cong toℕ head-eq

        toℕ-L : toℕ (zero {n = m} ↑ˡ suc n) ≡ 0
        toℕ-L = toℕ-↑ˡ (zero {n = m}) (suc n)

        -- toℕ (suc m ↑ʳ zero) = suc m + 0 = suc _.
        toℕ-R : toℕ (suc m ↑ʳ zero {n = n}) ≡ suc m + 0
        toℕ-R = toℕ-↑ʳ (suc m) zero
      in 0≢suc (trans (sym toℕ-L) (trans toℕ-eq toℕ-R))

  -- From the iso, derive `K.dom ≡ K.cod`.  Uses `G.dom ≡ G.cod`
  -- (`hId-cod≡dom`) and the iso's `φ-dom`/`φ-cod`.
  iso→K-dom≡cod
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → ⟪ α⇒ {A} {A} {A} ⟫ ≅ᴴ ⟪ σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ⟫
    → Hypergraph.dom (hSwap (A ⊗₀ A) A) ≡ Hypergraph.cod (hSwap (A ⊗₀ A) A)
  iso→K-dom≡cod {A} iso = trans φ-dom (trans
      (cong (map φ) (sym (hId-cod≡dom ((A ⊗₀ A) ⊗₀ A))))
      (sym φ-cod))
    where open _≅ᴴ_ iso

  -- Combining: an iso forces `flatten A ≡ []`.
  iso→flatten-empty
    : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
    → ⟪ α⇒ {A} {A} {A} ⟫ ≅ᴴ ⟪ σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ⟫
    → flatten A ≡ []
  iso→flatten-empty {A} ⦃ s ⦄ iso with flatten A in eq
  ... | []      = refl
  ... | x ∷ ys  =
    ⊥-elim (flatten-non-empty-no-K-eq {A = A} x ys eq
              (iso→K-dom≡cod {A = A} ⦃ s ⦄ iso))

--------------------------------------------------------------------------------
-- Main lemmas.

decode-rel-resp-≅ᴴ-α⇒-σ
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ α⇒ {A} {A} {A} ⟫ ≅ᴴ ⟪ σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ⟫
  → decode-rel (α⇒ {A} {A} {A})
  ≈Term decode-rel (σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄)
decode-rel-resp-≅ᴴ-α⇒-σ {A} ⦃ s ⦄ iso =
  decode-rel-resp-≅ᴴ-α⇒-σ-flatten-empty {A = A} ⦃ s ⦄
    (iso→flatten-empty {A = A} ⦃ s ⦄ iso)

decode-rel-resp-≅ᴴ-σ-α⇒
  : ∀ {A} ⦃ s : Symm ≤ Symm ⦄
  → ⟪ σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄ ⟫ ≅ᴴ ⟪ α⇒ {A} {A} {A} ⟫
  → decode-rel (σ {A = A ⊗₀ A} {B = A} ⦃ s ⦄)
  ≈Term decode-rel (α⇒ {A} {A} {A})
decode-rel-resp-≅ᴴ-σ-α⇒ ⦃ s ⦄ iso =
  ≈-Term-sym (decode-rel-resp-≅ᴴ-α⇒-σ ⦃ s ⦄ (sym-≅ᴴ iso))
