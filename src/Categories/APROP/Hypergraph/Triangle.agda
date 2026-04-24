{-# OPTIONS --safe --without-K --lossy-unification #-}

--------------------------------------------------------------------------------
-- Triangle coherence axiom:  `id ⊗ λ⇒ ∘ α⇒ ≈Term ρ⇒ ⊗ id`.
--
-- Constructive proof.  The plan:
--
-- LHS = ⟪ id {A} ⊗₁ λ⇒ {B} ∘ α⇒ {A} {unit} {B} ⟫
--     = hComposeP ⟪ α⇒ {A} {unit} {B} ⟫ (hTensor (hId A) (hId B))
--     = hComposeP ⟪ α⇒ {A} {unit} {B} ⟫ (hId (A ⊗₀ B))       -- hId on ⊗ unfolds
--     ≅ᴴ ⟪ α⇒ {A} {unit} {B} ⟫                                -- hCompose-hId-R-iso-generic
--     = subst₂ _ refl (++-assoc (flatten A) [] (flatten B))
--                      (hId ((A ⊗₀ unit) ⊗₀ B))
--
-- RHS = ⟪ ρ⇒ {A} ⊗₁ id {B} ⟫
--     = hTensor (subst₂ _ refl (++-identityʳ (flatten A)) (hId (A ⊗₀ unit))) (hId B)
--     ≡  subst₂ _ refl (cong (_++ flatten B) (++-identityʳ (flatten A)))
--                      (hTensor (hId (A ⊗₀ unit)) (hId B))    -- hTensor-subst₂-left
--     ≡  subst₂ _ refl (cong (_++ flatten B) (++-identityʳ (flatten A)))
--                      (hId ((A ⊗₀ unit) ⊗₀ B))              -- hId on ⊗
--
-- The two sides differ only in the proof of
-- `(flatten A ++ []) ++ flatten B ≡ flatten A ++ flatten B`:
--   * LHS uses `++-assoc (flatten A) [] (flatten B)`.
--   * RHS uses `cong (_++ flatten B) (++-identityʳ (flatten A))`.
--
-- These are propositionally equal; provable by induction on `flatten A`.
-- With that identity, `subst`-transporting on the proof equation bridges
-- the two `subst₂` values via `refl-≅ᴴ`, after stripping the outer
-- `hCompose-hId-R`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Triangle (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor; hEmpty)
open import Categories.APROP.Hypergraph.Translation sig
  using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.SoundnessProved sig
  using (hCompose-hId-R-iso-generic)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- List-level identity used by the triangle law.
--
-- `++-assoc xs [] ys` and `cong (_++ ys) (++-identityʳ xs)` are both proofs
-- of `(xs ++ []) ++ ys ≡ xs ++ ys`.  They are propositionally equal, by
-- induction on `xs`.

++-assoc-[]-id
  : ∀ {A : Set} (xs ys : List A)
  → ++-assoc xs [] ys ≡ cong (_++ ys) (++-identityʳ xs)
++-assoc-[]-id []       ys = refl
++-assoc-[]-id (x ∷ xs) ys =
  -- `++-assoc (x ∷ xs) [] ys = cong (x ∷_) (++-assoc xs [] ys)`
  -- and
  -- `cong (_++ ys) (++-identityʳ (x ∷ xs))
  --    = cong (_++ ys) (cong (x ∷_) (++-identityʳ xs))
  --    = cong (x ∷_) (cong (_++ ys) (++-identityʳ xs))`       (cong-∘ flip)
  trans (cong (cong (x ∷_)) (++-assoc-[]-id xs ys))
        (cong-swap (++-identityʳ xs))
  where
    -- `cong (x ∷_) (cong (_++ ys) p) ≡ cong (_++ ys) (cong (x ∷_) p)`.
    -- Both sides equal `cong (λ z → x ∷ (z ++ ys)) p` because
    -- `(x ∷ z) ++ ys = x ∷ (z ++ ys)` computes.
    cong-swap : ∀ {a b : List _} (p : a ≡ b)
              → cong (x ∷_) (cong (_++ ys) p) ≡ cong (_++ ys) (cong (x ∷_) p)
    cong-swap refl = refl

--------------------------------------------------------------------------------
-- `hTensor` commutes with `subst₂` on the left argument's boundaries.

hTensor-subst₂-left
  : ∀ {As As' Bs Bs' Cs Ds : List X}
      (p : As ≡ As') (q : Bs ≡ Bs')
      (X₀ : Hypergraph FlatGen As Bs) (Y₀ : Hypergraph FlatGen Cs Ds)
  → hTensor (subst₂ (Hypergraph FlatGen) p q X₀) Y₀
  ≡ subst₂ (Hypergraph FlatGen) (cong (_++ Cs) p) (cong (_++ Ds) q)
           (hTensor X₀ Y₀)
hTensor-subst₂-left refl refl X₀ Y₀ = refl

--------------------------------------------------------------------------------
-- Triangle proof.
--
-- Use explicit `Hypergraph`-typed annotations to name the LHS and RHS
-- hypergraphs at the same Hypergraph type.  This lets us bridge them
-- via propositional equality without running into the ObjTerm-level
-- discrepancy between `A⊗(unit⊗B)` and `A⊗B` (both flatten to
-- `flatten A ++ flatten B` but are syntactically different).

triangle-sound
  : ∀ {A B}
  → ⟪ id {A} ⊗₁ λ⇒ {B} ∘ α⇒ {A} {unit} {B} ⟫
  ≅ᴴ ⟪ ρ⇒ {A} ⊗₁ id {B} ⟫
triangle-sound {A} {B} =
  trans-≅ᴴ lhs-shape α⟫-≅ᴴ-⟪ρ⇒⊗id
  where
    eqA : flatten A ++ [] ≡ flatten A
    eqA = ++-identityʳ (flatten A)

    -- Explicitly-typed views of each HomTerm's translation.  Agda's
    -- INJECTIVE_FOR_INFERENCE on ⟪_⟫ would otherwise try to invert
    -- `⟪ ρ⇒ ⊗₁ id {B} ⟫`'s type against the context, leading to an
    -- ObjTerm-level mismatch (`A⊗B` vs `A⊗(unit⊗B)`) even though both
    -- flatten to `flatten A ++ flatten B`.  Pinning the Hypergraph
    -- type directly tells Agda to match at the flattened level.
    lhs-hg : Hypergraph FlatGen ((flatten A ++ []) ++ flatten B)
                                 (flatten A ++ flatten B)
    lhs-hg = ⟪ α⇒ {A} {unit} {B} ⟫

    rhs-hg : Hypergraph FlatGen ((flatten A ++ []) ++ flatten B)
                                 (flatten A ++ flatten B)
    rhs-hg = ⟪ ρ⇒ {A} ⊗₁ id {B} ⟫

    -- `⟪ id {A} ⊗₁ λ⇒ {B} ∘ α⇒ {A}{unit}{B} ⟫ = hComposeP lhs-hg (hId (A⊗B))`,
    -- because ⟪id⊗λ⇒⟫ = hTensor (hId A) (hId B) = hId (A⊗B) definitionally
    -- and ⟪_ ∘ _⟫ flips the args.  Strip the hId via hCompose-hId-R.
    lhs-shape : ⟪ id {A} ⊗₁ λ⇒ {B} ∘ α⇒ {A} {unit} {B} ⟫ ≅ᴴ lhs-hg
    lhs-shape = hCompose-hId-R-iso-generic (A ⊗₀ B) lhs-hg

    -- The key propositional step: after simplification both `lhs-hg` and
    -- `rhs-hg` are subst₂'s of `hTensor (hId (A ⊗₀ unit)) (hId B)`, and
    -- their subst-proofs are propositionally equal.
    lhs≡rhs : lhs-hg ≡ rhs-hg
    lhs≡rhs =
      -- `lhs-hg = subst₂ _ refl eqABC G` where G = hTensor (hTensor (hId A) hEmpty) (hId B).
      -- `rhs-hg = hTensor (subst₂ _ refl eqA (hId (A⊗unit))) (hId B)
      --         = subst₂ _ refl (cong (_++ _) eqA) G`       (hTensor-subst₂-left + hId on ⊗)
      -- equal to lhs-hg via `++-assoc-[]-id`.
      trans
        (cong (λ p → subst₂ (Hypergraph FlatGen) refl p
                              (hTensor (hTensor (hId A) hEmpty) (hId B)))
              (++-assoc-[]-id (flatten A) (flatten B)))
        (sym (hTensor-subst₂-left refl eqA
                (hTensor (hId A) hEmpty) (hId B)))

    α⟫-≅ᴴ-⟪ρ⇒⊗id : lhs-hg ≅ᴴ rhs-hg
    α⟫-≅ᴴ-⟪ρ⇒⊗id = subst (lhs-hg ≅ᴴ_) lhs≡rhs (refl-≅ᴴ _)
