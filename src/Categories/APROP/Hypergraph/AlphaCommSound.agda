{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- α-naturality for the APROP-to-hypergraph translation.
--
-- Proves `α-comm-sound : ⟪ α⇒ ∘ (f⊗g)⊗h ⟫ ≅ᴴ ⟪ f⊗(g⊗h) ∘ α⇒ ⟫`
-- constructively, reducing it to one focused postulate
-- `hTensor-assoc-iso` (reusable for triangle, pentagon, hexagon).
--
-- Proof plan:
--   Show both LHS and RHS are ≅ᴴ to a common "mid" form
--     mid = subst₂ _ refl eqBD (hTensor (hTensor ⟪f⟫ ⟪g⟫) ⟪h⟫)
--
--   LHS chain:
--     ⟪α⇒{B,D,F} ∘ (f⊗g)⊗h⟫
--       = hComposeP (hTensor (hTensor ⟪f⟫ ⟪g⟫) ⟪h⟫)
--                   (subst₂ _ refl eqBD (hId ((B⊗D)⊗F)))
--       ≡ subst₂ _ refl eqBD (hComposeP _ (hId _))    [hComposeP-subst-both]
--       ≅ᴴ subst₂ _ refl eqBD (hTensor (hTensor ⟪f⟫ ⟪g⟫) ⟪h⟫) = mid
--                                                      [hCompose-hId-R-iso-generic]
--
--   RHS chain:
--     ⟪f⊗(g⊗h) ∘ α⇒{A,C,E}⟫
--       = hComposeP (subst₂ _ refl eqAC (hId ((A⊗C)⊗E)))
--                   (hTensor ⟪f⟫ (hTensor ⟪g⟫ ⟪h⟫))
--       ≡ hComposeP (hId _) (subst₂ _ (sym eqAC) refl RHS-tree)
--                                                      [hComposeP-subst-both]
--       ≅ᴴ subst₂ _ (sym eqAC) refl RHS-tree           [hCompose-hId-L-iso-generic]
--       ≅ᴴ subst₂ _ (sym eqAC) refl
--            (subst₂ _ eqAC eqBD LHS-tree)             [hTensor-assoc-iso, inverted]
--       ≡ subst₂ _ refl eqBD LHS-tree = mid            [subst₂-cancel-sym-l]
--
-- Because this file uses `hTensor-assoc-iso` as a postulate, it is not
-- `--safe`. The postulate is strictly more informative than
-- `α-comm-sound` since it's a structural claim about tensors (reusable).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.AlphaCommSound (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hId; hTensor)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; hComposeP-subst-both)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)
open import Categories.APROP.Hypergraph.CoherenceHelpers sig
  using (subst₂-cancel-sym-l; subst₂-cancel-sym-r; Unique-subst₂-dom)
open import Categories.APROP.Hypergraph.CoherenceReductions sig
  using (reduce-via-hId-R; reduce-via-hId-L)

open import Data.List using (List; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; subst₂; cong₂)

--------------------------------------------------------------------------------
-- Focused postulate: hTensor associativity up to boundary subst₂.
--
-- Reusable for α-comm, triangle, pentagon, hexagon proofs.  Specialises
-- (at F = hId A, G = hId B, H = hId C) to `subst₂-hId-assoc-cancel`
-- from `SoundnessAxioms` — so this postulate is strictly more general.
--
-- A future constructive proof would go field-by-field through the
-- `nV-subst₂ / vlab-subst₂ / dom-subst₂ / cod-subst₂` helpers, similar to
-- `hTensor-hEmpty-G-iso`. Expected ~100-200 lines.

postulate
  hTensor-assoc-iso
    : ∀ {As Bs Cs As' Bs' Cs' : List X}
        (F : Hypergraph FlatGen As As')
        (G : Hypergraph FlatGen Bs Bs')
        (H : Hypergraph FlatGen Cs Cs')
    → subst₂ (Hypergraph FlatGen)
             (++-assoc As Bs Cs) (++-assoc As' Bs' Cs')
             (hTensor (hTensor F G) H)
    ≅ᴴ hTensor F (hTensor G H)

--------------------------------------------------------------------------------
-- α-naturality.

α-comm-sound
  : ∀ {A B C D E F} {f : HomTerm A B} {g : HomTerm C D} {h : HomTerm E F}
  → ⟪ α⇒ {B} {D} {F} ∘ (f ⊗₁ g) ⊗₁ h ⟫ ≅ᴴ ⟪ f ⊗₁ (g ⊗₁ h) ∘ α⇒ {A} {C} {E} ⟫
α-comm-sound {A} {B} {C} {D} {E} {F} {f} {g} {h} =
  trans-≅ᴴ LHS≅mid (sym-≅ᴴ RHS≅mid)
  where
    eqAC : (flatten A ++ flatten C) ++ flatten E
         ≡ flatten A ++ flatten C ++ flatten E
    eqAC = ++-assoc (flatten A) (flatten C) (flatten E)

    eqBD : (flatten B ++ flatten D) ++ flatten F
         ≡ flatten B ++ flatten D ++ flatten F
    eqBD = ++-assoc (flatten B) (flatten D) (flatten F)

    LHS-tree : Hypergraph FlatGen
                 ((flatten A ++ flatten C) ++ flatten E)
                 ((flatten B ++ flatten D) ++ flatten F)
    LHS-tree = hTensor (hTensor ⟪ f ⟫ ⟪ g ⟫) ⟪ h ⟫

    RHS-tree : Hypergraph FlatGen
                 (flatten A ++ flatten C ++ flatten E)
                 (flatten B ++ flatten D ++ flatten F)
    RHS-tree = hTensor ⟪ f ⟫ (hTensor ⟪ g ⟫ ⟪ h ⟫)

    -- Common middle form.
    mid : Hypergraph FlatGen
            ((flatten A ++ flatten C) ++ flatten E)
            (flatten B ++ flatten D ++ flatten F)
    mid = subst₂ (Hypergraph FlatGen) refl eqBD LHS-tree

    ----------------------------------------------------------------------------
    -- LHS ≅ᴴ mid.

    abstract
      arg-lhs-tree : ⟪ (f ⊗₁ g) ⊗₁ h ⟫ ≡ LHS-tree
      arg-lhs-tree = refl

      arg-α⇒-B : ⟪ α⇒ {B} {D} {F} ⟫
               ≡ subst₂ (Hypergraph FlatGen) refl eqBD (hId ((B ⊗₀ D) ⊗₀ F))
      arg-α⇒-B = refl

    lhs-≡ : ⟪ α⇒ {B} {D} {F} ∘ (f ⊗₁ g) ⊗₁ h ⟫
          ≡ subst₂ (Hypergraph FlatGen) refl eqBD
                   (hComposeP LHS-tree (hId ((B ⊗₀ D) ⊗₀ F)))
    lhs-≡ = trans (cong₂ hComposeP arg-lhs-tree arg-α⇒-B)
                  (hComposeP-subst-both refl refl eqBD LHS-tree
                                        (hId ((B ⊗₀ D) ⊗₀ F)))

    LHS≅mid : ⟪ α⇒ {B} {D} {F} ∘ (f ⊗₁ g) ⊗₁ h ⟫ ≅ᴴ mid
    LHS≅mid = reduce-via-hId-R ((B ⊗₀ D) ⊗₀ F) LHS-tree eqBD lhs-≡

    ----------------------------------------------------------------------------
    -- RHS ≅ᴴ mid.

    -- Bridged form: RHS-tree with the dom-side subst moved onto it.
    RHS-bridged : Hypergraph FlatGen
                    ((flatten A ++ flatten C) ++ flatten E)
                    (flatten B ++ flatten D ++ flatten F)
    RHS-bridged = subst₂ (Hypergraph FlatGen) (sym eqAC) refl RHS-tree

    abstract
      arg-rhs-tree : ⟪ f ⊗₁ (g ⊗₁ h) ⟫ ≡ RHS-tree
      arg-rhs-tree = refl

      arg-α⇒-A : ⟪ α⇒ {A} {C} {E} ⟫
               ≡ subst₂ (Hypergraph FlatGen) refl eqAC (hId ((A ⊗₀ C) ⊗₀ E))
      arg-α⇒-A = refl

    -- Rewrite RHS-tree as `subst₂ eqAC refl RHS-bridged` so hComposeP-subst-both applies.
    rhs-tree-expand : RHS-tree
                    ≡ subst₂ (Hypergraph FlatGen) eqAC refl RHS-bridged
    rhs-tree-expand = sym (subst₂-cancel-sym-r eqAC RHS-tree)

    rhs-≡ : ⟪ f ⊗₁ (g ⊗₁ h) ∘ α⇒ {A} {C} {E} ⟫
          ≡ hComposeP (hId ((A ⊗₀ C) ⊗₀ E)) RHS-bridged
    rhs-≡ = trans (cong₂ hComposeP arg-α⇒-A
                    (trans arg-rhs-tree rhs-tree-expand))
                  (hComposeP-subst-both refl eqAC refl
                                        (hId ((A ⊗₀ C) ⊗₀ E))
                                        RHS-bridged)

    -- Unique witness for RHS-bridged's dom.
    RHS-bridged-dom-unique : Unique (Hypergraph.dom RHS-bridged)
    RHS-bridged-dom-unique =
      Unique-subst₂-dom (sym eqAC) refl RHS-tree
        (⟪_⟫-dom-unique (f ⊗₁ (g ⊗₁ h)))

    -- Step A: RHS ≅ᴴ RHS-bridged (strip the hId on G side).
    RHS≅RHS-bridged : ⟪ f ⊗₁ (g ⊗₁ h) ∘ α⇒ {A} {C} {E} ⟫ ≅ᴴ RHS-bridged
    RHS≅RHS-bridged =
      reduce-via-hId-L ((A ⊗₀ C) ⊗₀ E) RHS-bridged
        RHS-bridged-dom-unique rhs-≡

    -- Step B: RHS-bridged ≅ᴴ mid via hTensor-assoc-iso inverted.
    --
    -- hTensor-assoc-iso ⟪f⟫ ⟪g⟫ ⟪h⟫ :
    --   subst₂ _ eqAC eqBD LHS-tree ≅ᴴ RHS-tree
    --
    -- Apply subst₂-resp-≅ᴴ (sym eqAC) refl to both sides:
    --   subst₂ _ (sym eqAC) refl (subst₂ _ eqAC eqBD LHS-tree)
    --     ≅ᴴ subst₂ _ (sym eqAC) refl RHS-tree = RHS-bridged
    -- The LHS simplifies via subst₂-cancel-sym-l to:
    --   subst₂ _ refl eqBD LHS-tree = mid.
    RHS-bridged≅mid : RHS-bridged ≅ᴴ mid
    RHS-bridged≅mid =
      subst (RHS-bridged ≅ᴴ_) mid-alt≡mid
        (sym-≅ᴴ step-from-tensor-assoc)
      where
        mid-alt : Hypergraph FlatGen
                    ((flatten A ++ flatten C) ++ flatten E)
                    (flatten B ++ flatten D ++ flatten F)
        mid-alt = subst₂ (Hypergraph FlatGen) (sym eqAC) refl
                    (subst₂ (Hypergraph FlatGen) eqAC eqBD LHS-tree)

        mid-alt≡mid : mid-alt ≡ mid
        mid-alt≡mid = subst₂-cancel-sym-l eqAC eqBD LHS-tree

        step-from-tensor-assoc : mid-alt ≅ᴴ RHS-bridged
        step-from-tensor-assoc =
          subst₂-resp-≅ᴴ (sym eqAC) refl
            (hTensor-assoc-iso ⟪ f ⟫ ⟪ g ⟫ ⟪ h ⟫)

    RHS≅mid : ⟪ f ⊗₁ (g ⊗₁ h) ∘ α⇒ {A} {C} {E} ⟫ ≅ᴴ mid
    RHS≅mid = trans-≅ᴴ RHS≅RHS-bridged RHS-bridged≅mid
