{-# OPTIONS --safe --without-K #-}

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Frontend.Rewrite (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Solver.Frontend.Core sig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Balance sig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Carve sig
open import Categories.APROP.Hypergraph.Solver.Rewrite.Deep sig
open import Categories.Category.Monoidal.Bundle
open import Categories.FreeMonoidal

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base

open APROP sig

private variable A B P Q : ObjTerm

-- Matching the outer Maybe keeps abstract frames neutral and shares the
-- position search across projections. Matching its inner Σ eta-reduces,
-- exposing the translated frame before a concrete position is available.
--
-- Balanced deep-context spines keep the hComposeP construction logarithmic
-- in depth; term-level focuses use the identity normaliser.
frameM : (bal : ∀ {C D} → HomTerm C D → HomTerm C D)
         (mid : HomTerm P Q) (m : Maybe (Foc A B P Q)) → T (is-just m) → HomTerm A B
frameM bal mid (just (k , pre , post)) _ = bal post ∘ (id {k} ⊗₁ mid) ∘ bal pre
frameM bal mid nothing ()

focFrame : (s : HomTerm A B) (lᵗ : HomTerm P Q) (mid : HomTerm P Q)
         → (n : ℕ) → T (is-just (focusAtₙ s lᵗ n)) → HomTerm A B
focFrame s lᵗ mid n found = frameM (λ h → h) mid (focusAtₙ s lᵗ n) found

deepFrame : (s : HomTerm A B) (lᵗ : HomTerm P Q) (mid : HomTerm P Q)
          → (n : ℕ) → T (is-just (deepFocₙ s lᵗ n)) → HomTerm A B
deepFrame s lᵗ mid n found = frameM reassocBal mid (deepFocₙ s lᵗ n) found

module Rewrite {o ℓ e} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  (let ⟦v⟧ = fromMC {v = Symm} C.monoidalCategory (λ ⦃ _ ⦄ → C.symmetric))
  (⟦_⟧ᵖ₀ : X → C.Obj)
  (let open FreeObjInterp Symm X ⟦v⟧ ⟦_⟧ᵖ₀ using (⟦_⟧₀))
  (⟦_⟧ᵖ₁ : ∀ {x y} → mor x y → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀)
  where

  open Target C ⟦_⟧ᵖ₀ ⟦_⟧ᵖ₁

  -- Match frameM's same scrutinee to reduce its neutral frame.
  frame-rule-step
    : (bal : ∀ {C D} → HomTerm C D → HomTerm C D)
      (lᵗ rᵗ : HomTerm P Q) → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → (m : Maybe (Foc A B P Q)) (found : T (is-just m))
    → ⟦ frameM bal lᵗ m found ⟧₁ C.≈ ⟦ frameM bal rᵗ m found ⟧₁
  frame-rule-step bal lᵗ rᵗ rule (just (k , pre , post)) _ =
    C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , rule)))
  frame-rule-step bal lᵗ rᵗ rule nothing ()
