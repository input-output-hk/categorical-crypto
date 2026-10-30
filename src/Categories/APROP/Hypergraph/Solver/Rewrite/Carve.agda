{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Term-level focusing. Candidates are certified downstream by findIso;
-- redexes hidden by global SMC rearrangement need the subMatch/decode route.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Rewrite.Carve (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Translation sig
open import Categories.APROP.Hypergraph.Solver.Match.FindIso sig

open import Data.List.Base
open import Data.List.Properties.Ext
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open APROP sig

private
  variable
    A B P Q : ObjTerm

Foc : ObjTerm → ObjTerm → ObjTerm → ObjTerm → Set
Foc A B P Q = Σ ObjTerm λ k → HomTerm A (k ⊗₀ P) × HomTerm (k ⊗₀ Q) B

leaf-try : HomTerm A B → HomTerm P Q → Maybe (Foc A B P Q)
leaf-try {A} {B} {P} {Q} s lᵗ with A ≟-ObjTerm P | B ≟-ObjTerm Q
... | yes refl | yes refl = Maybe.map (λ _ → unit , λ⇐ , λ⇒)
  (withTranslation s (λ H → withTranslation lᵗ (findIso H)))
leaf-try _ _ | _ | _ = nothing

-- Whole-term first, then right-to-left within composition and tensor.

focusAll : HomTerm A B → HomTerm P Q → List (Foc A B P Q)

go-all : HomTerm A B → HomTerm P Q → List (Foc A B P Q)
go-all (g ∘ f) lᵗ =
     map (λ { (k , pre , post) → (k , pre , g ∘ post) }) (focusAll f lᵗ)
  ++ map (λ { (k , pre , post) → (k , pre ∘ f , post) }) (focusAll g lᵗ)
go-all (_⊗₁_ {A₁} {_} {A₂} a b) lᵗ =
     map (λ { (k , pre , post) →
            (A₁ ⊗₀ k , α⇐ ∘ (id {A₁} ⊗₁ pre) , (a ⊗₁ post) ∘ α⇒) })
         (focusAll b lᵗ)
  ++ map (λ { (k , pre , post) →
            -- Route b's wire left so the redex remains rightmost.
            ( k ⊗₀ A₂
            , α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ∘ (pre ⊗₁ id {A₂})
            , (post ⊗₁ b) ∘ α⇐ ∘ (id {k} ⊗₁ σ) ∘ α⇒ ) })
         (focusAll a lᵗ)
go-all _ _ = []

focusAll s lᵗ with leaf-try s lᵗ
... | just r  = r ∷ go-all s lᵗ
... | nothing = go-all s lᵗ

focusAtₙ : HomTerm A B → HomTerm P Q → ℕ → Maybe (Foc A B P Q)
focusAtₙ s lᵗ n = lookupMaybe (focusAll s lᵗ) n

focusAt : HomTerm A B → HomTerm P Q → Maybe (Foc A B P Q)
focusAt s lᵗ = focusAtₙ s lᵗ 0
