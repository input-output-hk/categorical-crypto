{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- APROPSignatureDec extension (TensorRocq §4.2, arXiv:2604.17592).
--
-- The hypergraph-isomorphism decision procedure `findIso` needs decidable
-- equality on `X` (atom labels) and on `mor A B` (edge labels).
-- `APROPSignatureDec` wraps an `APROPSignature` with these two fields, and
-- derives `_≟-ObjTerm_` (structural decidable equality, used for comparing
-- labelled arities when matching edges).
--
-- Decidable equality on `FlatGen` itself is avoided (its `flat` constructor
-- is generalised in `A, B` and `flatten` is not injective in general);
-- label comparison is handled at edge-matching time instead.
--------------------------------------------------------------------------------

open import Categories.APROP using (APROPSignature)

module Categories.APROP.Hypergraph.Solver.Signature where

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (map′)

record APROPSignatureDec : Set₁ where
  field
    sig : APROPSignature

  open APROPSignature sig public

  field
    _≟X_    : DecidableEquality X
    _≟-mor_ : ∀ {A B} → DecidableEquality (mor A B)

  -- Derived: decidable equality on `ObjTerm` from `_≟X_`.

  open import Categories.FreeMonoidal
  open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var) public

  private
    ⊗-injˡ : ∀ {A A' B B' : ObjTerm} → (A ⊗₀ B) ≡ (A' ⊗₀ B') → A ≡ A'
    ⊗-injˡ refl = refl

    ⊗-injʳ : ∀ {A A' B B' : ObjTerm} → (A ⊗₀ B) ≡ (A' ⊗₀ B') → B ≡ B'
    ⊗-injʳ refl = refl

    Var-inj : ∀ {x y : X} → Var x ≡ Var y → x ≡ y
    Var-inj refl = refl

  _≟-ObjTerm_ : DecidableEquality ObjTerm
  unit     ≟-ObjTerm unit      = yes refl
  unit     ≟-ObjTerm (_ ⊗₀ _)  = no λ ()
  unit     ≟-ObjTerm Var _     = no λ ()
  (_ ⊗₀ _) ≟-ObjTerm unit      = no λ ()
  (A ⊗₀ B) ≟-ObjTerm (A' ⊗₀ B') with A ≟-ObjTerm A' | B ≟-ObjTerm B'
  ... | yes p | yes q = yes (cong₂ _⊗₀_ p q)
  ... | yes _ | no ¬q = no (λ eq → ¬q (⊗-injʳ eq))
  ... | no ¬p | _     = no (λ eq → ¬p (⊗-injˡ eq))
  (_ ⊗₀ _) ≟-ObjTerm Var _     = no λ ()
  Var _    ≟-ObjTerm unit      = no λ ()
  Var _    ≟-ObjTerm (_ ⊗₀ _)  = no λ ()
  Var x    ≟-ObjTerm Var y     = map′ (cong Var) Var-inj (x ≟X y)
