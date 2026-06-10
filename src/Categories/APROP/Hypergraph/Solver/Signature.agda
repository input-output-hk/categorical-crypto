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
open import Categories.FreeMonoidal

--------------------------------------------------------------------------------
-- Structural decidable equality on `ObjTerm` over an atom set `X`, derived
-- from decidable equality on `X`.  Factored out (parameterised over `_≟X_`)
-- so it can be reused independently of the `APROPSignatureDec` record — e.g.
-- to discharge UIP obligations when building `mor` out of `ObjTerm` proofs.

module ObjTermDec {X : Set} (_≟X_ : DecidableEquality X) where
  open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var) public

  private
    ⊗-injˡ : ∀ {A A' B B' : ObjTerm} → (A ⊗₀ B) ≡ (A' ⊗₀ B') → A ≡ A'
    ⊗-injˡ refl = refl

    ⊗-injʳ : ∀ {A A' B B' : ObjTerm} → (A ⊗₀ B) ≡ (A' ⊗₀ B') → B ≡ B'
    ⊗-injʳ refl = refl

    Var-inj : ∀ {x y : X} → Var x ≡ Var y → x ≡ y
    Var-inj refl = refl

  ≟-ObjTerm : DecidableEquality ObjTerm
  ≟-ObjTerm unit     unit       = yes refl
  ≟-ObjTerm unit     (_ ⊗₀ _)   = no λ ()
  ≟-ObjTerm unit     (Var _)    = no λ ()
  ≟-ObjTerm (_ ⊗₀ _) unit       = no λ ()
  ≟-ObjTerm (A ⊗₀ B) (A' ⊗₀ B') with ≟-ObjTerm A A' | ≟-ObjTerm B B'
  ... | yes p | yes q = yes (cong₂ _⊗₀_ p q)
  ... | yes _ | no ¬q = no (λ eq → ¬q (⊗-injʳ eq))
  ... | no ¬p | _     = no (λ eq → ¬p (⊗-injˡ eq))
  ≟-ObjTerm (_ ⊗₀ _) (Var _)    = no λ ()
  ≟-ObjTerm (Var _)  unit       = no λ ()
  ≟-ObjTerm (Var _)  (_ ⊗₀ _)   = no λ ()
  ≟-ObjTerm (Var x)  (Var y)    = map′ (cong Var) Var-inj (x ≟X y)

record APROPSignatureDec : Set₁ where
  field
    sig : APROPSignature

  open APROPSignature sig public

  field
    _≟X_    : DecidableEquality X
    _≟-mor_ : ∀ {A B} → DecidableEquality (mor A B)

  -- Derived: decidable equality on `ObjTerm` from `_≟X_`.
  open ObjTermDec _≟X_ public using (ObjTerm; unit; _⊗₀_; Var)

  _≟-ObjTerm_ : DecidableEquality ObjTerm
  _≟-ObjTerm_ = ObjTermDec.≟-ObjTerm _≟X_
