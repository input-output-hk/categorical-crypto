{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Phase 4a.0: APROPSignatureDec extension (TensorRocq §4.2, arXiv:2604.17592).
--
-- The decision procedure `findIso` for hypergraph isomorphism needs:
--   (1) decidable equality on `X` (atom labels, for vertex-label matching
--       and interface seeding), and
--   (2) decidable equality on `mor A B` (edge labels, for edge matching).
--
-- `APROPSignatureDec` wraps an existing `APROPSignature` and bolts on
-- these two extra fields. Existing `APROPSignature`-parameterised
-- modules (soundness, Triangle, Pentagon, SigmaNat, …) are untouched
-- and keep working unchanged. Only the solver (4a.1–4a.6) and the
-- `smcat` tactic (Phase 4b) need `APROPSignatureDec`.
--
-- We also derive `_≟-ObjTerm_` : DecidableEquality ObjTerm, from
-- `_≟X_`. It is a straightforward structural decidable equality on
-- the ObjTerm data type, and the solver uses it for comparing
-- labelled arities when matching edges.
--
-- Decidable equality on `FlatGen` itself is trickier (the constructor
-- `flat : ∀ {A B} → mor A B → FlatGen (flatten A) (flatten B)` is
-- generalised in `A, B`, and `flatten` is not injective in general).
-- We handle label comparison at edge-matching time (Phase 4a.3)
-- rather than as a generic `_≟-FlatGen_`.
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

  --------------------------------------------------------------------------
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
