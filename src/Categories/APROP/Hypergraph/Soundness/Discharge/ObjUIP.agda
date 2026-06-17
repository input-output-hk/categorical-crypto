{-# OPTIONS --safe --without-K #-}

-- UIP on `ObjTerm` from decidable equality on the atom type `X`
-- (Hedberg), under `--without-K`:
--   1. `DecidableEquality X ⇒ DecidableEquality ObjTerm` (`ObjTerm-≟`),
--   2. `DecidableEquality A ⇒ UIP A` via stdlib's Hedberg lemma.

module Categories.APROP.Hypergraph.Soundness.Discharge.ObjUIP where

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.Definitions using (Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
import Axiom.UniquenessOfIdentityProofs as UIPmod

open import Categories.FreeMonoidal using (Variant)
import Categories.FreeMonoidal as FM

-- Generic over a `Variant` and atom type `X`, so it specialises to the
-- APROP `ObjTerm` (`FreeMonoidalHelper Symm X`).
module ObjUIP {v : Variant} {X : Set} where

  open FM.FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var)

  -- Step 1: decidable equality on `ObjTerm`, by structural recursion.
  ObjTerm-≟ : DecidableEquality X → DecidableEquality ObjTerm

  ObjTerm-≟ _≟X_ unit       unit       = yes refl
  ObjTerm-≟ _≟X_ unit       (b₁ ⊗₀ b₂) = no λ ()
  ObjTerm-≟ _≟X_ unit       (Var _)    = no λ ()

  ObjTerm-≟ _≟X_ (a₁ ⊗₀ a₂) unit       = no λ ()
  ObjTerm-≟ _≟X_ (a₁ ⊗₀ a₂) (Var _)    = no λ ()
  ObjTerm-≟ _≟X_ (a₁ ⊗₀ a₂) (b₁ ⊗₀ b₂)
    with ObjTerm-≟ _≟X_ a₁ b₁ | ObjTerm-≟ _≟X_ a₂ b₂
  ... | yes refl | yes refl = yes refl
  ... | no  a₁≢b₁ | _       = no λ where refl → a₁≢b₁ refl
  ... | _         | no a₂≢b₂ = no λ where refl → a₂≢b₂ refl

  ObjTerm-≟ _≟X_ (Var _)    unit       = no λ ()
  ObjTerm-≟ _≟X_ (Var _)    (_ ⊗₀ _)   = no λ ()
  ObjTerm-≟ _≟X_ (Var x)    (Var y)    with x ≟X y
  ... | yes refl = yes refl
  ... | no  x≢y  = no λ where refl → x≢y refl

  -- Step 2: Hedberg.  Decidable equality ⇒ UIP / ≡-irrelevance.
  objUIP : DecidableEquality X → Irrelevant (_≡_ {A = ObjTerm})
  objUIP _≟X_ = UIPmod.Decidable⇒UIP.≡-irrelevant (ObjTerm-≟ _≟X_)

  -- The shape consumed in `DecodeRelRespIsoWired`.
  objUIP′ : DecidableEquality X → ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
  objUIP′ _≟X_ {a} {b} p q = objUIP _≟X_ p q
