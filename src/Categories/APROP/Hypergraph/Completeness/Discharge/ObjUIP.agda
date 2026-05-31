{-# OPTIONS --without-K #-}

-- Discharges the `objUIP` postulate from
-- `Categories.APROP.Hypergraph.Completeness.Discharge.DecodeRelRespIsoWired`
-- as a CONDITIONAL theorem:
--
--   objUIP : DecidableEquality X → Irrelevant (_≡_ {A = ObjTerm})
--
-- i.e. uniqueness-of-identity-proofs on `ObjTerm = unit | _⊗₀_ | Var X`,
-- under `--without-K`, given decidable equality on the atom type `X`.
--
-- Route (Hedberg's theorem):
--   1. `DecidableEquality X ⇒ DecidableEquality ObjTerm`, by structural
--      recursion on the three constructors (`ObjTerm-≟`).
--   2. `DecidableEquality A ⇒ UIP A`, via the stdlib Hedberg lemma
--      `Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP.≡-irrelevant`
--      (where `UIP A = Irrelevant {A = A} _≡_`).
--
-- No postulates.  This is the conditional lemma that supplies `objUIP`
-- once `X`-decidable-equality (`sig-dec`) is available; the live chain's
-- `objUIP` is over a bare `sig` with no DecEq, so it is consumed there.

module Categories.APROP.Hypergraph.Completeness.Discharge.ObjUIP where

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.Definitions using (Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Axiom.UniquenessOfIdentityProofs using (UIP)
import Axiom.UniquenessOfIdentityProofs as UIPmod

open import Categories.FreeMonoidal using (Variant)
import Categories.FreeMonoidal as FM

------------------------------------------------------------------------
-- Work generically over a `Variant` and an atom type `X`, so the result
-- specialises to the APROP `ObjTerm` (which is `FreeMonoidalHelper Symm X`).
------------------------------------------------------------------------

module ObjUIP {v : Variant} {X : Set} where

  open FM.FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var)

  ----------------------------------------------------------------------
  -- Step 1: decidable equality on `ObjTerm` from decidable equality on X.
  --
  -- Done by direct structural recursion.  Injectivity of the
  -- constructors (`⊗₀` and `Var`) is recovered by pattern-matching on
  -- `refl`, which is sound under `--without-K`.
  ----------------------------------------------------------------------

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

  ----------------------------------------------------------------------
  -- Step 2: Hedberg.  Decidable equality ⇒ UIP / ≡-irrelevance.
  ----------------------------------------------------------------------

  objUIP : DecidableEquality X → Irrelevant (_≡_ {A = ObjTerm})
  objUIP _≟X_ = UIPmod.Decidable⇒UIP.≡-irrelevant (ObjTerm-≟ _≟X_)

  -- Same statement, packaged as the stdlib `UIP` abbreviation.
  objUIP-UIP : DecidableEquality X → UIP ObjTerm
  objUIP-UIP = objUIP

  -- The exact shape of the discharged postulate in `DecodeRelRespIsoWired`:
  --   objUIP : ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
  objUIP′ : DecidableEquality X → ∀ {a b : ObjTerm} (p q : a ≡ b) → p ≡ q
  objUIP′ _≟X_ {a} {b} p q = objUIP _≟X_ p q
