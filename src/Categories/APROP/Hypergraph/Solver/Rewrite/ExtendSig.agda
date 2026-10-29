{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Extend a signature with one hole generator for context carving.
-- The atom alphabet is unchanged; decoded hole-free contexts retract to sig.
--------------------------------------------------------------------------------

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Solver.Rewrite.ExtendSig
  (sig : APROPSignature)
  (let open APROPSignature sig)
  (let open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var))
  (P Q : ObjTerm)
  where

open import Categories.APROP.Hypergraph.Model.FromAPROP sig
open import Data.Maybe.Base
open import Relation.Binary.Definitions
open import Relation.Nullary

-- Equality indices keep hole case splits possible under without-K;
-- decidable ObjTerm equality makes those proofs unique.

data Mor⁺ : ObjTerm → ObjTerm → Set where
  old  : ∀ {A B} → mor A B → Mor⁺ A B
  hole : ∀ {A B} → A ≡ P → B ≡ Q → Mor⁺ A B

hole! : Mor⁺ P Q
hole! = hole refl refl

private
  old-inj : ∀ {A B} {f g : mor A B} → old f ≡ old g → f ≡ g
  old-inj refl = refl

_≟-Mor⁺_ : ∀ {A B} → DecidableEquality (Mor⁺ A B)
old f    ≟-Mor⁺ old g     = map′ (cong old) old-inj (f ≟-mor g)
old f    ≟-Mor⁺ hole _ _  = no λ ()
hole _ _ ≟-Mor⁺ old g     = no λ ()
hole p q ≟-Mor⁺ hole p' q' = yes (cong₂ hole (uip-ObjTerm p p') (uip-ObjTerm q q'))

sig⁺ : APROPSignature
sig⁺ = record { X = X ; mor = Mor⁺ ; _≟X_ = _≟X_ ; _≟-mor_ = _≟-Mor⁺_ }

import Categories.APROP.Hypergraph.Model.FromAPROP sig⁺ as F⁺
open APROP sig using (HomTerm; Agen; id; _∘_; _⊗₁_; λ⇒; λ⇐; ρ⇒; ρ⇐; α⇒; α⇐; σ)
open APROP sig⁺ using ()
  renaming ( HomTerm to HomTerm⁺ ; Agen to Agen⁺ ; id to id⁺ ; _∘_ to _∘⁺_
           ; _⊗₁_ to _⊗₁⁺_ ; λ⇒ to λ⇒⁺ ; λ⇐ to λ⇐⁺ ; ρ⇒ to ρ⇒⁺ ; ρ⇐ to ρ⇐⁺
           ; α⇒ to α⇒⁺ ; α⇐ to α⇐⁺ ; σ to σ⁺ )

relabel : ∀ {As Bs} → FlatGen As Bs → F⁺.FlatGen As Bs
relabel (flat-rec oa ob f) = F⁺.flat-rec oa ob (old f)



retract : ∀ {A B} → HomTerm⁺ A B → Maybe (HomTerm A B)
retract (Agen⁺ (old f))    = just (Agen f)
retract (Agen⁺ (hole _ _)) = nothing
retract id⁺             = just id
retract (g ∘⁺ f)        = zipWith _∘_  (retract g) (retract f)
retract (f ⊗₁⁺ g)       = zipWith _⊗₁_ (retract f) (retract g)
retract λ⇒⁺             = just λ⇒
retract λ⇐⁺             = just λ⇐
retract ρ⇒⁺             = just ρ⇒
retract ρ⇐⁺             = just ρ⇐
retract α⇒⁺             = just α⇒
retract α⇐⁺             = just α⇐
retract σ⁺              = just σ
