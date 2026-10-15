{-# OPTIONS --safe --without-K --guardedness #-}

-- Ordinary Fine tests need not come with certified preimages; this morphism
-- does not assert a security-transfer theorem.
open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Erasure (𝔖 : Signature) where

open import Categories.FreeMonoidal
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.Symbolic.Computational 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖 using (Atom)
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Symbolic.Fine 𝔖 as Fine

module Erasure (sch : Scheme) where
  module Source = CertifiedSource sch
  private module S = Source.Src
  private module Obj = FreeObjInterp Mon Atom (fromMC Fine.𝔻𝕐 noSymmetric) Fine.Var

  erase-object : (A : S.ObjTerm) → Obj.⟦ A ⟧₀ ≡ A
  erase-object S.unit = refl
  erase-object (A S.⊗₀ B) = cong₂ Fine._⊗₀_ (erase-object A) (erase-object B)
  erase-object (S.Var _) = refl

  erasureData : FreeFunctorData Source.certData
  erasureData = record
    { ⟦v⟧ = fromMC Fine.𝔻𝕐 noSymmetric
    ; ⟦_⟧ᵖ₀ = Fine.Var
    ; ⟦_⟧ᵖ₁ = λ { {x} {y} (Source.certified ux uy p _ _) →
        subst₂ Fine.HomTerm (sym (erase-object x)) (sym (erase-object y))
          (Fine.var (ux , uy , p)) } }

  erase : StrongMonoidalFunctor Source.𝔻𝕐ᶜ Fine.𝔻𝕐
  erase = freeStrongMonoidal erasureData

  module F = StrongMonoidalFunctor erase

  erase-test : {A : S.ObjTerm} → Source.Test A → Fine.Test (F.₀ A)
  erase-test (Y , T) = F.₀ Y , F.₁ T

  erase-test-cong : {A : S.ObjTerm} {t u : Source.Test A}
    → Source.SameTerm t u → Fine.SameTerm (erase-test t) (erase-test u)
  erase-test-cong (Source.same e) = Fine.same (F.F-resp-≈ e)

  erase-pull : {A B : S.ObjTerm} (f : S.HomTerm B A) (t : Source.Test A)
    → Fine.SameTerm (erase-test (Source.pull f t)) (Fine.pullᵗ (F.₁ f) (erase-test t))
  erase-pull f (Y , T) = Fine.same Fine.≈-Term-refl

  ν : PresheafMorphism F.F Source.ℰ≅ᶜ Fine.ℰ≅
  ν = record { ν = ntHelper record
    { η = λ A → record
      { to = λ t → lift (erase-test {A} (lower t))
      ; cong = λ e → lift (erase-test-cong {A} (lower e)) }
    ; commute = λ f {t} → lift (erase-pull f (lower t)) } }

  certified→fine : UCSetupMorphism Source.Sym≅ᶜ.StdSetup Fine.Sym≅.StdSetup
  certified→fine = StdUCMorphism Source.𝔻𝕐ᶜ Fine.𝔻𝕐 Source.ℰ≅ᶜ Fine.ℰ≅ erase ν
