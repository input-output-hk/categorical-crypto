{-# OPTIONS --safe --without-K #-}

-- Checks of the symbolic layers over `comonlundhcortier2008`'s Σ₀: normal
-- forms, the decided theory, deducibility both ways, the alphabets as the
-- interfaces the semantics reads, and one role run.

module CategoricalCrypto.Symbolic.Test where

open import Categories.FreeMonoidal
open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Unit
open import Function.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary using (∅)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc

import CategoricalCrypto.Symbolic.Deduction as Deduction
import CategoricalCrypto.Symbolic.Role as Role

open Deduction Σ₀ E₀
open EqTheory E₀
open Role Σ₀
open FreeMonoidalHelper Mon Atom
open Run E₀
open Terms Σ₀

private
  m k r : Msg
  m = name (0 , 0)
  k = name (0 , 1)
  r = name (0 , 2)

  c : Msg
  c = enc⟨ m , k , r ⟩

  _ : nf dec⟨ c , k ⟩ ≡ m
  _ = refl

  _ : nf dec⟨ c , m ⟩ ≡ dec⟨ c , m ⟩
  _ = refl

  _ : does (π₂ ⟪ m , c ⟫ ≟E c) ≡ true
  _ = refl

  _ : does (dec⟨ c , m ⟩ ≟E m) ≡ false
  _ = refl

  opened : (c ∷ k ∷ [] , ∅) ⊢ m
  opened = app dec (var (here refl) ∷ var (there (here refl)) ∷ []) , refl

  _ : (c ∷ k ∷ [] , ∅) ⊢ᵢ m
  _ = Equivalence.to ⊢⇔⊢ᵢ opened

  ⟦_⟧ᴵ : ObjTerm → Iface
  ⟦ x ⟧ᴵ = Alphabet pos x ⇿ Alphabet neg x

  _ : ∀ {A B} → ⟦ A ⊗₀ B ⟧ᴵ ≡ ⟦ A ⟧ᴵ ⊗ᴵ ⟦ B ⟧ᴵ
  _ = refl

  _ : ⟦ unit ⟧ᴵ ≡ unitᴵ
  _ = refl

  _ : ⟦ Var verdict ⟧ᴵ ≡ (Bool ⇿ ⊤)
  _ = refl

  wire : ObjTerm
  wire = Var (port tt tt)

  -- On a message from the left, draw a key and coins and emit the ciphertext
  -- to the right; echo anything from the right back to it.
  encrypter : Role wire wire
  encrypter = record
    { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
    ; react = λ where
        zero (here refl)         _ → new tt (new tt (emit zero [] (there (here refl))
          (app enc (var (there (there (here refl))) ∷ var (there (here refl)) ∷ var (here refl) ∷ []))))
        zero (there (here refl)) _ → emit zero [] (there (here refl)) (var (here refl))
    }

  _ : proj₂ (step 7 encrypter (init encrypter) (here refl ↦ m))
    ≡ there (here refl) ↦ enc⟨ m , name (7 , 0) , name (7 , 1) ⟩
  _ = refl

  _ : Known (m ∷ [] , Own 7) (proj₂ (step 7 encrypter (init encrypter) (here refl ↦ m)))
  _ = emits⊢ 7 encrypter [] (here refl ↦ m)
