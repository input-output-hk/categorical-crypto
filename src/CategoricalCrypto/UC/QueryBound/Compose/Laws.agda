{-# OPTIONS --safe --without-K --guardedness #-}

-- The composition closure of `QB`, at the hom level and at 𝒢's own objects —
-- what `UC.Machine.Grading.gradingᴹ` plugs into the graded subcategory's `pred-∘`.
-- Every implicit is PINNED, and the section is its own module, for the reason
-- `UC.Machine.Grading`'s header records: each field pays the `Proc` inversion
-- once.  Measured warm cost: 10 s.

open import Categories.Category

open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_)
open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Compose.Step
open import CategoricalCrypto.UC.QueryBound.Object

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.UC.QueryBound.Compose.Laws where

private module 𝒢 = Category (𝒢ₚ 0ℓ)

qb-∘ : (A B C : Iface) {c c′ : ℕ} (g : Proc B C) (f : Proc A B)
     → QB {B} {C} c g → QB {A} {B} c′ f
     → QB {A} {C} (c ℕ.* c′)
         (Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
           (Col.W.α Pw.MC.∘ᴹ ((g Pw.T.⊗ᵉ f) Pw.MC.∘ᴹ Col.W.γ)))
qb-∘ A B C g f (Ng , cg , eg) (Nf , cf , ef) =
  qb-resp-≈ {A} {C}
    (Col.compose-raw≈∘ᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} Ng Nf
     Pw.S.○ᴹ 𝒢.∘-resp-≈ {Pos A , Neg A} {Pos B , Neg B} {Pos C , Neg C} eg ef
     Pw.S.○ᴹ Pw.S.⟺ᴹ (Col.compose-raw≈∘ᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} g f))
    (qbᵢ-∘ A B C Ng Nf cg cf)

qb-∘-category : (A B C : Iface) {c c′ : ℕ}
              → (g : 𝒢ₚ 0ℓ [ (Pos B , Neg B) , (Pos C , Neg C) ])
              → (f : 𝒢ₚ 0ℓ [ (Pos A , Neg A) , (Pos B , Neg B) ])
              → QB {B} {C} c g → QB {A} {B} c′ f
              → QB {A} {C} (c ℕ.* c′)
                  (𝒢._∘_ {Pos A , Neg A} {Pos B , Neg B} {Pos C , Neg C} g f)
qb-∘-category A B C {c} {c′} g f qg qf =
  qb-resp-≈ {A} {C}
    (Col.compose-raw≈∘ᴳ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} g f)
    (qb-∘ A B C {c} {c′} g f qg qf)

opaque
  unfolding QBᴳ

  qb-∘ᴳ : (A B C : 𝒢.Obj) {c c′ : ℕ} (g : 𝒢ₚ 0ℓ [ B , C ]) (f : 𝒢ₚ 0ℓ [ A , B ])
        → QBᴳ B C c g → QBᴳ A B c′ f → QBᴳ A C (c ℕ.* c′) (g 𝒢.∘ f)
  qb-∘ᴳ (A⁺ , A⁻) (B⁺ , B⁻) (C⁺ , C⁻) {c} {c′} g f qg qf =
    qb-∘-category (retᴵ (A⁺ , A⁻)) (retᴵ (B⁺ , B⁻)) (retᴵ (C⁺ , C⁻))
      {c} {c′} g f qg qf
