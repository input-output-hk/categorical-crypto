{-# OPTIONS --safe --without-K --guardedness #-}

-- `BudgetLawsᴹ`, assembled.  The two hypotheses are the ones `qb-T₁ᴹ`/`qb-subᴹ`
-- already take: `T₁ᴵ`/`subᴵ` respect `_≈_`, which `UC.Machine.Dictionary`
-- proves.  Every implicit is PINNED, and the section is its own module, for the
-- reason `UC.Machine.Grading`'s header records: each field pays the `Proc`
-- inversion once.  The hom-level composition closure lives here as its only
-- consumer; `Compose.Step` therefore need not load composite congruence.
-- Measured warm cost with congruence cached: 10.1 s.

open import Categories.Category using (_[_≈_])

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; T₁ᴵ; subᴵ)
open import CategoricalCrypto.UC.QueryBound
  using (QB; BudgetLawsᴹ; qb-resp-≈; qb-idᴹ; qb-T₁ᴹ; qb-subᴹ)
open import CategoricalCrypto.UC.QueryBound.Compose.Step using (qbᵢ-∘)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Collapse.Congruence as ColCong

module CategoricalCrypto.UC.QueryBound.Compose.Laws where

qb-∘ : (A B C : Iface) {c c′ : ℕ} (g : Proc B C) (f : Proc A B)
     → QB {B} {C} c g → QB {A} {B} c′ f
     → QB {A} {C} (c ℕ.* c′)
         (Col.MT.traceᴹ (Pos A ⊎ Neg C) (Neg A ⊎ Pos C) (Neg B ⊎ Pos B)
           (Col.W.α Col.MC.∘ᴹ ((g Col.T.⊗ᵉ f) Col.MC.∘ᴹ Col.W.γ)) )
qb-∘ A B C g f (Ng , cg , eg) (Nf , cf , ef) =
  qb-resp-≈ {A} {C}
    (ColCong.compose-resp-≈ᴹ {Pos A} {Neg A} {Pos B} {Neg B} {Pos C} {Neg C} eg ef)
    (qbᵢ-∘ A B C Ng Nf cg cf)

budgetLawsᴹ : ({Y A B : Iface} {f g : Proc A B} → 𝒫ᴵ [ f ≈ g ] → 𝒫ᴵ [ T₁ᴵ Y f ≈ T₁ᴵ Y g ])
            → ({X Y A : Iface} {s t : Proc X Y} → 𝒫ᴵ [ s ≈ t ] → 𝒫ᴵ [ subᴵ s {A} ≈ subᴵ t ])
            → BudgetLawsᴹ
budgetLawsᴹ rT rS = record
  { qb-id  = λ {A} → qb-idᴹ {A}
  ; qb-∘   = λ {A} {B} {C} {c} {c′} {g} {f} → qb-∘ A B C {c} {c′} g f
  ; qb-T₁  = λ {Y} {A} {B} {c} {f} → qb-T₁ᴹ rT Y A B {c} f
  ; qb-sub = λ {X} {Y} {A} {c} {s} → qb-subᴹ rS X Y A {c} s
  }
