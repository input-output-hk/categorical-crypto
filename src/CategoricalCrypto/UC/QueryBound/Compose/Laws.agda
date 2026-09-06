{-# OPTIONS --safe --without-K --guardedness #-}

-- `BudgetLawsᴹ`, assembled.  The two hypotheses are the ones `qb-T₁ᴹ`/`qb-subᴹ`
-- already take: `T₁ᴵ`/`subᴵ` respect `_≈_`, which `UC.Machine.Dictionary`
-- proves.  Every implicit is PINNED, and the section is its own module, for the
-- reason `UC.Machine.Grading`'s header records: each field pays the `Proc`
-- inversion once.  Measured warm cost ~220 s for these 27 lines, which is what
-- that per-field price looks like.

open import Categories.Category using (_[_≈_])

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; T₁ᴵ; subᴵ)
open import CategoricalCrypto.UC.QueryBound
  using (QB; BudgetLawsᴹ; qb-idᴹ; qb-T₁ᴹ; qb-subᴹ)
open import CategoricalCrypto.UC.QueryBound.Compose.Step using (qb-∘)

module CategoricalCrypto.UC.QueryBound.Compose.Laws where

budgetLawsᴹ : ({Y A B : Iface} {f g : Proc A B} → 𝒫ᴵ [ f ≈ g ] → 𝒫ᴵ [ T₁ᴵ Y f ≈ T₁ᴵ Y g ])
            → ({X Y A : Iface} {s t : Proc X Y} → 𝒫ᴵ [ s ≈ t ] → 𝒫ᴵ [ subᴵ s {A} ≈ subᴵ t ])
            → BudgetLawsᴹ
budgetLawsᴹ rT rS = record
  { qb-id  = λ {A} → qb-idᴹ {A}
  ; qb-∘   = λ {A} {B} {C} {c} {c′} {g} {f} → qb-∘ A B C {c} {c′} g f
  ; qb-T₁  = λ {Y} {A} {B} {c} {f} → qb-T₁ᴹ rT Y A B {c} f
  ; qb-sub = λ {X} {Y} {A} {c} {s} → qb-subᴹ rS X Y A {c} s
  }
