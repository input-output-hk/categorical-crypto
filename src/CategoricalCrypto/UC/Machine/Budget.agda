{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.Budget.Budget` at the machine model: the resource doctrine's nine fields,
-- inhabited.
--
-- This is the assembly `UC.Machine.Grading`'s header used to declare owed.  It
-- sits in its own module rather than beside `ucBaseᴹ` for two reasons: the
-- content it plugs comes from `UC.QueryBound` and below, which imports
-- `UC.Machine`; and heavy assemblies get their own module
-- (`docs/protocol-rewrite.md`, perf finding on `Gradingᴹ`).
--
-- The field types remain derived from `gradingᴹ`; spelling a monoidal-level
-- action type here forces conversion through the machine tensor.  `QBᴳ` and
-- the object-indexed laws are opaque nominal boundaries, so this assembly does
-- not re-index an implicit `Iface` pair or unfold the tensor's middle-four
-- composite while checking dependent fields.

open import Categories.Category using (Category; _[_,_])

open import Data.Nat.Base as ℕ using (ℕ)
open import Level using (0ℓ; suc)

open import CategoricalCrypto.Machines.Base using (𝒢ₚ)
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Machine using (gradingᴹ)
open import CategoricalCrypto.UC.Machine.Grading
  using (qb-T₁ᴳ-object; qb-subᴳ-object; qb-a⇒ᴳ-object; qb-a⇐ᴳ-object)
open import CategoricalCrypto.UC.QueryBound.Object
  using (QBᴳ; qb-idᴳ; qb-monoᴳ; qb-resp-≈ᴳ)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘ᴳ)

module CategoricalCrypto.UC.Machine.Budget where

private module 𝒢 = Category (𝒢ₚ 0ℓ)

qb-∘ᴹ : {A B C : 𝒢.Obj} {c c′ : ℕ} {g : 𝒢ₚ 0ℓ [ B , C ]} {f : 𝒢ₚ 0ℓ [ A , B ]}
       → QBᴳ B C c g → QBᴳ A B c′ f → QBᴳ A C (c ℕ.* c′) (g 𝒢.∘ f)
qb-∘ᴹ {A} {B} {C} {c} {c′} {g} {f} = qb-∘ᴳ A B C {c} {c′} g f

budgetᴹ : Budget (𝒢ₚ 0ℓ) gradingᴹ (suc 0ℓ)
budgetᴹ = record
  { QB    = λ c {A} {B} → QBᴳ A B c
  ; qb-id = λ {A} → qb-idᴳ A
  ; qb-∘  = qb-∘ᴹ
  ; qb-resp-≈ = λ {A} {B} {c} {f} {g} → qb-resp-≈ᴳ A B {c} {f} {g}
  ; qb-mono   = λ {A} {B} {c} {c′} {f} → qb-monoᴳ A B {c} {c′} {f}
  ; qb-T₁     = λ {Y} {A} {B} {c} {f} → qb-T₁ᴳ-object Y A B {c} f
  ; qb-sub    = λ {X} {Y} {A} {c} {s} → qb-subᴳ-object X Y A {c} s
  ; qb-a⇒     = λ {X} {Y} {A} → qb-a⇒ᴳ-object X Y A
  ; qb-a⇐     = λ {X} {Y} {A} → qb-a⇐ᴳ-object X Y A
  }
