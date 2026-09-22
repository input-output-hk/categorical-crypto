{-# OPTIONS --safe --without-K --guardedness #-}

-- The certificate the compiled closed context carries, at the allowance
-- `UC.Quantitative.EventLift` reads its hypothesis at.
--
-- Its own module because the term is a five-fold `qb-∘` tower over
-- `qb-compileᴹ` (`docs/event-bounds-in-setup.md` §B), and the lift itself
-- must not pay for normalizing it.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (*-identityʳ)
open import Data.Sum.Base using ([_,_]; inj₂)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (subst)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine using (Proc; 𝒫ᴵ; Ωᴵ; T₁ᴵ)
open import CategoricalCrypto.UC.Machine.Bridge using (λᴵ⇒)
open import CategoricalCrypto.UC.Machine.Dictionary using (T₁-⊗₁)
open import CategoricalCrypto.UC.Machine.Grading using (qb-T₁ᴳ)
open import CategoricalCrypto.UC.Machine.Slide using (Kctx; qb-Kctx)
open import CategoricalCrypto.UC.QueryBound
  using (QB; certified⇒QB; qb-closed; qb-resp-≈; qbᵢ-wire)
open import CategoricalCrypto.UC.QueryBound.Compose.Laws using (qb-∘-category)
open import CategoricalCrypto.UC.Quantitative.EventLift using (openedᴹ)
open import CategoricalCrypto.UC.Quantitative.Hits using (compileᴹ; monitorᴹ; qb-compileᴹ; κμ)

module CategoricalCrypto.UC.Quantitative.EventLift.Budget where

private module 𝒫 = Category 𝒫ᴵ

module _ (Y B : Iface) (report : Neg B → Pos B → Bool) (E : Proc (Y ⊗ᴵ B) Ωᴵ)
         {c : ℕ} (qE : QB c E) where

  qb-opened : QB (κμ c) (openedᴹ Y B report E)
  qb-opened = subst (λ k → QB k (openedᴹ Y B report E)) (*-identityʳ (κμ c))
    (qb-∘-category (Y ⊗ᴵ (unitᴵ ⊗ᴵ B)) (Y ⊗ᴵ B) Ωᴵ
      (compileᴹ Y B (monitorᴹ report) E) (T₁ᴵ Y λᴵ⇒)
      (qb-compileᴹ Y B report E qE)
      (qb-resp-≈ (𝒫.Equiv.sym (T₁-⊗₁ {Y} (λᴵ⇒ {B})))
        (qb-T₁ᴳ Y (unitᴵ ⊗ᴵ B) B λᴵ⇒ (certified⇒QB (qbᵢ-wire [ ⊥-elim , id ] inj₂)))))

  -- The closure spends nothing, so `ctxBudget (κμ c) 0` is `κμ c` and the
  -- second leg of the allowance never enters.
  qb-compiled : (m : Proc unitᴵ (Y ⊗ᴵ unitᴵ)) → QB (κμ c) (Kctx (openedᴹ Y B report E) m)
  qb-compiled m = subst (λ k → QB k (Kctx (openedᴹ Y B report E) m)) (*-identityʳ (κμ c))
                        (qb-Kctx (openedᴹ Y B report E) m qb-opened (qb-closed m))
