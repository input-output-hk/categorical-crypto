{-# OPTIONS --safe --without-K #-}

-- Environment agreement with an explicit slack, and its collapse.
--
-- `UC.Environment._≈ℰ_` is where a security statement LANDS; `_≈ℰ[ ε ]_` is
-- where one is PROVED, the error still visible.  `absorbᵘ` is `induces` read at
-- the environment level: closeness at every positive error is agreement.
--
-- The budget the slack is allowed to depend on is not here — a general
-- approximate observation has no resource doctrine.  It appears one layer up,
-- where the error is a function of the security parameter and of the context's
-- carried query bound (`UC.Family._≈ℰ[_]_`, whose `absorb` is this collapse
-- with a vanishing bound supplying the errors).

open import Level using (Level; _⊔_)

open import CategoricalCrypto.UC.Approximate using (ApproximateObservation; ErrorAlgebra)
open import CategoricalCrypto.UC.Core using (UCBase)

module CategoricalCrypto.UC.Environment.Approximate
  {o ℓ e os ℓs es ℓe ℓa : Level} (base : UCBase o ℓ e os ℓs)
  {Err : ErrorAlgebra es ℓe}
  (approx : ApproximateObservation (UCBase.observation base) Err ℓa) where

open import CategoricalCrypto.UC.Environment base

open ApproximateObservation approx

private variable A B′ : Obj

infix 4 _≈ℰ[_]_

_≈ℰ[_]_ : {A B′ : Obj} → A ⇒ B′ → Error → A ⇒ B′ → Set (o ⊔ ℓ ⊔ ℓa)
_≈ℰ[_]_ {A} {B′} f ε g = (Y : Obj) (Et : Test (Y ⊛ B′)) (m : Closure (Y ⊛ A))
                       → obs (tv₁ Y f Et) m ≈[ ε ] obs (tv₁ Y g Et) m

absorbᵘ : {f g : A ⇒ B′} → ((ε : Error) → Positive ε → f ≈ℰ[ ε ] g) → f ≈ℰ g
absorbᵘ h Y Et m = induces λ ε pos → h ε pos Y Et m
