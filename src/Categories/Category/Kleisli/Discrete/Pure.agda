{-# OPTIONS --safe --without-K #-}

-- The pure morphisms of `Klᴹ` — those `≈ᵏ`-equal to a `return`-composed
-- function — form a wide symmetric monoidal subcategory.  This is the class
-- iteration transfers along: a pure map may be replayed on both sides of a loop
-- because replaying it duplicates no effect.
--
-- The witness is packaged as a record rather than a `Σ`, and `fn` is
-- existential rather than definitional: a composite of structural morphisms is
-- only `≈ᵏ`-pure, the junction delays of `_>>=_` standing between it and its
-- underlying function.

open import Categories.Category.Monoidal.Pure using (PureSub)
open import Categories.Monad.Discrete using (DiscreteMonad)

import Categories.Category.Kleisli.Discrete as KD

open import Data.Product.Base using (proj₁; proj₂; map; swap; assocʳ′)
open import Function.Base using (id; _∘_)

module Categories.Category.Kleisli.Discrete.Pure {ℓ} (Mo : DiscreteMonad ℓ) where

open DiscreteMonad Mo
open KD Mo

private variable A B C D : Set ℓ

record IsPure (f : A → M B) : Set ℓ where
  field
    fn    : A → B
    is-fn : f ≈ᵏ pureᵏ fn

open IsPure

structural : (h : A → B) → IsPure (pureᵏ h)
structural h = record { fn = h ; is-fn = λ _ → ≈ᴹ.refl }

∘-pure : {f : B → M C} {g : A → M B} → IsPure f → IsPure g → IsPure (f <=< g)
∘-pure {f = f} {g} p q = record
  { fn    = fn p ∘ fn q
  ; is-fn = λ a → ≈ᴹ.trans (>>=-cong (is-fn q a) (is-fn p)) >>=-identityˡ-≈
  }

⊗-pure : {f : A → M B} {g : C → M D} → IsPure f → IsPure g → IsPure (f ⊗ᵏ g)
⊗-pure {f = f} {g} p q = record
  { fn    = map (fn p) (fn q)
  ; is-fn = λ r → ≈ᴹ.trans (>>=-cong (is-fn p (proj₁ r))
                                     (λ _ → >>=-cong-x (is-fn q (proj₂ r))))
                           (pureᵏ-⊗ (fn p) (fn q) r)
  }

PureSubᵏ : PureSub Klᴹ-SymmetricMonoidal
PureSubᵏ = record
  { Pure    = IsPure
  ; pure-id = structural id
  ; pure-∘  = ∘-pure
  ; pure-⊗₁ = ⊗-pure
  ; pure-λ⇒ = structural proj₂
  ; pure-ρ⇒ = structural proj₁
  ; pure-α⇒ = structural assocʳ′
  ; pure-σ⇒ = structural swap
  }
