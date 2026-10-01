{-# OPTIONS --safe --without-K #-}

-- The pure morphisms of `Klᴹ` (see `Categories.Category.Monoidal.Pure`).  `fn`
-- is existential, not definitional: a composite of structural morphisms is only
-- `≈ᵏ`-pure, the junction delays of `_>>=_` standing between it and its
-- underlying function.

open import Categories.Category.Monoidal.Pure
open import Categories.Monad.Discrete

import Categories.Category.Construction.Kleisli.Discrete as KD

open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂; [_,_])
open import Data.Unit.Polymorphic.Base using (tt)
open import Function.Base

module Categories.Category.Construction.Kleisli.Discrete.Pure {ℓ} (Mo : DiscreteMonad ℓ) where

open DiscreteMonad Mo
open KD Mo

private variable A B C D : Set ℓ

IsPure : (A → M B) → Set ℓ
IsPure {A = A} {B} f = Σ[ h ∈ (A → B) ] f ≈ᵏ pureᵏ h

fn : {f : A → M B} → IsPure f → A → B
fn = proj₁

is-fn : {f : A → M B} (p : IsPure f) → f ≈ᵏ pureᵏ (fn p)
is-fn = proj₂

≈-pure : {f g : A → M B} → f ≈ᵏ g → IsPure f → IsPure g
≈-pure f≈g (h , p) = h , λ a → ≈ᴹ.trans (≈ᴹ.sym (f≈g a)) (p a)

structural : (h : A → B) → IsPure (pureᵏ h)
structural h = h , λ _ → ≈ᴹ.refl

∘-pure : {f : B → M C} {g : A → M B} → IsPure f → IsPure g → IsPure (f <=< g)
∘-pure (h , p) (k , q) = h ∘ k , λ a → ≈ᴹ.trans (>>=-cong (q a) p) >>=-identityˡ-≈

⊗-pure : {f : A → M B} {g : C → M D} → IsPure f → IsPure g → IsPure (f ⊗ᵏ g)
⊗-pure (h , p) (k , q) =
  map h k , λ r → ≈ᴹ.trans (>>=-cong (p (proj₁ r)) (λ _ → >>=-cong-x (q (proj₂ r)))) (pureᵏ-⊗ h k r)

[]-pure : {f : A → M C} {g : B → M C} → IsPure f → IsPure g → IsPure [ f , g ]
[]-pure (h , p) (k , q) = [ h , k ] , λ where (inj₁ a) → p a
                                              (inj₂ b) → q b

PureSubᵏ : PureSub Klᴹ-SymmetricMonoidal
PureSubᵏ = record
  { Pure        = IsPure
  ; pure-resp-≈ = ≈-pure
  ; pure-id     = structural id
  ; pure-∘      = ∘-pure
  ; pure-⊗₁     = ⊗-pure
  ; pure-λ⇒     = structural proj₂
  ; pure-λ⇐     = structural (tt ,_)
  ; pure-ρ⇒     = structural proj₁
  ; pure-ρ⇐     = structural (_, tt)
  ; pure-α⇒     = structural assocʳ′
  ; pure-α⇐     = structural assocˡ′
  ; pure-σ⇒     = structural swap
  }
