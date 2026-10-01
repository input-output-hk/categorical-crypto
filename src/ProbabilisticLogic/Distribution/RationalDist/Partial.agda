{-# OPTIONS --safe --without-K #-}

-- The PARTIAL rational distribution monad `Dist⊥ A = Dist-ℚ (Maybe A)`: total
-- mass stays 1 and `nothing` is an explicit divergence/deadlock sink, so `Dist⊥`
-- represents finitely-supported SUB-probability computations.

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad

open import Data.Rational as ℚ
open import Data.Rational.Properties

open import Relation.Binary

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

module ProbabilisticLogic.Distribution.RationalDist.Partial where

private variable
  ℓ ℓ′ ℓ″ : Level
  A : Type ℓ
  B : Type ℓ′
  C : Type ℓ″

private
  module Eq {ℓ} {A : Type ℓ} = IsEquivalence (≈Mℚ-isEquivalence {A = A})

------------------------------------------------------------------------
-- Affineness of `Dist-ℚ`

lookupᴰℚ-const : (μ : Dist-ℚ A) (q : ℚ) → lookupᴰℚ (entries μ) (λ _ → q) ≡ q
lookupᴰℚ-const μ q = trans (mass-as-const (entries μ) q)
                           (trans (cong (ℚ._* q) (mass-1 μ)) (*-identityˡ q))

>>=ᴹ-const : (μ : Dist-ℚ A) (ν : Dist-ℚ B) → (μ >>=ᴹ (λ _ → ν)) ≈Mℚ ν
>>=ᴹ-const μ ν P = trans (lookupᴰℚ-bind (entries μ) (λ _ → entries ν) P)
                         (lookupᴰℚ-const μ (lookupᴰℚ (entries ν) P))

------------------------------------------------------------------------
-- The partial monad.

Dist⊥ : Type ℓ → Type ℓ
Dist⊥ A = Dist-ℚ (Maybe A)

return⊥ : A → Dist⊥ A
return⊥ a = return-ℚ (just a)

kmaybe : (A → Dist⊥ B) → Maybe A → Dist⊥ B
kmaybe f (just a) = f a
kmaybe f nothing  = return-ℚ nothing

infixl 1 _>>=⊥_
_>>=⊥_ : Dist⊥ A → (A → Dist⊥ B) → Dist⊥ B
μ >>=⊥ f = μ >>=ᴹ kmaybe f

------------------------------------------------------------------------
-- Monad + setoid-monad structure.

>>=⊥-cong : {μ ν : Dist⊥ A} {f g : A → Dist⊥ B}
          → μ ≈Mℚ ν → (∀ a → f a ≈Mℚ g a) → (μ >>=⊥ f) ≈Mℚ (ν >>=⊥ g)
>>=⊥-cong {μ = μ} {ν} {f} {g} μ≈ν f≈g =
  >>=ᴹ-cong {μ = μ} {ν} {kmaybe f} {kmaybe g} μ≈ν kpt
  where
    kpt : ∀ ma → kmaybe f ma ≈Mℚ kmaybe g ma
    kpt (just a) = f≈g a
    kpt nothing  = (λ P → refl)

>>=⊥-identityˡ : (a : A) (h : A → Dist⊥ B) → (return⊥ a >>=⊥ h) ≈Mℚ h a
>>=⊥-identityˡ a h = >>=ᴹ-identityˡ (just a) (kmaybe h)

>>=⊥-identityʳ : (μ : Dist⊥ A) → (μ >>=⊥ return⊥) ≈Mℚ μ
>>=⊥-identityʳ μ = Eq.trans {i = μ >>=⊥ return⊥} {j = μ >>=ᴹ return-ℚ} {k = μ}
  (>>=ᴹ-congˡ μ (kmaybe return⊥) return-ℚ kpt)
  (>>=ᴹ-identityʳ μ)
  where
    kpt : ∀ ma → kmaybe return⊥ ma ≈Mℚ return-ℚ ma
    kpt (just a) = (λ P → refl)
    kpt nothing  = (λ P → refl)

>>=⊥-assoc : (μ : Dist⊥ A) (g : A → Dist⊥ B) (h : B → Dist⊥ C)
           → ((μ >>=⊥ g) >>=⊥ h) ≈Mℚ (μ >>=⊥ λ x → g x >>=⊥ h)
>>=⊥-assoc μ g h = Eq.trans
  {i = (μ >>=⊥ g) >>=⊥ h}
  {j = μ >>=ᴹ (λ ma → kmaybe g ma >>=ᴹ kmaybe h)}
  {k = μ >>=⊥ (λ x → g x >>=⊥ h)}
  (>>=ᴹ-assoc μ (kmaybe g) (kmaybe h))
  (>>=ᴹ-congˡ μ (λ ma → kmaybe g ma >>=ᴹ kmaybe h) (kmaybe (λ x → g x >>=⊥ h)) kpt)
  where
    kpt : ∀ ma → (kmaybe g ma >>=ᴹ kmaybe h) ≈Mℚ kmaybe (λ x → g x >>=⊥ h) ma
    kpt (just a) = (λ P → refl)
    kpt nothing  = >>=ᴹ-identityˡ nothing (kmaybe h)

-- Bind congruences with the reflexive side PINNED explicitly (cf. `>>=ᴹ-congˡ`).
>>=⊥-congˡ : (μ : Dist⊥ A) (f g : A → Dist⊥ B)
           → (∀ a → f a ≈Mℚ g a) → (μ >>=⊥ f) ≈Mℚ (μ >>=⊥ g)
>>=⊥-congˡ μ f g pt = >>=⊥-cong {μ = μ} {μ} {f} {g} (λ P → refl) pt

>>=⊥-congʳ : (f : A → Dist⊥ B) (μ ν : Dist⊥ A) → μ ≈Mℚ ν → (μ >>=⊥ f) ≈Mℚ (ν >>=⊥ f)
>>=⊥-congʳ f μ ν μ≈ν = >>=⊥-cong {μ = μ} {ν} {f} {f} μ≈ν (λ a → Eq.refl {x = f a})

-- Commutativity, via the affine law (a dropped sample on either side).
module _ {X : Type ℓ} {Y : Type ℓ′} where

  private
    pair : Maybe X → Maybe Y → Dist-ℚ (Maybe (X × Y))
    pair (just a) (just b) = return-ℚ (just (a , b))
    pair (just a) nothing  = return-ℚ nothing
    pair nothing  _        = return-ℚ nothing

  >>=⊥-comm : (x : Dist⊥ X) (y : Dist⊥ Y)
            → (x >>=⊥ λ x′ → y >>=⊥ λ y′ → return⊥ (x′ ,′ y′))
              ≈Mℚ (y >>=⊥ λ y′ → x >>=⊥ λ x′ → return⊥ (x′ , y′))
  >>=⊥-comm x y =
    Eq.trans
      {i = x >>=⊥ (λ x′ → y >>=⊥ (λ y′ → return⊥ (x′ ,′ y′)))}
      {j = x >>=ᴹ (λ ma → y >>=ᴹ (λ mb → pair ma mb))}
      {k = y >>=⊥ (λ y′ → x >>=⊥ (λ x′ → return⊥ (x′ , y′)))}
      (>>=ᴹ-congˡ x (kmaybe (λ x′ → y >>=⊥ (λ y′ → return⊥ (x′ ,′ y′))))
                    (λ ma → y >>=ᴹ (λ mb → pair ma mb)) ptL)
   (Eq.trans
      {i = x >>=ᴹ (λ ma → y >>=ᴹ (λ mb → pair ma mb))}
      {j = y >>=ᴹ (λ mb → x >>=ᴹ (λ ma → pair ma mb))}
      {k = y >>=⊥ (λ y′ → x >>=⊥ (λ x′ → return⊥ (x′ , y′)))}
      (>>=ᴹ-comm x y pair)
      (>>=ᴹ-congˡ y (λ mb → x >>=ᴹ (λ ma → pair ma mb))
                    (kmaybe (λ y′ → x >>=⊥ (λ x′ → return⊥ (x′ , y′)))) ptR))
    where
      ptL : ∀ ma → kmaybe (λ x′ → y >>=⊥ (λ y′ → return⊥ (x′ ,′ y′))) ma
                   ≈Mℚ (y >>=ᴹ λ mb → pair ma mb)
      ptL (just a) = >>=ᴹ-congˡ y (kmaybe (λ y′ → return⊥ (a ,′ y′))) (pair (just a)) inner
        where
          inner : ∀ mb → kmaybe (λ y′ → return⊥ (a ,′ y′)) mb ≈Mℚ pair (just a) mb
          inner (just b) = (λ P → refl)
          inner nothing  = (λ P → refl)
      ptL nothing  = Eq.sym {x = y >>=ᴹ (λ _ → return-ℚ nothing)} {return-ℚ nothing}
                       (>>=ᴹ-const y (return-ℚ nothing))

      ptR : ∀ mb → (x >>=ᴹ λ ma → pair ma mb)
                   ≈Mℚ kmaybe (λ y′ → x >>=⊥ (λ x′ → return⊥ (x′ , y′))) mb
      ptR (just b) = >>=ᴹ-congˡ x (λ ma → pair ma (just b)) (kmaybe (λ x′ → return⊥ (x′ , b))) inner
        where
          inner : ∀ ma → pair ma (just b) ≈Mℚ kmaybe (λ x′ → return⊥ (x′ , b)) ma
          inner (just a) = (λ P → refl)
          inner nothing  = (λ P → refl)
      ptR nothing  = Eq.trans
                       {i = x >>=ᴹ (λ ma → pair ma nothing)}
                       {j = x >>=ᴹ (λ _ → return-ℚ nothing)}
                       {k = return-ℚ nothing}
                       (>>=ᴹ-congˡ x (λ ma → pair ma nothing) (λ _ → return-ℚ nothing) inner)
                       (>>=ᴹ-const x (return-ℚ nothing))
        where
          inner : ∀ ma → pair ma nothing ≈Mℚ return-ℚ nothing
          inner (just a) = (λ P → refl)
          inner nothing  = (λ P → refl)

Dmap⊥ : (A → B) → Dist⊥ A → Dist⊥ B
Dmap⊥ f μ = μ >>=⊥ (return⊥ ∘ f)

instance
  Functor-Dist⊥ : Functor Dist⊥
  Functor-Dist⊥ ._<$>_ = Dmap⊥

  Applicative-Dist⊥ : Applicative Dist⊥
  Applicative-Dist⊥ .pure = return⊥
  Applicative-Dist⊥ ._<*>_ fs xs = fs >>=⊥ λ f → xs >>=⊥ (return⊥ ∘ f)

  Monad-Dist⊥ : Monad Dist⊥
  Monad-Dist⊥ .return = return⊥
  Monad-Dist⊥ ._>>=_  = _>>=⊥_
