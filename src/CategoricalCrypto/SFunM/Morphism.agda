{-# OPTIONS --safe --without-K #-}

-- A monad morphism `θ : M ⇒ N` abstracts the effects of a stateful function
-- without touching its control flow: state space and initial state are kept,
-- only the step kernel is post-composed with `θ`.  Everything below reduces to
-- `θ-trace`, the statement that `θ` commutes with running a machine.

open import categorical-crypto.Prelude hiding (Functor)

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
open import Categories.Monad.Discrete
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Sum

import CategoricalCrypto.SFunM as SFun
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Properties as SFunProperties

module CategoricalCrypto.SFunM.Morphism (Mo No : DiscreteMonad 0ℓ)
  (let module ℳ = DiscreteMonad Mo; module 𝒩 = DiscreteMonad No)
  (θ : {A : Type} → ℳ.M A → 𝒩.M A)
  (θ-cong : {A : Type} {x y : ℳ.M A} → x ℳ.≈ᴹ y → θ x 𝒩.≈ᴹ θ y)
  (θ-return : {A : Type} (a : A) → θ (ℳ.return a) 𝒩.≈ᴹ 𝒩.return a)
  (θ-bind : {A B : Type} (m : ℳ.M A) (k : A → ℳ.M B)
          → θ (m ℳ.>>= k) 𝒩.≈ᴹ (θ m 𝒩.>>= λ a → θ (k a)))
  where

private variable A B C D St : Type

private
  module 𝓝  = SFun No
  module 𝓝M = SFunMonoidal No
  module 𝓝P = SFunProperties No
  module 𝒮ᴺ = Category 𝓝.SFunᵉ-Category

  θ-<$>ᴹ : (h : A → B) (m : ℳ.M A) → θ (h ℳ.<$>ᴹ m) 𝒩.≈ᴹ (h 𝒩.<$>ᴹ θ m)
  θ-<$>ᴹ h m = 𝒩.≈ᴹ.trans (θ-bind m _) (𝒩.>>=-cong-f λ _ → θ-return _)

open SFun Mo
open SFunMonoidal Mo
open SFunProperties Mo

open 𝒩.≈ᴹ-Reasoning
open 𝒮ᴺ.HomReasoning using (_○_; ⟺; _⟩∘⟨_)

mapᵉ : SFunᵉ A B → 𝓝.SFunᵉ A B
mapᵉ f = 𝓝.mkᵉ init (θ ∘ fun)
  where open SFunᵉ f

θ-trace : (f : SFunType A B St) (s : St) (xs : List A)
        → θ (trace f s xs) 𝒩.≈ᴹ 𝓝.trace (θ ∘ f) s xs
θ-trace f s []       = θ-return []
θ-trace f s (a ∷ as) = begin
  θ (f (s , a) ℳ.>>= λ (s′ , b) → trace f s′ as ℳ.>>= λ bs → ℳ.return (b ∷ bs))
    ≈⟨ θ-bind (f (s , a)) _ ⟩
  (θ (f (s , a)) 𝒩.>>= λ (s′ , b) → θ (trace f s′ as ℳ.>>= λ bs → ℳ.return (b ∷ bs)))
    ≈⟨ 𝒩.>>=-cong-f (λ (s′ , b) → 𝒩.≈ᴹ.trans (θ-<$>ᴹ (b ∷_) (trace f s′ as))
                                             (𝒩.<$>ᴹ-cong (θ-trace f s′ as))) ⟩
  𝓝.trace (θ ∘ f) s (a ∷ as) ∎

θ-eval : (f : SFunᵉ A B) (xs : List A) → θ (eval f xs) 𝒩.≈ᴹ 𝓝.eval (mapᵉ f) xs
θ-eval f xs = θ-trace fun init xs
  where open SFunᵉ f

mapᵉ-cong : {f g : SFunᵉ A B} → f ≈ᵉ g → mapᵉ f 𝓝.≈ᵉ mapᵉ g
mapᵉ-cong {f = f} {g} f≈g xs = begin
  𝓝.eval (mapᵉ f) xs  ≈˘⟨ θ-eval f xs ⟩
  θ (eval f xs)        ≈⟨ θ-cong (f≈g xs) ⟩
  θ (eval g xs)        ≈⟨ θ-eval g xs ⟩
  𝓝.eval (mapᵉ g) xs  ∎

mapᵉ-id : mapᵉ (idᵉ {A = A}) 𝓝.≈ᵉ 𝓝.idᵉ
mapᵉ-id xs = begin
  𝓝.eval (mapᵉ idᵉ) xs  ≈˘⟨ θ-eval idᵉ xs ⟩
  θ (eval idᵉ xs)        ≈˘⟨ θ-cong (id-correct xs) ⟩
  θ (ℳ.return xs)        ≈⟨ θ-return xs ⟩
  𝒩.return xs            ≈⟨ 𝓝.id-correct xs ⟩
  𝓝.eval 𝓝.idᵉ xs      ∎

mapᵉ-∘ : (g : SFunᵉ B C) (f : SFunᵉ A B) → mapᵉ (g ∘ᵉ f) 𝓝.≈ᵉ (mapᵉ g 𝓝.∘ᵉ mapᵉ f)
mapᵉ-∘ g f xs = begin
  𝓝.eval (mapᵉ (g ∘ᵉ f)) xs
    ≈˘⟨ θ-eval (g ∘ᵉ f) xs ⟩
  θ (eval (g ∘ᵉ f) xs)
    ≈˘⟨ θ-cong (trace-∘ xs) ⟩
  θ (eval f xs ℳ.>>= eval g)
    ≈⟨ θ-bind (eval f xs) (eval g) ⟩
  (θ (eval f xs) 𝒩.>>= λ ys → θ (eval g ys))
    ≈⟨ 𝒩.>>=-cong (θ-eval f xs) (θ-eval g) ⟩
  (𝓝.eval (mapᵉ f) xs 𝒩.>>= 𝓝.eval (mapᵉ g))
    ≈⟨ 𝓝.trace-∘ xs ⟩
  𝓝.eval (mapᵉ g 𝓝.∘ᵉ mapᵉ f) xs ∎

SFunᵉ-map : Functor SFunᵉ-Category 𝓝.SFunᵉ-Category
SFunᵉ-map = record
  { F₀           = id
  ; F₁           = mapᵉ
  ; identity     = mapᵉ-id
  ; homomorphism = λ {_ _ _ f g} → mapᵉ-∘ g f
  ; F-resp-≈     = mapᵉ-cong
  }

------------------------------------------------------------------------
-- Strong monoidality

mapᵉ-stateless : (h : A → B) → mapᵉ (statelessᵉ h) 𝓝.≈ᵉ 𝓝P.statelessᵉ h
mapᵉ-stateless h = 𝓝P.≈ᵉ-sim id refl λ _ a →
  𝒩.≈ᴹ.trans (𝒩.<$>ᴹ-cong (θ-return (tt , h a))) 𝒩.>>=-identityˡ-≈

mapᵉ-⊗ : (f : SFunᵉ A B) (g : SFunᵉ C D)
       → mapᵉ (f ⊗ᵉ g) 𝓝.≈ᵉ (mapᵉ f 𝓝M.⊗ᵉ mapᵉ g)
mapᵉ-⊗ f g = 𝓝P.≈ᵉ-sim id refl λ where
    (s , _) (inj₁ a) → 𝒩.≈ᴹ.trans (𝒩.<$>ᴹ-cong (θ-<$>ᴹ _ (F.fun (s , a))))
                                  (𝒩.<$>ᴹ-∘ _ _ (θ (F.fun (s , a))))
    (_ , t) (inj₂ c) → 𝒩.≈ᴹ.trans (𝒩.<$>ᴹ-cong (θ-<$>ᴹ _ (G.fun (t , c))))
                                  (𝒩.<$>ᴹ-∘ _ _ (θ (G.fun (t , c))))
  where module F = SFunᵉ f; module G = SFunᵉ g

SFunᵉ-map-monoidal : StrongMonoidalFunctor SFunᵉ-MonoidalCategory 𝓝M.SFunᵉ-MonoidalCategory
SFunᵉ-map-monoidal = record
  { F = SFunᵉ-map
  ; isStrongMonoidal = record
      { ε      = record { from = 𝓝.idᵉ ; to = 𝓝.idᵉ
                        ; iso = record { isoˡ = 𝒮ᴺ.identityˡ ; isoʳ = 𝒮ᴺ.identityˡ } }
      ; ⊗-homo = niHelper record
          { η       = λ _ → 𝓝.idᵉ
          ; η⁻¹     = λ _ → 𝓝.idᵉ
          ; commute = λ (f , g) → 𝒮ᴺ.identityˡ ○ ⟺ (mapᵉ-⊗ f g) ○ ⟺ 𝒮ᴺ.identityʳ
          ; iso     = λ _ → record { isoˡ = 𝒮ᴺ.identityˡ ; isoʳ = 𝒮ᴺ.identityˡ }
          }
      ; associativity = strict assocʳ
          ○ ⟺ (𝒮ᴺ.identityˡ ○ 𝓝M.⊗ᵉ-identity ⟩∘⟨ 𝒮ᴺ.Equiv.refl ○ 𝒮ᴺ.identityˡ)
      ; unitaryˡ      = strict (fromInj₂ ⊥-elim)
      ; unitaryʳ      = strict (fromInj₁ ⊥-elim)
      }
  }
  where
    strict : (h : A ⊎ C → B)
           → (mapᵉ (statelessᵉ h) 𝓝.∘ᵉ (𝓝.idᵉ 𝓝.∘ᵉ (𝓝.idᵉ 𝓝M.⊗ᵉ 𝓝.idᵉ)))
             𝓝.≈ᵉ 𝓝P.statelessᵉ h
    strict h = mapᵉ-stateless h ⟩∘⟨ (𝒮ᴺ.identityˡ ○ 𝓝M.⊗ᵉ-identity) ○ 𝒮ᴺ.identityʳ
