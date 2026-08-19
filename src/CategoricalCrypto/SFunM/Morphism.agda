{-# OPTIONS --safe --without-K #-}

-- A monad morphism `θ : M ⇒ N` induces a strong monoidal functor `SFunᵉ M → SFunᵉ N`

open import categorical-crypto.Prelude hiding (Functor; _>>=_; return)

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
open import Categories.Monad.Construction.Kleisli
open import Categories.Monad.Construction.Kleisli.Ext
import Categories.Monad.Setoids.Discrete as Discrete
import Categories.Monad.Setoids.Discrete.Morphism as DiscreteMorphism
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Sum
open import Data.Sum.Ext

import CategoricalCrypto.SFunM as SFun
import CategoricalCrypto.SFunM.Monoidal as SFunMonoidal
import CategoricalCrypto.SFunM.Properties as SFunProperties

module CategoricalCrypto.SFunM.Morphism
  (K K′ : KleisliTriple (Setoids 0ℓ 0ℓ)) (Θ : KleisliTriple⇒ (Setoids 0ℓ 0ℓ) K K′) -- TODO: might as well name the Kleisli triples M and N, for consistency below
  (M-Comm : Discrete.Commutative K) (N-Comm : Discrete.Commutative K′) where

private variable A B C D St : Type

-- TODO: it'd be better to qualify this as ℳ.*
open Discrete K
open DiscreteMorphism K K′ Θ
open SFun K
open Laws M-Comm
open SFunMonoidal K M-Comm
open SFunProperties K

private
  module 𝓝  = SFun K′
  module 𝓝L = 𝓝.Laws N-Comm
  module 𝓝M = SFunMonoidal K′ N-Comm
  module 𝓝P = SFunProperties K′
  module 𝒩  = Category 𝓝L.SFunᵉ-Category

open N.≈ᴹ-Reasoning
open 𝒩.HomReasoning using (_○_; ⟺; _⟩∘⟨_)

mapᵉ : SFunᵉ A B → 𝓝.SFunᵉ A B
mapᵉ f = 𝓝.mkᵉ init (θ ∘ fun)
  where open SFunᵉ f

θ-trace : (f : SFunType A B St) (s : St) (xs : List A)
        → θ (trace f s xs) ≈ᴺ 𝓝.trace (θ ∘ f) s xs
θ-trace f s []       = θ-return []
θ-trace f s (a ∷ as) = begin
  θ (f (s , a) >>= λ (s′ , b) → trace f s′ as >>= λ bs → return (b ∷ bs))
    ≈⟨ θ-bind (f (s , a)) _ ⟩
  (θ (f (s , a)) N.>>= λ (s′ , b) → θ (trace f s′ as >>= λ bs → return (b ∷ bs)))
    ≈⟨ N.>>=-cong-f (λ (s′ , b) → N.≈ᴹ.trans (θ-<$>ᴹ (b ∷_) (trace f s′ as))
                                             (N.<$>ᴹ-cong (θ-trace f s′ as))) ⟩
  𝓝.trace (θ ∘ f) s (a ∷ as) ∎

θ-eval : (f : SFunᵉ A B) (xs : List A) → θ (eval f xs) ≈ᴺ 𝓝.eval (mapᵉ f) xs
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
  θ (return xs)          ≈⟨ θ-return xs ⟩
  N.return xs            ≈⟨ 𝓝L.id-correct xs ⟩
  𝓝.eval 𝓝.idᵉ xs      ∎

mapᵉ-∘ : (g : SFunᵉ B C) (f : SFunᵉ A B) → mapᵉ (g ∘ᵉ f) 𝓝.≈ᵉ (mapᵉ g 𝓝.∘ᵉ mapᵉ f)
mapᵉ-∘ g f xs = begin
  𝓝.eval (mapᵉ (g ∘ᵉ f)) xs
    ≈˘⟨ θ-eval (g ∘ᵉ f) xs ⟩
  θ (eval (g ∘ᵉ f) xs)
    ≈˘⟨ θ-cong (trace-∘ xs) ⟩
  θ (eval f xs >>= eval g)
    ≈⟨ θ-bind (eval f xs) (eval g) ⟩
  (θ (eval f xs) N.>>= λ ys → θ (eval g ys))
    ≈⟨ N.>>=-cong (θ-eval f xs) (θ-eval g) ⟩
  (𝓝.eval (mapᵉ f) xs N.>>= 𝓝.eval (mapᵉ g))
    ≈⟨ 𝓝L.trace-∘ xs ⟩
  𝓝.eval (mapᵉ g 𝓝.∘ᵉ mapᵉ f) xs ∎

SFunᵉ-map : Functor SFunᵉ-Category 𝓝L.SFunᵉ-Category
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
  N.≈ᴹ.trans (N.<$>ᴹ-cong (θ-return (tt , h a))) N.>>=-identityˡ-≈

mapᵉ-⊗ : (f : SFunᵉ A B) (g : SFunᵉ C D)
       → mapᵉ (f ⊗ᵉ g) 𝓝.≈ᵉ (mapᵉ f 𝓝M.⊗ᵉ mapᵉ g)
mapᵉ-⊗ f g = 𝓝P.≈ᵉ-sim id refl λ where
    (s , _) (inj₁ a) → N.≈ᴹ.trans (N.<$>ᴹ-cong (θ-<$>ᴹ _ (F.fun (s , a))))
                                  (N.<$>ᴹ-∘ _ _ (θ (F.fun (s , a))))
    (_ , t) (inj₂ c) → N.≈ᴹ.trans (N.<$>ᴹ-cong (θ-<$>ᴹ _ (G.fun (t , c))))
                                  (N.<$>ᴹ-∘ _ _ (θ (G.fun (t , c))))
  where module F = SFunᵉ f; module G = SFunᵉ g

SFunᵉ-map-monoidal : StrongMonoidalFunctor SFunᵉ-MonoidalCategory 𝓝M.SFunᵉ-MonoidalCategory
SFunᵉ-map-monoidal = record
  { F = SFunᵉ-map
  ; isStrongMonoidal = record
      { ε      = record { from = 𝓝.idᵉ ; to = 𝓝.idᵉ
                        ; iso = record { isoˡ = 𝒩.identityˡ ; isoʳ = 𝒩.identityˡ } }
      ; ⊗-homo = niHelper record
          { η       = λ _ → 𝓝.idᵉ
          ; η⁻¹     = λ _ → 𝓝.idᵉ
          ; commute = λ (f , g) → 𝒩.identityˡ ○ ⟺ (mapᵉ-⊗ f g) ○ ⟺ 𝒩.identityʳ
          ; iso     = λ _ → record { isoˡ = 𝒩.identityˡ ; isoʳ = 𝒩.identityˡ }
          }
      ; associativity = strict assocʳ
          ○ ⟺ (𝒩.identityˡ ○ 𝓝M.⊗ᵉ-identity ⟩∘⟨ 𝒩.Equiv.refl ○ 𝒩.identityˡ)
      ; unitaryˡ      = strict unitˡ⇒
      ; unitaryʳ      = strict unitʳ⇒
      }
  }
  where
    strict : (h : A ⊎ C → B)
           → (mapᵉ (statelessᵉ h) 𝓝.∘ᵉ (𝓝.idᵉ 𝓝.∘ᵉ (𝓝.idᵉ 𝓝M.⊗ᵉ 𝓝.idᵉ)))
             𝓝.≈ᵉ 𝓝P.statelessᵉ h
    strict h = mapᵉ-stateless h ⟩∘⟨ (𝒩.identityˡ ○ 𝓝M.⊗ᵉ-identity) ○ 𝒩.identityʳ
