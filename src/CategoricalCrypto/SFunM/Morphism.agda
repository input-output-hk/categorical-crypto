{-# OPTIONS --safe --without-K #-}

-- A monad morphism `θ : M ⇒ N` induces a strong monoidal functor `SFunᵉ M → SFunᵉ N`

open import categorical-crypto.Prelude hiding (Functor)

open import Class.Core
open import Class.Monad.Ext.Setoid

open import Categories.Category
open import Categories.Functor using (Functor)
open import Categories.Functor.Monoidal
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Sum
open import Data.Sum.Ext

import Relation.Binary.Reasoning.Setoid as R-Setoid

open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunM.Monoidal
open import CategoricalCrypto.SFunM.Properties

module CategoricalCrypto.SFunM.Morphism where

private variable A B C D St : Type

module _ {M N : Type↑}
  ⦃ Monad-M : Monad M ⦄ ⦃ MS-M : MonadSetoid M ⦄
  ⦃ ML-M : MonadLawsSetoid M ⦄ ⦃ MC-M : CommutativeMonadSetoid M ⦄
  ⦃ Monad-N : Monad N ⦄ ⦃ MS-N : MonadSetoid N ⦄
  ⦃ ML-N : MonadLawsSetoid N ⦄ ⦃ MC-N : CommutativeMonadSetoid N ⦄
  (Θ : MonadMorphismSetoid M N)
  where

  open MonadMorphismSetoid Θ

  private
    module N≈ = MonadSetoid MS-N
    module N-Laws = MonadLawsSetoid ML-N
    module N-Reasoning {ℓ} {X : Type ℓ} = R-Setoid (N≈.≈ᴹ-setoid {A = X})

  open N-Reasoning

  mapᵉ : SFunᵉ {M = M} A B → SFunᵉ {M = N} A B
  mapᵉ f = mkᵉ init (θ ∘ fun)
    where open SFunᵉ f

  θ-trace : (f : SFunType {M = M} A B St) (s : St) (xs : List A)
          → θ (trace f s xs) ≈ᴹ trace (θ ∘ f) s xs
  θ-trace f s []       = θ-return []
  θ-trace f s (a ∷ as) = begin
    θ (f (s , a) >>= λ (s′ , b) → trace f s′ as >>= λ bs → return (b ∷ bs))
      ≈⟨ θ-bind (f (s , a)) _ ⟩
    (θ (f (s , a)) >>= λ (s′ , b) → θ (trace f s′ as >>= λ bs → return (b ∷ bs)))
      ≈⟨ N≈.>>=-cong-f (λ (s′ , b) → N≈.≈ᴹ.trans (θ-<$>ᴹ (b ∷_) (trace f s′ as))
                                                (N≈.<$>ᴹ-cong (θ-trace f s′ as))) ⟩
    trace (θ ∘ f) s (a ∷ as) ∎

  θ-eval : (f : SFunᵉ {M = M} A B) (xs : List A) → θ (eval f xs) ≈ᴹ eval (mapᵉ f) xs
  θ-eval f xs = θ-trace fun init xs
    where open SFunᵉ f

  mapᵉ-cong : {f g : SFunᵉ {M = M} A B} → f ≈ᵉ g → mapᵉ f ≈ᵉ mapᵉ g
  mapᵉ-cong {f = f} {g} f≈g xs = begin
    eval (mapᵉ f) xs  ≈˘⟨ θ-eval f xs ⟩
    θ (eval f xs)     ≈⟨ θ-cong (f≈g xs) ⟩
    θ (eval g xs)     ≈⟨ θ-eval g xs ⟩
    eval (mapᵉ g) xs  ∎

  mapᵉ-id : mapᵉ (idᵉ {A = A}) ≈ᵉ idᵉ
  mapᵉ-id xs = begin
    eval (mapᵉ idᵉ) xs  ≈˘⟨ θ-eval idᵉ xs ⟩
    θ (eval idᵉ xs)     ≈˘⟨ θ-cong (id-correct xs) ⟩
    θ (return xs)       ≈⟨ θ-return xs ⟩
    return xs           ≈⟨ id-correct xs ⟩
    eval idᵉ xs         ∎

  mapᵉ-∘ : (g : SFunᵉ {M = M} B C) (f : SFunᵉ {M = M} A B) → mapᵉ (g ∘ᵉ f) ≈ᵉ (mapᵉ g ∘ᵉ mapᵉ f)
  mapᵉ-∘ g f xs = begin
    eval (mapᵉ (g ∘ᵉ f)) xs
      ≈˘⟨ θ-eval (g ∘ᵉ f) xs ⟩
    θ (eval (g ∘ᵉ f) xs)
      ≈˘⟨ θ-cong (trace-∘ xs) ⟩
    θ (eval f xs >>= eval g)
      ≈⟨ θ-bind (eval f xs) (eval g) ⟩
    (θ (eval f xs) >>= λ ys → θ (eval g ys))
      ≈⟨ N≈.>>=-cong (θ-eval f xs) (θ-eval g) ⟩
    (eval (mapᵉ f) xs >>= eval (mapᵉ g))
      ≈⟨ trace-∘ xs ⟩
    eval (mapᵉ g ∘ᵉ mapᵉ f) xs ∎

  SFunᵉ-map : Functor (SFunᵉ-Category {M = M}) (SFunᵉ-Category {M = N})
  SFunᵉ-map = record
    { F₀           = id
    ; F₁           = mapᵉ
    ; identity     = mapᵉ-id
    ; homomorphism = λ {_ _ _ f g} → mapᵉ-∘ g f
    ; F-resp-≈     = mapᵉ-cong
    }

  ------------------------------------------------------------------------
  -- Strong monoidality

  private
    module 𝒩 = Category (SFunᵉ-Category {M = N})

    open 𝒩.HomReasoning

  mapᵉ-stateless : (h : A → B) → mapᵉ (statelessᵉ {M = M} h) ≈ᵉ statelessᵉ {M = N} h
  mapᵉ-stateless h = ≈ᵉ-sim id refl λ _ a →
    N≈.≈ᴹ.trans (N≈.<$>ᴹ-cong (θ-return (tt , h a))) >>=-identityˡ-≈

  mapᵉ-⊗ : (f : SFunᵉ {M = M} A B) (g : SFunᵉ {M = M} C D) → mapᵉ (f ⊗ᵉ g) ≈ᵉ (mapᵉ f ⊗ᵉ mapᵉ g)
  mapᵉ-⊗ f g = ≈ᵉ-sim id refl λ where
      (s , _) (inj₁ a) → N≈.≈ᴹ.trans (N≈.<$>ᴹ-cong (θ-<$>ᴹ _ (F.fun (s , a))))
                                     (N-Laws.<$>ᴹ-∘ _ _ (θ (F.fun (s , a))))
      (_ , t) (inj₂ c) → N≈.≈ᴹ.trans (N≈.<$>ᴹ-cong (θ-<$>ᴹ _ (G.fun (t , c))))
                                     (N-Laws.<$>ᴹ-∘ _ _ (θ (G.fun (t , c))))
    where module F = SFunᵉ f; module G = SFunᵉ g

  SFunᵉ-map-monoidal : StrongMonoidalFunctor (SFunᵉ-MonoidalCategory {M = M})
                                             (SFunᵉ-MonoidalCategory {M = N})
  SFunᵉ-map-monoidal = record
    { F = SFunᵉ-map
    ; isStrongMonoidal = record
        { ε      = record { from = idᵉ ; to = idᵉ
                          ; iso = record { isoˡ = 𝒩.identityˡ ; isoʳ = 𝒩.identityˡ } }
        ; ⊗-homo = niHelper record
            { η       = λ _ → idᵉ
            ; η⁻¹     = λ _ → idᵉ
            ; commute = λ (f , g) → 𝒩.identityˡ ○ ⟺ (mapᵉ-⊗ f g) ○ ⟺ 𝒩.identityʳ
            ; iso     = λ _ → record { isoˡ = 𝒩.identityˡ ; isoʳ = 𝒩.identityˡ }
            }
        ; associativity = strict assocʳ
            ○ ⟺ (𝒩.identityˡ ○ ⊗ᵉ-identity {M = N} ⟩∘⟨refl ○ 𝒩.identityˡ)
        ; unitaryˡ      = strict unitˡ⇒
        ; unitaryʳ      = strict unitʳ⇒
        }
    }
    where
      strict : (h : A ⊎ C → B)
             → (mapᵉ (statelessᵉ {M = M} h) ∘ᵉ (idᵉ ∘ᵉ (idᵉ {M = N} ⊗ᵉ idᵉ))) ≈ᵉ statelessᵉ {M = N} h
      strict h = mapᵉ-stateless h ⟩∘⟨ (𝒩.identityˡ ○ ⊗ᵉ-identity {M = N}) ○ 𝒩.identityʳ
