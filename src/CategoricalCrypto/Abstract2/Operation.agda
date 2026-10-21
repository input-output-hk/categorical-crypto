{-# OPTIONS --safe --without-K #-}

-- Combinator for proving that operations are compatible with `≤UC`

module CategoricalCrypto.Abstract2.Operation where

open import Data.Product
open import Level

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module OperationUC
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  where
  open AbstractUC setup

  ProtocolFamily : ∀ {ι} {I : Set ι}
    → (A B : I → 𝒞.Obj) → (X : I → ℐ.Obj) → Set (ι ⊔ ℓ′)
  ProtocolFamily {I = I} A B X = (i : I) → A i 𝒞.⇒ T₀ (X i) (B i)

  UC-operation : ∀ {ι} {I : Set ι}
    {A B : I → 𝒞.Obj} {C D : 𝒞.Obj} {G : (I → ℐ.Obj) → ℐ.Obj}
    (mapG : ∀ {X Y : I → ℐ.Obj} → ((i : I) → X i ℐ.⇒ Y i) → G X ℐ.⇒ G Y)
    (op : ∀ {X : I → ℐ.Obj} → ProtocolFamily A B X → C 𝒞.⇒ T₀ (G X) D)
    (op-cong : ∀ {X} {fs gs : ProtocolFamily A B X}
      → ((i : I) → fs i ≈ᵁ gs i) → op fs ≈ᵁ op gs)
    (op-sub : ∀ {X Y : I → ℐ.Obj} (s : (i : I) → X i ℐ.⇒ Y i) (fs : ProtocolFamily A B X)
      → op (λ i → sub (s i) 𝒞.∘ fs i) ≈ᵁ sub (mapG s) 𝒞.∘ op fs)
    → ∀ {X Y} {fs : ProtocolFamily A B X} {gs : ProtocolFamily A B Y}
    → ((i : I) → fs i ≤UC gs i) → op fs ≤UC op gs
  UC-operation mapG op op-cong op-sub {X} {Y} {fs} {gs} le =
    dummy-complete (mapG sim , ≈ᵁ-trans (op-cong eq) (op-sub sim gs))
    where
    sim : ∀ i → Y i ℐ.⇒ X i
    sim i = proj₁ (≤UC⇒dummy (le i))

    eq : ∀ i → fs i ≈ᵁ sub (sim i) 𝒞.∘ gs i
    eq i = proj₂ (≤UC⇒dummy (le i))
