{-# OPTIONS --safe --without-K --guardedness #-}

-- Congruence for the raw G-composition, split from `Collapse` so consumers
-- that only need to expose a composite step do not pay for this conversion.
-- `_∘ᴹ_` is opaque: these endpoints therefore remain nominal while the
-- already-checked category congruence transports their equality.

open import Data.Sum.Base using (_⊎_)

open import CategoricalCrypto.Machines.Collapse

module CategoricalCrypto.Machines.Collapse.Congruence where

compose-resp-≈ᴹ : {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
                   {g g′ : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)}
                   {f f′ : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺)}
                 → g S.≈ᴹ g′ → f S.≈ᴹ f′
                 → MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                     (W.α MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ W.γ))
                   S.≈ᴹ
                   MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                     (W.α MC.∘ᴹ ((g′ T.⊗ᵉ f′) MC.∘ᴹ W.γ))
compose-resp-≈ᴹ {A⁺} {A⁻} {B⁺} {B⁻} {C⁺} {C⁻}
                {g} {g′} {f} {f′} eg ef =
  TC.trace-resp-≈ᴹ {A⁺ ⊎ C⁻} {A⁻ ⊎ C⁺} {B⁻ ⊎ B⁺} eout
  where
  e⊗ : (g T.⊗ᵉ f) S.≈ᴹ (g′ T.⊗ᵉ f′)
  e⊗ = T.⊗ᵉ-resp-≈ᴹ {f = g} {h = g′} {g = f} {i = f′} eg ef

  ein : ((g T.⊗ᵉ f) MC.∘ᴹ W.γ) S.≈ᴹ
        ((g′ T.⊗ᵉ f′) MC.∘ᴹ W.γ)
  ein = Cat.∘ᴹ-resp-≈ᴹ
    {f = g T.⊗ᵉ f} {h = g′ T.⊗ᵉ f′} {g = W.γ} {i = W.γ} e⊗ S.reflᴹ

  eout : (W.α MC.∘ᴹ ((g T.⊗ᵉ f) MC.∘ᴹ W.γ)) S.≈ᴹ
         (W.α MC.∘ᴹ ((g′ T.⊗ᵉ f′) MC.∘ᴹ W.γ))
  eout = Cat.∘ᴹ-resp-≈ᴹ
    {f = W.α} {h = W.α}
    {g = (g T.⊗ᵉ f) MC.∘ᴹ W.γ} {i = (g′ T.⊗ᵉ f′) MC.∘ᴹ W.γ}
    S.reflᴹ ein
