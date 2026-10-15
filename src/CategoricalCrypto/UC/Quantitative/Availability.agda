{-# OPTIONS --safe --without-K #-}

-- Designated caps are supplied grade maps, fixed before the environment.
-- Comparison at unit grade needs neither a tensor on the computation category
-- nor an isomorphism T I B ≅ B. This is only the designated no-adversary mode:
-- it implies no arbitrary-adversary liveness, fairness, deadline or eventual
-- delivery guarantee. Replacement budgets follow at-trans, not at-compose's
-- reversed protocol-composition order; ⊕ need not commute.

open import Data.Product.Base
open import Function.Bundles
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.UC.Quantitative.Availability
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.UC.Quantitative E
open import CategoricalCrypto.UC.Quantitative.Bridge E

module Designated {o ℓ e o′ ℓ′ e′ c ℓb : Level}
                  (S : QUCSetup o ℓ e o′ ℓ′ e′ c ℓb) where

  open QBridge S public

  private variable
    A B : 𝒞.Obj
    X Y Z : ℐ.Obj
    ε δ κ εs εa δs δa : Error

  close : X ℐ.⇒ ℐ.unit → A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ ℐ.unit B
  close a f = sub a 𝒞.∘ f

  Availability : Error → X ℐ.⇒ ℐ.unit → Y ℐ.⇒ ℐ.unit
               → A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ Y B
               → Set (o ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)
  Availability ε a b f g = close a f ≈ᵁ[ ε ] close b g

  record SecureAvailable (εs εa : Error) (a : X ℐ.⇒ ℐ.unit) (b : Y ℐ.⇒ ℐ.unit)
                         (f : A 𝒞.⇒ T₀ X B) (g : A 𝒞.⇒ T₀ Y B)
                         : Set (o ⊔ ℓ ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb) where
    constructor secure-available
    field security : Witness εs f g
          availability : Availability εa a b f g

  close-resp-cap : {a b : X ℐ.⇒ ℐ.unit} (f : A 𝒞.⇒ T₀ X B)
                 → a ℐ.≈ b → close a f 𝒞.≈ close b f
  close-resp-cap f eq = 𝒞.∘-resp-≈ˡ (sub-resp-≈ eq)

  close-regrade : (a : X ℐ.⇒ ℐ.unit) (s : Y ℐ.⇒ X) (g : A 𝒞.⇒ T₀ Y B)
                → close a (sub s 𝒞.∘ g) 𝒞.≈ close (a ℐ.∘ s) g
  close-regrade a s g = sub-merge

  mode-preserving : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                    {s : Y ℐ.⇒ X} {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                  → a ℐ.∘ s ℐ.≈ b → At s ε f g → Availability ε a b f g
  mode-preserving {a = a} {s = s} {g = g} compat h =
    ctx-resp 𝒞.Equiv.refl
      (𝒞.Equiv.trans (close-regrade a s g) (close-resp-cap g compat)) (ctx-sub a h)

  secure-mode-preserving : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                           {s : Y ℐ.⇒ X} {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                         → a ℐ.∘ s ℐ.≈ b → At s ε f g → SecureAvailable ε ε a b f g
  secure-mode-preserving compat h = secure-available (_ , h) (mode-preserving compat h)

  availability-trans : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit} {c : Z ℐ.⇒ ℐ.unit}
                       {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} {h : A 𝒞.⇒ T₀ Z B}
                     → Availability ε a b f g → Availability δ b c g h
                     → Availability (ε ⊕ δ) a c f h
  availability-trans = ctx-trans

  -- The parentheses retain the order of the actual three-step comparison.
  secure-trans-bridge : {a : X ℐ.⇒ ℐ.unit} {b₁ b₂ : Y ℐ.⇒ ℐ.unit} {c : Z ℐ.⇒ ℐ.unit}
                        {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} {h : A 𝒞.⇒ T₀ Z B}
                      → Availability κ b₁ b₂ g g
                      → SecureAvailable εs εa a b₁ f g → SecureAvailable δs δa b₂ c g h
                      → SecureAvailable (εs ⊕ δs) ((εa ⊕ κ) ⊕ δa) a c f h
  secure-trans-bridge bridge (secure-available (s , hs) ha) (secure-available (t , ht) hb) =
    secure-available (s ℐ.∘ t , at-trans hs ht) (ctx-trans (ctx-trans ha bridge) hb)

  secure-trans : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit} {c : Z ℐ.⇒ ℐ.unit}
                 {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} {h : A 𝒞.⇒ T₀ Z B}
               → SecureAvailable εs εa a b f g → SecureAvailable δs δa b c g h
               → SecureAvailable (εs ⊕ δs) (εa ⊕ δa) a c f h
  secure-trans (secure-available (s , hs) ha) (secure-available (t , ht) hb) =
    secure-available (s ℐ.∘ t , at-trans hs ht) (ctx-trans ha hb)

  secure-trans-cap : {a : X ℐ.⇒ ℐ.unit} {b₁ b₂ : Y ℐ.⇒ ℐ.unit} {c : Z ℐ.⇒ ℐ.unit}
                     {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} {h : A 𝒞.⇒ T₀ Z B}
                   → b₁ ℐ.≈ b₂
                   → SecureAvailable εs εa a b₁ f g → SecureAvailable δs δa b₂ c g h
                   → SecureAvailable (εs ⊕ δs) (εa ⊕ δa) a c f h
  secure-trans-cap {g = g} compat (secure-available hs ha) cg =
    secure-trans (secure-available hs (ctx-resp 𝒞.Equiv.refl (close-resp-cap g compat) ha)) cg

  zero-availability : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                      {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                    → (close a f ≈ᵁ close b g) ⇔ Availability ε₀ a b f g
  zero-availability = zero-agreement

  zero-secure : {a : X ℐ.⇒ ℐ.unit} {b : Y ℐ.⇒ ℐ.unit}
                {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
              → ((f ≤UC g) × (close a f ≈ᵁ close b g)) ⇔ SecureAvailable ε₀ ε₀ a b f g
  zero-secure = mk⇔
    (λ (hs , ha) → secure-available (zero-emulation⇒ hs) (zero-agreement⇒ ha))
    (λ (secure-available hs ha) → zero-emulation⇐ hs , zero-agreement⇐ ha)
