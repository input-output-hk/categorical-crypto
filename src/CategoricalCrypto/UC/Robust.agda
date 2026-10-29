{-# OPTIONS --safe --without-K #-}

-- Robust properties
--
-- Properties that are preserved by `≤UC` under reasonable assumptions

open import categorical-crypto.Prelude using (PredS)
open import Data.Product
open import Data.Unit
open import Function.Bundles
open import Function.Properties.Equivalence

open import Level

open import Categories.Functor

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module CategoricalCrypto.UC.Robust
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open AbstractUC setup public

private variable
  A B : 𝒞.Obj
  W X X′ Y : ℐ.Obj
  d p : Level

module ℰ = Functor ℰ

-- predicates on ℰ.₀ (T₀ W A) that preserve the setoid equality
Predℰ : (A : 𝒞.Obj) (p : Level) → Set (o ⊔ cs ⊔ ℓs ⊔ suc p)
Predℰ A p = (W : ℐ.Obj) → PredS (ℰ.₀ (T₀ W A)) p

------------------------------------------------------------------------
-- Admissible environments

Admissible : (A : 𝒞.Obj) (d : Level) → Set (o ⊔ cs ⊔ suc d)
Admissible A d = ∀ W X → Env (T₀ (W ⊗₀ X) A) → Set d

⊤ᴬ : Admissible A 0ℓ
⊤ᴬ _ _ _ = ⊤

Respects≈Env : Admissible A d → Set (o ⊔ cs ⊔ ℓs ⊔ d)
Respects≈Env Adm = ∀ {W X u v} → u Env.≈ v → Adm W X u → Adm W X v

-- A morphism that preserves admissibility
ClosedUnder : Admissible A d → X ℐ.⇒ Y → Set (o ⊔ cs ⊔ d)
ClosedUnder {X = X} {Y} Adm s = ∀ W e → Adm W Y e → Adm W X (regradeEnv W s e)

------------------------------------------------------------------------
-- Robustness

module _ (P : Predℰ A p) (Adm : Admissible B d) where
  Robust : A 𝒞.⇒ T₀ X B → Set (o ⊔ cs ⊔ d ⊔ p)
  Robust {X = X} f = ∀ W e → Adm W X e → P W ⟨$⟩ run W f e

  robust-resp-≈ᵁ : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g → Robust g → Robust f
  robust-resp-≈ᵁ u rob W e adm = Equivalence.from (Func.cong (P W) (KE.run∼ (u W))) (rob W e adm)

  robust-sub : {g : A 𝒞.⇒ T₀ Y B} (s : Y ℐ.⇒ X) → ClosedUnder Adm s → Robust g → Robust (sub s 𝒞.∘ g)
  robust-sub {g = g} s cl rob W e adm =
    Equivalence.from (Func.cong (P W) (run-sub W s g e)) (rob W (regradeEnv W s e) (cl W e adm))

  ------------------------------------------------------------------------
  -- Preservation

  -- Preservation at a fixed simulator
  uc-preserves-at : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} (s : Y ℐ.⇒ X)
                  → f ≈ᵁ sub s 𝒞.∘ g → ClosedUnder Adm s → Robust g → Robust f
  uc-preserves-at s u cl rob = robust-resp-≈ᵁ u (robust-sub s cl rob)

  -- When admissible environments form a presheaf, robustness is always preserved
  uc-preserves : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → ((s : Y ℐ.⇒ X) → ClosedUnder Adm s)
               → f ≤UC g → Robust g → Robust f
  uc-preserves cl le = let s , u = ≤UC⇒dummy le in uc-preserves-at s u (cl s)

------------------------------------------------------------------------
-- environments that arise via pullback from environments on V

module _ (V : ℐ.Obj) where
  Factors : Admissible B (ℓ ⊔ cs ⊔ ℓs)
  Factors {B = B} W X e = ∃[ a ] Σ[ d ∈ Env (T₀ (W ⊗₀ V) B) ] e Env.≈ regradeEnv W a d

  factors-resp : Respects≈Env (Factors {B})
  factors-resp eq (a , d , p) = a , d , Env.trans (Env.sym eq) p

  factors-closed : (s : Y ℐ.⇒ X) → ClosedUnder (Factors {B}) s
  factors-closed s W e (a , d , p) =
    a ℐ.∘ s , d , Env.trans (pull-cong (sub (ℐ.id ⊗₁ s)) p) (regrade-∘ W a s d)
