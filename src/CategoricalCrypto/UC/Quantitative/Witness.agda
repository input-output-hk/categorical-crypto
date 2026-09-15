{-# OPTIONS --safe --without-K #-}

-- Quantitative emulation witnesses and their composition
-- (`docs/quantitative-uc-setup-plan.typ` §5.2).
--
-- A witness is a simulator TOGETHER WITH an error: `At s ε f g` says `s` brings
-- `g` within ε of `f` in every prefix context.  `Witness` is the dummy form and
-- `Witness⁺` the universal one, and the two are interderivable at a FIXED
-- error — the simulator is one morphism, never a function of the accuracy.
--
-- Both composition theorems are derived, not assumed: `at-trans` and
-- `at-compose` are the graded decomposition identities of `Abstract2` with the
-- error carried along, and the arithmetic they spend is only that `ε₀` is a
-- unit up to `⊑`.  `at-compose`'s error is `εu ⊕ εf` in that order because the
-- chain absorbs the second leg first (`ctx-pre`, then `ctx-ext`).
--
-- Simulators stay proof-relevant morphisms of `ℐ`: whatever feasibility or cost
-- evidence that category carries is inherited here and is never erased.

open import Data.Product.Base using (Σ-syntax; _,_)
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.UC.Quantitative.Witness
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.UC.Quantitative E

module QWitness {o ℓ e o′ ℓ′ e′ c ℓb : Level}
                (S : QUCSetup o ℓ e o′ ℓ′ e′ c ℓb) where

  open QuantitativeUC S public

  private variable
    A B C′ : 𝒞.Obj
    X Y Z P R : ℐ.Obj
    ε δ εf εu : Error

  At : (s : Y ℐ.⇒ X) → Error → (f : A 𝒞.⇒ T₀ X B) (g : A 𝒞.⇒ T₀ Y B)
     → Set (o ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)
  At s ε f g = f ≈ᵁ[ ε ] (sub s 𝒞.∘ g)

  Witness Witness⁺ : Error → (f : A 𝒞.⇒ T₀ X B) (g : A 𝒞.⇒ T₀ Y B)
                   → Set (o ⊔ ℓ ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)
  Witness {X = X} {Y = Y} ε f g = Σ[ s ∈ Y ℐ.⇒ X ] At s ε f g
  Witness⁺ {X = X} ε f g = {X′ : ℐ.Obj} (a : X ℐ.⇒ X′) → Witness ε (sub a 𝒞.∘ f) g

  ------------------------------------------------------------------------
  -- Dummy and universal

  dummy⇒universal : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                  → Witness ε f g → Witness⁺ ε f g
  dummy⇒universal {g = g} (s₀ , h) a =
    a ℐ.∘ s₀ , ctx-mono ⊕-identityʳ (ctx-trans (ctx-sub a h) (≈C⇒ctx strict))
    where strict : sub a 𝒞.∘ sub s₀ 𝒞.∘ g 𝒞.≈ sub (a ℐ.∘ s₀) 𝒞.∘ g
          strict = let open 𝒞 in sym-assoc ○ ⟺ sub-homomorphism ⟩∘⟨refl

  universal⇒dummy : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                  → Witness⁺ ε f g → Witness ε f g
  universal⇒dummy {f = f} u =
    let s , h = u ℐ.id in s , ctx-resp (sub-identityˡ f) 𝒞.Equiv.refl h

  ------------------------------------------------------------------------
  -- Composition

  at-trans : {s : Y ℐ.⇒ X} {t : Z ℐ.⇒ Y} {f : A 𝒞.⇒ T₀ X B}
             {g : A 𝒞.⇒ T₀ Y B} {h : A 𝒞.⇒ T₀ Z B}
           → At s ε f g → At t δ g h → At (s ℐ.∘ t) (ε ⊕ δ) f h
  at-trans {s = s} {t = t} {h = h} e₁ e₂ =
    ctx-mono (⊕-mono ⊑-refl ⊕-identityʳ)
      (ctx-trans e₁ (ctx-trans (ctx-sub s e₂) (≈C⇒ctx strict)))
    where strict : sub s 𝒞.∘ sub t 𝒞.∘ h 𝒞.≈ sub (s ℐ.∘ t) 𝒞.∘ h
          strict = let open 𝒞 in sym-assoc ○ ⟺ sub-homomorphism ⟩∘⟨refl

  at-compose : {s : Y ℐ.⇒ X} {t : R ℐ.⇒ P}
               {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
               {u : B 𝒞.⇒ T₀ P C′} {v : B 𝒞.⇒ T₀ R C′}
             → At s εf f g → At t εu u v
             → At ((ℐ.id ⊗₁ t) ℐ.∘ (s ⊗₁ ℐ.id)) (εu ⊕ εf) (u ∙ f) (v ∙ g)
  at-compose {Y = Y} {X = X} {s = s} {t = t} {f = f} {g = g} {v = v} ef eu =
    ctx-mono (⊕-mono ⊑-refl ⊕-identityʳ)
      (ctx-trans (ctx-pre f eu) (ctx-trans (ctx-ext (sub t 𝒞.∘ v) ef) (≈C⇒ctx strict)))
    where
    strict : ext X (sub t 𝒞.∘ v) 𝒞.∘ sub s 𝒞.∘ g
           𝒞.≈ sub ((ℐ.id ⊗₁ t) ℐ.∘ (s ⊗₁ ℐ.id)) 𝒞.∘ ext Y v 𝒞.∘ g
    strict = let open 𝒞 in begin
        ext X (sub t ∘ v) ∘ sub s ∘ g
          ≈⟨ sub-commute₂ ⟩∘⟨refl ⟩
        (sub (ℐ.id ⊗₁ t) ∘ ext X v) ∘ sub s ∘ g
          ≈⟨ assoc ⟩
        sub (ℐ.id ⊗₁ t) ∘ ext X v ∘ sub s ∘ g
          ≈⟨ refl⟩∘⟨ sym-assoc ⟩
        sub (ℐ.id ⊗₁ t) ∘ (ext X v ∘ sub s) ∘ g
          ≈⟨ refl⟩∘⟨ (sub-commute₁ ⟩∘⟨refl) ⟩
        sub (ℐ.id ⊗₁ t) ∘ (sub (s ⊗₁ ℐ.id) ∘ ext Y v) ∘ g
          ≈⟨ refl⟩∘⟨ assoc ⟩
        sub (ℐ.id ⊗₁ t) ∘ sub (s ⊗₁ ℐ.id) ∘ ext Y v ∘ g
          ≈⟨ sym-assoc ⟩
        (sub (ℐ.id ⊗₁ t) ∘ sub (s ⊗₁ ℐ.id)) ∘ ext Y v ∘ g
          ≈⟨ (⟺ sub-homomorphism) ⟩∘⟨refl ⟩
        sub ((ℐ.id ⊗₁ t) ℐ.∘ (s ⊗₁ ℐ.id)) ∘ ext Y v ∘ g  ∎
