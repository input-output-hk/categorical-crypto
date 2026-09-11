{-# OPTIONS --safe --without-K #-}

-- Factoring a graded morphism through a PURE stage, and what the UC order does
-- with it.  Three statements, all of them about `_≤UC_` and none of them new
-- metatheory:
--
--   `∙-return`    a graded composite whose second factor is pure collapses:
--                 `h ∙ (return ∘ w)` is `h ∘ w`, once the unit grade `ℐ.unit`
--                 the composition introduced is removed by `sub λ⇒`.  This is
--                 the graded Kleisli triple's right unit law and nothing else.
--   `≤UC-resp-≈` emulation is a congruence for 𝒞-equality on both sides.
--   `≤UC-sub`     a SPLIT regrading acts on emulation.  Post-composing `sub c`
--                 on both sides is not a congruence in general — the simulator
--                 would have to commute with `c` — but a retraction `r` of `c`
--                 conjugates it, `c ∘ s₀ ∘ r` being the simulator that works.
--
-- Together they are what turns `UC-compose` at a pure second factor into an
-- emulation between the ungraded composites: the grade the Kleisli composition
-- introduces is a unit, hence split, hence invisible to the order.
-- `CategoricalCrypto.UC.Factor` is that consequence at the machine model.

open import Data.Product.Base using (_,_; proj₁; proj₂)

open import CategoricalCrypto.Abstract2 using (module AbstractUC)
open import CategoricalCrypto.UCSetup using (UCSetup)

module CategoricalCrypto.Abstract2.Factor
  {o ℓ e o′ ℓ′ e′ cs ℓs} (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open AbstractUC setup

private variable
  A B C′ : 𝒞.Obj
  X Y P : ℐ.Obj

-- `return ∘ w` is graded at the unit, so `h ∙ (return ∘ w)` is graded at
-- `ℐ.unit ⊗₀ P`; `sub λ⇒` is the regrading back.
∙-return : (h : B 𝒞.⇒ T₀ P C′) (w : A 𝒞.⇒ B)
         → sub λ⇒ 𝒞.∘ (h ∙ (return 𝒞.∘ w)) 𝒞.≈ h 𝒞.∘ w
∙-return h w = let open 𝒞 in begin
    sub λ⇒ ∘ ext ℐ.unit h ∘ return ∘ w    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    sub λ⇒ ∘ (ext ℐ.unit h ∘ return) ∘ w  ≈⟨ sym-assoc ⟩
    (sub λ⇒ ∘ ext ℐ.unit h ∘ return) ∘ w  ≈⟨ ext-identityʳ ⟩∘⟨refl ⟩
    h ∘ w                                 ∎

≤UC-resp-≈ : {f f′ : A 𝒞.⇒ T₀ X B} {g g′ : A 𝒞.⇒ T₀ Y B}
           → f 𝒞.≈ f′ → g 𝒞.≈ g′ → f ≤UC g → f′ ≤UC g′
≤UC-resp-≈ ef eg p a =
  let s , e = p a
  in s , ≈ᵁ-trans (≈C⇒≈ᵁ (𝒞.∘-resp-≈ʳ (𝒞.Equiv.sym ef)))
                  (≈ᵁ-trans e (≈C⇒≈ᵁ (𝒞.∘-resp-≈ʳ eg)))

≤UC-sub : (c : X ℐ.⇒ Y) (r : Y ℐ.⇒ X) → r ℐ.∘ c ℐ.≈ ℐ.id
        → {f g : A 𝒞.⇒ T₀ X B} → f ≤UC g → sub c 𝒞.∘ f ≤UC sub c 𝒞.∘ g
≤UC-sub {X = X} c r inv {f} {g} p = dummy-complete (c ℐ.∘ s₀ ℐ.∘ r , eq)
  where
  s₀ : X ℐ.⇒ X
  s₀ = proj₁ (p ℐ.id)

  em : f ≈ᵁ sub s₀ 𝒞.∘ g
  em = ≈ᵁ-trans (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ f))) (proj₂ (p ℐ.id))

  -- The conjugation, which is where the retraction is spent.
  grade : (c ℐ.∘ s₀ ℐ.∘ r) ℐ.∘ c ℐ.≈ c ℐ.∘ s₀
  grade = let open ℐ.HomReasoning in begin
      (c ℐ.∘ s₀ ℐ.∘ r) ℐ.∘ c  ≈⟨ ℐ.assoc ⟩
      c ℐ.∘ (s₀ ℐ.∘ r) ℐ.∘ c  ≈⟨ refl⟩∘⟨ ℐ.assoc ⟩
      c ℐ.∘ s₀ ℐ.∘ r ℐ.∘ c    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ inv ⟩
      c ℐ.∘ s₀ ℐ.∘ ℐ.id       ≈⟨ refl⟩∘⟨ ℐ.identityʳ ⟩
      c ℐ.∘ s₀                ∎

  strict : sub c 𝒞.∘ sub s₀ 𝒞.∘ g 𝒞.≈ sub (c ℐ.∘ s₀ ℐ.∘ r) 𝒞.∘ (sub c 𝒞.∘ g)
  strict = let open 𝒞 in begin
      sub c ∘ sub s₀ ∘ g                  ≈⟨ sym-assoc ⟩
      (sub c ∘ sub s₀) ∘ g                ≈⟨ ⟺ sub-homomorphism ⟩∘⟨refl ⟩
      sub (c ℐ.∘ s₀) ∘ g                  ≈⟨ sub-resp-≈ (ℐ.Equiv.sym grade) ⟩∘⟨refl ⟩
      sub ((c ℐ.∘ s₀ ℐ.∘ r) ℐ.∘ c) ∘ g    ≈⟨ sub-homomorphism ⟩∘⟨refl ⟩
      (sub (c ℐ.∘ s₀ ℐ.∘ r) ∘ sub c) ∘ g  ≈⟨ assoc ⟩
      sub (c ℐ.∘ s₀ ℐ.∘ r) ∘ sub c ∘ g    ∎

  eq : sub c 𝒞.∘ f ≈ᵁ sub (c ℐ.∘ s₀ ℐ.∘ r) 𝒞.∘ (sub c 𝒞.∘ g)
  eq = ≈ᵁ-trans (sub-cong c em) (≈C⇒≈ᵁ strict)
