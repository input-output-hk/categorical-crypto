{-# OPTIONS --safe --without-K #-}

-- The locally graded ("naive one-sided") UC layer.  A protocol/functionality is
-- a bare graded-Kleisli morphism f : A ⇒ T₀ X B — the adversary interface X is
-- the grade, carried on the morphism — and an adversary/simulator is a grade
-- morphism acting by `sub`.  Observational equivalence is the U-kernel _≈ᵁ_,
-- the kernel of the ENRICHED forgetful functor into graded families: all
-- prefix-context components μ ∘ T₁ agree under the bare kernel _≈ℰ_ (the
-- layer-0 structure is McDermott–Uustalu, MPC 2022).  Over ≈ᵁ the four UC
-- metatheorems — ≤UC-refl, dummy-complete, ≤UC-trans, UC-compose — are
-- hypothesis-free.  `GradeStable` (the ℳ-module property of ℰ) is sufficient
-- for the converse of ≈ᵁ⇒≈ℰ and is needed only by `bridge`, which ingests a
-- bare ≈ℰ artifact into the compositional world — a conservation law paid once
-- at artifact ingestion, never in the metatheory.

module CategoricalCrypto.Abstract2 where

import Relation.Binary.Reasoning.Setoid as SetoidR
open import Data.Product
open import Function.Bundles
open import Level
open import Relation.Binary.Bundles

open import Categories.LocallyGraded
import Categories.LocallyGraded.Kleisli as LGKleisli

open import CategoricalCrypto.UCSetup

module AbstractUC
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  where
  open UCSetup setup public

  private variable
    A B C′ : 𝒞.Obj
    X X′ Y Z P Q : ℐ.Obj

  infix  4 _≈ᵁ_ _≤UC_

  ------------------------------------------------------------------------
  -- The U-kernel ≈ᵁ and its congruences
  ------------------------------------------------------------------------

  _≈ᵁ_ : (f g : A 𝒞.⇒ T₀ X B) → Set (o ⊔ cs ⊔ ℓs)
  _≈ᵁ_ {X = X} f g = ∀ Y → μ Y X 𝒞.∘ T₁ Y f ≈ℰ μ Y X 𝒞.∘ T₁ Y g

  ≈ᵁ-refl : {f : A 𝒞.⇒ T₀ X B} → f ≈ᵁ f
  ≈ᵁ-refl _ = ≈ℰ-refl

  ≈ᵁ-sym : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g → g ≈ᵁ f
  ≈ᵁ-sym e Y = ≈ℰ-sym (e Y)

  ≈ᵁ-trans : {f g h : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g → g ≈ᵁ h → f ≈ᵁ h
  ≈ᵁ-trans e₁ e₂ Y = ≈ℰ-trans (e₁ Y) (e₂ Y)

  ≈ᵁ-setoid : (A B : 𝒞.Obj) (X : ℐ.Obj) → Setoid ℓ′ (o ⊔ cs ⊔ ℓs)
  ≈ᵁ-setoid A B X = record
    { Carrier = A 𝒞.⇒ T₀ X B
    ; _≈_ = _≈ᵁ_
    ; isEquivalence = record { refl = ≈ᵁ-refl ; sym = ≈ᵁ-sym ; trans = ≈ᵁ-trans } }

  ≈C⇒≈ᵁ : {f g : A 𝒞.⇒ T₀ X B} → f 𝒞.≈ g → f ≈ᵁ g
  ≈C⇒≈ᵁ e _ = ≈C⇒≈ℰ (𝒞.∘-resp-≈ʳ (T-resp-≈ e))

  sub-cong : (c : X ℐ.⇒ X′) {x x′ : A 𝒞.⇒ T₀ X B} → x ≈ᵁ x′ → sub c 𝒞.∘ x ≈ᵁ sub c 𝒞.∘ x′
  sub-cong c {x} {x′} e Y = ≈ℰ-trans (≈C⇒≈ℰ (sub-decomp c x Y))
      (≈ℰ-trans (≈ℰ-cong-post (sub (ℐ.id ⊗₁ c)) (e Y))
                (≈ℰ-sym (≈C⇒≈ℰ (sub-decomp c x′ Y))))

  ext-cong : (k : B 𝒞.⇒ T₀ P C′) {f f′ : A 𝒞.⇒ T₀ X B}
           → f ≈ᵁ f′ → ext X k 𝒞.∘ f ≈ᵁ ext X k 𝒞.∘ f′
  ext-cong {X = X} k {f} {f′} e W = ≈ℰ-trans (≈C⇒≈ℰ (∙-decomp k f W))
      (≈ℰ-trans (≈ℰ-cong-post (sub α⇒ 𝒞.∘ ext (W ⊗₀ X) k) (e W))
                (≈ℰ-sym (≈C⇒≈ℰ (∙-decomp k f′ W))))

  ∙-cong-arg : {h h′ : B 𝒞.⇒ T₀ P C′} (f : A 𝒞.⇒ T₀ X B)
             → h ≈ᵁ h′ → ext X h 𝒞.∘ f ≈ᵁ ext X h′ 𝒞.∘ f
  ∙-cong-arg {X = X} {h = h} {h′} f e W = ≈ℰ-trans (≈C⇒≈ℰ (∙-decomp h f W))
      (≈ℰ-trans (≈ℰ-cong-pre (μ W X 𝒞.∘ T₁ W f) (≈ℰ-cong-post (sub α⇒) extℰ))
                (≈ℰ-sym (≈C⇒≈ℰ (∙-decomp h′ f W))))
    where extℰ : ext (W ⊗₀ X) h ≈ℰ ext (W ⊗₀ X) h′
          extℰ = ≈ℰ-trans (≈ℰ-sym (≈C⇒≈ℰ (μT h))) (≈ℰ-trans (e (W ⊗₀ X)) (≈C⇒≈ℰ (μT h′)))

  ------------------------------------------------------------------------
  -- ≈ᵁ refines ≈ℰ; GradeStable suffices for the converse
  ------------------------------------------------------------------------

  subλ⇐λ⇒ : sub λ⇐ 𝒞.∘ sub λ⇒ 𝒞.≈ 𝒞.id {T₀ (ℐ.unit ⊗₀ X) A}
  subλ⇐λ⇒ = let open 𝒞 in ⟺ sub-homomorphism ○ (sub-resp-≈ ℐ.unitorˡ.isoˡ ○ sub-identity)

  λ-cancel : (x : A 𝒞.⇒ T₀ X B) → sub λ⇒ 𝒞.∘ sub λ⇐ 𝒞.∘ x 𝒞.≈ x
  λ-cancel x = let open 𝒞 in begin
      sub λ⇒ ∘ sub λ⇐ ∘ x    ≈⟨ sym-assoc ⟩
      (sub λ⇒ ∘ sub λ⇐) ∘ x  ≈⟨ subλ⇒λ⇐ ⟩∘⟨refl ⟩
      𝒞.id ∘ x               ≈⟨ identityˡ ⟩
      x                      ∎
    where subλ⇒λ⇐ : sub λ⇒ 𝒞.∘ sub λ⇐ 𝒞.≈ 𝒞.id
          subλ⇒λ⇐ = let open 𝒞 in ⟺ sub-homomorphism ○ (sub-resp-≈ ℐ.unitorˡ.isoʳ ○ sub-identity)

  unit-comp : (f : A 𝒞.⇒ T₀ X B)
            → (μ ℐ.unit X 𝒞.∘ T₁ ℐ.unit f) 𝒞.∘ return 𝒞.≈ sub λ⇐ 𝒞.∘ f
  unit-comp {X = X} f = let open 𝒞 in begin
      (μ ℐ.unit X ∘ T₁ ℐ.unit f) ∘ return  ≈⟨ assoc ⟩
      μ ℐ.unit X ∘ T₁ ℐ.unit f ∘ return    ≈⟨ refl⟩∘⟨ ⟺ return-commute ⟩
      μ ℐ.unit X ∘ return ∘ f              ≈⟨ sym-assoc ⟩
      (μ ℐ.unit X ∘ return) ∘ f            ≈⟨ μunit-return ⟩∘⟨refl ⟩
      sub λ⇐ ∘ f                           ∎
    where μunit-return : μ ℐ.unit X 𝒞.∘ return 𝒞.≈ sub λ⇐
          μunit-return = let open 𝒞 in begin
              μ ℐ.unit X ∘ return                        ≈⟨ introˡ subλ⇐λ⇒ ⟩
              (sub λ⇐ ∘ sub λ⇒) ∘ μ ℐ.unit X ∘ return    ≈⟨ assoc ⟩
              sub λ⇐ ∘ sub λ⇒ ∘ μ ℐ.unit X ∘ return      ≈⟨ refl⟩∘⟨ μ-identityˡ ⟩
              sub λ⇐ ∘ 𝒞.id                              ≈⟨ identityʳ ⟩
              sub λ⇐                                     ∎

  ≈ᵁ⇒≈ℰ : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g → f ≈ℰ g
  ≈ᵁ⇒≈ℰ {f = f} {g} e = ≈ℰ-trans (≈ℰ-sym (≈C⇒≈ℰ (λ-cancel f)))
      (≈ℰ-trans (≈ℰ-cong-post (sub λ⇒) key) (≈C⇒≈ℰ (λ-cancel g)))
    where key : (sub λ⇐ 𝒞.∘ f) ≈ℰ (sub λ⇐ 𝒞.∘ g)
          key = ≈ℰ-trans (≈ℰ-sym (≈C⇒≈ℰ (unit-comp f)))
                  (≈ℰ-trans (≈ℰ-cong-pre return (e ℐ.unit)) (≈C⇒≈ℰ (unit-comp g)))

  bridge : {f g : A 𝒞.⇒ T₀ X B} → GradeStable → f ≈ℰ g → f ≈ᵁ g
  bridge {X = X} gs e Y = ≈ℰ-cong-post (μ Y X) (gs Y e)

  ------------------------------------------------------------------------
  -- The UC metatheory
  ------------------------------------------------------------------------

  _≤UC_ : A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ Y B → Set (o ⊔ ℓ ⊔ cs ⊔ ℓs)
  _≤UC_ {X = X} {Y = Y} f g =
    ∀ {X′} (a : X ℐ.⇒ X′) → Σ[ s ∈ Y ℐ.⇒ X′ ] sub a 𝒞.∘ f ≈ᵁ sub s 𝒞.∘ g

  -- dummy variant, equivalent to `_≤UC_` (see below)
  _≤UCᵈ_ : A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ Y B → Set (o ⊔ ℓ ⊔ cs ⊔ ℓs)
  _≤UCᵈ_ {X = X} {Y = Y} f g = Σ[ s ∈ Y ℐ.⇒ X ] f ≈ᵁ sub s 𝒞.∘ g

  ≤UC-refl : (f : A 𝒞.⇒ T₀ X B) → f ≤UC f
  ≤UC-refl f a = a , ≈ᵁ-refl

  ≤UC-trans : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} {h : A 𝒞.⇒ T₀ Z B}
            → f ≤UC g → g ≤UC h → f ≤UC h
  ≤UC-trans f≤g g≤h a =
    let (s₁ , e₁) = f≤g a
        (s₂ , e₂) = g≤h s₁
    in s₂ , ≈ᵁ-trans e₁ e₂

  ≤UC-resp-≈ : {f f′ : A 𝒞.⇒ T₀ X B} {g g′ : A 𝒞.⇒ T₀ Y B}
             → f 𝒞.≈ f′ → g 𝒞.≈ g′ → f ≤UC g → f′ ≤UC g′
  ≤UC-resp-≈ ef eg p a =
    let s , e = p a
    in s , ≈ᵁ-trans (≈C⇒≈ᵁ (𝒞.∘-resp-≈ʳ (𝒞.Equiv.sym ef)))
                    (≈ᵁ-trans e (≈C⇒≈ᵁ (𝒞.∘-resp-≈ʳ eg)))

  dummy-complete : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
                 → Σ[ s₀ ∈ Y ℐ.⇒ X ] f ≈ᵁ sub s₀ 𝒞.∘ g
                 → f ≤UC g
  dummy-complete {g = g} (s₀ , e) a = a ℐ.∘ s₀ , ≈ᵁ-trans (sub-cong a e) (≈C⇒≈ᵁ strict)
    where strict : sub a 𝒞.∘ sub s₀ 𝒞.∘ g 𝒞.≈ sub (a ℐ.∘ s₀) 𝒞.∘ g
          strict = let open 𝒞 in sym-assoc ○ ⟺ sub-homomorphism ⟩∘⟨refl

  ≈ᵁ⇒≤UC : {f g : A 𝒞.⇒ T₀ X B} → f ≈ᵁ g → f ≤UC g
  ≈ᵁ⇒≤UC {g = g} h = dummy-complete (ℐ.id , ≈ᵁ-trans h (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ g))))

  ≤UC⇒dummy : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
            → f ≤UC g → Σ[ s ∈ Y ℐ.⇒ X ] f ≈ᵁ sub s 𝒞.∘ g
  ≤UC⇒dummy {f = f} le =
    let s , e = le ℐ.id in s , ≈ᵁ-trans (≈ᵁ-sym (≈C⇒≈ᵁ (sub-identityˡ f))) e

  ≤UCᵈ⇔≤UC : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → f ≤UCᵈ g ⇔ f ≤UC g
  ≤UCᵈ⇔≤UC {f = f} {g} = mk⇔ {B = f ≤UC g} dummy-complete ≤UC⇒dummy

  UC-compose : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
               {h : B 𝒞.⇒ T₀ P C′} {k : B 𝒞.⇒ T₀ Q C′}
             → f ≤UC g → h ≤UC k → h ∙ f ≤UC k ∙ g
  UC-compose {X = X} {Y = Y} {P = P} {Q = Q} {f = f} {g = g} {h = h} {k = k} f≤g h≤k {Z} a =
      s , (let open SetoidR (≈ᵁ-setoid _ _ _) in begin
        sub a 𝒞.∘ (h ∙ f)
          ≈⟨ sub-cong a (∙-cong-arg f (proj₂ (≤UC⇒dummy h≤k))) ⟩
        sub a 𝒞.∘ ext X (sub t 𝒞.∘ k) 𝒞.∘ f
          ≈⟨ sub-cong a (ext-cong (sub t 𝒞.∘ k) (proj₂ (≤UC⇒dummy f≤g))) ⟩
        sub a 𝒞.∘ ext X (sub t 𝒞.∘ k) 𝒞.∘ sub sf 𝒞.∘ g
          ≈⟨ ≈C⇒≈ᵁ strict-final ⟩
        sub s 𝒞.∘ k ∙ g  ∎)
    where
      t : Q ℐ.⇒ P
      t = proj₁ (≤UC⇒dummy h≤k)

      sf : Y ℐ.⇒ X
      sf = proj₁ (≤UC⇒dummy f≤g)

      s : Y ⊗₀ Q ℐ.⇒ Z
      s = a ℐ.∘ ℐ.id ⊗₁ t ℐ.∘ sf ⊗₁ ℐ.id

      strict-final : sub a 𝒞.∘ ext X (sub t 𝒞.∘ k) 𝒞.∘ sub sf 𝒞.∘ g
                   𝒞.≈ sub s 𝒞.∘ ext Y k 𝒞.∘ g
      strict-final = let open 𝒞 in begin
          sub a ∘ ext X (sub t ∘ k) ∘ sub sf ∘ g
            ≈⟨ refl⟩∘⟨ (sub-commute₂ ⟩∘⟨refl) ⟩
          sub a ∘ (sub (ℐ.id ⊗₁ t) ∘ ext X k) ∘ sub sf ∘ g
            ≈⟨ refl⟩∘⟨ assoc ⟩
          sub a ∘ sub (ℐ.id ⊗₁ t) ∘ ext X k ∘ sub sf ∘ g
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc) ⟩
          sub a ∘ sub (ℐ.id ⊗₁ t) ∘ (ext X k ∘ sub sf) ∘ g
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (sub-commute₁ ⟩∘⟨refl)) ⟩
          sub a ∘ sub (ℐ.id ⊗₁ t) ∘ (sub (sf ⊗₁ ℐ.id) ∘ ext Y k) ∘ g
            ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc) ⟩
          sub a ∘ sub (ℐ.id ⊗₁ t) ∘ sub (sf ⊗₁ ℐ.id) ∘ ext Y k ∘ g
            ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          sub a ∘ (sub (ℐ.id ⊗₁ t) ∘ sub (sf ⊗₁ ℐ.id)) ∘ ext Y k ∘ g
            ≈⟨ sym-assoc ⟩
          (sub a ∘ sub (ℐ.id ⊗₁ t) ∘ sub (sf ⊗₁ ℐ.id)) ∘ ext Y k ∘ g
            ≈⟨ (refl⟩∘⟨ (⟺ sub-homomorphism)) ⟩∘⟨refl ⟩
          (sub a ∘ sub (ℐ.id ⊗₁ t ℐ.∘ sf ⊗₁ ℐ.id)) ∘ ext Y k ∘ g
            ≈⟨ (⟺ sub-homomorphism) ⟩∘⟨refl ⟩
          sub s ∘ ext Y k ∘ g  ∎

  -- Note the hom-equality of this packaging is 𝒞._≈_, NOT ≈ᵁ.
  naiveKleisli : LocallyGradedCategory ℐ o′ ℓ′ e′
  naiveKleisli = LGKleisli.naiveKleisli triple

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
