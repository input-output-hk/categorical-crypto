{-# OPTIONS --safe --without-K #-}

-- OAP (open adversarial protocols) is the graded Kleisli category of
-- ℳ over ℐ; OP is the graded Kleisli category of the same ℳ
-- restricted to coherence isomorphisms on the grading.

module CategoricalCrypto.Abstract where

open import Level
open import Data.Product
open import Relation.Binary.Bundles
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.CoherenceIsos
open import Categories.Functor
import Categories.GradedKleisli as GK
import Categories.GradedKleisli.Regrade as Rg
import Categories.KernelCongruence as KernelCong
import Categories.KernelCongruence.Reindex as KernelReindex

open import CategoricalCrypto.UCSetup

module AbstractUC
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  where
  open UCSetup setup public
  open Coherence ℐ
  module ℂ = MonoidalCategory Coh

  OAP      = Rg.Klℐ       𝒞 Coh ℐ ⟦-⟧-monoidal triple
  OP       = Rg.Kl𝒥       𝒞 Coh ℐ ⟦-⟧-monoidal triple
  Regrade₀ = Rg.Regrade₀  𝒞 Coh ℐ ⟦-⟧-monoidal triple
  Regrade₁ = Rg.Regrade₁  𝒞 Coh ℐ ⟦-⟧-monoidal triple
  ι-hom    = Functor.homomorphism (Rg.Regrade 𝒞 Coh ℐ ⟦-⟧-monoidal triple)
  module OAP = Category OAP
  module OP  = Category OP

  U-resp = GK.U-resp 𝒞 ℐ triple
  U-∘C   = GK.U-∘ 𝒞 ℐ triple

  infix  10 _⇒ᴼ_ _⇒ᴼᴾ_
  infix  4  _≤UC_

  Iᵤ : Category o ℓ e
  Iᵤ = ℐ.U


  ⟨_,_⟩ : 𝒞.Obj → ℐ.Obj → OAP.Obj
  ⟨ A , I ⟩ = I , A

  car : OAP.Obj → 𝒞.Obj
  car = proj₂
  grd : OAP.Obj → ℐ.Obj
  grd = proj₁

  _⇒ᴼ_ : OAP.Obj → OAP.Obj → Set (o ⊔ ℓ ⊔ ℓ′)
  A ⇒ᴼ B = OAP [ A , B ]

  pattern mkᴼ X f a = X , f , a

  U : ∀ {A B} → (A ⇒ᴼ B) → T₀ (grd A) (car A) 𝒞.⇒ T₀ (grd B) (car B)
  U = GK.U₁ 𝒞 ℐ triple

  U-functor : Functor OAP 𝒞
  U-functor = GK.U-functor 𝒞 ℐ triple

  -- `_≈ℰ'_` is the kernel congruence of ℰ∘Uᵒᵖ on OAP-homs
  module KO = KernelCong (Category.op OAP) (Setoids cs ℓs) (ℰ ∘F Functor.op U-functor)
  module KU = KernelReindex (Functor.op U-functor) ℰ

  open KO using () renaming
    ( _∼_ to _≈ℰ'_; ∼-sym to ≈'-sym; ∼-congˡ to ≈'-congʳ; ∼-congʳ to ≈'-congˡ
    ; ≈⇒∼ to ≋⇒≈ℰ' ) public

  ≈'-setoid : (A B : OAP.Obj) → Setoid (o ⊔ ℓ ⊔ ℓ′) (cs ⊔ ℓs)
  ≈'-setoid A B = KO.∼-setoid B A

  U-≈ℰ⇒≈ℰ' : ∀ {A B} {x y : A ⇒ᴼ B} → U x ≈ℰ U y → x ≈ℰ' y
  U-≈ℰ⇒≈ℰ' = KU.∼⇒∼∘

  ≈ℰ'⇒U-≈ℰ : ∀ {A B} {x y : A ⇒ᴼ B} → x ≈ℰ' y → U x ≈ℰ U y
  ≈ℰ'⇒U-≈ℰ = KU.∼∘⇒∼

  U-≋ : ∀ {A B} {x y : A ⇒ᴼ B} → x OAP.≈ y → U x ≈ℰ U y
  U-≋ p = ≈C⇒≈ℰ (U-resp p)

  U-∘ : ∀ {A B C} (x : B ⇒ᴼ C) (y : A ⇒ᴼ B) → U (x OAP.∘ y) ≈ℰ (U x 𝒞.∘ U y)
  U-∘ x y = ≈C⇒≈ℰ (U-∘C x y)

  ------------------------------------------------------------------------
  -- Attacks
  ------------------------------------------------------------------------

  -- an attack on the identity protocol
  pureAtk : ∀ {A X Y} → X ℐ.⇒ Y  → ⟨ A , X ⟩ ⇒ᴼ ⟨ A , Y ⟩
  pureAtk a = mkᴼ ℐ.unit return (a ℐ.∘ ρ⇒)

  U-pureAtk : ∀ {A X Y} (a : X ℐ.⇒ Y) → U (pureAtk {A} a) 𝒞.≈ sub a
  U-pureAtk _ = 𝒞.pushˡ sub-homomorphism 𝒞.○ 𝒞.elimʳ ext-identityˡ

  pureAtk-id : ∀ {A X} → U (pureAtk {A} {X} ℐ.id) ≈ℰ 𝒞.id
  pureAtk-id = ≈C⇒≈ℰ (U-pureAtk ℐ.id ○ sub-identity)
    where open 𝒞.HomReasoning

  Objᴼᴾ : Set (o ⊔ o′)
  Objᴼᴾ = Category.Obj OP

  ⟨_,_⟩ᴼᴾ : 𝒞.Obj → ℂ.Obj → Objᴼᴾ
  ⟨ A , I ⟩ᴼᴾ = I , A

  _⇒ᴼᴾ_ : Objᴼᴾ → Objᴼᴾ → Set (o ⊔ ℓ′)
  A ⇒ᴼᴾ B = OP [ A , B ]

  ι : ∀ {A B} → A ⇒ᴼᴾ B → Regrade₀ A ⇒ᴼ Regrade₀ B
  ι = Regrade₁

  ------------------------------------------------------------------------
  -- The pure-attack algebra
  ------------------------------------------------------------------------


  atk-idˡ : ∀ {A B} (x : A ⇒ᴼ B) → pureAtk ℐ.id OAP.∘ x ≈ℰ' x
  atk-idˡ x = U-≈ℰ⇒≈ℰ' (begin
      U (pureAtk ℐ.id OAP.∘ x)  ≈⟨ U-∘ (pureAtk ℐ.id) x ⟩
      U (pureAtk ℐ.id) 𝒞.∘ U x  ≈⟨ ≈ℰ-cong-pre (U x) pureAtk-id ⟩
      𝒞.id 𝒞.∘ U x              ≈⟨ ≈C⇒≈ℰ 𝒞.identityˡ ⟩
      U x                       ∎)
    where open SetoidR (≈ℰ-setoid _ _)

  atk-idʳ : ∀ {A B} (x : A ⇒ᴼ B) → x OAP.∘ pureAtk ℐ.id ≈ℰ' x
  atk-idʳ x = U-≈ℰ⇒≈ℰ' (begin
      U (x OAP.∘ pureAtk ℐ.id)  ≈⟨ U-∘ x (pureAtk ℐ.id) ⟩
      U x 𝒞.∘ U (pureAtk ℐ.id)  ≈⟨ ≈ℰ-cong-post (U x) pureAtk-id ⟩
      U x 𝒞.∘ 𝒞.id              ≈⟨ ≈C⇒≈ℰ 𝒞.identityʳ ⟩
      U x                       ∎)
    where open SetoidR (≈ℰ-setoid _ _)

  pureAtk-∘ : ∀ {A X Y Z} (a′ : Y ℐ.⇒ Z) (a : X ℐ.⇒ Y)
            → pureAtk {A} a′ OAP.∘ pureAtk a ≈ℰ' pureAtk (a′ ℐ.∘ a)
  pureAtk-∘ a′ a = U-≈ℰ⇒≈ℰ' (≈C⇒≈ℰ (begin
      U (pureAtk a′ OAP.∘ pureAtk a)    ≈⟨ U-∘C (pureAtk a′) (pureAtk a) ⟩
      U (pureAtk a′) 𝒞.∘ U (pureAtk a)  ≈⟨ U-pureAtk a′ ⟩∘⟨ U-pureAtk a ⟩
      sub a′ 𝒞.∘ sub a                  ≈⟨ sub-homomorphism ⟨
      sub (a′ ℐ.∘ a)                    ≈⟨ U-pureAtk (a′ ℐ.∘ a) ⟨
      U (pureAtk (a′ ℐ.∘ a))            ∎))
    where open 𝒞.HomReasoning

  -- Transport of a grade-only attack across an included OP-hom.  Its adversary
  -- part is a coherence iso `a = ⟦α⟧₁` (Coh(ℐ) is a groupoid), so sliding `s` is
  -- naturality of `sub` conjugated by `a`: the simulator is `s″ = a ∘ (s⊗id) ∘ a⁻¹`.
  pureAtk-transport : ∀ {B C : 𝒞.Obj} {K M : ℂ.Obj}
                        (k : ⟨ B , K ⟩ᴼᴾ ⇒ᴼᴾ ⟨ C , M ⟩ᴼᴾ) (s : ⟦ K ⟧₀ ℐ.⇒ ⟦ K ⟧₀)
                    → Σ[ s″ ∈ ⟦ M ⟧₀ ℐ.⇒ ⟦ M ⟧₀ ] ι k OAP.∘ pureAtk s ≈ℰ' pureAtk s″ OAP.∘ ι k
  pureAtk-transport {K = K} {M} (mkᴼ β g α) s = s″ , U-≈ℰ⇒≈ℰ' (≈C⇒≈ℰ chain)
    where
      -- `a` is the adversary component of `ι k`: ⟦α⟧₁ post-composed with the
      -- (strict, = ℐ.id) ⊗-homo the general Regrade inserts.
      a  = ⟦ α ⟧₁ ℐ.∘ ℐ.id
      a⁻¹ = ⟦ inv α ⟧₁
      s″ = a ℐ.∘ (s ℐ.⊗₁ ℐ.id) ℐ.∘ a⁻¹

      a⁻¹∘a : a⁻¹ ℐ.∘ a ℐ.≈ ℐ.id
      a⁻¹∘a = let open ℐ.HomReasoning in (refl⟩∘⟨ ℐ.identityʳ) ○ ⟦⟧-resp-≈ (inv-isoˡ α)

      ℐeqn : a ℐ.∘ (s ℐ.⊗₁ ℐ.id) ℐ.≈ s″ ℐ.∘ a
      ℐeqn = ℐ.Equiv.sym (begin
          s″ ℐ.∘ a                             ≈⟨ ℐ.assoc ⟩
          a ℐ.∘ ((s ℐ.⊗₁ ℐ.id) ℐ.∘ a⁻¹) ℐ.∘ a  ≈⟨ refl⟩∘⟨ ℐ.assoc ⟩
          a ℐ.∘ (s ℐ.⊗₁ ℐ.id) ℐ.∘ a⁻¹ ℐ.∘ a    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ a⁻¹∘a ⟩
          a ℐ.∘ (s ℐ.⊗₁ ℐ.id) ℐ.∘ ℐ.id         ≈⟨ refl⟩∘⟨ ℐ.identityʳ ⟩
          a ℐ.∘ (s ℐ.⊗₁ ℐ.id)                  ∎)
        where open ℐ.HomReasoning

      slide : U (ι (mkᴼ β g α)) 𝒞.∘ sub s 𝒞.≈ sub s″ 𝒞.∘ U (ι (mkᴼ β g α))
      slide = let open 𝒞 in
        pullʳ sub-commute₁ ○ pullˡ (⟺ sub-homomorphism) ○ (sub-resp-≈ ℐeqn ⟩∘⟨refl) ○ pushˡ sub-homomorphism

      chain : U (ι (mkᴼ β g α) OAP.∘ pureAtk s) 𝒞.≈ U (pureAtk s″ OAP.∘ ι (mkᴼ β g α))
      chain = begin
          U (ι (mkᴼ β g α) OAP.∘ pureAtk s)     ≈⟨ U-∘C (ι (mkᴼ β g α)) (pureAtk s) ⟩
          U (ι (mkᴼ β g α)) 𝒞.∘ U (pureAtk s)   ≈⟨ refl⟩∘⟨ U-pureAtk s ⟩
          U (ι (mkᴼ β g α)) 𝒞.∘ sub s           ≈⟨ slide ⟩
          sub s″ 𝒞.∘ U (ι (mkᴼ β g α))          ≈⟨ ⟺ (U-pureAtk s″) ⟩∘⟨refl ⟩
          U (pureAtk s″) 𝒞.∘ U (ι (mkᴼ β g α))  ≈⟨ U-∘C (pureAtk s″) (ι (mkᴼ β g α)) ⟨
          U (pureAtk s″ OAP.∘ ι (mkᴼ β g α))    ∎
        where open 𝒞.HomReasoning

  -- UC emulation
  _≤UC_ : ∀ {A B : 𝒞.Obj} {X X′ Y Y′ : ℂ.Obj}
    → ⟨ A , X ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , Y ⟩ᴼᴾ → ⟨ A , X′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , Y′ ⟩ᴼᴾ → Set (o ⊔ ℓ ⊔ cs ⊔ ℓs)
  _≤UC_ {X = X} {X′} {Y} {Y′} f g =
    ∀ {D} (a : ⟦ Y ⟧₀ ℐ.⇒ D) → Σ[ s⁺ ∈ ⟦ Y′ ⟧₀ ℐ.⇒ D ] Σ[ s⁻ ∈ ⟦ X ⟧₀ ℐ.⇒ ⟦ X′ ⟧₀ ]
      pureAtk a OAP.∘ ι f ≈ℰ' pureAtk s⁺ OAP.∘ ι g OAP.∘ pureAtk s⁻

  ------------------------------------------------------------------------
  -- The metatheorems
  ------------------------------------------------------------------------

  ≤UC-refl : ∀ {A B : 𝒞.Obj} {I J : ℂ.Obj} {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} → f ≤UC f
  ≤UC-refl {f = f} w = w , ℐ.id , ≈'-congˡ (pureAtk w) (≈'-sym (atk-idʳ (ι f)))

  -- Completeness of the dummy adversary: `_≤UC_` at the input-side mediator
  -- `u`, of which Machine.Core's `_≤'UC_` is the `u := ℐ.id` instance.
  dummy-complete : ∀ {A B : 𝒞.Obj} {I I′ J K : ℂ.Obj}
                     {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} {g : ⟨ A , I′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , K ⟩ᴼᴾ}
                 → Σ[ s ∈ ⟦ K ⟧₀ ℐ.⇒ ⟦ J ⟧₀ ] Σ[ u ∈ ⟦ I ⟧₀ ℐ.⇒ ⟦ I′ ⟧₀ ]
                     ι f ≈ℰ' (pureAtk s OAP.∘ ι g OAP.∘ pureAtk u)
                 → f ≤UC g
  dummy-complete {f = f} {g} (s , u , e) w = w ℐ.∘ s , u , (begin
      pureAtk w OAP.∘ ι f                                    ≈⟨ ≈'-congˡ (pureAtk w) e ⟩
      pureAtk w OAP.∘ pureAtk s OAP.∘ ι g OAP.∘ pureAtk u    ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟨
      (pureAtk w OAP.∘ pureAtk s) OAP.∘ ι g OAP.∘ pureAtk u  ≈⟨ ≈'-congʳ (ι g OAP.∘ pureAtk u) (pureAtk-∘ w s) ⟩
      pureAtk (w ℐ.∘ s) OAP.∘ ι g OAP.∘ pureAtk u            ∎)
    where open SetoidR (≈'-setoid _ _)

  ≤UC-trans : ∀ {A B : 𝒞.Obj} {I I′ I″ J K L : ℂ.Obj}
                {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} {g : ⟨ A , I′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , K ⟩ᴼᴾ}
                {h : ⟨ A , I″ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , L ⟩ᴼᴾ}
            → f ≤UC g → g ≤UC h → f ≤UC h
  ≤UC-trans {f = f} {g} {h} f≤g g≤h w =
    let (s₁ , u₁ , e₁) = f≤g w
        (s₂ , u₂ , e₂) = g≤h s₁
        open SetoidR (≈'-setoid _ _)
    in s₂ , (u₂ ℐ.∘ u₁) , (begin
      pureAtk w OAP.∘ ι f                                       ≈⟨ e₁ ⟩
      pureAtk s₁ OAP.∘ ι g OAP.∘ pureAtk u₁                     ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟨
      (pureAtk s₁ OAP.∘ ι g) OAP.∘ pureAtk u₁                   ≈⟨ ≈'-congʳ (pureAtk u₁) e₂ ⟩
      (pureAtk s₂ OAP.∘ ι h OAP.∘ pureAtk u₂) OAP.∘ pureAtk u₁  ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟩
      pureAtk s₂ OAP.∘ (ι h OAP.∘ pureAtk u₂) OAP.∘ pureAtk u₁  ≈⟨ ≈'-congˡ (pureAtk s₂) (≋⇒≈ℰ' OAP.assoc) ⟩
      pureAtk s₂ OAP.∘ ι h OAP.∘ pureAtk u₂ OAP.∘ pureAtk u₁    ≈⟨ ≈'-congˡ (pureAtk s₂) (≈'-congˡ (ι h) (pureAtk-∘ u₂ u₁)) ⟩
      pureAtk s₂ OAP.∘ ι h OAP.∘ pureAtk (u₂ ℐ.∘ u₁)            ∎)

  -- Universal composition: plain monotonicity of OP.∘ in both arguments (the
  -- heterogeneous grades make h ≤UC k well-typed across the middle interface).
  UC-compose : ∀ {A B C : 𝒞.Obj} {I I′ J K L M : ℂ.Obj}
                 {f : ⟨ A , I ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , J ⟩ᴼᴾ} {g : ⟨ A , I′ ⟩ᴼᴾ ⇒ᴼᴾ ⟨ B , K ⟩ᴼᴾ}
                 {h : ⟨ B , J ⟩ᴼᴾ ⇒ᴼᴾ ⟨ C , L ⟩ᴼᴾ} {k : ⟨ B , K ⟩ᴼᴾ ⇒ᴼᴾ ⟨ C , M ⟩ᴼᴾ}
             → f ≤UC g → h ≤UC k → h OP.∘ f ≤UC k OP.∘ g
  UC-compose {f = f} {g} {h} {k} f≤g h≤k w =
    let (s , u , e₂) = h≤k w
        (s′ , u′ , e₁) = f≤g u
        (s″ , eT) = pureAtk-transport k s′
        open SetoidR (≈'-setoid _ _)
    in (s ℐ.∘ s″) , u′ , (begin
      pureAtk w OAP.∘ ι (h OP.∘ f)
        ≈⟨ ≈'-congˡ (pureAtk w) (≋⇒≈ℰ' (ι-hom {f = f} {g = h})) ⟩
      pureAtk w OAP.∘ ι h OAP.∘ ι f                                      ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟨
      (pureAtk w OAP.∘ ι h) OAP.∘ ι f                                    ≈⟨ ≈'-congʳ (ι f) e₂ ⟩
      (pureAtk s OAP.∘ ι k OAP.∘ pureAtk u) OAP.∘ ι f                    ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟩
      pureAtk s OAP.∘ (ι k OAP.∘ pureAtk u) OAP.∘ ι f                    ≈⟨ ≈'-congˡ (pureAtk s) (≋⇒≈ℰ' OAP.assoc) ⟩
      pureAtk s OAP.∘ ι k OAP.∘ pureAtk u OAP.∘ ι f                      ≈⟨ ≈'-congˡ (pureAtk s) (≈'-congˡ (ι k) e₁) ⟩
      pureAtk s OAP.∘ ι k OAP.∘ pureAtk s′ OAP.∘ ι g OAP.∘ pureAtk u′    ≈⟨ ≈'-congˡ (pureAtk s) (≋⇒≈ℰ' OAP.assoc) ⟨
      pureAtk s OAP.∘ (ι k OAP.∘ pureAtk s′) OAP.∘ ι g OAP.∘ pureAtk u′
        ≈⟨ ≈'-congˡ (pureAtk s) (≈'-congʳ (ι g OAP.∘ pureAtk u′) eT) ⟩
      pureAtk s OAP.∘ (pureAtk s″ OAP.∘ ι k) OAP.∘ ι g OAP.∘ pureAtk u′  ≈⟨ ≈'-congˡ (pureAtk s) (≋⇒≈ℰ' OAP.assoc) ⟩
      pureAtk s OAP.∘ pureAtk s″ OAP.∘ ι k OAP.∘ ι g OAP.∘ pureAtk u′    ≈⟨ ≋⇒≈ℰ' OAP.assoc ⟨
      (pureAtk s OAP.∘ pureAtk s″) OAP.∘ ι k OAP.∘ ι g OAP.∘ pureAtk u′
        ≈⟨ ≈'-congʳ (ι k OAP.∘ ι g OAP.∘ pureAtk u′) (pureAtk-∘ s s″) ⟩
      pureAtk (s ℐ.∘ s″) OAP.∘ ι k OAP.∘ ι g OAP.∘ pureAtk u′            ≈⟨ ≈'-congˡ (pureAtk (s ℐ.∘ s″)) (≋⇒≈ℰ' OAP.assoc) ⟨
      pureAtk (s ℐ.∘ s″) OAP.∘ (ι k OAP.∘ ι g) OAP.∘ pureAtk u′
        ≈⟨ ≈'-congˡ (pureAtk (s ℐ.∘ s″)) (≈'-congʳ (pureAtk u′) (≋⇒≈ℰ' (OAP.Equiv.sym (ι-hom {f = g} {g = k})))) ⟩
      pureAtk (s ℐ.∘ s″) OAP.∘ ι (k OP.∘ g) OAP.∘ pureAtk u′             ∎)
