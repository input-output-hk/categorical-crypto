{-# OPTIONS --safe --without-K #-}

-- The OAP ⇄ U-kernel equivalence, on OP protocols whose input grade is the
-- Coh unit ("closed on the resource side").  ⌊_⌋ flattens such a protocol to
-- its bare graded-Kleisli morphism, ⌈_⌉ presents a bare morphism at the
-- syntactic grade Var X, and ≤UCᵇ is the bare one-sided emulation over ≈ℰ.
-- The conditional structure is the point:
--
--   oap⇒bare :               f ≤UC g (OAP)    → ⌊f⌋ ≤UCᵇ ⌊g⌋      (always)
--   ᵁ⇒bare   :               f ≤UC g (≈ᵁ)     → f ≤UCᵇ g          (always)
--   ᵁ⇒oap    :               ⌊f⌋ ≤UC ⌊g⌋ (≈ᵁ) → f ≤UC g (OAP)     (always)
--   bare⇒ᵁ   : GradeStable → f ≤UCᵇ g         → f ≤UC g (≈ᵁ)
--   bare⇒oap : GradeStable → ⌊f⌋ ≤UCᵇ ⌊g⌋     → f ≤UC g (OAP)
--
-- GradeStable — the ℳ-module property of ℰ — is what bridges bare to U-kernel
-- (sufficient, not equivalent): ≤UCᵇ records observations at the domain A, while
-- the OAP and ≈ᵁ relations compare components of the enriched image (domain
-- T₀ unit A), and lifting a bare artifact into a component is T₁-descent.
-- Hence bare⇒oap is NOT unconditional; ᵁ⇒oap is hypothesis-free because its
-- ≈ᵁ hypothesis already carries the unit-grade component that ≤UCᵇ forgets.
-- Under GradeStable all the relations coincide (oap⇔ᵁ, bare⇔⌈⌉).

open import Level

import CategoricalCrypto.Abstract as Abstract
open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.UCSetup

module CategoricalCrypto.Abstract2.Equivalence
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level}
  (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs)
  where

open import Data.Product
open import Function using (_⇔_; mk⇔)
import Relation.Binary.Reasoning.Setoid as SetoidR

open import Categories.Category.Monoidal
open import Categories.CoherenceIsos
open import Categories.Functor hiding (id)
import Categories.GradedKleisli as GK
import Categories.LocallyGraded.FreeActegory as FA
import Categories.LocallyGraded.FreeActegory.Kleisli as FAK

open AbstractUC setup

setupᴼ : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs
setupᴼ = record { 𝒞 = 𝒞 ; ℐ = ℐ ; ℳ = ℳ ; ℰ = ℰ }

module OAP = Abstract.AbstractUC setupᴼ
open OAP using (U; ι; pureAtk; ≋⇒≈ℰ'; U-∘C; U-pureAtk; pureAtk-∘;
                pureAtk-transport; atk-idʳ; ≈'-congˡ; ≈'-congʳ; ≈'-setoid;
                U-≈ℰ⇒≈ℰ'; ≈ℰ'⇒U-≈ℰ)
module OAPᶜ = OAP.OAP

open Coherence ℐ
module ℂ = MonoidalCategory Coh

private variable
  A B : 𝒞.Obj
  J K : ℂ.Obj
  X Y Z : ℐ.Obj

-- OP protocols whose input (downward) grade is the Coh unit.
Prot : 𝒞.Obj → 𝒞.Obj → ℂ.Obj → Set (o ⊔ ℓ′)
Prot A B J = OAP.⟨ A , ℂ.unit ⟩ᴼᴾ OAP.⇒ᴼᴾ OAP.⟨ B , J ⟩ᴼᴾ

-- The interface iso α : unit ⊗ β ⇒ J is absorbed into the grade by `sub`;
-- ⟦_⟧₀ is strict monoidal, so the unit-coherence cell is ℐ's λ⇐.
⌊_⌋ : Prot A B J → A 𝒞.⇒ T₀ ⟦ J ⟧₀ B
⌊ β , g , α ⌋ = sub (⟦ α ⟧₁ ℐ.∘ λ⇐) 𝒞.∘ g

⌈_⌉ : A 𝒞.⇒ T₀ X B → Prot A B (Var X)
⌈_⌉ {X = X} x = Var X , x , ℂ.unitorˡ.from

infix 4 _≤UCᵇ_

-- The bare-kernel one-sided emulation: output-side simulators only, compared
-- under ≈ℰ.
_≤UCᵇ_ : A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ Y B → Set (o ⊔ ℓ ⊔ cs ⊔ ℓs)
_≤UCᵇ_ {X = X} {Y = Y} f g =
  ∀ {X′} (a : X ℐ.⇒ X′) → Σ[ s ∈ Y ℐ.⇒ X′ ] (sub a 𝒞.∘ f) ≈ℰ (sub s 𝒞.∘ g)

≤UCᵇ-resp-≈ : {f f′ : A 𝒞.⇒ T₀ X B} {g g′ : A 𝒞.⇒ T₀ Y B}
            → f 𝒞.≈ f′ → g 𝒞.≈ g′ → f ≤UCᵇ g → f′ ≤UCᵇ g′
≤UCᵇ-resp-≈ ef eg f≤g a = let (s , e) = f≤g a in
  s , ≈ℰ-trans (≈C⇒≈ℰ (𝒞.∘-resp-≈ʳ (𝒞.Equiv.sym ef))) (≈ℰ-trans e (≈C⇒≈ℰ (𝒞.∘-resp-≈ʳ eg)))

------------------------------------------------------------------------
-- The key lemma: U (ι x) is the unit-grade component of ⌊ x ⌋
------------------------------------------------------------------------

Uι-decomp : (x : Prot A B J) → U (ι x) 𝒞.≈ sub λ⇒ 𝒞.∘ ext ℐ.unit ⌊ x ⌋
Uι-decomp (β , g , α) = let open 𝒞 in ⟺ (begin
    sub λ⇒ ∘ ext ℐ.unit (sub (⟦ α ⟧₁ ℐ.∘ λ⇐) ∘ g)
  ≈⟨ refl⟩∘⟨ sub-commute₂ ⟩
    sub λ⇒ ∘ (sub (ℐ.id ⊗₁ (⟦ α ⟧₁ ℐ.∘ λ⇐)) ∘ ext ℐ.unit g)
  ≈⟨ pullˡ (⟺ sub-homomorphism) ⟩
    sub (λ⇒ ℐ.∘ ℐ.id ⊗₁ (⟦ α ⟧₁ ℐ.∘ λ⇐)) ∘ ext ℐ.unit g
  ≈⟨ sub-resp-≈ λ-step ⟩∘⟨refl ⟩
    sub (⟦ α ⟧₁ ℐ.∘ ℐ.id) ∘ ext ℐ.unit g  ∎)
  where
    λ-step : λ⇒ ℐ.∘ ℐ.id ⊗₁ (⟦ α ⟧₁ ℐ.∘ λ⇐) ℐ.≈ ⟦ α ⟧₁ ℐ.∘ ℐ.id
    λ-step = let open ℐ.HomReasoning in
      ℐ.unitorˡ-commute-from ○ ℐ.assoc ○ (refl⟩∘⟨ ℐ.unitorˡ.isoˡ)

⌊⌋-return : (x : Prot A B J) → U (ι x) 𝒞.∘ return 𝒞.≈ ⌊ x ⌋
⌊⌋-return x = let open 𝒞 in (Uι-decomp x ⟩∘⟨refl) ○ assoc ○ ext-identityʳ

-- The attacked composite under U, as the unit-grade ≈ᵁ-component of the
-- attacked bare protocol.
U-atk : (x : Prot A B J) (a : ⟦ J ⟧₀ ℐ.⇒ Z)
      → U (pureAtk a OAPᶜ.∘ ι x)
        𝒞.≈ sub λ⇒ 𝒞.∘ (μ ℐ.unit Z 𝒞.∘ T₁ ℐ.unit (sub a 𝒞.∘ ⌊ x ⌋))
U-atk {Z = Z} x a = let open 𝒞 in begin
    U (pureAtk a OAPᶜ.∘ ι x)                           ≈⟨ U-∘C (pureAtk a) (ι x) ⟩
    U (pureAtk a) ∘ U (ι x)                            ≈⟨ U-pureAtk a ⟩∘⟨ Uι-decomp x ⟩
    sub a ∘ (sub λ⇒ ∘ ext ℐ.unit ⌊ x ⌋)                ≈⟨ pullˡ (⟺ sub-homomorphism) ⟩
    sub (a ℐ.∘ λ⇒) ∘ ext ℐ.unit ⌊ x ⌋                  ≈⟨ sub-resp-≈ (ℐ.Equiv.sym ℐ.unitorˡ-commute-from) ⟩∘⟨refl ⟩
    sub (λ⇒ ℐ.∘ ℐ.id ⊗₁ a) ∘ ext ℐ.unit ⌊ x ⌋          ≈⟨ pushˡ sub-homomorphism ⟩
    sub λ⇒ ∘ (sub (ℐ.id ⊗₁ a) ∘ ext ℐ.unit ⌊ x ⌋)      ≈⟨ refl⟩∘⟨ ⟺ sub-commute₂ ⟩
    sub λ⇒ ∘ ext ℐ.unit (sub a ∘ ⌊ x ⌋)                ≈⟨ refl⟩∘⟨ ⟺ (μT (sub a ∘ ⌊ x ⌋)) ⟩
    sub λ⇒ ∘ (μ ℐ.unit Z ∘ T₁ ℐ.unit (sub a ∘ ⌊ x ⌋))  ∎

atk-return : (x : Prot A B J) (a : ⟦ J ⟧₀ ℐ.⇒ Z)
           → U (pureAtk a OAPᶜ.∘ ι x) 𝒞.∘ return 𝒞.≈ sub a 𝒞.∘ ⌊ x ⌋
atk-return x a = let open 𝒞 in
  ((U-∘C (pureAtk a) (ι x) ○ (U-pureAtk a ⟩∘⟨refl)) ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ ⌊⌋-return x)

------------------------------------------------------------------------
-- The theorems
------------------------------------------------------------------------

-- OAP emulation flattens to bare emulation, unconditionally: the input
-- simulator s⁻ (a grade-endo of the unit) slides across ι g by
-- pureAtk-transport and folds into the output simulator.
oap⇒bare : {f : Prot A B J} {g : Prot A B K} → f OAP.≤UC g → ⌊ f ⌋ ≤UCᵇ ⌊ g ⌋
oap⇒bare {f = f} {g = g} f≤g a =
  let (s⁺ , s⁻ , E) = f≤g a
      (s″ , E″)     = pureAtk-transport g s⁻
      E′ : (pureAtk a OAPᶜ.∘ ι f) OAP.≈ℰ' (pureAtk (s⁺ ℐ.∘ s″) OAPᶜ.∘ ι g)
      E′ = let open SetoidR (≈'-setoid _ _) in begin
        pureAtk a OAPᶜ.∘ ι f                       ≈⟨ E ⟩
        pureAtk s⁺ OAPᶜ.∘ ι g OAPᶜ.∘ pureAtk s⁻    ≈⟨ ≈'-congˡ (pureAtk s⁺) E″ ⟩
        pureAtk s⁺ OAPᶜ.∘ pureAtk s″ OAPᶜ.∘ ι g    ≈⟨ ≋⇒≈ℰ' OAPᶜ.assoc ⟨
        (pureAtk s⁺ OAPᶜ.∘ pureAtk s″) OAPᶜ.∘ ι g  ≈⟨ ≈'-congʳ (ι g) (pureAtk-∘ s⁺ s″) ⟩
        pureAtk (s⁺ ℐ.∘ s″) OAPᶜ.∘ ι g             ∎
  in s⁺ ℐ.∘ s″ ,
     ≈ℰ-trans (≈ℰ-sym (≈C⇒≈ℰ (atk-return f a)))
       (≈ℰ-trans (≈ℰ-cong-pre return (≈ℰ'⇒U-≈ℰ E′)) (≈C⇒≈ℰ (atk-return g (s⁺ ℐ.∘ s″))))

ᵁ⇒bare : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → f ≤UC g → f ≤UCᵇ g
ᵁ⇒bare f≤g a = let (s , e) = f≤g a in s , ≈ᵁ⇒≈ℰ e

bare⇒ᵁ : GradeStable → {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → f ≤UCᵇ g → f ≤UC g
bare⇒ᵁ gs f≤g a = let (s , e) = f≤g a in s , bridge gs e

-- U-kernel emulation of the flattenings gives OAP emulation with NO
-- hypothesis: the ≈ᵁ witness instantiated at grade unit IS the OAP
-- comparison, up to the λ unit coherence (s⁻ = ℐ.id, absorbed by atk-idʳ).
ᵁ⇒oap : {f : Prot A B J} {g : Prot A B K} → ⌊ f ⌋ ≤UC ⌊ g ⌋ → f OAP.≤UC g
ᵁ⇒oap {f = f} {g = g} f≤g a =
  let (s , e) = f≤g a
  in s , ℐ.id , U-≈ℰ⇒≈ℰ' (let open SetoidR (≈ℰ-setoid _ _) in begin
    U (pureAtk a OAPᶜ.∘ ι f)
      ≈⟨ ≈C⇒≈ℰ (U-atk f a) ⟩
    sub λ⇒ 𝒞.∘ (μ ℐ.unit _ 𝒞.∘ T₁ ℐ.unit (sub a 𝒞.∘ ⌊ f ⌋))
      ≈⟨ ≈ℰ-cong-post (sub λ⇒) (e ℐ.unit) ⟩
    sub λ⇒ 𝒞.∘ (μ ℐ.unit _ 𝒞.∘ T₁ ℐ.unit (sub s 𝒞.∘ ⌊ g ⌋))
      ≈⟨ ≈C⇒≈ℰ (U-atk g s) ⟨
    U (pureAtk s OAPᶜ.∘ ι g)
      ≈⟨ ≈ℰ'⇒U-≈ℰ (≈'-congˡ (pureAtk s) (atk-idʳ (ι g))) ⟨
    U (pureAtk s OAPᶜ.∘ ι g OAPᶜ.∘ pureAtk ℐ.id)  ∎)

bare⇒oap : GradeStable → {f : Prot A B J} {g : Prot A B K}
         → ⌊ f ⌋ ≤UCᵇ ⌊ g ⌋ → f OAP.≤UC g
bare⇒oap gs {f = f} {g = g} f≤g = ᵁ⇒oap {f = f} {g = g} (bare⇒ᵁ gs f≤g)

-- Under GradeStable the OAP and U-kernel relations coincide on
-- unit-input protocols; without it, ᵁ⇒oap is the one-way ingestion.
oap⇔ᵁ : GradeStable → {f : Prot A B J} {g : Prot A B K}
      → (f OAP.≤UC g) ⇔ (⌊ f ⌋ ≤UC ⌊ g ⌋)
oap⇔ᵁ gs {f = f} {g = g} = mk⇔ fwd (ᵁ⇒oap {f = f} {g = g})
  where fwd : f OAP.≤UC g → ⌊ f ⌋ ≤UC ⌊ g ⌋
        fwd f≤g = bare⇒ᵁ gs (oap⇒bare {f = f} {g = g} f≤g)

------------------------------------------------------------------------
-- The ⌈_⌉ counterparts: ⌊_⌋ and ⌈_⌉ are mutually inverse
------------------------------------------------------------------------

⌊⌈⌉⌋-id : (x : A 𝒞.⇒ T₀ X B) → ⌊ ⌈ x ⌉ ⌋ 𝒞.≈ x
⌊⌈⌉⌋-id = FA.flatten-unflatten naiveKleisli

ι⌈⌊⌋⌉-id : (x : Prot A B J) → ι ⌈ ⌊ x ⌋ ⌉ OAPᶜ.≈ ι x
ι⌈⌊⌋⌉-id x = OAPᶜ.Equiv.trans
  (GK.≈-components 𝒞 ℐ triple
    (𝒞.∘-resp-≈ˡ (sub-resp-≈ (ℐ.∘-resp-≈ˡ (ℐ.Equiv.sym ℐ.identityʳ)))) ℐ.identityʳ)
  (Functor.F-resp-≈ (FAK.fromFreeActegory 𝒞 ℐ triple)
    (FA.unflatten-flatten naiveKleisli (ι x)))

oap⇒bare-⌈⌉ : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → ⌈ f ⌉ OAP.≤UC ⌈ g ⌉ → f ≤UCᵇ g
oap⇒bare-⌈⌉ {f = f} {g = g} f≤g =
  ≤UCᵇ-resp-≈ (⌊⌈⌉⌋-id f) (⌊⌈⌉⌋-id g) (oap⇒bare {f = ⌈ f ⌉} {g = ⌈ g ⌉} f≤g)

bare⇒oap-⌈⌉ : GradeStable → {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
            → f ≤UCᵇ g → ⌈ f ⌉ OAP.≤UC ⌈ g ⌉
bare⇒oap-⌈⌉ gs {f = f} {g = g} f≤g = ᵁ⇒oap {f = ⌈ f ⌉} {g = ⌈ g ⌉} (bare⇒ᵁ gs
  (≤UCᵇ-resp-≈ (𝒞.Equiv.sym (⌊⌈⌉⌋-id f)) (𝒞.Equiv.sym (⌊⌈⌉⌋-id g)) f≤g))

bare⇔⌈⌉ : GradeStable → {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B}
        → (f ≤UCᵇ g) ⇔ (⌈ f ⌉ OAP.≤UC ⌈ g ⌉)
bare⇔⌈⌉ gs = mk⇔ (bare⇒oap-⌈⌉ gs) oap⇒bare-⌈⌉
