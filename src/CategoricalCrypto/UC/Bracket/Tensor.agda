{-# OPTIONS --safe --without-K --guardedness #-}

-- The tensor of well-bracketed machines (`docs/uc-setup-ssp.md` §4.2).  The
-- flattening of a tensor is not `𝒢ₚ`'s tensor of the flattenings but a
-- relabelling of it (`φʷ`), so the tensor `𝒲` inherits is `𝒢ₚ`'s conjugated
-- by `φʷ`.  `_⊗ʷ_` is that conjugate as one machine (`conj≈⊗ʷ`): its step hands
-- a message to the factor owning the channel, and it is well-bracketed because
-- a legal environment has one open query at a time (`⊗ʷ-W`).
--
-- Interfaces are passed explicitly at use sites: `flat` forgets `Ch-dec`.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
import Categories.GConstructionMonoidal as GM

open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Wire

import CategoricalCrypto.Iface as Flat

module CategoricalCrypto.UC.Bracket.Tensor where

private
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

private variable
  A B C D : Iface
  X X′ Y Y′ : Set
  F F′ G G′ : X → Set

------------------------------------------------------------------------
-- The relabelling

-- A `Σ` over a sum of channel sets is the sum of the `Σ`s.
joinΣ : {F : X → Set} {G : Y → Set} → Σ X F ⊎ Σ Y G → Σ (X ⊎ Y) [ F , G ]′
joinΣ (inj₁ (x , u)) = inj₁ x , u
joinΣ (inj₂ (y , v)) = inj₂ y , v

splitΣ : {F : X → Set} {G : Y → Set} → Σ (X ⊎ Y) [ F , G ]′ → Σ X F ⊎ Σ Y G
splitΣ (inj₁ x , u) = inj₁ (x , u)
splitΣ (inj₂ y , v) = inj₂ (y , v)

φʷ : Proc (flat A Flat.⊗ᴵ flat C) (flat (A ⊗ᴵ C))
φʷ = wireᴹ joinΣ splitΣ

φʷ⁻¹ : Proc (flat (A ⊗ᴵ C)) (flat A Flat.⊗ᴵ flat C)
φʷ⁻¹ = wireᴹ splitΣ joinΣ

------------------------------------------------------------------------
-- The direct tensor

-- A factor's emission, onto its own side of both tensors, with the other
-- factor's state beside its own.
retagˡ : {F : X → Set} {F′ : X′ → Set} {G : Y → Set} {G′ : Y′ → Set}
       → Σ X F ⊎ Σ Y G → Σ (X ⊎ X′) [ F , F′ ]′ ⊎ Σ (Y ⊎ Y′) [ G , G′ ]′
retagˡ = Sum.map (λ u → joinΣ (inj₁ u)) (λ v → joinΣ (inj₁ v))

retagʳ : {F : X → Set} {F′ : X′ → Set} {G : Y → Set} {G′ : Y′ → Set}
       → Σ X′ F′ ⊎ Σ Y′ G′ → Σ (X ⊎ X′) [ F , F′ ]′ ⊎ Σ (Y ⊎ Y′) [ G , G′ ]′
retagʳ = Sum.map (λ u → joinΣ (inj₂ u)) (λ v → joinΣ (inj₂ v))

pairˡ : {S T : Set} {F : X → Set} {F′ : X′ → Set} {G : Y → Set} {G′ : Y′ → Set}
      → T → S × (Σ X F ⊎ Σ Y G) → (S × T) × (Σ (X ⊎ X′) [ F , F′ ]′ ⊎ Σ (Y ⊎ Y′) [ G , G′ ]′)
pairˡ t (s′ , y) = (s′ , t) , retagˡ y

pairʳ : {S T : Set} {F : X → Set} {F′ : X′ → Set} {G : Y → Set} {G′ : Y′ → Set}
      → S → T × (Σ X′ F′ ⊎ Σ Y′ G′) → (S × T) × (Σ (X ⊎ X′) [ F , F′ ]′ ⊎ Σ (Y ⊎ Y′) [ G , G′ ]′)
pairʳ s (t′ , y) = (s , t′) , retagʳ y

module _ (f : Proc (flat A) (flat B)) (g : Proc (flat C) (flat D)) where

  stepʷ : (MC.St f × MC.St g) × (Flat.Pos (flat (A ⊗ᴵ C)) ⊎ Flat.Neg (flat (B ⊗ᴵ D)))
        → Dₚ ((MC.St f × MC.St g) × (Flat.Neg (flat (A ⊗ᴵ C)) ⊎ Flat.Pos (flat (B ⊗ᴵ D))))
  stepʷ ((s , t) , inj₁ (inj₁ a , r)) = mapₚ (pairˡ t) (MC.step f (s , inj₁ (a , r)))
  stepʷ ((s , t) , inj₁ (inj₂ c , r)) = mapₚ (pairʳ s) (MC.step g (t , inj₁ (c , r)))
  stepʷ ((s , t) , inj₂ (inj₁ b , q)) = mapₚ (pairˡ t) (MC.step f (s , inj₂ (b , q)))
  stepʷ ((s , t) , inj₂ (inj₂ d , q)) = mapₚ (pairʳ s) (MC.step g (t , inj₂ (d , q)))

infixr 10 _⊗ʷ_

_⊗ʷ_ : Proc (flat A) (flat B) → Proc (flat C) (flat D) → Proc (flat (A ⊗ᴵ C)) (flat (B ⊗ᴵ D))
_⊗ʷ_ {A} {B} {C} {D} f g = MC.mk (MC.state f MC.⊛ MC.state g) (stepʷ {A = A} {B = B} {C = C} {D = D} f g)

------------------------------------------------------------------------
-- Well-bracketed

module _ {f : Proc (flat A) (flat B)} {g : Proc (flat C) (flat D)} (wf : W {A} {B} f) (wg : W {C} {D} g) where

  private
    module F = W wf
    module G = W wg

    I : MC.St f × MC.St g → Phase (A ⊗ᴵ C) (B ⊗ᴵ D) → Set
    I (s , t) idle                        = F.I s idle × G.I t idle
    I (s , t) (calling (inj₁ b) (inj₁ a)) = F.I s (calling b a) × G.I t idle
    I (s , t) (calling (inj₂ d) (inj₂ c)) = F.I s idle × G.I t (calling d c)
    I _       _                           = ⊥

    I-init : ∀ n → Supp n (MC.point (MC.state f MC.⊛ MC.state g) tt) λ s → I s idle
    I-init n = Supp-bind _ n _ _ (Supp-return _ _ (λ i →
      Supp-bind _ i _ _ (Supp-map _ _ (λ _ if j →
        Supp-bind _ j _ _ (Supp-map _ _ (λ _ ig → Supp-return _ _ (if , ig)) j _ (G.I-init j)))
        i _ (F.I-init i))) n)

    legalˡ : ∀ {b t} → G.I t idle → ∀ r → Legal F.I (serving b) r
           → ∀ j → Supp j (returnₚ (pairˡ t r)) (Legal I (serving (inj₁ b)))
    legalˡ ig (_ , inj₁ _) (_ , call , if)   = Supp-return _ _ (calling _ _ , call , if , ig)
    legalˡ ig (_ , inj₂ _) (_ , answer , if) = Supp-return _ _ (idle , answer , if , ig)

    legalʳ : ∀ {d s} → F.I s idle → ∀ r → Legal G.I (serving d) r
           → ∀ j → Supp j (returnₚ (pairʳ s r)) (Legal I (serving (inj₂ d)))
    legalʳ if (_ , inj₁ _) (_ , call , ig)   = Supp-return _ _ (calling _ _ , call , if , ig)
    legalʳ if (_ , inj₂ _) (_ , answer , ig) = Supp-return _ _ (idle , answer , if , ig)

    I-step : ∀ {s φ x φ′} → I s φ → Opp φ x φ′ → ∀ n
           → Supp n (MC.step (_⊗ʷ_ {A} {B} {C} {D} f g) (s , x)) (Legal I φ′)
    I-step {_ , _} {x = inj₂ (inj₁ _ , _)} (if , ig) query n =
      Supp-bind _ n _ _ (Supp-map _ _ (legalˡ ig) n _ (F.I-step if query n))
    I-step {_ , _} {x = inj₂ (inj₂ _ , _)} (if , ig) query n =
      Supp-bind _ n _ _ (Supp-map _ _ (legalʳ if) n _ (G.I-step ig query n))
    I-step {_ , _} {calling (inj₁ _) (inj₁ _)} (if , ig) return n =
      Supp-bind _ n _ _ (Supp-map _ _ (legalˡ ig) n _ (F.I-step if return n))
    I-step {_ , _} {calling (inj₂ _) (inj₂ _)} (if , ig) return n =
      Supp-bind _ n _ _ (Supp-map _ _ (legalʳ if) n _ (G.I-step ig return n))
    I-step {_ , _} {calling (inj₁ _) (inj₂ _)} () return
    I-step {_ , _} {calling (inj₂ _) (inj₁ _)} () return

  ⊗ʷ-W : W {A ⊗ᴵ C} {B ⊗ᴵ D} (_⊗ʷ_ {A} {B} {C} {D} f g)
  ⊗ʷ-W = record { I = I ; I-init = I-init ; I-step = I-step }

------------------------------------------------------------------------
-- The direct tensor is the conjugated `𝒢ₚ` tensor

module _ (f : Proc (flat A) (flat B)) (g : Proc (flat C) (flat D)) where

  private
    -- `𝒢ₚ`'s tensor with both interchanges absorbed into the step.
    ⊗ᴳ-flat : Proc (flat A Flat.⊗ᴵ flat C) (flat B Flat.⊗ᴵ flat D)
    ⊗ᴳ-flat = MC.mk (MC.state (f T.⊗ᵉ g))
      (V._∘_ (V._⊗₁_ V.id (K.pureᵏ midfn)) (V._∘_ (MC.step (f T.⊗ᵉ g)) (V._⊗₁_ V.id (K.pureᵏ midfn))))

    opaque
      unfolding midᴹ GM._⊗₁ᴳ_

      collapse-⊗ : 𝒫._≈_ {flat A Flat.⊗ᴵ flat C} {flat B Flat.⊗ᴵ flat D}
                     (𝔾._⊗₁_ {⟦ flat A ⟧ᴵ} {⟦ flat B ⟧ᴵ} {⟦ flat C ⟧ᴵ} {⟦ flat D ⟧ᴵ} f g) ⊗ᴳ-flat
      collapse-⊗ =
           Cat.∘ᴹ-resp-≈ᴹ midᴹ-pure (Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ midᴹ-pure)
        S.○ᴹ S.≲⇒≈ᴹ (Cat.∘ᴹ-resp-≲ S.≲-refl (T.pure-∘ʳ (K.pureᵏ midfn) (f T.⊗ᵉ g)))
        S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ midfn) _)

    -- One arm of the interface tensor, read at a point: the factor's step,
    -- re-paired with the other factor's state and retagged.
    armˡ : (s : MC.St f) (t : MC.St g) (z : Flat.Pos (flat A) ⊎ Flat.Neg (flat B))
           {O : (MC.St f × MC.St g) × ((Flat.Neg (flat A) ⊎ Flat.Neg (flat C)) ⊎ (Flat.Pos (flat B) ⊎ Flat.Pos (flat D)))
              → (MC.St f × MC.St g) × (Flat.Neg (flat (A ⊗ᴵ C)) ⊎ Flat.Pos (flat (B ⊗ᴵ D)))}
         → (∀ r → O ((proj₁ r , t) , midfn (inj₁ (proj₂ r))) ≡ pairˡ t r)
         → mapₚ O (T.tstep (MC.onL (MC.step f)) (MC.onR (MC.step g)) ((s , t) , inj₁ z)
                    >>=ₚ V._⊗₁_ V.id (K.pureᵏ midfn))
           ≈ₚ mapₚ (pairˡ t) (MC.step f (s , z))
    armˡ s t z {O} eq =
         bindˣ (bindˣ (tstep-inj₁ _ _ (s , t) z ⟨≈⟩ bindˣ (onL-pt (MC.step f) s t z) ⟨≈⟩ map-map d _ _)
                ⟨≈⟩ bind-map d _ _ ⟨≈⟩ bindᶠ (λ r → pureᴵ midfn _))
      ⟨≈⟩ map-fuse d _ O (pairˡ t) eq
      where d = MC.step f (s , z)

    armʳ : (s : MC.St f) (t : MC.St g) (z : Flat.Pos (flat C) ⊎ Flat.Neg (flat D))
           {O : (MC.St f × MC.St g) × ((Flat.Neg (flat A) ⊎ Flat.Neg (flat C)) ⊎ (Flat.Pos (flat B) ⊎ Flat.Pos (flat D)))
              → (MC.St f × MC.St g) × (Flat.Neg (flat (A ⊗ᴵ C)) ⊎ Flat.Pos (flat (B ⊗ᴵ D)))}
         → (∀ r → O ((s , proj₁ r) , midfn (inj₂ (proj₂ r))) ≡ pairʳ s r)
         → mapₚ O (T.tstep (MC.onL (MC.step f)) (MC.onR (MC.step g)) ((s , t) , inj₂ z)
                    >>=ₚ V._⊗₁_ V.id (K.pureᵏ midfn))
           ≈ₚ mapₚ (pairʳ s) (MC.step g (t , z))
    armʳ s t z {O} eq =
         bindˣ (bindˣ (tstep-inj₂ _ _ (s , t) z ⟨≈⟩ bindˣ (onR-pt (MC.step g) s t z) ⟨≈⟩ map-map d _ _)
                ⟨≈⟩ bind-map d _ _ ⟨≈⟩ bindᶠ (λ r → pureᴵ midfn _))
      ⟨≈⟩ map-fuse d _ O (pairʳ s) eq
      where d = MC.step g (t , z)

  conj≈⊗ʷ : 𝒫._≈_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)}
              (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat B Flat.⊗ᴵ flat D} {flat (B ⊗ᴵ D)} (φʷ {B} {D})
                (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat A Flat.⊗ᴵ flat C} {flat B Flat.⊗ᴵ flat D}
                  (𝔾._⊗₁_ {⟦ flat A ⟧ᴵ} {⟦ flat B ⟧ᴵ} {⟦ flat C ⟧ᴵ} {⟦ flat D ⟧ᴵ} f g) (φʷ⁻¹ {A} {C})))
              (_⊗ʷ_ {A} {B} {C} {D} f g)
  conj≈⊗ʷ =
         𝒫.∘-resp-≈ {flat (A ⊗ᴵ C)} {flat B Flat.⊗ᴵ flat D} {flat (B ⊗ᴵ D)} (S.reflᴹ {f = φʷ {B} {D}})
           ( 𝒫.∘-resp-≈ {flat (A ⊗ᴵ C)} {flat A Flat.⊗ᴵ flat C} {flat B Flat.⊗ᴵ flat D}
               collapse-⊗ (S.reflᴹ {f = φʷ⁻¹ {A} {C}})
           S.○ᴹ ∘-wireᴹ splitΣ joinΣ ⊗ᴳ-flat)
    S.○ᴹ wire-∘ᴹ joinΣ splitΣ (sandwichᴹ ⊗ᴳ-flat (Sum.map splitΣ (λ a → a)) (Sum.map joinΣ (λ a → a)))
    S.○ᴹ sandwich-∘ ⊗ᴳ-flat (Sum.map splitΣ (λ a → a)) (Sum.map joinΣ (λ a → a))
                            (Sum.map (λ a → a) splitΣ) (Sum.map (λ a → a) joinΣ)
    S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
           ((s , t) , inj₁ (inj₁ a , r)) →
             bindˣ (bindˣ (enter-pure midfn _ (s , t) (inj₁ (inj₁ (a , r)))))
             ⟨≈⟩ armˡ s t (inj₁ (a , r)) λ where (_ , inj₁ _) → refl ; (_ , inj₂ _) → refl
           ((s , t) , inj₁ (inj₂ c , r)) →
             bindˣ (bindˣ (enter-pure midfn _ (s , t) (inj₁ (inj₂ (c , r)))))
             ⟨≈⟩ armʳ s t (inj₁ (c , r)) λ where (_ , inj₁ _) → refl ; (_ , inj₂ _) → refl
           ((s , t) , inj₂ (inj₁ b , q)) →
             bindˣ (bindˣ (enter-pure midfn _ (s , t) (inj₂ (inj₁ (b , q)))))
             ⟨≈⟩ armˡ s t (inj₂ (b , q)) λ where (_ , inj₁ _) → refl ; (_ , inj₂ _) → refl
           ((s , t) , inj₂ (inj₂ d , q)) →
             bindˣ (bindˣ (enter-pure midfn _ (s , t) (inj₂ (inj₂ (d , q)))))
             ⟨≈⟩ armʳ s t (inj₂ (d , q)) λ where (_ , inj₁ _) → refl ; (_ , inj₂ _) → refl)
