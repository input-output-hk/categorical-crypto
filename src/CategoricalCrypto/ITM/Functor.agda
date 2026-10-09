{-# OPTIONS --safe --without-K --guardedness #-}

-- `Fᴾ : 𝕋ᴹ → 𝔾ᵒ`, the free strong monoidal functor whose leaves run their
-- tables (`ITM.Run`).  Its object map is structural over the SEALED tensor
-- and unit, so it meets `ifaceᵒ ⟦ A ⟧` only propositionally (`F₀≡`, from the
-- seal's exported `⊗ᵒ` and `unitᵒ`; nothing here unfolds the seal).  A leaf is
-- therefore a transport that never computes, and facts about leaves cross it
-- through `leafᵒ-resp` and `leafᵒ-∘`.

module CategoricalCrypto.ITM.Functor where

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor.Monoidal

open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Run
open import CategoricalCrypto.UC.Model.Seal

private
  module G = MonoidalCategory 𝔾ᵒ

  variable
    A B C : Ports
    X X′ Y Y′ Z Z′ : G.Obj

open FreeMonoidalHelper Mon Pol

⟦_⟧ᴾ : Pol → G.Obj
⟦ p ⟧ᴾ = ifaceᵒ ⟦ Var p ⟧

⟦v⟧ᴾ : ⟦ Mon ⟧ᵥ
⟦v⟧ᴾ = fromMC 𝔾ᵒ noSymmetric

open FreeObjInterp Mon Pol ⟦v⟧ᴾ ⟦_⟧ᴾ

F₀≡ : (A : Ports) → ⟦ A ⟧₀ ≡ ifaceᵒ ⟦ A ⟧
F₀≡ unit     = unitᵒ
F₀≡ (A ⊗₀ B) = trans (cong₂ G._⊗₀_ (F₀≡ A) (F₀≡ B)) (⊗ᵒ ⟦ A ⟧ ⟦ B ⟧)
F₀≡ (Var _)  = refl

leafᵒ : Gen A B → ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀
leafᵒ {A} {B} M = subst₂ G._⇒_ (sym (F₀≡ A)) (sym (F₀≡ B)) (procᵒ (runᴾ M))

private
  ≈-subst₂ : (p : X ≡ X′) (q : Y ≡ Y′) {f g : X G.⇒ Y}
           → f G.≈ g → subst₂ G._⇒_ p q f G.≈ subst₂ G._⇒_ p q g
  ≈-subst₂ refl refl e = e

  subst₂-∘ : (p : X ≡ X′) (q : Y ≡ Y′) (r : Z ≡ Z′) (g : Y G.⇒ Z) (f : X G.⇒ Y)
           → subst₂ G._⇒_ p r (g G.∘ f) ≡ subst₂ G._⇒_ q r g G.∘ subst₂ G._⇒_ p q f
  subst₂-∘ refl refl refl _ _ = refl

leafᵒ-resp : {M N : Gen A B} → procᵒ (runᴾ M) G.≈ procᵒ (runᴾ N) → leafᵒ M G.≈ leafᵒ N
leafᵒ-resp {A} {B} = ≈-subst₂ (sym (F₀≡ A)) (sym (F₀≡ B))

leafᵒ-∘ : {K : Gen A C} {M : Gen B C} {N : Gen A B}
        → procᵒ (runᴾ K) G.≈ procᵒ (runᴾ M) G.∘ procᵒ (runᴾ N) → leafᵒ K G.≈ leafᵒ M G.∘ leafᵒ N
leafᵒ-∘ {A = A} {C = C} {B = B} e =
  G.Equiv.trans (≈-subst₂ (sym (F₀≡ A)) (sym (F₀≡ C)) e)
                (G.Equiv.reflexive (subst₂-∘ (sym (F₀≡ A)) (sym (F₀≡ B)) (sym (F₀≡ C)) _ _))

Fᴾ : StrongMonoidalFunctor 𝕋ᴹ 𝔾ᵒ
Fᴾ = freeStrongMonoidal record { ⟦v⟧ = ⟦v⟧ᴾ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᴾ ; ⟦_⟧ᵖ₁ = leafᵒ }
