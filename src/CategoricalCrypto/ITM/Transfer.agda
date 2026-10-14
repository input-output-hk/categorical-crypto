{-# OPTIONS --safe --without-K --guardedness #-}

-- Perfect pulled-back PM tests. Only duals of image domains are needed;
-- no GradeStable or unrestricted simulator backtranslation is assumed.
module CategoricalCrypto.ITM.Transfer where

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Monoidal
import Categories.Morphism as Mor

open import Data.Product.Base
open import Function.Bundles
open import Relation.Binary.PropositionalEquality as Eq

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Iface
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Functor
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Machine.Cup using (dualᴵ)
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction using (dualᵒ; T₁-≈ℰ⇒∼ᴿ)
open import CategoricalCrypto.UC.RandomSystems.Morphism using (≈ᴿ⇒≈ᵁ)
open import CategoricalCrypto.UC.RandomSystems.Seal
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.ITM.Setup as S
import CategoricalCrypto.UC.Model.Setup as P

private
  module F = StrongMonoidalFunctor Fᴾ
  module Q = MonoidalCongruence congᴿ
  module M = UCSetupMorphism S.itm⇒prot
  variable
    A B X Y : Ports

open Transfer S.itm⇒prot using (G) public

image-dual : (A : Ports) → F.₀ (dualPorts A) ≡ dualᵒ (F.₀ A)
image-dual A = Eq.trans (F₀≡ (dualPorts A))
  (Eq.trans (cong ifaceᵒ (cong₂ _⇿_ (Msg-dual ⁺ A) (Msg-dual ⁻ A)))
    (Eq.sym (cong (λ I → ifaceᵒ (dualᴵ I)) (Eq.trans (cong objᵒ (F₀≡ A)) (objᵒ-ifaceᵒ ⟦ A ⟧)))))

image-dual-iso : (A : Ports) → Mor._≅_ P.𝒞 (F.₀ (dualPorts A)) (dualᵒ (F.₀ A))
image-dual-iso A = equality-iso (image-dual A)
  where
  equality-iso : ∀ {U V} → U ≡ V → Mor._≅_ P.𝒞 U V
  equality-iso refl = record { from = P.id ; to = P.id ; iso = record { isoˡ = P.identityˡ ; isoʳ = P.identityˡ } }

private
  prefix-image : (W : Ports) (f : A S.⇒ S.T₀ X B)
               → P.prefix (F.₀ W) (G f) P.≈ F.₁ (S.prefix W f)
  prefix-image W f = let open P.𝒞 in
    at-image 𝕋ᴹ 𝔾ᵒ S.ℰᵀ P.ℰᵒ Fᴾ S.νᵀ {Y = W} f
      ○ elimˡ (identityʳ ○ P.⊗.identity) ○ identityʳ

  image-component : {f g : A S.⇒ S.T₀ X B} → f S.≈ᵁ g
                  → (W : Ports) → P.prefix (F.₀ W) (G f) P.≈ℰ P.prefix (F.₀ W) (G g)
  image-component {f = f} {g} e W = P.≈ℰ-trans (P.≈C⇒≈ℰ (prefix-image W f))
    (P.≈ℰ-trans (Equivalence.to S.≈ℰ⇔ (e W)) (P.≈ℰ-sym (P.≈C⇒≈ℰ (prefix-image W g))))

preserves-≈ᵁ : Transfer.Preserves-≈ᵁ S.itm⇒prot
preserves-≈ᵁ {A = A} {B = B} {X = X} {f = f} {g} e = ≈ᴿ⇒≈ᵁ (T₁-≈ℰ⇒∼ᴿ at-dual)
  where
  unμ : (h : F.₀ A P.⇒ P.T₀ (F.₀ X) (F.₀ B)) (W : P.Channel)
      → (P.α⇒ P.∘ P.prefix W h) P.≈ℰ P.T₁ W h
  unμ h W = P.≈C⇒≈ℰ (P.𝒞.cancelˡ P.ℐ.associator.isoʳ)

  at-image-dual : P.T₁ (F.₀ (dualPorts A)) (G f) P.≈ℰ P.T₁ (F.₀ (dualPorts A)) (G g)
  at-image-dual = P.≈ℰ-trans (P.≈ℰ-sym (unμ (G f) _))
    (P.≈ℰ-trans (P.≈ℰ-cong-post P.α⇒ (image-component e (dualPorts A))) (unμ (G g) _))

  at-dual : P.T₁ (dualᵒ (F.₀ A)) (G f) P.≈ℰ P.T₁ (dualᵒ (F.₀ A)) (G g)
  at-dual = subst (λ W → P.T₁ W (G f) P.≈ℰ P.T₁ W (G g)) (image-dual A) at-image-dual

reflects-≈ᵁ : {f g : A S.⇒ S.T₀ X B} → G f P.≈ᵁ G g → f S.≈ᵁ g
reflects-≈ᵁ {f = f} {g} e W = Equivalence.from S.≈ℰ⇔
  (P.≈ℰ-trans (P.≈ℰ-sym (P.≈C⇒≈ℰ (prefix-image W f)))
    (P.≈ℰ-trans (e (F.₀ W)) (P.≈C⇒≈ℰ (prefix-image W g))))

preserves-≤UC : Transfer.Preserves-≤UC S.itm⇒prot
preserves-≤UC = Transfer.transfer⁺ S.itm⇒prot preserves-≈ᵁ

private
  sub-image : (s : Y S.⇒ X) (g : A S.⇒ S.T₀ Y B)
            → G (S.sub s S.∘ g) P.≈ P.sub (F.₁ s) P.∘ G g
  sub-image {B = B} s g = let open P.𝒞 in
    (refl⟩∘⟨ F.homomorphism {f = g} {g = S.sub s})
      ○ sym-assoc ○ (M.κ-sub {A = B} s ⟩∘⟨refl) ○ assoc

-- The target dummy simulator must be represented behaviourally by an
-- explicitly supplied source grade morphism; tests alone cannot supply it.
reflects-≤UC-witness : {f : A S.⇒ S.T₀ X B} {g : A S.⇒ S.T₀ Y B}
                    → (s′ : F.₀ Y P.⇒ F.₀ X) → G f P.≈ᵁ (P.sub s′ P.∘ G g)
                    → (s : Y S.⇒ X) → F.₁ s Q.∼ s′ → f S.≤UC g
reflects-≤UC-witness {g = g} s′ witness s lift = S.dummy-complete (s , reflects-≈ᵁ
  (P.≈ᵁ-trans witness (P.≈ᵁ-trans
    (≈ᴿ⇒≈ᵁ (Q.∘-resp-∼ (Q.⊗-resp-∼ (Q.∼.sym lift) Q.∼.refl) Q.∼.refl))
    (P.≈ᵁ-sym (P.≈C⇒≈ᵁ (sub-image s g))))))

reflects-≤UC-image-witness : {f : A S.⇒ S.T₀ X B} {g : A S.⇒ S.T₀ Y B}
                          → (s : Y S.⇒ X) → G f P.≈ᵁ G (S.sub s S.∘ g) → f S.≤UC g
reflects-≤UC-image-witness {g = g} s e = reflects-≤UC-witness (F.₁ s)
  (P.≈ᵁ-trans e (P.≈C⇒≈ᵁ (sub-image s g))) s Q.∼.refl
