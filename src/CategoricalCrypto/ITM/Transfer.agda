{-# OPTIONS --safe --without-K --guardedness #-}

-- Perfect pulled-back PM tests. Only duals of image domains are needed;
-- no GradeStable or unrestricted simulator backtranslation is assumed.
module CategoricalCrypto.ITM.Transfer where

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Construction.Quotient
open import Categories.Functor.Monoidal
import Categories.Morphism as Mor

open import Relation.Binary.PropositionalEquality as Eq

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Iface
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Functor
import CategoricalCrypto.Standard2.Coverage as Coverage
open import CategoricalCrypto.UC.Machine.Cup using (dualᴵ)
open import CategoricalCrypto.UC.Model.Coverage
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction using (dualᵒ)
open import CategoricalCrypto.UC.RandomSystems.Morphism using (≈ᴿ⇒≈ᵁ)
open import CategoricalCrypto.UC.RandomSystems.Seal
open import CategoricalCrypto.UCSetup.Coverage

import CategoricalCrypto.ITM.Setup as S
import CategoricalCrypto.UC.Model.Setup as P

private
  module F = StrongMonoidalFunctor Fᴾ
  module Q = MonoidalCongruence congᴿ
  module C = Coverage.Coverage 𝕋ᴹ 𝔾ᵒ S.ℰᵀ P.ℰᵒ Fᴾ S.νᵀ
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

test-coverage : TestCoverage S.itm⇒prot
test-coverage = epi⇒TestCoverage S.itm⇒prot S.νᵀ-epi

dual-context : (A : Ports) → C.ContextRepresentation (dualᵒ (F.₀ A))
dual-context A = record { source = dualPorts A ; iso = image-dual-iso A }

preserves-≈ᵁ : Transfer.Preserves-≈ᵁ S.itm⇒prot
preserves-≈ᵁ {A = A} e = dual-prefix⇒≈ᵁ (C.covered-context test-coverage (dual-context A) e)

reflects-≈ᵁ : {f g : A S.⇒ S.T₀ X B} → G f P.≈ᵁ G g → f S.≈ᵁ g
reflects-≈ᵁ = C.reflects-≈ᵁ S.νᵀ-mono

preserves-≤UC : Transfer.Preserves-≤UC S.itm⇒prot
preserves-≤UC = Transfer.transfer⁺ S.itm⇒prot preserves-≈ᵁ

simulator-representation : (s′ : F.₀ Y P.⇒ F.₀ X) (s : Y S.⇒ X)
                         → F.₁ s Q.∼ s′ → C.SimulatorRepresentation s′ s
simulator-representation s′ s lift = record { action = λ g →
  ≈ᴿ⇒≈ᵁ (Q.∘-resp-∼ (Q.⊗-resp-∼ (Q.∼.sym lift) Q.∼.refl) Q.∼.refl) }

-- The target dummy simulator must be represented behaviourally by an
-- explicitly supplied source grade morphism; tests alone cannot supply it.
reflects-≤UC-witness : {f : A S.⇒ S.T₀ X B} {g : A S.⇒ S.T₀ Y B}
                    → (s′ : F.₀ Y P.⇒ F.₀ X) → G f P.≈ᵁ (P.sub s′ P.∘ G g)
                    → (s : Y S.⇒ X) → F.₁ s Q.∼ s′ → f S.≤UC g
reflects-≤UC-witness s′ witness s lift =
  C.reflects-≤UC-witness S.νᵀ-mono s′ witness s (simulator-representation s′ s lift)

reflects-≤UC-image-witness : {f : A S.⇒ S.T₀ X B} {g : A S.⇒ S.T₀ Y B}
                          → (s : Y S.⇒ X) → G f P.≈ᵁ G (S.sub s S.∘ g) → f S.≤UC g
reflects-≤UC-image-witness {g = g} s e = reflects-≤UC-witness (F.₁ s)
  (P.≈ᵁ-trans e (P.≈C⇒≈ᵁ (C.sub-image s g))) s Q.∼.refl
