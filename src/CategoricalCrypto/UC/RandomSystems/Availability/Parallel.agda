{-# OPTIONS --safe --without-K --guardedness #-}

open import Categories.Category.Monoidal.Bundle
open import Categories.Category.Monoidal.Construction.Quotient
import Categories.Morphism.Reasoning as MR
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Function.Bundles

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Seal.Monoidal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.RandomSystems.Availability
open import CategoricalCrypto.UC.RandomSystems.Availability.Composition using (cap-compose)
open import CategoricalCrypto.UC.RandomSystems.Availability.Symmetric
open import CategoricalCrypto.UC.RandomSystems.Quantitative
open import CategoricalCrypto.UC.RandomSystems.Seal

import CategoricalCrypto.UC.Model.Setup as PM
import CategoricalCrypto.UC.Quantitative.Availability.Standard as Standard
import CategoricalCrypto.UC.RandomSystems.Setup as RS

module CategoricalCrypto.UC.RandomSystems.Availability.Parallel where

module Standardᴿ = Standard.Standard ℚ-ordered RS.𝔾ᴿ symmetricᴿ Qᴿ
module QParallelᴿ = Standardᴿ.Laws

private
  module G = MonoidalCategory 𝔾ᵒ
  module W = Standard.Structural ℚ-ordered 𝔾ᵒ symmetricᵒ
  variable
    A B C D X Y P R : G.Obj
    εf εu εfs εfa εus εua : ℚ

parallel : (A G.⇒ PM.T₀ X B) → (C G.⇒ PM.T₀ P D)
         → (A G.⊗₀ C) G.⇒ PM.T₀ (X G.⊗₀ P) (B G.⊗₀ D)
parallel = QParallelᴿ.pair

available-within-parallel : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                            {c : P G.⇒ G.unit} {d : R G.⇒ G.unit}
                            {f : A G.⇒ PM.T₀ X B} {g : A G.⇒ PM.T₀ Y B}
                            {u : C G.⇒ PM.T₀ P D} {v : C G.⇒ PM.T₀ R D}
                          → AvailableWithin εf a b f g → AvailableWithin εu c d u v
                          → AvailableWithin (εf ℚ.+ εu) (cap-compose a c) (cap-compose b d)
                              (parallel f u) (parallel g v)
available-within-parallel {a = a} {b} {c} {d} {f} {g} {u} {v} hf hu =
  Equivalence.to (Availability⇔AvailableWithin
    {a = cap-compose a c} {b = cap-compose b d} {f = parallel f u} {g = parallel g v})
    (QParallelᴿ.availability-parallel {f = f} {g = g} {u = u} {v = v}
      (Equivalence.from (Availability⇔AvailableWithin {f = f} {g = g}) hf)
      (Equivalence.from (Availability⇔AvailableWithin {f = u} {g = v}) hu))

securely-constructs-parallel : {a : X G.⇒ G.unit} {b : Y G.⇒ G.unit}
                               {c : P G.⇒ G.unit} {d : R G.⇒ G.unit}
                               {f : A G.⇒ PM.T₀ X B} {g : A G.⇒ PM.T₀ Y B}
                               {u : C G.⇒ PM.T₀ P D} {v : C G.⇒ PM.T₀ R D}
                             → SecurelyConstructs εfs εfa a b f g → SecurelyConstructs εus εua c d u v
                             → SecurelyConstructs (εfs ℚ.+ εus) (εfa ℚ.+ εua)
                                 (cap-compose a c) (cap-compose b d) (parallel f u) (parallel g v)
securely-constructs-parallel {a = a} {b} {c} {d} {f} {g} {u} {v} hf hu =
  Equivalence.to (SecureAvailable⇔SecurelyConstructs
    {a = cap-compose a c} {b = cap-compose b d} {f = parallel f u} {g = parallel g v})
    (QParallelᴿ.secure-parallel {f = f} {g = g} {u = u} {v = v}
      (Equivalence.from (SecureAvailable⇔SecurelyConstructs {f = f} {g = g}) hf)
      (Equivalence.from (SecureAvailable⇔SecurelyConstructs {f = u} {g = v}) hu))

no-adversary-parallel : (a : X G.⇒ G.unit) (c : P G.⇒ G.unit)
                        (f : A G.⇒ PM.T₀ X B) (u : C G.⇒ PM.T₀ P D)
                      → no-adversary (cap-compose a c) (parallel f u)
                        G.≈ (no-adversary a f G.⊗₁ no-adversary c u)
no-adversary-parallel a c f u = let open G; open G.HomReasoning; open MR G.U in begin
  unitorˡ.from ∘ (PM.sub (cap-compose a c) ∘ (W.middle4 ∘ (f ⊗₁ u)))
    ≈⟨ refl⟩∘⟨ ((Equiv.trans (⊗.F-resp-≈ (Equiv.refl , Equiv.sym identityˡ)) ⊗.homomorphism) ⟩∘⟨refl) ⟩
  unitorˡ.from ∘ ((PM.sub unitorˡ.from ∘ PM.sub (a ⊗₁ c)) ∘ (W.middle4 ∘ (f ⊗₁ u)))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  unitorˡ.from ∘ (PM.sub unitorˡ.from ∘ (PM.sub (a ⊗₁ c) ∘ (W.middle4 ∘ (f ⊗₁ u))))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc) ⟩
  unitorˡ.from ∘ (PM.sub unitorˡ.from ∘ ((PM.sub (a ⊗₁ c) ∘ W.middle4) ∘ (f ⊗₁ u)))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (W.middle4-sub a c ⟩∘⟨refl)) ⟩
  unitorˡ.from ∘ (PM.sub unitorˡ.from ∘ ((W.middle4 ∘ (PM.sub a ⊗₁ PM.sub c)) ∘ (f ⊗₁ u)))
    ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc) ⟩
  unitorˡ.from ∘ (PM.sub unitorˡ.from ∘ (W.middle4 ∘ ((PM.sub a ⊗₁ PM.sub c) ∘ (f ⊗₁ u))))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  unitorˡ.from ∘ ((PM.sub unitorˡ.from ∘ W.middle4) ∘ ((PM.sub a ⊗₁ PM.sub c) ∘ (f ⊗₁ u)))
    ≈⟨ sym-assoc ⟩
  (unitorˡ.from ∘ (PM.sub unitorˡ.from ∘ W.middle4)) ∘ ((PM.sub a ⊗₁ PM.sub c) ∘ (f ⊗₁ u))
    ≈⟨ W.unit-middle4 ⟩∘⟨ Equiv.sym ⊗.homomorphism ⟩
  (unitorˡ.from ⊗₁ unitorˡ.from) ∘ ((PM.sub a ∘ f) ⊗₁ (PM.sub c ∘ u))
    ≈⟨ Equiv.sym ⊗.homomorphism ⟩
  (unitorˡ.from ∘ (PM.sub a ∘ f)) ⊗₁ (unitorˡ.from ∘ (PM.sub c ∘ u)) ∎

opaque
  unfolding 𝔾ᵒ ifaceᵒ untensorᵒ congᴿ

  ∼ᴿ⇒≈ᴿ-tensor : {A B C D : Iface}
    {f g : (ifaceᵒ A G.⊗₀ ifaceᵒ C) G.⇒ (ifaceᵒ B G.⊗₀ ifaceᵒ D)}
    → MonoidalCongruence._∼_ congᴿ f g → untensorᵒ f ≈ᴿ untensorᵒ g
  ∼ᴿ⇒≈ᴿ-tensor e = e
