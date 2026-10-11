{-# OPTIONS --safe --without-K --guardedness #-}

-- Concrete request/resume pins, including unsolicited input while suspended,
-- and two-site composition/tensor instances of the sealed compilation laws.

open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Interchange.Braided as BI
import Categories.Morphism as Mor

open import Data.Bool.Base using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.PM.Choice
open import CategoricalCrypto.ND.PM.Choice.Compose
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.Model.Wire

module CategoricalCrypto.ND.PM.Choice.Pin where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module N = Grade 𝔾ˢ C

open Mor G.U

Bit : Iface
Bit = Bool ⇿ ⊥

branch : Bool → Proc⁺ [] Bit Bit
branch b = MC.mk (initˢ Bool b) λ where
  (t , inj₁ _) → returnₚ (t , inj₂ (inj₂ t))
  (_ , inj₂ (inj₁ (() , _)))
  (_ , inj₂ (inj₂ ()))

one : Proc⁺ (Bool ∷ []) Bit Bit
one = choose {Bool} {[]} {Bit} {Bit} branch

private module O = Online {Bool} {[]} {Bit} {Bit} branch

request : MC.step one (O.fresh , inj₁ false) ≡ returnₚ (O.wait (inj₁ false) , inj₂ (inj₁ (inj₁ tt)))
request = refl

resume : (b : Bool) → MC.step one (O.wait (inj₁ false) , inj₂ (inj₁ (inj₁ tt , b)))
           ≈ₚ returnₚ (O.active b b , inj₂ (inj₂ b))
resume b = >>=ₚ-identityˡ b _ ⟨≈⟩ >>=ₚ-identityˡ (b , inj₂ (inj₂ b)) _

no-early-pick : MC.step one (O.fresh , inj₂ (inj₁ (inj₁ tt , true))) ≡ botₚ
no-early-pick = refl

no-overlap : MC.step one (O.wait (inj₁ false) , inj₁ true) ≡ botₚ
no-overlap = refl

no-repeat-pick : MC.step one (O.active true true , inj₂ (inj₁ (inj₁ tt , false))) ≡ botₚ
no-repeat-pick = refl

-- A selected branch's requests at an existing site keep that site's index;
-- the new outer site occupies the first position rather than intercepting it.
private module O′ = Online {Bool} {Bool ∷ []} {Bit} {Bit} (λ _ → one)

old-request : O′.emit (inj₂ (inj₁ (inj₁ tt))) ≡ inj₂ (inj₁ (inj₂ (inj₁ tt)))
old-request = refl

two : Proc⁺ (Bool ∷ Bool ∷ []) Bit Bit
two = _∘⁺_ {Bool ∷ []} {Bit} {Bit} {Bool ∷ []} {Bit} one one

two-compiled : ⌈_⌉ {Bool ∷ Bool ∷ []} {Bit} {Bit} two
  G.≈ (N.C++.from (Bool ∷ []) (Bool ∷ []) G.⊗₁ G.id) G.∘ G.associator.to
    G.∘ (G.id G.⊗₁ ⌈_⌉ {Bool ∷ []} {Bit} {Bit} one) G.∘ ⌈_⌉ {Bool ∷ []} {Bit} {Bit} one
two-compiled = ⌈⌉-∘ {Bool ∷ []} {Bit} {Bit} {Bool ∷ []} {Bit} one one

parallel : Proc⁺ (Bool ∷ Bool ∷ []) (Bit ⊗ᴵ Bit) (Bit ⊗ᴵ Bit)
parallel = _⊗⁺_ {Bool ∷ []} {Bit} {Bit} {Bool ∷ []} {Bit} {Bit} one one

parallel-compiled : ⌈_⌉ {Bool ∷ Bool ∷ []} {Bit ⊗ᴵ Bit} {Bit ⊗ᴵ Bit} parallel
  G.≈ (G.id G.⊗₁ _≅_.from (⊗ᵒ≅ Bit Bit)) G.∘ (N.C++.from (Bool ∷ []) (Bool ∷ []) G.⊗₁ G.id)
    G.∘ BI.swapInner.from G.braided G.∘ (⌈_⌉ {Bool ∷ []} {Bit} {Bit} one G.⊗₁ ⌈_⌉ {Bool ∷ []} {Bit} {Bit} one)
    G.∘ _≅_.to (⊗ᵒ≅ Bit Bit)
parallel-compiled = ⌈⌉-⊗ {Bool ∷ []} {Bit} {Bit} {Bool ∷ []} {Bit} {Bit} one one
