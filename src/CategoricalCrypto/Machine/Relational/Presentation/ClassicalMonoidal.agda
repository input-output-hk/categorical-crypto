{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalMonoidal where

open import Axiom.ExcludedMiddle
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Monoidal
open import Categories.Functor.Monoidal.Properties using (∘-StrongMonoidal)
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
open import Data.Empty
import Data.Empty.Polymorphic as Empty
open import Data.Product.Base using (_,_)
open import Data.Sum.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

import CategoricalCrypto.Channel.Core as Ch
import CategoricalCrypto.Machine.Forwarder as Fwd
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
import CategoricalCrypto.Machine.Relational.Model as Native
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalFunctor as F
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalStructural as Structural
open Structural using (cross; cross-cong; cross-compose; cross-tensor; cross-id; cross-forwarder)
import CategoricalCrypto.Machine.Relational.Presentation.ClassicalTensor as Tensor
import CategoricalCrypto.Machines.Positive.Bridge as Bridge
import CategoricalCrypto.Machines.Positive.Model as Model
import CategoricalCrypto.Machines.Positive.Raw as Raw
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.UC.Machine.Dictionary as Dict
import CategoricalCrypto.UC.Model.Seal as Seal

private
  module R = Re.At 0ℓ
  module G = Raw.At 0ℓ
  module Q = MonoidalCategory Model.𝔾₊
  module N = MonoidalCategory Native.𝔾ᴿᵐ

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  module C = Classical.WithLEM lem
  module T = Tensor.WithLEM lem
  module Map = F.WithLEM lem
  open C using (compile; congruence)
  open Map using (arrow)
  open Structural.WithLEM lem using (cross-wire)
  open N.HomReasoning

  opaque
    unfolding Seal.𝔾ᵒ Seal.objᵒ Map.arrow Model.positive-congruence
              Ch._⊗₀_ Ch.destruct-⊗ Ch.construct-⊗ Ch.⊗-sym Ch.⊗-combine
              Ch.⊗-left-assoc Ch.⊗-right-assoc Ch.⊗-right-neutral
              Ch.⊗-right-intro T.tensor-proc Fwd.⊗mapᵢ Fwd.⊗mapₒ

    coherence : IsStrongMonoidalFunctor Model.𝔾₊ Native.𝔾ᴿᵐ Map.functor
    coherence = record
        { ε = record
          { from = cross ⊥-elim Empty.⊥-elim
          ; to = cross Empty.⊥-elim ⊥-elim
          ; iso = record
            { isoˡ = cross-compose _ _ _ _ ○ cross-cong (λ ()) (λ ()) ○ cross-id
            ; isoʳ = cross-compose _ _ _ _ ○ cross-cong Empty.⊥-elim Empty.⊥-elim ○ cross-id } }
        ; ⊗-homo = niHelper record
          { η = λ _ → W.id ; η⁻¹ = λ _ → W.id
          ; commute = λ (f , g) → N.identityˡ ○ ⟺ (tensor-preservation f g) ○ ⟺ N.identityʳ
          ; iso = λ _ → record { isoˡ = N.identityˡ ; isoʳ = N.identityˡ } }
        ; associativity = (refl⟩∘⟨ (N.identityˡ ○ N.⊗.identity)) ○ N.identityʳ ○ assoc-preservation
            ○ ⟺ (N.identityˡ ○ (N.⊗.identity ⟩∘⟨refl) ○ N.identityˡ)
        ; unitaryˡ = (left-preservation ⟩∘⟨ (N.identityˡ
            ○ W.⊗-cong ≈ᴿ-refl (≈ᴿ-sym cross-id) ○ cross-tensor _ _ _ _))
            ○ cross-compose _ _ _ _
            ○ cross-cong (λ { (inj₁ ()) ; (inj₂ a) → refl }) (λ _ → refl)
            ○ ⟺ (cross-forwarder Ch.⊗-left-neutral Ch.⊗-left-intro)
        ; unitaryʳ = (right-preservation ⟩∘⟨ (N.identityˡ
            ○ W.⊗-cong (≈ᴿ-sym cross-id) ≈ᴿ-refl ○ cross-tensor _ _ _ _))
            ○ cross-compose _ _ _ _
            ○ cross-cong (λ { (inj₁ a) → refl ; (inj₂ ()) }) (λ _ → refl)
            ○ ⟺ (cross-forwarder Ch.⊗-right-neutral Ch.⊗-right-intro)
        }
      where
      tensor-preservation : ∀ {A B C D : Q.Obj} (f : A Q.⇒ B) (g : C Q.⇒ D)
        → arrow (f Q.⊗₁ g) ≈ᴿ (arrow f W.⊗₁ arrow g)
      tensor-preservation f g = ≈ᴿ-trans
        (congruence (R.QS._○ᴹ_ (R.repack-resp (R.PS.⟺ᴹ (G.tensorₚ-project f g)))
          (Bridge.repack-tensor 0ℓ f g)))
        (T.tensor (R.repack f) (R.repack g))

      assoc-preservation : ∀ {A B C : Q.Obj} → arrow (Q.associator.from {A} {B} {C}) ≈ᴿ N.associator.from
      assoc-preservation = congruence (R.repack-resp (R.PS.⟺ᴹ Dict.a⇒-α⇒))
        ○ cross-wire assocʳ assocˡ
        ○ cross-cong (λ { (inj₁ (inj₁ _)) → refl ; (inj₁ (inj₂ _)) → refl ; (inj₂ _) → refl })
            (λ { (inj₁ _) → refl ; (inj₂ (inj₁ _)) → refl ; (inj₂ (inj₂ _)) → refl })
        ○ ⟺ (cross-forwarder M.⊗-assocᵢ M.⊗-assocₒ)

      left-preservation : ∀ {A : Q.Obj} → arrow (Q.unitorˡ.from {A}) ≈ᴿ cross Dict.drop⇒ˡ inj₂
      left-preservation = congruence (R.repack-resp (R.PS.⟺ᴹ Dict.λ⇒-λᴳ)) ○ cross-wire Dict.drop⇒ˡ inj₂

      right-preservation : ∀ {A : Q.Obj} → arrow (Q.unitorʳ.from {A}) ≈ᴿ cross Dict.drop⇒ʳ inj₁
      right-preservation = congruence (R.repack-resp (R.PS.⟺ᴹ Dict.ρ⇒-ρᴳ)) ○ cross-wire Dict.drop⇒ʳ inj₁

  PMmay→native : StrongMonoidalFunctor Model.𝔾₊ Native.𝔾ᴿᵐ
  PMmay→native = record { F = Map.functor ; isStrongMonoidal = coherence }

  PM→native : StrongMonoidalFunctor Seal.𝔾ᵒ Native.𝔾ᴿᵐ
  PM→native = ∘-StrongMonoidal PMmay→native Model.forget-probabilities
