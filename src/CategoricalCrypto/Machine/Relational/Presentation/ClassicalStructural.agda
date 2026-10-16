{-# OPTIONS --safe --guardedness #-}

module CategoricalCrypto.Machine.Relational.Presentation.ClassicalStructural where

open import Axiom.ExcludedMiddle
open import Data.Maybe.Base
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
import Data.Unit.Polymorphic.Base as Poly
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Positive

import CategoricalCrypto.Channel.Core as Ch
open import CategoricalCrypto.Iface
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Forwarder as Fwd
import CategoricalCrypto.Machine.Iso as Iso
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Isomorphism
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.Machine.Relational.Presentation.Classical as Classical
open import CategoricalCrypto.Machine.Relational.Presentation.Descent using (channel)
import CategoricalCrypto.Machines.Positive.Repack as Re
import CategoricalCrypto.UC.Machine as UC

private
  module R = Re.At 0ℓ
  variable A B : Iface

private variable X Y Z V : Ch.Channel

cross : (Ch.Channel.inType X → Ch.Channel.inType Y)
  → (Ch.Channel.outType Y → Ch.Channel.outType X) → Initialized X Y
cross up down = all-states (Fwd.Xfwd up down)

cross-cong : {up up′ : Ch.Channel.inType X → Ch.Channel.inType Y}
  {down down′ : Ch.Channel.outType Y → Ch.Channel.outType X}
  → (∀ x → up x ≡ up′ x) → (∀ y → down y ≡ down′ y) → cross up down ≈ᴿ cross up′ down′
cross-cong up down = all-states-cong (Fwd.Xfwd-≅ᴹ up down)

cross-compose : (up : Ch.Channel.inType X → Ch.Channel.inType Y)
  (down : Ch.Channel.outType Y → Ch.Channel.outType X)
  (up′ : Ch.Channel.inType Y → Ch.Channel.inType Z)
  (down′ : Ch.Channel.outType Z → Ch.Channel.outType Y)
  → (cross up′ down′ W.∘ cross up down) ≈ᴿ cross (λ x → up′ (up x)) (λ z → down (down′ z))
cross-compose up down up′ down′ = total-iso Fwd.∘-Xfwd (λ _ → tt , tt) (λ _ → tt)

cross-tensor : (up : Ch.Channel.inType X → Ch.Channel.inType Y)
  (down : Ch.Channel.outType Y → Ch.Channel.outType X)
  (up′ : Ch.Channel.inType Z → Ch.Channel.inType V)
  (down′ : Ch.Channel.outType V → Ch.Channel.outType Z)
  → (cross up down W.⊗₁ cross up′ down′) ≈ᴿ cross (Fwd.⊗mapᵢ up up′) (Fwd.⊗mapₒ down down′)
cross-tensor up down up′ down′ = total-iso Fwd.⊗₁-Xfwd (λ _ → tt , tt) (λ _ → tt)

cross-id : cross {X} {X} (λ x → x) (λ x → x) ≈ᴿ W.id
cross-id = total-iso (Iso.≅ᴹ-sym Fwd.id-is-Xfwd) (λ _ → tt) (λ _ → refl)

cross-forwarder : (up : X Ch.[ Ch.In ]⇒[ Ch.In ] Y) (down : Y Ch.[ Ch.Out ]⇒[ Ch.Out ] X)
  → all-states (M.TotalFunctionMachine' up down) ≈ᴿ cross (Ch.app up) (Ch.app down)
cross-forwarder up down = all-states-cong (Fwd.tfm'-is-Xfwd up down)

module WithLEM (lem : ExcludedMiddle 0ℓ) where
  open Classical.WithLEM lem

  opaque
    unfolding Ch._⊗₀_ Ch.destruct-⊗ Ch.construct-⊗ Ch.⊗-sym Ch.⊗-combine compile-step

    wire : (up : Pos A → Pos B) (down : Neg B → Neg A)
      → compile (R.repack (UC.wireᴹ up down)) ≈ᴿ
          all-states (M.TotalFunctionMachine' (Ch.mk⇒ up) (Ch.mk⇒ down))
    wire up down = record
      { Related = λ _ _ → ⊤
      ; initial-to = λ _ → tt , tt , tt
      ; initial-from = λ _ → Poly.tt , positive-return Poly.tt , tt
      ; step-to = λ
          { {i = inj₁ a} {o = just o} _ p → tt , cong (λ r → just (proj₂ r)) (positive-return-reflect p) , tt
          ; {i = inj₂ b} {o = just o} _ p → tt , cong (λ r → just (proj₂ r)) (positive-return-reflect p) , tt
          ; {o = nothing} _ () }
      ; step-from = λ
          { {s = s} {i = inj₁ a} {o = just o} _ p → s ,
              subst (λ o → Positive (R.P.step (UC.wireᴹ up down) (s , inj₁ a)) (s , o))
                (just-injective p) (positive-return _) , tt
          ; {s = s} {i = inj₂ b} {o = just o} _ p → s ,
              subst (λ o → Positive (R.P.step (UC.wireᴹ up down) (s , inj₂ b)) (s , o))
                (just-injective p) (positive-return _) , tt
          ; {i = inj₁ a} {o = nothing} _ ()
          ; {i = inj₂ b} {o = nothing} _ () }
      }

    wire-id : compile (R.repack (UC.wireᴹ {A} {A} (λ a → a) (λ b → b))) ≈ᴿ W.id
    wire-id = record
      { Related = λ _ _ → ⊤
      ; initial-to = λ _ → tt , refl , tt
      ; initial-from = λ _ → Poly.tt , positive-return Poly.tt , tt
      ; step-to = step-to (wire (λ a → a) (λ b → b))
      ; step-from = step-from (wire (λ a → a) (λ b → b))
      }

  cross-wire : (up : Pos A → Pos B) (down : Neg B → Neg A)
    → compile (R.repack (UC.wireᴹ up down)) ≈ᴿ cross up down
  cross-wire up down = ≈ᴿ-trans (wire up down) (cross-forwarder (Ch.mk⇒ up) (Ch.mk⇒ down))
