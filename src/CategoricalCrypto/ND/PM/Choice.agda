{-# OPTIONS --safe --without-K --guardedness #-}

-- A choice is selected on demand: the first activation is retained until the
-- new choice factor supplies its pick. Branch initialisation happens only
-- after that pick; requests by the selected branch remain online.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
import Data.Unit.Polymorphic.Base as PolyUnit
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Factor.Read
open import CategoricalCrypto.ND.PM.Read
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.Relabel using (Pick)
open import CategoricalCrypto.SSP.Iface using (Ch)
open import CategoricalCrypto.ND.SSP.Choice using (Cᴵ⟦_⟧)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.ND.PM.Choice where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module P = Category 𝒫ᴵ
  module N = Grade 𝔾ˢ C
  variable
    A B D E : Iface
    S : Set
    S⃗ T⃗ : List Set

Proc⁺ : List Set → Iface → Iface → Set₁
Proc⁺ S⃗ A B = Proc A (Cᶠ S⃗ ⊗ᴵ B)

module Online {S : Set} {S⃗ : List Set} {A B : Iface} (P : S → Proc⁺ S⃗ A B) where
  Input : Set
  Input = Pos A ⊎ (Pick S⃗ ⊎ Neg B)

  data State : Set where
    fresh : State
    wait : Input → State
    active : (s : S) → MC.St (P s) → State

  emit : Neg A ⊎ (Ch Cᴵ⟦ S⃗ ⟧ ⊎ Pos B) → Neg A ⊎ ((Ch Cᴵ⟦ S ∷ S⃗ ⟧) ⊎ Pos B)
  emit (inj₁ a) = inj₁ a
  emit (inj₂ (inj₁ c)) = inj₂ (inj₁ (inj₂ c))
  emit (inj₂ (inj₂ b)) = inj₂ (inj₂ b)

  run : (s : S) → MC.St (P s) → Input → Dₚ (State × (Neg A ⊎ (Ch Cᴵ⟦ S ∷ S⃗ ⟧ ⊎ Pos B)))
  run s t i = mapₚ (λ (t′ , o) → active s t′ , emit o) (MC.step (P s) (t , i))

  feed : State → Input → Dₚ (State × (Neg A ⊎ (Ch Cᴵ⟦ S ∷ S⃗ ⟧ ⊎ Pos B)))
  feed fresh i = returnₚ (wait i , inj₂ (inj₁ (inj₁ tt)))
  feed (wait _) _ = botₚ
  feed (active s t) i = run s t i

  step : State × (Pos A ⊎ (Pick (S ∷ S⃗) ⊎ Neg B))
       → Dₚ (State × (Neg A ⊎ (Ch Cᴵ⟦ S ∷ S⃗ ⟧ ⊎ Pos B)))
  step (t , inj₁ a) = feed t (inj₁ a)
  step (wait i , inj₂ (inj₁ (inj₁ _ , s))) = MC.point (MC.state (P s)) PolyUnit.tt >>=ₚ λ t → run s t i
  step (fresh , inj₂ (inj₁ (inj₁ _ , _))) = botₚ
  step (active _ _ , inj₂ (inj₁ (inj₁ _ , _))) = botₚ
  step (t , inj₂ (inj₁ (inj₂ c , p))) = feed t (inj₂ (inj₁ (c , p)))
  step (t , inj₂ (inj₂ b)) = feed t (inj₂ (inj₂ b))

  machine : Proc⁺ (S ∷ S⃗) A B
  machine = MC.mk (initˢ State fresh) step

  choose-request : (a : Pos A) → step (fresh , inj₁ a) ≡ returnₚ (wait (inj₁ a) , inj₂ (inj₁ (inj₁ tt)))
  choose-request _ = refl

  choose-resume : (i : Input) (s : S)
                → step (wait i , inj₂ (inj₁ (inj₁ tt , s))) ≡ (MC.point (MC.state (P s)) PolyUnit.tt >>=ₚ λ t → run s t i)
  choose-resume _ _ = refl

choose : (S → Proc⁺ S⃗ A B) → Proc⁺ (S ∷ S⃗) A B
choose {S} {S⃗} {A} {B} = Online.machine {S} {S⃗} {A} {B}

------------------------------------------------------------------------
-- Graded process operations
------------------------------------------------------------------------

plain : Proc A B → Proc⁺ [] A B
plain {A} {B} p = P._∘_ {A} {𝟭ᴵ ⊗ᴵ B} {Cᶠ [] ⊗ᴵ B} (subᴵ {A = B} nilᶠ)
  (P._∘_ {A} {B} {𝟭ᴵ ⊗ᴵ B} (wireᴹ {B} {𝟭ᴵ ⊗ᴵ B} inj₂ drop⇒ˡ) p)

infixr 9 _∘⁺_
_∘⁺_ : Proc⁺ T⃗ B D → Proc⁺ S⃗ A B → Proc⁺ (S⃗ ++ T⃗) A D
_∘⁺_ {T⃗} {B} {D} {S⃗} {A} q p =
  P._∘_ {A} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ D} {Cᶠ (S⃗ ++ T⃗) ⊗ᴵ D} (subᴵ {A = D} (joinᶠ S⃗ T⃗))
    (P._∘_ {A} {Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ D)} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ D} (a⇐ᴵ {Cᶠ S⃗} {Cᶠ T⃗} {D})
      (P._∘_ {A} {Cᶠ S⃗ ⊗ᴵ B} {Cᶠ S⃗ ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ D)} (T₁ᴵ (Cᶠ S⃗) q) p))

infixr 10 _⊗⁺_
_⊗⁺_ : Proc⁺ S⃗ A B → Proc⁺ T⃗ D E → Proc⁺ (S⃗ ++ T⃗) (A ⊗ᴵ D) (B ⊗ᴵ E)
_⊗⁺_ {S⃗} {A} {B} {T⃗} {D} {E} p q =
  P._∘_ {A ⊗ᴵ D} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ (B ⊗ᴵ E)} {Cᶠ (S⃗ ++ T⃗) ⊗ᴵ (B ⊗ᴵ E)} (subᴵ {A = B ⊗ᴵ E} (joinᶠ S⃗ T⃗))
    (P._∘_ {A ⊗ᴵ D} {(Cᶠ S⃗ ⊗ᴵ B) ⊗ᴵ (Cᶠ T⃗ ⊗ᴵ E)} {(Cᶠ S⃗ ⊗ᴵ Cᶠ T⃗) ⊗ᴵ (B ⊗ᴵ E)}
      (swapInnerᴵ (Cᶠ S⃗) B (Cᶠ T⃗) E) (tensorᴵ {A} {Cᶠ S⃗ ⊗ᴵ B} {D} {Cᶠ T⃗ ⊗ᴵ E} p q))

⌈_⌉ : Proc⁺ S⃗ A B → ifaceᵒ A G.⇒ N.C⟦ S⃗ ⟧ G.⊗₀ ifaceᵒ B
⌈_⌉ {S⃗} {A} {B} p = conjugate (ifaceᶠ A) (flat S⃗ ⊗ᶠ ifaceᶠ B) p

reads-compile : (p : Proc⁺ S⃗ A B) → Reads (ifaceᶠ A) (flat S⃗ ⊗ᶠ ifaceᶠ B) (⌈_⌉ {S⃗} {A} {B} p) p
reads-compile {S⃗} {A} {B} p = reads-conjugate (ifaceᶠ A) (flat S⃗ ⊗ᶠ ifaceᶠ B) p
