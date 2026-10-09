{-# OPTIONS --safe #-}

-- `itm⇒iso`, the arrow from ITM systems into machine-iso
-- (`docs/uc-setup-itm.md` §4.2).  `Fᴿ` reads a leaf as its run relation
-- (`Halts`): coins become nondeterministic choice, a diverging activation has
-- no transition and `blank` is forgotten.  It is strict into the REVERSED
-- machine tensor, so `⟦ A ⊗₀ B ⟧₀` is `⟦ B ⟧₀ ⊗₀ ⟦ A ⟧₀` and the channel codec
-- reads a tree mirrored.
--
-- The source observation is `ℰᴵˢᵒ`, pulled back from `Machine.UC.ℰ-tests`, not
-- `ITM.Setup`'s `ℰᵀ`: machine-iso compares tests up to state bijections,
-- which no map out of `ℰᵀ`'s classes respects.  K, because `Machine.UC` uses it.

module CategoricalCrypto.ITM.Relational where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base hiding (map₁)
open import Data.Unit.Base
open import Function.Base hiding (flip)
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core hiding (In; Out) renaming (_⊗₀_ to _⊗ᶜ_)
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.Machine.Core
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Machine.UC as Iso

module _ {I O : Set} (M : TM I O) where
  open Conf

  -- `runᵀᴹ` read as a relation: the activation from `c` ends in `r`, a coin
  -- taking either bit.
  data Halts : Conf M → Mem M × (O × Bits) → Set where
    halt : ∀ {c o q} → δ-at M c ≡ send o q → Halts c ((q , work c) , o , reverse (buf c))
    step : ∀ {c q w mʷ mⁱ b r} → δ-at M c ≡ run q w mʷ mⁱ b → Halts (exec M q w mʷ mⁱ b c) r → Halts c r
    toss : ∀ {c q₀ q₁ r} x → δ-at M c ≡ flip q₀ q₁ → Halts (goto M (if x then q₁ else q₀) c) r → Halts c r

open Channel
open FreeMonoidalHelper Mon Pol

-- The tensor clause of `⟦_⟧₀`, stated over an abstract target: unfolding it at
-- the transparent `Iso.machines` keeps the conversion checker busy for more
-- than a minute per use, while this lemma's instance is free.
module _ {o ℓ e} (⟦v⟧ : ⟦ Mon ⟧ᵥ {o} {ℓ} {e}) (⟦_⟧ᵖ₀ : Pol → ⟦_⟧ᵥ.Cat.Obj ⟦v⟧) where
  open FreeObjInterp Mon Pol ⟦v⟧ ⟦_⟧ᵖ₀

  ⊗-step : (A B : Ports) → ⟦ A ⊗₀ B ⟧₀ ≡ ⟦_⟧ᵥ.Cat._⊗₀_ ⟦v⟧ ⟦ A ⟧₀ ⟦ B ⟧₀
  ⊗-step _ _ = refl

⟦_⟧ᶜ : Pol → Channel
⟦ ⁺ ⟧ᶜ = Bits ⇿ ⊥
⟦ ⁻ ⟧ᶜ = ⊥ ⇿ Bits

⟦v⟧ᴿ : ⟦ Mon ⟧ᵥ
⟦v⟧ᴿ = fromMC Iso.machines noSymmetric

open FreeObjInterp Mon Pol ⟦v⟧ᴿ ⟦_⟧ᶜ

⊗-mirror : (A B : Ports) → ⟦ A ⊗₀ B ⟧₀ ≡ ⟦ B ⟧₀ ⊗ᶜ ⟦ A ⟧₀
⊗-mirror = ⊗-step ⟦v⟧ᴿ ⟦_⟧ᶜ

-- `⁺` messages travel rightwards, as a channel's `inType` does.
mode : Pol → Mode
mode ⁺ = Mode.In
mode ⁻ = Mode.Out

decodeᶜ : (p : Pol) (A : Ports) → modeType (mode p) ⟦ A ⟧₀ → Port p A × Bits
decodeᶜ ⁺ unit     ()
decodeᶜ ⁻ unit     ()
decodeᶜ p (A ⊗₀ B) x = [ map₁ inj₂ ∘′ decodeᶜ p B , map₁ inj₁ ∘′ decodeᶜ p A ]′
  (destruct-⊗ {m = mode p} (subst (modeType (mode p)) (⊗-mirror A B) x))
decodeᶜ ⁺ (Var ⁺)  w = tt , w
decodeᶜ ⁺ (Var ⁻)  ()
decodeᶜ ⁻ (Var ⁺)  ()
decodeᶜ ⁻ (Var ⁻)  w = tt , w

encodeᶜ : (p : Pol) (A : Ports) → Port p A × Bits → modeType (mode p) ⟦ A ⟧₀
encodeᶜ _ unit     (() , _)
encodeᶜ p (A ⊗₀ B) (i , w) = subst (modeType (mode p)) (sym (⊗-mirror A B))
  (construct-⊗ {m = mode p} ([ inj₂ ∘′ encodeᶜ p A ∘′ (_, w) , inj₁ ∘′ encodeᶜ p B ∘′ (_, w) ]′ i))
encodeᶜ ⁺ (Var ⁺)  (_ , w) = w
encodeᶜ ⁺ (Var ⁻)  (() , _)
encodeᶜ ⁻ (Var ⁺)  (() , _)
encodeᶜ ⁻ (Var ⁻)  (_ , w) = w

-- The codomain's half of a machine's channel is transposed, so its `⁻` ports
-- arrive with the domain's `⁺` ones and its `⁺` ports leave with the `⁻` ones.
decodeᴿ : (A B : Ports) → inType (⟦ A ⟧₀ ⊗ᵀ ⟦ B ⟧₀) → In A B × Bits
decodeᴿ A B i = [ map₁ inj₁ ∘′ decodeᶜ ⁺ A , map₁ inj₂ ∘′ decodeᶜ ⁻ B ]′ (destruct-⊗ {m = Mode.In} i)

encodeᴿ : (A B : Ports) → Out A B × Bits → outType (⟦ A ⟧₀ ⊗ᵀ ⟦ B ⟧₀)
encodeᴿ A B (inj₁ o , w) = construct-⊗ {m = Mode.Out} (inj₁ (encodeᶜ ⁻ A (o , w)))
encodeᴿ A B (inj₂ o , w) = construct-⊗ {m = Mode.Out} (inj₂ (encodeᶜ ⁺ B (o , w)))

leafᴿ : {A B : Ports} → Gen A B → Machine ⟦ A ⟧₀ ⟦ B ⟧₀
leafᴿ {A} {B} M = MkMachine {State = Mem M} λ m i o m′ →
  Σ[ y ∈ Out A B × Bits ] Halts M (load M m (decodeᴿ A B i)) (m′ , y) × o ≡ just (encodeᴿ A B y)

Fᴿ : StrongMonoidalFunctor 𝕋ᴹ Iso.machines
Fᴿ = freeStrongMonoidal record { ⟦v⟧ = ⟦v⟧ᴿ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᶜ ; ⟦_⟧ᵖ₁ = leafᴿ }

private module Fᴿ = StrongMonoidalFunctor Fᴿ

ℰᴵˢᵒ : Presheaf (MonoidalCategory.U 𝕋ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰᴵˢᵒ = Iso.ℰ-tests ∘F Functor.op Fᴿ.F

module Rel = StdUC 𝕋ᴹ ℰᴵˢᵒ

-- `pullbackᵛ`, written out for the reason given at `ITM.Setup.νᵀ`.
νᴿ : PresheafMorphism Fᴿ.F ℰᴵˢᵒ Iso.ℰ-tests
νᴿ = record { ν = ntHelper record
  { η = λ _ → record { to = λ x → x ; cong = λ e → e } ; commute = λ _ → Setoid.refl (Functor.₀ Iso.ℰ-tests _) } }

νᴿ-epi : PresheafMorphism.Epi νᴿ
νᴿ-epi y = y , Setoid.refl (Functor.₀ Iso.ℰ-tests _)

νᴿ-mono : PresheafMorphism.Mono νᴿ
νᴿ-mono e = e

itm⇒iso : UCSetupMorphism Rel.StdSetup Iso.StdSetup
itm⇒iso = StdUCMorphism 𝕋ᴹ Iso.machines ℰᴵˢᵒ Iso.ℰ-tests Fᴿ νᴿ
