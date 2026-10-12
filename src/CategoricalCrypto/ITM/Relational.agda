{-# OPTIONS --safe #-}

-- The uninitialized structural interpretation into Machine.UC, and the
-- initialization-aware execution boundary (`docs/uc-setup-itm.md` §4.2).
-- The target category has no chosen initial state. Its contextual state
-- isomorphism tests are neither initialized trace tests nor probability tests.
-- Trees are mirrored because the target tensor is reversed.

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
open import Data.Fin.Base using (Fin)
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
open import CategoricalCrypto.Machine.Core hiding (ℰ)
open import CategoricalCrypto.Machine.Initialized
open import CategoricalCrypto.Machine.Iso
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

module Uninitialized where
  leaf : {A B : Ports} → Gen A B → Machine ⟦ A ⟧₀ ⟦ B ⟧₀
  leaf {A} {B} M = MkMachine {State = Mem M} λ m i o m′ →
    Σ[ y ∈ Out A B × Bits ] Halts M (load M m (decodeᴿ A B i)) (m′ , y) × o ≡ just (encodeᴿ A B y)

  module Reinitialize {I O : Set} (M : TM I O) (q : Fin (TM.#Q M)) where
    M′ : TM I O
    M′ = record M { start = q }

    private
      conf-to : Conf M → Conf M′
      conf-to c = record
        { state = Conf.state c ; work = Conf.work c ; port = Conf.port c
        ; input = Conf.input c ; buf = Conf.buf c }

      conf-from : Conf M′ → Conf M
      conf-from c = record
        { state = Conf.state c ; work = Conf.work c ; port = Conf.port c
        ; input = Conf.input c ; buf = Conf.buf c }

    halts-to : ∀ {c r} → Halts M c r → Halts M′ (conf-to c) r
    halts-to (halt eq) = halt eq
    halts-to (step eq h) = step eq (halts-to h)
    halts-to (toss x eq h) = toss x eq (halts-to h)

    halts-from : ∀ {c r} → Halts M′ c r → Halts M (conf-from c) r
    halts-from (halt eq) = halt eq
    halts-from (step eq h) = step eq (halts-from h)
    halts-from (toss x eq h) = toss x eq (halts-from h)

  reinitialize-iso : {A B : Ports} (M : Gen A B) (q : Fin (TM.#Q M))
                   → leaf M ≅ᴹ leaf (Reinitialize.M′ M q)
  reinitialize-iso M q = MkIso (λ s → s) (λ s → s) (λ _ → refl) (λ _ → refl)
    (λ { (y , h , eq) → y , Reinitialize.halts-to M q h , eq })
    (λ { (y , h , eq) → y , Reinitialize.halts-from M q h , eq })

  private
    -- Check contextual congruence before instantiating the relational
    -- category, so elaboration need not normalize its composed step relations.
    module ImageContext {o ℓ e} (ffd : FreeFunctorData itmData {o} {ℓ} {e}) where
      module C = FreeFunctorData.C ffd
      module I = Functor (FreeFunctor.freeFunctor ffd)
      module S = FreeMonoidal itmData

      congruence : ∀ {A X B} {f g : S.HomTerm A (X S.⊗₀ B)} (W : Ports)
                 → I.F₁ f C.≈ I.F₁ g
                 → I.F₁ (S.α⇐ {A = W} {B = X} {C = B} S.∘ (S.id {A = W} S.⊗₁ f))
                   C.≈ I.F₁ (S.α⇐ {A = W} {B = X} {C = B} S.∘ (S.id {A = W} S.⊗₁ g))
      congruence {A} {X} {B} {f} {g} W e = C.∘-resp-≈ C.Equiv.refl
        (C.⊗.F-resp-≈ {I.F₀ W , I.F₀ A} {I.F₀ W , I.F₀ (X S.⊗₀ B)}
          {C.id {A = I.F₀ W} , I.F₁ f} {C.id {A = I.F₀ W} , I.F₁ g}
          (C.Equiv.refl , e))

    relationalData : FreeFunctorData itmData
    relationalData = record { ⟦v⟧ = ⟦v⟧ᴿ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᶜ ; ⟦_⟧ᵖ₁ = leaf }

  F : StrongMonoidalFunctor 𝕋ᴹ Iso.machines
  F = freeStrongMonoidal relationalData

  private
    module F = StrongMonoidalFunctor F
    module Context = ImageContext relationalData

  ℰ : Presheaf (MonoidalCategory.U 𝕋ᴹ) (Setoids (suc 0ℓ) (suc 0ℓ))
  ℰ = Iso.ℰ-tests ∘F Functor.op F.F

  module UC = StdUC 𝕋ᴹ ℰ

  -- `pullbackᵛ`, written out for the reason given at `ITM.Setup.νᵀ`.
  ν : PresheafMorphism F.F ℰ Iso.ℰ-tests
  ν = record { ν = ntHelper record
    { η = λ _ → record { to = λ x → x ; cong = λ e → e }
    ; commute = λ _ → Setoid.refl (Functor.₀ Iso.ℰ-tests _) } }

  ν-epi : PresheafMorphism.Epi ν
  ν-epi y = y , Setoid.refl (Functor.₀ Iso.ℰ-tests _)

  ν-mono : PresheafMorphism.Mono ν
  ν-mono e = e

  ⇒iso : UCSetupMorphism UC.StdSetup Iso.StdSetup
  ⇒iso = StdUCMorphism 𝕋ᴹ Iso.machines ℰ Iso.ℰ-tests F ν

  image-prefix-iso : ∀ {A X B} {f g : A UC.𝒞.⇒ UC.T₀ X B} (W : Ports)
                   → F.₁ f ≅ᴹ F.₁ g
                   → F.₁ (UC.prefix {A = A} {X = X} {B = B} W f)
                     ≅ᴹ F.₁ (UC.prefix {A = A} {X = X} {B = B} W g)
  image-prefix-iso {A} {X} {B} {f} {g} W e =
    Context.congruence {A = A} {X = X} {B = B} {f = f} {g = g} W e

  image-iso⇒≈ᵁ : ∀ {A X B} {f g : A UC.𝒞.⇒ UC.T₀ X B}
               → F.₁ f ≅ᴹ F.₁ g → f UC.≈ᵁ g
  image-iso⇒≈ᵁ {A} {X} {B} {f} {g} e W =
    UC.KE.mk∼ {X = (W UC.⊗₀ X) UC.⊗₀ B} {Y = W UC.⊗₀ A}
      {f = UC.prefix {A = A} {X = X} {B = B} W f}
      {g = UC.prefix {A = A} {X = X} {B = B} W g}
      (Functor.F-resp-≈ Iso.ℰ-tests
        {f = F.₁ (UC.prefix {A = A} {X = X} {B = B} W f)}
        {g = F.₁ (UC.prefix {A = A} {X = X} {B = B} W g)}
        (image-prefix-iso {A = A} {X = X} {B = B} {f = f} {g = g} W e))

initializedLeaf : {A B : Ports} → Gen A B → InitializedMachine ⟦ A ⟧₀ ⟦ B ⟧₀
initializedLeaf M = initialize (Uninitialized.leaf M) (blank M)
