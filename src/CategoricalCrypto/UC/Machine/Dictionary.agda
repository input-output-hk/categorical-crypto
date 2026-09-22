{-# OPTIONS --safe --without-K --guardedness #-}

-- The ancilla dictionary: `UC.Machine`'s direct relays read as the monoidal
-- spellings of the same processes.  Those readings are the bridge between the
-- pinned relays and the 𝒢-tensor's own action — a query-bound certificate is
-- about a relay, a `UC.Budget` field is about `_⊗₁_` with an identity, and
-- `UC.Machine.Grading` carries one to the other through these eight
-- zigzags.  Nothing here states a `Monoidal` law's type, which is what
-- makes it affordable (`UC.Machine`'s header prices the alternative).
--
-- The Kleisli-pure layer the readings run on — `pureᵏ` of a relabelling, the
-- junction calculus, `midᴹ` — is machine-layer, not UC, and lives in
-- `Machines.Pure`.
--
-- Every object implicit is passed explicitly, for the reason `UC.Machine`'s
-- header gives: inferring one asks Agda to invert `_⊗₁ᴳ_`.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle
  using (MonoidalCategory; SymmetricMonoidalCategory)
open import Categories.Monad.Discrete using (DiscreteMonad)
import Categories.Category.Cocartesian.Ext as CE
import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Monoidal.Distributive as MD
import Categories.Category.Monoidal.Utilities as MU
import Categories.GConstructionMonoidal as GM

open import Data.Empty.Polymorphic using (⊥-elim)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Sum.Ext using (⊎assocˡ; ⊎assocʳ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (refl)

open import ProbabilisticLogic.Dp using (Dₚ; returnₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
  using (Dₚ-DiscreteMonad; 𝒱ₚ; 𝒢ₚᴹ; distₚ; 𝒫ₚ)
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Protocol.Machine using (⟦_⟧ᴵ)
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Category as MCat
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Frame as Frame
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Machines.Tensor as Tensor

module CategoricalCrypto.UC.Machine.Dictionary where

private
  module 𝒱 = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module 𝔾 = MonoidalCategory (𝒢ₚᴹ 0ℓ)
  module 𝒫 = Category 𝒫ᴵ

open Core (𝒱ₚ 0ℓ)
open MD.MonoidalDistributive (distₚ 0ℓ)
open CE 𝒱.U cocartesian
open DiscreteMonad (Dₚ-DiscreteMonad {0ℓ})
  renaming (_≈ᴹ_ to _≈ᵈ_; module ≈ᴹ to ≈ᵈ)
open Frame (𝒱ₚ 0ℓ)
open KD (Dₚ-DiscreteMonad {0ℓ})
open MCat (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open MU.Shorthands 𝒱.monoidal
open Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
open Tensor (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ)

open import Categories.Category.Monoidal.Reasoning 𝒱.monoidal

-- The 𝒢-level reassociators, which the base's own `α⇒`/`α⇐` would shadow.
open MU.Shorthands 𝔾.monoidal using () renaming (α⇒ to α⇒ᴳ; α⇐ to α⇐ᴳ)

private
  variable V X : 𝒱.Obj

------------------------------------------------------------------------
-- Every wire is an embedding

private
  -- A wire's step is the copairing of its two relabellings, crossed.
  wireStep-copair : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
                  → 𝒱._≈_ (wireStep {A} {B} up down)
                      (𝒱._⊗₁_ 𝒱.id [ 𝒱._∘_ i₂ (pureᵏ up) , 𝒱._∘_ i₁ (pureᵏ down) ])
  wireStep-copair _ _ (_ , inj₁ _) =
    ≈ᵈ.sym (≈ᵈ.trans >>=-identityˡ-≈
                     (≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈) >>=-identityˡ-≈))
  wireStep-copair _ _ (_ , inj₂ _) =
    ≈ᵈ.sym (≈ᵈ.trans >>=-identityˡ-≈
                     (≈ᵈ.trans (>>=-cong-x >>=-identityˡ-≈) >>=-identityˡ-≈))

------------------------------------------------------------------------
-- The ancilla reassociators are the 𝒢-associator

-- The relays' common shape: a stateless relabelling IS `⌜_,_⌝` of the two
-- directions, whenever the two base maps are pure.  This is what makes
-- `UC.Machine.Wire`'s absorption apply to them — and the six structural
-- zigzags below are its instances, spelled out at the 𝒢-associator and the two
-- 𝒢-unitors.
wire-pure : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
            (u : 𝒱._⇒_ (Pos A) (Pos B)) (v : 𝒱._⇒_ (Neg B) (Neg A))
          → 𝒱._≈_ u (pureᵏ up) → 𝒱._≈_ v (pureᵏ down)
          → 𝒫._≈_ {A} {B} (wireᴹ up down) (σᴹ ∘ᴹ (pureᴹ u ⊗ᵉ pureᴹ v))
wire-pure up down u v eu ev =
    ≲⇒≈ᴹ (mk-cong (wireStep-copair up down ○ ⟺ (refl⟩⊗⟨ bridge)))
  ○ᴹ ≲⇒≈ᴹ˘ (⌜⌝-pureᴹ u v)
  where
  bridge = swap-copair u v ○ []-cong₂ (refl⟩∘⟨ eu) (refl⟩∘⟨ ev)

wire-⌜⌝ : {A B : Iface} (up : Pos A → Pos B) (down : Neg B → Neg A)
        → 𝒫._≈_ {A} {B} (wireᴹ up down)
            (σᴹ ∘ᴹ (pureᴹ (pureᵏ up) ⊗ᵉ pureᴹ (pureᵏ down)))
wire-⌜⌝ up down =
  wire-pure up down (pureᵏ up) (pureᵏ down) 𝒱.Equiv.refl 𝒱.Equiv.refl

a⇒-α⇐ : {X Y A : Iface}
      → 𝒫._≈_ {X ⊗ᴵ (Y ⊗ᴵ A)} {(X ⊗ᴵ Y) ⊗ᴵ A}
          (a⇒ᴵ {X} {Y} {A}) (α⇐ᴳ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
a⇒-α⇐ = wire-pure ⊎assocˡ ⊎assocʳ α+⇐ α+⇒ assocˡᵏ assocʳᵏ

a⇐-α⇒ : {X Y A : Iface}
      → 𝒫._≈_ {(X ⊗ᴵ Y) ⊗ᴵ A} {X ⊗ᴵ (Y ⊗ᴵ A)}
          (a⇐ᴵ {X} {Y} {A}) (α⇒ᴳ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ})
a⇐-α⇒ = wire-pure ⊎assocʳ ⊎assocˡ α+⇒ α+⇐ assocʳᵏ assocˡᵏ

------------------------------------------------------------------------
-- The trivial-ancilla relays are the 𝒢-unitors

-- The bundle's own monoidal unit, read as an interface.  It is NOT `unitᴵ`:
-- that one is empty at `Data.Empty.⊥` and this one at `𝒱ₚ`'s initial object,
-- and `docs/stduc-supersession-plan.md` §1.1 prices the iso between them.
𝟭ᴵ : Iface
𝟭ᴵ = retᴵ 𝔾.unit

-- The relabellings a unitor performs: the trivial ancilla contributes no case.
drop⇒ˡ : {A : Set} → Pos 𝟭ᴵ ⊎ A → A
drop⇒ˡ = Sum.[ ⊥-elim , (λ a → a) ]

drop⇒ʳ : {A : Set} → A ⊎ Neg 𝟭ᴵ → A
drop⇒ʳ = Sum.[ (λ a → a) , ⊥-elim ]

private
  -- The cocartesian unitors are pure: `to` is an injection on the nose, and
  -- `from` is the copairing whose empty leg has no clause.
  unitˡᵏ : 𝒱._≈_ (⊕.unitorˡ.from {V}) (pureᵏ drop⇒ˡ)
  unitˡᵏ (inj₂ _) = ≈ᵈ.refl

  unitʳᵏ : 𝒱._≈_ (⊕.unitorʳ.from {V}) (pureᵏ drop⇒ʳ)
  unitʳᵏ (inj₁ _) = ≈ᵈ.refl

  unitˡᵏ⁻ : 𝒱._≈_ (⊕.unitorˡ.to {V}) (pureᵏ inj₂)
  unitˡᵏ⁻ _ = ≈ᵈ.refl

  unitʳᵏ⁻ : 𝒱._≈_ (⊕.unitorʳ.to {V}) (pureᵏ inj₁)
  unitʳᵏ⁻ _ = ≈ᵈ.refl

λ⇒-λᴳ : {A : Iface}
      → 𝒫._≈_ {𝟭ᴵ ⊗ᴵ A} {A} (wireᴹ drop⇒ˡ inj₂) (𝔾.unitorˡ.from {⟦ A ⟧ᴵ})
λ⇒-λᴳ = wire-pure drop⇒ˡ inj₂ ⊕.unitorˡ.from ⊕.unitorˡ.to unitˡᵏ unitˡᵏ⁻

λ⇐-λᴳ : {A : Iface}
      → 𝒫._≈_ {A} {𝟭ᴵ ⊗ᴵ A} (wireᴹ inj₂ drop⇒ˡ) (𝔾.unitorˡ.to {⟦ A ⟧ᴵ})
λ⇐-λᴳ = wire-pure inj₂ drop⇒ˡ ⊕.unitorˡ.to ⊕.unitorˡ.from unitˡᵏ⁻ unitˡᵏ

ρ⇒-ρᴳ : {A : Iface}
      → 𝒫._≈_ {A ⊗ᴵ 𝟭ᴵ} {A} (wireᴹ drop⇒ʳ inj₁) (𝔾.unitorʳ.from {⟦ A ⟧ᴵ})
ρ⇒-ρᴳ = wire-pure drop⇒ʳ inj₁ ⊕.unitorʳ.from ⊕.unitorʳ.to unitʳᵏ unitʳᵏ⁻

ρ⇐-ρᴳ : {A : Iface}
      → 𝒫._≈_ {A} {A ⊗ᴵ 𝟭ᴵ} (wireᴹ inj₁ drop⇒ʳ) (𝔾.unitorʳ.to {⟦ A ⟧ᴵ})
ρ⇐-ρᴳ = wire-pure inj₁ drop⇒ʳ ⊕.unitorʳ.to ⊕.unitorʳ.from unitʳᵏ⁻ unitʳᵏ

------------------------------------------------------------------------
-- The two relays are the 𝒢-tensor with an identity

private
  -- Both relays collapse to the same shape: the conjugation of a `tstep` by the
  -- interchange, which is what `_⊗₁ᴳ_` is once its two `mid`s are absorbed.
  T₁-step : {Y A B : Iface} (f : Proc A B)
          → 𝒱._≈_
              (𝒱._∘_ (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))
                     (𝒱._∘_ (tstep (𝒱._⊗₁_ 𝒱.id +-swap) (step f))
                            (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))))
              (step (T₁ᴵ Y {A} {B} f))
  T₁-step f (s , inj₁ (inj₁ y)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₁ (inj₁ y))) relabel))
             (exit-pure midfn s (inj₁ (inj₂ y)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₁ _ _ s (inj₁ y))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (s , inj₁ y))) >>=-identityˡ-≈)
  T₁-step f (s , inj₂ (inj₁ y)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₂ (inj₁ y))) relabel))
             (exit-pure midfn s (inj₁ (inj₁ y)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₁ _ _ s (inj₂ y))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (s , inj₂ y))) >>=-identityˡ-≈)
  T₁-step f (s , inj₁ (inj₂ a)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₁ (inj₂ a)))
                                   (tstep-inj₂ _ _ s (inj₁ a))))
             (≈ᵈ.trans (>>=-assoc-≈ (step f (s , inj₁ a)))
                       (>>=-cong-f λ where
                          (s′ , inj₁ a′) → exit-pure midfn s′ (inj₂ (inj₁ a′))
                          (s′ , inj₂ b′) → exit-pure midfn s′ (inj₂ (inj₂ b′))))
  T₁-step f (s , inj₂ (inj₂ b)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ s (inj₂ (inj₂ b)))
                                   (tstep-inj₂ _ _ s (inj₂ b))))
             (≈ᵈ.trans (>>=-assoc-≈ (step f (s , inj₂ b)))
                       (>>=-cong-f λ where
                          (s′ , inj₁ a′) → exit-pure midfn s′ (inj₂ (inj₁ a′))
                          (s′ , inj₂ b′) → exit-pure midfn s′ (inj₂ (inj₂ b′))))

  sub-step : {X Y A : Iface} (s : Proc X Y)
           → 𝒱._≈_
               (𝒱._∘_ (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))
                      (𝒱._∘_ (tstep (step s) (𝒱._⊗₁_ 𝒱.id +-swap))
                             (𝒱._⊗₁_ 𝒱.id (pureᵏ midfn))))
               (step (subᴵ′ {X} {Y} {A} s))
  sub-step s (t , inj₁ (inj₂ a)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₁ (inj₂ a))) relabel))
             (exit-pure midfn t (inj₂ (inj₂ a)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₂ _ _ t (inj₁ a))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (t , inj₁ a))) >>=-identityˡ-≈)
  sub-step s (t , inj₂ (inj₂ a)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₂ (inj₂ a))) relabel))
             (exit-pure midfn t (inj₂ (inj₁ a)))
    where
    relabel = ≈ᵈ.trans (tstep-inj₂ _ _ t (inj₂ a))
                       (≈ᵈ.trans (>>=-cong-x (swapᴵ (t , inj₂ a))) >>=-identityˡ-≈)
  sub-step s (t , inj₁ (inj₁ x)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₁ (inj₁ x)))
                                   (tstep-inj₁ _ _ t (inj₁ x))))
             (≈ᵈ.trans (>>=-assoc-≈ (step s (t , inj₁ x)))
                       (>>=-cong-f λ where
                          (t′ , inj₁ x′) → exit-pure midfn t′ (inj₁ (inj₁ x′))
                          (t′ , inj₂ y′) → exit-pure midfn t′ (inj₁ (inj₂ y′))))
  sub-step s (t , inj₂ (inj₁ y)) =
    ≈ᵈ.trans (>>=-cong-x (≈ᵈ.trans (enter-pure midfn _ t (inj₂ (inj₁ y)))
                                   (tstep-inj₁ _ _ t (inj₂ y))))
             (≈ᵈ.trans (>>=-assoc-≈ (step s (t , inj₂ y)))
                       (>>=-cong-f λ where
                          (t′ , inj₁ x′) → exit-pure midfn t′ (inj₁ (inj₁ x′))
                          (t′ , inj₂ y′) → exit-pure midfn t′ (inj₁ (inj₂ y′))))

opaque
  unfolding midᴹ GM._⊗₁ᴳ_

  T₁-⊗₁ : {Y A B : Iface} (f : Proc A B)
        → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y {A} {B} f)
            (𝔾._⊗₁_ {⟦ Y ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ B ⟧ᴵ} (𝒫.id {Y}) f)
  T₁-⊗₁ {Y} {A} {B} f = ⟺ᴹ
    ( ∘ᴹ-resp-≈ᴹ midᴹ-pure (∘ᴹ-resp-≈ᴹ reflᴹ midᴹ-pure)
    ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (∘ᴹ-resp-≲ (pure⊗-stateˡ +-swap f) ≲-refl))
    ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ (pureᵏ midfn) _))
    ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ (pureᵏ midfn) _)
    ○ᴹ ≲⇒≈ᴹ (mk-cong (T₁-step {Y} {A} {B} f)) )

  sub-⊗₁ : {X Y A : Iface} (s : Proc X Y)
         → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ′ {X} {Y} {A} s)
             (𝔾._⊗₁_ {⟦ X ⟧ᴵ} {⟦ Y ⟧ᴵ} {⟦ A ⟧ᴵ} {⟦ A ⟧ᴵ} s (𝒫.id {A}))
  sub-⊗₁ {X} {Y} {A} s = ⟺ᴹ
    ( ∘ᴹ-resp-≈ᴹ midᴹ-pure (∘ᴹ-resp-≈ᴹ reflᴹ midᴹ-pure)
    ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (∘ᴹ-resp-≲ (pure⊗-stateʳ s +-swap) ≲-refl))
    ○ᴹ ≲⇒≈ᴹ (∘ᴹ-resp-≲ ≲-refl (pure-∘ʳ (pureᵏ midfn) _))
    ○ᴹ ≲⇒≈ᴹ (pure-∘ˡ (pureᵏ midfn) _)
    ○ᴹ ≲⇒≈ᴹ (mk-cong (sub-step {X} {Y} {A} s)) )

------------------------------------------------------------------------
-- The ancilla relay is a functor

-- What the zigzag above buys without unfolding anything: the 𝒢-tensor's own
-- functoriality read back on `T₁ᴵ`.  A composite relayed past an ancilla is
-- the relays composed, which is what lets a morphism absorbed into a context
-- slide off the process and onto the test
-- (`UC.Model.EventBounds.ctxRun-∘`).

T₁-resp-≈ : {Y A B : Iface} {f g : Proc A B} → 𝒫._≈_ {A} {B} f g
          → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} (T₁ᴵ Y f) (T₁ᴵ Y g)
T₁-resp-≈ {Y} {A} {B} {f} {g} e =
     T₁-⊗₁ {Y} {A} {B} f
  ○ᴹ 𝔾.⊗.F-resp-≈ {(⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ)} {(⟦ Y ⟧ᴵ , ⟦ B ⟧ᴵ)}
       {(𝒫.id {Y} , f)} {(𝒫.id {Y} , g)} (𝔾.Equiv.refl {x = 𝒫.id {Y}} , e)
  ○ᴹ ⟺ᴹ (T₁-⊗₁ {Y} {A} {B} g)

sub-resp-≈ : {X Y A : Iface} {s t : Proc X Y} → 𝒫._≈_ {X} {Y} s t
           → 𝒫._≈_ {X ⊗ᴵ A} {Y ⊗ᴵ A} (subᴵ s {A}) (subᴵ t {A})
sub-resp-≈ {X} {Y} {A} {s} {t} e =
     sub-⊗₁ {X} {Y} {A} s
  ○ᴹ 𝔾.⊗.F-resp-≈ {(⟦ X ⟧ᴵ , ⟦ A ⟧ᴵ)} {(⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ)}
       {(s , 𝒫.id {A})} {(t , 𝒫.id {A})} (e , 𝔾.Equiv.refl {x = 𝒫.id {A}})
  ○ᴹ ⟺ᴹ (sub-⊗₁ {X} {Y} {A} t)

T₁-∘ : {Y A B C : Iface} (g : Proc B C) (f : Proc A B)
     → 𝒫._≈_ {Y ⊗ᴵ A} {Y ⊗ᴵ C} (T₁ᴵ Y (g 𝒫.∘ f)) (T₁ᴵ Y g 𝒫.∘ T₁ᴵ Y f)
T₁-∘ {Y} {A} {B} {C} g f =
     T₁-⊗₁ {Y} {A} {C} (g 𝒫.∘ f)
  ○ᴹ 𝔾.⊗.F-resp-≈ {(⟦ Y ⟧ᴵ , ⟦ A ⟧ᴵ)} {(⟦ Y ⟧ᴵ , ⟦ C ⟧ᴵ)}
       {(𝒫.id {Y} , g 𝒫.∘ f)} {(𝒫.id {Y} 𝒫.∘ 𝒫.id {Y} , g 𝒫.∘ f)}
       (𝒫.Equiv.sym 𝒫.identity² , 𝔾.Equiv.refl {x = g 𝒫.∘ f})
  ○ᴹ 𝔾.⊗.homomorphism
  ○ᴹ ⟺ᴹ (𝒫.∘-resp-≈ (T₁-⊗₁ {Y} {B} {C} g) (T₁-⊗₁ {Y} {A} {B} f))
