{-# OPTIONS --safe --without-K --guardedness #-}

-- SSP compiled into PM[wb] (`docs/uc-setup-ssp.md` §4.3).  A protocol compiles
-- to a well-bracketed machine (`UC.Bracket.morphism-W`), hence to a map of
-- `𝒲ᴹ`, and compilation respects `≈ᵖ` and `∘ᵖ` already at `𝒲ᴹ`'s hom equality.
-- The identity and the tensor hold only in PM[wb]: every padded well-bracketed
-- closure absorbs the compiled identity `eᵂ` (`absorbᵂ`), so maps that agree
-- under `eᵂ` on both sides are equal there (`≈-under-eᵂ`), and under `eᵂ` the
-- compiled identity, tensor and structure maps are `𝒲ᴹ`'s
-- (`UC.Bracket.Monitor`, `UC.Bracket.Relabel`).  Hence `Fᵂ`.  The morphism of
-- setups also needs SSP-indistinguishable tests to stay indistinguishable
-- against every well-bracketed closure, a density fact taken as the parameter
-- of `GamesDense`; the transfer of `≤UC` needs `Preserves-≈ℰ` besides.

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism

open import Data.Product.Base
open import Level

open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Compose
open import CategoricalCrypto.Protocol.Machine.Resp
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Bracket.Monitor
open import CategoricalCrypto.UC.Bracket.Monoidal
open import CategoricalCrypto.UC.Bracket.Relabel
open import CategoricalCrypto.UC.Bracket.Setup
open import CategoricalCrypto.UC.Bracket.Tensor
open import CategoricalCrypto.UC.Core
open import CategoricalCrypto.UC.Machine hiding (Ωᴵ)
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UCSetup.Morphism

import Categories.Category.Monoidal.Construction.Quotient as Quotient
import Categories.Morphism as Mor
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.SSP.Setup as SSP

module CategoricalCrypto.SSP.Semantics where

private
  module G  = MonoidalCategory 𝔾ᵒ
  module Gᴹ = Mor G.U
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ
  module P  = MonoidalCategory Protᴹ

private variable A B C D : Iface

------------------------------------------------------------------------
-- Compiled protocols as well-bracketed maps

⟦_⟧ᵂ : Protocol A B → A 𝒲ᵂ.⇒ B
⟦_⟧ᵂ {A} P = procᵒ (protᴹ P) , protᴹ P , morphism-W ⦃ Ch-dec A ⦄ P , G.Equiv.refl

⟦⟧ᵂ-resp : {P P′ : Protocol A B} → P ≈ᵖ P′ → ⟦ P ⟧ᵂ 𝒲ᵂ.≈ ⟦ P′ ⟧ᵂ
⟦⟧ᵂ-resp {A} e = ≈ᴹ⇒≈ᵒ (morphism-resp (toProtocol-resp ⦃ Ch-dec A ⦄ e))

⟦⟧ᵂ-∘ : (P₂ : Protocol B C) (P₁ : Protocol A B) → ⟦ P₂ ∘ᵖ P₁ ⟧ᵂ 𝒲ᵂ.≈ ⟦ P₂ ⟧ᵂ 𝒲ᵂ.∘ ⟦ P₁ ⟧ᵂ
⟦⟧ᵂ-∘ {B} {A = A} P₂ P₁ = G.Equiv.trans
  (≈ᴹ⇒≈ᵒ (morphism-sim (toProtocol-∘ ⦃ Ch-dec A ⦄ ⦃ Ch-dec B ⦄ P₂ P₁) S.○ᴹ morphismCompose _ _)) (procᵒ-∘ _ _)

-- The compiled identity: the monitor of `docs/uc-setup-ssp.md` §4.3.
eᵂ : A 𝒲ᵂ.⇒ A
eᵂ = ⟦ wireᵖ ⟧ᵂ

eᵂ-idem : eᵂ {A} 𝒲ᵂ.∘ eᵂ {A} 𝒲ᵂ.≈ eᵂ {A}
eᵂ-idem {A} = G.Equiv.trans (G.Equiv.sym (⟦⟧ᵂ-∘ (wireᵖ {A}) (wireᵖ {A})))
  (⟦⟧ᵂ-resp (≲⇒≈ᵖ (wireᵖ-identityˡ (wireᵖ {A}))))

------------------------------------------------------------------------
-- Absorption into closures

-- A map padded with identities and run against a closure is, as a hom of
-- `𝔾ᵒ`, the machine composite of the two witnesses.
pad∘ : {Y A B Z : Iface} (X : A 𝒲ᵂ.⇒ B) (c : unitᴵ 𝒲ᵂ.⇒ (Y ⊗ᴵ A) ⊗ᴵ Z)
     → proj₁ ((𝒲ᵂ.id {Y} 𝒲ᵂ.⊗₁ X) 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {Z} 𝒲ᵂ.∘ c)
       G.≈ procᵒ (𝒫._∘_ {flat unitᴵ} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)} {flat ((Y ⊗ᴵ B) ⊗ᴵ Z)}
                    (_⊗ʷ_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Z} {Z} (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) (proj₁ (proj₂ X)))
                          (𝒫.id {flat Z}))
                    (proj₁ (proj₂ c)))
pad∘ {Y} {A} {B} {Z} (x , x̂ , _ , ex) (c , ĉ , _ , ec) =
  G.∘-resp-≈ (refl⟩∘⟨ (G.⊗.F-resp-≈ (inner , procᵒ-id) ⟩∘⟨refl)) ec
  ○ (⊗-conj {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Z} {Z} (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) x̂) (𝒫.id {flat Z}) ⟩∘⟨refl)
  ○ ⟺ (procᵒ-∘ {flat unitᴵ} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)} {flat ((Y ⊗ᴵ B) ⊗ᴵ Z)} _ ĉ)
  where
  open G.HomReasoning
  inner : Gᴹ._≅_.from (φ {Y} {B}) G.∘ (G.id G.⊗₁ x) G.∘ Gᴹ._≅_.to (φ {Y} {A})
          G.≈ procᵒ (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) x̂)
  inner = (refl⟩∘⟨ (G.⊗.F-resp-≈ (procᵒ-id , ex) ⟩∘⟨refl)) ○ ⊗-conj {Y} {Y} {A} {B} (𝒫.id {flat Y}) x̂

-- Every padded well-bracketed closure absorbs the monitor.
absorbᵂ : {Y A Z : Iface} (c : unitᴵ 𝒲ᵂ.⇒ (Y ⊗ᴵ A) ⊗ᴵ Z) → pad {Y} {Z = Z} (eᵂ {A}) 𝒲ᵂ.∘ c 𝒲ᵂ.≈ c
absorbᵂ {Y} {A} {Z} c@(_ , ĉ , wĉ , eĉ) = pad∘ (eᵂ {A}) c ○ ≈ᴹ⇒≈ᵒ (monitor-invisible {Y} {A} {Z} ĉ wĉ) ○ ⟺ eĉ
  where open G.HomReasoning

-- Agreement under the monitor on both sides, read off the first components.
≈-under-eᵂ : {f g : A 𝒲ᵂ.⇒ B} → proj₁ (eᵂ {B} 𝒲ᵂ.∘ f 𝒲ᵂ.∘ eᵂ {A}) G.≈ proj₁ (eᵂ {B} 𝒲ᵂ.∘ g 𝒲ᵂ.∘ eᵂ {A}) → f ≈ g
≈-under-eᵂ {A} {B} {f} {g} = monitored⇒∼ eᵂ absorbᵂ {A} {B} {f} {g}

------------------------------------------------------------------------
-- The two lemmas and the structure maps

-- Lemma 1 (`docs/uc-setup-ssp.md` §4.3): in PM[wb] the monitor is the identity.
wire≈σ : eᵂ {A} ≈ id
wire≈σ {A} = ≈-under-eᵂ {A} {A} {eᵂ} {𝒲ᵂ.id} (refl⟩∘⟨ (eᵂ-idem {A} ○ ⟺ G.identityˡ))
  where open G.HomReasoning

⊗-monitorᵂ : (P : Protocol A B) (P′ : Protocol C D)
           → eᵂ {B ⊗ᴵ D} 𝒲ᵂ.∘ ⟦ P ⊗ᵖ P′ ⟧ᵂ 𝒲ᵂ.∘ eᵂ {A ⊗ᴵ C}
             𝒲ᵂ.≈ eᵂ {B ⊗ᴵ D} 𝒲ᵂ.∘ (⟦ P ⟧ᵂ 𝒲ᵂ.⊗₁ ⟦ P′ ⟧ᵂ) 𝒲ᵂ.∘ eᵂ {A ⊗ᴵ C}
⊗-monitorᵂ {A} {B} {C} {D} P P′ =
    ⟺ (unproc (protᴹ (P ⊗ᵖ P′)))
  ○ ≈ᴹ⇒≈ᵒ (S.⟺ᴹ (⊗-monitor {A} {B} {C} {D} P P′))
  ○ unproc (_⊗ʷ_ {A} {B} {C} {D} (protᴹ P) (protᴹ P′))
  ○ (refl⟩∘⟨ (⟺ (⊗-conj {A} {B} {C} {D} (protᴹ P) (protᴹ P′)) ⟩∘⟨refl))
  where
  open G.HomReasoning
  unproc : (h : Proc (flat (A ⊗ᴵ C)) (flat (B ⊗ᴵ D)))
         → procᵒ (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {flat (B ⊗ᴵ D)} (e (B ⊗ᴵ D))
                   (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} h (e (A ⊗ᴵ C))))
           G.≈ procᵒ (e (B ⊗ᴵ D)) G.∘ procᵒ h G.∘ procᵒ (e (A ⊗ᴵ C))
  unproc h = procᵒ-∘ (e (B ⊗ᴵ D)) _ ○ (refl⟩∘⟨ procᵒ-∘ h (e (A ⊗ᴵ C)))

-- Lemma 2 (`docs/uc-setup-ssp.md` §4.3): in PM[wb] compilation preserves the tensor.
⊗≈⊗ : (P : Protocol A B) (P′ : Protocol C D) → ⟦ P ⊗ᵖ P′ ⟧ᵂ ≈ ⟦ P ⟧ᵂ ⊗₁ ⟦ P′ ⟧ᵂ
⊗≈⊗ {A} {B} {C} {D} P P′ = ≈-under-eᵂ {A ⊗ᴵ C} {B ⊗ᴵ D} {⟦ P ⊗ᵖ P′ ⟧ᵂ} {⟦ P ⟧ᵂ 𝒲ᵂ.⊗₁ ⟦ P′ ⟧ᵂ} (⊗-monitorᵂ P P′)

-- A compiled structure map of `Protᴹ` is `𝒲ᴹ`'s after the monitor.
λ-relabelᵂ : ⟦ P.unitorˡ.from {A} ⟧ᵂ 𝒲ᵂ.≈ 𝒲ᵂ.unitorˡ.from {A} 𝒲ᵂ.∘ eᵂ {unitᴵ ⊗ᴵ A}
λ-relabelᵂ {A} = ≈ᴹ⇒≈ᵒ (λ-relabel {A}) ○ procᵒ-∘ (λʷ {A}) (e (unitᴵ ⊗ᴵ A)) ○ (⟺ (λ-wire {A}) ⟩∘⟨refl)
  where open G.HomReasoning

ρ-relabelᵂ : ⟦ P.unitorʳ.from {A} ⟧ᵂ 𝒲ᵂ.≈ 𝒲ᵂ.unitorʳ.from {A} 𝒲ᵂ.∘ eᵂ {A ⊗ᴵ unitᴵ}
ρ-relabelᵂ {A} = ≈ᴹ⇒≈ᵒ (ρ-relabel {A}) ○ procᵒ-∘ (ρʷ {A}) (e (A ⊗ᴵ unitᴵ)) ○ (⟺ (ρ-wire {A}) ⟩∘⟨refl)
  where open G.HomReasoning

α-relabelᵂ : ⟦ P.associator.from {A} {B} {C} ⟧ᵂ 𝒲ᵂ.≈ 𝒲ᵂ.associator.from {A} {B} {C} 𝒲ᵂ.∘ eᵂ {(A ⊗ᴵ B) ⊗ᴵ C}
α-relabelᵂ {A} {B} {C} =
  ≈ᴹ⇒≈ᵒ (α-relabel {A} {B} {C}) ○ procᵒ-∘ (αʷ {A} {B} {C}) (e ((A ⊗ᴵ B) ⊗ᴵ C)) ○ (⟺ (α-wire {A} {B} {C}) ⟩∘⟨refl)
  where open G.HomReasoning

------------------------------------------------------------------------
-- The functor

Fᵂ : StrongMonoidalFunctor Protᴹ PM[wb]ᴹ
Fᵂ = record
  { F = record
    { F₀ = λ A → A ; F₁ = ⟦_⟧ᵂ ; identity = wire≈σ
    ; homomorphism = λ {_} {_} {_} {f} {g} → ≈⇒∼ (⟦⟧ᵂ-∘ g f)
    ; F-resp-≈ = λ e → ≈⇒∼ (⟦⟧ᵂ-resp e) }
  ; isStrongMonoidal = record
    { ε = Mor.≅.refl (MonoidalCategory.U PM[wb]ᴹ)
    ; ⊗-homo = niHelper record
      { η = λ (A , C) → id {A ⊗ᴵ C} ; η⁻¹ = λ (A , C) → id {A ⊗ᴵ C}
      ; commute = λ { {A , C} {B , D} (p , p′) →
          ≈-under-eᵂ {A ⊗ᴵ C} {B ⊗ᴵ D} {id ∘ ⟦ p ⟧ᵂ ⊗₁ ⟦ p′ ⟧ᵂ} {⟦ p ⊗ᵖ p′ ⟧ᵂ ∘ id}
            ((refl⟩∘⟨ (G.identityˡ ⟩∘⟨refl)) ○ ⟺ (⊗-monitorᵂ p p′) ○ (refl⟩∘⟨ (⟺ G.identityʳ ⟩∘⟨refl))) }
      ; iso = λ _ → record { isoˡ = ≈⇒∼ G.identity² ; isoʳ = ≈⇒∼ G.identity² } }
    ; associativity = λ {X} {Y} {Z} →
        ≈-under-eᵂ {(X ⊗ᴵ Y) ⊗ᴵ Z} {X ⊗ᴵ (Y ⊗ᴵ Z)}
          {⟦ P.associator.from ⟧ᵂ 𝒲ᵂ.∘ 𝒲ᵂ.id 𝒲ᵂ.∘ 𝒲ᵂ.id {X ⊗ᴵ Y} 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {Z}}
          {𝒲ᵂ.id 𝒲ᵂ.∘ 𝒲ᵂ.id {X} 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {Y ⊗ᴵ Z} 𝒲ᵂ.∘ 𝒲ᵂ.associator.from}
          (refl⟩∘⟨ ((drop (𝒲ᵂ.⊗.identity {X ⊗ᴵ Y , Z}) ⟩∘⟨refl) ○ unmon {(X ⊗ᴵ Y) ⊗ᴵ Z} (α-relabelᵂ {X} {Y} {Z})
                    ○ ⟺ ((G.identityˡ ○ (𝒲ᵂ.⊗.identity {X , Y ⊗ᴵ Z} ⟩∘⟨refl) ○ G.identityˡ) ⟩∘⟨refl)))
    ; unitaryˡ = λ {X} →
        ≈-under-eᵂ {unitᴵ ⊗ᴵ X} {X} {⟦ P.unitorˡ.from ⟧ᵂ 𝒲ᵂ.∘ 𝒲ᵂ.id 𝒲ᵂ.∘ 𝒲ᵂ.id {unitᴵ} 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {X}}
          {𝒲ᵂ.unitorˡ.from}
          (refl⟩∘⟨ ((drop (𝒲ᵂ.⊗.identity {unitᴵ , X}) ⟩∘⟨refl) ○ unmon {unitᴵ ⊗ᴵ X} (λ-relabelᵂ {X})))
    ; unitaryʳ = λ {X} →
        ≈-under-eᵂ {X ⊗ᴵ unitᴵ} {X} {⟦ P.unitorʳ.from ⟧ᵂ 𝒲ᵂ.∘ 𝒲ᵂ.id 𝒲ᵂ.∘ 𝒲ᵂ.id {X} 𝒲ᵂ.⊗₁ 𝒲ᵂ.id {unitᴵ}}
          {𝒲ᵂ.unitorʳ.from}
          (refl⟩∘⟨ ((drop (𝒲ᵂ.⊗.identity {X , unitᴵ}) ⟩∘⟨refl) ○ unmon {X ⊗ᴵ unitᴵ} (ρ-relabelᵂ {X}))) } }
  where
  open G.HomReasoning
  ≈⇒∼ : {A B : Iface} {f g : A 𝒲ᵂ.⇒ B} → f 𝒲ᵂ.≈ g → f ≈ g
  ≈⇒∼ = Quotient.MonoidalCongruence.≈⇒∼ uKernelᵂ
  drop : ∀ {X Y : G.Obj} {L : X G.⇒ Y} {I : X G.⇒ X} → I G.≈ G.id → L G.∘ G.id G.∘ I G.≈ L
  drop e = (refl⟩∘⟨ (G.identityˡ ○ e)) ○ G.identityʳ
  unmon : ∀ {A} {Y : G.Obj} {L M : Uᵂ A G.⇒ Y} → L G.≈ M G.∘ proj₁ (eᵂ {A})
        → L G.∘ proj₁ (eᵂ {A}) G.≈ M G.∘ proj₁ (eᵂ {A})
  unmon {A} r = (r ⟩∘⟨refl) ○ G.assoc ○ (refl⟩∘⟨ eᵂ-idem {A})

------------------------------------------------------------------------
-- The morphism of setups, over the density of SSP games

module GamesDense (games-dense : ∀ {A} {D D′ : Protocol A Ωᴵ} → D SSP.≋ D′
                               → Observable._≋_ (Evaluation.observable evaluationᵂ) ⟦ D ⟧ᵂ ⟦ D′ ⟧ᵂ) where

  νᵂ : PresheafMorphism (StrongMonoidalFunctor.F Fᵂ) SSP.ℰᵖ ℰ[wb]
  νᵂ = record { ν = ntHelper record
    { η = λ _ → record { to = ⟦_⟧ᵂ ; cong = games-dense }
    ; commute = λ {_} {Y} f {D} → Observable.≈⇒≋ (Evaluation.observable evaluationᵂ) {A = Y}
        {t = ⟦ D ∘ᵖ f ⟧ᵂ} {u = ⟦ D ⟧ᵂ 𝒲ᵂ.∘ ⟦ f ⟧ᵂ} (⟦⟧ᵂ-∘ D f) } }

  SSP→PM[wb] : UCSetupMorphism SSP.StdSetup StdSetup
  SSP→PM[wb] = StdUCMorphism Protᴹ PM[wb]ᴹ SSP.ℰᵖ ℰ[wb] Fᵂ νᵂ

  -- `Fᵂ` is the identity on objects, so `≈ℰ` crossing suffices
  -- (`Standard2.Morphism.surjective⇒preserves-≈ᵁ`).
  ≤UC-transfer : Transfer.Preserves-≈ℰ SSP→PM[wb] → Transfer.Preserves-≤UC SSP→PM[wb]
  ≤UC-transfer pres = Transfer.transfer⁺ SSP→PM[wb] (surjective⇒preserves-≈ᵁ Protᴹ PM[wb]ᴹ SSP.ℰᵖ ℰ[wb] Fᵂ νᵂ
    (λ A → A , Mor.≅.refl (MonoidalCategory.U PM[wb]ᴹ)) pres)
