{-# OPTIONS --safe #-}

module CategoricalCrypto.Machine.Relational.Monoidal where

open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor.Bifunctor
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Channel.Core
import CategoricalCrypto.Machine.Core as M
import CategoricalCrypto.Machine.Forwarder as Fwd
import CategoricalCrypto.Machine.Iso as Iso
import CategoricalCrypto.Machine.Monoidal.Associator as Assoc
import CategoricalCrypto.Machine.Monoidal.Braiding as Braid
import CategoricalCrypto.Machine.Monoidal.Coherence as Coh
import CategoricalCrypto.Machine.Monoidal.Interchange as Inter
import CategoricalCrypto.Machine.Monoidal.Unitors as Unit
import CategoricalCrypto.Machine.Reindex.Collapse as Collapse
import CategoricalCrypto.Machine.Reindex.PairAssoc as PairAssoc
import CategoricalCrypto.Machine.Reindex.Post as Post
import CategoricalCrypto.Machine.Reindex.Swap as Swap
import CategoricalCrypto.Machine.Reindex.Unit as PairUnit
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Category
open import CategoricalCrypto.Machine.Relational.Isomorphism
open import CategoricalCrypto.Machine.Relational.Wiring

private variable A B C D E F : Channel

λ⇒ : Initialized (I ⊗₀ A) A
λ⇒ = all-states M.λ⇒

λ⇐ : Initialized A (I ⊗₀ A)
λ⇐ = all-states M.λ⇐

ρ⇒ : Initialized (A ⊗₀ I) A
ρ⇒ = all-states M.ρ⇒

ρ⇐ : Initialized A (A ⊗₀ I)
ρ⇐ = all-states M.ρ⇐

α⇒ : Initialized ((A ⊗₀ B) ⊗₀ C) (A ⊗₀ (B ⊗₀ C))
α⇒ = all-states M.⊗-assoc

α⇐ : Initialized (A ⊗₀ (B ⊗₀ C)) ((A ⊗₀ B) ⊗₀ C)
α⇐ = all-states M.⊗-assoc⃖

σ : Initialized (A ⊗₀ B) (B ⊗₀ A)
σ = all-states M.⊗-symₘ

opaque
  unfolding Inter.⊗₁-interchange

  interchange : (f : Initialized A B) (g : Initialized B C)
              → (h : Initialized D E) (k : Initialized E F)
              → ((g ∘ f) ⊗₁ (k ∘ h)) ≈ᴿ ((g ⊗₁ k) ∘ (f ⊗₁ h))
  interchange f g h k = lift-iso (Inter.⊗₁-interchange (machine f) (machine g) (machine h) (machine k))
    (λ { ((p , q) , (r , s)) → (p , r) , (q , s) })
    (λ { ((p , r) , (q , s)) → (p , q) , (r , s) })

⊗-bifunctor : Bifunctor 𝓡 𝓡 𝓡
⊗-bifunctor = record
  { F₀ = λ (A , B) → A ⊗₀ B
  ; F₁ = λ (f , g) → f ⊗₁ g
  ; identity = total-iso Fwd.⊗₁-id (λ _ → refl , refl) (λ _ → refl)
  ; homomorphism = λ { {f = f , h} {g , k} → interchange f g h k }
  ; F-resp-≈ = λ (φ , ψ) → ⊗-cong φ ψ
  }

open Mor 𝓡 using (_≅_)
open MR 𝓡 using (conjugate-to)

unitorˡ-iso : (I ⊗₀ A) ≅ A
unitorˡ-iso = record
  { from = λ⇒ ; to = λ⇐ ; iso = record
    { isoˡ = total-iso Coh.λ-isoˡ (λ _ → tt , tt) (λ _ → refl)
    ; isoʳ = total-iso Coh.λ-isoʳ (λ _ → tt , tt) (λ _ → refl) } }

unitorʳ-iso : (A ⊗₀ I) ≅ A
unitorʳ-iso = record
  { from = ρ⇒ ; to = ρ⇐ ; iso = record
    { isoˡ = total-iso Coh.ρ-isoˡ (λ _ → tt , tt) (λ _ → refl)
    ; isoʳ = total-iso Coh.ρ-isoʳ (λ _ → tt , tt) (λ _ → refl) } }

associator-iso : ((A ⊗₀ B) ⊗₀ C) ≅ (A ⊗₀ (B ⊗₀ C))
associator-iso = record
  { from = α⇒ ; to = α⇐ ; iso = record
    { isoˡ = total-iso Coh.α-isoˡ (λ _ → tt , tt) (λ _ → refl)
    ; isoʳ = total-iso Coh.α-isoʳ (λ _ → tt , tt) (λ _ → refl) } }

opaque
  unfolding Unit.λ⇒-natural Unit.ρ⇒-natural Assoc.⊗-assoc⃖-natural Braid.σ-natural
            Collapse.∘-collapse-cod Collapse.∘-collapse-dom
            Post.∘-identityˡ-Post Post.∘-identityʳ-Post
            PairUnit.Pair-unitˡ PairUnit.Pair-unitʳ PairAssoc.Pair-asc3 Swap.Pair-swap

  λ-natural : (f : Initialized A B) → (λ⇒ ∘ (id ⊗₁ f)) ≈ᴿ (f ∘ λ⇒)
  λ-natural f = lift-iso (Unit.λ⇒-natural (machine f))
    (λ { ((_ , p) , _) → tt , p }) (λ { (_ , p) → (refl , p) , tt })

  ρ-natural : (f : Initialized A B) → (ρ⇒ ∘ (f ⊗₁ id)) ≈ᴿ (f ∘ ρ⇒)
  ρ-natural f = lift-iso (Unit.ρ⇒-natural (machine f))
    (λ { ((p , _) , _) → tt , p }) (λ { (_ , p) → (p , refl) , tt })

  α⁻¹-natural : (f : Initialized A B) (g : Initialized C D) (h : Initialized E F)
              → (((f ⊗₁ g) ⊗₁ h) ∘ α⇐) ≈ᴿ (α⇐ ∘ (f ⊗₁ (g ⊗₁ h)))
  α⁻¹-natural f g h = lift-iso (Assoc.⊗-assoc⃖-natural (machine f) (machine g) (machine h))
    (λ { (_ , ((p , q) , r)) → (p , q , r) , tt })
    (λ { ((p , q , r) , _) → tt , (p , q) , r })

  σ-natural : (f : Initialized A B) (g : Initialized C D)
            → (σ ∘ (f ⊗₁ g)) ≈ᴿ ((g ⊗₁ f) ∘ σ)
  σ-natural f g = lift-iso (Braid.σ-natural (machine f) (machine g))
    (λ { ((p , q) , _) → tt , q , p }) (λ { (_ , q , p) → (p , q) , tt })

monoidal : Monoidal 𝓡
monoidal = monoidalHelper 𝓡 record
  { ⊗ = ⊗-bifunctor ; unit = I
  ; unitorˡ = unitorˡ-iso ; unitorʳ = unitorʳ-iso ; associator = associator-iso
  ; unitorˡ-commute = λ {_} {_} {f} → λ-natural f
  ; unitorʳ-commute = λ {_} {_} {f} → ρ-natural f
  ; assoc-commute = λ {_} {_} {f} {_} {_} {g} {_} {_} {h} →
      ≈ᴿ-sym (conjugate-to associator-iso associator-iso (≈ᴿ-sym (α⁻¹-natural f g h)))
  ; triangle = total-iso Coh.triangle (λ _ → tt , refl , tt) (λ _ → tt , refl)
  ; pentagon = total-iso Coh.pentagon
      (λ _ → ((tt , refl) , tt) , refl , tt) (λ _ → tt , tt)
  }

σ-σ : (σ {A = B} {B = A} ∘ σ {A = A} {B = B}) ≈ᴿ id
σ-σ = total-iso Coh.σ-σ (λ _ → tt , tt) (λ _ → refl)

symmetric : Symmetric monoidal
symmetric = symmetricHelper monoidal record
  { braiding = niHelper record
    { η = λ _ → σ ; η⁻¹ = λ _ → σ
    ; commute = λ (f , g) → σ-natural f g
    ; iso = λ _ → record { isoˡ = σ-σ ; isoʳ = σ-σ } }
  ; commutative = σ-σ
  ; hexagon = total-iso Coh.hexagon
      (λ _ → ((tt , refl) , tt) , refl , tt) (λ _ → (tt , tt) , tt)
  }
