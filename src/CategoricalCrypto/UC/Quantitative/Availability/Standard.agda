{-# OPTIONS --safe --without-K #-}

import Categories.Category.Construction.Core as Core
open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
import Categories.Category.Monoidal.Braided.Properties as Braided
import Categories.Category.Monoidal.Interchange.Braided as Interchange
import Categories.Category.Monoidal.Interchange.Symmetric as SymmetricInterchange
import Categories.Category.Monoidal.Properties as MonoidalProperties
import Categories.Category.Monoidal.Reasoning as MonoidalReasoning
import Categories.Category.Monoidal.Utilities as Utilities
open import Categories.Functor.Presheaf using (Presheaf)
import Categories.Functor.Monoidal.CurriedTensor as Tensor
import Categories.Monad.Graded.FromMonad as FromMonad
import Categories.Morphism.Reasoning as MorphismReasoning
open import Level using (Level; _⊔_)

open import CategoricalCrypto.Approx.Error using (OrderedErrorAlgebra)

module CategoricalCrypto.UC.Quantitative.Availability.Standard
  {es ℓe : Level} (E : OrderedErrorAlgebra es ℓe) where

open OrderedErrorAlgebra E
open import CategoricalCrypto.Approx.Space E using (Approx)
open import CategoricalCrypto.UC.Quantitative E
import CategoricalCrypto.UC.Quantitative.Availability.Composition E as Composition

module Structural {o ℓ e : Level}
  (M : MonoidalCategory o ℓ e) (S : Symmetric (MonoidalCategory.monoidal M)) where

  private module M = MonoidalCategory M
  open M
  open MonoidalReasoning monoidal
  open Utilities.Shorthands monoidal
  open Utilities monoidal using (_⊗ᵢ_)
  open Core.Shorthands U using (idᵢ)
  open MorphismReasoning U
  open MonoidalProperties monoidal using (coherence₃)
  private module I = Interchange (Symmetric.braided S)
  private module IS = SymmetricInterchange S
  private module T = FromMonad (Tensor.curriedTensor M)

  private variable
    A B C D X Y P′ R : Obj

  middle4 : ((X ⊗₀ B) ⊗₀ (P′ ⊗₀ D)) ⇒ ((X ⊗₀ P′) ⊗₀ (B ⊗₀ D))
  middle4 = I.swapInner.from

  middle4-sub : (s : Y ⇒ X) (t : R ⇒ P′)
    → ((s ⊗₁ t) ⊗₁ id {B ⊗₀ D}) ∘ middle4
      ≈ middle4 ∘ ((s ⊗₁ id) ⊗₁ (t ⊗₁ id))
  middle4-sub s t = (refl⟩⊗⟨ ⟺ ⊗.identity) ⟩∘⟨refl ○ ⟺ I.swapInner-natural

  unit-middle4 : λ⇒ {B ⊗₀ D} ∘ ((λ⇒ {unit} ⊗₁ id) ∘ middle4)
    ≈ λ⇒ {B} ⊗₁ λ⇒ {D}
  unit-middle4 = sym-assoc
    ○ (refl⟩∘⟨ IS.swapInner-selfInverse)
    ○ ⟺ (switch-fromtoʳ I.swapInner
      (switch-tofromʳ (unitorˡ ⊗ᵢ idᵢ) (assoc ○ I.swapInner-unitˡ)))

  unit-close-compose : (f : A ⇒ unit ⊗₀ B) (u : B ⇒ unit ⊗₀ C)
    → λ⇒ ∘ ((λ⇒ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ u)) ∘ f))
      ≈ (λ⇒ ∘ u) ∘ (λ⇒ ∘ f)
  unit-close-compose f u = begin
    λ⇒ ∘ ((λ⇒ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ u)) ∘ f))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ assoc) ⟩
    λ⇒ ∘ ((λ⇒ ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ u) ∘ f)))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    λ⇒ ∘ (((λ⇒ ⊗₁ id) ∘ α⇐) ∘ ((id ⊗₁ u) ∘ f))
      ≈⟨ refl⟩∘⟨ ((((coherence₃ ⟩⊗⟨refl) ⟩∘⟨refl)
        ○ ⟺ (switch-fromtoʳ associator triangle)) ⟩∘⟨refl) ⟩
    λ⇒ ∘ ((id ⊗₁ λ⇒) ∘ ((id ⊗₁ u) ∘ f))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    λ⇒ ∘ (((id ⊗₁ λ⇒) ∘ (id ⊗₁ u)) ∘ f)
      ≈⟨ refl⟩∘⟨ ((⟺ ⊗.homomorphism ○ (identityˡ ⟩⊗⟨refl)) ⟩∘⟨refl) ⟩
    λ⇒ ∘ ((id ⊗₁ (λ⇒ ∘ u)) ∘ f)
      ≈⟨ sym-assoc ⟩
    (λ⇒ ∘ (id ⊗₁ (λ⇒ ∘ u))) ∘ f
      ≈⟨ unitorˡ-commute-from {f = λ⇒ ∘ u} ⟩∘⟨refl ⟩
    ((λ⇒ ∘ u) ∘ λ⇒) ∘ f
      ≈⟨ assoc ⟩
    (λ⇒ ∘ u) ∘ (λ⇒ ∘ f) ∎

  close-compose : (a : X ⇒ unit) (c : P′ ⇒ unit)
    (f : A ⇒ X ⊗₀ B) (u : B ⇒ P′ ⊗₀ C)
    → ((λ⇒ ∘ (a ⊗₁ c)) ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ u)) ∘ f)
      ≈ (λ⇒ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ ((c ⊗₁ id) ∘ u))) ∘ ((a ⊗₁ id) ∘ f))
  close-compose a c f u = begin
    T.sub (λ⇒ ∘ (a ⊗₁ c)) ∘ (T.ext _ u ∘ f)
      ≈⟨ (T.sub-homomorphism ⟩∘⟨refl) ○ assoc ⟩
    T.sub λ⇒ ∘ T.sub (a ⊗₁ c) ∘ T.ext _ u ∘ f
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    T.sub λ⇒ ∘ (T.sub (a ⊗₁ c) ∘ T.ext _ u) ∘ f
      ≈⟨ refl⟩∘⟨ (⟺ T.sub-commute) ⟩∘⟨refl ⟩
    T.sub λ⇒ ∘ (T.ext unit (T.sub c ∘ u) ∘ T.sub a) ∘ f
      ≈⟨ refl⟩∘⟨ assoc ⟩
    (λ⇒ ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ ((c ⊗₁ id) ∘ u))) ∘ ((a ⊗₁ id) ∘ f)) ∎

module Standard {o ℓ e c ℓb : Level}
  (M : MonoidalCategory o ℓ e) (S : Symmetric (MonoidalCategory.monoidal M))
  (Q : Presheaf (MonoidalCategory.U M) (Approx c (es ⊔ ℓe ⊔ ℓb))) where

  private module M = MonoidalCategory M
  open M
  open MonoidalReasoning monoidal
  open Utilities.Shorthands monoidal
  open MorphismReasoning U
  private module S = Symmetric S
  open Structural M S public
  open Braided.Shorthands S.braided

  QSetup : QUCSetup o ℓ e o ℓ e c ℓb
  QSetup = record { 𝒞 = U ; ℐ = M ; ℳ = Tensor.curriedTensor M ; Q = Q }

  private
    module Quant = QuantitativeUC QSetup
    module P = Composition.Parallel QSetup monoidal
  open Quant using (Env; module Env; pull; pull-cong; pull-resp-≈; pull-∘;
    pull-mono; _≈[_]_; ≈-sym; ≈-resp₀; _≈ᵁ[_]_; prefix; run)

  private variable
    A B C D X Y P′ R : Obj
    ε : Error

  -- The all-ancilla quantifier lets a tensor factor become part of a context.
  -- This is not a tensor nonexpansiveness assumption on the test presheaf.
  Ambient : (A ⇒ B) → Error → (A ⇒ B) → Set (o ⊔ c ⊔ es ⊔ ℓe ⊔ ℓb)
  Ambient {B = B} f ε g = (W : Obj) (q : Env (W ⊗₀ B))
    → pull (id ⊗₁ f) q ≈[ ε ] pull (id ⊗₁ g) q

  private
    pull-split : (W : Obj) (k : B ⇒ C) (f : A ⇒ B) (q : Env (W ⊗₀ C))
      → pull (id {W} ⊗₁ (k ∘ f)) q
        ≈[ ε₀ ] pull (id ⊗₁ f) (pull (id ⊗₁ k) q)
    pull-split W k f q = Env.trans (pull-resp-≈ split₂ˡ q) (pull-∘ _ _ q)

  ambient-resp : {f f′ g g′ : A ⇒ B} → f ≈ f′ → g ≈ g′
    → Ambient f ε g → Ambient f′ ε g′
  ambient-resp ef eg h W q = ≈-resp₀
    (pull-resp-≈ (refl⟩⊗⟨ ⟺ ef) q) (pull-resp-≈ (refl⟩⊗⟨ eg) q) (h W q)

  ambient-pre : {f g : A ⇒ B} (k : C ⇒ A)
    → Ambient f ε g → Ambient (f ∘ k) ε (g ∘ k)
  ambient-pre {f = f} {g} k h W q = ≈-resp₀
    (pull-split W f k q) (≈-sym (pull-split W g k q))
    (pull-mono (id ⊗₁ k) (h W q))

  ambient-post : {f g : A ⇒ B} (k : B ⇒ C)
    → Ambient f ε g → Ambient (k ∘ f) ε (k ∘ g)
  ambient-post {f = f} {g} k h W q = ≈-resp₀
    (pull-split W k f q) (≈-sym (pull-split W k g q)) (h W (pull (id ⊗₁ k) q))

  ambient-pad : {f g : A ⇒ B} → Ambient f ε g
    → Ambient (id {C} ⊗₁ f) ε (id ⊗₁ g)
  ambient-pad {A = A} {B = B} {C = C} {f = f} {g} h W q = ≈-resp₀ (cut f) (≈-sym (cut g))
    (pull-mono α⇐ (h (W ⊗₀ C) (pull α⇒ q)))
    where
    pad : (k : A ⇒ B) → id {W} ⊗₁ (id {C} ⊗₁ k)
      ≈ (α⇒ ∘ (id {W ⊗₀ C} ⊗₁ k)) ∘ α⇐
    pad k = begin
      id ⊗₁ (id ⊗₁ k)
        ≈˘⟨ identityʳ ⟩
      (id ⊗₁ (id ⊗₁ k)) ∘ id
        ≈˘⟨ refl⟩∘⟨ associator.isoʳ ⟩
      (id ⊗₁ (id ⊗₁ k)) ∘ (α⇒ ∘ α⇐)
        ≈⟨ sym-assoc ⟩
      ((id ⊗₁ (id ⊗₁ k)) ∘ α⇒) ∘ α⇐
        ≈˘⟨ assoc-commute-from ⟩∘⟨refl ⟩
      (α⇒ ∘ ((id ⊗₁ id) ⊗₁ k)) ∘ α⇐
        ≈⟨ (refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl)) ⟩∘⟨refl ⟩
      (α⇒ ∘ (id ⊗₁ k)) ∘ α⇐ ∎

    cut : (k : A ⇒ B) → pull (id ⊗₁ (id ⊗₁ k)) q
      ≈[ ε₀ ] pull α⇐ (pull (id ⊗₁ k) (pull α⇒ q))
    cut k = Env.trans (pull-resp-≈ (pad k) q)
      (Env.trans (pull-∘ _ _ q) (pull-cong α⇐ (pull-∘ α⇒ (id ⊗₁ k) q)))

  ambient-padʳ : {f g : A ⇒ B} → Ambient f ε g
    → Ambient (f ⊗₁ id {C}) ε (g ⊗₁ id)
  ambient-padʳ {A = A} {B = B} {C = C} {f = f} {g} h =
    ambient-resp (⟺ (swap f)) (⟺ (swap g))
      (ambient-post σ⇒ (ambient-pre σ⇒ (ambient-pad h)))
    where
    swap : (k : A ⇒ B) → k ⊗₁ id {C} ≈ σ⇒ ∘ ((id {C} ⊗₁ k) ∘ σ⇒)
    swap k = ⟺ (pullˡ (S.braiding.⇒.commute _) ○ cancelʳ S.commutative)

  ambient-tensor-left : {f g : A ⇒ B} (u : C ⇒ D)
    → Ambient f ε g → Ambient (f ⊗₁ u) ε (g ⊗₁ u)
  ambient-tensor-left u h = ambient-resp (⟺ serialize₂₁) (⟺ serialize₂₁)
    (ambient-post (id ⊗₁ u) (ambient-padʳ h))

  ambient-tensor-right : (f : A ⇒ B) {u v : C ⇒ D}
    → Ambient u ε v → Ambient (f ⊗₁ u) ε (f ⊗₁ v)
  ambient-tensor-right f h = ambient-resp (⟺ serialize₁₂) (⟺ serialize₁₂)
    (ambient-post (f ⊗₁ id) (ambient-pad h))

  ctx⇒ambient : {f g : A ⇒ X ⊗₀ B} → f ≈ᵁ[ ε ] g → Ambient f ε g
  ctx⇒ambient {A = A} {X = X} {B = B} {f = f} {g} h W q = ≈-resp₀ (cut f) (≈-sym (cut g))
    (h W (pull α⇒ q))
    where
    cut : (k : A ⇒ X ⊗₀ B) → pull (id {W} ⊗₁ k) q
      ≈[ ε₀ ] run W k (pull α⇒ q)
    cut k = Env.trans
      (pull-resp-≈ (⟺ (cancelˡ associator.isoʳ)) q)
      (pull-∘ α⇒ (prefix W k) q)

  ambient⇒ctx : {f g : A ⇒ X ⊗₀ B} → Ambient f ε g → f ≈ᵁ[ ε ] g
  ambient⇒ctx {A = A} {X = X} {B = B} {f = f} {g} h W q =
    ≈-resp₀ (cut f) (≈-sym (cut g)) (h W (pull α⇐ q))
    where
    cut : (k : A ⇒ X ⊗₀ B) → run W k q ≈[ ε₀ ] pull (id {W} ⊗₁ k) (pull α⇐ q)
    cut k = pull-∘ α⇐ (id ⊗₁ k) q

  pairing : P.Pairing
  pairing = record
    { χ = middle4
    ; χ-sub = middle4-sub
    ; action-left = λ u h → ambient⇒ctx
        (ambient-post middle4 (ambient-tensor-left u (ctx⇒ambient h)))
    ; action-right = λ f h → ambient⇒ctx
        (ambient-post middle4 (ambient-tensor-right f (ctx⇒ambient h)))
    }

  module Laws = P.Laws pairing
