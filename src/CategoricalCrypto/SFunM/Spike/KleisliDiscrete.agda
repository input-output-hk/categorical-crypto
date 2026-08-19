{-# OPTIONS --safe --without-K #-}

-- SPIKE: the `𝒱` the general Mealy layer runs on — the Kleisli category of a
-- `Setoids` monad at the *discrete* objects, i.e. TYPES and maps `A → M B`,
-- with the cartesian tensor.  `Discrete.Kleisliᴹ` is the same category built
-- upstream; this presentation is spelled out with `_>>=_` instead of `μ ∘ F₁`
-- so that it computes on closed inputs, and it carries the monoidal structure.
--
-- Only two laws use the monad's commutativity: the tensor's `homomorphism`
-- (interchange) and the braiding's `commute`.  Everything else — both unitors,
-- the associator, all six iso laws, triangle, pentagon, hexagon — is a
-- rearrangement of the triple's own laws.

open import Categories.Category.Core using (Category)
open import Categories.Category.Helper using (categoryHelper)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper; SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric; symmetricHelper)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Monad.Construction.Kleisli using (KleisliTriple)
import Categories.Monad.Setoids.Discrete as Discrete
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Product using (_×_; _,_; proj₁; proj₂; map; swap; assocʳ′; assocˡ′)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function.Base using (id; _∘_)
open import Level using (suc)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

module CategoricalCrypto.SFunM.Spike.KleisliDiscrete {ℓ}
  (K : KleisliTriple (Setoids ℓ ℓ)) (K-Comm : Discrete.Commutative K) where

open Discrete K
open Commutative K-Comm
open ≈ᴹ-Reasoning

private variable A A′ B B′ C C′ D E : Set ℓ

------------------------------------------------------------------------
-- The category

infix 4 _≈ᵏ_

_≈ᵏ_ : (A → M B) → (A → M B) → Set ℓ
f ≈ᵏ g = ∀ a → f a ≈ᴹ g a

≈ᵏ-isEquivalence : IsEquivalence (_≈ᵏ_ {A} {B})
≈ᵏ-isEquivalence = record
  { refl  = λ _ → ≈ᴹ.refl
  ; sym   = λ f≈g a → ≈ᴹ.sym (f≈g a)
  ; trans = λ f≈g g≈h a → ≈ᴹ.trans (f≈g a) (g≈h a)
  }

Klᴹ : Category (suc ℓ) ℓ ℓ
Klᴹ = categoryHelper record
  { Obj       = Set ℓ
  ; _⇒_       = λ A B → A → M B
  ; _≈_       = _≈ᵏ_
  ; id        = return
  ; _∘_       = _<=<_
  ; assoc     = λ _ → ≈ᴹ.sym (>>=-assoc-≈ _)
  ; identityˡ = λ _ → >>=-identityʳ-≈ _
  ; identityʳ = λ _ → >>=-identityˡ-≈
  ; equiv     = ≈ᵏ-isEquivalence
  ; ∘-resp-≈  = λ f≈h g≈i a → >>=-cong (g≈i a) f≈h
  }

private module Kl = Category Klᴹ

open Kl.HomReasoning using (_○_; ⟺; _⟩∘⟨_; refl⟩∘⟨_)

------------------------------------------------------------------------
-- Pure morphisms

-- Every structural morphism of the cartesian tensor is a function.
pureᵏ : (A → B) → (A → M B)
pureᵏ = return ∘_

pureᵏ-cong : {h k : A → B} → (∀ a → h a ≡ k a) → pureᵏ h ≈ᵏ pureᵏ k
pureᵏ-cong h≡k a = ≈ᴹ.reflexive (cong return (h≡k a))

pureᵏ-∘ : (h : B → C) (k : A → B) → (pureᵏ h <=< pureᵏ k) ≈ᵏ pureᵏ (h ∘ k)
pureᵏ-∘ _ _ _ = >>=-identityˡ-≈

------------------------------------------------------------------------
-- The tensor

infixr 10 _⊗ᵏ_

-- Projections rather than a pattern-matching lambda: `_⊗ᵏ_` then reduces on an
-- argument that is not yet a literal pair, which is what lets the Mealy layer's
-- structural shuffles compute.
_⊗ᵏ_ : (A → M B) → (C → M D) → A × C → M (B × D)
(f ⊗ᵏ g) p = f (proj₁ p) >>= λ b → g (proj₂ p) >>= λ d → return (b , d)

-- The workhorse behind every law below.
⊗ᵏ-expand : (f : A → M B) (g : C → M D) (h : B × D → M E) (p : A × C)
          → ((f ⊗ᵏ g) p >>= h) ≈ᴹ (f (proj₁ p) >>= λ b → g (proj₂ p) >>= λ d → h (b , d))
⊗ᵏ-expand f g h p =
  ≈ᴹ.trans (>>=-assoc-≈ (f (proj₁ p)))
           (>>=-cong-f λ _ → ≈ᴹ.trans (>>=-assoc-≈ (g (proj₂ p)))
                                      (>>=-cong-f λ _ → >>=-identityˡ-≈))

pureᵏ-⊗ : (h : A → B) (k : C → D) → (pureᵏ h ⊗ᵏ pureᵏ k) ≈ᵏ pureᵏ (map h k)
pureᵏ-⊗ _ _ (_ , _) = ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈

⊗ᵏ-identity : (p : A × B) → (return ⊗ᵏ return) p ≈ᴹ return p
⊗ᵏ-identity (_ , _) = ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈

-- The interchange law is the one place the tensor needs `>>=-comm-y`: the two
-- factors' effects happen in opposite orders on the two sides.
⊗ᵏ-homomorphism : {f : A → M B} {g : B → M C} {f′ : A′ → M B′} {g′ : B′ → M C′}
                → ((g <=< f) ⊗ᵏ (g′ <=< f′)) ≈ᵏ ((g ⊗ᵏ g′) <=< (f ⊗ᵏ f′))
⊗ᵏ-homomorphism {f = f} {g} {f′} {g′} (a , c) = begin
  ((f a >>= g) >>= λ b → (f′ c >>= g′) >>= λ d → return (b , d))
    ≈⟨ >>=-assoc-≈ (f a) ⟩
  (f a >>= λ x → g x >>= λ b → (f′ c >>= g′) >>= λ d → return (b , d))
    ≈⟨ >>=-cong-f (λ _ → >>=-cong-f λ _ → >>=-assoc-≈ (f′ c)) ⟩
  (f a >>= λ x → g x >>= λ b → f′ c >>= λ y → g′ y >>= λ d → return (b , d))
    ≈⟨ >>=-cong-f (λ _ → >>=-comm-y _) ⟩
  (f a >>= λ x → f′ c >>= λ y → g x >>= λ b → g′ y >>= λ d → return (b , d))
    ≈˘⟨ ⊗ᵏ-expand f f′ (g ⊗ᵏ g′) (a , c) ⟩
  ((f ⊗ᵏ f′) (a , c) >>= (g ⊗ᵏ g′)) ∎

⊗ᵏ-resp-≈ : {f h : A → M B} {g i : C → M D} → f ≈ᵏ h → g ≈ᵏ i → (f ⊗ᵏ g) ≈ᵏ (h ⊗ᵏ i)
⊗ᵏ-resp-≈ f≈h g≈i p = >>=-cong (f≈h (proj₁ p)) λ _ → >>=-cong (g≈i (proj₂ p)) λ _ → ≈ᴹ.refl

⊗ᵏ-bifunctor : Bifunctor Klᴹ Klᴹ Klᴹ
⊗ᵏ-bifunctor = record
  { F₀           = λ (A , B) → A × B
  ; F₁           = λ (f , g) → f ⊗ᵏ g
  ; identity     = ⊗ᵏ-identity
  ; homomorphism = ⊗ᵏ-homomorphism
  ; F-resp-≈     = λ (f≈h , g≈i) → ⊗ᵏ-resp-≈ f≈h g≈i
  }

------------------------------------------------------------------------
-- The structural morphisms

⊤ᵏ : Set ℓ
⊤ᵏ = ⊤

λ⇒ᵏ : ⊤ᵏ × A → M A
λ⇒ᵏ = pureᵏ proj₂

λ⇐ᵏ : A → M (⊤ᵏ × A)
λ⇐ᵏ = pureᵏ (tt ,_)

ρ⇒ᵏ : A × ⊤ᵏ → M A
ρ⇒ᵏ = pureᵏ proj₁

ρ⇐ᵏ : A → M (A × ⊤ᵏ)
ρ⇐ᵏ = pureᵏ (_, tt)

α⇒ᵏ : (A × B) × C → M (A × B × C)
α⇒ᵏ = pureᵏ assocʳ′

α⇐ᵏ : A × B × C → M ((A × B) × C)
α⇐ᵏ = pureᵏ assocˡ′

σᵏ : A × B → M (B × A)
σᵏ = pureᵏ swap

λ-isoˡ : (λ⇐ᵏ <=< λ⇒ᵏ {A}) ≈ᵏ return
λ-isoˡ _ = >>=-identityˡ-≈

λ-isoʳ : (λ⇒ᵏ <=< λ⇐ᵏ {A}) ≈ᵏ return
λ-isoʳ _ = >>=-identityˡ-≈

ρ-isoˡ : (ρ⇐ᵏ <=< ρ⇒ᵏ {A}) ≈ᵏ return
ρ-isoˡ _ = >>=-identityˡ-≈

ρ-isoʳ : (ρ⇒ᵏ <=< ρ⇐ᵏ {A}) ≈ᵏ return
ρ-isoʳ _ = >>=-identityˡ-≈

α-isoˡ : (α⇐ᵏ <=< α⇒ᵏ {A} {B} {C}) ≈ᵏ return
α-isoˡ ((_ , _) , _) = >>=-identityˡ-≈

α-isoʳ : (α⇒ᵏ <=< α⇐ᵏ {A} {B} {C}) ≈ᵏ return
α-isoʳ (_ , _ , _) = >>=-identityˡ-≈

σ-involutiveᵏ : (σᵏ <=< σᵏ {A} {B}) ≈ᵏ return
σ-involutiveᵏ (_ , _) = >>=-identityˡ-≈

------------------------------------------------------------------------
-- Naturality

unitorˡ-commuteᵏ : {f : A → M B} → (λ⇒ᵏ <=< (return ⊗ᵏ f)) ≈ᵏ (f <=< λ⇒ᵏ)
unitorˡ-commuteᵏ {f = f} (t , a) = begin
  ((return ⊗ᵏ f) (t , a) >>= λ⇒ᵏ)
    ≈⟨ ⊗ᵏ-expand return f λ⇒ᵏ (t , a) ⟩
  (return t >>= λ _ → f a >>= λ b → return b)
    ≈⟨ >>=-identityˡ-≈ ⟩
  (f a >>= return)
    ≈⟨ >>=-identityʳ-≈ (f a) ⟩
  f a
    ≈˘⟨ >>=-identityˡ-≈ ⟩
  (return a >>= f) ∎

unitorʳ-commuteᵏ : {f : A → M B} → (ρ⇒ᵏ <=< (f ⊗ᵏ return)) ≈ᵏ (f <=< ρ⇒ᵏ)
unitorʳ-commuteᵏ {f = f} (a , t) = begin
  ((f ⊗ᵏ return) (a , t) >>= ρ⇒ᵏ)
    ≈⟨ ⊗ᵏ-expand f return ρ⇒ᵏ (a , t) ⟩
  (f a >>= λ b → return t >>= λ _ → return b)
    ≈⟨ >>=-cong-f (λ _ → >>=-identityˡ-≈) ⟩
  (f a >>= return)
    ≈⟨ >>=-identityʳ-≈ (f a) ⟩
  f a
    ≈˘⟨ >>=-identityˡ-≈ ⟩
  (return a >>= f) ∎

assoc-commuteᵏ : {f : A → M A′} {g : B → M B′} {h : C → M C′}
               → (α⇒ᵏ <=< ((f ⊗ᵏ g) ⊗ᵏ h)) ≈ᵏ ((f ⊗ᵏ (g ⊗ᵏ h)) <=< α⇒ᵏ)
assoc-commuteᵏ {f = f} {g} {h} ((a , b) , c) = begin
  (((f ⊗ᵏ g) ⊗ᵏ h) ((a , b) , c) >>= α⇒ᵏ)
    ≈⟨ ⊗ᵏ-expand (f ⊗ᵏ g) h α⇒ᵏ ((a , b) , c) ⟩
  ((f ⊗ᵏ g) (a , b) >>= λ p → h c >>= λ z → α⇒ᵏ (p , z))
    ≈⟨ ⊗ᵏ-expand f g _ (a , b) ⟩
  (f a >>= λ x → g b >>= λ y → h c >>= λ z → return (x , y , z))
    ≈˘⟨ >>=-cong-f (λ _ → ⊗ᵏ-expand g h _ (b , c)) ⟩
  (f a >>= λ x → (g ⊗ᵏ h) (b , c) >>= λ q → return (x , q))
    ≈˘⟨ >>=-identityˡ-≈ ⟩
  (α⇒ᵏ ((a , b) , c) >>= (f ⊗ᵏ (g ⊗ᵏ h))) ∎

-- The braiding is the second and last place `>>=-comm-y` is needed.
braiding-commuteᵏ : {f : A → M A′} {g : B → M B′} → (σᵏ <=< (f ⊗ᵏ g)) ≈ᵏ ((g ⊗ᵏ f) <=< σᵏ)
braiding-commuteᵏ {f = f} {g} (a , b) = begin
  ((f ⊗ᵏ g) (a , b) >>= σᵏ)
    ≈⟨ ⊗ᵏ-expand f g σᵏ (a , b) ⟩
  (f a >>= λ x → g b >>= λ y → return (y , x))
    ≈⟨ >>=-comm-y _ ⟩
  (g b >>= λ y → f a >>= λ x → return (y , x))
    ≈˘⟨ >>=-identityˡ-≈ ⟩
  (σᵏ (a , b) >>= (g ⊗ᵏ f)) ∎

------------------------------------------------------------------------
-- Coherence

triangleᵏ : ((return ⊗ᵏ λ⇒ᵏ {B}) <=< α⇒ᵏ {A} {⊤ᵏ}) ≈ᵏ (ρ⇒ᵏ ⊗ᵏ return)
triangleᵏ ((_ , _) , _) = >>=-identityˡ-≈

pentagonᵏ : ((return ⊗ᵏ α⇒ᵏ {B} {C} {D}) <=< (α⇒ᵏ <=< (α⇒ᵏ {A} ⊗ᵏ return)))
          ≈ᵏ (α⇒ᵏ <=< α⇒ᵏ)
pentagonᵏ = pureᵏ-⊗ id assocʳ′ ⟩∘⟨ (refl⟩∘⟨ pureᵏ-⊗ assocʳ′ id)
          ○ refl⟩∘⟨ pureᵏ-∘ _ _
          ○ pureᵏ-∘ _ _
          ○ pureᵏ-cong (λ where (((_ , _) , _) , _) → refl)
          ○ ⟺ (pureᵏ-∘ _ _)

hexagonᵏ : ((return ⊗ᵏ σᵏ {A} {C}) <=< (α⇒ᵏ <=< (σᵏ {A} {B} ⊗ᵏ return)))
         ≈ᵏ (α⇒ᵏ <=< (σᵏ <=< α⇒ᵏ))
hexagonᵏ = pureᵏ-⊗ id swap ⟩∘⟨ (refl⟩∘⟨ pureᵏ-⊗ swap id)
         ○ refl⟩∘⟨ pureᵏ-∘ _ _
         ○ pureᵏ-∘ _ _
         ○ pureᵏ-cong (λ where ((_ , _) , _) → refl)
         ○ ⟺ (refl⟩∘⟨ pureᵏ-∘ _ _ ○ pureᵏ-∘ _ _)

------------------------------------------------------------------------
-- The bundles

Klᴹ-Monoidal : Monoidal Klᴹ
Klᴹ-Monoidal = monoidalHelper Klᴹ record
  { ⊗               = ⊗ᵏ-bifunctor
  ; unit            = ⊤ᵏ
  ; unitorˡ         = record { from = λ⇒ᵏ ; to = λ⇐ᵏ ; iso = record { isoˡ = λ-isoˡ ; isoʳ = λ-isoʳ } }
  ; unitorʳ         = record { from = ρ⇒ᵏ ; to = ρ⇐ᵏ ; iso = record { isoˡ = ρ-isoˡ ; isoʳ = ρ-isoʳ } }
  ; associator      = record { from = α⇒ᵏ ; to = α⇐ᵏ ; iso = record { isoˡ = α-isoˡ ; isoʳ = α-isoʳ } }
  ; unitorˡ-commute = unitorˡ-commuteᵏ
  ; unitorʳ-commute = unitorʳ-commuteᵏ
  ; assoc-commute   = assoc-commuteᵏ
  ; triangle        = triangleᵏ
  ; pentagon        = pentagonᵏ
  }

Klᴹ-Symmetric : Symmetric Klᴹ-Monoidal
Klᴹ-Symmetric = symmetricHelper Klᴹ-Monoidal record
  { braiding    = niHelper record
      { η       = λ _ → σᵏ
      ; η⁻¹     = λ _ → σᵏ
      ; commute = λ _ → braiding-commuteᵏ
      ; iso     = λ _ → record { isoˡ = σ-involutiveᵏ ; isoʳ = σ-involutiveᵏ }
      }
  ; commutative = σ-involutiveᵏ
  ; hexagon     = hexagonᵏ
  }

Klᴹ-SymmetricMonoidal : SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
Klᴹ-SymmetricMonoidal = record { U = Klᴹ ; monoidal = Klᴹ-Monoidal ; symmetric = Klᴹ-Symmetric }
