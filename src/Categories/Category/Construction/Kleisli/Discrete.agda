{-# OPTIONS --safe --without-K #-}

-- The Kleisli category of a `DiscreteMonad` at the discrete objects, with the
-- cartesian tensor.  Spelled out with `_>>=_` rather than `μ ∘ F₁` so that it
-- computes on closed inputs.
--
-- The symmetric structure is hand-rolled on purpose: upstream's
-- `Kleisli-Symmetric` heap-exhausts here, because its `commutative` field
-- eta-expands the Kleisli hom setoid's `IsEquivalence` into metas that are never
-- solved.  Do not replace it by a transport off that construction.

open import Categories.Category.Core
open import Categories.Category.Helper
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
open import Categories.Functor.Bifunctor
open import Categories.Monad.Discrete
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Product
open import Data.Unit.Polymorphic
open import Function.Base
open import Level
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality

module Categories.Category.Construction.Kleisli.Discrete {ℓ} (Mo : DiscreteMonad ℓ) where

open DiscreteMonad Mo
open ≈ᴹ-Reasoning

private variable A A′ B B′ C C′ D E : Set ℓ

------------------------------------------------------------------------
-- The category
------------------------------------------------------------------------

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

open Category.HomReasoning Klᴹ using (_○_; ⟺; _⟩∘⟨_; refl⟩∘⟨_)

------------------------------------------------------------------------
-- Pure morphisms
------------------------------------------------------------------------

pureᵏ : (A → B) → (A → M B)
pureᵏ = return ∘_

pureᵏ-cong : {h k : A → B} → h ≗ k → pureᵏ h ≈ᵏ pureᵏ k
pureᵏ-cong h≡k a = ≈ᴹ.reflexive (cong return (h≡k a))

pureᵏ-∘ : (h : B → C) (k : A → B) → (pureᵏ h <=< pureᵏ k) ≈ᵏ pureᵏ (h ∘ k)
pureᵏ-∘ _ _ _ = >>=-identityˡ-≈

------------------------------------------------------------------------
-- The tensor
------------------------------------------------------------------------

infixr 10 _⊗ᵏ_

-- Projections rather than a pattern-matching lambda: `_⊗ᵏ_` then reduces on an
-- argument that is not yet a literal pair, which is what lets a consumer's
-- structural shuffles compute.
_⊗ᵏ_ : (A → M B) → (C → M D) → A × C → M (B × D)
(f ⊗ᵏ g) p = f (proj₁ p) >>= λ b → g (proj₂ p) >>= λ d → return (b , d)

⊗ᵏ-expand : (f : A → M B) (g : C → M D) (h : B × D → M E) (p : A × C)
          → ((f ⊗ᵏ g) p >>= h) ≈ᴹ (f (proj₁ p) >>= λ b → g (proj₂ p) >>= λ d → h (b , d))
⊗ᵏ-expand f g h p =
  ≈ᴹ.trans (>>=-assoc-≈ (f (proj₁ p)))
           (>>=-cong-f λ _ → ≈ᴹ.trans (>>=-assoc-≈ (g (proj₂ p)))
                                      (>>=-cong-f λ _ → >>=-identityˡ-≈))

pureᵏ-⊗ : (h : A → B) (k : C → D) → (pureᵏ h ⊗ᵏ pureᵏ k) ≈ᵏ pureᵏ (map h k)
pureᵏ-⊗ _ _ (_ , _) = ≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈

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
  ; identity     = pureᵏ-⊗ id id
  ; homomorphism = ⊗ᵏ-homomorphism
  ; F-resp-≈     = λ (f≈h , g≈i) → ⊗ᵏ-resp-≈ f≈h g≈i
  }

------------------------------------------------------------------------
-- The structural morphisms
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Naturality
------------------------------------------------------------------------

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

assoc-commuteᵏ : {f : A → M A′} {g : B → M B′} {h : C → M C′} → (α⇒ᵏ <=< ((f ⊗ᵏ g) ⊗ᵏ h)) ≈ᵏ ((f ⊗ᵏ (g ⊗ᵏ h)) <=< α⇒ᵏ)
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
------------------------------------------------------------------------

triangleᵏ : ((return ⊗ᵏ λ⇒ᵏ {B}) <=< α⇒ᵏ {A}) ≈ᵏ (ρ⇒ᵏ ⊗ᵏ return)
triangleᵏ ((_ , _) , _) = >>=-identityˡ-≈

pentagonᵏ : ((return ⊗ᵏ α⇒ᵏ {B} {C} {D}) <=< (α⇒ᵏ <=< (α⇒ᵏ {A} ⊗ᵏ return))) ≈ᵏ (α⇒ᵏ <=< α⇒ᵏ)
pentagonᵏ = pureᵏ-⊗ id assocʳ′ ⟩∘⟨ (refl⟩∘⟨ pureᵏ-⊗ assocʳ′ id)
          ○ refl⟩∘⟨ pureᵏ-∘ _ _
          ○ pureᵏ-∘ _ _
          ○ pureᵏ-cong (λ where (((_ , _) , _) , _) → refl)
          ○ ⟺ (pureᵏ-∘ _ _)

hexagonᵏ : ((return ⊗ᵏ σᵏ {A} {C}) <=< (α⇒ᵏ <=< (σᵏ {A} {B} ⊗ᵏ return))) ≈ᵏ (α⇒ᵏ <=< (σᵏ <=< α⇒ᵏ))
hexagonᵏ = pureᵏ-⊗ id swap ⟩∘⟨ (refl⟩∘⟨ pureᵏ-⊗ swap id)
         ○ refl⟩∘⟨ pureᵏ-∘ _ _
         ○ pureᵏ-∘ _ _
         ○ pureᵏ-cong (λ where ((_ , _) , _) → refl)
         ○ ⟺ (refl⟩∘⟨ pureᵏ-∘ _ _ ○ pureᵏ-∘ _ _)

------------------------------------------------------------------------
-- The bundles
------------------------------------------------------------------------

Klᴹ-Monoidal : Monoidal Klᴹ
Klᴹ-Monoidal = monoidalHelper Klᴹ record
  { ⊗               = ⊗ᵏ-bifunctor
  ; unit            = ⊤ᵏ
  ; unitorˡ         = record { from = λ⇒ᵏ ; to = λ⇐ᵏ ; iso = record { isoˡ = λ _ → >>=-identityˡ-≈ ; isoʳ = λ _ → >>=-identityˡ-≈ } }
  ; unitorʳ         = record { from = ρ⇒ᵏ ; to = ρ⇐ᵏ ; iso = record { isoˡ = λ _ → >>=-identityˡ-≈ ; isoʳ = λ _ → >>=-identityˡ-≈ } }
  ; associator      = record { from = α⇒ᵏ ; to = α⇐ᵏ ; iso = record
      { isoˡ = λ { ((_ , _) , _) → >>=-identityˡ-≈ } ; isoʳ = λ { (_ , _ , _) → >>=-identityˡ-≈ } } }
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
      ; iso     = λ _ → record { isoˡ = σσ ; isoʳ = σσ }
      }
  ; commutative = σσ
  ; hexagon     = hexagonᵏ
  }
  where σσ : (σᵏ <=< σᵏ {A} {B}) ≈ᵏ return
        σσ (_ , _) = >>=-identityˡ-≈

Klᴹ-SymmetricMonoidal : SymmetricMonoidalCategory (suc ℓ) ℓ ℓ
Klᴹ-SymmetricMonoidal = record { U = Klᴹ ; monoidal = Klᴹ-Monoidal ; symmetric = Klᴹ-Symmetric }
