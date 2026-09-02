{-# OPTIONS --safe --without-K #-}

-- The monoidal structure is given by parallel composition

open import categorical-crypto.Prelude hiding (_>>=_; return)

open import Categories.Category.Core
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
import Categories.Functor.Bifunctor as CatBi
open import Categories.Monad.Construction.Kleisli
import Categories.Monad.Setoids.Discrete as Discrete
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Sum renaming (map to map⊎)
open import Data.Sum.Ext
open import Data.Sum.Properties

import CategoricalCrypto.SFunM.Kleisli as SFun
import CategoricalCrypto.SFunM.Kleisli.Properties as SFunProperties

module CategoricalCrypto.SFunM.Kleisli.Monoidal (K : KleisliTriple (Setoids 0ℓ 0ℓ))
  (M-Comm : Discrete.Commutative K) where

open Discrete K
open SFun K
open Laws M-Comm
open SFunProperties K

private
  variable A A′ B B′ C C′ D S S′ : Type

  module 𝒮 = Category SFunᵉ-Category

open 𝒮.HomReasoning using (_○_; ⟺; _⟩∘⟨_; refl⟩∘⟨_; _⟩∘⟨refl)
open import Categories.Morphism.Reasoning SFunᵉ-Category
open ≈ᴹ-Reasoning

------------------------------------------------------------------------
-- The tensor

infixr 10 _⊗ᵏ_ _⊗ᵉ_

_⊗ᵏ_ : SFunType A B S → SFunType C D S′ → SFunType (A ⊎ C) (B ⊎ D) (S × S′)
(f ⊗ᵏ g) ((s , t) , inj₁ a) = (λ (s′ , b) → (s′ , t) , inj₁ b) <$>ᴹ f (s , a)
(f ⊗ᵏ g) ((s , t) , inj₂ c) = (λ (t′ , d) → (s , t′) , inj₂ d) <$>ᴹ g (t , c)

_⊗ᵉ_ : SFunᵉ A B → SFunᵉ C D → SFunᵉ (A ⊎ C) (B ⊎ D)
f ⊗ᵉ g = mkᵉ (F.init , G.init) (F.fun ⊗ᵏ G.fun)
  where module F = SFunᵉ f
        module G = SFunᵉ g

------------------------------------------------------------------------
-- The structural morphisms

λ⇒ᵉ : SFunᵉ (⊥ ⊎ A) A
λ⇒ᵉ = statelessᵉ unitˡ⇒

λ⇐ᵉ : SFunᵉ A (⊥ ⊎ A)
λ⇐ᵉ = statelessᵉ inj₂

ρ⇒ᵉ : SFunᵉ (A ⊎ ⊥) A
ρ⇒ᵉ = statelessᵉ unitʳ⇒

ρ⇐ᵉ : SFunᵉ A (A ⊎ ⊥)
ρ⇐ᵉ = statelessᵉ inj₁

α⇒ᵉ : SFunᵉ ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
α⇒ᵉ = statelessᵉ assocʳ

α⇐ᵉ : SFunᵉ (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
α⇐ᵉ = statelessᵉ assocˡ

σᵉ : SFunᵉ (A ⊎ B) (B ⊎ A)
σᵉ = statelessᵉ swap

statelessᵉ-⊗ : (h : A → B) (k : C → D) → (statelessᵉ h ⊗ᵉ statelessᵉ k) ≈ᵉ statelessᵉ (map⊎ h k)
statelessᵉ-⊗ h k = ≈ᵉ-sim (λ _ → tt) refl λ where
  _ (inj₁ _) → ≈ᴹ.trans (<$>ᴹ-cong >>=-identityˡ-≈) >>=-identityˡ-≈
  _ (inj₂ _) → ≈ᴹ.trans (<$>ᴹ-cong >>=-identityˡ-≈) >>=-identityˡ-≈

unitorˡ-commuteᵉ : {f : SFunᵉ A B} → (λ⇒ᵉ ∘ᵉ (idᵉ ⊗ᵉ f)) ≈ᵉ (f ∘ᵉ λ⇒ᵉ)
unitorˡ-commuteᵉ {f = f} = statelessᵉ-natural unitˡ⇒ unitˡ⇒ proj₂ refl λ where
    (_ , s) (inj₂ a) → ≈ᴹ.trans (<$>ᴹ-∘ _ _ (F.fun (s , a))) (>>=-identityʳ-≈ (F.fun (s , a)))
  where module F = SFunᵉ f

unitorʳ-commuteᵉ : {f : SFunᵉ A B} → (ρ⇒ᵉ ∘ᵉ (f ⊗ᵉ idᵉ)) ≈ᵉ (f ∘ᵉ ρ⇒ᵉ)
unitorʳ-commuteᵉ {f = f} = statelessᵉ-natural unitʳ⇒ unitʳ⇒ proj₁ refl λ where
    (s , _) (inj₁ a) → ≈ᴹ.trans (<$>ᴹ-∘ _ _ (F.fun (s , a))) (>>=-identityʳ-≈ (F.fun (s , a)))
  where module F = SFunᵉ f

assoc-commuteᵉ : {f : SFunᵉ A A′} {g : SFunᵉ B B′} {h : SFunᵉ C C′}
               → (α⇒ᵉ ∘ᵉ ((f ⊗ᵉ g) ⊗ᵉ h)) ≈ᵉ ((f ⊗ᵉ (g ⊗ᵉ h)) ∘ᵉ α⇒ᵉ)
assoc-commuteᵉ {f = f} {g} {h} =
    statelessᵉ-natural assocʳ assocʳ (λ ((u , v) , w) → u , (v , w)) refl λ where
      ((u , _) , _) (inj₁ (inj₁ a)) →
        ≈ᴹ.trans (<$>ᴹ-cong (<$>ᴹ-∘ _ _ (F.fun (u , a)))) (<$>ᴹ-∘ _ _ (F.fun (u , a)))
      ((_ , v) , _) (inj₁ (inj₂ b)) →
        ≈ᴹ.trans (≈ᴹ.trans (<$>ᴹ-cong (<$>ᴹ-∘ _ _ (G.fun (v , b)))) (<$>ᴹ-∘ _ _ (G.fun (v , b))))
                 (≈ᴹ.sym (<$>ᴹ-∘ _ _ (G.fun (v , b))))
      ((_ , _) , w) (inj₂ c) →
        ≈ᴹ.trans (<$>ᴹ-∘ _ _ (H.fun (w , c))) (≈ᴹ.sym (<$>ᴹ-∘ _ _ (H.fun (w , c))))
  where module F = SFunᵉ f; module G = SFunᵉ g; module H = SFunᵉ h

braiding-commuteᵉ : {f : SFunᵉ A A′} {g : SFunᵉ B B′} → (σᵉ ∘ᵉ (f ⊗ᵉ g)) ≈ᵉ ((g ⊗ᵉ f) ∘ᵉ σᵉ)
braiding-commuteᵉ {f = f} {g} =
    statelessᵉ-natural swap swap (λ (u , v) → v , u) refl λ where
      (u , _) (inj₁ a) → <$>ᴹ-∘ _ _ (F.fun (u , a))
      (_ , v) (inj₂ b) → <$>ᴹ-∘ _ _ (G.fun (v , b))
  where module F = SFunᵉ f; module G = SFunᵉ g

------------------------------------------------------------------------
-- Coherence

λ-isoˡ : (λ⇐ᵉ ∘ᵉ λ⇒ᵉ {A}) ≈ᵉ idᵉ
λ-isoˡ = statelessᵉ-inv λ where (inj₂ _) → refl

λ-isoʳ : (λ⇒ᵉ ∘ᵉ λ⇐ᵉ {A}) ≈ᵉ idᵉ
λ-isoʳ = statelessᵉ-inv λ _ → refl

ρ-isoˡ : (ρ⇐ᵉ ∘ᵉ ρ⇒ᵉ {A}) ≈ᵉ idᵉ
ρ-isoˡ = statelessᵉ-inv λ where (inj₁ _) → refl

ρ-isoʳ : (ρ⇒ᵉ ∘ᵉ ρ⇐ᵉ {A}) ≈ᵉ idᵉ
ρ-isoʳ = statelessᵉ-inv λ _ → refl

α-isoˡ : (α⇐ᵉ ∘ᵉ α⇒ᵉ {A} {B} {C}) ≈ᵉ idᵉ
α-isoˡ = statelessᵉ-inv λ where
  (inj₁ (inj₁ _)) → refl
  (inj₁ (inj₂ _)) → refl
  (inj₂ _)        → refl

α-isoʳ : (α⇒ᵉ ∘ᵉ α⇐ᵉ {A} {B} {C}) ≈ᵉ idᵉ
α-isoʳ = statelessᵉ-inv λ where
  (inj₁ _)        → refl
  (inj₂ (inj₁ _)) → refl
  (inj₂ (inj₂ _)) → refl

σ-involutiveᵉ : (σᵉ ∘ᵉ σᵉ {A} {B}) ≈ᵉ idᵉ
σ-involutiveᵉ = statelessᵉ-inv swap-involutive

triangleᵉ : ((idᵉ {A} ⊗ᵉ λ⇒ᵉ {B}) ∘ᵉ α⇒ᵉ) ≈ᵉ (ρ⇒ᵉ ⊗ᵉ idᵉ)
triangleᵉ = statelessᵉ-⊗ id unitˡ⇒ ⟩∘⟨refl
          ○ ⟺ (statelessᵉ-∘ (map⊎ id unitˡ⇒) assocʳ)
          ○ statelessᵉ-cong (λ where
              (inj₁ (inj₁ _)) → refl
              (inj₂ _)        → refl)
          ○ ⟺ (statelessᵉ-⊗ unitʳ⇒ id)

pentagonᵉ : ((idᵉ ⊗ᵉ α⇒ᵉ {B} {C} {D}) ∘ᵉ (α⇒ᵉ ∘ᵉ (α⇒ᵉ {A} ⊗ᵉ idᵉ))) ≈ᵉ (α⇒ᵉ ∘ᵉ α⇒ᵉ)
pentagonᵉ = statelessᵉ-⊗ id assocʳ ⟩∘⟨ (refl⟩∘⟨ statelessᵉ-⊗ assocʳ id)
          ○ refl⟩∘⟨ (⟺ (statelessᵉ-∘ assocʳ (map⊎ assocʳ id)))
          ○ ⟺ (statelessᵉ-∘ (map⊎ id assocʳ) (assocʳ ∘ map⊎ assocʳ id))
          ○ statelessᵉ-cong (λ where
              (inj₁ (inj₁ (inj₁ _))) → refl
              (inj₁ (inj₁ (inj₂ _))) → refl
              (inj₁ (inj₂ _))        → refl
              (inj₂ _)               → refl)
          ○ statelessᵉ-∘ assocʳ assocʳ

hexagonᵉ : ((idᵉ ⊗ᵉ σᵉ {A} {C}) ∘ᵉ (α⇒ᵉ ∘ᵉ (σᵉ {A} {B} ⊗ᵉ idᵉ))) ≈ᵉ (α⇒ᵉ ∘ᵉ (σᵉ ∘ᵉ α⇒ᵉ))
hexagonᵉ = statelessᵉ-⊗ id swap ⟩∘⟨ (refl⟩∘⟨ statelessᵉ-⊗ swap id)
         ○ refl⟩∘⟨ (⟺ (statelessᵉ-∘ assocʳ (map⊎ swap id)))
         ○ ⟺ (statelessᵉ-∘ (map⊎ id swap) (assocʳ ∘ map⊎ swap id))
         ○ statelessᵉ-cong (λ where
             (inj₁ (inj₁ _)) → refl
             (inj₁ (inj₂ _)) → refl
             (inj₂ _)        → refl)
         ○ (statelessᵉ-∘ assocʳ (swap ∘ assocʳ)
           ○ refl⟩∘⟨ statelessᵉ-∘ swap assocʳ)

------------------------------------------------------------------------
-- Functoriality

⊗ᵉ-identity : (idᵉ {A} ⊗ᵉ idᵉ {B}) ≈ᵉ idᵉ
⊗ᵉ-identity = statelessᵉ-⊗ id id ○ statelessᵉ-cong map-id ○ statelessᵉ-id

⊗ᵉ-homomorphism : {f : SFunᵉ A B} {g : SFunᵉ B C}
                  {f′ : SFunᵉ A′ B′} {g′ : SFunᵉ B′ C′}
                → ((g ∘ᵉ f) ⊗ᵉ (g′ ∘ᵉ f′)) ≈ᵉ ((g ⊗ᵉ g′) ∘ᵉ (f ⊗ᵉ f′))
⊗ᵉ-homomorphism {f = f} {g} {f′} {g′} =
  ≈ᵉ-sim (λ ((sg , sf) , (sg′ , sf′)) → (sg , sg′) , (sf , sf′)) refl kern
  where
    module F = SFunᵉ f; module G = SFunᵉ g
    module F′ = SFunᵉ f′; module G′ = SFunᵉ g′

    Λ = λ ((u , v) , y) → ((proj₁ u , proj₁ v) , (proj₂ u , proj₂ v)) , y

    kern : ∀ s x → _
    kern ((sg , sf) , (sg′ , sf′)) (inj₁ a) = begin
      (Λ <$>ᴹ (Λ₁ <$>ᴹ (F.fun (sf , a) >>= mid)))
        ≈⟨ <$>ᴹ-∘ Λ Λ₁ _ ⟩
      ((Λ ∘ Λ₁) <$>ᴹ (F.fun (sf , a) >>= mid))
        ≈⟨ >>=-<$>ᴹ (Λ ∘ Λ₁) (F.fun (sf , a)) mid ⟩
      (F.fun (sf , a) >>= λ p → (Λ ∘ Λ₁) <$>ᴹ mid p)
        ≈⟨ >>=-cong-f (λ p → >>=-<$>ᴹ (Λ ∘ Λ₁) (G.fun (sg , proj₂ p)) _) ⟩
      (F.fun (sf , a) >>= λ p → G.fun (sg , proj₂ p) >>= λ q →
        (Λ ∘ Λ₁) <$>ᴹ return ((proj₁ q , proj₁ p) , proj₂ q))
        ≈⟨ >>=-cong-f (λ p → >>=-cong-f λ q → >>=-identityˡ-≈) ⟩
      (F.fun (sf , a) >>= λ p → G.fun (sg , proj₂ p) >>= λ q →
        return (((proj₁ q , sg′) , (proj₁ p , sf′)) , inj₁ (proj₂ q)))
        ≈˘⟨ >>=-cong-f (λ p → <$>ᴹ->>= Λg (G.fun (sg , proj₂ p)) (outer p)) ⟩
      (F.fun (sf , a) >>= λ p → (Λg <$>ᴹ G.fun (sg , proj₂ p)) >>= outer p)
        ≈˘⟨ <$>ᴹ->>= Λf (F.fun (sf , a)) cont ⟩
      ((Λf <$>ᴹ F.fun (sf , a)) >>= cont) ∎
      where
        Λ₁    = λ (u , c) → (u , (sg′ , sf′)) , inj₁ c
        Λf    = λ (u , b) → (u , sf′) , inj₁ b
        Λg    = λ (u , c) → (u , sg′) , inj₁ c
        mid   = λ p → G.fun (sg , proj₂ p) >>= λ q → return ((proj₁ q , proj₁ p) , proj₂ q)
        outer = λ p q → return ((proj₁ q , (proj₁ p , sf′)) , proj₂ q)
        cont  = λ P → (G.fun ⊗ᵏ G′.fun) ((sg , sg′) , proj₂ P)
                        >>= λ q → return ((proj₁ q , proj₁ P) , proj₂ q)
    kern ((sg , sf) , (sg′ , sf′)) (inj₂ c) = begin
      (Λ <$>ᴹ (Λ₁ <$>ᴹ (F′.fun (sf′ , c) >>= mid)))
        ≈⟨ <$>ᴹ-∘ Λ Λ₁ _ ⟩
      ((Λ ∘ Λ₁) <$>ᴹ (F′.fun (sf′ , c) >>= mid))
        ≈⟨ >>=-<$>ᴹ (Λ ∘ Λ₁) (F′.fun (sf′ , c)) mid ⟩
      (F′.fun (sf′ , c) >>= λ p → (Λ ∘ Λ₁) <$>ᴹ mid p)
        ≈⟨ >>=-cong-f (λ p → >>=-<$>ᴹ (Λ ∘ Λ₁) (G′.fun (sg′ , proj₂ p)) _) ⟩
      (F′.fun (sf′ , c) >>= λ p → G′.fun (sg′ , proj₂ p) >>= λ q →
        (Λ ∘ Λ₁) <$>ᴹ return ((proj₁ q , proj₁ p) , proj₂ q))
        ≈⟨ >>=-cong-f (λ p → >>=-cong-f λ q → >>=-identityˡ-≈) ⟩
      (F′.fun (sf′ , c) >>= λ p → G′.fun (sg′ , proj₂ p) >>= λ q →
        return (((sg , proj₁ q) , (sf , proj₁ p)) , inj₂ (proj₂ q)))
        ≈˘⟨ >>=-cong-f (λ p → <$>ᴹ->>= Λg (G′.fun (sg′ , proj₂ p)) (outer p)) ⟩
      (F′.fun (sf′ , c) >>= λ p → (Λg <$>ᴹ G′.fun (sg′ , proj₂ p)) >>= outer p)
        ≈˘⟨ <$>ᴹ->>= Λf (F′.fun (sf′ , c)) cont ⟩
      ((Λf <$>ᴹ F′.fun (sf′ , c)) >>= cont) ∎
      where
        Λ₁    = λ (u , d) → ((sg , sf) , u) , inj₂ d
        Λf    = λ (u , d) → (sf , u) , inj₂ d
        Λg    = λ (u , d) → (sg , u) , inj₂ d
        mid   = λ p → G′.fun (sg′ , proj₂ p) >>= λ q → return ((proj₁ q , proj₁ p) , proj₂ q)
        outer = λ p q → return ((proj₁ q , (sf , proj₁ p)) , proj₂ q)
        cont  = λ P → (G.fun ⊗ᵏ G′.fun) ((sg , sg′) , proj₂ P)
                        >>= λ q → return ((proj₁ q , proj₁ P) , proj₂ q)

-- No simulation is available for the congruence: `f ≈ᵉ g` relates traces, not
-- states, so it goes through a trace lemma instead.
private
  lefts : List (A ⊎ C) → List A
  lefts []             = []
  lefts (inj₁ a ∷ xs)  = a ∷ lefts xs
  lefts (inj₂ _ ∷ xs)  = lefts xs

  fillˡ : List (A ⊎ C) → List B → List (B ⊎ C)
  fillˡ []                 _        = []
  fillˡ (inj₁ _ ∷ xs)      []       = []
  fillˡ (inj₁ _ ∷ xs)      (b ∷ bs) = inj₁ b ∷ fillˡ xs bs
  fillˡ (inj₂ c ∷ xs)      bs       = inj₂ c ∷ fillˡ xs bs

  ⊗idᵏ-trace : (f : SFunType A B S) (s : S) (xs : List (A ⊎ C))
             → trace (f ⊗ᵏ idᵏ) (s , tt) xs ≈ᴹ (fillˡ xs <$>ᴹ trace f s (lefts xs))
  ⊗idᵏ-trace f s []             = ≈ᴹ.sym >>=-identityˡ-≈
  ⊗idᵏ-trace f s (inj₁ a ∷ xs)  = begin
    (((λ (s′ , b) → (s′ , tt) , inj₁ b) <$>ᴹ f (s , a)) >>= cont)
      ≈⟨ <$>ᴹ->>= _ (f (s , a)) cont ⟩
    (f (s , a) >>= λ p → trace (f ⊗ᵏ idᵏ) (proj₁ p , tt) xs >>= consˡ p)
      ≈⟨ >>=-cong-f (λ p → >>=-cong-x (⊗idᵏ-trace f (proj₁ p) xs)) ⟩
    (f (s , a) >>= λ p → (fillˡ xs <$>ᴹ trace f (proj₁ p) (lefts xs)) >>= consˡ p)
      ≈⟨ >>=-cong-f (λ p → <$>ᴹ->>= (fillˡ xs) (trace f (proj₁ p) (lefts xs)) (consˡ p)) ⟩
    (f (s , a) >>= λ p → trace f (proj₁ p) (lefts xs) >>= λ bs → return (inj₁ (proj₂ p) ∷ fillˡ xs bs))
      ≈˘⟨ >>=-cong-f (λ p → >>=-cong-f λ bs → >>=-identityˡ-≈) ⟩
    (f (s , a) >>= λ p → trace f (proj₁ p) (lefts xs) >>= λ bs → fill <$>ᴹ return (proj₂ p ∷ bs))
      ≈˘⟨ >>=-cong-f (λ p → >>=-<$>ᴹ fill (trace f (proj₁ p) (lefts xs)) _) ⟩
    (f (s , a) >>= λ p → fill <$>ᴹ (trace f (proj₁ p) (lefts xs) >>= λ bs → return (proj₂ p ∷ bs)))
      ≈˘⟨ >>=-<$>ᴹ fill (f (s , a)) _ ⟩
    (fill <$>ᴹ trace f s (a ∷ lefts xs)) ∎
    where
      fill  = fillˡ (inj₁ a ∷ xs)
      consˡ = λ p bs → return (inj₁ (proj₂ p) ∷ bs)
      cont  = λ p → trace (f ⊗ᵏ idᵏ) (proj₁ p) xs >>= λ bs → return (proj₂ p ∷ bs)
  ⊗idᵏ-trace f s (inj₂ c ∷ xs)  = begin
    ((((λ (t′ , d) → (s , t′) , inj₂ d) <$>ᴹ return (tt , c))) >>= cont)
      ≈⟨ <$>ᴹ->>= _ (return (tt , c)) cont ⟩
    (return (tt , c) >>= λ p → cont ((s , proj₁ p) , inj₂ (proj₂ p)))
      ≈⟨ >>=-identityˡ-≈ ⟩
    (trace (f ⊗ᵏ idᵏ) (s , tt) xs >>= consʳ)
      ≈⟨ >>=-cong-x (⊗idᵏ-trace f s xs) ⟩
    ((fillˡ xs <$>ᴹ trace f s (lefts xs)) >>= consʳ)
      ≈⟨ <$>ᴹ->>= (fillˡ xs) (trace f s (lefts xs)) consʳ ⟩
    (fillˡ (inj₂ c ∷ xs) <$>ᴹ trace f s (lefts xs)) ∎
    where
      consʳ = λ bs → return (inj₂ c ∷ bs)
      cont  = λ p → trace (f ⊗ᵏ idᵏ) (proj₁ p) xs >>= λ bs → return (proj₂ p ∷ bs)

  ⊗idᵉ-resp : {f g : SFunᵉ A B} → f ≈ᵉ g → (f ⊗ᵉ idᵉ {C}) ≈ᵉ (g ⊗ᵉ idᵉ {C})
  ⊗idᵉ-resp {f = f} {g} f≈g xs = begin
    eval (f ⊗ᵉ idᵉ) xs
      ≈⟨ ⊗idᵏ-trace F.fun F.init xs ⟩
    (fillˡ xs <$>ᴹ eval f (lefts xs))
      ≈⟨ <$>ᴹ-cong (f≈g (lefts xs)) ⟩
    (fillˡ xs <$>ᴹ eval g (lefts xs))
      ≈˘⟨ ⊗idᵏ-trace G.fun G.init xs ⟩
    eval (g ⊗ᵉ idᵉ) xs ∎
    where module F = SFunᵉ f; module G = SFunᵉ g

  -- Conjugating by the braiding saves a second trace lemma for the right factor.
  σ-conjᵉ : (f : SFunᵉ C D) → (σᵉ ∘ᵉ ((f ⊗ᵉ idᵉ {A}) ∘ᵉ σᵉ)) ≈ᵉ (idᵉ {A} ⊗ᵉ f)
  σ-conjᵉ f = pullˡ braiding-commuteᵉ ○ cancelʳ σ-involutiveᵉ

  id⊗ᵉ-resp : {f g : SFunᵉ C D} → f ≈ᵉ g → (idᵉ {A} ⊗ᵉ f) ≈ᵉ (idᵉ {A} ⊗ᵉ g)
  id⊗ᵉ-resp {f = f} {g} f≈g = ⟺ (σ-conjᵉ f) ○ refl⟩∘⟨ (⊗idᵉ-resp f≈g ⟩∘⟨refl) ○ σ-conjᵉ g

⊗-split : (f : SFunᵉ A B) (g : SFunᵉ C D) → (f ⊗ᵉ g) ≈ᵉ ((idᵉ ⊗ᵉ g) ∘ᵉ (f ⊗ᵉ idᵉ))
⊗-split f g = ≈ᵉ-sim (λ (s , t) → (tt , t) , (s , tt)) refl kern
  where
    module F = SFunᵉ f; module G = SFunᵉ g

    Λφ = λ ((u , v) , y) → ((tt , v) , (u , tt)) , y

    kern : ∀ s x → _
    kern (s , t) (inj₁ a) = begin
      (Λφ <$>ᴹ (Λ <$>ᴹ F.fun (s , a)))
        ≈⟨ <$>ᴹ-∘ Λφ Λ (F.fun (s , a)) ⟩
      ((Λφ ∘ Λ) <$>ᴹ F.fun (s , a))
        ≈˘⟨ >>=-cong-f (λ p → ≈ᴹ.trans (<$>ᴹ->>= _ (return (tt , proj₂ p)) (mid p)) >>=-identityˡ-≈) ⟩
      (F.fun (s , a) >>= λ p → ((λ (u , y) → (u , t) , inj₁ y) <$>ᴹ return (tt , proj₂ p)) >>= mid p)
        ≈˘⟨ <$>ᴹ->>= Λf (F.fun (s , a)) cont ⟩
      ((Λf <$>ᴹ F.fun (s , a)) >>= cont) ∎
      where
        Λ    = λ (s′ , b) → (s′ , t) , inj₁ b
        Λf   = λ (s′ , b) → (s′ , tt) , inj₁ b
        mid  = λ p Q → return ((proj₁ Q , (proj₁ p , tt)) , proj₂ Q)
        cont = λ P → (idᵏ ⊗ᵏ G.fun) ((tt , t) , proj₂ P) >>= λ Q → return ((proj₁ Q , proj₁ P) , proj₂ Q)
    kern (s , t) (inj₂ c) = begin
      (Λφ <$>ᴹ (Λ <$>ᴹ G.fun (t , c)))
        ≈⟨ <$>ᴹ-∘ Λφ Λ (G.fun (t , c)) ⟩
      ((Λφ ∘ Λ) <$>ᴹ G.fun (t , c))
        ≈˘⟨ <$>ᴹ->>= Λg (G.fun (t , c)) mid ⟩
      ((Λg <$>ᴹ G.fun (t , c)) >>= mid)
        ≈˘⟨ ≈ᴹ.trans (<$>ᴹ->>= Λf (return (tt , c)) cont) >>=-identityˡ-≈ ⟩
      ((Λf <$>ᴹ return (tt , c)) >>= cont) ∎
      where
        Λ    = λ (t′ , d) → (s , t′) , inj₂ d
        Λf   = λ (u , y) → (s , u) , inj₂ y
        Λg   = λ (t′ , d) → (tt , t′) , inj₂ d
        mid  = λ Q → return ((proj₁ Q , (s , tt)) , proj₂ Q)
        cont = λ P → (idᵏ ⊗ᵏ G.fun) ((tt , t) , proj₂ P) >>= λ Q → return ((proj₁ Q , proj₁ P) , proj₂ Q)

⊗ᵉ-resp-≈ : {f h : SFunᵉ A B} {g i : SFunᵉ C D} → f ≈ᵉ h → g ≈ᵉ i → (f ⊗ᵉ g) ≈ᵉ (h ⊗ᵉ i)
⊗ᵉ-resp-≈ {f = f} {h} {g} {i} f≈h g≈i = ⊗-split f g ○ id⊗ᵉ-resp g≈i ⟩∘⟨ ⊗idᵉ-resp f≈h ○ ⟺ (⊗-split h i)

⊗ᵉ-bifunctor : CatBi.Bifunctor SFunᵉ-Category SFunᵉ-Category SFunᵉ-Category
⊗ᵉ-bifunctor = record
  { F₀           = λ (A , B) → A ⊎ B
  ; F₁           = λ (f , g) → f ⊗ᵉ g
  ; identity     = ⊗ᵉ-identity
  ; homomorphism = ⊗ᵉ-homomorphism
  ; F-resp-≈     = λ (f≈h , g≈i) → ⊗ᵉ-resp-≈ f≈h g≈i
  }

------------------------------------------------------------------------
-- The bundles

SFunᵉ-Monoidal : Monoidal SFunᵉ-Category
SFunᵉ-Monoidal = monoidalHelper SFunᵉ-Category record
  { ⊗               = ⊗ᵉ-bifunctor
  ; unit            = ⊥
  ; unitorˡ         = record { from = λ⇒ᵉ ; to = λ⇐ᵉ ; iso = record { isoˡ = λ-isoˡ ; isoʳ = λ-isoʳ } }
  ; unitorʳ         = record { from = ρ⇒ᵉ ; to = ρ⇐ᵉ ; iso = record { isoˡ = ρ-isoˡ ; isoʳ = ρ-isoʳ } }
  ; associator      = record { from = α⇒ᵉ ; to = α⇐ᵉ ; iso = record { isoˡ = α-isoˡ ; isoʳ = α-isoʳ } }
  ; unitorˡ-commute = unitorˡ-commuteᵉ
  ; unitorʳ-commute = unitorʳ-commuteᵉ
  ; assoc-commute   = assoc-commuteᵉ
  ; triangle        = triangleᵉ
  ; pentagon        = pentagonᵉ
  }

SFunᵉ-Symmetric : Symmetric SFunᵉ-Monoidal
SFunᵉ-Symmetric = symmetricHelper SFunᵉ-Monoidal record
  { braiding = niHelper record
      { η       = λ _ → σᵉ
      ; η⁻¹     = λ _ → σᵉ
      ; commute = λ _ → braiding-commuteᵉ
      ; iso     = λ _ → record { isoˡ = σ-involutiveᵉ ; isoʳ = σ-involutiveᵉ }
      }
  ; commutative = σ-involutiveᵉ
  ; hexagon     = hexagonᵉ
  }

SFunᵉ-MonoidalCategory : MonoidalCategory _ _ _
SFunᵉ-MonoidalCategory = record { U = SFunᵉ-Category ; monoidal = SFunᵉ-Monoidal }
