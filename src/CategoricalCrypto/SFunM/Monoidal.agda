{-# OPTIONS --safe --without-K #-}

-- `SFunᵉ` is symmetric monoidal under the disjoint union of interfaces: the
-- tensor is a coproduct of interfaces, so the unit is `⊥`.

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad.Ext.Setoid

open import Categories.Category.Core
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric
import Categories.Functor.Bifunctor as CatBi
open import Categories.NaturalTransformation.NaturalIsomorphism using (niHelper)

open import Data.Sum.Base renaming (map to map⊎)
open import Data.Sum.Ext
open import Data.Sum.Properties

import Relation.Binary.Reasoning.Setoid as R-Setoid

open import CategoricalCrypto.SFunM
open import CategoricalCrypto.SFunM.Properties

module CategoricalCrypto.SFunM.Monoidal {M : Type↑}
  ⦃ Monad-M : Monad M                  ⦄
  ⦃ MS      : MonadSetoid M            ⦄
  ⦃ M-Laws  : MonadLawsSetoid M        ⦄
  ⦃ M-Comm  : CommutativeMonadSetoid M ⦄ where

private
  variable A A′ B B′ C C′ D S S′ : Type

  module 𝒮 = Category (SFunᵉ-Category {M = M})

open 𝒮.HomReasoning using (_○_; ⟺)
open import Categories.Morphism.Reasoning (SFunᵉ-Category {M = M}) using (pullˡ; cancelʳ)

------------------------------------------------------------------------
-- The tensor

infixr 10 _⊗ᵏ_ _⊗ᵉ_

_⊗ᵏ_ : SFunType A B S → SFunType C D S′ → SFunType (A ⊎ C) (B ⊎ D) (S × S′)
(f ⊗ᵏ g) ((s , t) , inj₁ a) = (λ (s′ , b) → (s′ , t) , inj₁ b) <$>ᴹ f (s , a)
(f ⊗ᵏ g) ((s , t) , inj₂ c) = (λ (t′ , d) → (s , t′) , inj₂ d) <$>ᴹ g (t , c)

_⊗ᵉ_ : SFunᵉ {M = M} A B → SFunᵉ {M = M} C D → SFunᵉ {M = M} (A ⊎ C) (B ⊎ D)
f ⊗ᵉ g = record { State = F.State × G.State ; init = F.init , G.init ; fun = F.fun ⊗ᵏ G.fun }
  where module F = SFunᵉ f
        module G = SFunᵉ g

------------------------------------------------------------------------
-- The structural morphisms
--
-- All of them are stateless, so their naturality squares are
-- kernel-level identities.

λ⇒ᵉ : SFunᵉ {M = M} (⊥ ⊎ A) A
λ⇒ᵉ = statelessᵉ unitˡ⇒

λ⇐ᵉ : SFunᵉ {M = M} A (⊥ ⊎ A)
λ⇐ᵉ = statelessᵉ inj₂

ρ⇒ᵉ : SFunᵉ {M = M} (A ⊎ ⊥) A
ρ⇒ᵉ = statelessᵉ unitʳ⇒

ρ⇐ᵉ : SFunᵉ {M = M} A (A ⊎ ⊥)
ρ⇐ᵉ = statelessᵉ inj₁

α⇒ᵉ : SFunᵉ {M = M} ((A ⊎ B) ⊎ C) (A ⊎ (B ⊎ C))
α⇒ᵉ = statelessᵉ assocʳ

α⇐ᵉ : SFunᵉ {M = M} (A ⊎ (B ⊎ C)) ((A ⊎ B) ⊎ C)
α⇐ᵉ = statelessᵉ assocˡ

σᵉ : SFunᵉ {M = M} (A ⊎ B) (B ⊎ A)
σᵉ = statelessᵉ swap

statelessᵉ-⊗ : (h : A → B) (k : C → D) → (statelessᵉ h ⊗ᵉ statelessᵉ k) ≈ᵉ statelessᵉ (map⊎ h k)
statelessᵉ-⊗ h k = ≈ᵉ-sim (λ _ → tt) refl kern
  where
    kern : ∀ s x → _
    kern s (inj₁ a) = ≈ᴹ.trans (<$>ᴹ-cong >>=-identityˡ-≈) >>=-identityˡ-≈
    kern s (inj₂ c) = ≈ᴹ.trans (<$>ᴹ-cong >>=-identityˡ-≈) >>=-identityˡ-≈

unitorˡ-commuteᵉ : {f : SFunᵉ {M = M} A B} → (λ⇒ᵉ ∘ᵉ (idᵉ ⊗ᵉ f)) ≈ᵉ (f ∘ᵉ λ⇒ᵉ)
unitorˡ-commuteᵉ {f = f} = statelessᵉ-natural unitˡ⇒ unitˡ⇒ proj₂ refl λ where
    (_ , s) (inj₂ a) → ≈ᴹ.trans (<$>ᴹ-∘ _ _ (F.fun (s , a))) (>>=-identityʳ-≈ (F.fun (s , a)))
  where module F = SFunᵉ f

unitorʳ-commuteᵉ : {f : SFunᵉ {M = M} A B} → (ρ⇒ᵉ ∘ᵉ (f ⊗ᵉ idᵉ)) ≈ᵉ (f ∘ᵉ ρ⇒ᵉ)
unitorʳ-commuteᵉ {f = f} = statelessᵉ-natural unitʳ⇒ unitʳ⇒ proj₁ refl λ where
    (s , _) (inj₁ a) → ≈ᴹ.trans (<$>ᴹ-∘ _ _ (F.fun (s , a))) (>>=-identityʳ-≈ (F.fun (s , a)))
  where module F = SFunᵉ f

assoc-commuteᵉ : {f : SFunᵉ {M = M} A A′} {g : SFunᵉ {M = M} B B′} {h : SFunᵉ {M = M} C C′}
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

braiding-commuteᵉ : {f : SFunᵉ {M = M} A A′} {g : SFunᵉ {M = M} B B′} → (σᵉ ∘ᵉ (f ⊗ᵉ g)) ≈ᵉ ((g ⊗ᵉ f) ∘ᵉ σᵉ)
braiding-commuteᵉ {f = f} {g} =
    statelessᵉ-natural swap swap (λ (u , v) → v , u) refl λ where
      (u , _) (inj₁ a) → <$>ᴹ-∘ _ _ (F.fun (u , a))
      (_ , v) (inj₂ b) → <$>ᴹ-∘ _ _ (G.fun (v , b))
  where module F = SFunᵉ f; module G = SFunᵉ g

------------------------------------------------------------------------
-- Coherence
--
-- Every law here is between composites of stateless machines, so it reduces
-- to a pointwise equation between `⊎`-shuffles.

private
  statelessᵉ-inv : {h : A → B} {k : B → A} → k ∘ h ≗ id → (statelessᵉ k ∘ᵉ statelessᵉ h) ≈ᵉ idᵉ
  statelessᵉ-inv {h = h} {k} inv = ⟺ (statelessᵉ-∘ k h) ○ statelessᵉ-cong {k = id} inv

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

triangleᵉ : ((idᵉ {M = M} {A} ⊗ᵉ λ⇒ᵉ {B}) ∘ᵉ α⇒ᵉ) ≈ᵉ (ρ⇒ᵉ ⊗ᵉ idᵉ)
triangleᵉ = ∘ᵉ-resp-≈ᵉ (statelessᵉ-⊗ id unitˡ⇒) 𝒮.Equiv.refl
          ○ ⟺ (statelessᵉ-∘ (map⊎ id unitˡ⇒) assocʳ)
          ○ statelessᵉ-cong (λ where
              (inj₁ (inj₁ _)) → refl
              (inj₂ _)        → refl)
          ○ ⟺ (statelessᵉ-⊗ unitʳ⇒ id)

pentagonᵉ : ((idᵉ ⊗ᵉ α⇒ᵉ {B} {C} {D}) ∘ᵉ (α⇒ᵉ ∘ᵉ (α⇒ᵉ {A} ⊗ᵉ idᵉ))) ≈ᵉ (α⇒ᵉ ∘ᵉ α⇒ᵉ)
pentagonᵉ = ∘ᵉ-resp-≈ᵉ (statelessᵉ-⊗ id assocʳ)
                      (∘ᵉ-resp-≈ᵉ 𝒮.Equiv.refl (statelessᵉ-⊗ assocʳ id))
          ○ ∘ᵉ-resp-≈ᵉ 𝒮.Equiv.refl (⟺ (statelessᵉ-∘ assocʳ (map⊎ assocʳ id)))
          ○ ⟺ (statelessᵉ-∘ (map⊎ id assocʳ) (assocʳ ∘ map⊎ assocʳ id))
          ○ statelessᵉ-cong (λ where
              (inj₁ (inj₁ (inj₁ _))) → refl
              (inj₁ (inj₁ (inj₂ _))) → refl
              (inj₁ (inj₂ _))        → refl
              (inj₂ _)               → refl)
          ○ statelessᵉ-∘ assocʳ assocʳ

hexagonᵉ : ((idᵉ ⊗ᵉ σᵉ {A} {C}) ∘ᵉ (α⇒ᵉ ∘ᵉ (σᵉ {A} {B} ⊗ᵉ idᵉ))) ≈ᵉ (α⇒ᵉ ∘ᵉ (σᵉ ∘ᵉ α⇒ᵉ))
hexagonᵉ = ∘ᵉ-resp-≈ᵉ (statelessᵉ-⊗ id swap)
                     (∘ᵉ-resp-≈ᵉ 𝒮.Equiv.refl (statelessᵉ-⊗ swap id))
         ○ ∘ᵉ-resp-≈ᵉ 𝒮.Equiv.refl (⟺ (statelessᵉ-∘ assocʳ (map⊎ swap id)))
         ○ ⟺ (statelessᵉ-∘ (map⊎ id swap) (assocʳ ∘ map⊎ swap id))
         ○ statelessᵉ-cong (λ where
             (inj₁ (inj₁ _)) → refl
             (inj₁ (inj₂ _)) → refl
             (inj₂ _)        → refl)
         ○ (statelessᵉ-∘ assocʳ (swap ∘ assocʳ)
           ○ ∘ᵉ-resp-≈ᵉ 𝒮.Equiv.refl (statelessᵉ-∘ swap assocʳ))

------------------------------------------------------------------------
-- Functoriality

⊗ᵉ-identity : (idᵉ {M = M} {A} ⊗ᵉ idᵉ {M = M} {B}) ≈ᵉ idᵉ
⊗ᵉ-identity = statelessᵉ-⊗ id id ○ statelessᵉ-cong map-id ○ statelessᵉ-id

⊗ᵉ-homomorphism : {f : SFunᵉ {M = M} A B} {g : SFunᵉ {M = M} B C}
                  {f′ : SFunᵉ {M = M} A′ B′} {g′ : SFunᵉ {M = M} B′ C′}
                → ((g ∘ᵉ f) ⊗ᵉ (g′ ∘ᵉ f′)) ≈ᵉ ((g ⊗ᵉ g′) ∘ᵉ (f ⊗ᵉ f′))
⊗ᵉ-homomorphism {f = f} {g} {f′} {g′} =
  ≈ᵉ-sim (λ ((sg , sf) , (sg′ , sf′)) → (sg , sg′) , (sf , sf′)) refl kern
  where
    module F = SFunᵉ f; module G = SFunᵉ g
    module F′ = SFunᵉ f′; module G′ = SFunᵉ g′
    open R-Setoid ≈ᴹ-setoid

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
        Λ     = λ ((u , v) , y) → ((proj₁ u , proj₁ v) , (proj₂ u , proj₂ v)) , y
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
        Λ     = λ ((u , v) , y) → ((proj₁ u , proj₁ v) , (proj₂ u , proj₂ v)) , y
        Λ₁    = λ (u , d) → ((sg , sf) , u) , inj₂ d
        Λf    = λ (u , d) → (sf , u) , inj₂ d
        Λg    = λ (u , d) → (sg , u) , inj₂ d
        mid   = λ p → G′.fun (sg′ , proj₂ p) >>= λ q → return ((proj₁ q , proj₁ p) , proj₂ q)
        outer = λ p q → return ((proj₁ q , (sf , proj₁ p)) , proj₂ q)
        cont  = λ P → (G.fun ⊗ᵏ G′.fun) ((sg , sg′) , proj₂ P)
                        >>= λ q → return ((proj₁ q , proj₁ P) , proj₂ q)

-- Congruence cannot be proven by a simulation, it goes through the trace instead
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
             → trace (f ⊗ᵏ SFunᵉ.fun idᵉ) (s , tt) xs ≈ᴹ (fillˡ xs <$>ᴹ trace f s (lefts xs))
  ⊗idᵏ-trace f s []             = ≈ᴹ.sym >>=-identityˡ-≈
  ⊗idᵏ-trace f s (inj₁ a ∷ xs)  = begin
    (((λ (s′ , b) → (s′ , tt) , inj₁ b) <$>ᴹ f (s , a)) >>= cont)
      ≈⟨ <$>ᴹ->>= _ (f (s , a)) cont ⟩
    (f (s , a) >>= λ p → trace (f ⊗ᵏ SFunᵉ.fun idᵉ) (proj₁ p , tt) xs >>= consˡ p)
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
      cont  = λ p → trace (f ⊗ᵏ SFunᵉ.fun idᵉ) (proj₁ p) xs >>= λ bs → return (proj₂ p ∷ bs)
      open R-Setoid ≈ᴹ-setoid
  ⊗idᵏ-trace f s (inj₂ c ∷ xs)  = begin
    ((((λ (t′ , d) → (s , t′) , inj₂ d) <$>ᴹ return (tt , c))) >>= cont)
      ≈⟨ <$>ᴹ->>= _ (return (tt , c)) cont ⟩
    (return (tt , c) >>= λ p → cont ((s , proj₁ p) , inj₂ (proj₂ p)))
      ≈⟨ >>=-identityˡ-≈ ⟩
    (trace (f ⊗ᵏ SFunᵉ.fun idᵉ) (s , tt) xs >>= consʳ)
      ≈⟨ >>=-cong-x (⊗idᵏ-trace f s xs) ⟩
    ((fillˡ xs <$>ᴹ trace f s (lefts xs)) >>= consʳ)
      ≈⟨ <$>ᴹ->>= (fillˡ xs) (trace f s (lefts xs)) consʳ ⟩
    (fillˡ (inj₂ c ∷ xs) <$>ᴹ trace f s (lefts xs)) ∎
    where
      consʳ = λ bs → return (inj₂ c ∷ bs)
      cont  = λ p → trace (f ⊗ᵏ SFunᵉ.fun idᵉ) (proj₁ p) xs >>= λ bs → return (proj₂ p ∷ bs)
      open R-Setoid ≈ᴹ-setoid

  ⊗idᵉ-resp : {f g : SFunᵉ {M = M} A B} → f ≈ᵉ g → (f ⊗ᵉ idᵉ {M = M} {C}) ≈ᵉ (g ⊗ᵉ idᵉ {M = M} {C})
  ⊗idᵉ-resp {f = f} {g} f≈g xs = begin
    eval (f ⊗ᵉ idᵉ) xs
      ≈⟨ ⊗idᵏ-trace (SFunᵉ.fun f) (SFunᵉ.init f) xs ⟩
    (fillˡ xs <$>ᴹ eval f (lefts xs))
      ≈⟨ <$>ᴹ-cong (f≈g (lefts xs)) ⟩
    (fillˡ xs <$>ᴹ eval g (lefts xs))
      ≈˘⟨ ⊗idᵏ-trace (SFunᵉ.fun g) (SFunᵉ.init g) xs ⟩
    eval (g ⊗ᵉ idᵉ) xs ∎
    where open R-Setoid ≈ᴹ-setoid

  -- `idᵉ ⊗ᵉ f` is the braiding conjugate of `f ⊗ᵉ idᵉ`, so the right factor
  -- needs no trace argument of its own.
  σ-conjᵉ : (f : SFunᵉ {M = M} C D) → (σᵉ ∘ᵉ ((f ⊗ᵉ idᵉ {M = M} {A}) ∘ᵉ σᵉ)) ≈ᵉ (idᵉ {M = M} {A} ⊗ᵉ f)
  σ-conjᵉ f = pullˡ (braiding-commuteᵉ {f = f} {g = idᵉ}) ○ cancelʳ σ-involutiveᵉ

  id⊗ᵉ-resp : {f g : SFunᵉ {M = M} C D} → f ≈ᵉ g → (idᵉ {M = M} {A} ⊗ᵉ f) ≈ᵉ (idᵉ {M = M} {A} ⊗ᵉ g)
  id⊗ᵉ-resp {f = f} {g} f≈g =
    ⟺ (σ-conjᵉ f) ○ 𝒮.∘-resp-≈ʳ (𝒮.∘-resp-≈ˡ (⊗idᵉ-resp f≈g)) ○ σ-conjᵉ g

⊗-split : (f : SFunᵉ {M = M} A B) (g : SFunᵉ {M = M} C D) → (f ⊗ᵉ g) ≈ᵉ ((idᵉ ⊗ᵉ g) ∘ᵉ (f ⊗ᵉ idᵉ))
⊗-split f g = ≈ᵉ-sim (λ (s , t) → (tt , t) , (s , tt)) refl kern
  where
    module F = SFunᵉ f; module G = SFunᵉ g
    open R-Setoid ≈ᴹ-setoid

    kern : ∀ s x → _
    kern (s , t) (inj₁ a) = begin
      (Λφ <$>ᴹ (Λ <$>ᴹ F.fun (s , a)))
        ≈⟨ <$>ᴹ-∘ Λφ Λ (F.fun (s , a)) ⟩
      ((Λφ ∘ Λ) <$>ᴹ F.fun (s , a))
        ≈˘⟨ >>=-cong-f (λ p → ≈ᴹ.trans (<$>ᴹ->>= _ (return (tt , proj₂ p)) (mid p)) >>=-identityˡ-≈) ⟩
      (F.fun (s , a) >>= λ p → ((λ (u , y) → (u , t) , inj₁ y) <$>ᴹ return (tt , proj₂ p)) >>= mid p)
        ≈˘⟨ <$>ᴹ->>= Λf (F.fun (s , a)) K ⟩
      ((Λf <$>ᴹ F.fun (s , a)) >>= K) ∎
      where
        Λφ  = λ ((u , v) , y) → ((tt , v) , (u , tt)) , y
        Λ   = λ (s′ , b) → (s′ , t) , inj₁ b
        Λf  = λ (s′ , b) → (s′ , tt) , inj₁ b
        mid = λ p Q → return ((proj₁ Q , (proj₁ p , tt)) , proj₂ Q)
        K   = λ P → (SFunᵉ.fun idᵉ ⊗ᵏ G.fun) ((tt , t) , proj₂ P)
                      >>= λ Q → return ((proj₁ Q , proj₁ P) , proj₂ Q)
    kern (s , t) (inj₂ c) = begin
      (Λφ <$>ᴹ (Λ <$>ᴹ G.fun (t , c)))
        ≈⟨ <$>ᴹ-∘ Λφ Λ (G.fun (t , c)) ⟩
      ((Λφ ∘ Λ) <$>ᴹ G.fun (t , c))
        ≈˘⟨ <$>ᴹ->>= Λg (G.fun (t , c)) mid ⟩
      ((Λg <$>ᴹ G.fun (t , c)) >>= mid)
        ≈˘⟨ ≈ᴹ.trans (<$>ᴹ->>= Λf (return (tt , c)) K) >>=-identityˡ-≈ ⟩
      ((Λf <$>ᴹ return (tt , c)) >>= K) ∎
      where
        Λφ  = λ ((u , v) , y) → ((tt , v) , (u , tt)) , y
        Λ   = λ (t′ , d) → (s , t′) , inj₂ d
        Λf  = λ (u , y) → (s , u) , inj₂ y
        Λg  = λ (t′ , d) → (tt , t′) , inj₂ d
        mid = λ Q → return ((proj₁ Q , (s , tt)) , proj₂ Q)
        K   = λ P → (SFunᵉ.fun idᵉ ⊗ᵏ G.fun) ((tt , t) , proj₂ P)
                      >>= λ Q → return ((proj₁ Q , proj₁ P) , proj₂ Q)

⊗ᵉ-resp-≈ : {f h : SFunᵉ {M = M} A B} {g i : SFunᵉ {M = M} C D} → f ≈ᵉ h → g ≈ᵉ i → (f ⊗ᵉ g) ≈ᵉ (h ⊗ᵉ i)
⊗ᵉ-resp-≈ {f = f} {h} {g} {i} f≈h g≈i =
  ⊗-split f g ○ ∘ᵉ-resp-≈ᵉ (id⊗ᵉ-resp g≈i) (⊗idᵉ-resp f≈h) ○ ⟺ (⊗-split h i)

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

SFunᵉ-Monoidal : Monoidal (SFunᵉ-Category {M = M})
SFunᵉ-Monoidal = monoidalHelper (SFunᵉ-Category {M = M}) record
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
SFunᵉ-MonoidalCategory = record { U = SFunᵉ-Category {M = M} ; monoidal = SFunᵉ-Monoidal }
