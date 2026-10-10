{-# OPTIONS --safe --without-K --guardedness #-}

-- `Supp-iterₚ`: a loop's depth-`n` support, from an invariant `J` of the loop
-- states and an exit predicate `Ψ` that every turn of the body lands in.  A
-- turn re-enters the body one step down (`tagᵢ`), so the induction is on the
-- budget alone and no coinduction is needed.  `iterₚ-transferˢ` is
-- `Dp.Iter.Transfer`'s transfer with the simulation asked only on such an
-- invariant.

open import Data.Bool.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Attach
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Iter.Transfer
open import ProbabilisticLogic.Dp.Reasoning

module ProbabilisticLogic.Dp.Iter.Supp where

private variable
  ℓ ℓ′ : Level
  S A B : Set ℓ

-- Where a turn may land: an exit satisfying `Ψ`, or a loop state satisfying `J`.
Turn : (S × A → Set ℓ′) → (S × B → Set ℓ′) → S × (B ⊎ A) → Set ℓ′
Turn J Ψ (s , inj₁ y) = Ψ (s , y)
Turn J Ψ (s , inj₂ x) = J (s , x)

module _ {u : Body S A B} {J : S × A → Set ℓ′} {Ψ : S × B → Set ℓ′}
         (body : ∀ {sa} → J sa → ∀ n → Supp n (u sa) (Turn J Ψ)) where

  mutual
    Supp-stepᵢ : (n : ℕ) (x : Dₚ (S × (B ⊎ A))) → Supp n x (Turn J Ψ) → Supp n (stepᵢ u x) Ψ
    Supp-stepᵢ zero    _ _         = tt
    Supp-stepᵢ (suc n) x (s₁ , s₂) = SuppL-tagᵢ n (br x true) s₁ , SuppL-tagᵢ n (br x false) s₂

    SuppL-tagᵢ : (n : ℕ) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
               → SuppL n y (Turn J Ψ) → SuppL n (tagᵢ u y) Ψ
    SuppL-tagᵢ n (inj₁ (_ , inj₁ _)) h = h
    SuppL-tagᵢ n (inj₁ (s , inj₂ x)) h = Supp-stepᵢ n (u (s , x)) (body h n)
    SuppL-tagᵢ n (inj₂ x′)           h = Supp-stepᵢ n x′ h

  Supp-iterₚ : ∀ {sa} → J sa → ∀ n → Supp n (iterₚ u sa) Ψ
  Supp-iterₚ j n = Supp-stepᵢ n _ (body j n)

-- On the loop over `Σ (S × A) J`, whose body attaches each turn's support
-- (`Dp.Attach`), the simulation is total: this is `iterₚ-transfer` from there
-- into `u` and into `u′`.
iterₚ-transferˢ : {S A B S′ A′ B′ : Set ℓ} (u : Body S A B) (u′ : Body S′ A′ B′)
                  (k : S × A → S′ × A′) (m : S × B → S′ × B′) (J : S × A → Set ℓ)
                → (∀ {sa} → J sa → ∀ n → Supp n (u sa) (Turn J (λ _ → ⊤)))
                → (∀ {sa} → J sa → u′ (k sa) ≈ₚ mapₚ (φ k m) (u sa))
                → ∀ {sa} → J sa → iterₚ u′ (k sa) ≈ₚ mapₚ m (iterₚ u sa)
iterₚ-transferˢ {S = S} {A} {B} u u′ k m J body sim {sa} j =
      iterₚ-transfer uᴶ u′ (k ∘′ π) (m ∘′ proj₂) sim′ (tt , sa , j)
  ⟨≈⟩ ≈sym (map-map (iterₚ uᴶ (tt , sa , j)) proj₂ m)
  ⟨≈⟩ map-arg m (≈sym (iterₚ-transfer uᴶ u π proj₂ sim₁ (tt , sa , j)))
  where
  τ : Σ (S × (B ⊎ A)) (Turn J (λ _ → ⊤)) → ⊤ × ((S × B) ⊎ Σ (S × A) J)
  τ ((s , inj₁ b) , _) = tt , inj₁ (s , b)
  τ ((s , inj₂ a) , t) = tt , inj₂ ((s , a) , t)

  uᴶ : Body ⊤ (Σ (S × A) J) (S × B)
  uᴶ (_ , sa′ , j′) = mapₚ τ (attach (u sa′) (body j′))

  π : ⊤ × Σ (S × A) J → S × A
  π = proj₁ ∘′ proj₂

  sim₁ : ∀ x → u (π x) ≈ₚ mapₚ (φ π proj₂) (uᴶ x)
  sim₁ (_ , sa′ , j′) = ≈sym (map-fuse (attach (u sa′) (body j′)) τ (φ π proj₂) proj₁
    (λ where ((_ , inj₁ _) , _) → refl ; ((_ , inj₂ _) , _) → refl) ⟨≈⟩ attach-proj (u sa′) (body j′))

  sim′ : ∀ x → u′ (k (π x)) ≈ₚ mapₚ (φ (k ∘′ π) (m ∘′ proj₂)) (uᴶ x)
  sim′ x@(_ , _ , j′) = sim j′ ⟨≈⟩ map-arg (φ k m) (sim₁ x) ⟨≈⟩ map-fuse (uᴶ x) (φ π proj₂) (φ k m) _
    λ where (_ , inj₁ _) → refl ; (_ , inj₂ _) → refl
