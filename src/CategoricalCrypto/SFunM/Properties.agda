{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (Functor)

open import Class.Core
open import Class.Monad.Ext.Setoid

open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor)

import Relation.Binary.Reasoning.Setoid as R-Setoid

open import CategoricalCrypto.SFunM

module CategoricalCrypto.SFunM.Properties {M : Type↑}
  ⦃ Monad-M : Monad M     ⦄
  ⦃ MS      : MonadSetoid M ⦄
  ⦃ M-Laws  : MonadLawsSetoid M ⦄ where

private variable A A′ B C S S′ : Type

------------------------------------------------------------------------
-- Simulation

-- A state map `φ` that intertwines the two kernels — running `f` and
-- relabelling the resulting state is running `g` on the relabelled state —
-- makes the two traces equal.
trace-sim : (φ : S → S′) {f : SFunType A B S} {g : SFunType A B S′}
          → (∀ s a → ((λ (s′ , b) → φ s′ , b) <$>ᴹ f (s , a)) ≈ᴹ g (φ s , a))
          → ∀ s xs → trace f s xs ≈ᴹ trace g (φ s) xs
trace-sim φ k s []       = ≈ᴹ.refl
trace-sim φ {f} {g} k s (a ∷ as) = begin
  (f (s , a) >>= λ (s′ , b) → trace f s′ as >>= λ bs → return (b ∷ bs))
    ≈⟨ >>=-cong-f (λ _ → >>=-cong-x (trace-sim φ k _ as)) ⟩
  (f (s , a) >>= λ (s′ , b) → trace g (φ s′) as >>= λ bs → return (b ∷ bs))
    ≈˘⟨ <$>ᴹ->>= (λ (s′ , b) → φ s′ , b) (f (s , a)) cont ⟩
  (((λ (s′ , b) → φ s′ , b) <$>ᴹ f (s , a)) >>= cont)
    ≈⟨ >>=-cong-x (k s a) ⟩
  (g (φ s , a) >>= cont) ∎
  where
    cont = λ (t , b) → trace g t as >>= λ bs → return (b ∷ bs)
    open R-Setoid ≈ᴹ-setoid

-- `trace-sim` at the initial states.
≈ᵉ-sim : {f g : SFunᵉ {M = M} A B} (φ : SFunᵉ.State f → SFunᵉ.State g)
       → φ (SFunᵉ.init f) ≡ SFunᵉ.init g
       → (∀ s a → ((λ (s′ , b) → φ s′ , b) <$>ᴹ SFunᵉ.fun f (s , a)) ≈ᴹ SFunᵉ.fun g (φ s , a))
       → f ≈ᵉ g
≈ᵉ-sim {f = f} {g} φ init≡ k xs =
  ≈ᴹ.trans (trace-sim φ k (SFunᵉ.init f) xs)
           (≈ᴹ.reflexive (cong (λ s → trace (SFunᵉ.fun g) s xs) init≡))

------------------------------------------------------------------------
-- Stateless machines

statelessᵉ : (A → B) → SFunᵉ {M = M} A B
statelessᵉ h = record { State = ⊤ ; init = tt ; fun = λ (_ , a) → return (tt , h a) }

statelessᵉ-cong : {h k : A → B} → h ≗ k → statelessᵉ h ≈ᵉ statelessᵉ k
statelessᵉ-cong h≗k = ≈ᵉ-sim id refl λ _ a →
  ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.reflexive (cong (λ b → return (tt , b)) (h≗k a)))

statelessᵉ-∘ : (h : B → C) (k : A → B) → statelessᵉ (h ∘ k) ≈ᵉ (statelessᵉ h ∘ᵉ statelessᵉ k)
statelessᵉ-∘ h k = ≈ᵉ-sim (λ _ → tt , tt) refl λ _ a →
  ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.sym (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈))

statelessᵉ-id : statelessᵉ {A = A} id ≈ᵉ idᵉ
statelessᵉ-id _ = ≈ᴹ.refl

-- Composing with a stateless machine leaves the kernel of the other factor
-- alone: it only relabels the output, resp. the input.
statelessᵉ-postᵏ : (h : B → C) (k : SFunType A B S) (s : S) (a : A)
                 → (SFunᵉ.fun (statelessᵉ h) ∘ᵉ' k) ((tt , s) , a)
                 ≈ᴹ ((λ (s′ , b) → (tt , s′) , h b) <$>ᴹ k (s , a))
statelessᵉ-postᵏ h k s a = >>=-cong-f λ _ → >>=-identityˡ-≈

statelessᵉ-preᵏ : (h : A′ → A) (k : SFunType A B S) (s : S) (a : A′)
                → (k ∘ᵉ' SFunᵉ.fun (statelessᵉ h)) ((s , tt) , a)
                ≈ᴹ ((λ (s′ , b) → (s′ , tt) , b) <$>ᴹ k (s , h a))
statelessᵉ-preᵏ h k s a = >>=-identityˡ-≈

module _ ⦃ M-Comm : CommutativeMonadSetoid M ⦄ where

  statelessᵉ-Functor : Functor (Sets 0ℓ) (SFunᵉ-Category {M = M})
  statelessᵉ-Functor = record
    { F₀           = id
    ; F₁           = statelessᵉ
    ; identity     = statelessᵉ-id
    ; homomorphism = λ {_ _ _ k h} → statelessᵉ-∘ h k
    ; F-resp-≈     = statelessᵉ-cong
    }
