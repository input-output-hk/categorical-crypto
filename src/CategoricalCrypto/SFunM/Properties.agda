{-# OPTIONS --safe --without-K #-}

open import categorical-crypto.Prelude hiding (Functor)

open import Class.Core
open import Class.Monad.Ext.Setoid

open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor)

open import CategoricalCrypto.SFunM

module CategoricalCrypto.SFunM.Properties {M : Type↑}
  ⦃ Monad-M : Monad M     ⦄
  ⦃ MS      : MonadSetoid M ⦄
  ⦃ M-Laws  : MonadLawsSetoid M ⦄ where

open ≈ᴹ-Reasoning

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
  where cont = λ (t , b) → trace g t as >>= λ bs → return (b ∷ bs)

≈ᵉ-sim : {f g : SFunᵉ {M = M} A B} (φ : SFunᵉ.State f → SFunᵉ.State g)
       → φ (SFunᵉ.init f) ≡ SFunᵉ.init g
       → (∀ s a → ((λ (s′ , b) → φ s′ , b) <$>ᴹ SFunᵉ.fun f (s , a)) ≈ᴹ SFunᵉ.fun g (φ s , a))
       → f ≈ᵉ g
≈ᵉ-sim {f = f} {g} φ init≡ k xs =
  ≈ᴹ.trans (trace-sim φ k (SFunᵉ.init f) xs)
           (≈ᴹ.reflexive (cong (λ s → trace (SFunᵉ.fun g) s xs) init≡))

------------------------------------------------------------------------
-- Stateless machines

statelessᵏ : (A → B) → SFunType A B ⊤
statelessᵏ h (_ , a) = return (tt , h a)

statelessᵉ : (A → B) → SFunᵉ {M = M} A B
statelessᵉ h = mkᵉ tt (statelessᵏ h)

statelessᵉ-cong : {h k : A → B} → h ≗ k → statelessᵉ h ≈ᵉ statelessᵉ k
statelessᵉ-cong h≗k = ≈ᵉ-sim id refl λ _ a →
  ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.reflexive (cong (λ b → return (tt , b)) (h≗k a)))

statelessᵉ-∘ : (h : B → C) (k : A → B) → statelessᵉ (h ∘ k) ≈ᵉ statelessᵉ h ∘ᵉ statelessᵉ k
statelessᵉ-∘ h k = ≈ᵉ-sim (λ _ → tt , tt) refl λ _ a →
  ≈ᴹ.trans >>=-identityˡ-≈ (≈ᴹ.sym (≈ᴹ.trans >>=-identityˡ-≈ >>=-identityˡ-≈))

statelessᵉ-id : statelessᵉ {A = A} id ≈ᵉ idᵉ
statelessᵉ-id _ = ≈ᴹ.refl

statelessᵉ-postᵏ : (h : B → C) (k : SFunType A B S) (s : S) (a : A)
                 → (statelessᵏ h ∘ᵉ' k) ((tt , s) , a)
                 ≈ᴹ ((λ (s′ , b) → (tt , s′) , h b) <$>ᴹ k (s , a))
statelessᵉ-postᵏ h k s a = >>=-cong-f λ _ → >>=-identityˡ-≈

statelessᵉ-preᵏ : (h : A′ → A) (k : SFunType A B S) (s : S) (a : A′)
                → (k ∘ᵉ' statelessᵏ h) ((s , tt) , a)
                ≈ᴹ ((λ (s′ , b) → (s′ , tt) , b) <$>ᴹ k (s , h a))
statelessᵉ-preᵏ h k s a = >>=-identityˡ-≈

statelessᵉ-inv : {h : A → B} {k : B → A} → k ∘ h ≗ id → statelessᵉ k ∘ᵉ statelessᵉ h ≈ᵉ idᵉ
statelessᵉ-inv {h = h} {k} inv =
  ≈ᵉ.trans (≈ᵉ.sym (statelessᵉ-∘ k h)) (≈ᵉ.trans (statelessᵉ-cong inv) statelessᵉ-id)

statelessᵉ-natural : {f : SFunᵉ {M = M} A B} {g : SFunᵉ {M = M} A′ C}
                     (h : A → A′) (k : B → C) (ψ : SFunᵉ.State f → SFunᵉ.State g)
                   → ψ (SFunᵉ.init f) ≡ SFunᵉ.init g
                   → (∀ s a → ((λ (s′ , b) → ψ s′ , k b) <$>ᴹ SFunᵉ.fun f (s , a))
                            ≈ᴹ SFunᵉ.fun g (ψ s , h a))
                   → statelessᵉ k ∘ᵉ f ≈ᵉ g ∘ᵉ statelessᵉ h
statelessᵉ-natural {f = f} {g} h k ψ init≡ sq =
  ≈ᵉ-sim (λ (_ , s) → ψ s , tt) (cong (_, tt) init≡) λ (_ , s) a →
    ≈ᴹ.trans (<$>ᴹ-cong (statelessᵉ-postᵏ k F.fun s a))
  $ ≈ᴹ.trans (<$>ᴹ-∘ _ _ (F.fun (s , a)))
  $ ≈ᴹ.sym
  $ ≈ᴹ.trans (statelessᵉ-preᵏ h G.fun (ψ s) a)
  $ ≈ᴹ.trans (<$>ᴹ-cong (≈ᴹ.sym (sq s a))) (<$>ᴹ-∘ _ _ (F.fun (s , a)))
  where module F = SFunᵉ f; module G = SFunᵉ g

module _ ⦃ M-Comm : CommutativeMonadSetoid M ⦄ where

  statelessᵉ-Functor : Functor (Sets 0ℓ) (SFunᵉ-Category {M = M})
  statelessᵉ-Functor = record
    { F₀           = id
    ; F₁           = statelessᵉ
    ; identity     = statelessᵉ-id
    ; homomorphism = λ {_ _ _ k h} → statelessᵉ-∘ h k
    ; F-resp-≈     = statelessᵉ-cong
    }
