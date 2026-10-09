{-# OPTIONS --safe --without-K --guardedness #-}

-- The ⊕-trace absorbed (`Behaviour.Absorb`): the distinguisher re-asks the
-- traced machine's loop letters itself, at most `n` times per activation.  Each
-- `iterₚ` turn costs the traced run a level (`Dp.Iter`), so the loop sandwich is
-- `iterₚ-congᵖ`'s.

open import Data.Bool.Base
open import Data.Nat.Base renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤n+m)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level using (0ℓ)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Behaviour.Absorb
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Trace as MTrace

module CategoricalCrypto.UC.Machine.Behaviour.Trace where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = MTrace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)
  variable A B X : Set

------------------------------------------------------------------------
-- The distinguisher

-- One activation's loop: each loop letter re-asked, at most `u` times.
loop : ℕ → Bool → (B → Strat (A ⊎ X) (B ⊎ X)) → B ⊎ X → Strat (A ⊎ X) (B ⊎ X)
loop u       v κ (inj₁ y) = κ y
loop zero    v κ (inj₂ x) = out v
loop (suc u) v κ (inj₂ x) = ask (inj₂ x) (loop u v κ)

traceˢ : Strat A B → Bool → ℕ → Strat (A ⊎ X) (B ⊎ X)
traceˢ (out c)    b n = out c
traceˢ (coin μ k) b n = coin μ λ c → traceˢ (k c) b n
traceˢ (ask a k)  b n = ask (inj₁ a) (loop n (not b) λ y → traceˢ (k y) b n)

------------------------------------------------------------------------
-- The traced run, its junctions absorbed

module _ (f : MC.Machine (A ⊎ X) (B ⊎ X)) where

  lbᶜ : Body (MC.St f) X B
  lbᶜ (s , x) = MC.step f (s , inj₂ x)

  trace-step : (s : MC.St f) (a : A)
             → MC.step (MT.traceᴹ A B X f) (s , a) ≈ₚ (MC.step f (s , inj₁ a) >>=ₚ contᵢ lbᶜ)
  trace-step s a = bindˣ (enter-pure inj₁ (MC.step f) s a)
               ⟨≈⟩ bindᶠ (λ r → Elgotᵏ.δ⇐-contᵢ 0ℓ lb r ⟨≈⟩ cont-cong r)
    where
    lb : Body (MC.St f) X B
    lb = MT.loopBody (MC.state f) A B X (MC.step f)

    cont-cong : (r : MC.St f × (B ⊎ X)) → contᵢ lb r ≈ₚ contᵢ lbᶜ r
    cont-cong (_  , inj₁ _) = ≈refl
    cont-cong (s′ , inj₂ x) =
      iterₚ-cong lb lbᶜ (λ p → enter-pure inj₂ (MC.step f) (proj₁ p) (proj₂ p)) (s′ , x)

  module _ (k : B → Strat A B) where

    exitᶜ : MC.St f × B → Dₚ Bool
    exitᶜ (s , y) = runFromˢ (MT.traceᴹ A B X f) s (k y)

    resolve : MC.St f × (B ⊎ X) → Dₚ Bool
    resolve (s , inj₁ y) = exitᶜ (s , y)
    resolve (s , inj₂ x) = iterₚ lbᶜ (s , x) >>=ₚ exitᶜ

    trace-run : (s : MC.St f) (a : A)
              → runFromˢ (MT.traceᴹ A B X f) s (ask a k) ≈ₚ (MC.step f (s , inj₁ a) >>=ₚ resolve)
    trace-run s a = bindˣ (trace-step s a) ⟨≈⟩ >>=ₚ-assoc (MC.step f (s , inj₁ a)) (contᵢ lbᶜ) exitᶜ
                ⟨≈⟩ bindᶠ λ where
                      (s′ , inj₁ y) → >>=ₚ-identityˡ (s′ , y) exitᶜ
                      (_  , inj₂ _) → ≈refl

------------------------------------------------------------------------
-- The loop sandwich

module _ (b : Bool) (f : MC.Machine (A ⊎ X) (B ⊎ X)) (κ : ℕ → B → Strat (A ⊎ X) (B ⊎ X))
         (H : MC.St f × B → Dₚ Bool)
         (ex : (s : MC.St f) (y : B) → Approximation.Approx b (λ n → runFromˢ f s (κ n y)) (H (s , y)))
         where
  open Approximation b

  private
    L : ℕ → ℕ → MC.St f → X → Dₚ Bool
    L u n s x = runFromˢ f s (loop u (not b) (κ n) (inj₂ x))

    cont : ℕ → ℕ → MC.St f × (B ⊎ X) → Dₚ Bool
    cont u n (s , z) = runFromˢ f s (loop u (not b) (κ n) z)

    loop-mono : {u u′ n n′ : ℕ} → u ≤ℕ u′ → n ≤ℕ n′ → (s : MC.St f) (x : X) (j : ℕ)
              → cum j (L u n s x) χ ℚ.≤ cum j (L u′ n′ s x) χ
    loop-mono {u′ = u′} {n′ = n′} z≤n _ s x j = ≤-trans (cut-zero j) (cum-nn j (L u′ n′ s x) χ χ-nn)
    loop-mono {suc u} {suc u′} {n} {n′} (s≤s le) le′ s x j = bind-mono branch j (MC.step f (s , inj₂ x))
      where
      branch : (r : MC.St f × (B ⊎ X)) (i : ℕ) → cum i (cont u n r) χ ℚ.≤ cum i (cont u′ n′ r) χ
      branch (s′ , inj₁ y)  i = mono (ex s′ y) le′ i
      branch (s′ , inj₂ x′) i = loop-mono le le′ s′ x′ i

    loop-lower : (j : ℕ) (s : MC.St f) (x : X)
               → Σ[ w ∈ ℕ ] cum j (iterₚ (lbᶜ f) (s , x) >>=ₚ H) χ ℚ.≤ cum w (L w w s x) χ
    loop-lower j s x = let w , h = inner j (s , x)
                       in w , ≤-trans (>>=ₚ-boundA j (iterₚ (lbᶜ f) (s , x)) H χ χ-nn) h
      where
      Tj : MC.St f × B → ℚ
      Tj r = cum j (H r) χ

      Tj-nn : NNF Tj
      Tj-nn r = cum-nn j (H r) χ χ-nn

      inner : (i : ℕ) (sx : MC.St f × X)
            → Σ[ w ∈ ℕ ] cum i (iterₚ (lbᶜ f) sx) Tj ℚ.≤ cum w (L w w (proj₁ sx) (proj₂ sx)) χ
      inner zero    sx = 0 , ≤-refl
      inner (suc i) sx =
        let w , sp = uniformize Φ up wit (suc i) (lbᶜ f sx)
        in suc i +ℕ w
         , ≤-trans (stepᵢ-boundA i (lbᶜ f) (lbᶜ f sx) Tj Tj-nn)
           (≤-trans (cum-mono-Supp (suc i) (lbᶜ f sx) (Tᵗ (lbᶜ f) Tj i) (λ r → cum w (cont w w r) χ) sp)
           (≤-trans (>>=ₚ-boundB (suc i) w (lbᶜ f sx) (cont w w) χ χ-nn)
                    (loop-mono (s≤s (m≤n+m w i)) (m≤n+m w (suc i)) (proj₁ sx) (proj₂ sx) (suc i +ℕ w))))
        where
        Φ : MC.St f × (B ⊎ X) → ℕ → Set
        Φ r w = Tᵗ (lbᶜ f) Tj i r ℚ.≤ cum w (cont w w r) χ

        up : (r : MC.St f × (B ⊎ X)) {w w′ : ℕ} → w ≤ℕ w′ → Φ r w → Φ r w′
        up (s′ , inj₁ y)  {w} {w′} le h =
          ≤-trans h (≤-trans (mono (ex s′ y) le w) (cum-mono le (runFromˢ f s′ (κ w′ y)) χ χ-nn))
        up (s′ , inj₂ x′) {w} {w′} le h =
          ≤-trans h (≤-trans (loop-mono le le s′ x′ w) (cum-mono le (L w′ w′ s′ x′) χ χ-nn))

        wit : (r : MC.St f × (B ⊎ X)) → Σ[ w ∈ ℕ ] Φ r w
        wit (s′ , inj₁ y)  =
          let n , M , h = lower (ex s′ y) j
          in n ⊔ M , ≤-trans h (≤-trans (mono (ex s′ y) (m≤m⊔n n M) M)
                                        (cum-mono (m≤n⊔m n M) (runFromˢ f s′ (κ (n ⊔ M) y)) χ χ-nn))
        wit (s′ , inj₂ x′) = inner i (s′ , x′)

    loop-upper : (n u : ℕ) (s : MC.St f) (x : X)
               → Cofinal χ χ (L u n s x) (iterₚ (lbᶜ f) (s , x) >>=ₚ H)
    loop-upper n zero    s x j = 0 , cut-zero j
    loop-upper n (suc u) s x =
      cofinal-trans (L (suc u) n s x) (lbᶜ f (s , x) >>=ₚ next) (iterₚ (lbᶜ f) (s , x) >>=ₚ H)
        (bind-cofinal (lbᶜ f (s , x)) branch)
        (≈ₚ⇒cofinal χ χ-nn (≈sym (bindˣ (iterₚ-fix (lbᶜ f) (s , x))
                                  ⟨≈⟩ >>=ₚ-assoc (lbᶜ f (s , x)) (contᵢ (lbᶜ f)) H)))
      where
      next : MC.St f × (B ⊎ X) → Dₚ Bool
      next r = contᵢ (lbᶜ f) r >>=ₚ H

      branch : (r : MC.St f × (B ⊎ X)) → Cofinal χ χ (cont u n r) (next r)
      branch (s′ , inj₁ y)  =
        cofinal-trans (runFromˢ f s′ (κ n y)) (H (s′ , y)) (next (s′ , inj₁ y)) (upper (ex s′ y) n)
                      (≈ₚ⇒cofinal χ χ-nn (≈sym (>>=ₚ-identityˡ (s′ , y) H)))
      branch (s′ , inj₂ x′) = loop-upper n u s′ x′

  loop-approx : (s : MC.St f) (x : X)
              → Approx (λ n → runFromˢ f s (loop n (not b) (κ n) (inj₂ x))) (iterₚ (lbᶜ f) (s , x) >>=ₚ H)
  loop-approx s x = record
    { mono  = λ le → loop-mono le le s x
    ; lower = λ j → let w , h = loop-lower j s x in w , w , h
    ; upper = λ n → loop-upper n n s x
    }

------------------------------------------------------------------------
-- The trace, absorbed

module _ (f : MC.Machine (A ⊎ X) (B ⊎ X)) (b : Bool) where
  open Approximation b

  trace-approx : (d : Strat A B) (s : MC.St f)
               → Approx (λ n → runFromˢ f s (traceˢ d b n)) (runFromˢ (MT.traceᴹ A B X f) s d)
  trace-approx (out c)    s = approx-ret c
  trace-approx (coin μ k) s = approx-bind (coinₚ μ) λ c → trace-approx (k c) s
  trace-approx (ask a k)  s =
    approx-≈ (approx-bind (MC.step f (s , inj₁ a)) {H = resolve f k} branch) (≈sym (trace-run f k s a))
    where
    branch : (r : MC.St f × (B ⊎ X))
           → Approx (λ n → runFromˢ f (proj₁ r) (loop n (not b) (λ y → traceˢ (k y) b n) (proj₂ r)))
                    (resolve f k r)
    branch (s′ , inj₁ y) = trace-approx (k y) s′
    branch (s′ , inj₂ x) =
      loop-approx b f (λ n y → traceˢ (k y) b n) (exitᶜ f k) (λ s″ y → trace-approx (k y) s″) s′ x

traceᴹ-absorb : Absorbs (MT.traceᴹ A B X)
traceᴹ-absorb = approx⇒absorbs traceˢ λ f d b →
  Approximation.approx-bind b (MC.point (MC.state f) tt) λ s → trace-approx f b d s
