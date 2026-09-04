{-# OPTIONS --safe --without-K --guardedness #-}

-- Elgot iteration on the Kleisli category of `Dₚ`, elementwise.  A body
-- `S × A → Dₚ (S × (B ⊎ A))` is iterated by guarded corecursion, one step per turn
-- of the loop, so `iterₚ` is total even when the loop is not.
--
-- Convergence here is quantitative: there is no `_⇓_` derivation to induct on, so
-- every law is an induction on the BUDGET, and the two bounds
-- `stepᵢ-boundA`/`stepᵢ-boundB` sandwich a loop's depth-`n` mass between `cum`s of
-- its body.  The budget decrement is also what makes `iterₚ-cong` well-founded
-- rather than circular: the test `Tᵗ u P n` a loop is measured against uses budget
-- `n`, one less than the loop's own.
--
-- Bodies, delays and continuations are explicit arguments throughout; that is what
-- keeps the modules of this hierarchy elaborating in seconds.

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤n+m; n≤1+n)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ)
open import Data.Rational.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; cong₂)

open import ProbabilisticLogic.Dp

module ProbabilisticLogic.Dp.Iter where

private variable
  ℓ : Level
  S A B S′ A′ B′ : Set ℓ
  j k : ℕ

------------------------------------------------------------------------
-- `mapₚ`, exactly

mutual
  mapₚ-cum : (n : ℕ) (h : A → B) (d : Dₚ A) (P : B → ℚ)
           → cum (suc n) (mapₚ h d) P ≡ cum n d (P ∘′ h)
  mapₚ-cum zero    h d P = cum-1-bind d (returnₚ ∘′ h) P
  mapₚ-cum (suc n) h d P =
    cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-mapₚ n h (br d true) P))
                (cong (wt d false ℚ.*_) (leafₚ-mapₚ n h (br d false) P))

  leafₚ-mapₚ : (n : ℕ) (h : A → B) (x : A ⊎ Dₚ A) (P : B → ℚ)
             → leafₚ (suc n) (tagₚ x (returnₚ ∘′ h)) P ≡ leafₚ n x (P ∘′ h)
  leafₚ-mapₚ n h (inj₁ p)  P = returnₚ-cum n (h p) P
  leafₚ-mapₚ n h (inj₂ d′) P = mapₚ-cum n h d′ P

mapₚ-≈ₚ : (h : A → B) (d : Dₚ A) (e : Dₚ A) → d ≈ₚ e → mapₚ h d ≈ₚ mapₚ h e
mapₚ-≈ₚ h d e de = >>=ₚ-cong d e (returnₚ ∘′ h) (returnₚ ∘′ h) de λ p → ≈ₚ-refl (returnₚ (h p))

------------------------------------------------------------------------
-- The operator

Body : (S A B : Set ℓ) → Set ℓ
Body S A B = S × A → Dₚ (S × (B ⊎ A))

-- `stepᵢ` consumes the body's own steps and adds one per turn, so the only
-- self-call is guarded and `iterₚ` needs no corecursion of its own.
mutual
  stepᵢ : Body S A B → Dₚ (S × (B ⊎ A)) → Dₚ (S × B)
  wt    (stepᵢ u x)   = wt x
  wt-nn (stepᵢ u x)   = wt-nn x
  wt-1  (stepᵢ u x)   = wt-1 x
  br    (stepᵢ u x) c = tagᵢ u (br x c)

  tagᵢ : Body S A B → (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)) → (S × B) ⊎ Dₚ (S × B)
  tagᵢ u (inj₁ (s , inj₁ b)) = inj₁ (s , b)
  tagᵢ u (inj₁ (s , inj₂ p)) = inj₂ (stepᵢ u (u (s , p)))
  tagᵢ u (inj₂ x′)           = inj₂ (stepᵢ u x′)

iterₚ : Body S A B → S × A → Dₚ (S × B)
iterₚ u sa = stepᵢ u (u sa)

------------------------------------------------------------------------
-- Unfolding (the fixpoint law)

contᵢ : Body S A B → S × (B ⊎ A) → Dₚ (S × B)
contᵢ u (s , inj₁ b) = returnₚ (s , b)
contᵢ u (s , inj₂ p) = iterₚ u (s , p)

-- `returnₚ` is only reached after a step, so budget 0 sees nothing of it.
returnₚ-cum-≤ : (n : ℕ) (q : A) (P : A → ℚ) → NNF P → cum n (returnₚ q) P ℚ.≤ P q
returnₚ-cum-≤ zero    q P nn = nn q
returnₚ-cum-≤ (suc n) q P nn = ≤-reflexive (returnₚ-cum n q P)

-- The unfolded loop is behind by exactly the one step the junction spends.
mutual
  stepᵢ-≤-unfold : (n : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A))) (P : S × B → ℚ) → NNF P
                 → cum n (stepᵢ u x) P ℚ.≤ cum (suc n) (x >>=ₚ contᵢ u) P
  stepᵢ-≤-unfold zero    u x P nn = cum-nn 1 (x >>=ₚ contᵢ u) P nn
  stepᵢ-≤-unfold (suc n) u x P nn =
    node-mono (wt x true) (wt x false) (wt-nn x true) (wt-nn x false)
               (leafᵢ-≤-unfold n u (br x true) P nn) (leafᵢ-≤-unfold n u (br x false) P nn)

  leafᵢ-≤-unfold : (n : ℕ) (u : Body S A B) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
                   (P : S × B → ℚ) → NNF P
                 → leafₚ n (tagᵢ u y) P ℚ.≤ leafₚ (suc n) (tagₚ y (contᵢ u)) P
  leafᵢ-≤-unfold n u (inj₁ (s , inj₁ b)) P nn = ≤-reflexive (sym (returnₚ-cum n (s , b) P))
  leafᵢ-≤-unfold n u (inj₁ (s , inj₂ p)) P nn = cum-mono (n≤1+n n) (iterₚ u (s , p)) P nn
  leafᵢ-≤-unfold n u (inj₂ x′)           P nn = stepᵢ-≤-unfold n u x′ P nn

mutual
  unfold-≤-stepᵢ : (n : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A))) (P : S × B → ℚ) → NNF P
                 → cum n (x >>=ₚ contᵢ u) P ℚ.≤ cum n (stepᵢ u x) P
  unfold-≤-stepᵢ zero    u x P nn = ≤-refl
  unfold-≤-stepᵢ (suc n) u x P nn =
    node-mono (wt x true) (wt x false) (wt-nn x true) (wt-nn x false)
               (leafᵢ-unfold-≤ n u (br x true) P nn) (leafᵢ-unfold-≤ n u (br x false) P nn)

  leafᵢ-unfold-≤ : (n : ℕ) (u : Body S A B) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
                   (P : S × B → ℚ) → NNF P
                 → leafₚ n (tagₚ y (contᵢ u)) P ℚ.≤ leafₚ n (tagᵢ u y) P
  leafᵢ-unfold-≤ n u (inj₁ (s , inj₁ b)) P nn = returnₚ-cum-≤ n (s , b) P nn
  leafᵢ-unfold-≤ n u (inj₁ (s , inj₂ p)) P nn = ≤-refl
  leafᵢ-unfold-≤ n u (inj₂ x′)           P nn = unfold-≤-stepᵢ n u x′ P nn

iterₚ-fix : (u : Body S A B) (sa : S × A) → iterₚ u sa ≈ₚ (u sa >>=ₚ contᵢ u)
iterₚ-fix u sa =
    (λ P nn n → suc n , stepᵢ-≤-unfold n u (u sa) P nn)
  , λ P nn n → n , unfold-≤-stepᵢ n u (u sa) P nn

------------------------------------------------------------------------
-- The loop sandwich
--
-- `Tᵗ u P j` is the test that reads a body's output: a result is scored by `P`, a
-- new loop variable by what the loop does from there within budget `j`.

Tᵗ : Body S A B → (S × B → ℚ) → ℕ → S × (B ⊎ A) → ℚ
Tᵗ u P j (s , inj₁ b) = P (s , b)
Tᵗ u P j (s , inj₂ p) = cum j (iterₚ u (s , p)) P

Tᵗ-nn : (u : Body S A B) (P : S × B → ℚ) (j : ℕ) → NNF P → NNF (Tᵗ u P j)
Tᵗ-nn u P j nn (s , inj₁ b) = nn (s , b)
Tᵗ-nn u P j nn (s , inj₂ p) = cum-nn j (iterₚ u (s , p)) P nn

Tᵗ-mono : (u : Body S A B) (P : S × B → ℚ) → NNF P → j ≤ℕ k
        → ∀ r → Tᵗ u P j r ℚ.≤ Tᵗ u P k r
Tᵗ-mono u P nn le (s , inj₁ b) = ≤-refl
Tᵗ-mono u P nn le (s , inj₂ p) = cum-mono le (iterₚ u (s , p)) P nn

mutual
  stepᵢ-boundA : (n : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A))) (P : S × B → ℚ) → NNF P
               → cum (suc n) (stepᵢ u x) P ℚ.≤ cum (suc n) x (Tᵗ u P n)
  stepᵢ-boundA n u x P nn =
    node-mono (wt x true) (wt x false) (wt-nn x true) (wt-nn x false)
               (leafᵢ-boundA n u (br x true) P nn) (leafᵢ-boundA n u (br x false) P nn)

  leafᵢ-boundA : (n : ℕ) (u : Body S A B) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
                 (P : S × B → ℚ) → NNF P
               → leafₚ n (tagᵢ u y) P ℚ.≤ leafₚ n y (Tᵗ u P n)
  leafᵢ-boundA n       u (inj₁ (s , inj₁ b)) P nn = ≤-refl
  leafᵢ-boundA n       u (inj₁ (s , inj₂ p)) P nn = ≤-refl
  leafᵢ-boundA zero    u (inj₂ x′)           P nn = ≤-refl
  leafᵢ-boundA (suc n) u (inj₂ x′)           P nn =
    ≤-trans (stepᵢ-boundA n u x′ P nn)
            (cum-mono-P (suc n) x′ (Tᵗ u P n) (Tᵗ u P (suc n)) (Tᵗ-mono u P nn (n≤1+n n)))

mutual
  stepᵢ-boundB : (n m : ℕ) (u : Body S A B) (x : Dₚ (S × (B ⊎ A))) (P : S × B → ℚ) → NNF P
               → cum n x (Tᵗ u P m) ℚ.≤ cum (n +ℕ m) (stepᵢ u x) P
  stepᵢ-boundB zero    m u x P nn = cum-nn m (stepᵢ u x) P nn
  stepᵢ-boundB (suc n) m u x P nn =
    node-mono (wt x true) (wt x false) (wt-nn x true) (wt-nn x false)
               (leafᵢ-boundB n m u (br x true) P nn) (leafᵢ-boundB n m u (br x false) P nn)

  leafᵢ-boundB : (n m : ℕ) (u : Body S A B) (y : (S × (B ⊎ A)) ⊎ Dₚ (S × (B ⊎ A)))
                 (P : S × B → ℚ) → NNF P
               → leafₚ n y (Tᵗ u P m) ℚ.≤ leafₚ (n +ℕ m) (tagᵢ u y) P
  leafᵢ-boundB n m u (inj₁ (s , inj₁ b)) P nn = ≤-refl
  leafᵢ-boundB n m u (inj₁ (s , inj₂ p)) P nn = cum-mono (m≤n+m m n) (iterₚ u (s , p)) P nn
  leafᵢ-boundB n m u (inj₂ x′)           P nn = stepᵢ-boundB n m u x′ P nn

------------------------------------------------------------------------
-- `iterₚ` respects `_≈ₚ_` in its body

-- `S`/`A`/`B` are module parameters, not `private variable`s: the `where` block's
-- own signatures mention them, and a `variable` there re-generalizes at a fresh
-- level.
module _ {S A B : Set ℓ} (u u′ : Body S A B) (h : ∀ sa → u sa ≼ₚ u′ sa) where

  iterₚ-congᵖ : (n : ℕ) (sa : S × A) (P : S × B → ℚ) → NNF P
              → Σ[ m ∈ ℕ ] (cum n (iterₚ u sa) P ℚ.≤ cum m (iterₚ u′ sa) P)
  iterₚ-congᵖ zero    sa P nn = 0 , ≤-refl
  iterₚ-congᵖ (suc n) sa P nn =
    let i  , le = h sa (Tᵗ u P n) (Tᵗ-nn u P n nn) (suc n)
        i′ , sp = uniformize Φ up wit i (u′ sa)
    in i +ℕ i′
     , ≤-trans (stepᵢ-boundA n u (u sa) P nn)
       (≤-trans le
       (≤-trans (cum-mono-Supp i (u′ sa) (Tᵗ u P n) (Tᵗ u′ P i′) sp)
                (stepᵢ-boundB i i′ u′ (u′ sa) P nn)))
    where
    Φ : S × (B ⊎ A) → ℕ → Set
    Φ r i = Tᵗ u P n r ℚ.≤ Tᵗ u′ P i r

    up : ∀ r {i i′} → i ≤ℕ i′ → Φ r i → Φ r i′
    up (s , inj₁ b) le q = q
    up (s , inj₂ p) le q = ≤-trans q (cum-mono le (iterₚ u′ (s , p)) P nn)

    wit : ∀ r → Σ[ i ∈ ℕ ] Φ r i
    wit (s , inj₁ b) = 0 , ≤-refl
    wit (s , inj₂ p) = iterₚ-congᵖ n (s , p) P nn

  iterₚ-≼ : (sa : S × A) → iterₚ u sa ≼ₚ iterₚ u′ sa
  iterₚ-≼ sa P nn n = iterₚ-congᵖ n sa P nn

iterₚ-cong : (u u′ : Body S A B) → (∀ sa → u sa ≈ₚ u′ sa)
           → (sa : S × A) → iterₚ u sa ≈ₚ iterₚ u′ sa
iterₚ-cong u u′ h sa =
    iterₚ-≼ u u′ (λ sa′ → proj₁ (h sa′)) sa
  , iterₚ-≼ u′ u (λ sa′ → proj₂ (h sa′)) sa

------------------------------------------------------------------------
-- Pure reindexings of a body's output
--
-- `φ` relabels along a pair of pure maps; `flat` is the codiagonal
-- `∇ = [ id , i₂ ]` on the two copies of the loop variable.  `Dp.Iter.Transfer`
-- and `Dp.Iter.Codiagonal` are what spend them.

φ : (S × A → S′ × A′) → (S × B → S′ × B′) → S × (B ⊎ A) → S′ × (B′ ⊎ A′)
φ k m (s , inj₁ b) = proj₁ (m (s , b)) , inj₁ (proj₂ (m (s , b)))
φ k m (s , inj₂ p) = proj₁ (k (s , p)) , inj₂ (proj₂ (k (s , p)))

flat : S × ((B ⊎ A) ⊎ A) → S × (B ⊎ A)
flat (s , inj₁ x) = s , x
flat (s , inj₂ p) = s , inj₂ p

------------------------------------------------------------------------
-- Replaying a deterministic loop
--
-- A body that answers with a `returnₚ` at every turn — what a clocked machine's
-- run looks like inside `Dₚ`.  These replay such a run one turn at a time.

iterₚ-turn : (u : Body S A B) (sa : S × A) (s : S) (p : A) → u sa ≡ returnₚ (s , inj₂ p)
           → iterₚ u sa ≈ₚ iterₚ u (s , p)
iterₚ-turn u sa s p eq = shift⇒≈ₚ (iterₚ u sa) (iterₚ u (s , p)) λ P n →
  trans (cong (λ x → cum (suc n) (stepᵢ u x) P) eq)
        (node-dirac (cum n (iterₚ u (s , p)) P) (cum n (iterₚ u (s , p)) P))

iterₚ-done : (u : Body S A B) (sa : S × A) (s : S) (r : B) → u sa ≡ returnₚ (s , inj₁ r)
           → iterₚ u sa ≈ₚ returnₚ (s , r)
iterₚ-done u sa s r eq = exactˢ⇒≈ₚ (iterₚ u sa) (returnₚ (s , r)) λ P n →
  trans (trans (cong (λ x → cum (suc n) (stepᵢ u x) P) eq)
               (node-dirac (P (s , r)) (P (s , r))))
        (sym (returnₚ-cum n (s , r) P))
