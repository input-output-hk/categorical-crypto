{-# OPTIONS --safe --without-K --guardedness #-}

-- A context a distinguisher can simulate preserves Δ = 0: maurer2002 Lemma
-- 5(ii), maurer2011cc Lemma 1, constructively.  `Strat` is well-founded while a
-- context may loop or diverge, so the simulating strategy is cut off at a
-- budget with the verdict `not b`, which the `b`-mass does not see: the cut-off
-- runs approximate the context's run from below (`Approx`), the situation
-- `Dp.Dominate` was written for.  See docs/uc-setup-random-systems.md §3.3.

open import Data.Bool.Base
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Data.Rational.Properties
open import Data.Sum.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality hiding ([_])
import Data.List.NonEmpty as NE
import Data.List.Relation.Unary.All as All

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import Relation.Binary.Structures as Structures

module CategoricalCrypto.UC.Machine.Behaviour.Absorb where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MS = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  variable
    X Y X′ Y′ X″ Y″ Z : Set

------------------------------------------------------------------------
-- A `Dₚ` tree as strategy coins

wtᴰ : Dₚ Z → Dist-ℚ Bool
wtᴰ e = mk-Dist ((wt e true , true) NE.∷ (wt e false , false) ∷ [])
                (trans (cong (wt e true ℚ.+_) (+-identityʳ (wt e false))) (wt-1 e))
                (wt-nn e true All.∷ wt-nn e false All.∷ All.[])

E-wtᴰ : (e : Dₚ Z) (P : Bool → ℚ) → E (wtᴰ e) P ≡ wt e true ℚ.* P true ℚ.+ wt e false ℚ.* P false
E-wtᴰ e P = cong (wt e true ℚ.* P true ℚ.+_) (+-identityʳ (wt e false ℚ.* P false))

-- At most `u` levels of `e`, each node a coin; a leaf continues with `κ`, the
-- budget's end answers `v`.  Recursion on the budget, as `Dp.flatten`.
unfoldˢ : ℕ → Bool → Dₚ Z → (Z → Strat X Y) → Strat X Y
unfoldˢ zero    v e κ = out v
unfoldˢ (suc u) v e κ = coin (wtᴰ e) λ c → [ κ , (λ e′ → unfoldˢ u v e′ κ) ] (br e c)

------------------------------------------------------------------------
-- Approximation from below in the `b`-mass

module Approximation (b : Bool) where

  χ : Bool → ℚ
  χ = indᵇ b

  χ-nn : NNF χ
  χ-nn = indᵇ-nn b

  cut-zero : (j : ℕ) → cum j (returnₚ (not b)) χ ℚ.≤ 0ℚ
  cut-zero zero    = ≤-refl
  cut-zero (suc j) = ≤-reflexive (trans (returnₚ-cum j (not b) χ) (indᵇ-not b))

  Mono : (ℕ → Dₚ Bool) → Set
  Mono F = {n n′ : ℕ} → n ≤ℕ n′ → (j : ℕ) → cum j (F n) χ ℚ.≤ cum j (F n′) χ

  -- The budget-`n` cut-offs `F n` of a run `D`: monotone in the budget, each
  -- below `D`, and cofinal in it.
  record Approx (F : ℕ → Dₚ Bool) (D : Dₚ Bool) : Set where
    field
      mono  : Mono F
      lower : (j : ℕ) → Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] cum j D χ ℚ.≤ cum m (F n) χ
      upper : (n : ℕ) → Cofinal χ χ (F n) D

  open Approx public

  mutual
    bind-mono : {K K′ : Z → Dₚ Bool} → (∀ z j → cum j (K z) χ ℚ.≤ cum j (K′ z) χ)
              → (j : ℕ) (e : Dₚ Z) → cum j (e >>=ₚ K) χ ℚ.≤ cum j (e >>=ₚ K′) χ
    bind-mono h zero    e = ≤-refl
    bind-mono h (suc j) e =
      node-mono (wt e true) (wt e false) (wt-nn e true) (wt-nn e false)
                (leaf-mono h j (br e true)) (leaf-mono h j (br e false))

    leaf-mono : {K K′ : Z → Dₚ Bool} → (∀ z j → cum j (K z) χ ℚ.≤ cum j (K′ z) χ)
              → (j : ℕ) (x : Z ⊎ Dₚ Z) → leafₚ j (tagₚ x K) χ ℚ.≤ leafₚ j (tagₚ x K′) χ
    leaf-mono h j (inj₁ z)  = h z j
    leaf-mono h j (inj₂ e′) = bind-mono h j e′

  approx-ret : (c : Bool) → Approx (λ _ → returnₚ c) (returnₚ c)
  approx-ret c = record
    { mono = λ _ _ → ≤-refl ; lower = λ j → 0 , j , ≤-refl
    ; upper = λ _ → cofinal-refl χ (returnₚ c) }

  approx-≈ : {F : ℕ → Dₚ Bool} {D D′ : Dₚ Bool} → Approx F D → D ≈ₚ D′ → Approx F D′
  approx-≈ {F} {D} {D′} a eq = record
    { mono  = mono a
    ; lower = λ j → let j′ , le = proj₂ eq χ χ-nn j ; n , m , le′ = lower a j′
                    in n , m , ≤-trans le le′
    ; upper = λ n → cofinal-trans (F n) D D′ (upper a n) (proj₁ eq χ χ-nn) }

  -- A bind the cut-off and the run share: `uniformize` picks one budget for the
  -- finitely many values the depth-`j` support reaches, as in `>>=ₚ-congᵖ`.
  approx-bind : (e : Dₚ Z) {K : ℕ → Z → Dₚ Bool} {H : Z → Dₚ Bool}
              → (∀ z → Approx (λ n → K n z) (H z)) → Approx (λ n → e >>=ₚ K n) (e >>=ₚ H)
  approx-bind {Z} e {K} {H} a = record
    { mono  = λ le j → bind-mono (λ z → mono (a z) le) j e
    ; lower = λ j → let i , sp = uniformize (Φ j) (up j) (wit j) j e
                    in i , j +ℕ i
                     , ≤-trans (>>=ₚ-boundA j e H χ χ-nn)
                       (≤-trans (cum-mono-Supp j e (λ z → cum j (H z) χ) (λ z → cum i (K i z) χ) sp)
                                (>>=ₚ-boundB j i e (K i) χ χ-nn))
    ; upper = λ n j → let i , sp = uniformize (Ψ n j) (up′ n j) (λ z → upper (a z) n j) j e
                      in j +ℕ i
                       , ≤-trans (>>=ₚ-boundA j e (K n) χ χ-nn)
                         (≤-trans (cum-mono-Supp j e (λ z → cum j (K n z) χ) (λ z → cum i (H z) χ) sp)
                                  (>>=ₚ-boundB j i e H χ χ-nn)) }
    where
    Φ : ℕ → Z → ℕ → Set
    Φ j z i = cum j (H z) χ ℚ.≤ cum i (K i z) χ

    up : (j : ℕ) (z : Z) {i i′ : ℕ} → i ≤ℕ i′ → Φ j z i → Φ j z i′
    up j z {i} {i′} le h = ≤-trans h (≤-trans (mono (a z) le i) (cum-mono le (K i′ z) χ χ-nn))

    wit : (j : ℕ) (z : Z) → Σ[ i ∈ ℕ ] Φ j z i
    wit j z = let n , m , h = lower (a z) j
              in n ⊔ m , ≤-trans h (≤-trans (mono (a z) (m≤m⊔n n m) m)
                                            (cum-mono (m≤n⊔m n m) (K (n ⊔ m) z) χ χ-nn))

    Ψ : ℕ → ℕ → Z → ℕ → Set
    Ψ n j z i = cum j (K n z) χ ℚ.≤ cum i (H z) χ

    up′ : (n j : ℕ) (z : Z) {i i′ : ℕ} → i ≤ℕ i′ → Ψ n j z i → Ψ n j z i′
    up′ n j z le h = ≤-trans h (cum-mono le (H z) χ χ-nn)

  -- A `Dₚ` tree the run takes and the cut-off unfolds into coins.
  module _ (f : MC.Machine X Y) (m : MC.St f) {Z : Set} (κ : ℕ → Z → Strat X Y)
           (H : Z → Dₚ Bool) where

    private
      run : Strat X Y → Dₚ Bool
      run = runFromˢ f m

      next : ℕ → ℕ → Z ⊎ Dₚ Z → Strat X Y
      next u n = [ κ n , (λ e′ → unfoldˢ u (not b) e′ (κ n)) ]

      unfold-mono : (∀ z → Mono (λ n → run (κ n z))) → {u u′ n n′ : ℕ} → u ≤ℕ u′ → n ≤ℕ n′
                  → (e : Dₚ Z) (j : ℕ)
                  → cum j (run (unfoldˢ u (not b) e (κ n))) χ
                    ℚ.≤ cum j (run (unfoldˢ u′ (not b) e (κ n′))) χ
      unfold-mono mono {u′ = u′} {n′ = n′} z≤n _ e j =
        ≤-trans (cut-zero j) (cum-nn j (run (unfoldˢ u′ (not b) e (κ n′))) χ χ-nn)
      unfold-mono mono {suc u} {suc u′} {n} {n′} (s≤s le) le′ e j =
        bind-mono (λ c → branch (br e c)) j (coinₚ (wtᴰ e))
        where
        branch : (x : Z ⊎ Dₚ Z) (i : ℕ) → cum i (run (next u n x)) χ ℚ.≤ cum i (run (next u′ n′ x)) χ
        branch (inj₁ z)  i = mono z le′ i
        branch (inj₂ e′) i = unfold-mono mono le le′ e′ i

      unfold-lower : (∀ z → Mono (λ n → run (κ n z)))
                   → (∀ z (j : ℕ) → Σ[ n ∈ ℕ ] Σ[ M ∈ ℕ ] cum j (H z) χ ℚ.≤ cum M (run (κ n z)) χ)
                   → (j : ℕ) (e : Dₚ Z)
                   → Σ[ u ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ M ∈ ℕ ]
                       cum j (e >>=ₚ H) χ ℚ.≤ cum M (run (unfoldˢ u (not b) e (κ n))) χ
      unfold-lower mono low zero    e = 0 , 0 , 0 , ≤-refl
      unfold-lower mono low (suc j) e =
        let u₁ , n₁ , M₁ , h₁ = branch (br e true)
            u₂ , n₂ , M₂ , h₂ = branch (br e false)
            U = u₁ ⊔ u₂
            N = n₁ ⊔ n₂
            M = M₁ ⊔ M₂
        in suc U , N , suc (suc M)
         , ≤-trans (node-mono (wt e true) (wt e false) (wt-nn e true) (wt-nn e false)
                     (≤-trans h₁ (lift (br e true) (m≤m⊔n u₁ u₂) (m≤m⊔n n₁ n₂) (m≤m⊔n M₁ M₂)))
                     (≤-trans h₂ (lift (br e false) (m≤n⊔m u₁ u₂) (m≤n⊔m n₁ n₂) (m≤n⊔m M₁ M₂))))
                   (≤-reflexive (sym (trans (coin-bind-cum (wtᴰ e) (λ c → run (next U N (br e c))) M χ)
                                            (E-wtᴰ e (λ c → cum M (run (next U N (br e c))) χ)))))
        where
        branch : (x : Z ⊎ Dₚ Z) → Σ[ u ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ M ∈ ℕ ]
                   leafₚ j (tagₚ x H) χ ℚ.≤ cum M (run (next u n x)) χ
        branch (inj₁ z)  = let n , M , h = low z j in 0 , n , M , h
        branch (inj₂ e′) = unfold-lower mono low j e′

        lift : (x : Z ⊎ Dₚ Z) {u u′ n n′ M M′ : ℕ} → u ≤ℕ u′ → n ≤ℕ n′ → M ≤ℕ M′
             → cum M (run (next u n x)) χ ℚ.≤ cum M′ (run (next u′ n′ x)) χ
        lift (inj₁ z)  {n′ = n′} {M} _ ln lM =
          ≤-trans (mono z ln M) (cum-mono lM (run (κ n′ z)) χ χ-nn)
        lift (inj₂ e′) {u′ = u′} {n′ = n′} {M} lu ln lM =
          ≤-trans (unfold-mono mono lu ln e′ M) (cum-mono lM (run (unfoldˢ u′ (not b) e′ (κ n′))) χ χ-nn)

      unfold-upper : (n : ℕ) → (∀ z → Cofinal χ χ (run (κ n z)) (H z))
                   → (u : ℕ) (e : Dₚ Z) → Cofinal χ χ (run (unfoldˢ u (not b) e (κ n))) (e >>=ₚ H)
      unfold-upper n cof zero    e j             = 0 , cut-zero j
      unfold-upper n cof (suc u) e zero          = 0 , ≤-refl
      unfold-upper n cof (suc u) e (suc zero)    =
        0 , ≤-reflexive (cum-1-bind (coinₚ (wtᴰ e)) (λ c → run (next u n (br e c))) χ)
      unfold-upper n cof (suc u) e (suc (suc j)) =
        let M₁ , h₁ = branch (br e true)
            M₂ , h₂ = branch (br e false)
        in suc (M₁ ⊔ M₂)
         , ≤-trans (≤-reflexive (trans (coin-bind-cum (wtᴰ e) (λ c → run (next u n (br e c))) j χ)
                                       (E-wtᴰ e (λ c → cum j (run (next u n (br e c))) χ))))
                   (node-mono (wt e true) (wt e false) (wt-nn e true) (wt-nn e false)
                     (≤-trans h₁ (leafₚ-mono (m≤m⊔n M₁ M₂) (tagₚ (br e true) H) χ χ-nn))
                     (≤-trans h₂ (leafₚ-mono (m≤n⊔m M₁ M₂) (tagₚ (br e false) H) χ χ-nn)))
        where
        branch : (x : Z ⊎ Dₚ Z) → Σ[ M ∈ ℕ ] cum j (run (next u n x)) χ ℚ.≤ leafₚ M (tagₚ x H) χ
        branch (inj₁ z)  = cof z j
        branch (inj₂ e′) = unfold-upper n cof u e′ j

    approx-unfold : (∀ z → Approx (λ n → run (κ n z)) (H z)) → (e : Dₚ Z)
                  → Approx (λ n → run (unfoldˢ n (not b) e (κ n))) (e >>=ₚ H)
    approx-unfold a e = record
      { mono  = λ le → unfold-mono (λ z → mono (a z)) le le e
      ; lower = λ j → let u , n , M , h = unfold-lower (λ z → mono (a z)) (λ z → lower (a z)) j e
                      in u ⊔ n , M
                       , ≤-trans h (unfold-mono (λ z → mono (a z)) (m≤m⊔n u n) (m≤n⊔m u n) e M)
      ; upper = λ n → unfold-upper n (λ z → upper (a z) n) n e }

------------------------------------------------------------------------
-- Contexts a distinguisher can absorb

-- `♯ d b i`: a strategy against the hole, simulating the rest of the context
-- for `d`; `i` is its budget.
record Absorbs {X Y X′ Y′ : Set} (C : MC.Machine X Y → MC.Machine X′ Y′) : Set₁ where
  field
    Ix    : Set
    ♯     : Strat X′ Y′ → Bool → Ix → Strat X Y
    lower : (f : MC.Machine X Y) (d : Strat X′ Y′) (b : Bool) (j : ℕ)
          → Σ[ i ∈ Ix ] Σ[ m ∈ ℕ ] cum j (runˢ (C f) d) (indᵇ b) ℚ.≤ cum m (runˢ f (♯ d b i)) (indᵇ b)
    upper : (f : MC.Machine X Y) (d : Strat X′ Y′) (b : Bool) (i : Ix)
          → Cofinal (indᵇ b) (indᵇ b) (runˢ f (♯ d b i)) (runˢ (C f) d)

-- per verdict b:  cum j (C f) ≤ cum m (f , ♯ d b i)        lower
--   ≤ cum m′ (f′ , ♯ d b i) + ε   (the hypothesis at ♯ d b i)  ≤ cum m″ (C f′) + ε   upper
absorbs⇒resp : {C : MC.Machine X Y → MC.Machine X′ Y′} → Absorbs C
             → {f f′ : MC.Machine X Y} → f ≈ᴿ f′ → C f ≈ᴿ C f′
absorbs⇒resp {X = X} {Y} {C = C} 𝔸 {f} {f′} e d ε pos = side f f′ e , side f′ f (≈ᴿ.sym e)
  where
  open Absorbs 𝔸
  module ≈ᴿ = Structures.IsEquivalence (≈ᴿ-isEquivalence {X} {Y})

  side : (g g′ : MC.Machine X Y) → g ≈ᴿ g′ → runˢ (C g) d ≼ₚ[ ε ] runˢ (C g′) d
  side g g′ e b j =
    let i , m , le₁ = lower g d b j
        m′ , le₂    = proj₁ (e (♯ d b i) ε pos) b m
        m″ , le₃    = upper g′ d b i m′
    in m″ , ≤-trans le₁ (≤-trans le₂ (+-monoˡ-≤ ε le₃))

absorbs-∘ : {C : MC.Machine X′ Y′ → MC.Machine X″ Y″} {C′ : MC.Machine X Y → MC.Machine X′ Y′}
          → Absorbs C → Absorbs C′ → Absorbs (λ f → C (C′ f))
absorbs-∘ {C = C} {C′} 𝔸 𝔹 = record
  { Ix    = A.Ix × B.Ix
  ; ♯     = λ d b (i , j) → B.♯ (A.♯ d b i) b j
  ; lower = λ f d b k → let i , m , le = A.lower (C′ f) d b k
                            j , m′ , le′ = B.lower f (A.♯ d b i) b m
                        in (i , j) , m′ , ≤-trans le le′
  ; upper = λ f d b (i , j) → cofinal-trans (runˢ f (B.♯ (A.♯ d b i) b j)) (runˢ (C′ f) (A.♯ d b i))
                                            (runˢ (C (C′ f)) d) (B.upper f (A.♯ d b i) b j)
                                            (A.upper (C′ f) d b i)
  }
  where
  module A = Absorbs 𝔸
  module B = Absorbs 𝔹

absorbs-resp : {C C′ : MC.Machine X Y → MC.Machine X′ Y′}
             → (∀ f d → runˢ (C f) d ≈ₚ runˢ (C′ f) d) → Absorbs C → Absorbs C′
absorbs-resp {C = C} {C′} eq 𝔸 = record
  { Ix    = Ix
  ; ♯     = ♯
  ; lower = λ f d b j → let j′ , le = proj₂ (eq f d) (indᵇ b) (indᵇ-nn b) j
                            i , m , le′ = lower f d b j′
                        in i , m , ≤-trans le le′
  ; upper = λ f d b i → cofinal-trans (runˢ f (♯ d b i)) (runˢ (C f) d) (runˢ (C′ f) d)
                                      (upper f d b i) (proj₁ (eq f d) (indᵇ b) (indᵇ-nn b))
  }
  where open Absorbs 𝔸

absorbs-≈ᴹ : {C C′ : MC.Machine X Y → MC.Machine X′ Y′} → (∀ f → C f MS.≈ᴹ C′ f)
           → Absorbs C → Absorbs C′
absorbs-≈ᴹ eq = absorbs-resp λ f → runˢ-resp-≈ᴹ (eq f)

approx⇒absorbs : {C : MC.Machine X Y → MC.Machine X′ Y′} (♯ : Strat X′ Y′ → Bool → ℕ → Strat X Y)
               → (∀ f d b → Approximation.Approx b (λ n → runˢ f (♯ d b n)) (runˢ (C f) d))
               → Absorbs C
approx⇒absorbs ♯ a = record
  { Ix    = ℕ
  ; ♯     = ♯
  ; lower = λ f d b → Approximation.lower (a f d b)
  ; upper = λ f d b → Approximation.upper (a f d b)
  }
