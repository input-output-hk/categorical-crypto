{-# OPTIONS --safe --without-K --guardedness #-}

-- Over a finite query alphabet with decidable equality, the non-adaptive
-- equality `_≈ᴮ_` (maurer2002 Def 3) is behavioural equality `_≈ᴿ_` (Defs 9–10).
--
-- A run is split along the alphabet by the first question the strategy asks
-- (`only`, `without`: exact at every depth, `Ψ-split`), and a fixed first
-- question moves into the input prefix (`Ψ-only`), its answer into the
-- strategy's history.  The strategy's coins commute with the machine's step
-- there (`>>=ₚ-swap`), which is what makes the next question's choice
-- non-adaptive.  Once no question is left, the run is a test of the prefix's
-- outputs, read at depth `j` as the rational `cum j`, which `_≈ᴮ_` compares
-- (`Ψ-askfree`).  An unbounded strategy is the limit of its cut-offs (`cut-approx`).

open import Algebra.Bundles
open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base using (List; []; _∷_; _++_; reverseAcc)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
import Algebra.Properties.CommutativeSemigroup as CommSemigroup

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Commutative
open import ProbabilisticLogic.Dp.Mass
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Behaviour.Absorb
open import CategoricalCrypto.UC.Machine.Run

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Machine.Behaviour.Finite where

private
  module MC = Core (𝒱ₚ 0ℓ)
  open CommSemigroup (CommutativeMonoid.commutativeSemigroup +-0-commutativeMonoid)
  variable
    X Y Z : Set
    n : ℕ

-- one half of `_≈ᴮ_`
Below : MC.Machine X Y → MC.Machine X Y → Set
Below {X} {Y} M M′ = (xs : List X) (P : List Y → ℚ) → (∀ ys → 0ℚ ℚ.≤ P ys × P ys ℚ.≤ 1ℚ)
                   → (ε : ℚ) → 0ℚ ℚ.< ε → Dom P ε (runᴸ M xs) (runᴸ M′ xs)

------------------------------------------------------------------------
-- Surgery on a strategy's first layer, its coin prefix

FirstAsksIn : List X → Strat X Y → Set
FirstAsksIn L (out _)    = ⊤
FirstAsksIn L (coin _ k) = ∀ c → FirstAsksIn L (k c)
FirstAsksIn L (ask x _)  = x ∈ L

play : Strat X Y → Dₚ Bool
play (out c)    = returnₚ c
play (coin μ k) = coinₚ μ >>=ₚ play ∘ k
play (ask _ _)  = botₚ

-- the first layer's questions all answered `y`
answer : Y → Strat X Y → Strat X Y
answer y (out c)    = out c
answer y (coin μ k) = coin μ (answer y ∘ k)
answer y (ask _ k)  = k y

module _ (b : Bool) where

  -- cut off after `n` questions, answering the verdict `b` does not count
  cut : ℕ → Strat X Y → Strat X Y
  cut n       (out c)    = out c
  cut n       (coin μ k) = coin μ (cut n ∘ k)
  cut zero    (ask _ _)  = out (not b)
  cut (suc n) (ask x k)  = ask x (cut n ∘ k)

  -- The first-layer leaves that ask `x`, and the rest; a leaf dropped from
  -- either answers the verdict `b` does not count.  Lemmas split on the
  -- decision through a `Dec` argument (`keep-split`, `keep-step`): with
  -- `with x ≟ x′` instead, `run-split` did not check within 300 s.
  module _ {x x′ : X} where

    keep drop : Dec (x ≡ x′) → (Y → Strat X Y) → Strat X Y
    keep (yes _) k = ask x′ k
    keep (no _)  k = out (not b)

    drop (yes _) k = out (not b)
    drop (no _)  k = ask x′ k

  module _ (_≟_ : DecidableEquality X) (x : X) where

    only without : Strat X Y → Strat X Y
    only (out _)    = out (not b)
    only (coin μ k) = coin μ (only ∘ k)
    only (ask x′ k) = keep (x ≟ x′) k

    without (out c)    = out c
    without (coin μ k) = coin μ (without ∘ k)
    without (ask x′ k) = drop (x ≟ x′) k

asks-cut : (b : Bool) (n : ℕ) (d : Strat X Y) → asks≤ n (cut b n d)
asks-cut b n       (out _)    = tt
asks-cut b n       (coin _ k) = λ c → asks-cut b n (k c)
asks-cut b zero    (ask _ _)  = tt
asks-cut b (suc n) (ask _ k)  = λ y → asks-cut b n (k y)

module _ (b : Bool) (_≟_ : DecidableEquality X) (x : X) where

  asks-only : (y : Y) (d : Strat X Y) → asks≤ (suc n) d → asks≤ n (answer y (only b _≟_ x d))
  asks-only y (out _)    a = tt
  asks-only y (coin _ k) a = λ c → asks-only y (k c) (a c)
  asks-only y (ask x′ k) a = kept (x ≟ x′) a
    where
    kept : (e : Dec (x ≡ x′)) → asks≤ (suc n) (ask x′ k) → asks≤ n (answer y (keep b e k))
    kept (yes _) a = a y
    kept (no _)  a = tt

  -- the family once `x` was asked and answered, against the history
  next : (List Y → Strat X Y) → List Y → Strat X Y
  next D []      = out (not b)
  next D (y ∷ h) = answer y (only b _≟_ x (D h))

  asks-next : (D : List Y → Strat X Y) → (∀ h → asks≤ (suc n) (D h)) → ∀ h → asks≤ n (next D h)
  asks-next D a []      = tt
  asks-next D a (y ∷ h) = asks-only y (D h) (a h)

  asks-without : (d : Strat X Y) → asks≤ n d → asks≤ n (without b _≟_ x d)
  asks-without (out _)    a = a
  asks-without (coin _ k) a = λ c → asks-without (k c) (a c)
  asks-without (ask x′ k) a = dropped (x ≟ x′) a
    where
    dropped : (e : Dec (x ≡ x′)) → asks≤ n (ask x′ k) → asks≤ n (drop b e k)
    dropped (yes _) a = tt
    dropped (no _)  a = a

  first-without : {L : List X} (d : Strat X Y) → FirstAsksIn (x ∷ L) d
                → FirstAsksIn L (without b _≟_ x d)
  first-without (out _)    f = tt
  first-without (coin _ k) f = λ c → first-without (k c) (f c)
  first-without {L = L} (ask x′ k) f = dropped (x ≟ x′) f
    where
    dropped : (e : Dec (x ≡ x′)) → x′ ∈ x ∷ L → FirstAsksIn L (drop b e k)
    dropped (yes _)   _            = tt
    dropped (no x≢x′) (here x′≡x)  = ⊥-elim (x≢x′ (sym x′≡x))
    dropped (no _)    (there x′∈L) = x′∈L

first-[] : (d : Strat X Y) → FirstAsksIn [] d → asks≤ 0 d
first-[] (out _)    f = tt
first-[] (coin _ k) f = λ c → first-[] (k c) (f c)
first-[] (ask _ _)  ()

first-all : {L : List X} → (∀ x → x ∈ L) → (d : Strat X Y) → FirstAsksIn L d
first-all all (out _)    = tt
first-all all (coin _ k) = λ c → first-all all (k c)
first-all all (ask x _)  = all x

------------------------------------------------------------------------
-- A bind is linear in its continuation, exactly at every depth

module _ (P : Z → ℚ) where

  private
    node-split : (w₁ w₂ a₁ b₁ a₂ b₂ : ℚ)
               → w₁ ℚ.* (a₁ ℚ.+ b₁) ℚ.+ w₂ ℚ.* (a₂ ℚ.+ b₂)
                 ≡ (w₁ ℚ.* a₁ ℚ.+ w₂ ℚ.* a₂) ℚ.+ (w₁ ℚ.* b₁ ℚ.+ w₂ ℚ.* b₂)
    node-split w₁ w₂ a₁ b₁ a₂ b₂ =
      trans (cong₂ ℚ._+_ (*-distribˡ-+ w₁ a₁ b₁) (*-distribˡ-+ w₂ a₂ b₂))
            (interchange (w₁ ℚ.* a₁) (w₁ ℚ.* b₁) (w₂ ℚ.* a₂) (w₂ ℚ.* b₂))

  mutual
    bind-split : {K K₁ K₂ : Y → Dₚ Z}
               → (∀ y j → cum j (K y) P ≡ cum j (K₁ y) P ℚ.+ cum j (K₂ y) P)
               → (j : ℕ) (e : Dₚ Y) → cum j (e >>=ₚ K) P ≡ cum j (e >>=ₚ K₁) P ℚ.+ cum j (e >>=ₚ K₂) P
    bind-split h zero    e = sym (+-identityʳ 0ℚ)
    bind-split h (suc j) e =
      trans (cong₂ ℚ._+_ (cong (wt e true ℚ.*_) (leaf-split h j (br e true)))
                         (cong (wt e false ℚ.*_) (leaf-split h j (br e false))))
            (node-split (wt e true) (wt e false) _ _ _ _)

    leaf-split : {K K₁ K₂ : Y → Dₚ Z}
               → (∀ y j → cum j (K y) P ≡ cum j (K₁ y) P ℚ.+ cum j (K₂ y) P)
               → (j : ℕ) (u : Y ⊎ Dₚ Y)
               → leafₚ j (tagₚ u K) P ≡ leafₚ j (tagₚ u K₁) P ℚ.+ leafₚ j (tagₚ u K₂) P
    leaf-split h j (inj₁ y)  = h y j
    leaf-split h j (inj₂ e′) = bind-split h j e′

------------------------------------------------------------------------
-- An input prefix fed in, its answers kept as a history (latest first)

module _ (M : MC.Machine X Y) where

  feed : MC.St M → List Y → List X → (MC.St M → List Y → Dₚ Bool) → Dₚ Bool
  feed s h []       K = K s h
  feed s h (x ∷ xs) K = MC.step M (s , x) >>=ₚ λ r → feed (proj₁ r) (proj₂ r ∷ h) xs K

  -- the strategy family `D` played after the prefix `xs`, against its history
  Ψ : List X → (List Y → Strat X Y) → Dₚ Bool
  Ψ xs D = MC.point (MC.state M) ttᵛ >>=ₚ λ s → feed s [] xs λ s′ h → runFromˢ M s′ (D h)

  feed-cong : {K K′ : MC.St M → List Y → Dₚ Bool} → (∀ s h → K s h ≈ₚ K′ s h)
            → (s : MC.St M) (h : List Y) (xs : List X) → feed s h xs K ≈ₚ feed s h xs K′
  feed-cong e s h []       = e s h
  feed-cong e s h (x ∷ xs) = bindᶠ λ r → feed-cong e (proj₁ r) (proj₂ r ∷ h) xs

  feed-snoc : (K : MC.St M → List Y → Dₚ Bool) (s : MC.St M) (h : List Y) (xs : List X) (x : X)
            → feed s h (xs ++ x ∷ []) K
              ≈ₚ feed s h xs (λ s′ h′ → MC.step M (s′ , x) >>=ₚ λ r → K (proj₁ r) (proj₂ r ∷ h′))
  feed-snoc K s h []        x = ≈refl
  feed-snoc K s h (x₀ ∷ xs) x = bindᶠ λ r → feed-snoc K (proj₁ r) (proj₂ r ∷ h) xs x

  feed-runᴸ : (C : List Y → Dₚ Bool) (s : MC.St M) (h : List Y) (xs : List X)
            → feed s h xs (λ _ h′ → C h′) ≈ₚ (runᴸFrom M s xs >>=ₚ λ ys → C (reverseAcc h ys))
  feed-runᴸ C s h []       = ≈sym (>>=ₚ-identityˡ [] _)
  feed-runᴸ C s h (x ∷ xs) =
      bindᶠ (λ r → feed-runᴸ C (proj₁ r) (proj₂ r ∷ h) xs)
    ⟨≈⟩ ≈sym ( >>=ₚ-assoc (MC.step M (s , x)) _ _
             ⟨≈⟩ bindᶠ λ r → bind-map (runᴸFrom M (proj₁ r) xs) (proj₂ r ∷_) _)

  play-run : (s : MC.St M) (d : Strat X Y) → asks≤ 0 d → runFromˢ M s d ≈ₚ play d
  play-run s (out _)    a = ≈refl
  play-run s (coin μ k) a = bindᶠ λ c → play-run s (k c) (a c)
  play-run s (ask _ _)  ()

  module _ (b : Bool) where
    open Approximation b

    feed-cofinal : {K K′ : MC.St M → List Y → Dₚ Bool} → (∀ s h → Cofinal χ χ (K s h) (K′ s h))
                 → (s : MC.St M) (h : List Y) (xs : List X) → Cofinal χ χ (feed s h xs K) (feed s h xs K′)
    feed-cofinal c s h []       = c s h
    feed-cofinal c s h (x ∷ xs) =
      bind-cofinal (MC.step M (s , x)) λ r → feed-cofinal c (proj₁ r) (proj₂ r ∷ h) xs

    feed-split : {K K₁ K₂ : MC.St M → List Y → Dₚ Bool}
               → (∀ s h j → cum j (K s h) χ ≡ cum j (K₁ s h) χ ℚ.+ cum j (K₂ s h) χ)
               → (s : MC.St M) (h : List Y) (xs : List X) (j : ℕ)
               → cum j (feed s h xs K) χ ≡ cum j (feed s h xs K₁) χ ℚ.+ cum j (feed s h xs K₂) χ
    feed-split e s h []       j = e s h j
    feed-split e s h (x ∷ xs) j =
      bind-split χ (λ r → feed-split e (proj₁ r) (proj₂ r ∷ h) xs) j (MC.step M (s , x))

    cut-approx : (s : MC.St M) (d : Strat X Y) → Approx (λ n → runFromˢ M s (cut b n d)) (runFromˢ M s d)
    cut-approx s (out c)    = approx-ret c
    cut-approx s (coin μ k) = approx-bind (coinₚ μ) λ c → cut-approx s (k c)
    cut-approx s (ask x k)  = record
      { mono  = λ where
          {zero}           le       j → ≤-trans (cut-zero j) (cum-nn j _ χ χ-nn)
          {suc _} {suc _} (s≤s le) j → mono A le j
      ; lower = λ j → let i , m , le = lower A j in suc i , m , le
      ; upper = λ where
          zero    j → 0 , cut-zero j
          (suc i)   → upper A i }
      where
      A = approx-bind (MC.step M (s , x)) λ r → cut-approx (proj₁ r) (k (proj₂ r))

module _ (b : Bool) (_≟_ : DecidableEquality X) (x : X) where
  open Approximation b

  private
    ret-zero : (j : ℕ) → cum j (returnₚ (not b)) χ ≡ 0ℚ
    ret-zero zero    = refl
    ret-zero (suc j) = trans (returnₚ-cum j (not b) χ) (indᵇ-not b)

    dead : (e : Dₚ Z) (j : ℕ) → cum j (e >>=ₚ λ _ → returnₚ (not b)) χ ℚ.≤ 0ℚ
    dead e j = ≤-trans (>>=ₚ-boundA j e _ χ χ-nn)
                       (≤-reflexive (trans (cum-cong-P j e _ _ λ _ → ret-zero j) (cum-zero j e)))

  module _ (M : MC.Machine X Y) where

    private
      ≡0+ : {a : ℚ} (c : ℚ) → a ≡ 0ℚ → c ≡ a ℚ.+ c
      ≡0+ c a≡0 = sym (trans (cong₂ ℚ._+_ a≡0 (refl {x = c})) (+-identityˡ c))

      ≡+0 : {a : ℚ} (c : ℚ) → a ≡ 0ℚ → c ≡ c ℚ.+ a
      ≡+0 c a≡0 = trans (sym (+-identityʳ c)) (cong₂ ℚ._+_ (refl {x = c}) (sym a≡0))

      keep-split : (s : MC.St M) {x′ : X} (e : Dec (x ≡ x′)) (k : Y → Strat X Y) (j : ℕ)
                 → cum j (runFromˢ M s (ask x′ k)) χ
                   ≡ cum j (runFromˢ M s (keep b e k)) χ ℚ.+ cum j (runFromˢ M s (drop b e k)) χ
      keep-split s {x′} (yes _) k j = ≡+0 (cum j (runFromˢ M s (ask x′ k)) χ) (ret-zero j)
      keep-split s {x′} (no _)  k j = ≡0+ (cum j (runFromˢ M s (ask x′ k)) χ) (ret-zero j)

    run-split : (s : MC.St M) (d : Strat X Y) (j : ℕ)
              → cum j (runFromˢ M s d) χ
                ≡ cum j (runFromˢ M s (only b _≟_ x d)) χ ℚ.+ cum j (runFromˢ M s (without b _≟_ x d)) χ
    run-split s (out c)    j = ≡0+ (cum j (returnₚ c) χ) (ret-zero j)
    run-split s (coin μ k) j = bind-split χ (λ c → run-split s (k c)) j (coinₚ μ)
    run-split s (ask x′ k) j = keep-split s (x ≟ x′) k j

    -- the question `x` asked first, the coins after its answer
    asked : MC.St M → Strat X Y → Dₚ Bool
    asked s d = MC.step M (s , x) >>=ₚ λ r → runFromˢ M (proj₁ r) (answer (proj₂ r) (only b _≟_ x d))

    private
      silent : (s : MC.St M) → Cofinal χ χ (returnₚ (not b)) (MC.step M (s , x) >>=ₚ λ _ → returnₚ (not b))
                             × Cofinal χ χ (MC.step M (s , x) >>=ₚ λ _ → returnₚ (not b)) (returnₚ (not b))
      silent s = (λ j → 0 , ≤-reflexive (ret-zero j)) , λ j → 0 , dead (MC.step M (s , x)) j

      keep-step : (s : MC.St M) {x′ : X} (e : Dec (x ≡ x′)) (k : Y → Strat X Y)
                → Cofinal χ χ (runFromˢ M s (keep b e k))
                              (MC.step M (s , x) >>=ₚ λ r → runFromˢ M (proj₁ r) (answer (proj₂ r) (keep b e k)))
                  × Cofinal χ χ (MC.step M (s , x) >>=ₚ λ r → runFromˢ M (proj₁ r) (answer (proj₂ r) (keep b e k)))
                                (runFromˢ M s (keep b e k))
      keep-step s (yes refl) k = cofinal-refl χ _ , cofinal-refl χ _
      keep-step s (no _)     k = silent s

    only-step : (s : MC.St M) (d : Strat X Y)
              → Cofinal χ χ (runFromˢ M s (only b _≟_ x d)) (asked s d)
                × Cofinal χ χ (asked s d) (runFromˢ M s (only b _≟_ x d))
    only-step s (out _)    = silent s
    only-step s (coin μ k) =
        cofinal-trans _ _ _ (bind-cofinal (coinₚ μ) λ c → proj₁ (only-step s (k c)))
                            (≈ₚ⇒cofinal χ χ-nn (>>=ₚ-swap (coinₚ μ) (MC.step M (s , x)) _))
      , cofinal-trans _ _ _ (≈ₚ⇒cofinal χ χ-nn (>>=ₚ-swap (MC.step M (s , x)) (coinₚ μ) _))
                            (bind-cofinal (coinₚ μ) λ c → proj₂ (only-step s (k c)))
    only-step s (ask x′ k) = keep-step s (x ≟ x′) k

    Ψ-split : (xs : List X) (D : List Y → Strat X Y) (j : ℕ)
            → cum j (Ψ M xs D) χ
              ≡ cum j (Ψ M xs λ h → only b _≟_ x (D h)) χ ℚ.+ cum j (Ψ M xs λ h → without b _≟_ x (D h)) χ
    Ψ-split xs D j = bind-split χ (λ s → feed-split M b (λ s′ h → run-split s′ (D h)) s [] xs) j
                                (MC.point (MC.state M) ttᵛ)

    Ψ-only : (xs : List X) (D : List Y → Strat X Y)
           → Cofinal χ χ (Ψ M xs λ h → only b _≟_ x (D h)) (Ψ M (xs ++ x ∷ []) (next b _≟_ x D))
             × Cofinal χ χ (Ψ M (xs ++ x ∷ []) (next b _≟_ x D)) (Ψ M xs λ h → only b _≟_ x (D h))
    Ψ-only xs D =
        cofinal-trans _ _ _ (bind-cofinal (MC.point (MC.state M) ttᵛ) λ s →
                               feed-cofinal M b (λ s′ h → proj₁ (only-step s′ (D h))) s [] xs)
                            (≈ₚ⇒cofinal χ χ-nn (bindᶠ λ s → ≈sym (feed-snoc M _ s [] xs x)))
      , cofinal-trans _ _ _ (≈ₚ⇒cofinal χ χ-nn (bindᶠ λ s → feed-snoc M _ s [] xs x))
                            (bind-cofinal (MC.point (MC.state M) ttᵛ) λ s →
                               feed-cofinal M b (λ s′ h → proj₂ (only-step s′ (D h))) s [] xs)

------------------------------------------------------------------------
-- The induction

module _ (b : Bool) where
  open Approximation b

  private
    dom-split : {a a₁ a₂ e e₁ e₂ : Dₚ Bool} {δ₁ δ₂ : ℚ}
              → (∀ j → cum j a χ ≡ cum j a₁ χ ℚ.+ cum j a₂ χ)
              → (∀ j → cum j e χ ≡ cum j e₁ χ ℚ.+ cum j e₂ χ)
              → Dom χ δ₁ a₁ e₁ → Dom χ δ₂ a₂ e₂ → Dom χ (δ₁ ℚ.+ δ₂) a e
    dom-split {e = e} {e₁} {e₂} {δ₁} {δ₂} sa se d₁ d₂ j =
      let m₁ , l₁ = d₁ j
          m₂ , l₂ = d₂ j
          m = m₁ ⊔ m₂
      in m , ≤-trans (≤-reflexive (sa j))
               (≤-trans (+-mono-≤ (≤-trans l₁ (+-monoˡ-≤ δ₁ (cum-mono (m≤m⊔n m₁ m₂) e₁ χ χ-nn)))
                                  (≤-trans l₂ (+-monoˡ-≤ δ₂ (cum-mono (m≤n⊔m m₁ m₂) e₂ χ χ-nn))))
                        (≤-reflexive (trans (interchange (cum m e₁ χ) δ₁ (cum m e₂ χ) δ₂)
                                            (cong (ℚ._+ (δ₁ ℚ.+ δ₂)) (sym (se m))))))

  module _ (M M′ : MC.Machine X Y) (below : Below M M′) where

    -- No question left: the run is a test of the prefix's outputs.
    Ψ-askfree : (xs : List X) (D : List Y → Strat X Y) → (∀ h → asks≤ 0 (D h))
              → (ε : ℚ) → 0ℚ ℚ.< ε → Dom χ ε (Ψ M xs D) (Ψ M′ xs D)
    Ψ-askfree xs D a ε pos =
      dom-resp (≈ₚ⇒cofinal χ χ-nn (played M)) (≈ₚ⇒cofinal χ χ-nn (≈sym (played M′))) λ j →
        let m , le = below xs (λ ys → cum j (C ys) χ)
                         (λ ys → cum-nn j (C ys) χ χ-nn , cum-≤1 j (C ys) χ (indᵇ-≤1 b)) ε pos j
        in m +ℕ j , ≤-trans (>>=ₚ-boundA j (runᴸ M xs) C χ χ-nn)
                     (≤-trans le (+-monoˡ-≤ ε (>>=ₚ-boundB m j (runᴸ M′ xs) C χ χ-nn)))
      where
      C : List Y → Dₚ Bool
      C ys = play (D (reverseAcc [] ys))

      played : (N : MC.Machine X Y) → Ψ N xs D ≈ₚ (runᴸ N xs >>=ₚ C)
      played N = bindᶠ (λ s → feed-cong N (λ s′ h → play-run N s′ (D h) (a h)) s [] xs
                              ⟨≈⟩ feed-runᴸ N (λ h → play (D h)) s [] xs)
             ⟨≈⟩ ≈sym (>>=ₚ-assoc (MC.point (MC.state N) ttᵛ) _ C)

    module _ (_≟_ : DecidableEquality X) (enum : List X) (complete : ∀ x → x ∈ enum) where

      Ψ-bounded : (n : ℕ) (xs : List X) (D : List Y → Strat X Y) → (∀ h → asks≤ n (D h))
                → (ε : ℚ) → 0ℚ ℚ.< ε → Dom χ ε (Ψ M xs D) (Ψ M′ xs D)
      Ψ-bounded zero    xs D a = Ψ-askfree xs D a
      Ψ-bounded (suc n) xs D a = split enum xs D a λ h → first-all complete (D h)
        where
        split : (L : List X) (xs : List X) (D : List Y → Strat X Y) → (∀ h → asks≤ (suc n) (D h))
              → (∀ h → FirstAsksIn L (D h)) → (ε : ℚ) → 0ℚ ℚ.< ε → Dom χ ε (Ψ M xs D) (Ψ M′ xs D)
        split []      xs D a f = Ψ-askfree xs D λ h → first-[] (D h) (f h)
        split (x ∷ L) xs D a f ε pos =
          dom-mono (≤-reflexive (½*+½* ε))
            (dom-split (Ψ-split b _≟_ x M xs D) (Ψ-split b _≟_ x M′ xs D)
              (dom-resp (proj₁ (Ψ-only b _≟_ x M xs D)) (proj₂ (Ψ-only b _≟_ x M′ xs D))
                (Ψ-bounded n (xs ++ x ∷ []) (next b _≟_ x D) (asks-next b _≟_ x D a) (½ ℚ.* ε)
                           (0<½* pos)))
              (split L xs (λ h → without b _≟_ x (D h)) (λ h → asks-without b _≟_ x (D h) (a h))
                     (λ h → first-without b _≟_ x (D h) (f h)) (½ ℚ.* ε) (0<½* pos)))

------------------------------------------------------------------------
-- The theorem

≈ᴮ⇒≈ᴿ-fin : DecidableEquality X → (enum : List X) → (∀ x → x ∈ enum)
          → {f g : MC.Machine X Y} → f ≈ᴮ g → f ≈ᴿ g
≈ᴮ⇒≈ᴿ-fin _≟_ enum complete {f} {g} e d ε pos =
    (λ b → side b f g λ xs P p δ q → proj₁ (e xs P p δ q))
  , (λ b → side b g f λ xs P p δ q → proj₂ (e xs P p δ q))
  where
  side : (b : Bool) (M M′ : MC.Machine _ _) → Below M M′ → Dom (indᵇ b) ε (runˢ M d) (runˢ M′ d)
  side b M M′ below j =
    let n , m , l₁ = Approx.lower (from M) j
        m′ , l₂    = Ψ-bounded b M M′ below _≟_ enum complete n [] (λ _ → cut b n d) (λ _ → asks-cut b n d)
                               ε pos m
        m″ , l₃    = Approx.upper (from M′) n m′
    in m″ , ≤-trans l₁ (≤-trans l₂ (+-monoˡ-≤ ε l₃))
    where
    open Approximation b
    from : (N : MC.Machine _ _) → Approx (λ n → runˢ N (cut b n d)) (runˢ N d)
    from N = approx-bind (MC.point (MC.state N) ttᵛ) λ s → cut-approx N b s d
