{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Propositional invariants of the canonical decoder
-- (`Canonical.canonical-go`) specialised at `id-fb`.
--
-- `canonical-target xs id-fb` is NOT *definitionally* `xs` (stdlib's
-- `P.id` is opaque enough that `residual id-fb` is only *pointwise*
-- `id-fb`), so we prove the propositional `canonical-target xs id-fb ≡ xs`
-- using `canonical-go-suc-unfold` to expose the with-block structure.
------------------------------------------------------------------------

module Categories.PermuteCoherence.CanonicalProps where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Patterns using (0F; 1F)
import Data.Fin.Permutation as P
open P using (Permutation; _∘ₚ_; transpose; lift₀; remove)
open import Data.List.Base using (List; []; _∷_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Product.Base using (Σ; _×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; cong; sym; trans)

open import Level using (Level)

open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.Canonical

private
  variable
    a : Level
    A : Set a

------------------------------------------------------------------------
-- Ground reductions: head-target / residual on `id-fb`.

head-target-id-fb : ∀ {n} → head-target {n} id-fb ≡ 0F
head-target-id-fb = refl

residual-id-fb : ∀ {n} → residual {n} id-fb ≈-fb id-fb
residual-id-fb i = refl

residual-id-fb-pw : ∀ {n} (i : Fin n) → (residual id-fb P.⟨$⟩ʳ i) ≡ i
residual-id-fb-pw i = refl

------------------------------------------------------------------------
-- cons-fb invariants.

head-target-cons-fb : ∀ {n} (b : FinBij n n) → head-target (cons-fb b) ≡ 0F
head-target-cons-fb _ = refl

residual-cons-fb : ∀ {n} (b : FinBij n n) → residual (cons-fb b) ≈-fb b
residual-cons-fb _ _ = refl

------------------------------------------------------------------------
-- bubble-to-front at position 0F.

bubble-to-front-zero
  : ∀ (x : A) (xs : List A)
  → bubble-to-front {n = length xs} (x ∷ xs) refl 0F
    ≡ (xs , refl , Perm.refl)
bubble-to-front-zero x xs = refl

------------------------------------------------------------------------
-- `canonical-go` returns `xs` whenever its bijection argument is
-- *pointwise* the identity (induction on the list via
-- `canonical-go-suc-unfold`).

open import Data.Fin.Properties using (suc-injective)

-- Pointwise-identity preservation under `residual`, via `P.lift₀-remove`
-- (the only fact about stdlib's `remove` we need).
residual-pw-id
  : ∀ {m} (c : FinBij (suc m) (suc m))
  → (∀ i → c P.⟨$⟩ʳ i ≡ i)
  → ∀ i → residual c P.⟨$⟩ʳ i ≡ i
residual-pw-id c c-id i =
  suc-injective
    (trans (P.lift₀-remove c (c-id 0F) (suc i)) (c-id (suc i)))

canonical-go-pw-id
  : ∀ (n : ℕ) (ys : List A) (ys-len : length ys ≡ n)
    (b : FinBij n n) (b-id : ∀ i → b P.⟨$⟩ʳ i ≡ i)
  → proj₁ (canonical-go n ys ys-len b) ≡ ys
canonical-go-pw-id zero    []       _    _ _    = refl
canonical-go-pw-id zero    (_ ∷ _)  ()
canonical-go-pw-id (suc n) []       ()
canonical-go-pw-id (suc n) (y ∷ ys) refl b b-id =
  trans (canonical-go-suc-unfold y ys b) (goal-with-ht (head-target b) (b-id 0F))
  where
  goal-with-ht
    : ∀ (k : Fin (suc n)) (eq : k ≡ 0F)
    → lookup (y ∷ ys) k
        ∷ proj₁ (canonical-go n
                              (proj₁ (bubble-to-front (y ∷ ys) refl k))
                              (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                              (residual b))
      ≡ y ∷ ys
  goal-with-ht .0F refl =
    cong (y ∷_) (canonical-go-pw-id n ys refl (residual b) (residual-pw-id b b-id))

canonical-go-id-fb-target
  : ∀ (n : ℕ) (xs : List A) (xs-len : length xs ≡ n)
  → proj₁ (canonical-go n xs xs-len id-fb) ≡ xs
canonical-go-id-fb-target n xs xs-len =
  canonical-go-pw-id n xs xs-len id-fb (λ _ → refl)

------------------------------------------------------------------------
-- `canonical-target xs id-fb ≡ xs`.

canonical-target-id-fb : ∀ (xs : List A) → canonical-target xs id-fb ≡ xs
canonical-target-id-fb xs = canonical-go-id-fb-target (length xs) xs refl

------------------------------------------------------------------------
-- Pointwise-congruence of `canonical-go .proj₁`, needed for the prep case
-- of the canonical bridge (where `residual (cons-fb (eval-↭ p))` is only
-- *pointwise* equal to `eval-↭ p`).

open import Data.Fin.Properties using (punchOut-cong)
open import Data.Fin.Base using (punchOut)

-- `punchOut` is congruent in both arguments (stdlib provides only the `j` half).
private
  punchOut-cong-both
    : ∀ {n} (i i' j j' : Fin (suc n))
        (ei : i ≡ i') (ej : j ≡ j')
        (p : i ≢ j) (p' : i' ≢ j')
    → punchOut p ≡ punchOut p'
  punchOut-cong-both i .i j j' refl ej _ _ = punchOut-cong i ej

residual-pw-cong
  : ∀ {n} (b b' : FinBij (suc n) (suc n))
  → (∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
  → ∀ i → residual b P.⟨$⟩ʳ i ≡ residual b' P.⟨$⟩ʳ i
residual-pw-cong b b' eq i =
  punchOut-cong-both _ _ _ _ (eq 0F) (eq (suc i)) _ _

open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Properties using (n<1+n)
open import Level using (0ℓ)

-- Pointwise-congruence of `canonical-go .proj₁`.  Structural recursion
-- fails the termination check (the recursive list is not a subterm), so
-- we use well-founded recursion on `n`.
private
  P-pw-cong : ∀ {a} (A : Set a) → ℕ → Set a
  P-pw-cong A n = ∀ (xs : List A) (xs-len : length xs ≡ n)
                    (b b' : FinBij n n) (eq : ∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
                → proj₁ (canonical-go n xs xs-len b)
                  ≡ proj₁ (canonical-go n xs xs-len b')

  go-pw-cong
    : ∀ {a} (A : Set a) (n : ℕ)
    → (∀ {m} → m Data.Nat.Base.< n → P-pw-cong A m)
    → P-pw-cong A n
  go-pw-cong A zero    rec []       _    _ _  _ = refl
  go-pw-cong A zero    rec (_ ∷ _)  ()
  go-pw-cong A (suc n) rec []       ()
  go-pw-cong A (suc n) rec (y ∷ ys) refl b b' eq =
    trans (canonical-go-suc-unfold y ys b)
      (trans (cong-with-k (head-target b) (head-target b') (eq 0F))
             (sym (canonical-go-suc-unfold y ys b')))
    where
    cong-with-k
      : ∀ (k k' : Fin (suc n)) (ek : k ≡ k')
      → lookup (y ∷ ys) k
          ∷ proj₁ (canonical-go n
                    (proj₁ (bubble-to-front (y ∷ ys) refl k))
                    (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
                    (residual b))
        ≡ lookup (y ∷ ys) k'
          ∷ proj₁ (canonical-go n
                    (proj₁ (bubble-to-front (y ∷ ys) refl k'))
                    (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k')))
                    (residual b'))
    cong-with-k k .k refl =
      cong (lookup (y ∷ ys) k ∷_)
           (rec {n} (n<1+n n)
              (proj₁ (bubble-to-front (y ∷ ys) refl k))
              (proj₁ (proj₂ (bubble-to-front (y ∷ ys) refl k)))
              (residual b) (residual b')
              (residual-pw-cong b b' eq))

canonical-go-pw-cong-target
  : ∀ (n : ℕ) (xs : List A) (xs-len : length xs ≡ n)
      (b b' : FinBij n n) (eq : ∀ i → b P.⟨$⟩ʳ i ≡ b' P.⟨$⟩ʳ i)
  → proj₁ (canonical-go n xs xs-len b)
    ≡ proj₁ (canonical-go n xs xs-len b')
canonical-go-pw-cong-target {A = A} = <-rec _ (go-pw-cong A)
