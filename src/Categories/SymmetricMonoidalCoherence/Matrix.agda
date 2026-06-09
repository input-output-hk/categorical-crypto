{-# OPTIONS --without-K --safe #-}

module Categories.SymmetricMonoidalCoherence.Matrix where

------------------------------------------------------------------------
-- Matrices in a biproduct category (Section 3.1 of the paper).
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to ℓsuc)

open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup; map; tabulate; replicate)
open import Function using (_∘′_; const) renaming (id to idf)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    a : Level
    m n p : ℕ

------------------------------------------------------------------------
-- Matrix type and basic operations
------------------------------------------------------------------------

Matrix : Set a → ℕ → ℕ → Set a
Matrix A m n = Vec (Vec A n) m

_[_,_] : {A : Set a} → Matrix A m n → Fin m → Fin n → A
M [ i , j ] = lookup (lookup M i) j

tabulateM : {A : Set a} → (Fin m → Fin n → A) → Matrix A m n
tabulateM f = tabulate (λ i → tabulate (f i))

transpose : {A : Set a} → Matrix A m n → Matrix A n m
transpose M = tabulateM (λ j i → M [ i , j ])

-- ℕ-indexed lookup (total, returns default for out-of-bounds)
lookupℕ : ∀ {A : Set} → A → Vec A m → ℕ → A
lookupℕ d []       _       = d
lookupℕ d (x ∷ _)  zero    = x
lookupℕ d (_ ∷ xs) (suc j) = lookupℕ d xs j

lookupM : ∀ {A : Set} → A → Matrix A m n → ℕ → ℕ → A
lookupM d []         _       _ = d
lookupM d (r ∷ _)    zero    j = lookupℕ d r j
lookupM d (_ ∷ rows) (suc i) j = lookupM d rows i j

------------------------------------------------------------------------
-- Lookup/tabulate round-trip lemmas
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

-- lookupℕ on tabulate returns the function value
lookupℕ-tabulate : ∀ {k} {A : Set} (d : A) (f : Fin k → A) (j : Fin k)
                 → lookupℕ d (tabulate f) (toℕ j) ≡ f j
lookupℕ-tabulate d f Fin.zero    = refl
lookupℕ-tabulate d f (Fin.suc j) = lookupℕ-tabulate d (λ x → f (Fin.suc x)) j

-- lookupM on tabulateM returns the function value
lookupM-tabulateM : ∀ {r c} {A : Set} (d : A) (f : Fin r → Fin c → A)
                    (i : Fin r) (j : Fin c)
                  → lookupM d (tabulateM f) (toℕ i) (toℕ j) ≡ f i j
lookupM-tabulateM d f Fin.zero    j = lookupℕ-tabulate d (f Fin.zero) j
lookupM-tabulateM d f (Fin.suc i) j = lookupM-tabulateM d (λ x → f (Fin.suc x)) i j

-- Extensionality for tabulate
tabulate-ext : ∀ {k} {A : Set} {f g : Fin k → A}
             → (∀ i → f i ≡ g i) → tabulate f ≡ tabulate g
tabulate-ext {k = ℕ.zero}  eq = refl
tabulate-ext {k = ℕ.suc k} eq =
  cong₂ _∷_ (eq Fin.zero) (tabulate-ext (λ i → eq (Fin.suc i)))

-- Extensionality for tabulateM
tabulateM-ext : ∀ {r c} {A : Set} {f g : Fin r → Fin c → A}
              → (∀ i j → f i j ≡ g i j) → tabulateM f ≡ tabulateM g
tabulateM-ext eq = tabulate-ext (λ i → tabulate-ext (eq i))

------------------------------------------------------------------------
-- Block matrices
--
-- A block matrix with k generator blocks has row groups
--   v⁻ (size sA) and t⁺ i (size cs i), and column groups
--   t⁻ i (size ds i) and v⁺ (size sB).
-- Each block (r, c) is a Bool sub-matrix of the appropriate size.
------------------------------------------------------------------------

data RowG (k : ℕ) : Set where
  v⁻  : RowG k
  t⁺  : Fin k → RowG k

data ColG (k : ℕ) : Set where
  t⁻  : Fin k → ColG k
  v⁺  : ColG k

module Sizes (sA sB : ℕ) {k : ℕ} (ds cs : Fin k → ℕ) where
  rSz : RowG k → ℕ
  rSz v⁻     = sA
  rSz (t⁺ i) = cs i
  cSz : ColG k → ℕ
  cSz (t⁻ i) = ds i
  cSz v⁺     = sB

BlockMatrix : (sA sB : ℕ) (k : ℕ) (ds cs : Fin k → ℕ) → Set
BlockMatrix sA sB k ds cs =
  (r : RowG k) (c : ColG k) → Matrix Bool (rSz r) (cSz c)
  where open Sizes sA sB ds cs

------------------------------------------------------------------------
-- Matrix multiplication, parameterised by (+, ·, 0)
------------------------------------------------------------------------

module MatMul {A : Set a} (_+_ : A → A → A) (_·_ : A → A → A) (0# : A) where

  dot : Vec A n → Vec A n → A
  dot []       []       = 0#
  dot (x ∷ xs) (y ∷ ys) = (x · y) + dot xs ys

  infixl 7 _*M_
  _*M_ : Matrix A m p → Matrix A p n → Matrix A m n
  A *M B = tabulateM (λ i j → dot (lookup A i) (tabulate (λ k → B [ k , j ])))

  scalarM : A → Matrix A n n
  scalarM {zero}  s = []
  scalarM {suc n} s = (s ∷ replicate _ 0#) ∷ map (0# ∷_) (scalarM s)

------------------------------------------------------------------------
-- Set-valued matrices: instantiate MatMul with (⊎, ×, ⊥)
------------------------------------------------------------------------

module SpanMatrix where

  SetMatrix : ℕ → ℕ → Set₁
  SetMatrix m n = Matrix Set m n

  open MatMul _⊎_ _×_ ⊥ public
    renaming (_*M_ to _*SetM_ ; dot to dotSet)

  idSetM : SetMatrix n n
  idSetM = tabulateM Diag
    where
      Diag : Fin n → Fin n → Set
      Diag {suc _} zero    zero    = ⊤
      Diag {suc _} zero    (suc _) = ⊥
      Diag {suc _} (suc i) zero    = ⊥
      Diag {suc _} (suc i) (suc j) = Diag i j

  permSetM : (Fin n → Fin n) → SetMatrix n n
  permSetM σ = tabulateM (λ i j → σ i ≡ j)

  directSumM : ∀ {m₁ n₁ m₂ n₂} → SetMatrix m₁ n₁ → SetMatrix m₂ n₂
             → SetMatrix (m₁ + m₂) (n₁ + n₂)
  directSumM {m₁} {n₁} A B = tabulateM λ i j →
    [ (λ i' → [ (λ j' → A [ i' , j' ]) , (λ _ → ⊥) ]′ (Fin.splitAt n₁ j))
    , (λ i' → [ (λ _ → ⊥) , (λ j' → B [ i' , j' ]) ]′ (Fin.splitAt n₁ j))
    ]′ (Fin.splitAt m₁ i)

------------------------------------------------------------------------
-- (Trailing `Biproduct` module removed for this feasibility spike: it
-- depended on `Categories.Object.Biproduct.Indexed`, which is absent on
-- this branch, and is unused by the matrix-level alignment logic.)
------------------------------------------------------------------------
