{-# OPTIONS --safe --without-K #-}

-- Finite exact IPDL, Gancher et al. §4.1–4.2. Reactions carry a uniform
-- depth bound; it bounds every continuation, not the number of API rounds.
module CategoricalCrypto.IPDL.Syntax where

open import Data.Bool.Base
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base hiding (lookup; take)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist

data Ty : Set where
  unit bit : Ty
  _⊠_ : Ty → Ty → Ty

Val : Ty → Set
Val unit = ⊤
Val bit = Bool
Val (σ ⊠ τ) = Val σ × Val τ

Ctx : Set
Ctx = List Ty

Ref : Ctx → Set
Ref Γ = Fin (length Γ)

ty : (Γ : Ctx) → Ref Γ → Ty
ty (τ ∷ Γ) zero = τ
ty (τ ∷ Γ) (suc c) = ty Γ c

private variable
  Γ Δ I O : Ctx
  τ : Ty
  n : ℕ

data Rxn (Γ : Ctx) (τ : Ty) : ℕ → Set where
  ret : Val τ → Rxn Γ τ n
  read : (c : Ref Γ) → (Val (ty Γ c) → Rxn Γ τ n) → Rxn Γ τ (suc n)
  coin : Dist-ℚ Bool → (Bool → Rxn Γ τ n) → Rxn Γ τ (suc n)

record Ren (Γ Δ : Ctx) : Set where
  field name : Ref Γ → Ref Δ
        typed : ∀ c → ty Δ (name c) ≡ ty Γ c
open Ren public

rename : Ren Γ Δ → Rxn Γ τ n → Rxn Δ τ n
rename ρ (ret v) = ret v
rename ρ (read c k) = read (name ρ c) λ v → rename ρ (k (subst Val (typed ρ c) v))
rename ρ (coin μ k) = coin μ λ b → rename ρ (k b)

Defs : Ctx → Ctx → Set
Defs Γ [] = ⊤
Defs Γ (τ ∷ Δ) = Σ ℕ (Rxn Γ τ) × Defs Γ Δ

record Net (I O : Ctx) : Set where
  field H : Ctx
        def : Defs (I ++ (O ++ H)) (O ++ H)
open Net public

Store : Ctx → Set
Store [] = ⊤
Store (τ ∷ Γ) = Maybe (Val τ) × Store Γ

empty : (Γ : Ctx) → Store Γ
empty [] = tt
empty (τ ∷ Γ) = nothing , empty Γ

lookup : (Γ : Ctx) → Store Γ → (c : Ref Γ) → Maybe (Val (ty Γ c))
lookup (τ ∷ Γ) (v , vs) zero = v
lookup (τ ∷ Γ) (v , vs) (suc c) = lookup Γ vs c

assign : (Γ : Ctx) → Store Γ → (c : Ref Γ) → Val (ty Γ c) → Store Γ
assign (τ ∷ Γ) (w , vs) (suc c) v = w , assign Γ vs c v
assign (τ ∷ Γ) (nothing , vs) zero v = just v , vs
assign (τ ∷ Γ) (just w , vs) zero v = just w , vs

assign-persistent : (Γ : Ctx) (s : Store Γ) (c : Ref Γ) (v w : Val (ty Γ c))
                  → assign Γ (assign Γ s c v) c w ≡ assign Γ s c v
assign-persistent (τ ∷ Γ) (nothing , vs) zero v w = refl
assign-persistent (τ ∷ Γ) (just x , vs) zero v w = refl
assign-persistent (τ ∷ Γ) (x , vs) (suc c) v w = cong (x ,_) (assign-persistent Γ vs c v w)

append : (Γ Δ : Ctx) → Store Γ → Store Δ → Store (Γ ++ Δ)
append [] Δ _ ys = ys
append (τ ∷ Γ) Δ (x , xs) ys = x , append Γ Δ xs ys

take : (Γ Δ : Ctx) → Store (Γ ++ Δ) → Store Γ
take [] Δ s = tt
take (τ ∷ Γ) Δ (x , xs) = x , take Γ Δ xs

Environment : Ctx → Set
Environment Γ = (c : Ref Γ) → Maybe (Val (ty Γ c))

data Cell (Γ : Ctx) (τ : Ty) : Set where
  waiting : (n : ℕ) → Rxn Γ τ n → Cell Γ τ
  assigned : Val τ → Cell Γ τ

Cells : Ctx → Ctx → Set
Cells Γ [] = ⊤
Cells Γ (τ ∷ Δ) = Cell Γ τ × Cells Γ Δ

start : Defs Γ Δ → Cells Γ Δ
start {Δ = []} _ = tt
start {Δ = τ ∷ Δ} ((n , r) , rs) = waiting n r , start rs

value : Cell Γ τ → Maybe (Val τ)
value (waiting _ _) = nothing
value (assigned v) = just v

values : Cells Γ Δ → Store Δ
values {Δ = []} _ = tt
values {Δ = τ ∷ Δ} (c , cs) = value c , values cs

cost : Cell Γ τ → ℕ
cost (waiting n _) = suc n
cost (assigned _) = zero

work : Cells Γ Δ → ℕ
work {Δ = []} _ = zero
work {Δ = τ ∷ Δ} (c , cs) = cost c + work cs
