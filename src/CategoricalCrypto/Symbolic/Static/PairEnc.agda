{-# OPTIONS --safe --without-K --guardedness #-}

-- The unrestricted multi-sorted statement has a sort/name obstruction; see
-- docs/uc-setup-symbolic.md §6.  No extra theory hypothesis is needed at E₀.

module CategoricalCrypto.Symbolic.Static.PairEnc where

open import Data.List.Base using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Deduction Σ₀ E₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp)
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ using (module Sym)
open import CategoricalCrypto.Symbolic.Static Σ₀ E₀ using (≈ₛ⇒≈ℰ)
open import CategoricalCrypto.Symbolic.Static.Distinguish using (≈ℰ⇒≈ₛ)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀ using (Emitter; frame)

open Terms Σ₀
open EqTheory E₀

private
  renˢ≡ren : ∀ ρ {s} (t : Tm s) → renˢ ρ t ≡ ren (ρ tt) t
  renˢ*≡ren* : ∀ ρ {ss} (ts : All Tm ss) → renˢ* ρ ts ≡ ren* (ρ tt) ts
  renˢ≡ren ρ (name _) = refl
  renˢ≡ren ρ (app f ts) = cong (app f) (renˢ*≡ren* ρ ts)
  renˢ*≡ren* _ [] = refl
  renˢ*≡ren* ρ (t ∷ ts) = cong₂ _∷_ (renˢ≡ren ρ t) (renˢ*≡ren* ρ ts)

sort-blind : SortBlind
sort-blind ρ {t = t} {u} e = subst₂ _≈E_ (sym (renˢ≡ren ρ t)) (sym (renˢ≡ren ρ u)) (ren-cong (ρ tt) {t = t} {u = u} e)

≈ℰ⇔≈ₛ : {Δ Ν : List ⊤} {ζs ζs′ : All (Rcp Ν) Δ}
      → (Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′) ⇔ (∀ κ → frame κ Ν ζs ≈ₛ frame κ Ν ζs′)
≈ℰ⇔≈ₛ = mk⇔ ≈ℰ⇒≈ₛ ≈ₛ⇒≈ℰ
