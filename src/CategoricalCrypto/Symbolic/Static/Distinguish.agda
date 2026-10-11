{-# OPTIONS --safe --without-K --guardedness #-}

-- Completeness for the single-sorted pairing/encryption theory.  A tester
-- queries every frame entry and draws its foreign names; a non-injective
-- renaming restores those names after the existential naming changes.

module CategoricalCrypto.Symbolic.Static.Distinguish where

open import Categories.Category
open import Data.Bool.Base using (true; T)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; _++_; length)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Base using (case_of_)
open import Function.Bundles using (Equivalence; mk⇔)
open import Function.Definitions using (Injective)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does)
open import Relation.Nullary.Decidable using (dec-true; isYes≗does; toWitness)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (returnₚ-bool-injective)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Deduction Σ₀ E₀
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp; void; verdict)
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀ using (module Sym; same⁻¹)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀

import Data.List.Relation.Unary.All as All
import Data.Nat.Properties as Nat
import CategoricalCrypto.Symbolic.Static.Distinguish.Names as N
import CategoricalCrypto.Symbolic.Static.Distinguish.Run as Run
import CategoricalCrypto.Symbolic.Static.Distinguish.Tester as Tester

private
  module D = Run Σ₀ E₀
  module U = Tester Σ₀ E₀

open Terms Σ₀
open EqTheory E₀
open Category.HomReasoning FreeMonoidal

private
  variable
    Δ Ν : List ⊤
    own : Name → Set

  reduce : (K : HomTerm (Ports Δ) (Var verdict)) (f : HomTerm (Var void) (Ports Δ))
         → ((K ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐ ≈Term K ∘ f
  reduce K f = begin
    ((K ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐  ≈⟨ assoc ○ assoc ⟩
    K ∘ (λ⇒ ∘ (id ⊗₁ f ∘ λ⇐))  ≈⟨ refl⟩∘⟨ (⟺ assoc) ⟩
    K ∘ ((λ⇒ ∘ id ⊗₁ f) ∘ λ⇐)  ≈⟨ refl⟩∘⟨ (λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl) ⟩
    K ∘ ((f ∘ λ⇒) ∘ λ⇐)        ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ λ⇒∘λ⇐≈id) ○ idʳ) ⟩
    K ∘ f ∎

  across : {ζs ζs′ : All (Rcp Ν) Δ} (K : HomTerm (Ports Δ) (Var verdict))
         → Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′
         → eval (K ∘ Emitter Ν ζs) true → eval (K ∘ Emitter Ν ζs′) true
  across K e v = Equivalence.to (eval-cong (reduce K _) true)
    (Equivalence.to (same⁻¹ (lower (Sym.KE.run∼ e {lift (unit , K ∘ λ⇒)})) λ⇐ true)
      (Equivalence.from (eval-cong (reduce K _) true) v))

  transfer : ∀ {Δ Ν : List ⊤} {own : Name → Set} {ζs ζs′ : All (Rcp Ν) Δ}
           → Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′ → (κ : ℕ)
           → (∀ {n} → own n → Foreign (frame κ Ν ζs) (frame κ Ν ζs′) n)
           → (ζ ζ′ : Recipe Δ own tt) → ζ ⟨ frame κ Ν ζs ⟩ ≈E ζ′ ⟨ frame κ Ν ζs ⟩
           → ζ ⟨ frame κ Ν ζs′ ⟩ ≈E ζ′ ⟨ frame κ Ν ζs′ ⟩
  transfer {Δ} {Ν} {own} {ζs} {ζs′} e κ foreign ζ ζ′ eq =
    trans (sym (backward ζ p))
      (trans (ren-cong ρ {t = ẑ ⟨ F ⟩} {u = ẑ′ ⟨ F ⟩} tested) (backward ζ′ p′))
    where
    φ = frame κ Ν ζs
    ψ = frame κ Ν ζs′
    ns = N.foreigns ζ ++ N.foreigns ζ′
    Θ = N.sorts ns
    c = length Δ + 0
    p : N.Covers ns ζ
    p = N.cover ζ ∈-++⁺ˡ
    p′ : N.Covers ns ζ′
    p′ = N.cover ζ′ (∈-++⁺ʳ (N.foreigns ζ))
    ẑ = N.hat ζ p
    ẑ′ = N.hat ζ′ p′
    K = var (ports-free Δ , tt , U.tester Θ ẑ ẑ′)

    granted : All (Foreign φ ψ) ns
    granted = All.map foreign (++⁺ (N.owned ζ) (N.owned ζ′))

    fixes : ∀ {n} → n ∈ names* φ → N.choose ns (suc κ) c n ≡ n
    fixes {n} n∈ = N.choose-fix ns (suc κ) c n λ p e → proj₁ (lookup granted p) (subst (_∈ names* φ) (sym e) n∈)

    yes-at-source : D.verdictᵀ Θ ẑ ẑ′ ζs (suc κ) κ ≡ true
    yes-at-source = dec-true (ẑ ⟨ ++⁺ (drawn (suc κ) c Θ) φ ⟩ ≟E ẑ′ ⟨ ++⁺ (drawn (suc κ) c Θ) φ ⟩)
      (subst₂ _≈E_ (N.forward ns ζ p (suc κ) c φ fixes) (N.forward ns ζ′ p′ (suc κ) c φ fixes)
                   (ren-cong (N.choose ns (suc κ) c) {t = ζ ⟨ φ ⟩} {u = ζ′ ⟨ φ ⟩} eq))

    naming : Occ (D.circuit Θ ẑ ẑ′ ζs) → ℕ
    naming (inj₁ _) = suc κ
    naming (inj₂ _) = κ

    fresh : Injective _≡_ _≡_ naming
    fresh {inj₁ tt} {inj₁ tt} _ = refl
    fresh {inj₂ tt} {inj₂ tt} _ = refl
    fresh {inj₁ tt} {inj₂ tt} e = ⊥-elim (Nat.1+n≢n e)
    fresh {inj₂ tt} {inj₁ tt} e = ⊥-elim (Nat.1+n≢n (sym e))

    source : eval (D.circuit Θ ẑ ẑ′ ζs) true
    source = named naming fresh (D.run Θ ẑ ẑ′ ζs naming ⟨≈⟩ ≡⇒≈ₚ (cong returnₚ yes-at-source))

    target : eval (D.circuit Θ ẑ ẑ′ ζs′) true
    target = across K e source

    κᵀ = eval.naming target (inj₁ tt)
    κᵉ = eval.naming target (inj₂ tt)

    distinct : κᵀ ≢ κᵉ
    distinct e = case eval.fresh target {x = inj₁ tt} {y = inj₂ tt} e of λ ()

    ρ = N.restore ns κ κᵀ κᵉ c
    F = ++⁺ (drawn κᵀ c Θ) (frame κᵉ Ν ζs′)

    true-at-target : D.verdictᵀ Θ ẑ ẑ′ ζs′ κᵀ κᵉ ≡ true
    true-at-target = returnₚ-bool-injective
      (≈sym (D.run Θ ẑ ẑ′ ζs′ (eval.naming target)) ⟨≈⟩ eval.answer target)

    tested : ẑ ⟨ F ⟩ ≈E ẑ′ ⟨ F ⟩
    tested = toWitness {a? = ẑ ⟨ F ⟩ ≟E ẑ′ ⟨ F ⟩}
      (subst T (sym (trans (isYes≗does (ẑ ⟨ F ⟩ ≟E ẑ′ ⟨ F ⟩)) true-at-target)) tt)

    backward : (ζ : Recipe Δ own tt) (p : N.Covers ns ζ) → ren ρ (N.hat ζ p ⟨ F ⟩) ≈E ζ ⟨ ψ ⟩
    backward ζ p = N.backward ns ζ p κ κᵀ κᵉ c ψ (frame κᵉ Ν ζs′) distinct (N.frame-restore ns κ κᵀ κᵉ c Ν ζs′)

≈ℰ⇒≈ₛ : {Δ Ν : List ⊤} {ζs ζs′ : All (Rcp Ν) Δ}
      → Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′ → ∀ κ → frame κ Ν ζs ≈ₛ frame κ Ν ζs′
≈ℰ⇒≈ₛ e κ ζ ζ′ = mk⇔ (transfer e κ (λ p → p) ζ ζ′)
  (transfer (Sym.≈ℰ-sym e) κ (λ p → proj₂ p , proj₁ p) ζ ζ′)
