{-# OPTIONS --safe --without-K #-}

-- A checked name-collapse model of the renaming-only contract, its public
-- forgery, and rejection by admissible EqTheory; positive E₀ consumers below.

module CategoricalCrypto.Symbolic.TheoryTests where

open import Categories.FreeMonoidal
open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base using (zero)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product
open import Data.Unit
open import Function.Base
open import Function.Bundles
open import Relation.Binary using (Decidable; IsEquivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary using (∅)

open import CategoricalCrypto.Symbolic.Term

import Data.Bool.Properties as Bool
import CategoricalCrypto.Symbolic.Deduction as Deduction
import CategoricalCrypto.Symbolic.Role as Role
import CategoricalCrypto.Symbolic.Term.PairEnc as PairEnc

module Collapse where
  Σᶜ : Signature
  Σᶜ = record
    { Sort = ⊤ ; Sym = Bool ; dom = λ _ → [] ; cod = λ _ → tt
    ; _≟ˢ_ = λ _ _ → yes refl ; _≟ᶠ_ = Bool._≟_ }

  open Terms Σᶜ

  c₀ c₁ : Tm tt
  c₀ = app false []
  c₁ = app true []

  collapse : ∀ {s} → Tm s → Tm s
  collapse {tt} (name _) = c₀
  collapse (app b []) = app b []

  infix 4 _≈collapse_
  _≈collapse_ : ∀ {s} → Tm s → Tm s → Set
  t ≈collapse u = collapse t ≡ collapse u

  collapse-equiv : ∀ {s} → IsEquivalence (_≈collapse_ {s})
  collapse-equiv = record { refl = refl ; sym = sym ; trans = trans }

  collapse-app-cong : ∀ f {ts us} → All₂ _≈collapse_ ts us → app f ts ≈collapse app f us
  collapse-app-cong _ [] = refl

  collapse-ren : ∀ ρ {s} (t : Tm s) → collapse (ren ρ t) ≡ collapse t
  collapse-ren ρ (name {tt} _) = refl
  collapse-ren ρ (app _ []) = refl

  collapse-ren-cong : ∀ ρ {s} {t u : Tm s} → t ≈collapse u → ren ρ t ≈collapse ren ρ u
  collapse-ren-cong ρ {t = t} {u} e = trans (collapse-ren ρ t) (trans e (sym (collapse-ren ρ u)))

  collapse-dec : ∀ {s} → Decidable (_≈collapse_ {s})
  collapse-dec t u = collapse t ≟ᵗ collapse u

  collapse-nontrivial : ∀ s → ∃₂ λ (t u : Tm s) → ¬ t ≈collapse u
  collapse-nontrivial tt = c₀ , c₁ , λ ()

  collapse-canon-≈ : ∀ {s} (t : Tm s) → collapse t ≈collapse t
  collapse-canon-≈ (name {tt} _) = refl
  collapse-canon-≈ (app _ []) = refl

  collapse-complete : ∀ {s} {t u : Tm s} → t ≈collapse u → collapse t ≡ collapse u
  collapse-complete e = e

  collapse-canon-names : ∀ {s} (t : Tm s) {n} → n ∈ names (collapse t) → n ∈ names t
  collapse-canon-names (name {tt} _) ()
  collapse-canon-names (app _ []) ()

  public-guess : Recipe [] ∅ tt
  public-guess = app false []

  public-forgery : ∀ n → public-guess ⟨ [] ⟩ ≈collapse name n
  public-forgery _ = refl

  owned-forgery : ∀ n m → ((Recipe [] (_≡ n) tt ∋ mine n refl) ⟨ [] ⟩) ≈collapse name m
  owned-forgery _ _ = refl

  guard-accepts-forgery : does (collapse-dec (public-guess ⟨ [] ⟩) (name (7 , 0))) ≡ true
  guard-accepts-forgery = refl

  collapse-not-subst-closed : ¬ (∀ (σ : Substitution) {s} {t u : Tm s}
                              → t ≈collapse u → substᵗ σ t ≈collapse substᵗ σ u)
  collapse-not-subst-closed closed = c₁≢c₀
    (closed (λ { {tt} _ → c₁ }) {t = name (7 , 0)} {u = c₀} refl)
    where
    c₁≢c₀ : ¬ c₁ ≈collapse c₀
    c₁≢c₀ ()

  collapse-not-EqTheory : (E : EqTheory Σᶜ)
                       → ¬ (∀ {s} (t u : Tm s) → EqTheory._≈E_ E t u ⇔ t ≈collapse u)
  collapse-not-EqTheory E represents = EqTheory.fresh-name E (λ ())
    (Equivalence.from (represents (name (7 , 0)) c₀) refl)

module SortedOccurrences where
  Σ² : Signature
  Σ² = record
    { Sort = Bool ; Sym = ⊥ ; dom = λ () ; cod = λ ()
    ; _≟ˢ_ = Bool._≟_ ; _≟ᶠ_ = λ () }

  open Terms Σ²

  free : EqTheory Σ²
  free = record
    { _≈E_ = _≡_ ; isEquiv = record { refl = refl ; sym = sym ; trans = trans }
    ; app-cong = λ () ; subst-cong = λ σ e → cong (substᵗ σ) e
    ; _≟E_ = _≟ᵗ_ ; nontrivial = λ _ → name (0 , 0) , name (0 , 1) , λ ()
    ; canon = id ; canon-≈E = λ _ → refl ; ≈E⇒canon = id ; canon-names = λ _ p → p }

  split-sort : Substitution
  split-sort {false} _ = name (1 , 0)
  split-sort {true} _ = name (2 , 0)

  split-first : substᵗ split-sort (name {false} (0 , 0)) ≡ name (1 , 0)
  split-first = refl

  split-second : substᵗ split-sort (name {true} (0 , 0)) ≡ name (2 , 0)
  split-second = refl

  -- Ownership is still by raw code, not by sort. This witness deliberately
  -- records the representation limit, not a solved sorted-name migration.
  owned-at-two-sorts : Recipe [] (_≡ (0 , 0)) false × Recipe [] (_≡ (0 , 0)) true
  owned-at-two-sorts = mine (0 , 0) refl , mine (0 , 0) refl

module Supported where
  open PairEnc
  open Terms Σ₀
  open EqTheory E₀
  open Deduction Σ₀ E₀
  open Role Σ₀
  open FreeMonoidalHelper Mon Atom
  open Run E₀

  private variable n m : Name

  E₀-substitution : ∀ (σ : Substitution) {t u : Msg} → t ≈E u → substᵗ σ t ≈E substᵗ σ u
  E₀-substitution σ {t} {u} = subst-cong σ {t = t} {u = u}

  E₀-sort-blind : SortBlind
  E₀-sort-blind = renˢ-cong

  fresh-distinct : n ≢ m → ¬ name {tt} n ≈E name m
  fresh-distinct n≢m = distinct-names n≢m

  public-cannot-guess : ∀ n → ¬ ([] , ∅) ⊢ name {tt} n
  public-cannot-guess _ = ⊬-fresh (λ ()) (λ ())

  other-occurrence-cannot-guess : ¬ ([] , Own 1) ⊢ name {tt} (0 , 0)
  other-occurrence-cannot-guess = ⊬-fresh (λ ()) (λ ())

  fresh-emitter : Role (Var void) (Var (port tt tt))
  fresh-emitter = record
    { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
    ; react = λ where
        zero (here refl) _ → new tt (emit zero [] (here refl) (var (here refl)))
        zero (there ()) _ }

  fresh-emitter-cannot-hit-secret : ¬ name {tt} (7 , 0) ≈E name (8 , 0)
  fresh-emitter-cannot-hit-secret = emits≉fresh 7 fresh-emitter
    [] (here refl ↦ app (cst 0) []) (here refl) (λ ()) (λ ()) refl

  public-guard : React 1 (λ _ → []) (flag ∷ []) []
  public-guard = new tt (test (var (here refl)) (app (cst 0) [])
    (emit zero [] (here refl) true) (emit zero [] (here refl) false))

  public-guard-rejects : proj₂ (exec 7 public-guard [] 0) ≡ (here refl ↦ false)
  public-guard-rejects = refl

  fresh-guard : React 1 (λ _ → []) (flag ∷ []) (tt ∷ [])
  fresh-guard = new tt (test (var (here refl)) (var (there (here refl)))
    (emit zero [] (here refl) true) (emit zero [] (here refl) false))

  fresh-guard-rejects-other : proj₂ (exec 7 fresh-guard (name (8 , 0) ∷ []) 0) ≡ (here refl ↦ false)
  fresh-guard-rejects-other = refl

  fresh-guard-accepts-self : proj₂ (exec 7 fresh-guard (name (7 , 0) ∷ []) 0) ≡ (here refl ↦ true)
  fresh-guard-accepts-self = refl
