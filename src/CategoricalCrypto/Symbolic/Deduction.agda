{-# OPTIONS --safe --without-K #-}

-- Dolev–Yao deducibility and static equivalence over an equational theory.
-- `K ⊢ M` takes `abadicortier2006` Prop 1 (p. 6) as its definition — a recipe
-- evaluating to `M` modulo E — and `⊢⇔⊢ᵢ` recovers the inference rules of
-- §2.3.  Every name of a frame counts as restricted, so the recipes of `_≈ₛ_`
-- (Def 2 p. 7; `abadi2018applied` Def 4.3 p. 15) use only names foreign to both.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Deduction (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Product
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Unary using (_⊆_)

open Signature 𝔖
open Terms 𝔖
open EqTheory E

private variable
  s        : Sort
  ss Δ Δ′  : List Sort
  own own′ : Name → Set
  n        : Name
  f        : Sym
  t M M′   : Tm s
  ts       : All Tm ss
  φ ψ      : Frame Δ

-- An exposed frame, and the names the deducer may use itself.
Knowledge : List Sort → Set₁
Knowledge Δ = Frame Δ × (Name → Set)

private variable K : Knowledge Δ

infix 4 _⊢_ _⊢ᵢ_

_⊢_ : Knowledge Δ → Tm s → Set
K ⊢ M = Σ[ ζ ∈ Recipe _ (proj₂ K) _ ] ζ ⟨ proj₁ K ⟩ ≈E M

data _⊢ᵢ_ {Δ} (K : Knowledge Δ) : ∀ {s} → Tm s → Set where
  entry : (i : s ∈ Δ) → K ⊢ᵢ lookup (proj₁ K) i
  owned : proj₂ K n → K ⊢ᵢ name {s} n
  apply : Each (K ⊢ᵢ_) ts → K ⊢ᵢ app f ts
  conv  : K ⊢ᵢ M → M ≈E M′ → K ⊢ᵢ M′

private
  eval⊢ᵢ  : (ζ : Recipe Δ (proj₂ K) s) → K ⊢ᵢ ζ ⟨ proj₁ K ⟩
  eval⊢ᵢ* : (ζs : All (Recipe Δ (proj₂ K)) ss) → Each (K ⊢ᵢ_) (ζs ⟨ proj₁ K ⟩*)
  eval⊢ᵢ (var i)    = entry i
  eval⊢ᵢ (mine _ p) = owned p
  eval⊢ᵢ (app _ ζs) = apply (eval⊢ᵢ* ζs)
  eval⊢ᵢ* []       = []
  eval⊢ᵢ* (ζ ∷ ζs) = eval⊢ᵢ ζ ∷ eval⊢ᵢ* ζs

  ⊢ᵢ⇒⊢  : K ⊢ᵢ M → K ⊢ M
  ⊢ᵢ⇒⊢* : Each (K ⊢ᵢ_) ts → Σ[ ζs ∈ All (Recipe _ (proj₂ K)) _ ] All₂ _≈E_ (ζs ⟨ proj₁ K ⟩*) ts
  ⊢ᵢ⇒⊢ (entry i)  = var i , ≈E.refl
  ⊢ᵢ⇒⊢ (owned p)  = mine _ p , ≈E.refl
  ⊢ᵢ⇒⊢ (apply ds) = let ζs , es = ⊢ᵢ⇒⊢* ds in app _ ζs , app-cong _ es
  ⊢ᵢ⇒⊢ (conv d e) = let ζ , e′ = ⊢ᵢ⇒⊢ d in ζ , ≈E.trans e′ e
  ⊢ᵢ⇒⊢* []       = [] , []
  ⊢ᵢ⇒⊢* (d ∷ ds) = let ζ , e = ⊢ᵢ⇒⊢ d ; ζs , es = ⊢ᵢ⇒⊢* ds in ζ ∷ ζs , e ∷ es

⊢⇔⊢ᵢ : K ⊢ M ⇔ K ⊢ᵢ M
⊢⇔⊢ᵢ = mk⇔ (λ (ζ , e) → conv (eval⊢ᵢ ζ) e) ⊢ᵢ⇒⊢

------------------------------------------------------------------------
-- Closure properties

⊢-conv : K ⊢ M → M ≈E M′ → K ⊢ M′
⊢-conv (ζ , e) e′ = ζ , ≈E.trans e e′

⊢-entry : (i : s ∈ Δ) → K ⊢ lookup (proj₁ K) i
⊢-entry i = var i , ≈E.refl

⊢-owned : proj₂ K n → K ⊢ name {s} n
⊢-owned p = mine _ p , ≈E.refl

-- Evaluation commutes with substitution, up to E.
bind-⟨⟩  : (σ : ∀ {s} → s ∈ Δ → Recipe Δ′ own′ s) (h : own ⊆ own′)
         → (∀ {s} (i : s ∈ Δ) → σ i ⟨ ψ ⟩ ≈E lookup φ i)
         → (ζ : Recipe Δ own s) → bind σ h ζ ⟨ ψ ⟩ ≈E ζ ⟨ φ ⟩
bind-⟨⟩* : (σ : ∀ {s} → s ∈ Δ → Recipe Δ′ own′ s) (h : own ⊆ own′)
         → (∀ {s} (i : s ∈ Δ) → σ i ⟨ ψ ⟩ ≈E lookup φ i)
         → (ζs : All (Recipe Δ own) ss) → All₂ _≈E_ (bind* σ h ζs ⟨ ψ ⟩*) (ζs ⟨ φ ⟩*)
bind-⟨⟩ σ h e (var i)    = e i
bind-⟨⟩ σ h e (mine _ _) = ≈E.refl
bind-⟨⟩ σ h e (app f ζs) = app-cong f (bind-⟨⟩* σ h e ζs)
bind-⟨⟩* σ h e []       = []
bind-⟨⟩* σ h e (ζ ∷ ζs) = bind-⟨⟩ σ h e ζ ∷ bind-⟨⟩* σ h e ζs

-- Deduction composes: what is deducible from deducible entries is deducible.
⊢-cut : Each (K ⊢_) φ → own ⊆ proj₂ K → (φ , own) ⊢ M → K ⊢ M
⊢-cut ds h (ζ , e) =
  bind (λ i → proj₁ (lookupᴱ ds i)) h ζ , ≈E.trans (bind-⟨⟩ _ h (λ i → proj₂ (lookupᴱ ds i)) ζ) e

⊢-wk : (φ , own) ⊢ M → (t ∷ φ , own) ⊢ M
⊢-wk (ζ , e) = bind (λ i → var (there i)) (λ p → p) ζ , ≈E.trans (bind-⟨⟩ _ _ (λ _ → ≈E.refl) ζ) e

⊢-own : own ⊆ own′ → (φ , own) ⊢ M → (φ , own′) ⊢ M
⊢-own h (ζ , e) = bind var h ζ , ≈E.trans (bind-⟨⟩ _ h (λ _ → ≈E.refl) ζ) e

------------------------------------------------------------------------
-- Static equivalence

Foreign : Frame Δ → Frame Δ → Name → Set
Foreign φ ψ n = n ∉ names* φ × n ∉ names* ψ

infix 4 _≈ₛ_
_≈ₛ_ : Frame Δ → Frame Δ → Set
φ ≈ₛ ψ = ∀ {s} (ζ ζ′ : Recipe _ (Foreign φ ψ) s) → (ζ ⟨ φ ⟩ ≈E ζ′ ⟨ φ ⟩) ⇔ (ζ ⟨ ψ ⟩ ≈E ζ′ ⟨ ψ ⟩)
