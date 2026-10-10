{-# OPTIONS --safe --without-K #-}

-- Sorted terms over a signature, with located names; recipes over a frame; the
-- interface of an equational theory (`abadi2018applied` §2.1–2.2 pp. 3–6).  A
-- name is `(occurrence code , counter)`: every generator occurrence of a
-- symbolic circuit draws fresh names from a supply of its own, which is how
-- freshness becomes global (docs/uc-setup-symbolic.md §3.2, §3.5).

module CategoricalCrypto.Symbolic.Term where

open import Axiom.UniquenessOfIdentityProofs
open import Data.Empty
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat
open import Data.Product
open import Data.Product.Properties
open import Data.Unit
open import Function.Base
open import Level
open import Relation.Binary using (DecidableEquality; Decidable; IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary using (_⊆_)

import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.Nat.Properties as ℕ

record Signature : Set₁ where
  field
    Sort Sym : Set
    dom      : Sym → List Sort
    cod      : Sym → Sort
    _≟ˢ_     : DecidableEquality Sort
    _≟ᶠ_     : DecidableEquality Sym

Name : Set
Name = ℕ × ℕ

_≟ₙ_ : DecidableEquality Name
_≟ₙ_ = ≡-dec ℕ._≟_ ℕ._≟_

module Terms (𝔖 : Signature) where
  open Signature 𝔖

  private variable
    s           : Sort
    ss Δ Δ′     : List Sort
    own own′    : Name → Set

  data Tm : Sort → Set where
    name : Name → Tm s
    app  : (f : Sym) → All Tm (dom f) → Tm (cod f)

  -- `ν ñ. σ` with every name of `σ` restricted (`abadi2018applied` §2.1 p. 4)
  Frame : List Sort → Set
  Frame = All Tm

  ren  : (Name → Name) → Tm s → Tm s
  ren* : (Name → Name) → All Tm ss → All Tm ss
  ren ρ (name n)   = name (ρ n)
  ren ρ (app f ts) = app f (ren* ρ ts)
  ren* ρ []       = []
  ren* ρ (t ∷ ts) = ren ρ t ∷ ren* ρ ts

  names  : Tm s → List Name
  names* : All Tm ss → List Name
  names (name n)   = n ∷ []
  names (app _ ts) = names* ts
  names* []       = []
  names* (t ∷ ts) = names t ++ names* ts

  data Each (P : ∀ {s} → Tm s → Set) : ∀ {ss} → All Tm ss → Set where
    []  : Each P []
    _∷_ : {t : Tm s} {ts : All Tm ss} → P t → Each P ts → Each P (t ∷ ts)

  data All₂ (R : ∀ {s} → Tm s → Tm s → Set) : ∀ {ss} → All Tm ss → All Tm ss → Set where
    []  : All₂ R [] []
    _∷_ : {t u : Tm s} {ts us : All Tm ss} → R t u → All₂ R ts us → All₂ R (t ∷ ts) (u ∷ us)

  lookupᴱ : {P : ∀ {s} → Tm s → Set} {ts : All Tm ss} → Each P ts → (i : s ∈ ss) → P (lookup ts i)
  lookupᴱ (p ∷ _)  (here refl) = p
  lookupᴱ (_ ∷ ps) (there i)   = lookupᴱ ps i

  mapᴱ : {P Q : ∀ {s} → Tm s → Set} {ts : All Tm ss} → (∀ {s} {t : Tm s} → P t → Q t) → Each P ts → Each Q ts
  mapᴱ f []       = []
  mapᴱ f (p ∷ ps) = f p ∷ mapᴱ f ps

  ------------------------------------------------------------------------
  -- Syntactic equality, decided in `Σ Sort Tm` and read back at one sort by
  -- UIP: `app f ts ≡ app f us` cannot be split, since its index `cod f` is not
  -- a pattern.

  private
    UIPˢ : UIP Sort
    UIPˢ = Decidable⇒UIP.≡-irrelevant _≟ˢ_

    UIPˡ : UIP (List Sort)
    UIPˡ = Decidable⇒UIP.≡-irrelevant (List.≡-dec _≟ˢ_)

    nameOf : Σ Sort Tm → Maybe Name
    nameOf (_ , name n)  = just n
    nameOf (_ , app _ _) = nothing

    headOf : Σ Sort Tm → Maybe Sym
    headOf (_ , name _)  = nothing
    headOf (_ , app f _) = just f

    argsOf : Σ Sort Tm → Maybe (Σ (List Sort) (All Tm))
    argsOf (_ , name _)   = nothing
    argsOf (_ , app f ts) = just (dom f , ts)

    ≟Σ   : ∀ {s s′} (t : Tm s) (u : Tm s′) → Dec (_≡_ {A = Σ Sort Tm} (s , t) (s′ , u))
    ≟All : (ts us : All Tm ss) → Dec (ts ≡ us)
    ≟Σ {s} {s′} (name n) (name m) with s ≟ˢ s′ | n ≟ₙ m
    ... | yes refl | yes refl = yes refl
    ... | no s≢s′  | _        = no (s≢s′ ∘ ,-injectiveˡ)
    ... | yes _    | no n≢m   = no (n≢m ∘ just-injective ∘ cong nameOf)
    ≟Σ (name _) (app _ _) = no λ e → case cong headOf e of λ ()
    ≟Σ (app _ _) (name _) = no λ e → case cong headOf e of λ ()
    ≟Σ (app f ts) (app g us) with f ≟ᶠ g
    ... | no f≢g = no (f≢g ∘ just-injective ∘ cong headOf)
    ... | yes refl with ≟All ts us
    ...   | yes refl = yes refl
    ...   | no ts≢us = no (ts≢us ∘ ,-injectiveʳ-UIP UIPˡ ∘ just-injective ∘ cong argsOf)
    ≟All []       []       = yes refl
    ≟All (t ∷ ts) (u ∷ us) with ≟Σ t u | ≟All ts us
    ... | yes e   | yes refl = yes (cong (_∷ us) (,-injectiveʳ-UIP UIPˢ e))
    ... | no t≢u  | _        = no (t≢u ∘ cong (_ ,_) ∘ cong All.head)
    ... | yes _   | no ts≢us = no (ts≢us ∘ cong All.tail)

  infix 4 _≟ᵗ_
  _≟ᵗ_ : DecidableEquality (Tm s)
  t ≟ᵗ u = map′ (,-injectiveʳ-UIP UIPˢ) (cong (_ ,_)) (≟Σ t u)

  ------------------------------------------------------------------------
  -- Recipes: public contexts over a frame (`abadicortier2006` §2.3), which may
  -- also use the names `own` grants.

  data Recipe (Δ : List Sort) (own : Name → Set) : Sort → Set where
    var  : s ∈ Δ → Recipe Δ own s
    mine : (n : Name) → own n → Recipe Δ own s
    app  : (f : Sym) → All (Recipe Δ own) (dom f) → Recipe Δ own (cod f)

  infix 8 _⟨_⟩ _⟨_⟩*
  _⟨_⟩  : Recipe Δ own s → Frame Δ → Tm s
  _⟨_⟩* : All (Recipe Δ own) ss → Frame Δ → All Tm ss
  var i    ⟨ φ ⟩ = lookup φ i
  mine n _ ⟨ φ ⟩ = name n
  app f ζs ⟨ φ ⟩ = app f (ζs ⟨ φ ⟩*)
  []       ⟨ φ ⟩* = []
  (ζ ∷ ζs) ⟨ φ ⟩* = ζ ⟨ φ ⟩ ∷ ζs ⟨ φ ⟩*

  bind  : (∀ {s} → s ∈ Δ → Recipe Δ′ own′ s) → own ⊆ own′ → Recipe Δ own s → Recipe Δ′ own′ s
  bind* : (∀ {s} → s ∈ Δ → Recipe Δ′ own′ s) → own ⊆ own′ → All (Recipe Δ own) ss → All (Recipe Δ′ own′) ss
  bind σ h (var i)    = σ i
  bind σ h (mine n p) = mine n (h p)
  bind σ h (app f ζs) = app f (bind* σ h ζs)
  bind* σ h []       = []
  bind* σ h (ζ ∷ ζs) = bind σ h ζ ∷ bind* σ h ζs

  Ground  : Recipe Δ own s → Set
  Ground* : All (Recipe Δ own) ss → Set
  Ground (var _)    = ⊥
  Ground (mine _ _) = ⊤
  Ground (app _ ζs) = Ground* ζs
  Ground* []       = ⊤
  Ground* (ζ ∷ ζs) = Ground ζ × Ground* ζs

------------------------------------------------------------------------
-- An equational theory (`abadi2018applied` §2.2 p. 6): a non-trivial
-- congruence closed under renaming.  Guards are computed, so it is decidable.

record EqTheory (𝔖 : Signature) : Set₁ where
  open Signature 𝔖
  open Terms 𝔖
  infix 4 _≈E_ _≟E_
  field
    _≈E_       : ∀ {s} → Tm s → Tm s → Set
    isEquiv    : ∀ {s} → IsEquivalence (_≈E_ {s})
    app-cong   : ∀ f {ts us} → All₂ _≈E_ ts us → app f ts ≈E app f us
    ren-cong   : ∀ ρ {s} {t u : Tm s} → t ≈E u → ren ρ t ≈E ren ρ u
    _≟E_       : ∀ {s} → Decidable (_≈E_ {s})
    nontrivial : ∀ s → ∃₂ λ (t u : Tm s) → ¬ t ≈E u

  module ≈E {s} = IsEquivalence (isEquiv {s})

  Tm-setoid : Sort → Setoid 0ℓ 0ℓ
  Tm-setoid s = record { Carrier = Tm s ; _≈_ = _≈E_ ; isEquivalence = isEquiv }
