{-# OPTIONS --safe --without-K --guardedness #-}

-- One-sided domination at a FIXED test, with rational slack.
--
-- `_≼ₚ_` quantifies over every non-negative test, and `_≼ₚ[_]_` over the two
-- verdict indicators; both are "every budget of the left is matched at SOME
-- budget of the right".  A transfer that is only valid at one test — a
-- truncation that scores 0 under `indᵇ b` but 1 under `indᵇ (not b)`, say —
-- has neither shape, so `Dom` is that shape with the test fixed:
--
--     Dom P ε d e   =   no budget of `d` beats every budget of `e` by more than ε
--
-- and `d ≼ₚ[ ε ] e` is `∀ b → Dom (indᵇ b) ε d e`, definitionally.
--
-- `cum-shift` is the convexity that lets the slack cross a bind: a `Dₚ` node's
-- two weights sum to one, so averaging `P + ε` over the branches is averaging
-- `P` and adding ε — never more.  It is what `dom-bind` spends, and it is the
-- reason a branchwise ε-bound reassembles into one ε-bound.

open import Data.Bool.Base using (true; false)
open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_)
open import Data.Product.Base using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ)
open import Data.Rational.Properties as ℚP
open import Data.Nat.Properties as ℕP using ()
open import Data.Rational.Solver using (module +-*-Solver)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter using (returnₚ-cum-≤)

module ProbabilisticLogic.Dp.Dominate where

private variable
  a : Level
  A B : Set a
  P : A → ℚ
  ε δ : ℚ
  d e h : Dₚ A

------------------------------------------------------------------------
-- Convexity: a slack survives an average

private
  spread : (w₁ w₂ x₁ x₂ e : ℚ)
         → w₁ ℚ.* (x₁ ℚ.+ e) ℚ.+ w₂ ℚ.* (x₂ ℚ.+ e)
           ≡ (w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂) ℚ.+ (w₁ ℚ.+ w₂) ℚ.* e
  spread = solve 5 (λ w₁ w₂ x₁ x₂ e →
    w₁ :* (x₁ :+ e) :+ w₂ :* (x₂ :+ e) := (w₁ :* x₁ :+ w₂ :* x₂) :+ (w₁ :+ w₂) :* e) refl
    where open +-*-Solver

  mix : (w₁ w₂ x₁ x₂ e : ℚ) → w₁ ℚ.+ w₂ ≡ 1ℚ
      → w₁ ℚ.* (x₁ ℚ.+ e) ℚ.+ w₂ ℚ.* (x₂ ℚ.+ e) ≡ (w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂) ℚ.+ e
  mix w₁ w₂ x₁ x₂ e eq =
    trans (spread w₁ w₂ x₁ x₂ e)
          (cong ((w₁ ℚ.* x₁ ℚ.+ w₂ ℚ.* x₂) ℚ.+_)
                (trans (cong (ℚ._* e) eq) (*-identityˡ e)))

mutual
  cum-shift : (n : ℕ) (d : Dₚ A) (P : A → ℚ) (ε : ℚ) → 0ℚ ℚ.≤ ε
            → cum n d (λ p → P p ℚ.+ ε) ℚ.≤ cum n d P ℚ.+ ε
  cum-shift zero    d P ε 0≤ε = ≤-trans 0≤ε (≤-reflexive (sym (+-identityˡ ε)))
  cum-shift (suc n) d P ε 0≤ε =
    ≤-trans (node-mono (wt d true) (wt d false) (wt-nn d true) (wt-nn d false)
                       (leafₚ-shift n (br d true) P ε 0≤ε)
                       (leafₚ-shift n (br d false) P ε 0≤ε))
            (≤-reflexive (mix (wt d true) (wt d false)
                              (leafₚ n (br d true) P) (leafₚ n (br d false) P)
                              ε (wt-1 d)))

  leafₚ-shift : (n : ℕ) (x : A ⊎ Dₚ A) (P : A → ℚ) (ε : ℚ) → 0ℚ ℚ.≤ ε
              → leafₚ n x (λ p → P p ℚ.+ ε) ℚ.≤ leafₚ n x P ℚ.+ ε
  leafₚ-shift n (inj₁ p)  P ε 0≤ε = ≤-refl
  leafₚ-shift n (inj₂ d′) P ε 0≤ε = cum-shift n d′ P ε 0≤ε

-- A test that vanishes on every value a run can reach scores it at nothing —
-- the `cum`-level reading of "this branch is not the verdict observed".
mutual
  cum-zero : (n : ℕ) (d : Dₚ A) → cum n d (λ _ → 0ℚ) ≡ 0ℚ
  cum-zero zero    d = refl
  cum-zero (suc n) d =
    trans (cong₂ ℚ._+_ (cong (wt d true ℚ.*_) (leafₚ-zero n (br d true)))
                       (cong (wt d false ℚ.*_) (leafₚ-zero n (br d false))))
          (node-zero (wt d true) (wt d false))

  leafₚ-zero : (n : ℕ) (x : A ⊎ Dₚ A) → leafₚ n x (λ _ → 0ℚ) ≡ 0ℚ
  leafₚ-zero n (inj₁ p)  = refl
  leafₚ-zero n (inj₂ d′) = cum-zero n d′

bind-const-zero : {A B : Set a} (P : B → ℚ) → NNF P → (c : B) → P c ≡ 0ℚ
                → (d : Dₚ A) (n : ℕ) → cum n (d >>=ₚ λ _ → returnₚ c) P ℚ.≤ 0ℚ
bind-const-zero P nn c eq d n =
  ≤-trans (>>=ₚ-boundA n d (λ _ → returnₚ c) P nn)
  (≤-trans (cum-mono-P n d (λ _ → cum n (returnₚ c) P) (λ _ → 0ℚ)
             (λ _ → ≤-trans (returnₚ-cum-≤ n c P nn) (≤-reflexive eq)))
           (≤-reflexive (cum-zero n d)))

------------------------------------------------------------------------
-- The relation

-- The slack-free form, and the form carrying one.  A chain is written in the
-- slack-free one and picks the slack up at the single step that spends it.
Dom₀ : (A → ℚ) → Dₚ A → Dₚ A → Set
Dom₀ P d e = (n : ℕ) → Σ[ m ∈ ℕ ] (cum n d P ℚ.≤ cum m e P)

-- The same, bounded: a target faithful only to a depth is dominated only up
-- to that depth (`UC.Seam.Extract`'s truncation is the case in point).
Dom≤ : (A → ℚ) → ℕ → Dₚ A → Dₚ A → Set
Dom≤ P f d e = (n : ℕ) → n ≤ℕ f → Σ[ m ∈ ℕ ] (cum n d P ℚ.≤ cum m e P)

dom≤⇒dom₀ : ((f : ℕ) → Dom≤ P f d e) → Dom₀ P d e
dom≤⇒dom₀ h n = h n n ℕP.≤-refl

Dom : (A → ℚ) → ℚ → Dₚ A → Dₚ A → Set
Dom P ε d e = (n : ℕ) → Σ[ m ∈ ℕ ] (cum n d P ℚ.≤ cum m e P ℚ.+ ε)

dom₀-refl : (P : A → ℚ) (d : Dₚ A) → Dom₀ P d d
dom₀-refl P d n = n , ≤-refl

dom₀-trans : Dom₀ P d e → Dom₀ P e h → Dom₀ P d h
dom₀-trans p q n = let m , bd = p n
                       i , cd = q m
                   in i , ≤-trans bd cd

-- The two ways an ambient `_≈ₚ_` enters a domination chain.
≼⇒dom₀ : (P : A → ℚ) → NNF P → (d e : Dₚ A) → d ≼ₚ e → Dom₀ P d e
≼⇒dom₀ P nn d e le n = le P nn n

≈⇒dom₀ : (P : A → ℚ) → NNF P → (d e : Dₚ A) → d ≈ₚ e → Dom₀ P d e
≈⇒dom₀ P nn d e de = ≼⇒dom₀ P nn d e (proj₁ de)

dom₀⇒dom : 0ℚ ℚ.≤ ε → Dom₀ P d e → Dom P ε d e
dom₀⇒dom {ε = ε} {P = P} {e = e} 0≤ε dm n =
  let m , bd = dm n
  in m , ≤-trans bd (≤-trans (≤-reflexive (sym (+-identityʳ (cum m e P))))
                             (+-monoʳ-≤ (cum m e P) 0≤ε))

dom⇒dom₀ : Dom P 0ℚ d e → Dom₀ P d e
dom⇒dom₀ {P = P} {e = e} dm n =
  let m , bd = dm n in m , ≤-trans bd (≤-reflexive (+-identityʳ (cum m e P)))

dom-mono : ε ℚ.≤ δ → Dom P ε d e → Dom P δ d e
dom-mono {P = P} {e = e} le dm n =
  let m , bd = dm n in m , ≤-trans bd (+-monoʳ-≤ (cum m e P) le)

domˡ : Dom₀ P d e → Dom P ε e h → Dom P ε d h
domˡ p q n = let m , bd = p n
                 i , cd = q m
             in i , ≤-trans bd cd

domʳ : Dom P ε d e → Dom₀ P e h → Dom P ε d h
domʳ {ε = ε} p q n = let m , bd = p n
                         i , cd = q m
                     in i , ≤-trans bd (+-monoˡ-≤ ε cd)

------------------------------------------------------------------------
-- The bind congruence
--
-- The continuation's per-value witnesses are maxed out over a depth-`n`
-- support (`uniformize`, as in `>>=ₚ-congᵖ`) and the branchwise slacks are
-- averaged back into one by `cum-shift`.

-- `A`/`B` are module parameters, not `private variable`s: the `where` block's
-- own signatures mention them, and a `variable` there re-generalizes.
module _ {A B : Set a} (P : B → ℚ) (nn : NNF P) {ε : ℚ} (0≤ε : 0ℚ ℚ.≤ ε)
         (d : Dₚ A) (f g : A → Dₚ B) (dm : (p : A) → Dom P ε (f p) (g p)) where

  dom-bind : Dom P ε (d >>=ₚ f) (d >>=ₚ g)
  dom-bind n =
    n +ℕ i′
    , ≤-trans (>>=ₚ-boundA n d f P nn)
      (≤-trans (cum-mono-Supp n d (λ p → cum n (f p) P) (λ p → cum i′ (g p) P ℚ.+ ε) sp)
      (≤-trans (cum-shift n d (λ p → cum i′ (g p) P) ε 0≤ε)
               (+-monoˡ-≤ ε (>>=ₚ-boundB n i′ d g P nn))))
    where
    Φ : A → ℕ → Set
    Φ p i = cum n (f p) P ℚ.≤ cum i (g p) P ℚ.+ ε

    up : ∀ p {i i′} → i ≤ℕ i′ → Φ p i → Φ p i′
    up p le q = ≤-trans q (+-monoˡ-≤ ε (cum-mono le (g p) P nn))

    unif = uniformize Φ up (λ p → dm p n) n d
    i′ = proj₁ unif
    sp = proj₂ unif

module _ {A B : Set a} (P : B → ℚ) (nn : NNF P) (k : ℕ)
         (d : Dₚ A) (f g : A → Dₚ B) (dm : (p : A) → Dom≤ P k (f p) (g p)) where

  dom≤-bind : Dom≤ P k (d >>=ₚ f) (d >>=ₚ g)
  dom≤-bind n le =
    n +ℕ i′
    , ≤-trans (>>=ₚ-boundA n d f P nn)
      (≤-trans (cum-mono-Supp n d (λ p → cum n (f p) P) (λ p → cum i′ (g p) P) sp)
               (>>=ₚ-boundB n i′ d g P nn))
    where
    Φ : A → ℕ → Set
    Φ p i = cum n (f p) P ℚ.≤ cum i (g p) P

    up : ∀ p {i i′} → i ≤ℕ i′ → Φ p i → Φ p i′
    up p le′ q = ≤-trans q (cum-mono le′ (g p) P nn)

    unif = uniformize Φ up (λ p → dm p n le) n d
    i′ = proj₁ unif
    sp = proj₂ unif

dom₀-bind : {A B : Set a} (P : B → ℚ) → NNF P → (d : Dₚ A) (f g : A → Dₚ B)
          → ((p : A) → Dom₀ P (f p) (g p)) → Dom₀ P (d >>=ₚ f) (d >>=ₚ g)
dom₀-bind P nn d f g dm =
  dom≤⇒dom₀ λ k → dom≤-bind P nn k d f g (λ p n _ → dm p n)
