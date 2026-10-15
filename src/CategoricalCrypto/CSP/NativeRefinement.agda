{-# OPTIONS --safe --without-K --guardedness #-}

open import Data.Bool.Base
module CategoricalCrypto.CSP.NativeRefinement (E B : Set) (sync : E → Bool) where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.CSP.Confinement as Confinement
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.Process as Core
import CategoricalCrypto.CSP.ReadyRefinement as Refinement

module O = Operators E B sync
module P = Parallel E B sync
module L = Core E O.Index ⊤
module R = Refinement E O.Index ⊤
module C = Confinement E O.Index ⊤
open O
open L
open L.Tree
open R
open C

private variable
  p q p′ q′ t : Tree
  e : E
  l : Label

return-force : p ─[ visible (√ tt) ]→ t → force p ≡ ret tt
return-force (sRet eq) = eq

view-absent : (∀ t → p ─[ visible (event e) ]→ t → ⊥) → viewV (force p) e ≡ nothing
view-absent {p = p} {e = e} absent = invert (viewV (force p) e) refl
  where
  invert : (m : Maybe Tree) → viewV (force p) e ≡ m → m ≡ nothing
  invert nothing eq = refl
  invert (just t) eq = ⊥-elim (absent t (P.view-visible eq))

hide-visible-view : ∀ hide n e → viewV (hide-force hide n) e ≡ hide-result hide (not (hide e)) (viewV n e)
hide-visible-view hide (ret tt) e with hide e
... | true = refl
... | false = refl
hide-visible-view hide (sil t) e with hide e
... | true = refl
... | false = refl
hide-visible-view hide (react v b) e = refl

data Kept (hide : E → Bool) (p : Tree) (e : E) : Tree → Set where
  kept : ∀ {p′} → hide e ≡ false → p ─[ visible (event e) ]→ p′ → Kept hide p e (Hide hide p′)

hide-visible-result : ∀ hide (b : Bool) (m : Maybe Tree) → hide e ≡ b → viewV (force p) e ≡ m
  → hide-result hide (not b) m ≡ just t → Kept hide p e t
hide-visible-result hide true m inside offered ()
hide-visible-result hide false nothing outside offered ()
hide-visible-result hide false (just p′) outside offered refl = kept outside (P.view-visible offered)

hide-visible-invert : ∀ hide → Hide hide p ─[ visible (event e) ]→ t → Kept hide p e t
hide-visible-invert {p = p} {e = e} hide step = hide-visible-result hide (hide e) (viewV (force p) e) refl refl
  (trans (sym (hide-visible-view hide (force p) e)) (P.visible-view step))

mutual
  hide-refines : ∀ hide → p ⊑ q → Hide hide p ⊑ Hide hide q
  _⊑_.match (hide-refines hide ref) {l = τ} step = hidden-silent-match hide ref (P.hide-silent-invert hide step)
  _⊑_.match (hide-refines hide ref) {l = visible (event e)} step = hidden-visible-match hide ref (hide-visible-invert hide step)
  _⊑_.match (hide-refines hide ref) {l = visible (√ tt)} step = hidden-return-match hide ref (P.hide-return-invert hide step)
  _⊑_.ready (hide-refines hide ref) {l = τ} (t , step) = hidden-silent-ready hide ref (P.hide-silent-invert hide step)
  _⊑_.ready (hide-refines hide ref) {l = visible (event e)} (t , step) = hidden-visible-ready hide ref (hide-visible-invert hide step)
  _⊑_.ready (hide-refines hide ref) {l = visible (√ tt)} (t , step) = hidden-return-ready hide ref (P.hide-return-invert hide step)

  hidden-silent-match : ∀ hide → p ⊑ q → P.HideSilent hide q t
    → Σ Tree (λ s → Hide hide p ─[ τ ]→ s × s ⊑ t)
  hidden-silent-match hide ref (P.original step) = finish (_⊑_.match ref step)
    where
    finish : Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _) → Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _)
    finish (s , move , next) = Hide hide s , P.hide-silent-step hide move , hide-refines hide next
  hidden-silent-match hide ref (P.concealed-event inside step) = finish (_⊑_.match ref step)
    where
    finish : Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _) → Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _)
    finish (s , move , next) = Hide hide s , P.hide-hidden hide inside move , hide-refines hide next

  hidden-visible-match : ∀ hide → p ⊑ q → Kept hide q e t
    → Σ Tree (λ s → Hide hide p ─[ visible (event e) ]→ s × s ⊑ t)
  hidden-visible-match hide ref (kept outside step) = finish (_⊑_.match ref step)
    where
    finish : Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _) → Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
    finish (s , move , next) = Hide hide s , P.hide-keep hide outside move , hide-refines hide next

  hidden-return-match : ∀ hide → p ⊑ q → force q ≡ ret tt × t ≡ stop
    → Σ Tree (λ s → Hide hide p ─[ visible (√ tt) ]→ s × s ⊑ t)
  hidden-return-match hide ref (eq , refl) = finish (_⊑_.match ref (sRet eq))
    where
    finish : Σ Tree (λ s → _ ─[ visible (√ tt) ]→ s × s ⊑ stop)
      → Σ Tree (λ s → _ ─[ visible (√ tt) ]→ s × s ⊑ stop)
    finish (s , sRet ready , next) = stop , P.hide-return hide ready , reflexive

  hidden-silent-ready : ∀ hide → p ⊑ q → P.HideSilent hide p t → Enabled (Hide hide q) τ
  hidden-silent-ready hide ref (P.original step) = finish (_⊑_.ready ref (_ , step))
    where
    finish : Enabled _ τ → Enabled (Hide hide _) τ
    finish (s , move) = Hide hide s , P.hide-silent-step hide move
  hidden-silent-ready hide ref (P.concealed-event inside step) = finish (_⊑_.ready ref (_ , step))
    where
    finish : Enabled _ (visible (event _)) → Enabled (Hide hide _) τ
    finish (s , move) = Hide hide s , P.hide-hidden hide inside move

  hidden-visible-ready : ∀ hide → p ⊑ q → Kept hide p e t → Enabled (Hide hide q) (visible (event e))
  hidden-visible-ready hide ref (kept outside step) = finish (_⊑_.ready ref (_ , step))
    where
    finish : Enabled _ (visible (event _)) → Enabled (Hide hide _) (visible (event _))
    finish (s , move) = Hide hide s , P.hide-keep hide outside move

  hidden-return-ready : ∀ hide → p ⊑ q → force p ≡ ret tt × t ≡ stop → Enabled (Hide hide q) (visible (√ tt))
  hidden-return-ready hide ref (eq , refl) = finish (_⊑_.ready ref (stop , sRet eq))
    where
    finish : Enabled _ (visible (√ tt)) → Enabled (Hide hide _) (visible (√ tt))
    finish (s , sRet ready) = stop , P.hide-return hide ready

module Separated (α β : Alpha)
  (disjoint : ∀ e → sync e ≡ false → α e → β e → ⊥) where

  left-event : OffersOnly α p → OffersOnly β q → sync e ≡ false
    → p ─[ visible (event e) ]→ p′ → Par p q ─[ visible (event e) ]→ Par p′ q
  left-event cp cq outside step = P.par-left-visible outside step
    (view-absent (λ _ other → sep-from-OffersOnly cp cq disjoint outside step other))

  right-event : OffersOnly α p → OffersOnly β q → sync e ≡ false
    → q ─[ visible (event e) ]→ q′ → Par p q ─[ visible (event e) ]→ Par p q′
  right-event cp cq outside step = P.par-right-visible outside
    (view-absent (λ _ other → sep-from-OffersOnly cp cq disjoint outside other step)) step

  mutual
    par-refines : p ⊑ p′ → q ⊑ q′ → OffersOnly α p → OffersOnly β q
      → OffersOnly α p′ → OffersOnly β q′ → Par p q ⊑ Par p′ q′
    _⊑_.match (par-refines rp rq cp cq cp′ cq′) {l = τ} step =
      silent-match rp rq cp cq cp′ cq′ (P.par-silent-invert step)
    _⊑_.match (par-refines rp rq cp cq cp′ cq′) {l = visible (event e)} step =
      visible-match rp rq cp cq cp′ cq′
        (P.par-visible-invert (sep-from-OffersOnly cp′ cq′ disjoint) step)
    _⊑_.match (par-refines rp rq cp cq cp′ cq′) {l = visible (√ tt)} step =
      return-match rp rq (P.par-return-invert step)
    _⊑_.ready (par-refines rp rq cp cq cp′ cq′) {l = τ} (t , step) =
      silent-ready rp rq (P.par-silent-invert step)
    _⊑_.ready (par-refines rp rq cp cq cp′ cq′) {l = visible (event e)} (t , step) =
      visible-ready rp rq cp′ cq′ (P.par-visible-invert (sep-from-OffersOnly cp cq disjoint) step)
    _⊑_.ready (par-refines rp rq cp cq cp′ cq′) {l = visible (√ tt)} (t , step) =
      return-ready rp rq (P.par-return-invert step)

    silent-match : p ⊑ p′ → q ⊑ q′ → OffersOnly α p → OffersOnly β q
      → OffersOnly α p′ → OffersOnly β q′ → P.SilentMove p′ q′ t
      → Σ Tree (λ s → Par p q ─[ τ ]→ s × s ⊑ t)
    silent-match rp rq cp cq cp′ cq′ (P.left-silent step) = finish (_⊑_.match rp step)
      where
      finish : Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _) → Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _)
      finish (s , move , next) = Par s _ , P.par-left-silent move ,
        par-refines next rq (OffersOnly.after cp move) cq (OffersOnly.after cp′ step) cq′
    silent-match rp rq cp cq cp′ cq′ (P.right-silent step) = finish (_⊑_.match rq step)
      where
      finish : Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _) → Σ Tree (λ s → _ ─[ τ ]→ s × s ⊑ _)
      finish (s , move , next) = Par _ s , P.par-right-silent move ,
        par-refines rp next cp (OffersOnly.after cq move) cp′ (OffersOnly.after cq′ step)

    visible-match : p ⊑ p′ → q ⊑ q′ → OffersOnly α p → OffersOnly β q
      → OffersOnly α p′ → OffersOnly β q′ → P.VisibleMove p′ q′ e t
      → Σ Tree (λ s → Par p q ─[ visible (event e) ]→ s × s ⊑ t)
    visible-match rp rq cp cq cp′ cq′ (P.together inside sp sq) = finish (_⊑_.match rp sp) (_⊑_.match rq sq)
      where
      finish : Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
        → Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
        → Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
      finish (s , move , next) (u , move′ , next′) = Par s u , P.par-sync inside move move′ ,
        par-refines next next′ (OffersOnly.after cp move) (OffersOnly.after cq move′)
          (OffersOnly.after cp′ sp) (OffersOnly.after cq′ sq)
    visible-match rp rq cp cq cp′ cq′ (P.only-left outside sp) = finish (_⊑_.match rp sp)
      where
      finish : Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
        → Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
      finish (s , move , next) = Par s _ , left-event cp cq outside move ,
        par-refines next rq (OffersOnly.after cp move) cq (OffersOnly.after cp′ sp) cq′
    visible-match rp rq cp cq cp′ cq′ (P.only-right outside sq) = finish (_⊑_.match rq sq)
      where
      finish : Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
        → Σ Tree (λ s → _ ─[ visible (event _) ]→ s × s ⊑ _)
      finish (s , move , next) = Par _ s , right-event cp cq outside move ,
        par-refines rp next cp (OffersOnly.after cq move) cp′ (OffersOnly.after cq′ sq)

    return-match : p ⊑ p′ → q ⊑ q′ → force p′ ≡ ret tt × force q′ ≡ ret tt × t ≡ stop
      → Σ Tree (λ s → Par p q ─[ visible (√ tt) ]→ s × s ⊑ t)
    return-match rp rq (ep , eq , refl) = finish (_⊑_.match rp (sRet ep)) (_⊑_.match rq (sRet eq))
      where
      finish : Σ Tree (λ s → _ ─[ visible (√ tt) ]→ s × s ⊑ stop)
        → Σ Tree (λ s → _ ─[ visible (√ tt) ]→ s × s ⊑ stop)
        → Σ Tree (λ s → _ ─[ visible (√ tt) ]→ s × s ⊑ stop)
      finish (s , sRet ep′ , _) (u , sRet eq′ , _) = stop , P.par-return ep′ eq′ , reflexive

    silent-ready : p ⊑ p′ → q ⊑ q′ → P.SilentMove p q t → Enabled (Par p′ q′) τ
    silent-ready rp rq (P.left-silent step) = finish (_⊑_.ready rp (_ , step))
      where
      finish : Enabled _ τ → Enabled (Par _ _) τ
      finish (s , move) = Par s _ , P.par-left-silent move
    silent-ready rp rq (P.right-silent step) = finish (_⊑_.ready rq (_ , step))
      where
      finish : Enabled _ τ → Enabled (Par _ _) τ
      finish (s , move) = Par _ s , P.par-right-silent move

    visible-ready : p ⊑ p′ → q ⊑ q′ → OffersOnly α p′ → OffersOnly β q′
      → P.VisibleMove p q e t → Enabled (Par p′ q′) (visible (event e))
    visible-ready rp rq cp′ cq′ (P.together inside sp sq) = finish (_⊑_.ready rp (_ , sp)) (_⊑_.ready rq (_ , sq))
      where
      finish : Enabled _ (visible (event _)) → Enabled _ (visible (event _))
        → Enabled (Par _ _) (visible (event _))
      finish (s , move) (u , move′) = Par s u , P.par-sync inside move move′
    visible-ready rp rq cp′ cq′ (P.only-left outside sp) = finish (_⊑_.ready rp (_ , sp))
      where
      finish : Enabled _ (visible (event _)) → Enabled (Par _ _) (visible (event _))
      finish (s , move) = Par s _ , left-event cp′ cq′ outside move
    visible-ready rp rq cp′ cq′ (P.only-right outside sq) = finish (_⊑_.ready rq (_ , sq))
      where
      finish : Enabled _ (visible (event _)) → Enabled (Par _ _) (visible (event _))
      finish (s , move) = Par _ s , right-event cp′ cq′ outside move

    return-ready : p ⊑ p′ → q ⊑ q′ → force p ≡ ret tt × force q ≡ ret tt × t ≡ stop
      → Enabled (Par p′ q′) (visible (√ tt))
    return-ready rp rq (ep , eq , refl) = finish (_⊑_.ready rp (stop , sRet ep)) (_⊑_.ready rq (stop , sRet eq))
      where
      finish : Enabled _ (visible (√ tt)) → Enabled _ (visible (√ tt)) → Enabled (Par _ _) (visible (√ tt))
      finish (s , sRet ep′) (u , sRet eq′) = stop , P.par-return ep′ eq′
