{-# OPTIONS --safe --without-K --guardedness #-}

-- Constructive strong interface-parallel/interleaving interchange fragment of
-- ParallelInterchange.agda:478–503 at agda-cardano-common
-- 9a40d1de330f376c3a102e7c9f1282f4fa830a7e. Every visible event belongs to
-- the shared synchronization alphabet; the two channel namespaces are disjoint.
-- OffersOnly is persistent. No DR/FD law or classical normalization is imported.
module CategoricalCrypto.CSP.NativeInterchange (X B : Set) where

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Relation.Binary.PropositionalEquality
open import Data.Unit.Base

import CategoricalCrypto.CSP.Confinement as Confinement
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.Process as Core

module A = Operators (Bool × X) B (λ _ → true)
module I = Operators (Bool × X) B (λ _ → false)
module AP = Parallel (Bool × X) B (λ _ → true)
module IP = Parallel (Bool × X) B (λ _ → false)
module L = Core (Bool × X) A.Index ⊤
module C = Confinement (Bool × X) A.Index ⊤
open L
open L.Tree

record Quad : Set where
  field
    p₁ p₂ q₁ q₂ : Tree
    cp₁ : C.OffersOnly (λ e → proj₁ e ≡ false) p₁
    cp₂ : C.OffersOnly (λ e → proj₁ e ≡ true) p₂
    cq₁ : C.OffersOnly (λ e → proj₁ e ≡ false) q₁
    cq₂ : C.OffersOnly (λ e → proj₁ e ≡ true) q₂
open Quad

left-source right-source : Quad → Tree
left-source f = A.Par (I.Par (p₁ f) (p₂ f)) (I.Par (q₁ f) (q₂ f))
right-source f = I.Par (A.Par (p₁ f) (q₁ f)) (A.Par (p₂ f) (q₂ f))

change-p₁ : ∀ f {l p′} → p₁ f ─[ l ]→ p′ → Quad
change-p₁ f {p′ = p′} sp = record
  { p₁ = p′ ; p₂ = p₂ f ; q₁ = q₁ f ; q₂ = q₂ f
  ; cp₁ = C.OffersOnly.after (cp₁ f) sp ; cp₂ = cp₂ f ; cq₁ = cq₁ f ; cq₂ = cq₂ f }
change-p₂ : ∀ f {l p′} → p₂ f ─[ l ]→ p′ → Quad
change-p₂ f {p′ = p′} sp = record
  { p₁ = p₁ f ; p₂ = p′ ; q₁ = q₁ f ; q₂ = q₂ f
  ; cp₁ = cp₁ f ; cp₂ = C.OffersOnly.after (cp₂ f) sp ; cq₁ = cq₁ f ; cq₂ = cq₂ f }
change-q₁ : ∀ f {l q′} → q₁ f ─[ l ]→ q′ → Quad
change-q₁ f {q′ = q′} sq = record
  { p₁ = p₁ f ; p₂ = p₂ f ; q₁ = q′ ; q₂ = q₂ f
  ; cp₁ = cp₁ f ; cp₂ = cp₂ f ; cq₁ = C.OffersOnly.after (cq₁ f) sq ; cq₂ = cq₂ f }
change-q₂ : ∀ f {l q′} → q₂ f ─[ l ]→ q′ → Quad
change-q₂ f {q′ = q′} sq = record
  { p₁ = p₁ f ; p₂ = p₂ f ; q₁ = q₁ f ; q₂ = q′
  ; cp₁ = cp₁ f ; cp₂ = cp₂ f ; cq₁ = cq₁ f ; cq₂ = C.OffersOnly.after (cq₂ f) sq }

data Atomic (f : Quad) : Label → Quad → Set where
  τ-p₁ : ∀ {p′} (sp : p₁ f ─[ τ ]→ p′) → Atomic f τ (change-p₁ f sp)
  τ-p₂ : ∀ {p′} (sp : p₂ f ─[ τ ]→ p′) → Atomic f τ (change-p₂ f sp)
  τ-q₁ : ∀ {q′} (sq : q₁ f ─[ τ ]→ q′) → Atomic f τ (change-q₁ f sq)
  τ-q₂ : ∀ {q′} (sq : q₂ f ─[ τ ]→ q′) → Atomic f τ (change-q₂ f sq)
  pair₁ : ∀ {e p′ q′} (sp : p₁ f ─[ visible (event e) ]→ p′) (sq : q₁ f ─[ visible (event e) ]→ q′)
    → Atomic f (visible (event e)) (change-q₁ (change-p₁ f sp) sq)
  pair₂ : ∀ {e p′ q′} (sp : p₂ f ─[ visible (event e) ]→ p′) (sq : q₂ f ─[ visible (event e) ]→ q′)
    → Atomic f (visible (event e)) (change-q₂ (change-p₂ f sp) sq)

opposite : ∀ {b : Bool} → b ≡ false → b ≡ true → ⊥
opposite a b = impossible (trans (sym a) b)
  where impossible : false ≡ true → ⊥
        impossible ()

apart : C.Disjoint (λ e → proj₁ e ≡ false) (λ e → proj₁ e ≡ true)
apart e = opposite

sep-left : ∀ f → C.Sep (λ _ → false) (p₁ f) (p₂ f)
sep-left f = C.disjoint-interleaving-separation (cp₁ f) (cp₂ f) apart
sep-right : ∀ f → C.Sep (λ _ → false) (q₁ f) (q₂ f)
sep-right f = C.disjoint-interleaving-separation (cq₁ f) (cq₂ f) apart

pair-apart : ∀ f → C.Sep (λ _ → false) (A.Par (p₁ f) (q₁ f)) (A.Par (p₂ f) (q₂ f))
pair-apart f outside sp sq = compare (AP.par-visible-invert (λ ()) sp) (AP.par-visible-invert (λ ()) sq)
  where
  compare : ∀ {e t u} → AP.VisibleMove (p₁ f) (q₁ f) e t → AP.VisibleMove (p₂ f) (q₂ f) e u → ⊥
  compare (AP.together _ sp _) (AP.together _ sq _) = opposite (C.OffersOnly.now (cp₁ f) sp) (C.OffersOnly.now (cp₂ f) sq)
  compare (AP.only-left () _) _
  compare (AP.only-right () _) _
  compare _ (AP.only-left () _)
  compare _ (AP.only-right () _)

absent : ∀ {p e} (α : Bool) → C.OffersOnly (λ e → proj₁ e ≡ α) p → proj₁ e ≢ α
  → I.viewV (force p) e ≡ nothing
absent {p} {e} α cp neq = lookup (I.viewV (force p) e) refl
  where
  lookup : (m : Maybe Tree) → I.viewV (force p) e ≡ m → m ≡ nothing
  lookup nothing eq = refl
  lookup (just p′) eq = ⊥-elim (neq (C.OffersOnly.now cp (IP.view-visible eq)))

pair-absent : ∀ {p q e} (α : Bool) → C.OffersOnly (λ e → proj₁ e ≡ α) p → proj₁ e ≢ α
  → I.viewV (force (A.Par p q)) e ≡ nothing
pair-absent {p} {q} {e} α cp neq = lookup (I.viewV (force (A.Par p q)) e) refl
  where
  reject : ∀ {t} → AP.VisibleMove p q e t → ⊥
  reject (AP.together _ sp sq) = neq (C.OffersOnly.now cp sp)
  reject (AP.only-left () _)
  reject (AP.only-right () _)
  lookup : (m : Maybe Tree) → I.viewV (force (A.Par p q)) e ≡ m → m ≡ nothing
  lookup nothing eq = refl
  lookup (just p′) eq = ⊥-elim (reject (AP.par-visible-invert (λ ()) (IP.view-visible eq)))

atomic-left : ∀ {f l f′} → Atomic f l f′ → left-source f ─[ l ]→ left-source f′
atomic-left (τ-p₁ sp) = AP.par-left-silent (IP.par-left-silent sp)
atomic-left (τ-p₂ sp) = AP.par-left-silent (IP.par-right-silent sp)
atomic-left (τ-q₁ sq) = AP.par-right-silent (IP.par-left-silent sq)
atomic-left (τ-q₂ sq) = AP.par-right-silent (IP.par-right-silent sq)
atomic-left {f} (pair₁ sp sq) = AP.par-sync refl
  (IP.par-left-visible refl sp (absent true (cp₂ f) (λ eq → opposite (C.OffersOnly.now (cp₁ f) sp) eq)))
  (IP.par-left-visible refl sq (absent true (cq₂ f) (λ eq → opposite (C.OffersOnly.now (cq₁ f) sq) eq)))
atomic-left {f} (pair₂ sp sq) = AP.par-sync refl
  (IP.par-right-visible refl (absent false (cp₁ f) (λ eq → opposite eq (C.OffersOnly.now (cp₂ f) sp))) sp)
  (IP.par-right-visible refl (absent false (cq₁ f) (λ eq → opposite eq (C.OffersOnly.now (cq₂ f) sq))) sq)

atomic-right : ∀ {f l f′} → Atomic f l f′ → right-source f ─[ l ]→ right-source f′
atomic-right (τ-p₁ sp) = IP.par-left-silent (AP.par-left-silent sp)
atomic-right (τ-p₂ sp) = IP.par-right-silent (AP.par-left-silent sp)
atomic-right (τ-q₁ sq) = IP.par-left-silent (AP.par-right-silent sq)
atomic-right (τ-q₂ sq) = IP.par-right-silent (AP.par-right-silent sq)
atomic-right {f} (pair₁ sp sq) = IP.par-left-visible refl (AP.par-sync refl sp sq)
  (pair-absent true (cp₂ f) (λ eq → opposite (C.OffersOnly.now (cp₁ f) sp) eq))
atomic-right {f} (pair₂ sp sq) = IP.par-right-visible refl
  (pair-absent false (cp₁ f) (λ eq → opposite eq (C.OffersOnly.now (cp₂ f) sp))) (AP.par-sync refl sp sq)

Ready : Quad → Set
Ready f = force (p₁ f) ≡ ret tt × force (p₂ f) ≡ ret tt × force (q₁ f) ≡ ret tt × force (q₂ f) ≡ ret tt

par-ready : ∀ {p q} → force p ≡ ret tt → force q ≡ ret tt → force (A.Par p q) ≡ ret tt
par-ready {p} {q} ep eq = trans (cong (λ n → A.par-force n (force q) p q) ep) (cong (λ n → A.par-force (ret tt) n p q) eq)
interleave-ready : ∀ {p q} → force p ≡ ret tt → force q ≡ ret tt → force (I.Par p q) ≡ ret tt
interleave-ready {p} {q} ep eq = trans (cong (λ n → I.par-force n (force q) p q) ep) (cong (λ n → I.par-force (ret tt) n p q) eq)

return-left : ∀ {f} → Ready f → left-source f ─[ visible (√ tt) ]→ stop
return-left (ep₁ , ep₂ , eq₁ , eq₂) = AP.par-return (interleave-ready ep₁ ep₂) (interleave-ready eq₁ eq₂)
return-right : ∀ {f} → Ready f → right-source f ─[ visible (√ tt) ]→ stop
return-right (ep₁ , ep₂ , eq₁ , eq₂) = IP.par-return (par-ready ep₁ eq₁) (par-ready ep₂ eq₂)

data Steps (encode : Quad → Tree) (f : Quad) : Label → Tree → Set where
  advances : ∀ {l f′} → Atomic f l f′ → Steps encode f l (encode f′)
  returns : Ready f → Steps encode f (visible (√ tt)) stop

left-silent-invert : ∀ f {t} → left-source f ─[ τ ]→ t → Steps left-source f τ t
left-silent-invert f step = outer (AP.par-silent-invert step)
  where
  left : ∀ {t} → IP.SilentMove (p₁ f) (p₂ f) t → Steps left-source f τ (A.Par t (I.Par (q₁ f) (q₂ f)))
  left (IP.left-silent sp) = advances (τ-p₁ sp)
  left (IP.right-silent sp) = advances (τ-p₂ sp)
  right : ∀ {t} → IP.SilentMove (q₁ f) (q₂ f) t → Steps left-source f τ (A.Par (I.Par (p₁ f) (p₂ f)) t)
  right (IP.left-silent sq) = advances (τ-q₁ sq)
  right (IP.right-silent sq) = advances (τ-q₂ sq)
  outer : ∀ {t} → AP.SilentMove (I.Par (p₁ f) (p₂ f)) (I.Par (q₁ f) (q₂ f)) t → Steps left-source f τ t
  outer (AP.left-silent sp) = left (IP.par-silent-invert sp)
  outer (AP.right-silent sq) = right (IP.par-silent-invert sq)

right-silent-invert : ∀ f {t} → right-source f ─[ τ ]→ t → Steps right-source f τ t
right-silent-invert f step = outer (IP.par-silent-invert step)
  where
  left : ∀ {t} → AP.SilentMove (p₁ f) (q₁ f) t → Steps right-source f τ (I.Par t (A.Par (p₂ f) (q₂ f)))
  left (AP.left-silent sp) = advances (τ-p₁ sp)
  left (AP.right-silent sq) = advances (τ-q₁ sq)
  right : ∀ {t} → AP.SilentMove (p₂ f) (q₂ f) t → Steps right-source f τ (I.Par (A.Par (p₁ f) (q₁ f)) t)
  right (AP.left-silent sp) = advances (τ-p₂ sp)
  right (AP.right-silent sq) = advances (τ-q₂ sq)
  outer : ∀ {t} → IP.SilentMove (A.Par (p₁ f) (q₁ f)) (A.Par (p₂ f) (q₂ f)) t → Steps right-source f τ t
  outer (IP.left-silent sp) = left (AP.par-silent-invert sp)
  outer (IP.right-silent sq) = right (AP.par-silent-invert sq)

left-event-invert : ∀ f e {t} → left-source f ─[ visible (event e) ]→ t → Steps left-source f (visible (event e)) t
left-event-invert f e step = outer (AP.par-visible-invert (λ ()) step)
  where
  compare : ∀ {t u} → IP.VisibleMove (p₁ f) (p₂ f) e t → IP.VisibleMove (q₁ f) (q₂ f) e u
    → Steps left-source f (visible (event e)) (A.Par t u)
  compare (IP.together () _ _) _
  compare _ (IP.together () _ _)
  compare (IP.only-left _ sp) (IP.only-left _ sq) = advances (pair₁ sp sq)
  compare (IP.only-right _ sp) (IP.only-right _ sq) = advances (pair₂ sp sq)
  compare (IP.only-left _ sp) (IP.only-right _ sq) = ⊥-elim (opposite (C.OffersOnly.now (cp₁ f) sp) (C.OffersOnly.now (cq₂ f) sq))
  compare (IP.only-right _ sp) (IP.only-left _ sq) = ⊥-elim (opposite (C.OffersOnly.now (cq₁ f) sq) (C.OffersOnly.now (cp₂ f) sp))
  outer : ∀ {t} → AP.VisibleMove (I.Par (p₁ f) (p₂ f)) (I.Par (q₁ f) (q₂ f)) e t
    → Steps left-source f (visible (event e)) t
  outer (AP.together _ sp sq) = compare (IP.par-visible-invert (sep-left f) sp) (IP.par-visible-invert (sep-right f) sq)
  outer (AP.only-left () _)
  outer (AP.only-right () _)

right-event-invert : ∀ f e {t} → right-source f ─[ visible (event e) ]→ t → Steps right-source f (visible (event e)) t
right-event-invert f e step = outer (IP.par-visible-invert (pair-apart f) step)
  where
  left : ∀ {t} → AP.VisibleMove (p₁ f) (q₁ f) e t → Steps right-source f (visible (event e)) (I.Par t (A.Par (p₂ f) (q₂ f)))
  left (AP.together _ sp sq) = advances (pair₁ sp sq)
  left (AP.only-left () _)
  left (AP.only-right () _)
  right : ∀ {t} → AP.VisibleMove (p₂ f) (q₂ f) e t → Steps right-source f (visible (event e)) (I.Par (A.Par (p₁ f) (q₁ f)) t)
  right (AP.together _ sp sq) = advances (pair₂ sp sq)
  right (AP.only-left () _)
  right (AP.only-right () _)
  outer : ∀ {t} → IP.VisibleMove (A.Par (p₁ f) (q₁ f)) (A.Par (p₂ f) (q₂ f)) e t → Steps right-source f (visible (event e)) t
  outer (IP.together () _ _)
  outer (IP.only-left _ sp) = left (AP.par-visible-invert (λ ()) sp)
  outer (IP.only-right _ sq) = right (AP.par-visible-invert (λ ()) sq)

left-return-invert : ∀ f {t} → left-source f ─[ visible (√ tt) ]→ t → Steps left-source f (visible (√ tt)) t
left-return-invert f step = finish (AP.par-return-invert step)
  where
  finish : ∀ {t} → force (I.Par (p₁ f) (p₂ f)) ≡ ret tt × force (I.Par (q₁ f) (q₂ f)) ≡ ret tt × t ≡ stop
    → Steps left-source f (visible (√ tt)) t
  finish (ep , eq , refl) = returns (proj₁ rp , proj₂ rp , proj₁ rq , proj₂ rq)
    where rp = IP.par-node-return-invert _ _ _ _ ep
          rq = IP.par-node-return-invert _ _ _ _ eq

right-return-invert : ∀ f {t} → right-source f ─[ visible (√ tt) ]→ t → Steps right-source f (visible (√ tt)) t
right-return-invert f step = finish (IP.par-return-invert step)
  where
  finish : ∀ {t} → force (A.Par (p₁ f) (q₁ f)) ≡ ret tt × force (A.Par (p₂ f) (q₂ f)) ≡ ret tt × t ≡ stop
    → Steps right-source f (visible (√ tt)) t
  finish (ea , eb , refl) = returns (proj₁ ra , proj₁ rb , proj₂ ra , proj₂ rb)
    where ra = AP.par-node-return-invert _ _ _ _ ea
          rb = AP.par-node-return-invert _ _ _ _ eb

record Strong (p q : Tree) : Set where
  coinductive
  field
    forward : ∀ {l p′} → p ─[ l ]→ p′ → Σ Tree (λ q′ → q ─[ l ]→ q′ × Strong p′ q′)
    backward : ∀ {l q′} → q ─[ l ]→ q′ → Σ Tree (λ p′ → p ─[ l ]→ p′ × Strong p′ q′)

stop-strong : Strong stop stop
Strong.forward stop-strong step = ⊥-elim (stop-no-step step)
Strong.backward stop-strong step = ⊥-elim (stop-no-step step)

interchange : ∀ f → Strong (left-source f) (right-source f)
Strong.forward (interchange f) {l = τ} step = continue (left-silent-invert f step)
  where
  continue : ∀ {l t} → Steps left-source f l t → Σ Tree (λ r → right-source f ─[ l ]→ r × Strong t r)
  continue (advances {f′ = f′} move) = right-source f′ , atomic-right move , interchange f′
  continue (returns ready) = stop , return-right {f = f} ready , stop-strong
Strong.forward (interchange f) {l = visible (event e)} step = continue (left-event-invert f e step)
  where
  continue : ∀ {t} → Steps left-source f (visible (event e)) t → Σ Tree
    (λ r → right-source f ─[ visible (event e) ]→ r × Strong t r)
  continue (advances {f′ = f′} move) = right-source f′ , atomic-right move , interchange f′
Strong.forward (interchange f) {l = visible (√ tt)} step = continue (left-return-invert f step)
  where
  continue : ∀ {t} → Steps left-source f (visible (√ tt)) t → Σ Tree
    (λ r → right-source f ─[ visible (√ tt) ]→ r × Strong t r)
  continue (returns ready) = stop , return-right {f = f} ready , stop-strong
Strong.backward (interchange f) {l = τ} step = continue (right-silent-invert f step)
  where
  continue : ∀ {l t} → Steps right-source f l t → Σ Tree (λ r → left-source f ─[ l ]→ r × Strong r t)
  continue (advances {f′ = f′} move) = left-source f′ , atomic-left move , interchange f′
  continue (returns ready) = stop , return-left {f = f} ready , stop-strong
Strong.backward (interchange f) {l = visible (event e)} step = continue (right-event-invert f e step)
  where
  continue : ∀ {t} → Steps right-source f (visible (event e)) t → Σ Tree
    (λ r → left-source f ─[ visible (event e) ]→ r × Strong r t)
  continue (advances {f′ = f′} move) = left-source f′ , atomic-left move , interchange f′
Strong.backward (interchange f) {l = visible (√ tt)} step = continue (right-return-invert f step)
  where
  continue : ∀ {t} → Steps right-source f (visible (√ tt)) t → Σ Tree
    (λ r → left-source f ─[ visible (√ tt) ]→ r × Strong r t)
  continue (returns ready) = stop , return-left {f = f} ready , stop-strong

hide-strong : ∀ {p q} → Strong p q → Strong (A.Hide (λ _ → true) p) (A.Hide (λ _ → true) q)
Strong.forward (hide-strong {p} {q} proof) {l = τ} step = invert (AP.hide-silent-invert (λ _ → true) step)
  where
  old : ∀ {p′} → Σ Tree (λ q′ → q ─[ τ ]→ q′ × Strong p′ q′)
    → Σ Tree (λ t → A.Hide (λ _ → true) q ─[ τ ]→ t × Strong (A.Hide (λ _ → true) p′) t)
  old (q′ , sq , next) = A.Hide (λ _ → true) q′ , AP.hide-silent-step (λ _ → true) sq , hide-strong next
  hidden : ∀ {e p′} → Σ Tree (λ q′ → q ─[ visible (event e) ]→ q′ × Strong p′ q′)
    → Σ Tree (λ t → A.Hide (λ _ → true) q ─[ τ ]→ t × Strong (A.Hide (λ _ → true) p′) t)
  hidden (q′ , sq , next) = A.Hide (λ _ → true) q′ , AP.hide-hidden (λ _ → true) refl sq , hide-strong next
  invert : ∀ {t} → AP.HideSilent (λ _ → true) p t
    → Σ Tree (λ u → A.Hide (λ _ → true) q ─[ τ ]→ u × Strong t u)
  invert (AP.original sp) = old (Strong.forward proof sp)
  invert (AP.concealed-event _ sp) = hidden (Strong.forward proof sp)
Strong.forward (hide-strong proof) {l = visible (event e)} step = ⊥-elim (AP.hide-all-no-event step)
Strong.forward (hide-strong {p} {q} proof) {l = visible (√ tt)} step = finish (AP.hide-return-invert (λ _ → true) step)
  where
  matched : Σ Tree (λ q′ → q ─[ visible (√ tt) ]→ q′ × Strong stop q′)
    → Σ Tree (λ t → A.Hide (λ _ → true) q ─[ visible (√ tt) ]→ t × Strong stop t)
  matched (.stop , sRet ready , _) = stop , AP.hide-return (λ _ → true) ready , stop-strong
  finish : ∀ {t} → force p ≡ ret tt × t ≡ stop
    → Σ Tree (λ u → A.Hide (λ _ → true) q ─[ visible (√ tt) ]→ u × Strong t u)
  finish (ready , refl) = matched (Strong.forward proof (sRet ready))
Strong.backward (hide-strong {p} {q} proof) {l = τ} step = invert (AP.hide-silent-invert (λ _ → true) step)
  where
  old : ∀ {q′} → Σ Tree (λ p′ → p ─[ τ ]→ p′ × Strong p′ q′)
    → Σ Tree (λ t → A.Hide (λ _ → true) p ─[ τ ]→ t × Strong t (A.Hide (λ _ → true) q′))
  old (p′ , sp , next) = A.Hide (λ _ → true) p′ , AP.hide-silent-step (λ _ → true) sp , hide-strong next
  hidden : ∀ {e q′} → Σ Tree (λ p′ → p ─[ visible (event e) ]→ p′ × Strong p′ q′)
    → Σ Tree (λ t → A.Hide (λ _ → true) p ─[ τ ]→ t × Strong t (A.Hide (λ _ → true) q′))
  hidden (p′ , sp , next) = A.Hide (λ _ → true) p′ , AP.hide-hidden (λ _ → true) refl sp , hide-strong next
  invert : ∀ {t} → AP.HideSilent (λ _ → true) q t
    → Σ Tree (λ u → A.Hide (λ _ → true) p ─[ τ ]→ u × Strong u t)
  invert (AP.original sq) = old (Strong.backward proof sq)
  invert (AP.concealed-event _ sq) = hidden (Strong.backward proof sq)
Strong.backward (hide-strong proof) {l = visible (event e)} step = ⊥-elim (AP.hide-all-no-event step)
Strong.backward (hide-strong {p} {q} proof) {l = visible (√ tt)} step = finish (AP.hide-return-invert (λ _ → true) step)
  where
  matched : Σ Tree (λ p′ → p ─[ visible (√ tt) ]→ p′ × Strong p′ stop)
    → Σ Tree (λ t → A.Hide (λ _ → true) p ─[ visible (√ tt) ]→ t × Strong t stop)
  matched (.stop , sRet ready , _) = stop , AP.hide-return (λ _ → true) ready , stop-strong
  finish : ∀ {t} → force q ≡ ret tt × t ≡ stop
    → Σ Tree (λ u → A.Hide (λ _ → true) p ─[ visible (√ tt) ]→ u × Strong u t)
  finish (ready , refl) = matched (Strong.backward proof (sRet ready))

hidden-interchange : ∀ f → Strong (A.Hide (λ _ → true) (left-source f)) (A.Hide (λ _ → true) (right-source f))
hidden-interchange f = hide-strong (interchange f)

strong-divergence-forward : ∀ {p q} → Strong p q → Diverges p → Diverges q
Diverges.next (strong-divergence-forward proof d) = proj₁ (Strong.forward proof (Diverges.step d))
Diverges.step (strong-divergence-forward proof d) = proj₁ (proj₂ (Strong.forward proof (Diverges.step d)))
Diverges.rest (strong-divergence-forward proof d) = strong-divergence-forward
  (proj₂ (proj₂ (Strong.forward proof (Diverges.step d)))) (Diverges.rest d)

strong-divergence-backward : ∀ {p q} → Strong p q → Diverges q → Diverges p
Diverges.next (strong-divergence-backward proof d) = proj₁ (Strong.backward proof (Diverges.step d))
Diverges.step (strong-divergence-backward proof d) = proj₁ (proj₂ (Strong.backward proof (Diverges.step d)))
Diverges.rest (strong-divergence-backward proof d) = strong-divergence-backward
  (proj₂ (proj₂ (Strong.backward proof (Diverges.step d)))) (Diverges.rest d)
