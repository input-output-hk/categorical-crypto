{-# OPTIONS --safe --without-K --guardedness #-}

-- Operational slice of CSP/Operators.agda:486–634 at
-- agda-cardano-common 9a40d1de330f376c3a102e7c9f1282f4fa830a7e.
-- Branch tags preserve source choices, including the outside-A commitment.
open import Data.Bool.Base
module CategoricalCrypto.CSP.NativeParallel (E B : Set) (sync : E → Bool) where

open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.Process as Core
import CategoricalCrypto.CSP.Confinement as Confinement

module O = Operators E B sync
module N = Core E O.Index ⊤
module C = Confinement E O.Index ⊤
open O
open N
open C using (Sep; OffersOnly; Disjoint; sep-from-OffersOnly)
open N.Tree

private variable
  p q p′ q′ t : Tree
  e : E
  i : Index
  l : Label

visible-view : p ─[ visible (event e) ]→ p′ → viewV (force p) e ≡ just p′
visible-view {e = e} (sVis eq offered) = trans (cong (λ n → viewV n e) eq) offered

view-visible-node : (n : Node) → force p ≡ n → viewV n e ≡ just p′ → p ─[ visible (event e) ]→ p′
view-visible-node (ret tt) eq ()
view-visible-node (sil t) eq ()
view-visible-node (react v b) eq offered = sVis eq offered

view-visible : viewV (force p) e ≡ just p′ → p ─[ visible (event e) ]→ p′
view-visible {p = p} = view-visible-node (force p) refl

view-silent-node : (n : Node) → force p ≡ n → viewT n i ≡ just p′ → p ─[ τ ]→ p′
view-silent-node (ret tt) eq ()
view-silent-node {i = silence} (sil t) eq refl = sSil eq
view-silent-node {i = raw _} (sil t) eq ()
view-silent-node {i = left _} (sil t) eq ()
view-silent-node {i = right _} (sil t) eq ()
view-silent-node {i = commitment _} (sil t) eq ()
view-silent-node {i = concealed _} (sil t) eq ()
view-silent-node (react v b) eq offered = sTau eq offered

view-silent : viewT (force p) i ≡ just p′ → p ─[ τ ]→ p′
view-silent {p = p} = view-silent-node (force p) refl

silent-view : p ─[ τ ]→ p′ → Σ Index (λ i → viewT (force p) i ≡ just p′)
silent-view (sSil eq) = silence , cong (λ n → viewT n silence) eq
silent-view (sTau {i = i} eq offered) = i , trans (cong (λ n → viewT n i) eq) offered

par-node-visible : ∀ np nq p q e → viewV (par-force np nq p q) e ≡ par-visible np nq p q e
par-node-visible (ret tt) (ret tt) p q e with sync e
... | true = refl
... | false = refl
par-node-visible (ret tt) (sil t) p q e with sync e
... | true = refl
... | false = refl
par-node-visible (sil t) (ret tt) p q e with sync e
... | true = refl
... | false = refl
par-node-visible (ret tt) (react v b) p q e with sync e | v e
... | true | just t = refl
... | true | nothing = refl
... | false | just t = refl
... | false | nothing = refl
par-node-visible (react v b) (ret tt) p q e with sync e | v e
... | true | just t = refl
... | true | nothing = refl
... | false | just t = refl
... | false | nothing = refl
par-node-visible (sil _) (sil _) p q e = refl
par-node-visible (sil _) (react _ _) p q e = refl
par-node-visible (react _ _) (sil _) p q e = refl
par-node-visible (react _ _) (react _ _) p q e = refl

par-view-visible : ∀ p q e → viewV (force (Par p q)) e ≡ par-visible (force p) (force q) p q e
par-view-visible p q e = par-node-visible (force p) (force q) p q e

par-sync-result : ∀ np nq p q p′ q′ e → sync e ≡ true
  → viewV np e ≡ just p′ → viewV nq e ≡ just q′
  → par-visible np nq p q e ≡ just (Par p′ q′)
par-sync-result np nq p q p′ q′ e inside vp vq =
  trans (cong (λ z → par-visible-result z (viewV np e) (viewV nq e) p q) inside)
    (trans (cong (λ z → par-visible-result true z (viewV nq e) p q) vp)
      (cong (λ z → par-visible-result true (just p′) z p q) vq))

par-left-result : ∀ np nq p q p′ e → sync e ≡ false
  → viewV np e ≡ just p′ → viewV nq e ≡ nothing
  → par-visible np nq p q e ≡ just (Par p′ q)
par-left-result np nq p q p′ e outside vp vq =
  trans (cong (λ z → par-visible-result z (viewV np e) (viewV nq e) p q) outside)
    (trans (cong (λ z → par-visible-result false z (viewV nq e) p q) vp)
      (cong (λ z → par-visible-result false (just p′) z p q) vq))

par-right-result : ∀ np nq p q q′ e → sync e ≡ false
  → viewV np e ≡ nothing → viewV nq e ≡ just q′
  → par-visible np nq p q e ≡ just (Par p q′)
par-right-result np nq p q q′ e outside vp vq =
  trans (cong (λ z → par-visible-result z (viewV np e) (viewV nq e) p q) outside)
    (trans (cong (λ z → par-visible-result false z (viewV nq e) p q) vp)
      (cong (λ z → par-visible-result false nothing z p q) vq))

par-sync : sync e ≡ true → p ─[ visible (event e) ]→ p′ → q ─[ visible (event e) ]→ q′
         → Par p q ─[ visible (event e) ]→ Par p′ q′
par-sync {e = e} {p = p} {p′ = p′} {q = q} {q′ = q′} inside sp sq =
  view-visible (trans (par-view-visible p q e)
    (par-sync-result (force p) (force q) p q p′ q′ e inside (visible-view sp) (visible-view sq)))

par-left-visible : sync e ≡ false → p ─[ visible (event e) ]→ p′
  → viewV (force q) e ≡ nothing → Par p q ─[ visible (event e) ]→ Par p′ q
par-left-visible {e = e} {p = p} {p′ = p′} {q = q} outside sp absent =
  view-visible (trans (par-view-visible p q e)
    (par-left-result (force p) (force q) p q p′ e outside (visible-view sp) absent))

par-right-visible : sync e ≡ false → viewV (force p) e ≡ nothing
  → q ─[ visible (event e) ]→ q′ → Par p q ─[ visible (event e) ]→ Par p q′
par-right-visible {e = e} {p = p} {q = q} {q′ = q′} outside absent sq =
  view-visible (trans (par-view-visible p q e)
    (par-right-result (force p) (force q) p q q′ e outside absent (visible-view sq)))

data VisibleMove (p q : Tree) (e : E) : Tree → Set where
  together : ∀ {p′ q′} → sync e ≡ true → p ─[ visible (event e) ]→ p′
    → q ─[ visible (event e) ]→ q′ → VisibleMove p q e (Par p′ q′)
  only-left : ∀ {p′} → sync e ≡ false → p ─[ visible (event e) ]→ p′
    → VisibleMove p q e (Par p′ q)
  only-right : ∀ {q′} → sync e ≡ false → q ─[ visible (event e) ]→ q′
    → VisibleMove p q e (Par p q′)

par-result-invert : (s : Bool) (vp vq : Maybe Tree) → sync e ≡ s
  → viewV (force p) e ≡ vp → viewV (force q) e ≡ vq → Sep sync p q
  → par-visible-result s vp vq p q ≡ just t → VisibleMove p q e t
par-result-invert true (just p′) (just q′) inside vp vq sep refl =
  together inside (view-visible vp) (view-visible vq)
par-result-invert true (just _) nothing inside vp vq sep ()
par-result-invert true nothing _ inside vp vq sep ()
par-result-invert false (just p′) (just q′) outside vp vq sep result =
  ⊥-elim (sep outside (view-visible vp) (view-visible vq))
par-result-invert false (just p′) nothing outside vp vq sep refl = only-left outside (view-visible vp)
par-result-invert false nothing (just q′) outside vp vq sep refl = only-right outside (view-visible vq)
par-result-invert false nothing nothing outside vp vq sep ()

par-visible-invert : Sep sync p q → Par p q ─[ visible (event e) ]→ t → VisibleMove p q e t
par-visible-invert {p = p} {q = q} {e = e} sep step =
  par-result-invert (sync e) (viewV (force p) e) (viewV (force q) e) refl refl refl sep
    (trans (sym (par-view-visible p q e)) (visible-view step))

par-return : force p ≡ ret tt → force q ≡ ret tt → Par p q ─[ visible (√ tt) ]→ stop
par-return {p = p} {q = q} ep eq = sRet
  (trans (cong (λ n → par-force n (force q) p q) ep)
    (cong (λ n → par-force (ret tt) n p q) eq))

par-node-return-invert : ∀ np nq p q → par-force np nq p q ≡ ret tt → np ≡ ret tt × nq ≡ ret tt
par-node-return-invert (ret tt) (ret tt) p q eq = refl , refl
par-node-return-invert (ret tt) (sil _) p q ()
par-node-return-invert (ret tt) (react _ _) p q ()
par-node-return-invert (sil _) (ret tt) p q ()
par-node-return-invert (sil _) (sil _) p q ()
par-node-return-invert (sil _) (react _ _) p q ()
par-node-return-invert (react _ _) (ret tt) p q ()
par-node-return-invert (react _ _) (sil _) p q ()
par-node-return-invert (react _ _) (react _ _) p q ()

par-return-invert : Par p q ─[ visible (√ tt) ]→ t → force p ≡ ret tt × force q ≡ ret tt × t ≡ stop
par-return-invert {p = p} {q = q} (sRet eq) =
  proj₁ ready , proj₂ ready , refl
  where ready = par-node-return-invert (force p) (force q) p q eq

par-node-left-view : ∀ np nq p q i p′ → viewT np i ≡ just p′
  → Σ Index (λ j → viewT (par-force np nq p q) j ≡ just (Par p′ q))
par-node-left-view (ret tt) nq p q i p′ ()
par-node-left-view (sil r) (ret tt) p q silence .r refl = silence , refl
par-node-left-view (sil r) (ret tt) p q (raw _) p′ ()
par-node-left-view (sil r) (ret tt) p q (left _) p′ ()
par-node-left-view (sil r) (ret tt) p q (right _) p′ ()
par-node-left-view (sil r) (ret tt) p q (commitment _) p′ ()
par-node-left-view (sil r) (ret tt) p q (concealed _) p′ ()
par-node-left-view (react v b) (ret tt) p q i p′ offered =
  i , cong (par-map-left q) offered
par-node-left-view (sil r) (sil s) p q i p′ offered =
  left i , cong (par-map-left q) offered
par-node-left-view (sil r) (react v b) p q i p′ offered =
  left i , cong (par-map-left q) offered
par-node-left-view (react v b) (sil s) p q i p′ offered =
  left i , cong (par-map-left q) offered
par-node-left-view (react v b) (react w c) p q i p′ offered =
  left i , cong (par-map-left q) offered

par-node-right-view : ∀ np nq p q i q′ → viewT nq i ≡ just q′
  → Σ Index (λ j → viewT (par-force np nq p q) j ≡ just (Par p q′))
par-node-right-view np (ret tt) p q i q′ ()
par-node-right-view (ret tt) (sil s) p q silence .s refl = silence , refl
par-node-right-view (ret tt) (sil s) p q (raw _) q′ ()
par-node-right-view (ret tt) (sil s) p q (left _) q′ ()
par-node-right-view (ret tt) (sil s) p q (right _) q′ ()
par-node-right-view (ret tt) (sil s) p q (commitment _) q′ ()
par-node-right-view (ret tt) (sil s) p q (concealed _) q′ ()
par-node-right-view (ret tt) (react v b) p q i q′ offered =
  i , cong (par-map-right p) offered
par-node-right-view (sil r) (sil s) p q i q′ offered =
  right i , cong (par-map-right p) offered
par-node-right-view (sil r) (react v b) p q i q′ offered =
  right i , cong (par-map-right p) offered
par-node-right-view (react v b) (sil s) p q i q′ offered =
  right i , cong (par-map-right p) offered
par-node-right-view (react v b) (react w c) p q i q′ offered =
  right i , cong (par-map-right p) offered

view-silent-exists : Σ Index (λ i → viewT (force p) i ≡ just p′) → p ─[ τ ]→ p′
view-silent-exists (i , offered) = view-silent offered

par-left-silent : p ─[ τ ]→ p′ → Par p q ─[ τ ]→ Par p′ q
par-left-silent {p = p} {p′ = p′} {q = q} step = lift (silent-view step)
  where
  lift : Σ Index (λ i → viewT (force p) i ≡ just p′) → Par p q ─[ τ ]→ Par p′ q
  lift (i , offered) = view-silent-exists (par-node-left-view (force p) (force q) p q i p′ offered)

par-right-silent : q ─[ τ ]→ q′ → Par p q ─[ τ ]→ Par p q′
par-right-silent {q = q} {q′ = q′} {p = p} step = lift (silent-view step)
  where
  lift : Σ Index (λ i → viewT (force q) i ≡ just q′) → Par p q ─[ τ ]→ Par p q′
  lift (i , offered) = view-silent-exists (par-node-right-view (force p) (force q) p q i q′ offered)

data NodeSilent (np nq : Node) (p q : Tree) : Tree → Set where
  node-left : ∀ {i p′} → viewT np i ≡ just p′ → NodeSilent np nq p q (Par p′ q)
  node-right : ∀ {i q′} → viewT nq i ≡ just q′ → NodeSilent np nq p q (Par p q′)

mapped-left-invert : ∀ np nq p q i (m : Maybe Tree) → viewT np i ≡ m
  → par-map-left q m ≡ just t → NodeSilent np nq p q t
mapped-left-invert np nq p q i nothing offered ()
mapped-left-invert np nq p q i (just r) offered refl = node-left offered

mapped-right-invert : ∀ np nq p q i (m : Maybe Tree) → viewT nq i ≡ m
  → par-map-right p m ≡ just t → NodeSilent np nq p q t
mapped-right-invert np nq p q i nothing offered ()
mapped-right-invert np nq p q i (just r) offered refl = node-right offered

par-general-silent-invert : ∀ np nq p q i → par-silent np nq p q i ≡ just t → NodeSilent np nq p q t
par-general-silent-invert np nq p q (left i) =
  mapped-left-invert np nq p q i (viewT np i) refl
par-general-silent-invert np nq p q (right i) =
  mapped-right-invert np nq p q i (viewT nq i) refl
par-general-silent-invert np nq p q (raw _) ()
par-general-silent-invert np nq p q silence ()
par-general-silent-invert np nq p q (commitment _) ()
par-general-silent-invert np nq p q (concealed _) ()

par-node-silent-invert : ∀ np nq p q i → viewT (par-force np nq p q) i ≡ just t → NodeSilent np nq p q t
par-node-silent-invert (ret tt) (ret tt) p q i ()
par-node-silent-invert (ret tt) (sil s) p q silence refl = node-right {i = silence} refl
par-node-silent-invert (ret tt) (sil s) p q (raw _) ()
par-node-silent-invert (ret tt) (sil s) p q (left _) ()
par-node-silent-invert (ret tt) (sil s) p q (right _) ()
par-node-silent-invert (ret tt) (sil s) p q (commitment _) ()
par-node-silent-invert (ret tt) (sil s) p q (concealed _) ()
par-node-silent-invert (sil r) (ret tt) p q silence refl = node-left {i = silence} refl
par-node-silent-invert (sil r) (ret tt) p q (raw _) ()
par-node-silent-invert (sil r) (ret tt) p q (left _) ()
par-node-silent-invert (sil r) (ret tt) p q (right _) ()
par-node-silent-invert (sil r) (ret tt) p q (commitment _) ()
par-node-silent-invert (sil r) (ret tt) p q (concealed _) ()
par-node-silent-invert (ret tt) (react v b) p q i =
  mapped-right-invert (ret tt) (react v b) p q i (b i) refl
par-node-silent-invert (react v b) (ret tt) p q i =
  mapped-left-invert (react v b) (ret tt) p q i (b i) refl
par-node-silent-invert (sil r) (sil s) p q i = par-general-silent-invert (sil r) (sil s) p q i
par-node-silent-invert (sil r) (react v b) p q i = par-general-silent-invert (sil r) (react v b) p q i
par-node-silent-invert (react v b) (sil s) p q i = par-general-silent-invert (react v b) (sil s) p q i
par-node-silent-invert (react v b) (react w c) p q i = par-general-silent-invert (react v b) (react w c) p q i

data SilentMove (p q : Tree) : Tree → Set where
  left-silent : ∀ {p′} → p ─[ τ ]→ p′ → SilentMove p q (Par p′ q)
  right-silent : ∀ {q′} → q ─[ τ ]→ q′ → SilentMove p q (Par p q′)

node-silent : NodeSilent (force p) (force q) p q t → SilentMove p q t
node-silent (node-left offered) = left-silent (view-silent offered)
node-silent (node-right offered) = right-silent (view-silent offered)

par-silent-invert : Par p q ─[ τ ]→ t → SilentMove p q t
par-silent-invert {p = p} {q = q} step = invert (silent-view step)
  where
  invert : Σ Index (λ i → viewT (force (Par p q)) i ≡ just _) → SilentMove p q _
  invert (i , offered) = node-silent (par-node-silent-invert (force p) (force q) p q i offered)

hide-node-silent-view : ∀ hide n i p′ → viewT n i ≡ just p′
  → Σ Index (λ j → viewT (hide-force hide n) j ≡ just (Hide hide p′))
hide-node-silent-view hide (ret tt) i p′ ()
hide-node-silent-view hide (sil r) silence .r refl = silence , refl
hide-node-silent-view hide (sil r) (raw _) p′ ()
hide-node-silent-view hide (sil r) (left _) p′ ()
hide-node-silent-view hide (sil r) (right _) p′ ()
hide-node-silent-view hide (sil r) (commitment _) p′ ()
hide-node-silent-view hide (sil r) (concealed _) p′ ()
hide-node-silent-view hide (react v b) i p′ offered = left i , cong (hide-map hide) offered

hide-silent-step : ∀ hide → p ─[ τ ]→ p′ → Hide hide p ─[ τ ]→ Hide hide p′
hide-silent-step {p = p} {p′ = p′} hide step = lift (silent-view step)
  where
  lift : Σ Index (λ i → viewT (force p) i ≡ just p′) → Hide hide p ─[ τ ]→ Hide hide p′
  lift (i , offered) = view-silent-exists (hide-node-silent-view hide (force p) i p′ offered)

hide-hidden : ∀ hide → hide e ≡ true → p ─[ visible (event e) ]→ p′
  → Hide hide p ─[ τ ]→ Hide hide p′
hide-hidden {e = e} hide inside (sVis {v = v} {b = b} eq offered) = sTau {i = right (concealed e)}
  (cong (hide-force hide) eq)
  (trans (cong (λ z → hide-result hide z (v e)) inside) (cong (hide-map hide) offered))

hide-keep : ∀ hide → hide e ≡ false → p ─[ visible (event e) ]→ p′
  → Hide hide p ─[ visible (event e) ]→ Hide hide p′
hide-keep {e = e} hide outside (sVis {v = v} {b = b} eq offered) = sVis
  (cong (hide-force hide) eq)
  (trans (cong (λ z → hide-result hide (not z) (v e)) outside) (cong (hide-map hide) offered))

data HideNodeSilent (hide : E → Bool) (n : Node) : Tree → Set where
  old-silent : ∀ {i p′} → viewT n i ≡ just p′ → HideNodeSilent hide n (Hide hide p′)
  hidden-visible : ∀ {e p′} → hide e ≡ true → viewV n e ≡ just p′
    → HideNodeSilent hide n (Hide hide p′)

hide-map-invert : ∀ hide n i (m : Maybe Tree) → viewT n i ≡ m
  → hide-map hide m ≡ just t → HideNodeSilent hide n t
hide-map-invert hide n i nothing offered ()
hide-map-invert hide n i (just p′) offered refl = old-silent offered

hide-event-invert : ∀ hide n e (s : Bool) (m : Maybe Tree) → hide e ≡ s → viewV n e ≡ m
  → hide-result hide s m ≡ just t → HideNodeSilent hide n t
hide-event-invert hide n e false m inside offered ()
hide-event-invert hide n e true nothing inside offered ()
hide-event-invert hide n e true (just p′) inside offered refl = hidden-visible inside offered

hide-react-silent-invert : ∀ hide n i → hide-silent hide n i ≡ just t → HideNodeSilent hide n t
hide-react-silent-invert hide n (left i) = hide-map-invert hide n i (viewT n i) refl
hide-react-silent-invert hide n (right (concealed e)) =
  hide-event-invert hide n e (hide e) (viewV n e) refl refl
hide-react-silent-invert hide n (raw _) ()
hide-react-silent-invert hide n silence ()
hide-react-silent-invert hide n (commitment _) ()
hide-react-silent-invert hide n (concealed _) ()
hide-react-silent-invert hide n (right (raw _)) ()
hide-react-silent-invert hide n (right silence) ()
hide-react-silent-invert hide n (right (left _)) ()
hide-react-silent-invert hide n (right (right _)) ()
hide-react-silent-invert hide n (right (commitment _)) ()

hide-node-silent-invert : ∀ hide n i → viewT (hide-force hide n) i ≡ just t → HideNodeSilent hide n t
hide-node-silent-invert hide (ret tt) i ()
hide-node-silent-invert hide (sil p′) silence refl = old-silent {i = silence} refl
hide-node-silent-invert hide (sil p′) (raw _) ()
hide-node-silent-invert hide (sil p′) (left _) ()
hide-node-silent-invert hide (sil p′) (right _) ()
hide-node-silent-invert hide (sil p′) (commitment _) ()
hide-node-silent-invert hide (sil p′) (concealed _) ()
hide-node-silent-invert hide (react v b) i = hide-react-silent-invert hide (react v b) i

data HideSilent (hide : E → Bool) (p : Tree) : Tree → Set where
  original : ∀ {p′} → p ─[ τ ]→ p′ → HideSilent hide p (Hide hide p′)
  concealed-event : ∀ {e p′} → hide e ≡ true → p ─[ visible (event e) ]→ p′
    → HideSilent hide p (Hide hide p′)

hide-node-silent : ∀ hide → HideNodeSilent hide (force p) t → HideSilent hide p t
hide-node-silent hide (old-silent offered) = original (view-silent offered)
hide-node-silent hide (hidden-visible inside offered) = concealed-event inside (view-visible offered)

hide-silent-invert : ∀ hide → Hide hide p ─[ τ ]→ t → HideSilent hide p t
hide-silent-invert {p = p} {t = t} hide step = invert (silent-view step)
  where
  invert : Σ Index (λ i → viewT (force (Hide hide p)) i ≡ just t) → HideSilent hide p t
  invert (i , offered) = hide-node-silent hide (hide-node-silent-invert hide (force p) i offered)

hide-node-return-invert : ∀ hide n → hide-force hide n ≡ ret tt → n ≡ ret tt
hide-node-return-invert hide (ret tt) eq = refl
hide-node-return-invert hide (sil _) ()
hide-node-return-invert hide (react _ _) ()

hide-return : ∀ hide → force p ≡ ret tt → Hide hide p ─[ visible (√ tt) ]→ stop
hide-return hide ready = sRet (cong (hide-force hide) ready)

hide-return-invert : ∀ hide → Hide hide p ─[ visible (√ tt) ]→ t → force p ≡ ret tt × t ≡ stop
hide-return-invert {p = p} hide (sRet ready) = hide-node-return-invert hide (force p) ready , refl

hide-all-node-no-event : ∀ n e → viewV (hide-force (λ _ → true) n) e ≡ nothing
hide-all-node-no-event (ret tt) e = refl
hide-all-node-no-event (sil _) e = refl
hide-all-node-no-event (react _ _) e = refl

hide-all-no-event : Hide (λ _ → true) p ─[ visible (event e) ]→ t → ⊥
hide-all-no-event {p = p} {e = e} step =
  impossible (trans (sym (hide-all-node-no-event (force p) e)) (visible-view step))
  where
  impossible : nothing ≡ just t → ⊥
  impossible ()
