{-# OPTIONS --safe --without-K --guardedness #-}

-- Native nonempty nested Par on one shared alphabet, followed by Hide.
-- Each box has one port, mapped injectively to the common channel. Payloads,
-- internal branching and tree depth are unrestricted. Polarity admissibility
-- supplies one producer and a distinct listener; all incident boxes participate.
-- No zero-box Skip correspondence is asserted: the kernel has no empty √.
module CategoricalCrypto.CSP.NativeCorrespondence (X B : Set) where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base hiding (merge)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_; Dec; yes; no)

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Network ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → X)
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.Process as Core

module O = Operators (⊤ × X) B (λ _ → true)
module L = Core (⊤ × X) O.Index ⊤
module P = Parallel (⊤ × X) B (λ _ → true)
open O hiding (left; right)
open L
open L.Tree

unit-equality : (a b : ⊤) → Dec (a ≡ b)
unit-equality tt tt = yes refl

open Decidable⇒UIP unit-equality using (≡-irrelevant)

data Nonempty : Set where
  one : Nonempty
  _∙_ : Nonempty → Nonempty → Nonempty

shape+ : Nonempty → Shape
shape+ one = singleton
shape+ (s ∙ t) = shape+ s ⊕ shape+ t

Family : Nonempty → Set
Family s = ⟨ shape+ s ⟩ → Tree

fold : (s : Nonempty) → Family s → Tree
fold one q = q tt
fold (s ∙ t) q = Par (fold s (λ k → q (inj₁ k))) (fold t (λ k → q (inj₂ k)))

fold-cong : ∀ s {q r : Family s} → (∀ k → q k ≡ r k) → fold s q ≡ fold s r
fold-cong one eq = eq tt
fold-cong (s ∙ t) eq = cong₂ Par (fold-cong s (λ k → eq (inj₁ k))) (fold-cong t (λ k → eq (inj₂ k)))

replace : ∀ s → ⟨ shape+ s ⟩ → Tree → Family s → Family s
replace s k p q j with index-equality (shape+ s) k j
... | yes refl = p
... | no _ = q j

replace-left : ∀ s t k p q → fold (s ∙ t) (replace (s ∙ t) (inj₁ k) p q)
  ≡ Par (fold s (replace s k p (λ j → q (inj₁ j)))) (fold t (λ j → q (inj₂ j)))
replace-left s t k p q = cong₂ Par (fold-cong s left-eq) (fold-cong t (λ _ → refl))
  where
  left-eq : ∀ j → replace (s ∙ t) (inj₁ k) p q (inj₁ j) ≡ replace s k p (λ j → q (inj₁ j)) j
  left-eq j with index-equality (shape+ s) k j
  ... | yes refl = refl
  ... | no _ = refl

replace-right : ∀ s t k p q → fold (s ∙ t) (replace (s ∙ t) (inj₂ k) p q)
  ≡ Par (fold s (λ j → q (inj₁ j))) (fold t (replace t k p (λ j → q (inj₂ j))))
replace-right s t k p q = cong₂ Par (fold-cong s (λ _ → refl)) (fold-cong t right-eq)
  where
  right-eq : ∀ j → replace (s ∙ t) (inj₂ k) p q (inj₂ j) ≡ replace t k p (λ j → q (inj₂ j)) j
  right-eq j with index-equality (shape+ t) k j
  ... | yes refl = refl
  ... | no _ = refl

fold-silent : ∀ s q k {p′} → q k ─[ τ ]→ p′ → fold s q ─[ τ ]→ fold s (replace s k p′ q)
fold-silent one q tt step = step
fold-silent (s ∙ t) q (inj₁ k) step = subst (λ r → fold (s ∙ t) q ─[ τ ]→ r)
  (sym (replace-left s t k _ q)) (P.par-left-silent (fold-silent s (λ j → q (inj₁ j)) k step))
fold-silent (s ∙ t) q (inj₂ k) step = subst (λ r → fold (s ∙ t) q ─[ τ ]→ r)
  (sym (replace-right s t k _ q)) (P.par-right-silent (fold-silent t (λ j → q (inj₂ j)) k step))

record LocalMove (s : Nonempty) (q : Family s) (r : Tree) : Set where
  field box : ⟨ shape+ s ⟩; next : Tree; step : q box ─[ τ ]→ next; target : r ≡ fold s (replace s box next q)

fold-silent-invert : ∀ s q {r} → fold s q ─[ τ ]→ r → LocalMove s q r
fold-silent-invert one q step = record { box = tt ; next = _ ; step = step ; target = refl }
fold-silent-invert (s ∙ t) q step = invert (P.par-silent-invert step)
  where
  left = λ k → q (inj₁ k)
  right = λ k → q (inj₂ k)
  lift-left : ∀ {r} → LocalMove s left r → LocalMove (s ∙ t) q (Par r (fold t right))
  lift-left m = record
    { box = inj₁ (LocalMove.box m) ; next = LocalMove.next m ; step = LocalMove.step m
    ; target = trans (cong (λ r → Par r (fold t right)) (LocalMove.target m))
        (sym (replace-left s t (LocalMove.box m) (LocalMove.next m) q)) }
  lift-right : ∀ {r} → LocalMove t right r → LocalMove (s ∙ t) q (Par (fold s left) r)
  lift-right m = record
    { box = inj₂ (LocalMove.box m) ; next = LocalMove.next m ; step = LocalMove.step m
    ; target = trans (cong (Par (fold s left)) (LocalMove.target m))
        (sym (replace-right s t (LocalMove.box m) (LocalMove.next m) q)) }
  invert : ∀ {r} → P.SilentMove (fold s left) (fold t right) r → LocalMove (s ∙ t) q r
  invert (P.left-silent sp) = lift-left (fold-silent-invert s left sp)
  invert (P.right-silent sq) = lift-right (fold-silent-invert t right sq)

fold-event : ∀ s {q r : Family s} e → (∀ k → q k ─[ visible (event e) ]→ r k)
  → fold s q ─[ visible (event e) ]→ fold s r
fold-event one e offers = offers tt
fold-event (s ∙ t) e offers = P.par-sync refl
  (fold-event s e (λ k → offers (inj₁ k))) (fold-event t e (λ k → offers (inj₂ k)))

record AllMove (s : Nonempty) (q : Family s) (e : ⊤ × X) (r : Tree) : Set where
  field next : Family s; steps : ∀ k → q k ─[ visible (event e) ]→ next k; target : r ≡ fold s next

fold-event-invert : ∀ s q e {r} → fold s q ─[ visible (event e) ]→ r → AllMove s q e r
fold-event-invert one q e step = record { next = λ _ → _ ; steps = λ { tt → step } ; target = refl }
fold-event-invert (s ∙ t) q e step = invert (P.par-visible-invert (λ ()) step)
  where
  left = λ k → q (inj₁ k)
  right = λ k → q (inj₂ k)
  merge : ∀ {p′ q′} → AllMove s left e p′ → AllMove t right e q′ → AllMove (s ∙ t) q e (Par p′ q′)
  merge a b = record
    { next = [ AllMove.next a , AllMove.next b ]′
    ; steps = λ { (inj₁ k) → AllMove.steps a k ; (inj₂ k) → AllMove.steps b k }
    ; target = cong₂ Par (AllMove.target a) (AllMove.target b) }
  invert : ∀ {r} → P.VisibleMove (fold s left) (fold t right) e r → AllMove (s ∙ t) q e r
  invert (P.together _ sp sq) = merge (fold-event-invert s left e sp) (fold-event-invert t right e sq)
  invert (P.only-left () _)
  invert (P.only-right () _)

fold-return : ∀ s q → (∀ k → force (q k) ≡ ret tt) → force (fold s q) ≡ ret tt
fold-return one q ready = ready tt
fold-return (s ∙ t) q ready = trans
  (cong (λ n → par-force n (force (fold t (λ k → q (inj₂ k)))) (fold s (λ k → q (inj₁ k))) (fold t (λ k → q (inj₂ k))))
    (fold-return s _ (λ k → ready (inj₁ k))))
  (cong (λ n → par-force (ret tt) n (fold s (λ k → q (inj₁ k))) (fold t (λ k → q (inj₂ k))))
    (fold-return t _ (λ k → ready (inj₂ k))))

fold-return-invert : ∀ s q → force (fold s q) ≡ ret tt → ∀ k → force (q k) ≡ ret tt
fold-return-invert one q ready tt = ready
fold-return-invert (s ∙ t) q ready (inj₁ k) = fold-return-invert s _
  (proj₁ (P.par-node-return-invert _ _ _ _ ready)) k
fold-return-invert (s ∙ t) q ready (inj₂ k) = fold-return-invert t _
  (proj₂ (P.par-node-return-invert _ _ _ _ ready)) k

module Closed (s : Nonempty) (pol : ⟨ shape+ s ⟩ → Polarity)
  (producer listener : ⟨ shape+ s ⟩) (producer-output : pol producer ≡ output)
  (only-producer : ∀ k → pol k ≡ output → k ≡ producer)
  (listener-input : pol listener ≡ input) (distinct : listener ≢ producer)
  (initial : Family s) where

  boundary : ⟨ shape+ s ⟩ → Interface
  boundary k = interface singleton (λ _ → port tt (pol k))

  network : Network I I
  network = record
    { components = boxes (shape+ s) (λ k → record { boundary = boundary k ; Branch = Index ; initial = initial k })
    ; private-shape = singleton ; private-sort = λ _ → tt
    ; local-wire = λ { (k , tt) → inj₁ tt } ; wire-type = λ { (k , tt) → refl }
    ; aliases = [] ; alias-type = λ () }

  module W = Wiring network
  module K = Execution network

  connected-equality : ∀ {u v} → W.Connected u v → u ≡ v
  connected-equality W.same = refl
  connected-equality (W.alias ())
  connected-equality (W.reverse p) = sym (connected-equality p)
  connected-equality (W.join p q) = trans (connected-equality p) (connected-equality q)

  payload-identity : ∀ {u v} (eq : u ≡ v) (x : X) → subst (λ _ → X) eq x ≡ x
  payload-identity eq x = cong (λ z → subst (λ _ → X) z x) (≡-irrelevant eq refl)

  gather : ∀ {q r : Family s} x → (∀ k → q k ─[ visible (event (tt , x)) ]→ r k)
    → K.Gather (inj₁ tt) x q r
  gather x offers = record
    { selected = λ _ → just tt ; incident = λ { {k} tt conn → tt , refl }
    ; on-wire = λ { {k} {tt} refl → W.same }
    ; advances = λ { {k} {tt} refl → offers k }
    ; absent = λ () ; inhabited = producer , tt , refl }

  handshake : ∀ {q r x offers} → K.Handshake (gather {q} {r} x offers)
  handshake = record
    { output-support = record
        { provider = producer , tt , refl , producer-output
        ; unique-output = λ { {k} {tt} _ out-eq → only-producer k out-eq } }
    ; listener = listener , tt , refl , listener-input , distinct }

  gather-invert : ∀ {n x q r} → K.Gather n x q r → ∀ k → q k ─[ visible (event (tt , x)) ]→ r k
  gather-invert {n = n} {x = x} {q = q} {r = r} g k = chosen (K.Gather.incident g {k} tt connection)
    where
    connection : W.Connected (inj₁ tt) n
    connection = subst (W.Connected (inj₁ tt)) name-eq W.same
      where
      name-eq : inj₁ tt ≡ n
      name-eq = connected-equality (K.Gather.on-wire g (proj₂ (proj₂ (K.Gather.inhabited g))))
    chosen : Σ ⊤ (λ p → K.Gather.selected g k ≡ just p) → q k ─[ visible (event (tt , x)) ]→ r k
    chosen (tt , eq) = subst (λ y → q k ─[ visible (event (tt , y)) ]→ r k)
      (payload-identity (sym (K.class-payload {kp = k , tt} (K.Gather.on-wire g {k = k} {p = tt} eq))) x)
      (K.Gather.advances g {k = k} {p = tt} eq)

  native : Family s → Tree
  native q = Hide (λ _ → true) (fold s q)

  data Related : Tree → K.Configuration → Set where
    live : ∀ q → Related (native q) (K.running q)
    settled : Related stop K.completed

  native-hidden : ∀ {q r : Family s} x → (∀ k → q k ─[ visible (event (tt , x)) ]→ r k)
    → native q ─[ τ ]→ native r
  native-hidden x offers = P.hide-hidden (λ _ → true) refl (fold-event s (tt , x) offers)

  network-hidden : ∀ {q r : Family s} x → (∀ k → q k ─[ visible (event (tt , x)) ]→ r k)
    → K._─[_]→_ (K.running q) K.τ (K.running r)
  network-hidden x offers = K.hidden x (gather x offers) (λ { (inj₁ ()) ; (inj₂ ()) }) handshake

  data Matching : L.Label → K.Label → Set where
    silent-label : Matching τ K.τ
    return-label : Matching (visible (√ tt)) (K.visible K.√)

  update-fold : ∀ k p q → fold s (K.update k p q) ≡ fold s (replace s k p q)
  update-fold k p q = fold-cong s pointwise
    where
    pointwise : ∀ j → K.update k p q j ≡ replace s k p q j
    pointwise j with index-equality (shape+ s) k j
    ... | yes refl = refl
    ... | no _ = refl

  native-silent-step : ∀ {q t} → native q ─[ τ ]→ t
    → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) K.τ c × Related t c)
  native-silent-step {q} step = invert (P.hide-silent-invert (λ _ → true) step)
    where
    local : ∀ {r} → LocalMove s q r → Σ K.Configuration
      (λ c → K._─[_]→_ (K.running q) K.τ c × Related (Hide (λ _ → true) r) c)
    local m = K.running (K.update (LocalMove.box m) (LocalMove.next m) q) ,
      K.internal (LocalMove.step m) ,
      subst (λ t → Related t (K.running (K.update (LocalMove.box m) (LocalMove.next m) q)))
        (cong (Hide (λ _ → true))
          (trans (update-fold (LocalMove.box m) (LocalMove.next m) q) (sym (LocalMove.target m))))
        (live (K.update (LocalMove.box m) (LocalMove.next m) q))
    rendezvous : ∀ {r e} → AllMove s q e r → Σ K.Configuration
      (λ c → K._─[_]→_ (K.running q) K.τ c × Related (Hide (λ _ → true) r) c)
    rendezvous {e = tt , x} m = K.running (AllMove.next m) , network-hidden x (AllMove.steps m) ,
      subst (λ t → Related t (K.running (AllMove.next m)))
        (cong (Hide (λ _ → true)) (sym (AllMove.target m))) (live (AllMove.next m))
    invert : ∀ {t} → P.HideSilent (λ _ → true) (fold s q) t
      → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) K.τ c × Related t c)
    invert (P.original sp) = local (fold-silent-invert s q sp)
    invert (P.concealed-event {e = e} _ sp) = rendezvous (fold-event-invert s q e sp)

  native-return-step : ∀ {q t} → native q ─[ visible (√ tt) ]→ t
    → K._─[_]→_ (K.running q) (K.visible K.√) K.completed × Related t K.completed
  native-return-step {q} step = K.finish producer
    (fold-return-invert s q (proj₁ (P.hide-return-invert (λ _ → true) step))) ,
    subst (λ t → Related t K.completed) (sym (proj₂ (P.hide-return-invert (λ _ → true) step))) settled

  native-step : ∀ {q l t} → native q ─[ l ]→ t
    → Σ K.Label (λ kl → Σ K.Configuration
        (λ c → Matching l kl × K._─[_]→_ (K.running q) kl c × Related t c))
  native-step {l = τ} step = K.τ , silent-result (native-silent-step step)
    where
    silent-result : ∀ {t q} → Σ K.Configuration
      (λ c → K._─[_]→_ (K.running q) K.τ c × Related t c)
      → Σ K.Configuration (λ c → Matching τ K.τ × K._─[_]→_ (K.running q) K.τ c × Related t c)
    silent-result (c , sp , related) = c , silent-label , sp , related
  native-step {l = visible (√ tt)} step =
    K.visible K.√ , K.completed , return-label , native-return-step step
  native-step {l = visible (event e)} step = ⊥-elim (P.hide-all-no-event step)

  network-step : ∀ {q kl c} → K._─[_]→_ (K.running q) kl c
    → Σ L.Label (λ l → Σ Tree (λ t → Matching l kl × native q ─[ l ]→ t × Related t c))
  network-step {q} (K.internal {k = k} {t = t} step) =
    τ , native (K.update k t q) , silent-label ,
    subst (λ r → native q ─[ τ ]→ Hide (λ _ → true) r) (sym (update-fold k t q))
      (P.hide-silent-step (λ _ → true) (fold-silent s q k step)) , live (K.update k t q)
  network-step (K.exterior {e = inj₁ ()} _ _ _)
  network-step (K.exterior {e = inj₂ ()} _ _ _)
  network-step {q} (K.hidden {q′ = r} x g _ _) =
    τ , native r , silent-label , native-hidden x (gather-invert g) , live r
  network-step {q} (K.finish _ ready) = visible (√ tt) , stop , return-label ,
    P.hide-return (λ _ → true) (fold-return s q ready) , settled

  related-native-step : ∀ {p c l t} → Related p c → p ─[ l ]→ t
    → Σ K.Label (λ kl → Σ K.Configuration
        (λ c′ → Matching l kl × K._─[_]→_ c kl c′ × Related t c′))
  related-native-step (live q) = native-step
  related-native-step settled step = ⊥-elim (stop-no-step step)

  related-network-step : ∀ {p c kl c′} → Related p c → K._─[_]→_ c kl c′
    → Σ L.Label (λ l → Σ Tree (λ t → Matching l kl × p ─[ l ]→ t × Related t c′))
  related-network-step (live q) = network-step
  related-network-step settled step = ⊥-elim (K.completed-no-step step)

  -- The relation is closed under every actual step, not under a supplied
  -- semantic certificate. Its guarded closure matches divergence stepwise.
  record Bisim (p : Tree) (c : K.Configuration) : Set where
    coinductive
    field
      forward : ∀ {l t} → p ─[ l ]→ t → Σ K.Label (λ kl → Σ K.Configuration
        (λ c′ → Matching l kl × K._─[_]→_ c kl c′ × Bisim t c′))
      backward : ∀ {kl c′} → K._─[_]→_ c kl c′ → Σ L.Label (λ l → Σ Tree
        (λ t → Matching l kl × p ─[ l ]→ t × Bisim t c′))

  correspondence : ∀ {p c} → Related p c → Bisim p c
  Bisim.forward (correspondence related) step = continue (related-native-step related step)
    where
    continue : ∀ {l t c} → Σ K.Label (λ kl → Σ K.Configuration
      (λ c′ → Matching l kl × K._─[_]→_ c kl c′ × Related t c′))
      → Σ K.Label (λ kl → Σ K.Configuration
        (λ c′ → Matching l kl × K._─[_]→_ c kl c′ × Bisim t c′))
    continue (kl , c′ , labels , sp , next) = kl , c′ , labels , sp , correspondence next
  Bisim.backward (correspondence related) step = continue (related-network-step related step)
    where
    continue : ∀ {p kl c′} → Σ L.Label (λ l → Σ Tree
      (λ t → Matching l kl × p ─[ l ]→ t × Related t c′))
      → Σ L.Label (λ l → Σ Tree (λ t → Matching l kl × p ─[ l ]→ t × Bisim t c′))
    continue (l , t , labels , sp , next) = l , t , labels , sp , correspondence next

  initial-correspondence : Bisim (native initial) K.initial-configuration
  initial-correspondence = correspondence (live initial)

  related-native-silent : ∀ {p c t} → Related p c → p ─[ τ ]→ t
    → Σ K.Configuration (λ c′ → K._─[_]→_ c K.τ c′ × Related t c′)
  related-native-silent related step = extract (related-native-step related step)
    where
    extract : ∀ {c t} → Σ K.Label (λ kl → Σ K.Configuration
      (λ c′ → Matching τ kl × K._─[_]→_ c kl c′ × Related t c′))
      → Σ K.Configuration (λ c′ → K._─[_]→_ c K.τ c′ × Related t c′)
    extract (_ , c′ , silent-label , sp , next) = c′ , sp , next

  related-network-silent : ∀ {p c c′} → Related p c → K._─[_]→_ c K.τ c′
    → Σ Tree (λ t → p ─[ τ ]→ t × Related t c′)
  related-network-silent related step = extract (related-network-step related step)
    where
    extract : ∀ {p c′} → Σ L.Label (λ l → Σ Tree
      (λ t → Matching l K.τ × p ─[ l ]→ t × Related t c′))
      → Σ Tree (λ t → p ─[ τ ]→ t × Related t c′)
    extract (_ , t , silent-label , sp , next) = t , sp , next

  mutual
    native-divergence : ∀ {p c} → Related p c → Diverges p → K.Diverges c
    native-divergence related d = native-tail
      (related-native-silent related (Diverges.step d)) (Diverges.rest d)

    native-tail : ∀ {c t} → Σ K.Configuration
      (λ c′ → K._─[_]→_ c K.τ c′ × Related t c′) → Diverges t → K.Diverges c
    K.Diverges.next (native-tail (c′ , sp , next) d) = c′
    K.Diverges.step (native-tail (c′ , sp , next) d) = sp
    K.Diverges.rest (native-tail (c′ , sp , next) d) = native-divergence next d

  mutual
    network-divergence : ∀ {p c} → Related p c → K.Diverges c → Diverges p
    network-divergence related d = network-tail
      (related-network-silent related (K.Diverges.step d)) (K.Diverges.rest d)

    network-tail : ∀ {p c′} → Σ Tree
      (λ t → p ─[ τ ]→ t × Related t c′) → K.Diverges c′ → Diverges p
    Diverges.next (network-tail (t , sp , next) d) = t
    Diverges.step (network-tail (t , sp , next) d) = sp
    Diverges.rest (network-tail (t , sp , next) d) = network-divergence next d
