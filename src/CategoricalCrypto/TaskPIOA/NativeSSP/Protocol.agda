{-# OPTIONS --safe --without-K #-}

-- The connector calls the two component protocols; it does not inspect their
-- states. In particular, a right sender is sampled before its left receiver.
module CategoricalCrypto.TaskPIOA.NativeSSP.Protocol where

open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Coins
open import CategoricalCrypto.SSP.Dist.Kernel using
  (Coins; done; coins; sample; _>>=ᶜ_; _≈ᵏ_; ≈ᶜ⇒≈ᵏ; ≈ᵏ-trans; ≈ᵏ-sym; ≈ᵏ->>=ᶜ; ≈ᵏ-refl
  ; >>=ᶜ-ret; _⊑_; sampling; ⊑-run)
open import CategoricalCrypto.SSP.Dist.Laws using (coins-comm)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation using (evalC; evalC-cong; runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core using
  (Signature; Wiring; Input; Output; Task; Schedule; productSignature; find; left; right; prepend; emit)
open import CategoricalCrypto.TaskPIOA.NativeSSP.Core
open import CategoricalCrypto.TaskPIOA.NativeSSP.Product using (connect)
open import ProbabilisticLogic.Distribution.RationalDist

module _ {A B J} (w : Wiring A B J) where
  private S = productSignature A B J

  leftInput : Maybe (Input A) → P.Calls (Boundary A ⊗ᴵ Boundary B) ⊤
  leftInput nothing = P.ret tt
  leftInput (just i) = P.call (inj₁ (inj₁ i)) tt λ _ → P.ret tt

  rightInput : Maybe (Input B) → P.Calls (Boundary A ⊗ᴵ Boundary B) ⊤
  rightInput nothing = P.ret tt
  rightInput (just i) = P.call (inj₂ (inj₁ i)) tt λ _ → P.ret tt

  continuationLeft : Maybe (Output A) → P.Calls (Boundary A ⊗ᴵ Boundary B) (⊤ × Maybe (Output S))
  continuationLeft nothing = P.ret (tt , nothing)
  continuationLeft (just o) = rightInput (find (right w) (inj₂ o)) >>=ᶜ λ _ → P.ret (tt , just (inj₁ o))

  continuationRight : Maybe (Output B) → P.Calls (Boundary A ⊗ᴵ Boundary B) (⊤ × Maybe (Output S))
  continuationRight nothing = P.ret (tt , nothing)
  continuationRight (just o) = leftInput (find (left w) (inj₂ o)) >>=ᶜ λ _ → P.ret (tt , just (inj₂ o))

  connector : P.Protocol (Boundary A ⊗ᴵ Boundary B) (Boundary S)
  connector = record
    { St = ⊤ ; init = tt
    ; step = λ where
        _ (inj₁ i) _ → leftInput (find (left w) (inj₁ i)) >>=ᶜ λ _ →
          rightInput (find (right w) (inj₁ i)) >>=ᶜ λ _ → P.ret (tt , nothing)
        _ (inj₂ (inj₁ t)) _ → P.call (inj₁ (inj₂ t)) tt continuationLeft
        _ (inj₂ (inj₂ t)) _ → P.call (inj₂ (inj₂ t)) tt continuationRight }

  installed : (M : Machine A) (N : Machine B) → P.Protocol unitᴵ (Boundary S)
  installed M N = (connector P.∘ᵖ (protocol M P.⊗ᵖ protocol N)) P.∘ᵖ P.⌜ λᴵ ⌝

  embed : (M : Machine A) (N : Machine B) → State M × State N → P.St (installed M N)
  embed M N p = (tt , p) , tt

private variable X : Set

scheduled : ∀ {S} (V : P.Protocol unitᴵ (Boundary S)) → Schedule S → P.St V → P.Calls unitᴵ (List (Output S))
scheduled V [] q = P.ret []
scheduled {S} V (t ∷ ρ) q = P.step V q (inj₂ t) tt >>=ᶜ λ (q′ , o) → P.mapᶜ (prepend o) (scheduled {S} V ρ q′)

scheduled-core : ∀ {S} (M : Machine S) ρ q → scheduled {S} (protocol M) ρ q P.≈ᶜ scheduledTree M ρ q
scheduled-core M [] q = P.ret refl
scheduled-core {S} M (t ∷ ρ) q = bind-call-cong {t = P.step (protocol M) q (inj₂ t) tt}
  P.≈ᶜ-refl (λ (q′ , o) → P.mapᶜ-cong (prepend o) (scheduled-core {S} M ρ q′))

scheduled-simulation : ∀ {S} (V W : P.Protocol unitᴵ (Boundary S)) (θ : P.St V → P.St W)
  → (∀ q c → P.mapᶜ (map₁ θ) (P.step V q c tt) ≈ᵏ P.step W (θ q) c tt)
  → ∀ ρ q → scheduled {S} V ρ q ≈ᵏ scheduled {S} W ρ (θ q)
scheduled-simulation V W θ square [] q = ≈ᶜ⇒≈ᵏ (P.ret refl)
scheduled-simulation {S} V W θ square (t ∷ ρ) q = ≈ᵏ-trans
  (≈ᵏ->>=ᶜ {t = P.step V q (inj₂ t) tt} ≈ᵏ-refl
    (λ (q′ , o) → map-kernel (prepend o) (scheduled-simulation {S} V W θ square ρ q′)))
  (≈ᵏ-trans (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym
    (bind-map (map₁ θ) (P.step V q (inj₂ t) tt)
      (λ (q′ , o) → P.mapᶜ (prepend o) (scheduled {S} W ρ q′)))))
    (≈ᵏ->>=ᶜ (square q (inj₂ t)) (λ _ → ≈ᵏ-refl)))

module _ {A B J} (w : Wiring A B J) (M : Machine A) (N : Machine B) where
  private
    S = productSignature A B J
    T = protocol M P.⊗ᵖ protocol N
    U = connector w

  component : (p : State M × State N) (c : Ch (Boundary A ⊗ᴵ Boundary B))
    → Coins ((State M × State N) × R (Boundary A ⊗ᴵ Boundary B) c)
  component (q , r) (inj₁ (inj₁ i)) = mapCoins (λ q′ → ((q′ , r) , nothing)) (deliver M i q)
  component (q , r) (inj₁ (inj₂ t)) = mapCoins (λ (o , q′) → ((q′ , r) , o)) (tick M t q)
  component (q , r) (inj₂ (inj₁ i)) = mapCoins (λ r′ → ((q , r′) , nothing)) (deliver N i r)
  component (q , r) (inj₂ (inj₂ t)) = mapCoins (λ (o , r′) → ((q , r′) , o)) (tick N t r)

  component-tree : ∀ p c a → P.step T p c a P.≈ᶜ coins (component p c)
  component-tree (q , r) (inj₁ (inj₁ i)) tt = P.≈ᶜ-trans
    (P.mapᶜ-cong (map₁ (_, r)) (reindex-coins ι₁ (mapCoins (_, nothing) (deliver M i q))))
    (P.≈ᶜ-trans (map-coins (map₁ (_, r)) (mapCoins (_, nothing) (deliver M i q)))
      (coins-map-compose (_, nothing) (map₁ (_, r)) (deliver M i q)))
  component-tree (q , r) (inj₁ (inj₂ t)) tt = P.≈ᶜ-trans
    (P.mapᶜ-cong (map₁ (_, r)) (reindex-coins ι₁ (mapCoins swap (tick M t q))))
    (P.≈ᶜ-trans (map-coins (map₁ (_, r)) (mapCoins swap (tick M t q)))
      (coins-map-compose swap (map₁ (_, r)) (tick M t q)))
  component-tree (q , r) (inj₂ (inj₁ i)) tt = P.≈ᶜ-trans
    (P.mapᶜ-cong (map₁ (q ,_)) (reindex-coins ι₂ (mapCoins (_, nothing) (deliver N i r))))
    (P.≈ᶜ-trans (map-coins (map₁ (q ,_)) (mapCoins (_, nothing) (deliver N i r)))
      (coins-map-compose (_, nothing) (map₁ (q ,_)) (deliver N i r)))
  component-tree (q , r) (inj₂ (inj₂ t)) tt = P.≈ᶜ-trans
    (P.mapᶜ-cong (map₁ (q ,_)) (reindex-coins ι₂ (mapCoins swap (tick N t r))))
    (P.≈ᶜ-trans (map-coins (map₁ (q ,_)) (mapCoins swap (tick N t r)))
      (coins-map-compose swap (map₁ (q ,_)) (tick N t r)))

  interpret : P.Calls (Boundary A ⊗ᴵ Boundary B) (⊤ × X)
    → State M × State N → P.Calls (unitᴵ ⊗ᴵ unitᴵ) ((⊤ × (State M × State N)) × X)
  interpret (P.ret (s , x)) p = P.ret ((s , p) , x)
  interpret (P.call c a k) p = coins (component p c) >>=ᶜ λ (p′ , r) → interpret (k r) p′
  interpret (P.coin μ k) p = P.coin μ λ b → interpret (k b) p
  interpret P.dead p = P.dead

  tensor-interpret : (t : P.Calls (Boundary A ⊗ᴵ Boundary B) (⊤ × X)) (p : State M × State N)
    → P.graft U T t p P.≈ᶜ interpret t p
  tensor-interpret (P.ret x) p = P.ret refl
  tensor-interpret (P.call c a k) p = P.≈ᶜ-trans
    (serve-tree-cong U T k (component-tree p c a))
    (P.≈ᶜ-trans (serve-coins U T {c = c} k (component p c))
      (bind-call-cong {t = coins (component p c)} P.≈ᶜ-refl (λ (p′ , r) → tensor-interpret (k r) p′)))
  tensor-interpret (P.coin μ k) p = P.coin λ b → tensor-interpret (k b) p
  tensor-interpret P.dead p = P.dead

  interpret-left : (i : Maybe (Input A))
    (k : ⊤ → P.Calls (Boundary A ⊗ᴵ Boundary B) (⊤ × X)) (q : State M) (r : State N)
    → interpret (leftInput w i >>=ᶜ k) (q , r) P.≈ᶜ
      (coins (receive M i q) >>=ᶜ λ q′ → interpret (k tt) (q′ , r))
  interpret-left nothing k q r = P.≈ᶜ-refl
  interpret-left (just i) k q r = coins-map-bind
    (λ q′ → ((q′ , r) , nothing)) (deliver M i q)
    (λ (p′ , _) → interpret (k tt) p′)

  interpret-right : (i : Maybe (Input B))
    (k : ⊤ → P.Calls (Boundary A ⊗ᴵ Boundary B) (⊤ × X)) (q : State M) (r : State N)
    → interpret (rightInput w i >>=ᶜ k) (q , r) P.≈ᶜ
      (coins (receive N i r) >>=ᶜ λ r′ → interpret (k tt) (q , r′))
  interpret-right nothing k q r = P.≈ᶜ-refl
  interpret-right (just i) k q r = coins-map-bind
    (λ r′ → ((q , r′) , nothing)) (deliver N i r)
    (λ (p′ , _) → interpret (k tt) p′)

  afterLeft : Maybe (Output A) → State M × State N → Coins ((State M × State N) × Maybe (Output S))
  afterLeft nothing p = done (p , nothing)
  afterLeft (just o) (q , r) = mapCoins (λ r′ → ((q , r′) , just (inj₁ o)))
    (receive N (find (right w) (inj₂ o)) r)

  afterRight : Maybe (Output B) → State M × State N → Coins ((State M × State N) × Maybe (Output S))
  afterRight nothing p = done (p , nothing)
  afterRight (just o) (q , r) = mapCoins (λ q′ → ((q′ , r) , just (inj₂ o)))
    (receive M (find (left w) (inj₂ o)) q)

  operation : Ch (Boundary S) → State M × State N → Coins ((State M × State N) × Maybe (Output S))
  operation (inj₁ i) (q , r) = mapCoins (_, nothing)
    (pairCoins (receive M (find (left w) (inj₁ i)) q) (receive N (find (right w) (inj₁ i)) r))
  operation (inj₂ (inj₁ t)) (q , r) = tick M t q >>=ᶜᵒ λ (o , q′) → afterLeft o (q′ , r)
  operation (inj₂ (inj₂ t)) (q , r) = tick N t r >>=ᶜᵒ λ (o , r′) → afterRight o (q , r′)

  tag : (State M × State N) × X → (⊤ × (State M × State N)) × X
  tag (p , x) = (tt , p) , x

  after-left-tree : ∀ o q r → interpret (continuationLeft w o) (q , r) P.≈ᶜ coins (mapCoins tag (afterLeft o (q , r)))
  after-left-tree nothing q r = P.ret refl
  after-left-tree (just o) q r = P.≈ᶜ-trans
    (interpret-right (find (right w) (inj₂ o)) (λ _ → P.ret (tt , just (inj₁ o))) q r)
    (P.≈ᶜ-trans (P.≈ᶜ-sym (map-result (λ r′ → ((tt , (q , r′)) , just (inj₁ o)))
      (receive N (find (right w) (inj₂ o)) r)))
      (P.≈ᶜ-sym (coins-map-compose (λ r′ → ((q , r′) , just (inj₁ o))) tag
        (receive N (find (right w) (inj₂ o)) r))))

  after-right-tree : ∀ o q r → interpret (continuationRight w o) (q , r) P.≈ᶜ coins (mapCoins tag (afterRight o (q , r)))
  after-right-tree nothing q r = P.ret refl
  after-right-tree (just o) q r = P.≈ᶜ-trans
    (interpret-left (find (left w) (inj₂ o)) (λ _ → P.ret (tt , just (inj₂ o))) q r)
    (P.≈ᶜ-trans (P.≈ᶜ-sym (map-result (λ q′ → ((tt , (q′ , r)) , just (inj₂ o)))
      (receive M (find (left w) (inj₂ o)) q)))
      (P.≈ᶜ-sym (coins-map-compose (λ q′ → ((q′ , r) , just (inj₂ o))) tag
        (receive M (find (left w) (inj₂ o)) q))))

  operation-tree : ∀ c p → interpret (P.step U tt c tt) p P.≈ᶜ coins (mapCoins tag (operation c p))
  operation-tree (inj₁ i) (q , r) = P.≈ᶜ-trans
    (interpret-left (find (left w) (inj₁ i))
      (λ _ → rightInput w (find (right w) (inj₁ i)) >>=ᶜ λ _ → P.ret (tt , nothing)) q r)
    (P.≈ᶜ-trans
      (bind-call-cong {t = coins (receive M (find (left w) (inj₁ i)) q)} P.≈ᶜ-refl (λ q′ →
        interpret-right (find (right w) (inj₁ i)) (λ _ → P.ret (tt , nothing)) q′ r))
      (P.≈ᶜ-sym (P.≈ᶜ-trans
        (coins-map-compose (_, nothing) tag
          (pairCoins (receive M (find (left w) (inj₁ i)) q) (receive N (find (right w) (inj₁ i)) r)))
        (P.≈ᶜ-trans
          (pair-calls (receive M (find (left w) (inj₁ i)) q) (receive N (find (right w) (inj₁ i)) r)
            (λ q′ r′ → ((tt , (q′ , r′)) , nothing)))
          (bind-call-cong {t = coins (receive M (find (left w) (inj₁ i)) q)} P.≈ᶜ-refl (λ q′ →
            P.≈ᶜ-trans (map-coins (λ r′ → ((tt , (q′ , r′)) , nothing))
              (receive N (find (right w) (inj₁ i)) r))
              (map-result (λ r′ → ((tt , (q′ , r′)) , nothing))
                (receive N (find (right w) (inj₁ i)) r))))))))
  operation-tree (inj₂ (inj₁ t)) (q , r) = P.≈ᶜ-trans
    (coins-map-bind (λ (o , q′) → ((q′ , r) , o)) (tick M t q)
      (λ (p′ , o) → interpret (continuationLeft w o) p′))
    (P.≈ᶜ-trans (bind-call-cong {t = coins (tick M t q)} P.≈ᶜ-refl (λ (o , q′) → after-left-tree o q′ r))
      (P.≈ᶜ-sym (mapped-bind-calls tag (tick M t q) (λ (o , q′) → afterLeft o (q′ , r)))))
  operation-tree (inj₂ (inj₂ t)) (q , r) = P.≈ᶜ-trans
    (coins-map-bind (λ (o , r′) → ((q , r′) , o)) (tick N t r)
      (λ (p′ , o) → interpret (continuationRight w o) p′))
    (P.≈ᶜ-trans (bind-call-cong {t = coins (tick N t r)} P.≈ᶜ-refl (λ (o , r′) → after-right-tree o q r′))
      (P.≈ᶜ-sym (mapped-bind-calls tag (tick N t r) (λ (o , r′) → afterRight o (q , r′)))))

  installed-tree : ∀ c p → P.step (installed w M N) (embed w M N p) c tt P.≈ᶜ
    coins (mapCoins (map₁ (embed w M N)) (operation c p))
  installed-tree c p = P.≈ᶜ-trans
    (graft-cong (U P.∘ᵖ T) P.⌜ λᴵ ⌝
      (P.≈ᶜ-trans (tensor-interpret (P.step U tt c tt) p) (operation-tree c p)) tt)
    (P.≈ᶜ-trans (close-coins (U P.∘ᵖ T) (mapCoins tag (operation c p)))
      (coins-map-compose tag (λ (s , x) → ((s , tt) , x)) (operation c p)))

  routeRight : Maybe (Output A) → Maybe (Input B)
  routeRight nothing = nothing
  routeRight (just o) = find (right w) (inj₂ o)

  routeLeft : Maybe (Output B) → Maybe (Input A)
  routeLeft nothing = nothing
  routeLeft (just o) = find (left w) (inj₂ o)

  left-normal : ∀ {I} (f : (State M × State N) × Maybe (Output S) → X) o q r
    → coins {A = I} (mapCoins f (afterLeft o (q , r))) P.≈ᶜ
      (coins (receive N (routeRight o) r) >>=ᶜ λ r′ → P.ret (f ((q , r′) , Maybe.map inj₁ o)))
  left-normal f nothing q r = P.ret refl
  left-normal f (just o) q r = P.≈ᶜ-trans
    (coins-map-compose (λ r′ → ((q , r′) , just (inj₁ o))) f
      (receive N (find (right w) (inj₂ o)) r))
    (map-result (λ r′ → f ((q , r′) , just (inj₁ o))) (receive N (find (right w) (inj₂ o)) r))

  right-normal : ∀ {I} (f : (State M × State N) × Maybe (Output S) → X) o q r
    → coins {A = I} (mapCoins f (afterRight o (q , r))) P.≈ᶜ
      (coins (receive M (routeLeft o) q) >>=ᶜ λ q′ → P.ret (f ((q′ , r) , Maybe.map inj₂ o)))
  right-normal f nothing q r = P.ret refl
  right-normal f (just o) q r = P.≈ᶜ-trans
    (coins-map-compose (λ q′ → ((q′ , r) , just (inj₂ o))) f
      (receive M (find (left w) (inj₂ o)) q))
    (map-result (λ q′ → f ((q′ , r) , just (inj₂ o))) (receive M (find (left w) (inj₂ o)) q))

  left-selected : ∀ {I} (f : (State M × State N) × Maybe (Output S) → X)
    (κ : Coins (State M)) o r
    → coins {A = I} (mapCoins f (mapCoins (o ,_) κ >>=ᶜᵒ λ (o′ , q′) → afterLeft o′ (q′ , r))) P.≈ᶜ
      (coins κ >>=ᶜ λ q′ → coins (receive N (routeRight o) r) >>=ᶜ λ r′ →
        P.ret (f ((q′ , r′) , Maybe.map inj₁ o)))
  left-selected f κ o r = P.≈ᶜ-trans
    (selected-result f κ (o ,_) (λ (o′ , q′) → afterLeft o′ (q′ , r)))
    (bind-call-cong {t = coins κ} P.≈ᶜ-refl (λ q′ → left-normal f o q′ r))

  right-selected : ∀ {I} (f : (State M × State N) × Maybe (Output S) → X)
    (κ : Coins (State N)) o q
    → coins {A = I} (mapCoins f (mapCoins (o ,_) κ >>=ᶜᵒ λ (o′ , r′) → afterRight o′ (q , r′))) P.≈ᶜ
      (coins κ >>=ᶜ λ r′ → coins (receive M (routeLeft o) q) >>=ᶜ λ q′ →
        P.ret (f ((q′ , r′) , Maybe.map inj₂ o)))
  right-selected f κ o q = P.≈ᶜ-trans
    (selected-result f κ (o ,_) (λ (o′ , r′) → afterRight o′ (q , r′)))
    (bind-call-cong {t = coins κ} P.≈ᶜ-refl (λ r′ → right-normal f o q r′))

  nativeStep : Ch (Boundary S) → State M × State N → Coins ((State M × State N) × Maybe (Output S))
  nativeStep (inj₁ i) p = mapCoins (_, nothing) (deliver (connect w M N) i p)
  nativeStep (inj₂ t) p = mapCoins swap (tick (connect w M N) t p)

  native-operation : ∀ {I} (f : (State M × State N) × Maybe (Output S) → X) c p
    → coins {A = I} (mapCoins f (nativeStep c p)) ≈ᵏ coins (mapCoins f (operation c p))
  native-operation f (inj₁ i) p = ≈ᶜ⇒≈ᵏ P.≈ᶜ-refl
  native-operation f (inj₂ (inj₁ t)) (q , r) with select M q t
  ... | nothing = ≈ᶜ⇒≈ᵏ (P.ret refl)
  ... | just (inj₁ o) = ≈ᶜ⇒≈ᵏ (P.≈ᶜ-trans
    (native-result f (just (inj₁ o)) (transition M (inj₁ o) q) (receive N (find (right w) (inj₂ o)) r))
    (P.≈ᶜ-sym (left-selected f (transition M (inj₁ o) q) (just o) r)))
  ... | just (inj₂ h) = ≈ᶜ⇒≈ᵏ (P.≈ᶜ-trans
    (native-result f nothing (transition M (inj₂ h) q) (done r))
    (P.≈ᶜ-sym (left-selected f (transition M (inj₂ h) q) nothing r)))
  native-operation f (inj₂ (inj₂ t)) (q , r) with select N r t
  ... | nothing = ≈ᶜ⇒≈ᵏ (P.ret refl)
  ... | just (inj₁ o) = ≈ᵏ-trans
    (≈ᶜ⇒≈ᵏ (native-result f (just (inj₂ o)) (receive M (find (left w) (inj₂ o)) q) (transition N (inj₁ o) r)))
    (≈ᵏ-trans
      (coins-comm (receive M (find (left w) (inj₂ o)) q) (coins (transition N (inj₁ o) r))
        (λ q′ r′ → P.ret (f ((q′ , r′) , just (inj₂ o)))))
      (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym (right-selected f (transition N (inj₁ o) r) (just o) q))))
  ... | just (inj₂ h) = ≈ᵏ-trans
    (≈ᶜ⇒≈ᵏ (native-result f nothing (done q) (transition N (inj₂ h) r)))
    (≈ᵏ-trans (coins-comm (done q) (coins (transition N (inj₂ h) r))
      (λ q′ r′ → P.ret (f ((q′ , r′) , nothing))))
      (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym (right-selected f (transition N (inj₂ h) r) nothing q))))

  native-step-tree : ∀ c p → P.step (protocol (connect w M N)) p c tt P.≈ᶜ coins (nativeStep c p)
  native-step-tree (inj₁ i) p = P.≈ᶜ-refl
  native-step-tree (inj₂ t) p = P.≈ᶜ-refl

  joint-square : ∀ p c → P.mapᶜ (map₁ (embed w M N))
    (P.step (protocol (connect w M N)) p c tt) ≈ᵏ P.step (installed w M N) (embed w M N p) c tt
  joint-square p c = ≈ᵏ-trans
    (≈ᶜ⇒≈ᵏ (P.≈ᶜ-trans (P.mapᶜ-cong (map₁ (embed w M N)) (native-step-tree c p))
      (map-coins (map₁ (embed w M N)) (nativeStep c p))))
    (≈ᵏ-trans (native-operation (map₁ (embed w M N)) c p)
      (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym (installed-tree c p))))

  installed-scheduled : ∀ ρ p → scheduledTree (connect w M N) ρ p ≈ᵏ
    scheduled {S} (installed w M N) ρ (embed w M N p)
  installed-scheduled ρ p = ≈ᵏ-trans
    (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym (scheduled-core {S} (connect w M N) ρ p)))
    (scheduled-simulation {S} (protocol (connect w M N)) (installed w M N) (embed w M N) joint-square ρ p)

  installed-run : ∀ ρ p → evalC (scheduled {S} (installed w M N) ρ (embed w M N p))
    ≈Mℚ Dmap just (sample (run (connect w M N) ρ p))
  installed-run ρ p R = trans (sym (kernel-eval (installed-scheduled ρ p) R))
    (trans (evalC-cong (P.≈ᶜ-sym (run-calls (connect w M N) ρ p)) R)
      (eval-coins (run (connect w M N) ρ p) R))

  installed-trace : ∀ ρ → evalC (scheduled {S} (installed w M N) ρ (P.init (installed w M N)))
    ≈Mℚ Dmap just (trace (connect w M N) ρ)
  installed-trace ρ = installed-run ρ (start M , start N)

  joint-eval : ∀ p c → evalC (P.mapᶜ (map₁ (embed w M N))
    (P.step (protocol (connect w M N)) p c tt)) ≈Mℚ
    evalC (P.step (installed w M N) (embed w M N p) c tt)
  joint-eval p c = kernel-eval (joint-square p c)

  installed-sampling : protocol (connect w M N) ⊑ installed w M N
  installed-sampling = sampling (done ∘ embed w M N) (λ _ → refl) λ p c tt →
    ≈ᵏ-trans (≈ᵏ-sym (joint-square p c))
      (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym (>>=ᶜ-ret (map₁ (embed w M N))
        (P.step (protocol (connect w M N)) p c tt))))

  installed-context : (D : P.Protocol (Boundary S) Ωᴵ) (G : P.Protocol unitᴵ unitᴵ)
    → runᵖ ((D P.∘ᵖ protocol (connect w M N)) P.∘ᵖ G)
      ≈Mℚ runᵖ ((D P.∘ᵖ installed w M N) P.∘ᵖ G)
  installed-context = ⊑-run installed-sampling
