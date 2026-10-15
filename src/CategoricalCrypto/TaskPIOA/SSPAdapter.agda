{-# OPTIONS --safe --without-K #-}

-- Scheduled operational interpretation, not a UCSetupMorphism. A connected
-- activation samples the joint reply/state pair, including receive updates.
module CategoricalCrypto.TaskPIOA.SSPAdapter where

open import Class.DecEq
open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.Fin.Properties using () renaming (_≟_ to fin-dec)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Rational.Base using (ℚ)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using
  ( Coins; done; toss; coins; sample; _>>=ᶜ_; Oracle; ⟦_⟧; ⟦coins⟧
  ; ≈ᶜ⇒≈ᵏ; run≈ᵏ; _·_; regroup; Samples; sample-⟦⟧ )
open import CategoricalCrypto.SSP.Dist.Sampling
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation using (evalC; evalC-cong; runᵖ)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.TaskPIOA.Core
open import CategoricalCrypto.TaskPIOA.Product
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (maybeℚ)
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Product using (independent)
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

private variable
  X Y Z : Set
  S : Signature

finite-dec : (F : Finite) → DecEq ⟨ F ⟩
finite-dec empty = DecEq-⊥
finite-dec one = DecEq-⊤
finite-dec bit = DecEq-Bool
finite-dec (fin n) = record { _≟_ = fin-dec }
finite-dec (A ⊕ B) = DecEq-⊎ ⦃ finite-dec A ⦄ ⦃ finite-dec B ⦄
finite-dec (A ⊠ B) = DecEq-× ⦃ finite-dec A ⦄ ⦃ finite-dec B ⦄

Tick : Signature → Iface
Tick S = record { Ch = Task S ; Q = λ _ → ⊤ ; R = λ _ → Maybe (Output S)
                ; Ch-dec = finite-dec (tasks S) }

resource : (M : Automaton S) → P.Protocol unitᴵ (Tick S)
resource M = record
  { St = State M ; init = initial M
  ; step = λ q t _ → coins (rationalCoins (Dmap swap (tick M t q))) }

private
  eval-coins-bind : (κ : Coins X) (k : X → P.Calls unitᴵ Y)
    → evalC (coins κ >>=ᶜ k) ≈Mℚ (sample κ >>=ᴹ λ x → evalC (k x))
  eval-coins-bind (done x) k ξ = sym (>>=ᴹ-identityˡ x (evalC ∘ k) ξ)
  eval-coins-bind (toss μ f) k ξ = trans
    (>>=ᴹ-congˡ μ (λ b → evalC (coins (f b) >>=ᶜ k))
      (λ b → sample (f b) >>=ᴹ evalC ∘ k) (λ b → eval-coins-bind (f b) k) ξ)
    (sym (>>=ᴹ-assoc μ (sample ∘ f) (evalC ∘ k) ξ))

  eval-coins : (κ : Coins X) → evalC (coins κ) ≈Mℚ (sample κ >>=ᴹ return⊥)
  eval-coins (done x) ξ = sym (>>=ᴹ-identityˡ x return⊥ ξ)
  eval-coins (toss μ f) ξ = trans
    (>>=ᴹ-congˡ μ (evalC ∘ coins ∘ f) (λ b → sample (f b) >>=ᴹ return⊥)
      (λ b → eval-coins (f b)) ξ)
    (sym (>>=ᴹ-assoc μ (sample ∘ f) return⊥ ξ))

  eval-map : (f : X → Y) (t : P.Calls unitᴵ X)
    → evalC (P.mapᶜ f t) ≈Mℚ Dmap⊥ f (evalC t)
  eval-map f (P.ret x) ξ = sym (>>=⊥-identityˡ x (return⊥ ∘ f) ξ)
  eval-map f (P.call () _ _)
  eval-map f (P.coin μ k) ξ = trans
    (>>=ᴹ-congˡ μ (λ b → evalC (P.mapᶜ f (k b)))
      (λ b → Dmap⊥ f (evalC (k b))) (λ b → eval-map f (k b)) ξ)
    (sym (>>=ᴹ-assoc μ (evalC ∘ k) (kmaybe (return⊥ ∘ f)) ξ))
  eval-map f P.dead ξ = sym (>>=ᴹ-identityˡ nothing (kmaybe (return⊥ ∘ f)) ξ)

  map-total : (f : X → Y) (μ : Dist-ℚ X)
    → Dmap⊥ f (μ >>=ᴹ return⊥) ≈Mℚ (Dmap f μ >>=ᴹ return⊥)
  map-total f μ ξ = trans (>>=ᴹ-assoc μ return⊥ (kmaybe (return⊥ ∘ f)) ξ)
    (trans (>>=ᴹ-congˡ μ (λ x → return⊥ x >>=⊥ return⊥ ∘ f)
      (return⊥ ∘ f) (λ x → >>=⊥-identityˡ x (return⊥ ∘ f)) ξ)
      (sym (Dmap->>= f μ return⊥ ξ)))

native-tick : (M : Automaton S) (q : State M) (t : Task S)
  → evalC (P.step (resource M) q t tt) ≈Mℚ (Dmap swap (tick M t q) >>=ᴹ return⊥)
native-tick M q t ξ = trans (eval-coins (rationalCoins (Dmap swap (tick M t q))) ξ)
  (>>=ᴹ-congʳ return⊥ (sample (rationalCoins (Dmap swap (tick M t q))))
    (Dmap swap (tick M t q)) (rationalCoins-correct (Dmap swap (tick M t q))) ξ)

native-bind-tick : (M : Automaton S) (q : State M) (t : Task S)
  (k : State M × Maybe (Output S) → P.Calls unitᴵ X)
  → evalC (P.step (resource M) q t tt >>=ᶜ k)
    ≈Mℚ (tick M t q >>=ᴹ λ (o , q′) → evalC (k (q′ , o)))
native-bind-tick M q t k ξ = trans (eval-coins-bind (rationalCoins μ) k ξ)
  (trans (>>=ᴹ-congʳ (evalC ∘ k) (sample (rationalCoins μ)) μ (rationalCoins-correct μ) ξ)
    (Dmap->>= swap (tick M t q) (evalC ∘ k) ξ))
  where μ = Dmap swap (tick M t q)

private
  coins-ret : (κ : Coins X) → (coins {A = unitᴵ} κ >>=ᶜ P.ret) P.≈ᶜ coins κ
  coins-ret (done x) = P.ret refl
  coins-ret (toss μ f) = P.coin λ b → coins-ret (f b)

  coins-kernel : (κ : Coins X) (O : Oracle unitᴵ Y) (s : Y)
    → ⟦ coins κ ⟧ O s ≈Mℚ (sample κ >>=ᴹ λ x → return⊥ (x , s))
  coins-kernel κ O s ξ = trans (sym (run≈ᵏ (≈ᶜ⇒≈ᵏ (coins-ret κ)) O s ξ))
    (⟦coins⟧ κ P.ret O s ξ)

  total-bind : (μ : Dist-ℚ X) (f : X → Y) (k : Y → Dist⊥ Z)
    → ((μ >>=ᴹ return⊥ ∘ f) >>=⊥ k) ≈Mℚ (μ >>=ᴹ k ∘ f)
  total-bind μ f k ξ = trans (>>=ᴹ-assoc μ (return⊥ ∘ f) (kmaybe k) ξ)
    (>>=ᴹ-congˡ μ (λ x → return⊥ (f x) >>=⊥ k) (k ∘ f)
      (λ x → >>=⊥-identityˡ (f x) k) ξ)

tickOracle : (M : Automaton S) → Oracle (Tick S) (State M)
tickOracle M q t _ = tick M t q >>=ᴹ λ (o , q′) → return⊥ (q′ , o)

native-samples : (M : Automaton S) (O : Oracle unitᴵ X) (s : X)
  → Samples {A = Tick S} (λ q → return-ℚ (q , s)) (tickOracle M) (resource M · O)
native-samples M O s q t tt ξ = trans
  (>>=ᴹ-identityˡ (q , s) (λ u → (resource M · O) u t tt) ξ)
  (trans native-law (sym source-law))
  where
  μ = Dmap swap (tick M t q)
  κ = rationalCoins μ
  embed = λ x → return⊥ (x , s)
  target = tick M t q >>=ᴹ λ (o , q′) → return⊥ ((q′ , s) , o)
  H = λ (q′ , o) → return-ℚ (q′ , s) >>=ᴹ λ u → return⊥ (u , o)
  native-law : lookupᴰℚ (entries ((resource M · O) (q , s) t tt)) ξ
    ≡ lookupᴰℚ (entries target) ξ
  native-law = trans
    (>>=⊥-congʳ (return⊥ ∘ regroup) (⟦ coins κ ⟧ O s)
      (sample κ >>=ᴹ embed) (coins-kernel κ O s) ξ)
    (trans (total-bind (sample κ) (λ x → x , s) (return⊥ ∘ regroup) ξ)
      (trans (>>=ᴹ-congʳ (λ x → return⊥ (regroup (x , s))) (sample κ) μ
        (rationalCoins-correct μ) ξ)
        (Dmap->>= swap (tick M t q) (λ x → return⊥ (regroup (x , s))) ξ)))
  source-law : lookupᴰℚ (entries (tickOracle M q t tt >>=⊥ H)) ξ
    ≡ lookupᴰℚ (entries target) ξ
  source-law = trans (total-bind (tick M t q) swap H ξ)
    (>>=ᴹ-congˡ (tick M t q) (H ∘ swap)
      (λ (o , q′) → return⊥ ((q′ , s) , o))
      (λ (o , q′) → >>=ᴹ-identityˡ (q′ , s) (λ u → return⊥ (u , o))) ξ)

all-calls-agreement : (M : Automaton S) (O : Oracle unitᴵ X) (s : X)
  (t : P.Calls (Tick S) Y) (q : State M)
  → (return-ℚ (q , s) >>=ᴹ λ u → ⟦ t ⟧ (resource M · O) u)
    ≈Mℚ (⟦ t ⟧ (tickOracle M) q >>=⊥ λ p →
      return-ℚ (proj₂ p , s) >>=ᴹ λ u → return⊥ (proj₁ p , u))
all-calls-agreement {S} M O s = sample-⟦⟧ {A = Tick S}
  {ρ = λ q → return-ℚ (q , s)} {O₁ = tickOracle M} {O₂ = resource M · O}
  (native-samples M O s)

native-disabled : (M : Automaton S) → ∀ q t → choose M q t ≡ nothing
  → evalC (P.step (resource M) q t tt) ≈Mℚ return⊥ (q , nothing)
native-disabled M q t disabled ξ = trans (native-tick M q t ξ) (disabled-law ξ)
  where
  disabled-law : (Dmap swap (tick M t q) >>=ᴹ return⊥) ≈Mℚ return⊥ (q , nothing)
  disabled-law rewrite disabled = λ ξ′ → trans
    (Dmap->>= swap (return-ℚ (nothing , q)) return⊥ ξ′)
    (>>=ᴹ-identityˡ (nothing , q) (return⊥ ∘ swap) ξ′)

scheduledTree : (S : Signature) (R : P.Protocol unitᴵ (Tick S))
  → Schedule S → P.St R → P.Calls unitᴵ (List (Output S))
scheduledTree S R [] q = P.ret []
scheduledTree S R (t ∷ ρ) q = P.step R q t tt >>=ᶜ λ (q′ , o) →
  P.mapᶜ (prepend o) (scheduledTree S R ρ q′)

runTree : (M : Automaton S) → Schedule S → State M → P.Calls unitᴵ (List (Output S))
runTree {S} M = scheduledTree S (resource M)

nativeRunFrom : (M : Automaton S) → Schedule S → State M → Dist⊥ (List (Output S))
nativeRunFrom M ρ q = evalC (runTree M ρ q)

nativeTrace : (M : Automaton S) → Schedule S → Dist⊥ (List (Output S))
nativeTrace M ρ = nativeRunFrom M ρ (initial M)

run-agreement : (M : Automaton S) (ρ : Schedule S) (q : State M)
  → nativeRunFrom M ρ q ≈Mℚ (runFrom M ρ q >>=ᴹ return⊥)
run-agreement M [] q ξ = sym (>>=ᴹ-identityˡ [] return⊥ ξ)
run-agreement M (t ∷ ρ) q ξ = trans (eval-coins-bind κ K ξ)
  (trans (>>=ᴹ-congʳ (evalC ∘ K) (sample κ) μ (rationalCoins-correct μ) ξ)
    (trans (Dmap->>= swap (tick M t q) (evalC ∘ K) ξ)
      (trans (>>=ᴹ-congˡ (tick M t q) (λ (o , q′) → evalC (K (q′ , o)))
        (λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′) >>=ᴹ return⊥) inner ξ)
        (sym (>>=ᴹ-assoc (tick M t q)
          (λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′)) return⊥ ξ)))))
  where
  μ = Dmap swap (tick M t q)
  κ = rationalCoins μ
  K = λ (q′ , o) → P.mapᶜ (prepend o) (runTree M ρ q′)
  inner : ∀ p → evalC (K (swap p)) ≈Mℚ (Dmap (prepend (proj₁ p)) (runFrom M ρ (proj₂ p)) >>=ᴹ return⊥)
  inner (o , q′) ξ′ = trans (eval-map (prepend o) (runTree M ρ q′) ξ′)
    (trans (>>=⊥-congʳ (return⊥ ∘ prepend o) (nativeRunFrom M ρ q′)
      (runFrom M ρ q′ >>=ᴹ return⊥) (run-agreement M ρ q′) ξ′)
      (map-total (prepend o) (runFrom M ρ q′) ξ′))

reward-agreement : (M : Automaton S) (ρ : Schedule S) (q : State M) (reward : List (Output S) → ℚ)
  → lookupᴰℚ (entries (nativeRunFrom M ρ q)) (maybeℚ reward)
    ≡ lookupᴰℚ (entries (runFrom M ρ q)) reward
reward-agreement M ρ q reward = trans (run-agreement M ρ q (maybeℚ reward))
  (trans (lookupᴰℚ-bind (entries (runFrom M ρ q)) _ (maybeℚ reward))
    (lookupᴰℚ-cong-P (entries (runFrom M ρ q)) (λ xs → lookupᴰℚ-return (just xs) (maybeℚ reward))))

drive : (S : Signature) → Schedule S → (List (Output S) → P.Calls (Tick S) X) → P.Calls (Tick S) X
drive S [] k = k []
drive S (t ∷ ρ) k = P.call t tt λ o → drive S ρ (λ xs → k (prepend o xs))

consumer : (S : Signature) → Schedule S → (List (Output S) → Bool) → P.Protocol (Tick S) Ωᴵ
consumer S ρ verdict = record { St = ⊤ ; init = tt
  ; step = λ _ _ _ → drive S ρ (λ xs → P.ret (tt , verdict xs)) }

experiment : (M : Automaton S) → Schedule S → (List (Output S) → Bool) → Dist⊥ Bool
experiment {S} M ρ verdict = runᵖ (consumer S ρ verdict P.∘ᵖ resource M)

module ConsumerCorrespondence {S : Signature} {A : Iface}
  (M : Automaton S) (D : P.Protocol (Tick S) A) where

  private
    serve-coins : ∀ {t} (κ : Coins (State M × Maybe (Output S)))
      (k : Maybe (Output S) → P.Calls (Tick S) (P.St D × X))
      → evalC (P.mapᶜ proj₂ (P.serve D (resource M) {b = t} k (coins κ)))
        ≈Mℚ (sample κ >>=ᴹ λ (q , o) →
          evalC (P.mapᶜ proj₂ (P.graft D (resource M) (k o) q)))
    serve-coins (done (q , o)) k ξ = sym (>>=ᴹ-identityˡ (q , o)
      (λ (q′ , o′) → evalC (P.mapᶜ proj₂ (P.graft D (resource M) (k o′) q′))) ξ)
    serve-coins (toss μ f) k ξ = trans
      (>>=ᴹ-congˡ μ
        (λ b → evalC (P.mapᶜ proj₂ (P.serve D (resource M) k (coins (f b)))))
        (λ b → sample (f b) >>=ᴹ λ (q , o) →
          evalC (P.mapᶜ proj₂ (P.graft D (resource M) (k o) q)))
        (λ b → serve-coins (f b) k) ξ)
      (sym (>>=ᴹ-assoc μ (sample ∘ f)
        (λ (q , o) → evalC (P.mapᶜ proj₂ (P.graft D (resource M) (k o) q))) ξ))

  execution : (d : P.St D) (ρ : Schedule S) (q : State M) (f : List (Output S) → X)
    → evalC (P.mapᶜ proj₂ (P.graft D (resource M)
        (drive S ρ (λ xs → P.ret (d , f xs))) q))
      ≈Mℚ (runFrom M ρ q >>=ᴹ return⊥ ∘ f)
  execution d [] q f ξ = sym (>>=ᴹ-identityˡ [] (return⊥ ∘ f) ξ)
  execution d (t ∷ ρ) q f ξ = trans (serve-coins {t = t} κ K ξ)
    (trans (>>=ᴹ-congʳ continuation (sample κ) μ (rationalCoins-correct μ) ξ)
      (trans (Dmap->>= swap (tick M t q) continuation ξ)
        (trans (>>=ᴹ-congˡ (tick M t q)
          (λ (o , q′) → continuation (q′ , o))
          (λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′) >>=ᴹ return⊥ ∘ f)
          (λ (o , q′) ξ′ → trans (execution d ρ q′ (f ∘ prepend o) ξ′)
            (sym (Dmap->>= (prepend o) (runFrom M ρ q′) (return⊥ ∘ f) ξ′))) ξ)
          (sym (>>=ᴹ-assoc (tick M t q)
            (λ (o , q′) → Dmap (prepend o) (runFrom M ρ q′)) (return⊥ ∘ f) ξ)))))
    where
    μ = Dmap swap (tick M t q)
    κ = rationalCoins μ
    K = λ o → drive S ρ (λ xs → P.ret (d , f (prepend o xs)))
    continuation = λ (q′ , o) → evalC (P.mapᶜ proj₂ (P.graft D (resource M) (K o) q′))

experiment-agreement : (M : Automaton S) (ρ : Schedule S) (verdict : List (Output S) → Bool)
  → experiment M ρ verdict ≈Mℚ (traceDist M ρ >>=ᴹ return⊥ ∘ verdict)
experiment-agreement {S} M ρ verdict =
  ConsumerCorrespondence.execution M (consumer S ρ verdict) tt ρ (initial M) verdict

private
  bind-cong : {t u : P.Calls unitᴵ X} {f g : X → P.Calls unitᴵ Y}
    → t P.≈ᶜ u → (∀ x → f x P.≈ᶜ g x) → (t >>=ᶜ f) P.≈ᶜ (u >>=ᶜ g)
  bind-cong (P.ret refl) h = h _
  bind-cong (P.call {c = ()} e) h
  bind-cong (P.coin e) h = P.coin λ b → bind-cong (e b) h
  bind-cong P.dead h = P.dead

module Synchronized {A B J} (w : Wiring A B J) (M : Automaton A) (N : Automaton B) where
  private
    Joint = productSignature A B J
    Pair = State M × State N

  activation : Task Joint → Pair → Dist-ℚ (Maybe (Output Joint) × Pair)
  activation (inj₁ t) (q , r) with choose M q t
  ... | nothing = return-ℚ (nothing , (q , r))
  ... | just (inj₁ o) = Dmap (just (inj₁ o) ,_)
    (independent (kernel M (inj₁ o) q) (receive N (find (right w) (inj₂ o)) r))
  ... | just (inj₂ h) = Dmap (nothing ,_)
    (independent (kernel M (inj₂ h) q) (return-ℚ r))
  activation (inj₂ t) (q , r) with choose N r t
  ... | nothing = return-ℚ (nothing , (q , r))
  ... | just (inj₁ o) = Dmap (just (inj₂ o) ,_)
    (independent (receive M (find (left w) (inj₂ o)) q) (kernel N (inj₁ o) r))
  ... | just (inj₂ h) = Dmap (nothing ,_)
    (independent (return-ℚ q) (kernel N (inj₂ h) r))

  synchronized : P.Protocol unitᴵ (Tick Joint)
  synchronized = record { St = Pair ; init = initial M , initial N
    ; step = λ qr t _ → coins (rationalCoins (Dmap swap (activation t qr))) }

  activation-compatibility : ∀ t qr → activation t qr ≡ tick (product w M N) t qr
  activation-compatibility (inj₁ t) (q , r) with choose M q t
  ... | nothing = refl
  ... | just (inj₁ o) = refl
  ... | just (inj₂ h) = refl
  activation-compatibility (inj₂ t) (q , r) with choose N r t
  ... | nothing = refl
  ... | just (inj₁ o) = refl
  ... | just (inj₂ h) = refl

  receive-left : ∀ t q r o i → choose M q t ≡ just (inj₁ o)
    → find (right w) (inj₂ o) ≡ just i
    → activation (inj₁ t) (q , r) ≡ Dmap (just (inj₁ o) ,_)
      (independent (kernel M (inj₁ o) q) (input N i r))
  receive-left t q r o i chosen connected rewrite chosen | connected = refl

  receive-right : ∀ t q r o i → choose N r t ≡ just (inj₁ o)
    → find (left w) (inj₂ o) ≡ just i
    → activation (inj₂ t) (q , r) ≡ Dmap (just (inj₂ o) ,_)
      (independent (input M i q) (kernel N (inj₁ o) r))
  receive-right t q r o i chosen connected rewrite chosen | connected = refl

  step-compatibility : ∀ qr t → P.step synchronized qr t tt
    ≡ P.step (resource (product w M N)) qr t tt
  step-compatibility qr t = cong (coins ∘ rationalCoins ∘ Dmap swap) (activation-compatibility t qr)

  tree-compatibility : ∀ ρ qr → scheduledTree Joint synchronized ρ qr P.≈ᶜ runTree (product w M N) ρ qr
  tree-compatibility [] qr = P.ret refl
  tree-compatibility (t ∷ ρ) qr = bind-cong
    (subst (λ u → P.step synchronized qr t tt P.≈ᶜ u) (step-compatibility qr t) P.≈ᶜ-refl)
    (λ (qr′ , o) → P.mapᶜ-cong (prepend o) (tree-compatibility ρ qr′))

  native : Schedule Joint → Pair → Dist⊥ (List (Output Joint))
  native ρ qr = evalC (scheduledTree Joint synchronized ρ qr)

  schedule-compatibility : ∀ ρ qr → native ρ qr ≈Mℚ (runFrom (product w M N) ρ qr >>=ᴹ return⊥)
  schedule-compatibility ρ qr ξ = trans (evalC-cong (tree-compatibility ρ qr) ξ)
    (run-agreement (product w M N) ρ qr ξ)
