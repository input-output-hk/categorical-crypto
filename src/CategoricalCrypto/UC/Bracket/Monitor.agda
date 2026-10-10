{-# OPTIONS --safe --without-K --guardedness #-}

-- The monitor `e A` — the identity SSP protocol, compiled — and what it does
-- to well-bracketed machines (`docs/uc-setup-ssp.md` §4.3, C5).  `e` forwards
-- a query as a call on the same channel and the reply on that channel back up,
-- and is `botₚ` on anything else.
--
-- A `Relay` is any machine of that shape up to relabellings `dn`/`up`: at rest
-- it forwards a query, answers the reply on the called channel, and is at rest
-- again — `e`, a compiled relabelling `⌜ m ⌝` whose `up` recovers the queried
-- channel, a wire, and their tensors.  Below a relay, a well-bracketed closure
-- answers every query within the activation, on the queried channel (`W`), so
-- the relay is the closure relabelled (`absorb`); `monitor-invisible` is `e`
-- among ancillas.  Above a tensor of two compiled protocols, `e` lets one factor
-- be active at a time, so the direct tensor is the compiled one (`e∘⊗ʷ`,
-- `⊗-monitor`).
--
-- Both are `Protocol.Machine.Compose`'s technique: each side is a simulation
-- out of a third machine of reachable configurations.  For `absorb` that is the
-- closure with its idle invariant attached (`Dp.Attach`), read through the
-- composite's trace in two passes (`Collapse.Loop`).
--
-- Interfaces are passed explicitly, as in `UC.Bracket.Tensor`; left to
-- inference here they exhaust a 3 GiB heap.

open import Categories.Category

open import Class.DecEq
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Attach
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter using (contᵢ)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Compose
open import CategoricalCrypto.Protocol.Machine.Resp using (morphism-sim)
open import CategoricalCrypto.SSP.Compile
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.UC.Bracket
open import CategoricalCrypto.UC.Bracket.Category
open import CategoricalCrypto.UC.Bracket.Tensor
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Pure as Pure
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.Protocol as Flat

module CategoricalCrypto.UC.Bracket.Monitor where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module 𝒫  = Category 𝒫ᴵ

private variable
  A B C D Y Z : Iface
  K K′ L L′ : Set

------------------------------------------------------------------------
-- Compiled protocols and the monitor

protᴹ : Protocol A B → Proc (flat A) (flat B)
protᴹ {A} P = morphism (toProtocol ⦃ Ch-dec A ⦄ P)

-- The continuation a compiled call on `c` waits on (`SSP.Compile.toCalls`).
resume : (A : Iface) {X : Set} {c : Ch A} → (R A c → Calls A X) → Σ (Ch A) (R A) → Flat.Calls (flat A) X
resume A {c = c} k (c′ , r) = reply {A} ⦃ Ch-dec A ⦄ (_≟_ ⦃ Ch-dec A ⦄ c′ c) r λ r → toCalls ⦃ Ch-dec A ⦄ (k r)

e : (A : Iface) → Proc (flat A) (flat A)
e A = protᴹ (wireᵖ {A})

e-W : W {A} {A} (e A)
e-W {A} = morphism-W ⦃ Ch-dec A ⦄ wireᵖ

e∘prot : (P : Protocol A B)
       → 𝒫._≈_ {flat A} {flat B} (𝒫._∘_ {flat A} {flat B} {flat B} (e B) (protᴹ P)) (protᴹ P)
e∘prot {A} {B} P =
       S.⟺ᴹ (morphismCompose (toProtocol ⦃ Ch-dec B ⦄ wireᵖ) (toProtocol ⦃ Ch-dec A ⦄ P))
  S.○ᴹ S.⟺ᴹ (morphism-sim (toProtocol-∘ ⦃ Ch-dec A ⦄ ⦃ Ch-dec B ⦄ wireᵖ P))
  S.○ᴹ morphism-sim (toProtocol-sim ⦃ Ch-dec A ⦄ (wireᵖ-identityˡ P))

e-idem : 𝒫._≈_ {flat A} {flat A} (𝒫._∘_ {flat A} {flat A} {flat A} (e A) (e A)) (e A)
e-idem {A} = e∘prot {A} {A} wireᵖ

------------------------------------------------------------------------
-- Relays

record Relay {X X′ : Iface} (H : Proc (flat X) (flat X′))
             (dn : Σ (Ch X′) (Q X′) → Σ (Ch X) (Q X)) (up : Σ (Ch X) (R X) → Σ (Ch X′) (R X′)) : Set where
  field
    rest       : MC.St H
    rest-point : MC.point (MC.state H) tt ≈ₚ returnₚ rest
    held       : Σ (Ch X′) (Q X′) → MC.St H
    forward    : ∀ q → MC.step H (rest , inj₂ q) ≈ₚ returnₚ (held q , inj₁ (dn q))
    back       : ∀ q (r : R X (proj₁ (dn q)))
               → MC.step H (held q , inj₁ (proj₁ (dn q) , r)) ≈ₚ returnₚ (rest , inj₂ (up (proj₁ (dn q) , r)))

-- Relabellings that agree pointwise give the same relay, hence by `absorb` the
-- same sandwich: a wire and a compiled relabelling need not agree definitionally.
Relay-≗ : ∀ {H : Proc (flat A) (flat B)} {dn dn′ up up′} → (∀ q → dn q ≡ dn′ q) → (∀ r → up r ≡ up′ r)
        → Relay {A} {B} H dn up → Relay {A} {B} H dn′ up′
Relay-≗ {A} {H = H} {up = up} dn≗ up≗ h = record
  { rest = rest ; rest-point = rest-point ; held = held
  ; forward = λ q → forward q ⟨≈⟩ ret≡ (cong (λ z → held q , inj₁ z) (dn≗ q))
  ; back = λ q r →
      subst (λ x → ∀ (r : R A (proj₁ x)) → MC.step H (held q , inj₁ (proj₁ x , r))
                                           ≈ₚ returnₚ (rest , inj₂ (up (proj₁ x , r))))
            (dn≗ q) (back q) r
      ⟨≈⟩ ret≡ (cong (λ z → rest , inj₂ z) (up≗ _)) }
  where open Relay h

id-Relay : Relay {A} {A} (𝒫.id {flat A}) (λ q → q) (λ r → r)
id-Relay = record
  { rest = tt ; rest-point = ≈refl ; held = λ _ → tt
  ; forward = λ q → Pure.swapᴵ (tt , inj₂ q) ; back = λ q r → Pure.swapᴵ (tt , inj₁ (proj₁ q , r)) }

wire-Relay : {up : Σ (Ch A) (R A) → Σ (Ch B) (R B)} {down : Σ (Ch B) (Q B) → Σ (Ch A) (Q A)}
           → Relay {A} {B} (wireᴹ up down) down up
wire-Relay = record
  { rest = tt ; rest-point = ≈refl ; held = λ _ → tt ; forward = λ _ → ≈refl ; back = λ _ _ → ≈refl }

-- A compiled relabelling `⌜ m ⌝` is a relay wherever `up` reads the queried
-- channel back off the called one.
module _ (m : A ⇒ᴵ B) where

  ⌜⌝-held : Ch A → MSt (toProtocol ⦃ Ch-dec B ⦄ ⌜ m ⌝)
  ⌜⌝-held c = wait (resume B {c = ch m c} λ r → ret (init ⌜ m ⌝ , c , re m r))

  ⌜⌝-back : ∀ c r → MC.step (protᴹ ⌜ m ⌝) (⌜⌝-held c , inj₁ (ch m c , r))
                    ≈ₚ returnₚ (idle (init ⌜ m ⌝) , inj₂ (c , re m r))
  ⌜⌝-back c r = ≡⇒≈ₚ (cong (drive (toProtocol ⦃ Ch-dec B ⦄ ⌜ m ⌝)) (reply-refl {B} ⦃ Ch-dec B ⦄ r _))

  ⌜⌝-Relay : {up : Σ (Ch B) (R B) → Σ (Ch A) (R A)} → (∀ c r → up (ch m c , r) ≡ (c , re m r))
           → Relay {B} {A} (protᴹ ⌜ m ⌝) (λ (c , q) → ch m c , qu m q) up
  ⌜⌝-Relay up-ch = record
    { rest = idle (init ⌜ m ⌝) ; rest-point = ≈refl ; held = λ (c , _) → ⌜⌝-held c ; forward = λ _ → ≈refl
    ; back = λ (c , _) r → ⌜⌝-back c r ⟨≈⟩ ret≡ (cong (λ z → idle (init ⌜ m ⌝) , inj₂ z) (sym (up-ch c r))) }

e-Relay : Relay {A} {A} (e A) (λ q → q) (λ r → r)
e-Relay {A} = ⌜⌝-Relay {A} {A} idᴵ λ _ _ → refl

infixr 10 _⊗Σ_

_⊗Σ_ : {F : K → Set} {F′ : K′ → Set} {G : L → Set} {G′ : L′ → Set}
     → (Σ K F → Σ K′ F′) → (Σ L G → Σ L′ G′) → Σ (K ⊎ L) [ F , G ]′ → Σ (K′ ⊎ L′) [ F′ , G′ ]′
(f ⊗Σ g) (inj₁ k , u) = joinΣ (inj₁ (f (k , u)))
(f ⊗Σ g) (inj₂ l , v) = joinΣ (inj₂ (g (l , v)))

module _ {H₁ : Proc (flat A) (flat B)} {H₂ : Proc (flat C) (flat D)} {dn₁ up₁ dn₂ up₂}
         (h₁ : Relay {A} {B} H₁ dn₁ up₁) (h₂ : Relay {C} {D} H₂ dn₂ up₂) where

  private
    module H₁ = Relay h₁
    module H₂ = Relay h₂

  Relay-⊗ : Relay {A ⊗ᴵ C} {B ⊗ᴵ D} (_⊗ʷ_ {A} {B} {C} {D} H₁ H₂) (dn₁ ⊗Σ dn₂) (up₁ ⊗Σ up₂)
  Relay-⊗ = record
    { rest       = H₁.rest , H₂.rest
    ; rest-point = Pw.point-⊛ (MC.state H₁) (MC.state H₂) tt
                   ⟨≈⟩ bindˣ H₁.rest-point ⟨≈⟩ >>=ₚ-identityˡ H₁.rest _
                   ⟨≈⟩ bindˣ H₂.rest-point ⟨≈⟩ >>=ₚ-identityˡ H₂.rest _
    ; held       = λ where
        (inj₁ b , q) → H₁.held (b , q) , H₂.rest
        (inj₂ d , q) → H₁.rest , H₂.held (d , q)
    ; forward    = λ where
        (inj₁ b , q) → map-arg (pairˡ H₂.rest) (H₁.forward (b , q)) ⟨≈⟩ >>=ₚ-identityˡ _ _
        (inj₂ d , q) → map-arg (pairʳ H₁.rest) (H₂.forward (d , q)) ⟨≈⟩ >>=ₚ-identityˡ _ _
    ; back       = λ where
        (inj₁ b , q) r → map-arg (pairˡ H₂.rest) (H₁.back (b , q) r) ⟨≈⟩ >>=ₚ-identityˡ _ _
        (inj₂ d , q) r → map-arg (pairʳ H₁.rest) (H₂.back (d , q) r) ⟨≈⟩ >>=ₚ-identityˡ _ _
    }

-- A relay among the ancillas of a context (`docs/uc-setup-ssp.md` §4.2).
ancilla-Relay : ∀ {H : Proc (flat A) (flat B)} {dn up} → Relay {A} {B} H dn up
              → Relay {(Y ⊗ᴵ A) ⊗ᴵ Z} {(Y ⊗ᴵ B) ⊗ᴵ Z}
                  (_⊗ʷ_ {Y ⊗ᴵ A} {Y ⊗ᴵ B} {Z} {Z} (_⊗ʷ_ {Y} {Y} {A} {B} (𝒫.id {flat Y}) H) (𝒫.id {flat Z}))
                  (((λ q → q) ⊗Σ dn) ⊗Σ λ q → q) (((λ r → r) ⊗Σ up) ⊗Σ λ r → r)
ancilla-Relay {Y = Y} {Z = Z} h = Relay-⊗ (Relay-⊗ (id-Relay {Y}) h) (id-Relay {Z})

------------------------------------------------------------------------
-- Absorption

module _ {X X′ : Iface} {H : Proc (flat X) (flat X′)} {dn up} (h : Relay {X} {X′} H dn up)
         {c : Proc (flat unitᴵ) (flat X)} (wc : W {unitᴵ} {X} c) where

  private
    module H = Relay h
    module C = W wc

    St⁺ : Set
    St⁺ = Σ (MC.St c) λ s → C.I s idle

    Out : Set
    Out = Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch X′) (R X′)

    Move : Ch X → Set
    Move b = Σ (MC.St c × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch X) (R X))) (Legal C.I (serving b))

    -- With nothing below, a closure's legal move is the answer.
    settle : ∀ {b} → Move b → St⁺ × Out
    settle ((_ , _) , _ , call {a = ()} , _)
    settle ((s′ , y) , _ , answer , i′) = (s′ , i′) , Sum.map (λ a → a) up y

    step⁺ : St⁺ × (Σ (Ch unitᴵ) (R unitᴵ) ⊎ Σ (Ch X′) (Q X′)) → Dₚ (St⁺ × Out)
    step⁺ (_ , inj₁ (() , _))
    step⁺ ((s , i) , inj₂ q) = mapₚ settle (attach (MC.step c (s , inj₂ (dn q))) (C.I-step i query))

    M⁺ : Proc (flat unitᴵ) (flat X′)
    M⁺ = MC.mk record { obj = St⁺ ; point = λ _ → attach (MC.point (MC.state c) tt) C.I-init } step⁺

    settled : ∀ {b} (x : Move b)
            → Pw.padϕ proj₁ (settle x) ≈ₚ returnₚ (proj₁ (proj₁ x) , Sum.map (λ a → a) up (proj₂ (proj₁ x)))
    settled ((_ , _) , _ , call {a = ()} , _)
    settled ((_ , _) , _ , answer , _) = ≈refl

    to-sandwich : M⁺ S.≲ sandwichᴹ c (Sum.map (λ a → a) dn) (Sum.map (λ a → a) up)
    to-sandwich = Pw.simFn proj₁ (λ _ → attach-proj (MC.point (MC.state c) tt) C.I-init) λ where
      (_ , inj₁ (() , _))
      ((s , i) , inj₂ q) →
        let d = MC.step c (s , inj₂ (dn q)) ; p = C.I-step i query in
        bind-map (attach d p) settle (Pw.padϕ proj₁) ⟨≈⟩ bindᶠ settled ⟨≈⟩ ≈sym (>>=ₚ-attach d p _)

    open Col.Loop (Σ (Ch unitᴵ) (R unitᴵ) ⊎ Σ (Ch X′) (Q X′)) Out (Σ (Ch X) (Q X) ⊎ Σ (Ch X) (R X))
                  (Col.Sᴳ H c) (Col.kᴳ H c)

    ι : St⁺ → MC.St H × MC.St c
    ι (s , _) = H.rest , s

    pass₂ : (q : Σ (Ch X′) (Q X′)) (x : Move (proj₁ (dn q)))
          → contᵢ body ((H.held q , proj₁ (proj₁ x)) , Col.outᶠ (proj₂ (proj₁ x))) ≈ₚ Pw.padϕ ι (settle x)
    pass₂ q ((_ , _) , _ , call {a = ()} , _)
    pass₂ q ((s′ , inj₂ (b , r)) , _ , answer , _) =
      loop-pass (H.held q , s′) (inj₂ (b , r)) (H.rest , s′) (inj₁ (inj₂ (up (b , r))))
        (bindˣ (H.back q r) ⟨≈⟩ >>=ₚ-identityˡ (H.rest , inj₂ (up (b , r))) _)

    composite-step : (s : MC.St c) (i : C.I s idle) (q : Σ (Ch X′) (Q X′))
                   → (step⁺ ((s , i) , inj₂ q) >>=ₚ Pw.padϕ ι) ≈ₚ MC.step tracedᴹ ((H.rest , s) , inj₂ q)
    composite-step s i q =
          bind-map (attach d p) settle (Pw.padϕ ι)
      ⟨≈⟩ ≈sym (bindᶠ (pass₂ q))
      ⟨≈⟩ ≈sym (>>=ₚ-attach d p λ r → contᵢ body (pass₁ r))
      ⟨≈⟩ ≈sym (bind-map d pass₁ (contᵢ body))
      ⟨≈⟩ ≈sym (loop-fix (H.held q , s) (inj₁ (dn q)))
      ⟨≈⟩ ≈sym (bindˣ (bindˣ (H.forward q) ⟨≈⟩ >>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body))
      ⟨≈⟩ ≈sym (step-red (H.rest , s) (inj₂ q))
      where
      d = MC.step c (s , inj₂ (dn q))
      p = C.I-step i query

      pass₁ : MC.St c × (Σ (Ch unitᴵ) (Q unitᴵ) ⊎ Σ (Ch X) (R X))
            → (MC.St H × MC.St c) × (Out ⊎ (Σ (Ch X) (Q X) ⊎ Σ (Ch X) (R X)))
      pass₁ r = (H.held q , proj₁ r) , Col.outᶠ (proj₂ r)

    to-composite : M⁺ S.≲ _⊙_ {B = X} {C = X′} {A = unitᴵ} H c
    to-composite = Pw.simFn ι
      (λ x → ≈sym (>>=ₚ-attach (MC.point (MC.state c) tt) C.I-init λ s → returnₚ (H.rest , s))
             ⟨≈⟩ ≈sym (>>=ₚ-identityˡ H.rest λ a → MC.point (MC.state c) x >>=ₚ λ s → returnₚ (a , s))
             ⟨≈⟩ ≈sym (bindˣ H.rest-point)
             ⟨≈⟩ ≈sym (Pw.point-⊛ (MC.state H) (MC.state c) x))
      λ where
        (_ , inj₁ (() , _))
        ((s , i) , inj₂ q) → composite-step s i q

  absorb : 𝒫._≈_ {flat unitᴵ} {flat X′} (𝒫._∘_ {flat unitᴵ} {flat X} {flat X′} H c)
             (sandwichᴹ c (Sum.map (λ a → a) dn) (Sum.map (λ a → a) up))
  absorb = S.⟺ᴹ (⊙≈∘ {B = X} {C = X′} {A = unitᴵ} H c) S.○ᴹ S.≲⇒≈ᴹ˘ to-composite S.○ᴹ S.≲⇒≈ᴹ to-sandwich

monitor-invisible : (c : Proc (flat unitᴵ) (flat ((Y ⊗ᴵ A) ⊗ᴵ Z))) → W {unitᴵ} {(Y ⊗ᴵ A) ⊗ᴵ Z} c
                  → 𝒫._≈_ {flat unitᴵ} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)}
                      (𝒫._∘_ {flat unitᴵ} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)} {flat ((Y ⊗ᴵ A) ⊗ᴵ Z)}
                        (_⊗ʷ_ {Y ⊗ᴵ A} {Y ⊗ᴵ A} {Z} {Z} (_⊗ʷ_ {Y} {Y} {A} {A} (𝒫.id {flat Y}) (e A)) (𝒫.id {flat Z}))
                        c)
                      c
monitor-invisible {Y} {A} {Z} c wc =
  absorb (ancilla-Relay {Y = Y} {Z = Z} (e-Relay {A})) wc
  S.○ᴹ sandwich-id c _ _ (λ where
                            (inj₁ _)                    → refl
                            (inj₂ (inj₁ (inj₁ _) , _)) → refl
                            (inj₂ (inj₁ (inj₂ _) , _)) → refl
                            (inj₂ (inj₂ _ , _))         → refl)
                         (λ where
                            (inj₁ _)                    → refl
                            (inj₂ (inj₁ (inj₁ _) , _)) → refl
                            (inj₂ (inj₁ (inj₂ _) , _)) → refl
                            (inj₂ (inj₂ _ , _))         → refl)

------------------------------------------------------------------------
-- The monitored tensor

private
  -- `reply` at the machine level.
  check : {F : K → Set} {k k′ : K} {Z : Set} → Dec (k′ ≡ k) → F k′ → (F k → Dₚ Z) → Dₚ Z
  check (yes refl) r f = f r
  check (no _)     _ _ = botₚ

module _ (P : Protocol A B) (P′ : Protocol C D) where

  private
    T : Proc (flat (A ⊗ᴵ C)) (flat (B ⊗ᴵ D))
    T = _⊗ʷ_ {A} {B} {C} {D} (protᴹ P) (protᴹ P′)

    Out : Set
    Out = Σ (Ch (A ⊗ᴵ C)) (Q (A ⊗ᴵ C)) ⊎ Σ (Ch (B ⊗ᴵ D)) (R (B ⊗ᴵ D))

    -- The configurations `e (B ⊗ᴵ D) ∘ T` reaches: both factors at rest, or one
    -- waiting on its call while the other rests (`e` refuses a second query).
    data TSt : Set where
      both  : St P → St P′ → TSt
      waitˡ : (b : Ch B) (a : Ch A) → (R A a → Calls A (St P × R B b)) → St P′ → TSt
      waitʳ : St P → (d : Ch D) (c : Ch C) → (R C c → Calls C (St P′ × R D d)) → TSt

    driveˡ : (b : Ch B) → St P′ → Calls A (St P × R B b) → Dₚ (TSt × Out)
    driveˡ b t (ret (s , r)) = returnₚ (both s t , inj₂ (inj₁ b , r))
    driveˡ b t (call a q k)  = returnₚ (waitˡ b a k t , inj₁ (inj₁ a , q))
    driveˡ b t (coin μ k)    = coinₚ μ >>=ₚ λ x → driveˡ b t (k x)
    driveˡ b t dead          = botₚ

    driveʳ : St P → (d : Ch D) → Calls C (St P′ × R D d) → Dₚ (TSt × Out)
    driveʳ s d (ret (t , r)) = returnₚ (both s t , inj₂ (inj₂ d , r))
    driveʳ s d (call c q k)  = returnₚ (waitʳ s d c k , inj₁ (inj₂ c , q))
    driveʳ s d (coin μ k)    = coinₚ μ >>=ₚ λ x → driveʳ s d (k x)
    driveʳ s d dead          = botₚ

    stepᵗ : TSt × (Σ (Ch (A ⊗ᴵ C)) (R (A ⊗ᴵ C)) ⊎ Σ (Ch (B ⊗ᴵ D)) (Q (B ⊗ᴵ D))) → Dₚ (TSt × Out)
    stepᵗ (both s t , inj₂ (inj₁ b , q))       = driveˡ b t (step P s b q)
    stepᵗ (both s t , inj₂ (inj₂ d , q))       = driveʳ s d (step P′ t d q)
    stepᵗ (both _ _ , inj₁ _)                  = botₚ
    stepᵗ (waitˡ b a k t , inj₁ (inj₁ a′ , r)) = check {F = R A} (_≟_ ⦃ Ch-dec A ⦄ a′ a) r λ r → driveˡ b t (k r)
    stepᵗ (waitˡ _ _ _ _ , inj₁ (inj₂ _ , _))  = botₚ
    stepᵗ (waitˡ _ _ _ _ , inj₂ _)             = botₚ
    stepᵗ (waitʳ s d c k , inj₁ (inj₂ c′ , r)) = check {F = R C} (_≟_ ⦃ Ch-dec C ⦄ c′ c) r λ r → driveʳ s d (k r)
    stepᵗ (waitʳ _ _ _ _ , inj₁ (inj₁ _ , _))  = botₚ
    stepᵗ (waitʳ _ _ _ _ , inj₂ _)             = botₚ

    machineᵗ : Proc (flat (A ⊗ᴵ C)) (flat (B ⊗ᴵ D))
    machineᵗ = MC.mk record { obj = TSt ; point = λ _ → returnₚ (both (init P) (init P′)) } stepᵗ

    πᴿ : TSt → MSt (toProtocol ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (P ⊗ᵖ P′))
    πᴿ (both s t)      = idle (s , t)
    πᴿ (waitˡ b a k t) = wait (resume (A ⊗ᴵ C) {c = inj₁ a} λ r →
                           mapᶜ (map₂ (inj₁ b ,_)) (mapᶜ (map₁ (_, t)) (reindex (ι₁ {B = C}) (k r))))
    πᴿ (waitʳ s d c k) = wait (resume (A ⊗ᴵ C) {c = inj₂ c} λ r →
                           mapᶜ (map₂ (inj₂ d ,_)) (mapᶜ (map₁ (s ,_)) (reindex (ι₂ {A = A}) (k r))))

    rhs-driveˡ : (b : Ch B) (t : St P′) (u : Calls A (St P × R B b))
               → (driveˡ b t u >>=ₚ Pw.padϕ πᴿ)
                 ≈ₚ drive (toProtocol ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (P ⊗ᵖ P′)) (toCalls ⦃ Ch-dec (A ⊗ᴵ C) ⦄
                      (mapᶜ (map₂ (inj₁ b ,_)) (mapᶜ (map₁ (_, t)) (reindex (ι₁ {B = C}) u))))
    rhs-driveˡ b t (ret _)      = >>=ₚ-identityˡ _ _
    rhs-driveˡ b t (call _ _ _) = >>=ₚ-identityˡ _ _
    rhs-driveˡ b t (coin μ k)   = >>=ₚ-assoc (coinₚ μ) _ _ ⟨≈⟩ bindᶠ λ x → rhs-driveˡ b t (k x)
    rhs-driveˡ b t dead         = bot-bind-≈ₚ _

    rhs-driveʳ : (s : St P) (d : Ch D) (u : Calls C (St P′ × R D d))
               → (driveʳ s d u >>=ₚ Pw.padϕ πᴿ)
                 ≈ₚ drive (toProtocol ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (P ⊗ᵖ P′)) (toCalls ⦃ Ch-dec (A ⊗ᴵ C) ⦄
                      (mapᶜ (map₂ (inj₂ d ,_)) (mapᶜ (map₁ (s ,_)) (reindex (ι₂ {A = A}) u))))
    rhs-driveʳ s d (ret _)      = >>=ₚ-identityˡ _ _
    rhs-driveʳ s d (call _ _ _) = >>=ₚ-identityˡ _ _
    rhs-driveʳ s d (coin μ k)   = >>=ₚ-assoc (coinₚ μ) _ _ ⟨≈⟩ bindᶠ λ x → rhs-driveʳ s d (k x)
    rhs-driveʳ s d dead         = bot-bind-≈ₚ _

    -- The compiled tensor compares reply channels on `A ⊗ᴵ C`; `≡-dec` reduces
    -- that to the factor's comparison under `map′`.
    rhs-retˡ : (b : Ch B) (a : Ch A) (k : R A a → Calls A (St P × R B b)) (t : St P′) {a′ : Ch A}
               (d : Dec (a′ ≡ a)) (r : R A a′)
             → (check {F = R A} d r (λ r → driveˡ b t (k r)) >>=ₚ Pw.padϕ πᴿ)
               ≈ₚ drive (toProtocol ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (P ⊗ᵖ P′))
                    (reply {A ⊗ᴵ C} ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (map′ (cong inj₁) inj₁-injective d) r λ r →
                       toCalls ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (mapᶜ (map₂ (inj₁ b ,_)) (mapᶜ (map₁ (_, t)) (reindex (ι₁ {B = C}) (k r)))))
    rhs-retˡ b a k t (yes refl) r = rhs-driveˡ b t (k r)
    rhs-retˡ b a k t (no _)     r = bot-bind-≈ₚ _

    rhs-retʳ : (s : St P) (d : Ch D) (c : Ch C) (k : R C c → Calls C (St P′ × R D d)) {c′ : Ch C}
               (dc : Dec (c′ ≡ c)) (r : R C c′)
             → (check {F = R C} dc r (λ r → driveʳ s d (k r)) >>=ₚ Pw.padϕ πᴿ)
               ≈ₚ drive (toProtocol ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (P ⊗ᵖ P′))
                    (reply {A ⊗ᴵ C} ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (map′ (cong inj₂) inj₂-injective dc) r λ r →
                       toCalls ⦃ Ch-dec (A ⊗ᴵ C) ⦄ (mapᶜ (map₂ (inj₂ d ,_)) (mapᶜ (map₁ (s ,_)) (reindex (ι₂ {A = A}) (k r)))))
    rhs-retʳ s d c k (yes refl) r = rhs-driveʳ s d (k r)
    rhs-retʳ s d c k (no _)     r = bot-bind-≈ₚ _

    to-compiled : machineᵗ S.≲ protᴹ (P ⊗ᵖ P′)
    to-compiled = Pw.simFn πᴿ (λ _ → >>=ₚ-identityˡ _ _) λ where
      (both s t , inj₂ (inj₁ b , q))       → rhs-driveˡ b t (step P s b q)
      (both s t , inj₂ (inj₂ d , q))       → rhs-driveʳ s d (step P′ t d q)
      (both _ _ , inj₁ _)                  → bot-bind-≈ₚ _
      (waitˡ b a k t , inj₁ (inj₁ a′ , r)) → rhs-retˡ b a k t (_≟_ ⦃ Ch-dec A ⦄ a′ a) r
      (waitˡ _ _ _ _ , inj₁ (inj₂ _ , _))  → bot-bind-≈ₚ _
      (waitˡ _ _ _ _ , inj₂ _)             → bot-bind-≈ₚ _
      (waitʳ s d c k , inj₁ (inj₂ c′ , r)) → rhs-retʳ s d c k (_≟_ ⦃ Ch-dec C ⦄ c′ c) r
      (waitʳ _ _ _ _ , inj₁ (inj₁ _ , _))  → bot-bind-≈ₚ _
      (waitʳ _ _ _ _ , inj₂ _)             → bot-bind-≈ₚ _

    top : Ch (B ⊗ᴵ D) → MC.St (e (B ⊗ᴵ D))
    top = ⌜⌝-held {B ⊗ᴵ D} {B ⊗ᴵ D} idᴵ

    πᴸ : TSt → MC.St (e (B ⊗ᴵ D)) × MC.St T
    πᴸ (both s t)      = idle _ , idle s , idle t
    πᴸ (waitˡ b a k t) = top (inj₁ b) , wait (resume A {c = a} λ r → mapᶜ (map₂ (b ,_)) (k r)) , idle t
    πᴸ (waitʳ s d c k) = top (inj₂ d) , idle s , wait (resume C {c = c} λ r → mapᶜ (map₂ (d ,_)) (k r))

    open Col.Loop (Σ (Ch (A ⊗ᴵ C)) (R (A ⊗ᴵ C)) ⊎ Σ (Ch (B ⊗ᴵ D)) (Q (B ⊗ᴵ D))) Out
                  (Σ (Ch (B ⊗ᴵ D)) (Q (B ⊗ᴵ D)) ⊎ Σ (Ch (B ⊗ᴵ D)) (R (B ⊗ᴵ D)))
                  (Col.Sᴳ (e (B ⊗ᴵ D)) T) (Col.kᴳ (e (B ⊗ᴵ D)) T)

    -- The rest of an activation once `T` has emitted, the monitor holding `ch`.
    rest-of : Ch (B ⊗ᴵ D) → Dₚ (MC.St T × Out) → Dₚ ((MC.St (e (B ⊗ᴵ D)) × MC.St T) × Out)
    rest-of ch u = (u >>=ₚ λ r → returnₚ ((top ch , proj₁ r) , Col.outᶠ (proj₂ r))) >>=ₚ contᵢ body

    enter : (u : MC.St T) (y : Σ (Ch (B ⊗ᴵ D)) (Q (B ⊗ᴵ D)))
          → MC.step tracedᴹ ((idle _ , u) , inj₂ y) ≈ₚ rest-of (proj₁ y) (MC.step T (u , inj₂ y))
    enter u y =
          step-red (idle _ , u) (inj₂ y)
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ _ _)
      ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body)
      ⟨≈⟩ loop-fix (top (proj₁ y) , u) (inj₁ y)

    refused : (st : MC.St (e (B ⊗ᴵ D)) × MC.St T) (x : Σ (Ch (A ⊗ᴵ C)) (R (A ⊗ᴵ C)))
            → MC.step T (proj₂ st , inj₁ x) ≈ₚ botₚ → MC.step tracedᴹ (st , inj₁ x) ≈ₚ botₚ
    refused st x eq = step-red st (inj₁ x) ⟨≈⟩ bindˣ (bindˣ eq ⟨≈⟩ bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _

    -- The monitor refuses a second query.
    busy : (ch : Ch (B ⊗ᴵ D)) (u : MC.St T) (y : Σ (Ch (B ⊗ᴵ D)) (Q (B ⊗ᴵ D)))
         → MC.step tracedᴹ ((top ch , u) , inj₂ y) ≈ₚ botₚ
    busy ch u y = step-red (top ch , u) (inj₂ y) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _

    lhs-driveˡ : (b : Ch B) (t : St P′) (u : Calls A (St P × R B b))
               → (driveˡ b t u >>=ₚ Pw.padϕ πᴸ)
                 ≈ₚ rest-of (inj₁ b) (mapₚ (pairˡ (idle t))
                      (drive (toProtocol ⦃ Ch-dec A ⦄ P) (toCalls ⦃ Ch-dec A ⦄ (mapᶜ (map₂ (b ,_)) u))))
    lhs-driveˡ b t (ret (s′ , r)) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym ( bindˣ (bindˣ (>>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body)
               ⟨≈⟩ loop-pass (top (inj₁ b) , idle s′ , idle t) (inj₂ (inj₁ b , r)) (idle _ , idle s′ , idle t)
                     (inj₁ (inj₂ (inj₁ b , r)))
                     (bindˣ (⌜⌝-back {B ⊗ᴵ D} {B ⊗ᴵ D} idᴵ (inj₁ b) r) ⟨≈⟩ >>=ₚ-identityˡ _ _))
    lhs-driveˡ b t (call _ _ _) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym (bindˣ (bindˣ (>>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body))
    lhs-driveˡ b t (coin μ k) =
          >>=ₚ-assoc (coinₚ μ) _ _
      ⟨≈⟩ bindᶠ (λ x → lhs-driveˡ b t (k x))
      ⟨≈⟩ ≈sym (bindˣ (bindˣ (map-bind (coinₚ μ) _ _) ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ _) ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ _)
    lhs-driveˡ b t dead =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bindˣ (bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _)

    lhs-driveʳ : (s : St P) (d : Ch D) (u : Calls C (St P′ × R D d))
               → (driveʳ s d u >>=ₚ Pw.padϕ πᴸ)
                 ≈ₚ rest-of (inj₂ d) (mapₚ (pairʳ (idle s))
                      (drive (toProtocol ⦃ Ch-dec C ⦄ P′) (toCalls ⦃ Ch-dec C ⦄ (mapᶜ (map₂ (d ,_)) u))))
    lhs-driveʳ s d (ret (t′ , r)) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym ( bindˣ (bindˣ (>>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body)
               ⟨≈⟩ loop-pass (top (inj₂ d) , idle s , idle t′) (inj₂ (inj₂ d , r)) (idle _ , idle s , idle t′)
                     (inj₁ (inj₂ (inj₂ d , r)))
                     (bindˣ (⌜⌝-back {B ⊗ᴵ D} {B ⊗ᴵ D} idᴵ (inj₂ d) r) ⟨≈⟩ >>=ₚ-identityˡ _ _))
    lhs-driveʳ s d (call _ _ _) =
          >>=ₚ-identityˡ _ _
      ⟨≈⟩ ≈sym (bindˣ (bindˣ (>>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body))
    lhs-driveʳ s d (coin μ k) =
          >>=ₚ-assoc (coinₚ μ) _ _
      ⟨≈⟩ bindᶠ (λ x → lhs-driveʳ s d (k x))
      ⟨≈⟩ ≈sym (bindˣ (bindˣ (map-bind (coinₚ μ) _ _) ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ _) ⟨≈⟩ >>=ₚ-assoc (coinₚ μ) _ _)
    lhs-driveʳ s d dead =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bindˣ (bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _)

    lhs-retˡ : (b : Ch B) (a : Ch A) (k : R A a → Calls A (St P × R B b)) (t : St P′) {a′ : Ch A}
               (d : Dec (a′ ≡ a)) (r : R A a′)
             → (check {F = R A} d r (λ r → driveˡ b t (k r)) >>=ₚ Pw.padϕ πᴸ)
               ≈ₚ rest-of (inj₁ b) (mapₚ (pairˡ (idle t)) (drive (toProtocol ⦃ Ch-dec A ⦄ P)
                    (reply {A} ⦃ Ch-dec A ⦄ d r λ r → toCalls ⦃ Ch-dec A ⦄ (mapᶜ (map₂ (b ,_)) (k r)))))
    lhs-retˡ b a k t (yes refl) r = lhs-driveˡ b t (k r)
    lhs-retˡ b a k t (no _)     r =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bindˣ (bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _)

    lhs-retʳ : (s : St P) (d : Ch D) (c : Ch C) (k : R C c → Calls C (St P′ × R D d)) {c′ : Ch C}
               (dc : Dec (c′ ≡ c)) (r : R C c′)
             → (check {F = R C} dc r (λ r → driveʳ s d (k r)) >>=ₚ Pw.padϕ πᴸ)
               ≈ₚ rest-of (inj₂ d) (mapₚ (pairʳ (idle s)) (drive (toProtocol ⦃ Ch-dec C ⦄ P′)
                    (reply {C} ⦃ Ch-dec C ⦄ dc r λ r → toCalls ⦃ Ch-dec C ⦄ (mapᶜ (map₂ (d ,_)) (k r)))))
    lhs-retʳ s d c k (yes refl) r = lhs-driveʳ s d (k r)
    lhs-retʳ s d c k (no _)     r =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (bindˣ (bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ _)

    to-monitored : machineᵗ S.≲ _⊙_ {B = B ⊗ᴵ D} {C = B ⊗ᴵ D} {A = A ⊗ᴵ C} (e (B ⊗ᴵ D)) T
    to-monitored = Pw.simFn πᴸ
      (λ x → >>=ₚ-identityˡ _ _
             ⟨≈⟩ ≈sym ( Pw.point-⊛ (MC.state (e (B ⊗ᴵ D))) (MC.state T) x ⟨≈⟩ >>=ₚ-identityˡ _ _
                      ⟨≈⟩ bindˣ ( Pw.point-⊛ (MC.state (protᴹ P)) (MC.state (protᴹ P′)) x
                                ⟨≈⟩ >>=ₚ-identityˡ _ _ ⟨≈⟩ >>=ₚ-identityˡ _ _)
                      ⟨≈⟩ >>=ₚ-identityˡ _ _))
      λ where
        (both s t , inj₂ (inj₁ b , q)) →
          lhs-driveˡ b t (step P s b q) ⟨≈⟩ ≈sym (enter (idle s , idle t) (inj₁ b , q))
        (both s t , inj₂ (inj₂ d , q)) →
          lhs-driveʳ s d (step P′ t d q) ⟨≈⟩ ≈sym (enter (idle s , idle t) (inj₂ d , q))
        (both s t , inj₁ (inj₁ a′ , r)) →
          bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (refused (πᴸ (both s t)) (inj₁ a′ , r) (bot-bind-≈ₚ _))
        (both s t , inj₁ (inj₂ c′ , r)) →
          bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (refused (πᴸ (both s t)) (inj₂ c′ , r) (bot-bind-≈ₚ _))
        (waitˡ b a k t , inj₁ (inj₁ a′ , r)) →
          lhs-retˡ b a k t (_≟_ ⦃ Ch-dec A ⦄ a′ a) r ⟨≈⟩ ≈sym (step-red (πᴸ (waitˡ b a k t)) (inj₁ (inj₁ a′ , r)))
        (waitˡ b a k t , inj₁ (inj₂ c′ , r)) →
          bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (refused (πᴸ (waitˡ b a k t)) (inj₂ c′ , r) (bot-bind-≈ₚ _))
        (waitˡ b a k t , inj₂ y) →
          bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (busy (inj₁ b) (proj₂ (πᴸ (waitˡ b a k t))) y)
        (waitʳ s d c k , inj₁ (inj₂ c′ , r)) →
          lhs-retʳ s d c k (_≟_ ⦃ Ch-dec C ⦄ c′ c) r ⟨≈⟩ ≈sym (step-red (πᴸ (waitʳ s d c k)) (inj₁ (inj₂ c′ , r)))
        (waitʳ s d c k , inj₁ (inj₁ a′ , r)) →
          bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (refused (πᴸ (waitʳ s d c k)) (inj₁ a′ , r) (bot-bind-≈ₚ _))
        (waitʳ s d c k , inj₂ y) →
          bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (busy (inj₂ d) (proj₂ (πᴸ (waitʳ s d c k))) y)

  e∘⊗ʷ : 𝒫._≈_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)}
           (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {flat (B ⊗ᴵ D)} (e (B ⊗ᴵ D))
             (_⊗ʷ_ {A} {B} {C} {D} (protᴹ P) (protᴹ P′)))
           (protᴹ (P ⊗ᵖ P′))
  e∘⊗ʷ = S.⟺ᴹ (⊙≈∘ {B = B ⊗ᴵ D} {C = B ⊗ᴵ D} {A = A ⊗ᴵ C} (e (B ⊗ᴵ D)) T)
    S.○ᴹ S.≲⇒≈ᴹ˘ to-monitored S.○ᴹ S.≲⇒≈ᴹ to-compiled

  ⊗-monitor : 𝒫._≈_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)}
                (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {flat (B ⊗ᴵ D)} (e (B ⊗ᴵ D))
                  (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)}
                    (_⊗ʷ_ {A} {B} {C} {D} (protᴹ P) (protᴹ P′)) (e (A ⊗ᴵ C))))
                (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {flat (B ⊗ᴵ D)} (e (B ⊗ᴵ D))
                  (𝒫._∘_ {flat (A ⊗ᴵ C)} {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} (protᴹ (P ⊗ᵖ P′)) (e (A ⊗ᴵ C))))
  ⊗-monitor =
         𝒫.sym-assoc {flat (A ⊗ᴵ C)} {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {flat (B ⊗ᴵ D)}
                     {f = e (A ⊗ᴵ C)} {g = T} {h = e (B ⊗ᴵ D)}
    S.○ᴹ 𝒫.∘-resp-≈ˡ {flat (A ⊗ᴵ C)} {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {g = e (A ⊗ᴵ C)}
           (e∘⊗ʷ S.○ᴹ S.⟺ᴹ (e∘prot (P ⊗ᵖ P′)))
    S.○ᴹ 𝒫.assoc {flat (A ⊗ᴵ C)} {flat (A ⊗ᴵ C)} {flat (B ⊗ᴵ D)} {flat (B ⊗ᴵ D)}
                 {f = e (A ⊗ᴵ C)} {g = protᴹ (P ⊗ᵖ P′)} {h = e (B ⊗ᴵ D)}
