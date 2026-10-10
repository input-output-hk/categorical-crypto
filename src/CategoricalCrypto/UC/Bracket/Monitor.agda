{-# OPTIONS --safe --without-K --guardedness #-}

-- The monitor `e A` — the identity SSP protocol, compiled — and its
-- absorption into well-bracketed closures (`docs/uc-setup-ssp.md` §4.3, C5).
-- `e` forwards a query as a call on the same channel and the reply on that
-- channel back up, and is `botₚ` on anything else.  A `Relay` is any machine of
-- that shape up to relabellings `dn`/`up`: at rest it forwards a query, answers
-- the reply on the called channel, and is at rest again.  Below a relay, a
-- well-bracketed closure answers every query within the activation, on the
-- queried channel (`W`), so the relay is the closure relabelled (`absorb`);
-- relays are closed under `_⊗ʷ_` (`Relay-⊗`), whence `monitor-invisible`.
--
-- `absorb` is `Protocol.Machine.Compose`'s technique: both sides are
-- simulations out of a third machine, here the closure's states with the idle
-- invariant attached (`Dp.Attach`), read through the composite's trace in two
-- passes (`Collapse.Loop`).

open import Categories.Category

open import Class.DecEq
open import Data.Product.Base
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit.Polymorphic.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Attach
open import ProbabilisticLogic.Dp.Iter using (contᵢ)
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Compose using (morphismCompose)
open import CategoricalCrypto.Protocol.Machine.Resp
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

prot∘e : (P : Protocol A B)
       → 𝒫._≈_ {flat A} {flat B} (𝒫._∘_ {flat A} {flat A} {flat B} (protᴹ P) (e A)) (protᴹ P)
prot∘e {A} {B} P =
       S.⟺ᴹ (morphismCompose (toProtocol ⦃ Ch-dec A ⦄ P) (toProtocol ⦃ Ch-dec A ⦄ wireᵖ))
  S.○ᴹ S.⟺ᴹ (morphism-sim (toProtocol-∘ ⦃ Ch-dec A ⦄ ⦃ Ch-dec A ⦄ P wireᵖ))
  S.○ᴹ morphism-sim (toProtocol-sim ⦃ Ch-dec A ⦄ (wireᵖ-identityʳ P))

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
  ⌜⌝-held c = wait λ (b , r) →
    reply {B} ⦃ Ch-dec B ⦄ (_≟_ ⦃ Ch-dec B ⦄ b (ch m c)) r λ r → Flat.ret (init ⌜ m ⌝ , c , re m r)

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

-- A legal environment has one open query, so the other factor stays at rest.
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

    -- The second pass: the relay takes the answer back up and is at rest.
    passes : (q : Σ (Ch X′) (Q X′)) (x : Move (proj₁ (dn q)))
           → contᵢ body ((H.held q , proj₁ (proj₁ x)) , Col.outᶠ (proj₂ (proj₁ x))) ≈ₚ Pw.padϕ ι (settle x)
    passes q ((_ , _) , _ , call {a = ()} , _)
    passes q ((s′ , inj₂ (b , r)) , _ , answer , _) =
      loop-pass (H.held q , s′) (inj₂ (b , r)) (H.rest , s′) (inj₁ (inj₂ (up (b , r))))
        (bindˣ (H.back q r) ⟨≈⟩ >>=ₚ-identityˡ (H.rest , inj₂ (up (b , r))) _)

    composite-step : (s : MC.St c) (i : C.I s idle) (q : Σ (Ch X′) (Q X′))
                   → (step⁺ ((s , i) , inj₂ q) >>=ₚ Pw.padϕ ι) ≈ₚ MC.step tracedᴹ ((H.rest , s) , inj₂ q)
    composite-step s i q =
          bind-map (attach d p) settle (Pw.padϕ ι)
      ⟨≈⟩ ≈sym (bindᶠ (passes q))
      ⟨≈⟩ ≈sym (>>=ₚ-attach d p λ r → contᵢ body (pass₁ r))
      ⟨≈⟩ ≈sym (bind-map d pass₁ (contᵢ body))
      ⟨≈⟩ ≈sym (loop-fix (H.held q , s) (inj₁ (dn q)))
      ⟨≈⟩ ≈sym (bindˣ (bindˣ (H.forward q) ⟨≈⟩ >>=ₚ-identityˡ _ _) ⟨≈⟩ >>=ₚ-identityˡ _ (contᵢ body))
      ⟨≈⟩ ≈sym (step-red (H.rest , s) (inj₂ q))
      where
      d = MC.step c (s , inj₂ (dn q))
      p = C.I-step i query

      -- The first pass: `c` serves the forwarded query.
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
  absorb (Relay-⊗ (Relay-⊗ (id-Relay {Y}) (e-Relay {A})) (id-Relay {Z})) wc
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
