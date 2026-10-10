{-# OPTIONS --safe --without-K #-}

-- The one-time pad in the SSP setup: OTP encryption constructs a secure
-- channel from an authenticated one and a shared key (maurer2011cc §3.2–3.3),
-- the key a package drawn when first fetched (brzuska2018 Def. 9).
-- `Examples.RelSetup` is the possibilistic version; `aut` is its `relayPlain`.
-- A message travels by pollable state (`docs/uc-setup-ssp.md` §5.2): Alice
-- sends, Bob and Eve poll.
--
-- The composite `otp` inlines to the package `real` and the simulated secure
-- channel to `simulated`, each by one simulation.  No simulation relates
-- `otp` to any simulated ideal (`no-tree-simulation`): ≈ᶜ compares coins as
-- syntax, and the key is drawn at Alice's send where a simulator can draw only
-- at Eve's poll.  The two packages agree at every distinguisher by a deferred
-- sampling (`fresh`, `pending`, `revealed`, with the pad's bijection
-- `uniform-flip` at Eve's poll), which `≈ᵍ⇒≈ᵁ` reads as ≈ᵁ.
--
-- Not here: the transport to protocol-model's well-bracketed quotient,
-- `Fᵂ otp ≤UC Fᵂ ideal` from `otp≤ideal` along `SSP→PM[wb]`, and its
-- random-systems image, which needs the statement in PM itself since
-- `rewrite⇒RS` starts there.  See `docs/examples-ssp-otp.md`.

module CategoricalCrypto.Examples.SSP.OneTimePad where

open import Categories.Category

open import Data.Bool.Base
open import Data.Maybe.Base
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.Rational using (ℚ; 0ℚ; ½; _*_; _+_)
open import Data.Rational.Properties.Ext
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (case_of_; _∘′_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC
open import Relation.Nullary

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Distribution.Uniform.Flip

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface using (_⇿_)
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category
open import CategoricalCrypto.SSP.Reduction
open import CategoricalCrypto.SSP.Setup

private variable
  A : Iface
  L L′ X Y : Set

------------------------------------------------------------------------
-- Interfaces and resources
------------------------------------------------------------------------

Msg Key Cipher : Set
Msg    = Bool
Key    = Bool
Cipher = Bool

-- Alice sends; Bob, Eve and the key fetches poll.
Sendᴵ : Iface
Sendᴵ = oneᴵ (⊤ ⇿ Msg)

Pollᴵ : Set → Iface
Pollᴵ L = oneᴵ (L ⇿ ⊤)

Recvᴵ Keyᴵ Honᴵ Eveᴵ : Iface
Recvᴵ = Pollᴵ (Maybe Msg)
Keyᴵ  = Pollᴵ Key
Honᴵ  = Sendᴵ ⊗ᴵ Recvᴵ
Eveᴵ  = Pollᴵ (Maybe Cipher)

-- One message, kept from the first send; Eve's poll is answered by `leak`.
channel : (Maybe Msg → L) → unit ⇒ T₀ (Pollᴵ L) Honᴵ
channel leak = record
  { St = Maybe Msg ; init = nothing
  ; step = λ where
      s (inj₁ _)        _ → ret (s , leak s)
      s (inj₂ (inj₁ _)) m → ret (s <∣> just m , tt)
      s (inj₂ (inj₂ _)) _ → ret (s , s) }

-- The authenticated channel: Eve reads the message and cannot change it.
aut : unit ⇒ T₀ Eveᴵ Honᴵ
aut = channel (λ s → s)

-- The secure channel: Eve learns only that a message was sent.
ideal : unit ⇒ T₀ (Pollᴵ Bool) Honᴵ
ideal = channel is-just

key : Protocol unitᴵ Keyᴵ
key = record
  { St = Maybe Key ; init = nothing
  ; step = λ where
      nothing  _ _ → coin uniform-Bool λ k → ret (just k , k)
      (just k) _ _ → ret (just k , k) }

------------------------------------------------------------------------
-- The protocol, the real world and the simulator
------------------------------------------------------------------------

enc : Protocol (Keyᴵ ⊗ᴵ Sendᴵ) Sendᴵ
enc = record { St = ⊤ ; init = tt ; step = λ _ _ m →
  call (inj₁ tt) tt λ k → call (inj₂ tt) (m xor k) λ _ → ret (tt , tt) }

dec : Protocol (Keyᴵ ⊗ᴵ Recvᴵ) Recvᴵ
dec = record { St = ⊤ ; init = tt ; step = λ _ _ _ →
  call (inj₂ tt) tt λ where
    nothing  → ret (tt , nothing)
    (just c) → call (inj₁ tt) tt λ k → ret (tt , just (c xor k)) }

-- Both converters fetch the one key (brzuska2018 Def. 6, shared imports).
share : (Keyᴵ ⊗ᴵ Sendᴵ) ⊗ᴵ (Keyᴵ ⊗ᴵ Recvᴵ) ⇒ᴵ Honᴵ ⊗ᴵ Keyᴵ
share = record
  { ch = λ where
      (inj₁ (inj₁ _)) → inj₂ tt
      (inj₁ (inj₂ _)) → inj₁ (inj₁ tt)
      (inj₂ (inj₁ _)) → inj₂ tt
      (inj₂ (inj₂ _)) → inj₁ (inj₂ tt)
  ; qu = λ { {inj₁ (inj₁ _)} q → q ; {inj₁ (inj₂ _)} q → q ; {inj₂ (inj₁ _)} q → q ; {inj₂ (inj₂ _)} q → q }
  ; re = λ { {inj₁ (inj₁ _)} r → r ; {inj₁ (inj₂ _)} r → r ; {inj₂ (inj₁ _)} r → r ; {inj₂ (inj₂ _)} r → r } }

encdec : Protocol (Honᴵ ⊗ᴵ Keyᴵ) Honᴵ
encdec = (enc ⊗ᵖ dec) ∘ᵖ ⌜ share ⌝

otp : unit ⇒ T₀ Eveᴵ Honᴵ
otp = (wireᵖ ⊗ᵖ encdec) ∘ᵖ ⌜ αᴵ⁻¹ ⌝ ∘ᵖ (aut ⊗ᵖ key) ∘ᵖ ⌜ ∇ ⌝

-- On Eve's first poll after a send, draw a ciphertext and keep it.
sim : Pollᴵ Bool ⇒ Eveᴵ
sim = record
  { St = Maybe Cipher ; init = nothing
  ; step = λ where
      (just c) _ _ → ret (just c , just c)
      nothing  _ _ → call tt tt λ where
        false → ret (nothing , nothing)
        true  → coin uniform-Bool λ c → ret (just c , just c) }

------------------------------------------------------------------------
-- Inlining: both worlds as one package each
------------------------------------------------------------------------

-- The ciphertext on the channel and the key, drawn when first fetched.
real : unit ⇒ T₀ Eveᴵ Honᴵ
real = record
  { St = Maybe Cipher × Maybe Key ; init = nothing , nothing
  ; step = λ where
      (c , k)       (inj₁ _)        _ → ret ((c , k) , c)
      (c , k)       (inj₂ (inj₁ _)) m → fetch k λ k′ → ret ((c <∣> just (m xor k′) , just k′) , tt)
      (nothing , k) (inj₂ (inj₂ _)) _ → ret ((nothing , k) , nothing)
      (just c , k)  (inj₂ (inj₂ _)) _ → fetch k λ k′ → ret ((just c , just k′) , just (c xor k′)) }
  where
  fetch : Maybe Key → (Key → Calls unitᴵ X) → Calls unitᴵ X
  fetch nothing  f = coin uniform-Bool f
  fetch (just k) f = f k

-- The simulator's ciphertext and the secure channel's message.
simulated : unit ⇒ T₀ Eveᴵ Honᴵ
simulated = record
  { St = Maybe Cipher × Maybe Msg ; init = nothing , nothing
  ; step = λ where
      (c , m)             (inj₂ (inj₁ _)) m′ → ret ((c , m <∣> just m′) , tt)
      (c , m)             (inj₂ (inj₂ _)) _  → ret ((c , m) , m)
      (just c , m)        (inj₁ _)        _  → ret ((just c , m) , just c)
      (nothing , nothing) (inj₁ _)        _  → ret ((nothing , nothing) , nothing)
      (nothing , just m)  (inj₁ _)        _  → coin uniform-Bool λ c → ret ((just c , just m) , just c) }

otp≲real : otp ≲ᵖ real
otp≲real = record
  { θ = λ ((_ , ck) , _) → ck ; θ-init = refl
  ; θ-step = λ where
      _                              (inj₁ _)        _ → ≈ᶜ-refl
      ((_ , (_ , nothing)) , _)      (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      ((_ , (_ , just _)) , _)       (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      ((_ , (nothing , _)) , _)      (inj₂ (inj₂ _)) _ → ≈ᶜ-refl
      ((_ , (just _ , nothing)) , _) (inj₂ (inj₂ _)) _ → ≈ᶜ-refl
      ((_ , (just _ , just _)) , _)  (inj₂ (inj₂ _)) _ → ≈ᶜ-refl }

ideal≲simulated : sub sim ∘ ideal ≲ᵖ simulated
ideal≲simulated = record
  { θ = λ ((c , _) , m) → c , m ; θ-init = refl
  ; θ-step = λ where
      ((just _ , _) , _)        (inj₁ _)        _ → ≈ᶜ-refl
      ((nothing , _) , nothing) (inj₁ _)        _ → ≈ᶜ-refl
      ((nothing , _) , just _)  (inj₁ _)        _ → ≈ᶜ-refl
      _                         (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      _                         (inj₂ (inj₂ _)) _ → ≈ᶜ-refl }

------------------------------------------------------------------------
-- Deferred sampling: the two packages at every distinguisher
------------------------------------------------------------------------

-- An activation of `D` against a game from the given state.
play : (D : Protocol (Eveᴵ ⊗ᴵ Honᴵ) Ωᴵ) (G : Protocol unitᴵ (Eveᴵ ⊗ᴵ Honᴵ))
     → Calls (Eveᴵ ⊗ᴵ Honᴵ) (St D × Bool) → St G → Dist⊥ Bool
play D G t s = evalC (mapᶜ proj₂ (graft D G t s))

module _ (D : Protocol (Eveᴵ ⊗ᴵ Honᴵ) Ωᴵ) where

  -- After Eve's poll the worlds run in lockstep, the message being the unpadded ciphertext.
  revealed : ∀ t c k → play D real t (just c , just k) ≈Mℚ play D simulated t (just c , just (c xor k))
  revealed (ret _)                    c k = λ _ → refl
  revealed (call (inj₁ _) _ κ)        c k = revealed (κ (just c)) c k
  revealed (call (inj₂ (inj₁ _)) _ κ) c k = revealed (κ tt) c k
  revealed (call (inj₂ (inj₂ _)) _ κ) c k = revealed (κ (just (c xor k))) c k
  revealed (coin μ κ)                 c k =
    >>=ᴹ-congˡ μ (λ b → play D real (κ b) _) (λ b → play D simulated (κ b) _) λ b → revealed (κ b) c k
  revealed dead                       c k = λ _ → refl

  -- Between Alice's send and Eve's poll the real key is still a coin.
  pending : ∀ t m → (uniform-Bool >>=ᴹ λ k → play D real t (just (m xor k) , just k))
                    ≈Mℚ play D simulated t (nothing , just m)
  pending (ret (_ , b))              m = >>=ᴹ-const uniform-Bool (return⊥ b)
  pending (call (inj₁ _) _ κ)        false =
    >>=ᴹ-congˡ uniform-Bool (λ k → play D real (κ (just k)) (just k , just k))
                            (λ c → play D simulated (κ (just c)) (just c , just false)) λ where
      false → revealed (κ (just false)) false false
      true  → revealed (κ (just true)) true true
  pending (call (inj₁ _) _ κ)        true  =
    uniform-flip {f = λ k → play D real (κ (just (not k))) (just (not k) , just k)}
                 {g = λ c → play D simulated (κ (just c)) (just c , just true)} λ where
      false → revealed (κ (just true)) true false
      true  → revealed (κ (just false)) false true
  pending (call (inj₂ (inj₁ _)) _ κ) m = pending (κ tt) m
  pending (call (inj₂ (inj₂ _)) _ κ) m = λ P →
    trans (>>=ᴹ-congˡ uniform-Bool (λ k → play D real (κ (just ((m xor k) xor k))) (just (m xor k) , just k))
                                   (λ k → play D real (κ (just m)) (just (m xor k) , just k))
                                   (unpad m) P)
          (pending (κ (just m)) m P)
    where
    unpad : ∀ m k → play D real (κ (just ((m xor k) xor k))) (just (m xor k) , just k)
                    ≈Mℚ play D real (κ (just m)) (just (m xor k) , just k)
    unpad false false = λ _ → refl
    unpad false true  = λ _ → refl
    unpad true  false = λ _ → refl
    unpad true  true  = λ _ → refl
  pending (coin μ κ)                 m = λ P →
    trans (>>=ᴹ-comm uniform-Bool μ (λ k b → play D real (κ b) (just (m xor k) , just k)) P)
          (>>=ᴹ-congˡ μ (λ b → uniform-Bool >>=ᴹ λ k → play D real (κ b) (just (m xor k) , just k))
                        (λ b → play D simulated (κ b) (nothing , just m)) (λ b → pending (κ b) m) P)
  pending dead                       m = >>=ᴹ-const uniform-Bool (return-ℚ nothing)

  -- Before Alice's send nothing is drawn on either side.
  fresh : ∀ t → play D real t (nothing , nothing) ≈Mℚ play D simulated t (nothing , nothing)
  fresh (ret _)                    = λ _ → refl
  fresh (call (inj₁ _) _ κ)        = fresh (κ nothing)
  fresh (call (inj₂ (inj₁ _)) m κ) = pending (κ tt) m
  fresh (call (inj₂ (inj₂ _)) _ κ) = fresh (κ nothing)
  fresh (coin μ κ)                 =
    >>=ᴹ-congˡ μ (λ b → play D real (κ b) _) (λ b → play D simulated (κ b) _) λ b → fresh (κ b)
  fresh dead                       = λ _ → refl

-- brzuska2018 Def. 8 at ε = 0.
perfect : real ≈ᵍ[ 0ℚ ] simulated
perfect D = ≈Mℚ⇒≈[0] {runᵖ (D ∘ᵖ real)} {runᵖ (D ∘ᵖ simulated)} (fresh D (step D (init D) tt tt))

otp≤ideal : otp ≤UC ideal
otp≤ideal = dummy-complete (sim , ≈ᵁ-trans (≈C⇒≈ᵁ (≲⇒≈ᵖ otp≲real))
  (≈ᵁ-trans (≈ᵍ⇒≈ᵁ perfect) (≈ᵁ-sym (≈C⇒≈ᵁ (≲⇒≈ᵖ ideal≲simulated)))))

------------------------------------------------------------------------
-- Why no simulation does it: ≈ᵖ keeps where the coins are
------------------------------------------------------------------------

private
  tosses : Calls A X → Bool
  tosses (coin _ _) = true
  tosses _          = false

  tosses-map : (f : X → Y) (t : Calls A X) → tosses (mapᶜ f t) ≡ tosses t
  tosses-map f (ret _)      = refl
  tosses-map f (call _ _ _) = refl
  tosses-map f (coin _ _)   = refl
  tosses-map f dead         = refl

  tosses-≈ᶜ : {t t′ : Calls A X} → t ≈ᶜ t′ → tosses t ≡ tosses t′
  tosses-≈ᶜ (ret _)  = refl
  tosses-≈ᶜ (call _) = refl
  tosses-≈ᶜ (coin _) = refl
  tosses-≈ᶜ dead     = refl

  -- Does Alice's first send draw?
  draws : unit ⇒ T₀ Eveᴵ Honᴵ → Bool
  draws G = tosses (step G (init G) (inj₂ (inj₁ tt)) false)

  draws-sim : {G G′ : unit ⇒ T₀ Eveᴵ Honᴵ} → G ≲ᵖ G′ → draws G ≡ draws G′
  draws-sim {G} {G′} u =
    trans (sym (tosses-map (map₁ (θ u)) (step G (init G) (inj₂ (inj₁ tt)) false)))
          (trans (tosses-≈ᶜ (θ-step u (init G) (inj₂ (inj₁ tt)) false))
                 (cong (λ s → tosses (step G′ s (inj₂ (inj₁ tt)) false)) (θ-init u)))

-- The key is drawn at Alice's send, where a simulator cannot draw.
no-tree-simulation : (s : Pollᴵ Bool ⇒ Eveᴵ) → ¬ otp ≈ᵖ sub s ∘ ideal
no-tree-simulation s e = case EqC.gfold isEquivalence draws draws-sim e of λ ()

------------------------------------------------------------------------
-- Leaky channels (`Examples.RelSetup`'s relays)
------------------------------------------------------------------------

-- A simulator that relabels Eve's answer.
poll : (L → L′) → Pollᴵ L ⇒ Pollᴵ L′
poll f = ⌜ record { ch = λ _ → tt ; qu = λ _ → tt ; re = f } ⌝

relabel : (f : L → L′) (leak : Maybe Msg → L) → channel (f ∘′ leak) ≲ᵖ sub (poll f) ∘ channel leak
relabel f leak = record
  { θ = λ s → (tt , tt) , s ; θ-init = refl
  ; θ-step = λ where
      _ (inj₁ _)        _ → ≈ᶜ-refl
      _ (inj₂ (inj₁ _)) _ → ≈ᶜ-refl
      _ (inj₂ (inj₂ _)) _ → ≈ᶜ-refl }

-- Leakage may always be added.
ideal≤aut : ideal ≤UC aut
ideal≤aut = dummy-complete (poll is-just , ≈C⇒≈ᵁ (≲⇒≈ᵖ (relabel is-just (λ s → s))))

otp≤aut : otp ≤UC aut
otp≤aut = ≤UC-trans otp≤ideal ideal≤aut

-- Forward the message, leaking its complement.
relayEnc : unit ⇒ T₀ Eveᴵ Honᴵ
relayEnc = channel (map not)

complement : Eveᴵ ⇒ Eveᴵ
complement = poll (map not)

relay≤aut : relayEnc ≤UC aut
relay≤aut = dummy-complete (complement , ≈C⇒≈ᵁ (≲⇒≈ᵖ (relabel (map not) (λ s → s))))

------------------------------------------------------------------------
-- The authenticated channel does not realize the secure one
------------------------------------------------------------------------

-- Send `m`, then report whether Eve saw `true`.
probe : Msg → Protocol (Eveᴵ ⊗ᴵ Honᴵ) Ωᴵ
probe m = record { St = ⊤ ; init = tt ; step = λ _ _ _ →
  call (inj₂ (inj₁ tt)) m λ _ → call (inj₁ tt) tt λ r → ret (tt , fromMaybe false r) }

-- Relabelling the message by `not` is invisible to the secure channel, and
-- turns one probe into the other.
notᴵ : Honᴵ ⇒ᴵ Honᴵ
notᴵ = record
  { ch = λ c → c
  ; qu = λ { {inj₁ _} q → not q ; {inj₂ _} q → q }
  ; re = λ { {inj₁ _} r → r ; {inj₂ _} r → map not r } }

flip-ideal : T₁ (Pollᴵ Bool) ⌜ notᴵ ⌝ ∘ ideal ≲ᵖ ideal
flip-ideal = record
  { θ = λ (_ , s) → map not s ; θ-init = refl
  ; θ-step = λ where
      (_ , nothing) (inj₁ _)        _     → ≈ᶜ-refl
      (_ , just _)  (inj₁ _)        _     → ≈ᶜ-refl
      (_ , nothing) (inj₂ (inj₁ _)) false → ≈ᶜ-refl
      (_ , nothing) (inj₂ (inj₁ _)) true  → ≈ᶜ-refl
      (_ , just _)  (inj₂ (inj₁ _)) _     → ≈ᶜ-refl
      _             (inj₂ (inj₂ _)) _     → ≈ᶜ-refl }

probe-flip : probe true ∘ᵖ T₁ Eveᴵ ⌜ notᴵ ⌝ ≲ᵖ probe false
probe-flip = ≲ᵖ-const λ _ _ _ → ≈ᶜ-refl

-- In an abstract category: at `Prot` the unifier would solve each implicit
-- morphism through the transparent `_∘ᵖ_` (as `SSP.Reduction.Closed`).
private
  module Slide {o ℓ e} (𝒟 : Category o ℓ e) where
    module D = Category 𝒟
    open D.HomReasoning
    open import Categories.Morphism.Reasoning 𝒟

    -- The probe's relabelling slides past the simulator onto an ideal that absorbs it.
    slide : {U X Y Z : D.Obj} {G : U D.⇒ X} {S : X D.⇒ Y} {F′ : X D.⇒ X} {F : Y D.⇒ Y} {p₀ p₁ : Y D.⇒ Z}
          → p₀ D.≈ p₁ D.∘ F → F D.∘ S D.≈ S D.∘ F′ → F′ D.∘ G D.≈ G → p₀ D.∘ S D.∘ G D.≈ p₁ D.∘ S D.∘ G
    slide e₀ e₁ e₂ = (e₀ ⟩∘⟨refl) ○ pullʳ (pullˡ e₁) ○ (refl⟩∘⟨ pullʳ e₂)

leaky-not-secure : ¬ aut ≤UC ideal
leaky-not-secure le = 1≰½ (gap true)
  where
  open Approximation Approximation⊥ using (_≈[_]_; ≈[]-sym; ≈[]-trans)

  s : Pollᴵ Bool ⇒ Eveᴵ
  s = proj₁ (≤UC⇒dummy le)

  onAut onIdeal : Msg → Dist⊥ Bool
  onAut m   = runᵖ ((probe m ∘ᵖ aut) ∘ᵖ wireᵖ)
  onIdeal m = runᵖ ((probe m ∘ᵖ (sub s ∘ ideal)) ∘ᵖ wireᵖ)

  ¼ : ℚ
  ¼ = ½ * ½

  seen : ∀ m → onAut m ≈[ ¼ ] onIdeal m
  seen m = KE.run∼ (≈ᵁ⇒≈ℰ (proj₂ (≤UC⇒dummy le))) {probe m} id ¼ (0<½* (0<½* 0<1ℚ))

  -- Whatever the simulator, the simulated ideal shows both probes the same.
  blind : onIdeal true ≈Mℚ onIdeal false
  blind = runᵖ-resp (∘ᵖ-resp-≈ᵖ {f = probe true ∘ᵖ (sub s ∘ ideal)} {h = probe false ∘ᵖ (sub s ∘ ideal)}
                                {g = wireᵖ} {i = wireᵖ}
    (Equiv.sym (Slide.slide Prot {G = ideal} {S = sub s} {F′ = T₁ (Pollᴵ Bool) ⌜ notᴵ ⌝}
                            {F = T₁ Eveᴵ ⌜ notᴵ ⌝} {p₀ = probe false} {p₁ = probe true}
                            (Equiv.sym (≲⇒≈ᵖ probe-flip)) (Equiv.sym sub-commute′) (≲⇒≈ᵖ flip-ideal)))
    Equiv.refl)

  gap : onAut true ≈[ ¼ + (0ℚ + ¼) ] onAut false
  gap = ≈[]-trans {onAut true} {onIdeal true} {onAut false} (seen true)
          (≈[]-trans {onIdeal true} {onIdeal false} {onAut false} (≈Mℚ⇒≈[0] {onIdeal true} {onIdeal false} blind)
                     (≈[]-sym {onAut false} {onIdeal false} (seen false)))
