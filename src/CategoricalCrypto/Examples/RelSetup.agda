{-# OPTIONS --safe --without-K #-}

-- The locally graded UC theory (`Abstract2`) run at a concrete setup:
-- 𝒞 = ℐ = Rel monoidal via ×, ℳ = the curried tensor, ℰ = the hom
-- presheaf into the observation object. A protocol A ⇒ T₀ X B is a
-- relation from inputs to (leakage, output) pairs and `f ≤UC g` is
-- possibilistic simulation.

module CategoricalCrypto.Examples.RelSetup where

open import Data.Bool
open import Data.Bool.Properties
open import Data.Product
open import Data.Unit.Polymorphic
open import Level
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import Categories.Category.Instance.Rels
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Instance.Rels
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf
open import Categories.Functor.Properties

open import CategoricalCrypto.Standard2

Rel : MonoidalCategory (suc 0ℓ) (suc 0ℓ) 0ℓ
Rel = record { U = Rels 0ℓ 0ℓ ; monoidal = Rels-Monoidal }

-- An environment observes a subset of the interface it is attached to.
ℰ-tests : Presheaf (Rels 0ℓ 0ℓ) (Setoids (suc 0ℓ) 0ℓ)
ℰ-tests = Hom[ Rels 0ℓ 0ℓ ][-, ⊤ ]

open StdUC Rel ℰ-tests

private variable
  A B X : Set

------------------------------------------------------------------------
-- ≈ᵁ at this setup is equality of relations
------------------------------------------------------------------------

ℰ-faithful : Faithful ℰ-tests
ℰ-faithful {x = f} {y = g} eq = fwd , bwd
  where
  -- the test that observes a single interface value
  point : B → B ⇒ ⊤
  point b₀ b _ = b ≡ b₀

  fwd : ∀ {a b} → f a b → g a b
  fwd {a} {b} fab =
    let _ , (b′ , gab′ , b′≡b) , _ = proj₁ (eq {point b}) (tt , (b , fab , refl) , lift refl)
    in subst (g a) b′≡b gab′

  bwd : ∀ {a b} → g a b → f a b
  bwd {a} {b} gab =
    let _ , (b′ , fab′ , b′≡b) , _ = proj₂ (eq {point b}) (tt , (b , gab , refl) , lift refl)
    in subst (f a) b′≡b fab′

≈ᵁ⇒≈ : {f g : A ⇒ T₀ X B} → f ≈ᵁ g → f ≈ g
≈ᵁ⇒≈ e = KE.∼⇒≈ ℰ-faithful (≈ᵁ⇒≈ℰ e)

------------------------------------------------------------------------
-- A one-time pad, and algebraic perfect security
------------------------------------------------------------------------

Msg Key Cipher : Set
Msg = Bool
Key = Bool
Cipher = Bool

enc : Key → Msg → Cipher
enc k m = k xor m

enc-cancel : ∀ c m → enc (c xor m) m ≡ c
enc-cancel c m = trans (xor-assoc c m m) (trans (cong (c xor_) (xor-same m)) (xor-identityʳ c))

encChan : Msg ⇒ Cipher
encChan m c = ∃[ k ] c ≡ enc k m

anyCipher : unit ⇒ Cipher
anyCipher _ _ = ⊤

discard : Msg ⇒ unit
discard _ _ = ⊤

otp-perfect : encChan ≈ anyCipher ∘ discard
otp-perfect = (λ _ → tt , tt , tt) , λ where {m} {c} _ → c xor m , sym (enc-cancel c m)

------------------------------------------------------------------------
-- Two protocols and their ideal counterparts
------------------------------------------------------------------------

-- Hop 1: transmit the message, leaking a one-time-pad ciphertext …
sendEnc : Msg ⇒ T₀ Cipher Msg
sendEnc m (c , m′) = encChan m c × m ≡ m′

-- … while the ideal channel leaks nothing.
sendIdeal : Msg ⇒ T₀ unit Msg
sendIdeal m (_ , m′) = m ≡ m′

-- Hop 2: forward the message, leaking its complement …
relayEnc : Msg ⇒ T₀ Msg Msg
relayEnc m (t , m′) = t ≡ not m × m ≡ m′

-- … while the ideal relay leaks the message itself.
relayPlain : Msg ⇒ T₀ Msg Msg
relayPlain m (t , m′) = t ≡ m × m ≡ m′

complement : Msg ⇒ Msg
complement m t = t ≡ not m

------------------------------------------------------------------------
-- Emulation, and its composition
------------------------------------------------------------------------

send-sim : sendEnc ≈ sub anyCipher ∘ sendIdeal
send-sim = (λ { {m} (_ , m≡m′) → (tt , m) , refl , tt , lift m≡m′ })
         , λ { (_ , m≡m₀ , _ , lift m₀≡m′) →
               proj₂ otp-perfect (tt , tt , tt) , trans m≡m₀ m₀≡m′ }

-- The one-time-pad channel realizes the ideal channel
send≤ideal : sendEnc ≤UC sendIdeal
send≤ideal = dummy-complete (anyCipher , ≈C⇒≈ᵁ send-sim)

relay-sim : relayEnc ≈ sub complement ∘ relayPlain
relay-sim = (λ { {m} (t≡ , m≡) → (m , m) , (refl , refl) , t≡ , lift m≡ })
          , λ { (_ , (t₀≡m , m≡m₀) , t≡ , lift m₀≡m′) →
                trans t≡ (cong not t₀≡m) , trans m≡m₀ m₀≡m′ }

-- The complement-leaking relay realizes the message-leaking one
relay≤plain : relayEnc ≤UC relayPlain
relay≤plain = dummy-complete (complement , ≈C⇒≈ᵁ relay-sim)

-- Some more examples
relayed-otp : relayEnc ∙ sendEnc ≤UC relayPlain ∙ sendIdeal
relayed-otp = UC-compose send≤ideal relay≤plain

relayed-otp² : sendEnc ∙ (relayEnc ∙ sendEnc) ≤UC sendIdeal ∙ (relayPlain ∙ sendIdeal)
relayed-otp² = UC-compose relayed-otp send≤ideal

ideal-sim : sendIdeal ≈ sub discard ∘ relayPlain
ideal-sim = (λ { {m} m≡m′ → (m , m) , (refl , refl) , tt , lift m≡m′ })
          , λ { (_ , (_ , m≡m₀) , _ , lift m₀≡m′) → trans m≡m₀ m₀≡m′ }

-- Leakage may always be added
ideal≤leaky : sendIdeal ≤UC relayPlain
ideal≤leaky = dummy-complete (discard , ≈C⇒≈ᵁ ideal-sim)

send≤leaky : sendEnc ≤UC relayPlain
send≤leaky = ≤UC-trans send≤ideal ideal≤leaky

------------------------------------------------------------------------
-- the leaky channel does not realize the ideal one
------------------------------------------------------------------------

leaky-not-secure : ¬ relayPlain ≤UC sendIdeal
leaky-not-secure p =
  let _ , e = p id
      eq = ≈ᵁ⇒≈ e
      (u , _) , _ , s·true , _ =
        proj₁ eq {true} {true , true} ((true , true) , (refl , refl) , lift refl , lift refl)
      _ , (t₀≡false , _) , lift t₀≡true , _ =
        proj₂ eq {false} {true , false} ((u , false) , refl , s·true , lift refl)
  in contradiction (trans (sym t₀≡true) t₀≡false) λ ()
