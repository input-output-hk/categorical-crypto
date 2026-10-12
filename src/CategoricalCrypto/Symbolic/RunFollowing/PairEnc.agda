{-# OPTIONS --safe --without-K --guardedness #-}

-- Before the sender accepts a plaintext, the ciphertext handle is unavailable.
-- Afterwards the same abstract handle denotes the actual encryption on the
-- left and encryption of zero on the right. The chosen plaintext remains an
-- ordinary known term, not part of a fixed-message assumption.

open import Data.Nat.Base using (ℕ)

module CategoricalCrypto.Symbolic.RunFollowing.PairEnc (κ : ℕ) where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base
open import Data.Product
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Term.PairEnc.Cipher

import CategoricalCrypto.Machines.Sim.RunFollowing as Following

open Terms Σ₀
open EqTheory E₀

key coins : Name
key = κ , 0
coins = κ , 1

zero-message : Msg
zero-message = app (cst 0) []

KeyFree : Msg → Set
KeyFree t = key ∉ names t

record Plaintext : Set where
  constructor plaintext
  field
    message : Msg
    fresh-key : KeyFree message
    normal : nf message ≡ message
open Plaintext public

data World : Set where
  before : World
  after : Plaintext → World

infix 4 _≤ʷ_
data _≤ʷ_ : World → World → Set where
  stay : ∀ {w} → w ≤ʷ w
  accept : ∀ {m} → before ≤ʷ after m

transʷ : ∀ {w w′ w″} → w ≤ʷ w′ → w′ ≤ʷ w″ → w ≤ʷ w″
transʷ stay e = e
transʷ accept stay = accept

module F = Following World before _≤ʷ_ stay transʷ

Legal : World → Msg → Set
Legal before = KeyFree
Legal (after _) = λ _ → ⊤

expand : Bool → World → Msg → Msg
expand b before t = t
expand true (after m) t = t [ key ≔ cipher (message m) key coins ]
expand false (after m) t = t [ key ≔ cipher zero-message key coins ]

private variable
  b : Bool
  w w′ : World
  t u : Msg
  ss : List ⊤

expand* : Bool → World → All Tm ss → All Tm ss
expand* b w [] = []
expand* b w (t ∷ ts) = expand b w t ∷ expand* b w ts

expand*-before : ∀ b (ts : All Tm ss) → expand* b before ts ≡ ts
expand*-before b [] = refl
expand*-before b (t ∷ ts) = cong (t ∷_) (expand*-before b ts)

expand*-replace : ∀ (ts : All Tm ss) m → expand* true (after m) ts ≡ ts [ key ≔ cipher (message m) key coins ]*
expand*-replace [] m = refl
expand*-replace (t ∷ ts) m = cong (expand true (after m) t ∷_) (expand*-replace ts m)

expand*-zero : ∀ (ts : All Tm ss) m → expand* false (after m) ts ≡ ts [ key ≔ cipher zero-message key coins ]*
expand*-zero [] m = refl
expand*-zero (t ∷ ts) m = cong (expand false (after m) t ∷_) (expand*-zero ts m)

expand-app : ∀ b w f ts → expand b w (app f ts) ≡ app f (expand* b w ts)
expand-app b before f ts = cong (app f) (sym (expand*-before b ts))
expand-app true (after m) f ts = cong (app f) (sym (expand*-replace ts m))
expand-app false (after m) f ts = cong (app f) (sym (expand*-zero ts m))

expand-canon : ∀ b w t → nf (expand b w t) ≡ expand b w (nf t)
expand-canon b before t = refl
expand-canon true (after m) t = trans (nf-[≔] t) (cong (nf t [ key ≔_]) (cong (λ x → cipher x key coins) (normal m)))
expand-canon false (after m) t = nf-[≔] t

expand-injective : ∀ b w {t u} → expand b w t ≡ expand b w u → t ≡ u
expand-injective b before e = e
expand-injective true (after m) e = [≔]-injective e
expand-injective false (after m) e = [≔]-injective e

expand-equation : ∀ b w {t u} → expand b w t ≈E expand b w u → t ≈E u
expand-equation b w {t} {u} e = expand-injective b w (trans (sym (expand-canon b w t)) (trans e (expand-canon b w u)))

expand-cong : ∀ b w {t u} → t ≈E u → expand b w t ≈E expand b w u
expand-cong b w {t} {u} e = trans (expand-canon b w t) (trans (cong (expand b w) e) (sym (expand-canon b w u)))

expand-fresh : ∀ b w n → n ≢ key → expand b w (name n) ≡ name n
expand-fresh b before n n≢ = refl
expand-fresh true (after m) n n≢ = [≔]-∉ (name n) λ where (here refl) → n≢ refl ; (there ())
expand-fresh false (after m) n n≢ = [≔]-∉ (name n) λ where (here refl) → n≢ refl ; (there ())

promote-legal : w ≤ʷ w′ → Legal w t → Legal w′ t
promote-legal stay p = p
promote-legal accept p = tt

promote-expand : ∀ b (e : w ≤ʷ w′) t → Legal w t → expand b w′ t ≡ expand b w t
promote-expand b stay t p = refl
promote-expand true accept t p = [≔]-∉ t p
promote-expand false accept t p = [≔]-∉ t p

canon-legal : ∀ w t → Legal w t → Legal w (nf t)
canon-legal before t p = p ∘ canon-names t
canon-legal (after m) t p = tt

recipe-legal : ∀ w {Δ} (ζ : Recipe Δ (λ _ → ⊥) tt) (ρ : Frame Δ)
  → Each (Legal w) ρ → Legal w (ζ ⟨ ρ ⟩)
recipe-legal before ζ ρ legal p = [ no-name ρ legal , (λ ()) ]′ (recipe-names ζ ρ p)
  where
  no-name : ∀ {Δ} (ρ : Frame Δ) → Each KeyFree ρ → key ∉ names* ρ
  no-name [] [] ()
  no-name (t ∷ ρ) (p ∷ ps) q = [ p , no-name ρ ps ]′ (∈-++⁻ (names t) q)
recipe-legal (after m) ζ ρ legal = tt

record Letter (w : World) : Set where
  constructor letter
  field
    term : Msg
    legal : Legal w term
open Letter public

messages : F.Letters
messages = record { Base = Msg ; Related = Letter ; project = λ b w l → expand b w (term l) }

select : (l : Letter before) → Plaintext
select (letter m p) = plaintext (nf m) (canon-legal before m p) (≈E⇒canon {t = nf m} {u = m} (canon-≈E m))
