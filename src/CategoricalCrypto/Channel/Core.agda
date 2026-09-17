{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

module CategoricalCrypto.Channel.Core where

open import categorical-crypto.Prelude hiding ([_])
open import Data.Sum.Base
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

------------------------------------
-- Modes for messages (In or Out) --
------------------------------------

data Mode : Type where
  Out : Mode
  In : Mode

infixr 10 ¬ₘ_

¬ₘ_ : Fun₁ Mode
¬ₘ Out = In
¬ₘ In = Out

¬ₘ-idempotent : ∀ {m} → ¬ₘ ¬ₘ m ≡ m
¬ₘ-idempotent {Out} = refl
¬ₘ-idempotent {In} = refl

-------------------------------
-- Channels of communication --
-------------------------------

infix 10 _⇿_

record Channel : Type₁ where
  constructor _⇿_
  field
    inType outType : Type

open Channel

modeType : Mode → Channel → Type
modeType Out = outType
modeType In = inType

{-# INJECTIVE_FOR_INFERENCE modeType #-}

simpleChannel : (Mode → Type) → Channel
simpleChannel T = T In ⇿ T Out

----------------------------------------
-- Channel identity and transposition --
----------------------------------------

I : Channel
I = ⊥ ⇿ ⊥

_ᵀ : Fun₁ Channel
A ᵀ = A .outType ⇿ A .inType

ᵀ-identity : I ᵀ ≡ I
ᵀ-identity = refl

ᵀ-idempotent : ∀ {A} → A ᵀ ᵀ ≡ A
ᵀ-idempotent = refl

--------------------------------------------------------
-- Forwarding a message from a given Channel and Mode --
--------------------------------------------------------

infix 4 _[_]⇒[_]_

-- The combinators below are written with the constructor `mk⇒` rather than
-- a `record { app = … }` expression on purpose. Agda turns a record
-- expression on a right-hand side into copattern clauses, so a term
-- never reduces unless it is projected.
record _[_]⇒[_]_ (A : Channel) (mᵢ : Mode) (mₒ : Mode) (B : Channel) : Type where
  constructor mk⇒
  field
    app : modeType mᵢ A → modeType mₒ B

open _[_]⇒[_]_ public

⇒-trans : ∀ {A B C m m₁ m₂} → A [ m ]⇒[ m₁ ] B → B [ m₁ ]⇒[ m₂ ] C → A [ m ]⇒[ m₂ ] C
⇒-trans p q = mk⇒ (app q ∘ app p)

_⇒ₜ_ : ∀ {A B C m m₁ m₂} → A [ m ]⇒[ m₁ ] B → B [ m₁ ]⇒[ m₂ ] C → A [ m ]⇒[ m₂ ] C
_⇒ₜ_ = ⇒-trans

infixr 10 _⇒ₜ_

⇒-refl' : ∀ {m A B} → A ≡ B → A [ m ]⇒[ m ] B
⇒-refl' refl = mk⇒ id

⇒-refl : ∀ {m A} → A [ m ]⇒[ m ] A
⇒-refl = ⇒-refl' refl

----------------------------------
-- Forwarding and transposition --
----------------------------------

⇒-double-transpose-left : ∀ {m A} → A ᵀ ᵀ [ m ]⇒[ m ] A
⇒-double-transpose-left {A = A} rewrite ᵀ-idempotent {A} = ⇒-refl

⇒-double-transpose-right : ∀ {m A} → A [ m ]⇒[ m ] A ᵀ ᵀ
⇒-double-transpose-right {A = A} rewrite ᵀ-idempotent {A} = ⇒-refl

⇒-double-negate-left : ∀ {m A} → A [ ¬ₘ ¬ₘ m ]⇒[ m ] A
⇒-double-negate-left {m} rewrite (¬ₘ-idempotent {m}) = ⇒-refl

⇒-double-negate-right : ∀ {m A} → A [ m ]⇒[ ¬ₘ ¬ₘ m ] A
⇒-double-negate-right {m} rewrite (¬ₘ-idempotent {m}) = ⇒-refl

⇒-negate-transpose-right : ∀ {m A} → A [ m ]⇒[ ¬ₘ m ] A ᵀ
⇒-negate-transpose-right {Out} = mk⇒ id
⇒-negate-transpose-right {In} = mk⇒ id

⇒-negate-transpose-left : ∀ {m A} → A ᵀ [ ¬ₘ m ]⇒[ m ] A
⇒-negate-transpose-left = ⇒-negate-transpose-right ⇒ₜ ⇒-double-negate-left

⇒-transpose-left-negate-right : ∀ {m A} → A ᵀ [ m ]⇒[ ¬ₘ m ] A
⇒-transpose-left-negate-right {A = A} rewrite ᵀ-idempotent {A} = ⇒-negate-transpose-right {A = A ᵀ}

⇒-negate-left-transpose-right : ∀ {m A} → A [ ¬ₘ m ]⇒[ m ] A ᵀ
⇒-negate-left-transpose-right {A = A} rewrite ᵀ-idempotent {A} = ⇒-negate-transpose-left {A = A ᵀ}

-- `_⊗₀_` and the forwarders in the `opaque` block below are `opaque` because
-- the message types are sums; letting them reduce everywhere would make every
-- machine-layer goal a nest of `inj`s.  That is why every downstream proof in
-- the machine layer carries a long `unfolding` list.

-----------------------------------
-- Tensorial product on Channels --
-----------------------------------

infixr 9 _⊗₀_

opaque
  _⊗₀_ : Fun₂ Channel
  A ⊗₀ B = (inType A ⊎ inType B) ⇿ (outType A ⊎ outType B)

  destruct-⊗ : ∀ {A B m} → modeType m (A ⊗₀ B) → modeType m A ⊎ modeType m B
  destruct-⊗ {m = Out} = id
  destruct-⊗ {m = In} = id

  construct-⊗ : ∀ {A B m} → modeType m A ⊎ modeType m B → modeType m (A ⊗₀ B)
  construct-⊗ {m = Out} = id
  construct-⊗ {m = In}  = id

-----------------------------------
-- Forwarding tensorial products --
-----------------------------------

  ⊗-sym : ∀ {m A B} → A ⊗₀ B [ m ]⇒[ m ] B ⊗₀ A
  ⊗-sym {Out} = mk⇒ swap
  ⊗-sym {In} = mk⇒ swap

  ⊗-right-assoc : ∀ {m A B C} → (A ⊗₀ B) ⊗₀ C [ m ]⇒[ m ] A ⊗₀ B ⊗₀ C
  ⊗-right-assoc {Out} = mk⇒ assocʳ
  ⊗-right-assoc {In} = mk⇒ assocʳ

  ⊗-left-assoc : ∀ {m A B C} → A ⊗₀ B ⊗₀ C [ m ]⇒[ m ] (A ⊗₀ B) ⊗₀ C
  ⊗-left-assoc {Out} = mk⇒ assocˡ
  ⊗-left-assoc {In} = mk⇒ assocˡ

  ⊗-right-intro : ∀ {m A B} → A [ m ]⇒[ m ] A ⊗₀ B
  ⊗-right-intro {Out} = mk⇒ inj₁
  ⊗-right-intro {In} = mk⇒ inj₁

  ⊗-ᵀ-distrib : ∀ {m A B} → (A ⊗₀ B) ᵀ [ m ]⇒[ m ] A ᵀ ⊗₀ B ᵀ
  ⊗-ᵀ-distrib {Out} = mk⇒ id
  ⊗-ᵀ-distrib {In} = mk⇒ id

  ⊗-ᵀ-factor : ∀ {m A B} → A ᵀ ⊗₀ B ᵀ [ m ]⇒[ m ] (A ⊗₀ B) ᵀ
  ⊗-ᵀ-factor {Out} = mk⇒ id
  ⊗-ᵀ-factor {In} = mk⇒ id

  ⊗-right-neutral : ∀ {m A} → A ⊗₀ I [ m ]⇒[ m ] A
  ⊗-right-neutral {Out} = mk⇒ (λ {(inj₁ x) → x} )
  ⊗-right-neutral {In} = mk⇒ (λ {(inj₁ x) → x} )

  ⊗-fusion : ∀ {m A} → A ⊗₀ A [ m ]⇒[ m ] A
  ⊗-fusion {Out} = mk⇒ ([ id , id ] )
  ⊗-fusion {In} = mk⇒ ([ id , id ] )

  ⊗-combine : ∀ {m m₁ A B C D} → A [ m ]⇒[ m₁ ] B → C [ m ]⇒[ m₁ ] D → A ⊗₀ C [ m ]⇒[ m₁ ] B ⊗₀ D
  ⊗-combine {Out} {Out} p q = mk⇒ (λ { (inj₁ x) → inj₁ (p .app x) ; (inj₂ y) → inj₂ (q .app y)} )
  ⊗-combine {Out} {In} p q = mk⇒ (λ { (inj₁ x) → inj₁ (p .app x) ; (inj₂ y) → inj₂ (q .app y)} )
  ⊗-combine {In} {Out} p q = mk⇒ (λ { (inj₁ x) → inj₁ (p .app x) ; (inj₂ y) → inj₂ (q .app y)} )
  ⊗-combine {In} {In} p q = mk⇒ (λ { (inj₁ x) → inj₁ (p .app x) ; (inj₂ y) → inj₂ (q .app y)} )

⊗-left-intro : ∀ {m A B} → B [ m ]⇒[ m ] A ⊗₀ B
⊗-left-intro = ⊗-right-intro ⇒ₜ ⊗-sym

⊗-left-neutral : ∀ {m A} → I ⊗₀ A [ m ]⇒[ m ] A
⊗-left-neutral = ⊗-sym ⇒ₜ ⊗-right-neutral

⊗-right-double-intro : ∀ {m A B C} → A [ m ]⇒[ m ] B → A ⊗₀ C [ m ]⇒[ m ] B ⊗₀ C
⊗-right-double-intro p = ⊗-combine p ⇒-refl

⊗-left-double-intro : ∀ {m A B C} → B [ m ]⇒[ m ] C → A ⊗₀ B [ m ]⇒[ m ] A ⊗₀ C
⊗-left-double-intro p = ⊗-sym ⇒ₜ ⊗-right-double-intro p ⇒ₜ ⊗-sym

⊗-merge : ∀ {m m₁ A B C} → A [ m ]⇒[ m₁ ] C → B [ m ]⇒[ m₁ ] C → A ⊗₀ B [ m ]⇒[ m₁ ] C
⊗-merge p q = ⊗-combine p q ⇒ₜ ⊗-fusion

--------------------------------
-- Additional Channel builder --
--------------------------------

⨂_ : ∀ {n} → (Fin n → Channel) → Channel
⨂_ {zero} _ = I
⨂_ {suc n} f = f fzero ⊗₀ ⨂ (f ∘ fsuc)

_⨂ⁿ_ : ℕ → Channel → Channel
n ⨂ⁿ C = ⨂_ {n} (const C)

⨂≡ : ∀ {n} → {f g : Fin n → Channel} → (∀ k → f k ≡ g k) → ⨂ f ≡ ⨂ g
⨂≡ {zero} _ = refl
⨂≡ {suc _} p = cong₂ _⊗₀_ (p fzero) (⨂≡ (p ∘ fsuc))

⨂⇒ : ∀ {n m} {f : Fin n → Channel} k → f k [ m ]⇒[ m ] ⨂ f
⨂⇒ fzero = ⊗-right-intro
⨂⇒ (fsuc k) = ⨂⇒ k ⇒ₜ ⊗-left-intro
