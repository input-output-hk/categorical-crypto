{-# OPTIONS --safe --without-K #-}

-- Oracle signatures: a set of channels, each with its own query and reply
-- type — CryptHOL's interface types (lochbihler2019cc §IV-B), SSP's named
-- oracles (brzuska2018 Def. 3).  The reply type depends on the channel, which
-- is what lets a tensor answer each query on the channel it was asked on
-- (`docs/uc-setup-ssp.md` §3.1).
--
-- `_⇒ᴵ_` are container morphisms: channels and queries forward, replies
-- backward.  The flat `CategoricalCrypto.Iface` is the one-channel case
-- (`oneᴵ`), and `flat` is the wire format of the machine layer.

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.Product.Base using (Σ)
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base using (_∘_; const; id)

import CategoricalCrypto.Iface as Flat

module CategoricalCrypto.SSP.Iface where

infix  4 _⇒ᴵ_
infixr 9 _∘ᴵ_
infixr 10 _⊗ᴵ_ _⊗ᴵᴵ_

record Iface : Set₁ where
  field Ch : Set
        Q R : Ch → Set
open Iface public

unitᴵ Ωᴵ : Iface
unitᴵ = record { Ch = ⊥ ; Q = λ () ; R = λ () }
Ωᴵ = record { Ch = ⊤ ; Q = const ⊤ ; R = const Bool }

_⊗ᴵ_ : Iface → Iface → Iface
A ⊗ᴵ B = record { Ch = Ch A ⊎ Ch B ; Q = [ Q A , Q B ]′ ; R = [ R A , R B ]′ }

record _⇒ᴵ_ (A B : Iface) : Set where
  field ch : Ch A → Ch B
        qu : ∀ {c} → Q A c → Q B (ch c)
        re : ∀ {c} → R B (ch c) → R A c
open _⇒ᴵ_ public

private variable A B C D : Iface

idᴵ : A ⇒ᴵ A
idᴵ = record { ch = id ; qu = id ; re = id }

_∘ᴵ_ : B ⇒ᴵ C → A ⇒ᴵ B → A ⇒ᴵ C
m ∘ᴵ n = record { ch = ch m ∘ ch n ; qu = qu m ∘ qu n ; re = re n ∘ re m }

_⊗ᴵᴵ_ : A ⇒ᴵ B → C ⇒ᴵ D → A ⊗ᴵ C ⇒ᴵ B ⊗ᴵ D
m ⊗ᴵᴵ n = record
  { ch = map (ch m) (ch n)
  ; qu = λ { {inj₁ _} → qu m ; {inj₂ _} → qu n }
  ; re = λ { {inj₁ _} → re m ; {inj₂ _} → re n } }

ι₁ : A ⇒ᴵ A ⊗ᴵ B
ι₁ = record { ch = inj₁ ; qu = id ; re = id }

ι₂ : B ⇒ᴵ A ⊗ᴵ B
ι₂ = record { ch = inj₂ ; qu = id ; re = id }

∇ : A ⊗ᴵ A ⇒ᴵ A
∇ = record
  { ch = reduce
  ; qu = λ { {inj₁ _} → id ; {inj₂ _} → id }
  ; re = λ { {inj₁ _} → id ; {inj₂ _} → id } }

-- The inverses of `λᴵ` and `ρᴵ` are `ι₂` and `ι₁`.
λᴵ : unitᴵ ⊗ᴵ A ⇒ᴵ A
λᴵ = record
  { ch = [ ⊥-elim , id ]′
  ; qu = λ { {inj₁ ()} ; {inj₂ _} → id }
  ; re = λ { {inj₁ ()} ; {inj₂ _} → id } }

ρᴵ : A ⊗ᴵ unitᴵ ⇒ᴵ A
ρᴵ = record
  { ch = [ id , ⊥-elim ]′
  ; qu = λ { {inj₁ _} → id ; {inj₂ ()} }
  ; re = λ { {inj₁ _} → id ; {inj₂ ()} } }

αᴵ : (A ⊗ᴵ B) ⊗ᴵ C ⇒ᴵ A ⊗ᴵ (B ⊗ᴵ C)
αᴵ = record
  { ch = assocʳ
  ; qu = λ { {inj₁ (inj₁ _)} → id ; {inj₁ (inj₂ _)} → id ; {inj₂ _} → id }
  ; re = λ { {inj₁ (inj₁ _)} → id ; {inj₁ (inj₂ _)} → id ; {inj₂ _} → id } }

αᴵ⁻¹ : A ⊗ᴵ (B ⊗ᴵ C) ⇒ᴵ (A ⊗ᴵ B) ⊗ᴵ C
αᴵ⁻¹ = record
  { ch = assocˡ
  ; qu = λ { {inj₁ _} → id ; {inj₂ (inj₁ _)} → id ; {inj₂ (inj₂ _)} → id }
  ; re = λ { {inj₁ _} → id ; {inj₂ (inj₁ _)} → id ; {inj₂ (inj₂ _)} → id } }

swapᴵ : A ⊗ᴵ B ⇒ᴵ B ⊗ᴵ A
swapᴵ = record
  { ch = swap
  ; qu = λ { {inj₁ _} → id ; {inj₂ _} → id }
  ; re = λ { {inj₁ _} → id ; {inj₂ _} → id } }

oneᴵ : Flat.Iface → Iface
oneᴵ A = record { Ch = ⊤ ; Q = const (Flat.Neg A) ; R = const (Flat.Pos A) }

flat : Iface → Flat.Iface
flat A = Σ (Ch A) (R A) Flat.⇿ Σ (Ch A) (Q A)
