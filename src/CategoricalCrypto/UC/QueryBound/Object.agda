{-# OPTIONS --safe --without-K --guardedness #-}

-- `UC.QueryBound`'s hom-level predicate at 𝒢's OWN objects.
--
-- `⟦_⟧ᴵ` and `retᴵ` are definitional inverses (`UC.Machine`'s header), so a
-- query bound stated over `Iface`s and one stated over 𝒢-objects are the same
-- predicate; what differs is which spelling a consumer's statement must carry.
-- The ancilla action lives on 𝒢's objects, so the graded subcategory needs
-- THIS spelling in its field types; `UC.Machine.Grading`'s header records the
-- cost of the `Iface` form.
--
-- Keep that re-indexing opaque: reducing `QBᴳ` at a tensor-produced object
-- otherwise makes conversion invert the composite machine interface.  The two
-- image bridges expose the definitional inverse only inside this module's
-- controlled unfolding block.

open import Categories.Category

open import Data.Nat.Base as ℕ
open import Level

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.QueryBound.Object where

private module 𝒢 = Category (𝒢ₚ 0ℓ)

Certifiedᴳ : (A B : 𝒢.Obj) → ℕ → 𝒢ₚ 0ℓ [ A , B ] → Set
Certifiedᴳ A B = Certified {retᴵ A} {retᴵ B}

opaque
  QBᴳ : (A B : 𝒢.Obj) → ℕ → 𝒢ₚ 0ℓ [ A , B ] → Set₁
  QBᴳ A B = QB {retᴵ A} {retᴵ B}

opaque
  unfolding QBᴳ

  certified⇒QBᴳ : (A B : 𝒢.Obj) {c : ℕ} {M : 𝒢ₚ 0ℓ [ A , B ]}
                → Certifiedᴳ A B c M → QBᴳ A B c M
  certified⇒QBᴳ A B = certified⇒QB {retᴵ A} {retᴵ B}

  qb-resp-≈ᴳ : (A B : 𝒢.Obj) {c : ℕ} {M N : 𝒢ₚ 0ℓ [ A , B ]}
             → 𝒢ₚ 0ℓ [ M ≈ N ] → QBᴳ A B c M → QBᴳ A B c N
  qb-resp-≈ᴳ A B = qb-resp-≈ {retᴵ A} {retᴵ B}

  qb-monoᴳ : (A B : 𝒢.Obj) {c c′ : ℕ} {M : 𝒢ₚ 0ℓ [ A , B ]}
           → c ℕ.≤ c′ → QBᴳ A B c M → QBᴳ A B c′ M
  qb-monoᴳ A B = qb-mono {retᴵ A} {retᴵ B}

  qb-idᴳ : (A : 𝒢.Obj) → QBᴳ A A 1 (𝒢.id {A})
  qb-idᴳ A = qb-idᴹ {retᴵ A}

  qb-to-image : (A B : Iface) {c : ℕ} {M : 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]}
              → QB {A} {B} c M → QBᴳ ⟦ A ⟧ᴵ ⟦ B ⟧ᴵ c M
  qb-to-image A B q = q

  qb-from-image : (A B : Iface) {c : ℕ} {M : 𝒢ₚ 0ℓ [ ⟦ A ⟧ᴵ , ⟦ B ⟧ᴵ ]}
                → QBᴳ ⟦ A ⟧ᴵ ⟦ B ⟧ᴵ c M → QB {A} {B} c M
  qb-from-image A B q = q
