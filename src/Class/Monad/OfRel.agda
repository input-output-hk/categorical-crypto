{-# OPTIONS --safe #-}

-- "Relations-into-M" typeclass.
--
-- A `MonadOfRel M` is the structural assumption needed to encode an
-- arbitrary relation/predicate `P : A → Type` as a value of `M A`, and
-- to read membership back out. It captures the bridge from a
-- *relation* (Machine.stepRel) to a *function into M* (SFunᵉ.fun) —
-- see `CategoricalCrypto.Machine.Category` for the intended use.
--
-- For the canonical instance `M A = A → Type` (the predicate /
-- power-set monad), of-rel = id, member a m = m a, and both laws hold
-- definitionally. Other monads either don't admit a `MonadOfRel` at
-- all (e.g. Identity, Maybe in general) or admit one only with
-- restrictions.

open import categorical-crypto.Prelude

open import Class.Core
open import Class.Monad
open import Class.Prelude using (Typeω)

module Class.Monad.OfRel where

record MonadOfRel (M : Type↑) ⦃ Monad-M : Monad M ⦄ : Typeω where
  field
    -- Encode a predicate `P` as an M-value over its support.
    of-rel : ∀ {A : Type} → (A → Type) → M A

    -- Membership: "a is one of the values m might produce".
    member : ∀ {A : Type} → A → M A → Type

    -- Membership in `of-rel P` is exactly `P`. Stated as two
    -- implications so it does not depend on a particular `_⇔_`
    -- definition.
    of-rel-sound    : ∀ {A : Type} {P : A → Type} {a : A}
                    → P a → member a (of-rel P)
    of-rel-complete : ∀ {A : Type} {P : A → Type} {a : A}
                    → member a (of-rel P) → P a

    -- Extensionality: an M-value is the "of-rel" of its membership.
    -- (This is the key law that makes the Machine ↔ MaybeHom
    -- round-trip propositionally inverse on M-values.)
    member-η : ∀ {A : Type} (m : M A)
             → of-rel (λ a → member a m) ≡ m

    -- `member` is a monad morphism into the predicate monad:
    -- membership of `return` and `_>>=_` computes as expected. For the
    -- canonical instance (return a = (_≡ a), (m >>= f) b = ∃ a → m a ×
    -- f a b) all four hold by construction. These laws drive the
    -- "construction equality implies trace equivalence" bridge in
    -- `CategoricalCrypto.Machine.Category` (`≈ᴹᴴ-Kl⇒≈ᵗ`), where the
    -- membership of a monadic list-trace is computed step by step.
    return-member : ∀ {A : Type} {a : A} → member a (return a)
    member-return : ∀ {A : Type} {a b : A}
                  → member a (return b) → a ≡ b
    >>=-member    : ∀ {A B : Type} {m : M A} {f : A → M B} {a : A} {b : B}
                  → member a m → member b (f a) → member b (m >>= f)
    member->>=    : ∀ {A B : Type} {m : M A} {f : A → M B} {b : B}
                  → member b (m >>= f) → ∃ λ a → member a m × member b (f a)

open MonadOfRel ⦃...⦄ public
