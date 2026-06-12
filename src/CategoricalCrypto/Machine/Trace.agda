{-# OPTIONS --safe --no-require-unique-meta-solutions #-}

-- Pointed machines and finite-trace (run) equivalence.
--
-- A pointed machine is a machine together with an initial state — the
-- data that `Machine→Kl` (in `Machine.Category`) needs to read a
-- machine as a hom of the Maybe-graded Kleisli category over the
-- G-construction. `RunRel` is the machine's finite I/O behaviour: the
-- relational analogue, clause for clause, of the monadic list-trace
-- `SFunM.trace` that underlies the construction's hom equality `_≈ᵉ_`.
--
-- Trace equivalence `_≈ᵗ_` (equality of finite-run behaviour from the
-- initial states) is the M-free shadow of that hom equality: the
-- bridge `≈ᴹᴴ-Kl⇒≈ᵗ` in `Machine.Category` shows that machines whose
-- Kleisli images are `_≈ᴹᴴ-Kl_`-equal are trace equivalent. It sits
-- strictly below bisimulation: `≅ᴹ⇒≈ᵗ` below maps any init-respecting
-- machine isomorphism to a trace equivalence, while the classical
-- branching-time counterexamples separate the two for nondeterministic
-- step relations.
--
-- The pointed category operations `idᵖ`/`_∘ᵖ_` satisfy the identity
-- and associativity laws up to `_≈ᵗ_` (transported from the `_≅ᴹ_`
-- bisimulations of `Machine.Iso`). What is *not* provable here is that
-- `_∘ᵖ_` is a congruence for `_≈ᵗ_` — trace equivalence of composites
-- is a statement about decomposing interleaved feedback chains, not
-- about state bijections — so this module exposes no `Category`
-- record. The category carrying the construction's equality lives on
-- the Kleisli side: see `MaybeHomKlCategory` in `Machine.Category`.

module CategoricalCrypto.Machine.Trace where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Relation.Binary using (IsEquivalence)

open import CategoricalCrypto.Channel.Core using (Channel)
open import CategoricalCrypto.Machine.Core as MC using (Machine; MkMachine; _⊗ᵀ_)
open import CategoricalCrypto.Machine.Iso

open _≅ᴹ_

private variable A B C D : Channel

-- A pointed machine: a machine with a chosen initial state.
record Machineᵖ (A B : Channel) : Type₁ where
  constructor MkMachineᵖ
  field
    machine : Machine A B
    init    : Machine.State machine

open Machineᵖ public

-- The finite-run relation: `RunRel m s tr` holds when `m` can step
-- through the (input, optional output) pairs of `tr` in order,
-- starting from state `s`. One step per input — the same lockstep
-- discipline as the monadic list-trace `SFunM.trace`.
RunRel : (m : Machine A B) → Machine.State m
       → List (Channel.inType (A ⊗ᵀ B) × Maybe (Channel.outType (A ⊗ᵀ B)))
       → Type
RunRel m s []              = ⊤
RunRel m s ((i , mo) ∷ tr) =
  ∃ λ s' → Machine.stepRel m s i mo s' × RunRel m s' tr

-- Trace equivalence of pointed machines: the same finite runs are
-- possible from the initial states. Stated as two implications so it
-- does not depend on a particular `_⇔_` definition.
infix 4 _≈ᵗ_

record _≈ᵗ_ (m₁ m₂ : Machineᵖ A B) : Type where
  constructor MkTraceEq
  field
    runs-to   : ∀ {tr} → RunRel (machine m₁) (init m₁) tr
                       → RunRel (machine m₂) (init m₂) tr
    runs-from : ∀ {tr} → RunRel (machine m₂) (init m₂) tr
                       → RunRel (machine m₁) (init m₁) tr

open _≈ᵗ_ public

≈ᵗ-refl : {m : Machineᵖ A B} → m ≈ᵗ m
≈ᵗ-refl = MkTraceEq (λ r → r) (λ r → r)

≈ᵗ-sym : {m₁ m₂ : Machineᵖ A B} → m₁ ≈ᵗ m₂ → m₂ ≈ᵗ m₁
≈ᵗ-sym p = MkTraceEq (runs-from p) (runs-to p)

≈ᵗ-trans : {m₁ m₂ m₃ : Machineᵖ A B} → m₁ ≈ᵗ m₂ → m₂ ≈ᵗ m₃ → m₁ ≈ᵗ m₃
≈ᵗ-trans p q = MkTraceEq (λ r → runs-to q (runs-to p r))
                         (λ r → runs-from p (runs-from q r))

≈ᵗ-isEquivalence : IsEquivalence (_≈ᵗ_ {A} {B})
≈ᵗ-isEquivalence = record
  { refl = ≈ᵗ-refl ; sym = ≈ᵗ-sym ; trans = ≈ᵗ-trans }

------------------------------------------------------------------------
-- Bisimulation implies trace equivalence: an init-respecting `_≅ᴹ_`
-- maps runs to runs in both directions. (The converse fails for
-- nondeterministic step relations — trace equivalence is the strictly
-- coarser, linear-time notion.)

module _ {m₁ m₂ : Machine A B} (φ : m₁ ≅ᴹ m₂) where

  private
    runs-to-φ : ∀ s {tr} → RunRel m₁ s tr → RunRel m₂ (to φ s) tr
    runs-to-φ s {[]}            _            = tt
    runs-to-φ s {(i , mo) ∷ tr} (s' , p , r) =
      to φ s' , step-to φ p , runs-to-φ s' r

    runs-from-φ : ∀ s {tr} → RunRel m₂ s tr → RunRel m₁ (from φ s) tr
    runs-from-φ s {[]}            _            = tt
    runs-from-φ s {(i , mo) ∷ tr} (s' , p , r) =
      from φ s' , step-from φ p , runs-from-φ s' r

  ≅ᴹ⇒≈ᵗ : {s₁ : Machine.State m₁} {s₂ : Machine.State m₂}
        → to φ s₁ ≡ s₂
        → MkMachineᵖ m₁ s₁ ≈ᵗ MkMachineᵖ m₂ s₂
  ≅ᴹ⇒≈ᵗ {s₁} {s₂} eq = MkTraceEq
    (λ r → subst (λ s → RunRel m₂ s _) eq (runs-to-φ s₁ r))
    (λ r → subst (λ s → RunRel m₁ s _)
             (trans (cong (from φ) (sym eq)) (from∘to φ s₁))
             (runs-from-φ s₂ r))

------------------------------------------------------------------------
-- Pointed category operations. The composite's initial state pairs
-- the components' (the composite state of `MC._∘_` is
-- `State m₂ × State m₁`).

idᵖ : Machineᵖ A A
idᵖ = MkMachineᵖ MC.id tt

infixr 9 _∘ᵖ_

_∘ᵖ_ : Machineᵖ B C → Machineᵖ A B → Machineᵖ A C
MkMachineᵖ m₁ s₁ ∘ᵖ MkMachineᵖ m₂ s₂ = MkMachineᵖ (m₁ MC.∘ m₂) (s₂ , s₁)

-- The identity and associativity laws at `_≈ᵗ_`, transported from the
-- machine-level bisimulations. The init side conditions are `refl`:
-- each iso's state map sends the composite's initial state to the
-- expected one (`proj₁`/`proj₂` for the identity laws, the canonical
-- reassociation for `∘-assoc-≅ᴹ`).

opaque
  unfolding ∘-identityˡ-≅ᴹ ∘-identityʳ-≅ᴹ

  ∘ᵖ-identityˡ-≈ᵗ : {m : Machineᵖ A B} → (idᵖ ∘ᵖ m) ≈ᵗ m
  ∘ᵖ-identityˡ-≈ᵗ {m = MkMachineᵖ m s} = ≅ᴹ⇒≈ᵗ ∘-identityˡ-≅ᴹ refl

  ∘ᵖ-identityʳ-≈ᵗ : {m : Machineᵖ A B} → (m ∘ᵖ idᵖ) ≈ᵗ m
  ∘ᵖ-identityʳ-≈ᵗ {m = MkMachineᵖ m s} = ≅ᴹ⇒≈ᵗ ∘-identityʳ-≅ᴹ refl

∘ᵖ-assoc-≈ᵗ : {f : Machineᵖ A B} {g : Machineᵖ B C} {h : Machineᵖ C D}
            → ((h ∘ᵖ g) ∘ᵖ f) ≈ᵗ (h ∘ᵖ (g ∘ᵖ f))
∘ᵖ-assoc-≈ᵗ {f = MkMachineᵖ f sf} {MkMachineᵖ g sg} {MkMachineᵖ h sh} =
  ≅ᴹ⇒≈ᵗ ∘-assoc-≅ᴹ refl
