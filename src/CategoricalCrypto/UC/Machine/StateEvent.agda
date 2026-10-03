{-# OPTIONS --safe --without-K --guardedness #-}

-- State predicates over machine PRESENTATIONS, and the flag-wire machine that
-- turns a Boolean state test into an interface event
-- (`docs/state-event-contract.md`).
--
-- A predicate lives on one representative's state type and moves only along
-- the pure state map of a simulation (`pullTest`).  Machine equality does not
-- transport it: an erased state component gives no descent
-- (`UC.Machine.StateEvent.HitTests.ghost-no-descent`).
--
-- `M ▷ P` samples `P` at the initial state, which may be effectful, and at
-- every COMPLETED ACTIVATION — an answer on `B` — and answers the accumulated
-- flag on one extra `Ωᴵ` port, asked for by a tick.  The sampling
-- boundary is this fixed convention, so a simulation is boundary-compatible as
-- soon as it preserves the test: it preserves the step's output letter
-- (`▷-≲`).  Reading the flag of a composite is `UC.Machine.StateEvent.Read`.

open import Data.Bool.Base
open import Data.Product.Base
open import Data.Sum.Base hiding (map₁)
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Protocol.Machine.Run
open import CategoricalCrypto.UC.Machine

module CategoricalCrypto.UC.Machine.StateEvent where

------------------------------------------------------------------------
-- Predicates and tests, reindexed along simulations

module _ {A B : Iface} where

  StateTest : Proc A B → Set
  StateTest M = MC.St M → Bool

  pullTest : {M N : Proc A B} (σ : M S.≲ N) → StateTest N → StateTest M
  pullTest σ Q = Q ∘ ϕ σ

------------------------------------------------------------------------
-- Event-compatible simulations

Annotated : Iface → Iface → Set₁
Annotated A B = Σ[ M ∈ Proc A B ] StateTest M

record EventSim {A B : Iface} (x y : Annotated A B) : Set₁ where
  field
    sim    : proj₁ x S.≲ proj₁ y
    compat : (s : MC.St (proj₁ x)) → proj₂ x s ≡ proj₂ y (ϕ sim s)

open EventSim public

module _ {A B : Iface} where

  eventSim-refl : {x : Annotated A B} → EventSim x x
  eventSim-refl = record { sim = S.≲-refl ; compat = λ _ → refl }

  eventSim-trans : {x y z : Annotated A B} → EventSim x y → EventSim y z → EventSim x z
  eventSim-trans σ τ = record { sim = S.≲-trans (sim σ) (sim τ) ; compat = λ s → trans (compat σ s) (compat τ _) }

------------------------------------------------------------------------
-- The flag-wire machine

module _ {A B : Iface} (M : Proc A B) (P : StateTest M) where

  sample : Bool → MC.St M × (Neg A ⊎ Pos B) → (MC.St M × Bool) × (Neg A ⊎ (Pos B ⊎ Bool))
  sample f (s , inj₁ a) = (s , f) , inj₁ a
  sample f (s , inj₂ b) = (s , f ∨ P s) , inj₂ (inj₁ b)

  ▷step : (MC.St M × Bool) × (Pos A ⊎ (Neg B ⊎ ⊤)) → Dₚ ((MC.St M × Bool) × (Neg A ⊎ (Pos B ⊎ Bool)))
  ▷step ((s , f) , inj₁ a)        = mapₚ (sample f) (MC.step M (s , inj₁ a))
  ▷step ((s , f) , inj₂ (inj₁ b)) = mapₚ (sample f) (MC.step M (s , inj₂ b))
  ▷step ((s , f) , inj₂ (inj₂ _)) = returnₚ ((s , f) , inj₂ (inj₂ f))

  ▷state : MC.State
  ▷state = record { obj = MC.St M × Bool ; point = λ x → mapₚ (λ s → s , P s) (MC.point (MC.state M) x) }

  infixl 8 _▷_

  _▷_ : Proc A (B ⊗ᴵ Ωᴵ)
  _▷_ = MC.mk ▷state ▷step

------------------------------------------------------------------------
-- A compatible simulation lifts

module _ {A B : Iface} {M N : Proc A B} {P : StateTest M} {Q : StateTest N}
         (e : EventSim (M , P) (N , Q)) where

  private
    σ = sim e

    pad : {Z : Set} → (MC.St M × Bool) × Z → Dₚ ((MC.St N × Bool) × Z)
    pad r = returnₚ (map₁ (ϕ σ) (proj₁ r) , proj₂ r)

    agree : (f : Bool) (r : MC.St M × (Neg A ⊎ Pos B))
          → pad (sample M P f r) ≈ₚ (padϕ (ϕ σ) r >>=ₚ returnₚ ∘ sample N Q f)
    agree f (s , inj₁ a) = ≈sym (>>=ₚ-identityˡ _ _)
    agree f (s , inj₂ b) = ret≡ (cong (λ z → (ϕ σ s , f ∨ z) , inj₂ (inj₁ b)) (compat e s))
                       ⟨≈⟩ ≈sym (>>=ₚ-identityˡ _ _)

    go : (s : MC.St M) (f : Bool) (x : Pos A ⊎ Neg B)
       → (mapₚ (sample M P f) (MC.step M (s , x)) >>=ₚ pad)
         ≈ₚ mapₚ (sample N Q f) (MC.step N (ϕ σ s , x))
    go s f x = bind-map (MC.step M (s , x)) _ _
           ⟨≈⟩ bindᶠ (agree f)
           ⟨≈⟩ ≈sym (>>=ₚ-assoc (MC.step M (s , x)) _ _)
           ⟨≈⟩ bindˣ (step-sim σ (s , x))

  ▷-≲ : (M ▷ P) S.≲ (N ▷ Q)
  ▷-≲ = simFn (map₁ (ϕ σ)) pt st
    where
    -- Named on purpose: inlined into `simFn`, this module's check takes 184 s, not 18 s.
    pt : (x : _) → (MC.point (▷state M P) x >>=ₚ λ s → returnₚ (map₁ (ϕ σ) s)) ≈ₚ MC.point (▷state N Q) x
    pt x = bind-map (MC.point (MC.state M) x) _ _
       ⟨≈⟩ bindᶠ (λ s → ret≡ (cong (ϕ σ s ,_) (compat e s)))
       ⟨≈⟩ ≈sym (bind-map (MC.point (MC.state M) x) (ϕ σ) _)
       ⟨≈⟩ bindˣ (point-sim σ)

    st : (p : _) → _
    st ((s , f) , inj₁ a)        = go s f (inj₁ a)
    st ((s , f) , inj₂ (inj₁ b)) = go s f (inj₂ b)
    st ((s , f) , inj₂ (inj₂ _)) = >>=ₚ-identityˡ _ _
