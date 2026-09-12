{-# OPTIONS --safe --without-K --guardedness #-}

-- What the ledger costs its hash: one call per activation, hence `QB 1`.
--
-- The bound is the general fact about a protocol whose every step is a
-- `CategoricalCrypto.OracleCall.Call` — at most one query, and the answer ends
-- the activation.  As at `Examples.MerkleDamgard.QueryBound` the potential
-- CANNOT be read off `Protocol.Machine.MSt`: its `wait` holds the parked
-- continuation as a FUNCTION over arbitrary call trees, and a certificate must
-- answer at every state, reachable or not.  `QB`'s `≈ᴹ`-closure is what that is
-- for — `oneCallᴹ` is the same relay with its suspension named by the
-- continuation `fromCall` parked, whose potential is constantly zero because no
-- second call can follow.
--
-- `qb-oneCall` is stated over an arbitrary protocol and belongs in
-- `UC.QueryBound` beside `qbᵢ-wire`/`qbᵢ-closed`; it is here only because this
-- branch does not own that module (`QUALITY-REVIEW.md`).

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using () renaming (zero to fzero)
open import Data.List.Base using (List)
open import Data.Nat.Base as ℕ using (ℕ; z≤n; s≤s)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Examples.ChimericLedger
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Col
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.ChimericLedger.QueryBound where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})

------------------------------------------------------------------------
-- One call per activation

-- `call₁` is the protocol's step written in `Call` rather than in `Calls`: a
-- protocol IS one-shot exactly when its step factors through `fromCall`.
module OneCall {A B : Iface} (P : Protocol A B)
               (call₁ : St P → Neg B → Call (Neg A) (Pos A) (St P × Pos B))
               (factors : (s : St P) (b : Neg B) → step P s b ≡ fromCall (call₁ s b))
               where

  private
    -- Idle at a protocol state, or suspended on the ONE continuation the call
    -- parked — where `MSt`'s `wait` holds an arbitrary residual tree.
    Sᴺ : Set
    Sᴺ = St P ⊎ (Pos A → St P × Pos B)

    driveᶜ : Call (Neg A) (Pos A) (St P × Pos B) → Sᴺ × (Neg A ⊎ Pos B)
    driveᶜ (inj₁ (s , b)) = inj₁ s , inj₂ b
    driveᶜ (inj₂ (q , k)) = inj₂ k , inj₁ q

    stepᴺ : Sᴺ × (Pos A ⊎ Neg B) → Dₚ (Sᴺ × (Neg A ⊎ Pos B))
    stepᴺ (inj₁ s , inj₂ b) = returnₚ (driveᶜ (call₁ s b))
    stepᴺ (inj₂ k , inj₁ a) = returnₚ (inj₁ (proj₁ (k a)) , inj₂ (proj₂ (k a)))
    stepᴺ (inj₁ _ , inj₁ _) = botₚ
    stepᴺ (inj₂ _ , inj₂ _) = botₚ

    stateᴺ : MC.State
    stateᴺ = record
      { obj = Sᴺ ; point = λ _ → returnₚ (inj₁ (init P)) ; discard = λ _ → returnₚ ttᵛ }

    oneCallᴹ : Proc A B
    oneCallᴹ = MC.mk stateᴺ stepᴺ

    -- Nothing is ever owed: the one unit an activation deposits is spent on the
    -- call it makes, and the answer to that call only returns.
    Φᴺ : Sᴺ → ℕ
    Φᴺ _ = 0

    Answer = Ans Φᴺ (Neg A) (Pos B)

    onCall : (c : Call (Neg A) (Pos A) (St P × Pos B)) → Dₚ (Answer 1)
    onCall (inj₁ (s , b)) = returnₚ (inj₂ ((inj₁ s , z≤n) , b))
    onCall (inj₂ (q , k)) = returnₚ (inj₁ ((inj₂ k , s≤s z≤n) , q))

    onCall-coh : (c : Call (Neg A) (Pos A) (St P × Pos B))
               → mapₚ forget (onCall c) ≈ₚ returnₚ (driveᶜ c)
    onCall-coh (inj₁ _) = >>=ₚ-identityˡ _ _
    onCall-coh (inj₂ _) = >>=ₚ-identityˡ _ _

    certifiedᴺ : Certified 1 oneCallᴹ
    certifiedᴺ = record
      { Φ      = Φᴺ
      ; pointᵍ = returnₚ (inj₁ (init P) , z≤n)
      ; coh₀   = >>=ₚ-identityˡ _ _
      ; onLᵍ   = onL
      ; onRᵍ   = onR
      ; cohL   = cohL
      ; cohR   = cohR
      }
      where
      onL : (s : Sᴺ) (a : Pos A) → Dₚ (Answer (Φᴺ s))
      onL (inj₁ _) _ = botₚ
      onL (inj₂ k) a = returnₚ (inj₂ ((inj₁ (proj₁ (k a)) , z≤n) , proj₂ (k a)))

      onR : (s : Sᴺ) (b : Neg B) → Dₚ (Answer (Φᴺ s ℕ.+ 1))
      onR (inj₁ s) b = onCall (call₁ s b)
      onR (inj₂ _) _ = botₚ

      cohL : (s : Sᴺ) (a : Pos A) → mapₚ forget (onL s a) ≈ₚ stepᴺ (s , inj₁ a)
      cohL (inj₁ _) _ = bot-bind-≈ₚ _
      cohL (inj₂ _) _ = >>=ₚ-identityˡ _ _

      cohR : (s : Sᴺ) (b : Neg B) → mapₚ forget (onR s b) ≈ₚ stepᴺ (s , inj₂ b)
      cohR (inj₁ s) b = onCall-coh (call₁ s b)
      cohR (inj₂ _) _ = bot-bind-≈ₚ _

    θᴺ : Sᴺ → MSt P
    θᴺ (inj₁ s) = idle s
    θᴺ (inj₂ k) = wait λ r → ret (k r)

    -- Both drives land on the same pair, `θᴺ` rebuilding precisely the
    -- continuation `fromCall` parks.
    drive-one : (c : Call (Neg A) (Pos A) (St P × Pos B))
              → (returnₚ (driveᶜ c) >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id)) ≈ₚ drive P (fromCall c)
    drive-one (inj₁ x) = >>=ₚ-identityˡ _ _ ⟨≈⟩ Col.⊗-pureˡ θᴺ (driveᶜ (inj₁ x))
    drive-one (inj₂ x) = >>=ₚ-identityˡ _ _ ⟨≈⟩ Col.⊗-pureˡ θᴺ (driveᶜ (inj₂ x))

    θ-step : (z : Sᴺ × (Pos A ⊎ Neg B))
           → (stepᴺ z >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id))
             ≈ₚ ((K.pureᵏ θᴺ V.⊗₁ V.id) z >>=ₚ stepᴹ P)
    θ-step (inj₁ s , inj₂ b) =
      subst (λ t → (stepᴺ (inj₁ s , inj₂ b) >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id)) ≈ₚ drive P t)
            (sym (factors s b)) (drive-one (call₁ s b))
      ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴺ (inj₁ s , inj₂ b)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₂ k , inj₁ a) =
      >>=ₚ-identityˡ _ _ ⟨≈⟩ Col.⊗-pureˡ θᴺ (inj₁ (proj₁ (k a)) , inj₂ (proj₂ (k a)))
      ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴺ (inj₂ k , inj₁ a)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₁ s , inj₁ a) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴺ (inj₁ s , inj₁ a)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₂ k , inj₂ b) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴺ (inj₂ k , inj₂ b)) ⟨≈⟩ >>=ₚ-identityˡ _ _)

    θ-sim : oneCallᴹ S.≲ morphism P
    θ-sim = S.sim (K.pureᵏ θᴺ) (KP.structural θᴺ)
                  (λ r → >>=ₚ-identityˡ (θᴺ r) _)
                  (λ _ → >>=ₚ-identityˡ (inj₁ (init P)) _)
                  θ-step

  qb-oneCall : QB 1 (morphism P)
  qb-oneCall = oneCallᴹ , certifiedᴺ , S.≲⇒≈ᴹ θ-sim

open OneCall public using (qb-oneCall)

------------------------------------------------------------------------
-- …at the ledger

module _ (ℓ : ℕ) (ser : Ledger.Tx ℓ → List Bool) where

  open Ledger ℓ
  open Step ser
  open import CategoricalCrypto.Examples.ChimericLedger.POV ℓ ser

  -- `submit` hashes once, `audit` answers purely: `POV.ledger`'s step is
  -- `fromCall` of this, on the nose.
  ledgerCall : (vr : Variant) → LState → Query → Call (Neg HashIf) (Pos HashIf) (LState × Answer)
  ledgerCall vr s (submit tx) =
    reCall (fzero ,_) proj₂ (mapCall (λ sb → proj₁ sb , ok (proj₂ sb)) (applyTx vr s tx))
  ledgerCall _  s audit       = pureᶜ (s , totalIs (total s))

  qb-ledger : (vr : Variant) (s₀ : LState) → QB 1 (morphism (ledger vr s₀))
  qb-ledger vr s₀ = qb-oneCall (ledger vr s₀) (ledgerCall vr) factors
    where
    factors : (s : LState) (q : Query) → step (ledger vr s₀) s q ≡ fromCall (ledgerCall vr s q)
    factors _ (submit _) = refl
    factors _ audit      = refl
