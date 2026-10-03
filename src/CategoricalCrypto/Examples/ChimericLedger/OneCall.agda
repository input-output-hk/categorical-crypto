{-# OPTIONS --safe --without-K --guardedness #-}

-- A protocol whose every step is a `CategoricalCrypto.OracleCall.Call` asks at
-- most one query per activation and the answer to it only returns, so it is
-- 1-bounded.  The potential CANNOT be read off `Protocol.Machine.MSt`: its
-- `wait` holds the parked continuation as a FUNCTION over arbitrary call trees,
-- and a certificate must answer at every state, reachable or not — the
-- obstruction `Examples.MerkleDamgard.QueryBound`'s header records.  `QB`'s
-- `≈ᴹ`-closure is what that is for: `oneCallᴹ` is the same relay with its
-- suspension named by the continuation `fromCall` parks, whose potential is
-- constantly zero because no second call can follow.

open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.OracleCall
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Pointwise as Pw

module CategoricalCrypto.Examples.ChimericLedger.OneCall where

module _ {A B : Iface} (P : Protocol A B)
         (call₁ : St P → Neg B → Call (Neg A) (Pos A) (St P × Pos B))
         (factors : (s : St P) (b : Neg B) → step P s b ≡ fromCall (call₁ s b))
         where

  private
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

    oneCallᴹ : Proc A B
    oneCallᴹ = MC.mk (initˢ Sᴺ (inj₁ (init P))) stepᴺ

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
      ; cohL   = λ where (inj₁ _) _ → bot-bind-≈ₚ _
                         (inj₂ _) _ → >>=ₚ-identityˡ _ _
      ; cohR   = λ where (inj₁ s) b → onCall-coh (call₁ s b)
                         (inj₂ _) _ → bot-bind-≈ₚ _
      }
      where
      onL : (s : Sᴺ) (a : Pos A) → Dₚ (Answer (Φᴺ s))
      onL (inj₁ _) _ = botₚ
      onL (inj₂ k) a = returnₚ (inj₂ ((inj₁ (proj₁ (k a)) , z≤n) , proj₂ (k a)))

      onR : (s : Sᴺ) (b : Neg B) → Dₚ (Answer (Φᴺ s ℕ.+ 1))
      onR (inj₁ s) b = onCall (call₁ s b)
      onR (inj₂ _) _ = botₚ

    θᴺ : Sᴺ → MSt P
    θᴺ (inj₁ s) = idle s
    θᴺ (inj₂ k) = wait λ r → ret (k r)

    drive-one : (c : Call (Neg A) (Pos A) (St P × Pos B))
              → (returnₚ (driveᶜ c) >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id)) ≈ₚ drive P (fromCall c)
    drive-one (inj₁ x) = >>=ₚ-identityˡ _ _ ⟨≈⟩ Pw.⊗-pureˡ θᴺ (driveᶜ (inj₁ x))
    drive-one (inj₂ x) = >>=ₚ-identityˡ _ _ ⟨≈⟩ Pw.⊗-pureˡ θᴺ (driveᶜ (inj₂ x))

    θ-step : (z : Sᴺ × (Pos A ⊎ Neg B))
           → (stepᴺ z >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id))
             ≈ₚ ((K.pureᵏ θᴺ V.⊗₁ V.id) z >>=ₚ stepᴹ P)
    θ-step (inj₁ s , inj₂ b) =
      subst (λ t → (stepᴺ (inj₁ s , inj₂ b) >>=ₚ (K.pureᵏ θᴺ V.⊗₁ V.id)) ≈ₚ drive P t)
            (sym (factors s b)) (drive-one (call₁ s b))
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₁ s , inj₂ b)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₂ k , inj₁ a) =
      >>=ₚ-identityˡ _ _ ⟨≈⟩ Pw.⊗-pureˡ θᴺ (inj₁ (proj₁ (k a)) , inj₂ (proj₂ (k a)))
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₂ k , inj₁ a)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₁ s , inj₁ a) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₁ s , inj₁ a)) ⟨≈⟩ >>=ₚ-identityˡ _ _)
    θ-step (inj₂ k , inj₂ b) =
      bot-bind-≈ₚ _
      ⟨≈⟩ ≈sym (bindˣ (Pw.⊗-pureˡ θᴺ (inj₂ k , inj₂ b)) ⟨≈⟩ >>=ₚ-identityˡ _ _)

  qb-oneCall : QB 1 (morphism P)
  qb-oneCall = oneCallᴹ , certifiedᴺ
             , MS.≲⇒≈ᴹ (MS.sim (K.pureᵏ θᴺ) (KP.structural θᴺ) (λ _ → >>=ₚ-identityˡ (inj₁ (init P)) _) θ-step)
