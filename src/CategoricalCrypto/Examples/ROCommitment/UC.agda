{-# OPTIONS --safe --without-K --guardedness #-}

-- The corrupted-committer machines at the UC model, and what the extracting
-- simulator spends: `simExactHash`/`simExactAll` state the spend EXACTLY,
-- counting oracle relays and downward outputs of any kind
-- (`UC.QueryBound.Exact`), and `simCert` reads the second as the amortised
-- ceiling the grading asks for (`exact⇒certified`).  The
-- emulation is approximate (its ε is `Game.extraction-bound`), so there is no
-- `≈ᵁ` here.

open import Categories.LocallyGraded.SubCategory

open import Class.DecEq

open import Data.Bool.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Positive
open import Data.Product.Base
open import Data.Sum.Base hiding (map₂)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Dominated
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UC.QueryBound.Exact

module CategoricalCrypto.Examples.ROCommitment.UC (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open GradedSubCat gradingᵒ using (Pred)

------------------------------------------------------------------------
-- The images

realᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
realᵒ = gradedᵒ real

idealᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵ) (ifaceᵒ Honᴵ)
idealᵒ = gradedᵒ ideal

simᵒ : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ
simᵒ = procᵒ simulator

------------------------------------------------------------------------
-- The honest side: the receiver relays at most one query per message

-- An activation from above buys one downward oracle call and the answer to it
-- only returns, so the potential is constantly zero (`UC.QueryBound.qbᵢ-upward`,
-- the raw-machine counterpart of `qb-oneCall`).
recvCert : Certified 1 real
recvCert = qbᵢ-upward _ _ _ onL cohL
  where
  -- The letter is split before the state, so that a `cohL` clause at a
  -- VARIABLE state still reduces.
  onL : (s : RSt) (a : Pos Resᴵ) → Dₚ (Ans (λ _ → 0) (Neg Resᴵ) (Pos (Advᴵ ⊗ᴵ Honᴵ)) 0)
  onL _            rcptᴿ    = botₚ
  onL _            (outᴿ _) = botₚ
  onL _            rejᴿ     = botₚ
  onL (relayᴿ m)   (digᴿ d) = returnₚ (inj₂ ((waitᴿ m , z≤n) , inj₁ (ansᴬ d)))
  onL (checkᴿ c b) (digᴿ d) =
    returnₚ (inj₂ ((waitᴿ (just c) , z≤n) , inj₂ (verdict b ⌊ d ≟ c ⌋)))
  onL (waitᴿ _)    (digᴿ _) = botₚ

  cohL : (s : RSt) (a : Pos Resᴵ) → mapₚ forget (onL s a) ≈ₚ realStep (s , inj₁ a)
  cohL _            rcptᴿ    = bot-bind-≈ₚ _
  cohL _            (outᴿ _) = bot-bind-≈ₚ _
  cohL _            rejᴿ     = bot-bind-≈ₚ _
  cohL (relayᴿ _)   (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (checkᴿ _ _) (digᴿ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (waitᴿ _)    (digᴿ _) = bot-bind-≈ₚ _

recvQB : Pred 1⁺ (gradedᵒ real)
recvQB = qb-gradedᵒ (certified⇒QB recvCert)

resourceQBᵒ : Pred 1⁺ (procᵒ resource)
resourceQBᵒ = qbᵒ (qb-mono z≤n resourceQB)

------------------------------------------------------------------------
-- The allowance

-- An activation from above buys two downward messages; only the opening uses
-- both, and `checkˢ` is where the second one is still owed.
Φˢ : SSt → ℕ
Φˢ (waitˢ _ _)        = 0
Φˢ (relayˢ _ _ _)     = 0
Φˢ (checkˢ _ _ _ _ _) = 1

idealQB : QB 1 ideal
idealQB = qb-wire upᶠ downᶠ

------------------------------------------------------------------------
-- …exactly

-- One oracle relay (`hashes`) per adversary message that names a point
-- (`points`) — its own query, and the opening the receiver would have hashed
-- itself.
hashes : Neg Lkᴵ ⊎ Pos Advᴵ → ℕ
hashes (inj₁ (hashˢ _))   = 1
hashes (inj₁ (commitˢ _)) = 0
hashes (inj₁ openˢ)       = 0
hashes (inj₁ failˢ)       = 0
hashes (inj₂ _)           = 0

points : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
points (inj₁ _)           = 0
points (inj₂ (queryᴬ _))  = 1
points (inj₂ (commitᴬ _)) = 0
points (inj₂ (openᴬ _ _)) = 1

perMessage : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
perMessage (inj₁ _)           = 0
perMessage (inj₂ (queryᴬ _))  = 1
perMessage (inj₂ (commitᴬ _)) = 1
perMessage (inj₂ (openᴬ _ _)) = 2

Λᴴ : SSt → ℕ
Λᴴ _ = 0

pointˢ : Dₚ SSt
pointˢ = returnₚ (waitˢ [] nothing)

module EH = Ledger {Lkᴵ} {Advᴵ} SSt pointˢ simStep hashes points
module EA = Ledger {Lkᴵ} {Advᴵ} SSt pointˢ simStep downward perMessage

private
  hashes-release : (x y : Bool) → hashes (inj₁ (release x y)) ≡ 0
  hashes-release true  true  = refl
  hashes-release true  false = refl
  hashes-release false _     = refl

  st : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
     → Dₚ (Σ[ p ∈ SSt × (Neg Lkᴵ ⊎ Pos Advᴵ) ]
            (hashes (proj₂ p) + Λᴴ (proj₁ p) ≡ Λᴴ s + points x)
            × (downward (proj₂ p) + Φˢ (proj₁ p) ≡ Φˢ s + perMessage x))
  st (waitˢ L m) (inj₂ (queryᴬ x)) =
    returnₚ ((relayˢ x L m , inj₁ (hashˢ x)) , refl , refl)
  st (waitˢ L nothing) (inj₂ (commitᴬ c)) =
    returnₚ ((waitˢ L (just (c , extract c L)) , inj₁ (commitˢ (extract c L))) , refl , refl)
  st (waitˢ L (just (c , e))) (inj₂ (openᴬ b r)) =
    returnₚ ((checkˢ (b ∷ᵛ r) b L c e , inj₁ (hashˢ (b ∷ᵛ r))) , refl , refl)
  st (relayˢ x L m) (inj₁ (digˢ d)) =
    returnₚ ((waitˢ ((x , d) ∷ L) m , inj₂ (ansᴬ d)) , refl , refl)
  st (checkˢ x b L c e) (inj₁ (digˢ d)) =
    returnₚ ( (waitˢ ((x , d) ∷ L) (just (c , e))
              , inj₁ (release ⌊ d ≟ c ⌋ (not (b xor e))))
            , cong (_+ 0) (hashes-release ⌊ d ≟ c ⌋ (not (b xor e))) , refl )
  st _ _ = botₚ

  coh : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ) → mapₚ proj₁ (st s x) ≈ₚ simStep (s , x)
  coh (waitˢ _ _)        (inj₂ (queryᴬ _))  = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  coh (waitˢ _ nothing)  (inj₂ (commitᴬ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  coh (waitˢ _ (just _)) (inj₂ (openᴬ _ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  coh (relayˢ _ _ _)     (inj₁ (digˢ _))    = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  coh (checkˢ _ _ _ _ _) (inj₁ (digˢ _))    = >>=ₚ-identityˡ _ (returnₚ ∘′ proj₁)
  coh (waitˢ _ _)        (inj₁ (digˢ _))    = bot-bind-≈ₚ _
  coh (waitˢ _ (just _)) (inj₂ (commitᴬ _)) = bot-bind-≈ₚ _
  coh (waitˢ _ nothing)  (inj₂ (openᴬ _ _)) = bot-bind-≈ₚ _
  coh (relayˢ _ _ _)     (inj₂ (queryᴬ _))  = bot-bind-≈ₚ _
  coh (relayˢ _ _ _)     (inj₂ (commitᴬ _)) = bot-bind-≈ₚ _
  coh (relayˢ _ _ _)     (inj₂ (openᴬ _ _)) = bot-bind-≈ₚ _
  coh (checkˢ _ _ _ _ _) (inj₂ (queryᴬ _))  = bot-bind-≈ₚ _
  coh (checkˢ _ _ _ _ _) (inj₂ (commitᴬ _)) = bot-bind-≈ₚ _
  coh (checkˢ _ _ _ _ _) (inj₂ (openᴬ _ _)) = bot-bind-≈ₚ _

simExactHash : EH.QEᵢ
simExactHash = record
  { Λ = Λᴴ ; pointᴱ = returnₚ (waitˢ [] nothing , refl)
  ; coh₀ = >>=ₚ-identityˡ (waitˢ [] nothing , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = λ s x → mapₚ (map₂ proj₁) (st s x)
  ; cohᴱ = λ s x → map-map (st s x) (map₂ proj₁) proj₁ ⟨≈⟩ coh s x }

simExactAll : EA.QEᵢ
simExactAll = record
  { Λ = Φˢ ; pointᴱ = returnₚ (waitˢ [] nothing , refl)
  ; coh₀ = >>=ₚ-identityˡ (waitˢ [] nothing , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = λ s x → mapₚ (map₂ proj₂) (st s x)
  ; cohᴱ = λ s x → map-map (st s x) (map₂ proj₂) proj₁ ⟨≈⟩ coh s x }

simCert : Certified 2 simulator
simCert = exact⇒certified simExactAll (λ _ → refl) λ where
  (queryᴬ _)  → s≤s z≤n
  (commitᴬ _) → s≤s z≤n
  (openᴬ _ _) → s≤s (s≤s z≤n)

simQB : QB 2 simulator
simQB = certified⇒QB simCert

-- `Λᴴ` is 0 because each relay is issued in the step that pays for it.
sim-hash-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
               → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                      EH.Balanced Λᴴ (weight points w) p)
sim-hash-count = EH.exactᴱ simExactHash

sim-message-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
                  → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                         EA.Balanced Φˢ (weight perMessage w) p)
sim-message-count = EA.exactᴱ simExactAll
