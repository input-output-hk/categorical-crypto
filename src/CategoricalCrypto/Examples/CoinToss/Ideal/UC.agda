{-# OPTIONS --safe --without-K --guardedness #-}

-- The second hop at the UC model: the joint simulator's query certificate, and
-- the machine equality read across the seal as an exact graded emulation.
--
-- `coin-hop` is `Examples.CoinToss.Ideal.Machine.coin-machine` in the
-- grading's vocabulary, through the three coercions `UC.Graded` supplies for a
-- COMPOSED system: `ext-graded` for the stage on top, `graded₂-∘` for the
-- resource plugged under, and `sub-graded₂` for the joint simulator in front.
-- The agreement is exact, so the schedule it carries is `0`.

open import Data.Bool.Base using (_xor_)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; s≤s; z≤n)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (case_of_; _∘′_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Categories.Category using (Category)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import ProbabilisticLogic.Dp.Uniform using (uniformₚ)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Budget using (Budget)
open import CategoricalCrypto.UC.Graded using (ext-graded; graded₂-∘; sub-graded₂)
open import CategoricalCrypto.UC.Machine using (T₁ᴵ; a⇒ᴵ)
open import CategoricalCrypto.UC.Model.Dominated using (qb-gradedᵒ)
open import CategoricalCrypto.UC.Model.Enrichment using (budgetᵒ; qbᵒ)
open import CategoricalCrypto.UC.Model.Graded using (≈ᴹ⇒≈ᵍ₂)
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (Ans; Certified; certified⇒QB; forget)

open import CategoricalCrypto.Machines.Base using (𝒢ₚ)

module CategoricalCrypto.Examples.CoinToss.Ideal.UC (k : ℕ) where

open import CategoricalCrypto.Examples.CoinToss k
open import CategoricalCrypto.Examples.CoinToss.Ideal k
open import CategoricalCrypto.Examples.CoinToss.Ideal.Machine k
open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k

open Budget budgetᵒ using (QB)
open HomReasoning

private module M = Category (𝒢ₚ 0ℓ)

------------------------------------------------------------------------
-- The joint simulator spends one call per activation

-- `commitˢ`, `openˢ` and `failˢ` each buy exactly one `Lkᴵᶜ` message; a hash
-- query is answered from the simulator's own table and the coin's answer only
-- returns, so nothing is owed afterwards and the potential stays at zero.
-- This is `Examples.CoinToss.UC.recvCert`'s shape, at the other machine.
simJCert : Certified 1 simJ
simJCert = record
  { Φ      = λ _ → 0
  ; pointᵍ = returnₚ (preʲ [] , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (preʲ [] , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  Aᵍ : ℕ → Set
  Aᵍ = Ans {JSt} (λ _ → 0) (Neg Lkᴵᶜ) (Pos (Lkᴵ ⊗ᴵ Advᴵᶜ))

  hashG : Tbl → (Tbl → JSt) → Pt → Dₚ (Aᵍ 1)
  hashG t φ x = case lookupPt t x of λ where
    (just d) → returnₚ (inj₂ ((φ t , z≤n) , inj₁ (digˢ d)))
    nothing  → uniformₚ k >>=ₚ λ h →
                 returnₚ (inj₂ ((φ ((x , h) ∷ t) , z≤n) , inj₁ (digˢ h)))

  -- The lookup is scrutinized by both sides at once, so it is `rewrite`n once.
  cohHash : (t : Tbl) (φ : Tbl → JSt) (x : Pt) (w : Maybe Dig) → lookupPt t x ≡ w
          → mapₚ forget (hashG t φ x) ≈ₚ hashJ t φ x
  cohHash t φ x (just d) eq rewrite eq = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohHash t φ x nothing  eq rewrite eq =
    map-bind (uniformₚ k) _ forget ⟨≈⟩ bindᶠ λ _ → >>=ₚ-identityˡ _ (returnₚ ∘′ forget)

  onL : (s : JSt) (a : Pos Lkᴵᶜ) → Dₚ (Aᵍ 0)
  onL (preʲ _)    (coinᵏ _) = botₚ
  onL (askʲ t b₁) (coinᵏ c) = returnₚ (inj₂ ((midʲ t , z≤n) , inj₂ (shareᴬ (b₁ xor c))))
  onL (midʲ _)    (coinᵏ _) = botₚ
  onL (endʲ _)    (coinᵏ _) = botₚ

  onR : (s : JSt) (b : Neg (Lkᴵ ⊗ᴵ Advᴵᶜ)) → Dₚ (Aᵍ 1)
  onR s (inj₁ (hashˢ x))    = case s of λ where
    (preʲ t)   → hashG t preʲ x
    (askʲ t b) → hashG t (λ u → askʲ u b) x
    (midʲ t)   → hashG t midʲ x
    (endʲ t)   → hashG t endʲ x
  onR s (inj₁ (commitˢ b₁)) = case s of λ where
    (preʲ t) → returnₚ (inj₁ ((askʲ t b₁ , s≤s z≤n) , sampleᵏ))
    _        → botₚ
  onR s (inj₁ openˢ)        = case s of λ where
    (midʲ t) → returnₚ (inj₁ ((endʲ t , s≤s z≤n) , deliverᵏ))
    _        → botₚ
  onR s (inj₁ failˢ)        = case s of λ where
    (midʲ t) → returnₚ (inj₁ ((endʲ t , s≤s z≤n) , abortᵏ))
    _        → botₚ
  onR _ (inj₂ ())

  cohL : (s : JSt) (a : Pos Lkᴵᶜ) → mapₚ forget (onL s a) ≈ₚ jStep (s , inj₁ a)
  cohL (preʲ _)   (coinᵏ _) = bot-bind-≈ₚ _
  cohL (askʲ _ _) (coinᵏ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (midʲ _)   (coinᵏ _) = bot-bind-≈ₚ _
  cohL (endʲ _)   (coinᵏ _) = bot-bind-≈ₚ _

  cohR : (s : JSt) (b : Neg (Lkᴵ ⊗ᴵ Advᴵᶜ)) → mapₚ forget (onR s b) ≈ₚ jStep (s , inj₂ b)
  cohR (preʲ t)   (inj₁ (hashˢ x))   = cohHash t preʲ x _ refl
  cohR (askʲ t b) (inj₁ (hashˢ x))   = cohHash t (λ u → askʲ u b) x _ refl
  cohR (midʲ t)   (inj₁ (hashˢ x))   = cohHash t midʲ x _ refl
  cohR (endʲ t)   (inj₁ (hashˢ x))   = cohHash t endʲ x _ refl
  cohR (preʲ _)   (inj₁ (commitˢ _)) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (askʲ _ _) (inj₁ (commitˢ _)) = bot-bind-≈ₚ _
  cohR (midʲ _)   (inj₁ (commitˢ _)) = bot-bind-≈ₚ _
  cohR (endʲ _)   (inj₁ (commitˢ _)) = bot-bind-≈ₚ _
  cohR (preʲ _)   (inj₁ openˢ)       = bot-bind-≈ₚ _
  cohR (askʲ _ _) (inj₁ openˢ)       = bot-bind-≈ₚ _
  cohR (midʲ _)   (inj₁ openˢ)       = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (endʲ _)   (inj₁ openˢ)       = bot-bind-≈ₚ _
  cohR (preʲ _)   (inj₁ failˢ)       = bot-bind-≈ₚ _
  cohR (askʲ _ _) (inj₁ failˢ)       = bot-bind-≈ₚ _
  cohR (midʲ _)   (inj₁ failˢ)       = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (endʲ _)   (inj₁ failˢ)       = bot-bind-≈ₚ _
  cohR _          (inj₂ ())

simJQB : QB 1 (gradedᵒ simJ)
simJQB = qb-gradedᵒ (certified⇒QB simJCert)

-- The resource is closed, so it makes no downward call at all.
resourceQBᵒ : QB 0 (procᵒ resource)
resourceQBᵒ = qbᵒ resourceQB

------------------------------------------------------------------------
-- …and the machine equality, across the seal

-- Three coercions and nothing else: the stage on top is `ext-graded`, the
-- resource under it `graded₂-∘`, and the joint simulator in front of the ideal
-- coin `sub-graded₂`.
coin-hop : (ext (ifaceᵒ Lkᴵ) (gradedᵒ toss) ∘ gradedᵒ ideal) ∘ procᵒ resource
           ≈ sub (gradedᵒ simJ) ∘ gradedᵒ Fcoin
coin-hop =
       ∘-resp-≈ˡ (ext-graded toss ideal)
  ○    graded₂-∘ (M._∘_ a⇒ᴵ (M._∘_ (T₁ᴵ Lkᴵ toss) ideal)) resource
  ○    ≈ᴹ⇒≈ᵍ₂ coin-machine
  ○    Equiv.sym (sub-graded₂ simJ Fcoin)
