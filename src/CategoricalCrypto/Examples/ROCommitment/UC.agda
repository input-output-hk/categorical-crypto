{-# OPTIONS --safe --without-K --guardedness #-}

-- The three machines at the UC model, and what the extracting simulator
-- spends.
--
-- The grade is `ifaceᵒ Advᴵ`, inhabited by the corrupted committer's three
-- messages, so the simulator `procᵒ simulator : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ` is
-- not a scalar and nothing here is in reach of `UC.Seam.Grounded.subBlind`.
-- There is no `≈ᵁ` between `realᵒ` and `sub simᵒ ∘ idealᵒ`: the emulation is
-- approximate and its ε is `Examples.ROCommitment.Game.extraction-bound`.
--
-- What the simulator spends is stated EXACTLY, at two weightings of the same
-- `UC.QueryBound.Exact` ledger: `simExactHash` counts oracle relays and
-- `simExactAll` counts downward outputs of any kind.  `simCert` is the
-- matching amortised ceiling, which is what `UC.Budget` asks for.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true; not; _xor_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; s≤s; z≤n; _+_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.Model.Seal using (gradedᵒ; ifaceᵒ; procᵒ)
open import CategoricalCrypto.UC.Model.Setup
open import CategoricalCrypto.UC.QueryBound using (Certified; QB; certified⇒QB; forget)
open import CategoricalCrypto.UC.QueryBound.Exact

module CategoricalCrypto.Examples.ROCommitment.UC (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k using (extract)

------------------------------------------------------------------------
-- The images

realᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Advᴵ) (ifaceᵒ Honᴵ)
realᵒ = gradedᵒ real

idealᵒ : ifaceᵒ Resᴵ ⇒ T₀ (ifaceᵒ Lkᴵ) (ifaceᵒ Honᴵ)
idealᵒ = gradedᵒ ideal

simᵒ : ifaceᵒ Lkᴵ ⇒ ifaceᵒ Advᴵ
simᵒ = procᵒ simulator

------------------------------------------------------------------------
-- The allowance

-- An activation from above buys two downward messages; only the opening uses
-- both, and `checkˢ` is where the second one is still owed.
Φˢ : SSt → ℕ
Φˢ (waitˢ _ _)        = 0
Φˢ (relayˢ _ _ _)     = 0
Φˢ (checkˢ _ _ _ _ _) = 1

simCert : Certified 2 simulator
simCert = record
  { Φ      = Φˢ
  ; pointᵍ = returnₚ (waitˢ [] nothing , z≤n)
  ; coh₀   = >>=ₚ-identityˡ (waitˢ [] nothing , z≤n) (returnₚ ∘′ proj₁)
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
  onL : (s : SSt) (a : Pos Lkᴵ) → Dₚ _
  onL (relayˢ x L m)     (digˢ d) =
    returnₚ (inj₂ ((waitˢ ((x , d) ∷ L) m , z≤n) , ansᴬ d))
  onL (checkˢ x b L c e) (digˢ d) =
    returnₚ (inj₁ ( (waitˢ ((x , d) ∷ L) (just (c , e)) , s≤s z≤n)
                  , release ⌊ d ≟ c ⌋ (not (b xor e)) ))
  onL (waitˢ _ _)        (digˢ _) = botₚ

  onR : (s : SSt) (b : Neg Advᴵ) → Dₚ _
  onR (waitˢ L m)              (queryᴬ x)  =
    returnₚ (inj₁ ((relayˢ x L m , s≤s z≤n) , hashˢ x))
  onR (waitˢ L nothing)        (commitᴬ c) =
    returnₚ (inj₁ ((waitˢ L (just (c , extract c L)) , s≤s z≤n) , commitˢ (extract c L)))
  onR (waitˢ L (just (c , e))) (openᴬ b r) =
    returnₚ (inj₁ ((checkˢ (b ∷ᵛ r) b L c e , s≤s (s≤s z≤n)) , hashˢ (b ∷ᵛ r)))
  onR (relayˢ _ _ _)           (queryᴬ _)  = botₚ
  onR (checkˢ _ _ _ _ _)       (queryᴬ _)  = botₚ
  onR (waitˢ _ (just _))       (commitᴬ _) = botₚ
  onR (waitˢ _ nothing)        (openᴬ _ _) = botₚ
  onR (relayˢ _ _ _)           (commitᴬ _) = botₚ
  onR (relayˢ _ _ _)           (openᴬ _ _) = botₚ
  onR (checkˢ _ _ _ _ _)       (commitᴬ _) = botₚ
  onR (checkˢ _ _ _ _ _)       (openᴬ _ _) = botₚ

  cohL : (s : SSt) (a : Pos Lkᴵ) → mapₚ forget (onL s a) ≈ₚ simStep (s , inj₁ a)
  cohL (relayˢ _ _ _)     (digˢ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (checkˢ _ _ _ _ _) (digˢ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohL (waitˢ _ _)        (digˢ _) = bot-bind-≈ₚ _

  cohR : (s : SSt) (b : Neg Advᴵ) → mapₚ forget (onR s b) ≈ₚ simStep (s , inj₂ b)
  cohR (waitˢ _ _)        (queryᴬ _)  = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (waitˢ _ nothing)  (commitᴬ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (waitˢ _ (just _)) (openᴬ _ _) = >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
  cohR (waitˢ _ (just _)) (commitᴬ _) = bot-bind-≈ₚ _
  cohR (waitˢ _ nothing)  (openᴬ _ _) = bot-bind-≈ₚ _
  cohR (relayˢ _ _ _)     (queryᴬ _)  = bot-bind-≈ₚ _
  cohR (relayˢ _ _ _)     (commitᴬ _) = bot-bind-≈ₚ _
  cohR (relayˢ _ _ _)     (openᴬ _ _) = bot-bind-≈ₚ _
  cohR (checkˢ _ _ _ _ _) (queryᴬ _)  = bot-bind-≈ₚ _
  cohR (checkˢ _ _ _ _ _) (commitᴬ _) = bot-bind-≈ₚ _
  cohR (checkˢ _ _ _ _ _) (openᴬ _ _) = bot-bind-≈ₚ _

simQB : QB 2 simulator
simQB = certified⇒QB simCert

------------------------------------------------------------------------
-- …exactly

-- One oracle relay per adversary message that names a point — its own query,
-- and the opening the receiver would have hashed itself.
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

-- …and, of downward messages of ANY kind, one per query, one per commitment
-- and two per opening — the second of which `checkˢ` still owes.
perMessage : Pos Lkᴵ ⊎ Neg Advᴵ → ℕ
perMessage (inj₁ _)           = 0
perMessage (inj₂ (queryᴬ _))  = 1
perMessage (inj₂ (commitᴬ _)) = 1
perMessage (inj₂ (openᴬ _ _)) = 2

Λᴴ Λᴬ : SSt → ℕ
Λᴴ _                  = 0
Λᴬ (waitˢ _ _)        = 0
Λᴬ (relayˢ _ _ _)     = 0
Λᴬ (checkˢ _ _ _ _ _) = 1

pointˢ : Dₚ SSt
pointˢ = returnₚ (waitˢ [] nothing)

module EH = Ledger {Lkᴵ} {Advᴵ} SSt pointˢ simStep hashes points
module EA = Ledger {Lkᴵ} {Advᴵ} SSt pointˢ simStep downward perMessage

private
  -- The release message is not a relay, whichever way the two checks went.
  hashes-release : (x y : Bool) → hashes (inj₁ (release x y)) ≡ 0
  hashes-release true  true  = refl
  hashes-release true  false = refl
  hashes-release false _     = refl


simExactHash : EH.QEᵢ
simExactHash = record
  { Λ = Λᴴ ; pointᴱ = returnₚ (waitˢ [] nothing , refl)
  ; coh₀ = >>=ₚ-identityˡ (waitˢ [] nothing , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = st ; cohᴱ = coh }
  where
  st : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
     → Dₚ (Σ[ p ∈ SSt × (Neg Lkᴵ ⊎ Pos Advᴵ) ]
            Λᴴ s + points x ≡ hashes (proj₂ p) + Λᴴ (proj₁ p))
  st (waitˢ L m) (inj₂ (queryᴬ x)) =
    returnₚ ((relayˢ x L m , inj₁ (hashˢ x)) , refl)
  st (waitˢ L nothing) (inj₂ (commitᴬ c)) =
    returnₚ ((waitˢ L (just (c , extract c L)) , inj₁ (commitˢ (extract c L))) , refl)
  st (waitˢ L (just (c , e))) (inj₂ (openᴬ b r)) =
    returnₚ ((checkˢ (b ∷ᵛ r) b L c e , inj₁ (hashˢ (b ∷ᵛ r))) , refl)
  st (relayˢ x L m) (inj₁ (digˢ d)) =
    returnₚ ((waitˢ ((x , d) ∷ L) m , inj₂ (ansᴬ d)) , refl)
  st (checkˢ x b L c e) (inj₁ (digˢ d)) =
    returnₚ ( (waitˢ ((x , d) ∷ L) (just (c , e))
              , inj₁ (release ⌊ d ≟ c ⌋ (not (b xor e))))
            , sym (cong (_+ 0) (hashes-release ⌊ d ≟ c ⌋ (not (b xor e)))) )
  st (waitˢ _ _)        (inj₁ (digˢ _)) = botₚ
  st (waitˢ _ (just _)) (inj₂ (commitᴬ _)) = botₚ
  st (waitˢ _ nothing)  (inj₂ (openᴬ _ _)) = botₚ
  st (relayˢ _ _ _)     (inj₂ _) = botₚ
  st (checkˢ _ _ _ _ _) (inj₂ _) = botₚ

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

simExactAll : EA.QEᵢ
simExactAll = record
  { Λ = Λᴬ ; pointᴱ = returnₚ (waitˢ [] nothing , refl)
  ; coh₀ = >>=ₚ-identityˡ (waitˢ [] nothing , refl) (returnₚ ∘′ proj₁)
  ; stepᴱ = st ; cohᴱ = coh }
  where
  st : (s : SSt) (x : Pos Lkᴵ ⊎ Neg Advᴵ)
     → Dₚ (Σ[ p ∈ SSt × (Neg Lkᴵ ⊎ Pos Advᴵ) ]
            Λᴬ s + perMessage x ≡ downward (proj₂ p) + Λᴬ (proj₁ p))
  st (waitˢ L m) (inj₂ (queryᴬ x)) =
    returnₚ ((relayˢ x L m , inj₁ (hashˢ x)) , refl)
  st (waitˢ L nothing) (inj₂ (commitᴬ c)) =
    returnₚ ((waitˢ L (just (c , extract c L)) , inj₁ (commitˢ (extract c L))) , refl)
  st (waitˢ L (just (c , e))) (inj₂ (openᴬ b r)) =
    returnₚ ((checkˢ (b ∷ᵛ r) b L c e , inj₁ (hashˢ (b ∷ᵛ r))) , refl)
  st (relayˢ x L m) (inj₁ (digˢ d)) =
    returnₚ ((waitˢ ((x , d) ∷ L) m , inj₂ (ansᴬ d)) , refl)
  st (checkˢ x b L c e) (inj₁ (digˢ d)) =
    returnₚ ( (waitˢ ((x , d) ∷ L) (just (c , e))
              , inj₁ (release ⌊ d ≟ c ⌋ (not (b xor e)))) , refl )
  st (waitˢ _ _)        (inj₁ (digˢ _)) = botₚ
  st (waitˢ _ (just _)) (inj₂ (commitᴬ _)) = botₚ
  st (waitˢ _ nothing)  (inj₂ (openᴬ _ _)) = botₚ
  st (relayˢ _ _ _)     (inj₂ _) = botₚ
  st (checkˢ _ _ _ _ _) (inj₂ _) = botₚ

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

-- The occurrence statements: on EVERY branch of the simulator's run over an
-- activation word, the oracle relays it performs are exactly the points the
-- adversary named — no residual, because the relay is issued in the same step
-- — and the downward messages of any kind are the word's own weight up to an
-- opening still in flight.
sim-hash-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
               → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                      EH.Balanced Λᴴ (weight points w) p)
sim-hash-count = EH.exactᴱ simExactHash

sim-message-count : (w : List (Pos Lkᴵ ⊎ Neg Advᴵ))
                  → Dₚ (Σ[ p ∈ SSt × List (Neg Lkᴵ ⊎ Pos Advᴵ) ]
                         EA.Balanced Λᴬ (weight perMessage w) p)
sim-message-count = EA.exactᴱ simExactAll
