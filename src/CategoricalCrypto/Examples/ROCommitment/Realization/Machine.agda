{-# OPTIONS --safe --without-K --guardedness #-}

-- The real commitment system over the concrete resource, as a kernel: the
-- closed composite `real 𝒫.∘ resource` settles, so its `Dₚ` run is the run of
-- a `Dist⊥` kernel (`Protocol.Machine.Trace.Compose`).
--
-- The rank the loop needs is two-valued here and reads off `realStep`: a
-- resource query still owes its answer (1), an answer owes nothing (0),
-- because every clause of `realStep` on a `Pos Resᴵ` letter either emits
-- upward or diverges (`real-up`).  The resource's own activations are all
-- exits or loop points of smaller rank, so its side needs no inspection.

open import Class.DecEq

open import Data.Bool.Base using (not; _xor_)
open import Data.Empty using (⊥)
open import Data.List.Base using (_∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; suc; s≤s; z≤n; _+_; _≤_; _<_)
open import Data.Nat.Properties using (+-mono-≤; +-suc; ≤-refl)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using () renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (cong; subst)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Support

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base using (𝒱ₚ)
open import CategoricalCrypto.Protocol.Machine.Raw using (ansᴹ)
open import CategoricalCrypto.Protocol.Machine.Trace.Compose
open import CategoricalCrypto.UC.Machine using (Proc; subᴵ; ⊤ᵛ)

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.Examples.ROCommitment.Realization.Machine (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment k
open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Resource k
open import CategoricalCrypto.Examples.ROCommitment.Transport k using (resK; resource-settles)
open import CategoricalCrypto.Examples.ROCommitment.UC k using (Φˢ)

open Core (𝒱ₚ 0ℓ)

------------------------------------------------------------------------
-- The honest receiver's kernel

-- `realStep` with its `returnₚ`s read as point masses and its `botₚ`s as the
-- sink; the clause structure is `realStep`'s, so both sides reduce together.
Kʳ : RSt → Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ (RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
Kʳ s (inj₁ (digᴿ d))           = case s of λ where
  (relayᴿ m)   → return⊥ (waitᴿ m        , inj₂ (inj₁ (ansᴬ d)))
  (checkᴿ c b) → return⊥ (waitᴿ (just c) , inj₂ (inj₂ (verdict b ⌊ d ≟ c ⌋)))
  (waitᴿ _)    → return-ℚ nothing
Kʳ s (inj₁ rcptᴿ)              = return-ℚ nothing
Kʳ s (inj₁ (outᴿ _))           = return-ℚ nothing
Kʳ s (inj₁ rejᴿ)               = return-ℚ nothing
Kʳ s (inj₂ (inj₁ (queryᴬ x)))  = case s of λ where
  (waitᴿ m) → return⊥ (relayᴿ m , inj₁ (hashᴿ x))
  _         → return-ℚ nothing
Kʳ s (inj₂ (inj₁ (commitᴬ c))) = case s of λ where
  (waitᴿ nothing) → return⊥ (waitᴿ (just c) , inj₂ (inj₂ rcptᴴ))
  _               → return-ℚ nothing
Kʳ s (inj₂ (inj₁ (openᴬ b r))) = case s of λ where
  (waitᴿ (just c)) → return⊥ (checkᴿ c b , inj₁ (hashᴿ (b ∷ᵛ r)))
  _                → return-ℚ nothing
Kʳ s (inj₂ (inj₂ ()))

real-settles : (m : RSt) (y : Pos Resᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
             → Σ[ i ∈ ℕ ] Settles i (step real (m , y)) (Kʳ m y)
real-settles (waitᴿ _)    (inj₁ (digᴿ _)) = 0 , Settles-bot
real-settles (relayᴿ _)   (inj₁ (digᴿ _)) = 1 , Settles-return _
real-settles (checkᴿ _ _) (inj₁ (digᴿ _)) = 1 , Settles-return _
real-settles _ (inj₁ rcptᴿ)    = 0 , Settles-bot
real-settles _ (inj₁ (outᴿ _)) = 0 , Settles-bot
real-settles _ (inj₁ rejᴿ)     = 0 , Settles-bot
real-settles (waitᴿ _)    (inj₂ (inj₁ (queryᴬ _))) = 1 , Settles-return _
real-settles (relayᴿ _)   (inj₂ (inj₁ (queryᴬ _))) = 0 , Settles-bot
real-settles (checkᴿ _ _) (inj₂ (inj₁ (queryᴬ _))) = 0 , Settles-bot
real-settles (waitᴿ nothing)  (inj₂ (inj₁ (commitᴬ _))) = 1 , Settles-return _
real-settles (waitᴿ (just _)) (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot
real-settles (relayᴿ _)       (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot
real-settles (checkᴿ _ _)     (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot
real-settles (waitᴿ (just _)) (inj₂ (inj₁ (openᴬ _ _))) = 1 , Settles-return _
real-settles (waitᴿ nothing)  (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot
real-settles (relayᴿ _)       (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot
real-settles (checkᴿ _ _)     (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot
real-settles _ (inj₂ (inj₂ ()))

-- The receiver never answers the resource with another query: every clause of
-- `realStep` on a `Pos Resᴵ` letter emits upward or diverges.  This is the
-- whole content of the composite's rank.
real-up : (Φ : RSt × (Neg Resᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) → Set)
        → ((s : RSt) (c : Pos (Advᴵ ⊗ᴵ Honᴵ)) → Φ (s , inj₂ c))
        → (s : RSt) (z : Pos Resᴵ) (i : ℕ) → Supp i (step real (s , inj₁ z)) Φ
real-up Φ h (waitᴿ _)    (digᴿ _) = Supp-bot Φ
real-up Φ h (relayᴿ _)   (digᴿ _) = Supp-return Φ _ (h _ _)
real-up Φ h (checkᴿ _ _) (digᴿ _) = Supp-return Φ _ (h _ _)
real-up Φ h _ rcptᴿ    = Supp-bot Φ
real-up Φ h _ (outᴿ _) = Supp-bot Φ
real-up Φ h _ rejᴿ     = Supp-bot Φ

------------------------------------------------------------------------
-- The resource's kernel, at the closed factor's alphabet

Kᵒ : RState → ⊥ ⊎ Neg Resᴵ → Dist⊥ (RState × (⊥ ⊎ Pos Resᴵ))
Kᵒ s (inj₂ q) = Dmap⊥ ansᴹ (resK s q)

res-settles : (m : RState) (z : ⊥ ⊎ Neg Resᴵ)
            → Σ[ i ∈ ℕ ] Settles i (step resource (m , z)) (Kᵒ m z)
res-settles m (inj₂ q) = resource-settles m q

------------------------------------------------------------------------
-- The round-trip bound at `real 𝒫.∘ resource`

rankᴿ : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ) → ℕ
rankᴿ (_ , inj₁ _) = 1
rankᴿ (_ , inj₂ _) = 0

private
  Dropsᴿ : ℕ → (RSt × RState) × ((⊥ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) ⊎ (Neg Resᴵ ⊎ Pos Resᴵ)) → Set
  Dropsᴿ = Lp.Drops real resource Kʳ Kᵒ real-settles res-settles rankᴿ

  -- A resource answer is a loop point of rank 0; the receiver's reaction to it
  -- leaves the loop.
  dispatchᴿ : (w : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) (i : ℕ)
            → Supp i (Col.kᴳ real resource (proj₁ w , inj₂ (proj₂ w))) (Dropsᴿ (rankᴿ w))
  dispatchᴿ ((sg , sf) , inj₁ q) i =
    Supp-bind (Dropsᴿ 1) i _ _ (Supp-all _ (λ where (_ , inj₂ _) → Supp-return _ _ (s≤s z≤n)) i _)
  dispatchᴿ ((sg , sf) , inj₂ a) i =
    Supp-bind (Dropsᴿ 0) i _ _ (real-up _ (λ _ _ → Supp-return _ _ tt) sg a i)

rankedᴿ : Lp.Ranked real resource Kʳ Kᵒ real-settles res-settles rankᴿ
rankedᴿ = ranked-from-kᴳ real resource Kʳ Kᵒ real-settles res-settles rankᴿ dispatchᴿ

boundᴿ : (w : (RSt × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) → rankᴿ w < 2
boundᴿ (_ , inj₁ _) = s≤s (s≤s z≤n)
boundᴿ (_ , inj₂ _) = s≤s z≤n

-- The closed real system's kernel: one activation of the corrupted committer,
-- served to completion through the oracle.
Kᴿ : RSt × RState → Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ ((RSt × RState) × Pos (Advᴵ ⊗ᴵ Honᴵ))
Kᴿ = Kᶜˡ real resource Kʳ Kᵒ real-settles res-settles rankᴿ rankedᴿ 2 boundᴿ

------------------------------------------------------------------------
-- The ideal functionality, over the same resource

-- A wire: one letter in, one letter out, in either direction.
Kⁱ : ⊤ᵛ → Pos Resᴵ ⊎ Neg (Lkᴵ ⊗ᴵ Honᴵ) → Dist⊥ (⊤ᵛ × (Neg Resᴵ ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ)))
Kⁱ s (inj₁ p) = return⊥ (s , inj₂ (upᶠ p))
Kⁱ s (inj₂ n) = return⊥ (s , inj₁ (downᶠ n))

ideal-settles : (m : ⊤ᵛ) (y : Pos Resᴵ ⊎ Neg (Lkᴵ ⊗ᴵ Honᴵ))
              → Σ[ i ∈ ℕ ] Settles i (step ideal (m , y)) (Kⁱ m y)
ideal-settles m (inj₁ p) = 1 , Settles-return _
ideal-settles m (inj₂ n) = 1 , Settles-return _

ideal-up : (Φ : ⊤ᵛ × (Neg Resᴵ ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ)) → Set)
         → ((s : ⊤ᵛ) (c : Pos (Lkᴵ ⊗ᴵ Honᴵ)) → Φ (s , inj₂ c))
         → (s : ⊤ᵛ) (z : Pos Resᴵ) (i : ℕ) → Supp i (step ideal (s , inj₁ z)) Φ
ideal-up Φ h s z = Supp-return Φ _ (h _ _)

rankᴵⁿ : (⊤ᵛ × RState) × (Neg Resᴵ ⊎ Pos Resᴵ) → ℕ
rankᴵⁿ (_ , inj₁ _) = 1
rankᴵⁿ (_ , inj₂ _) = 0

private
  Dropsᴵⁿ : ℕ → (⊤ᵛ × RState) × ((⊥ ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ)) ⊎ (Neg Resᴵ ⊎ Pos Resᴵ)) → Set
  Dropsᴵⁿ = Lp.Drops ideal resource Kⁱ Kᵒ ideal-settles res-settles rankᴵⁿ

  dispatchᴵⁿ : (w : (⊤ᵛ × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) (i : ℕ)
             → Supp i (Col.kᴳ ideal resource (proj₁ w , inj₂ (proj₂ w))) (Dropsᴵⁿ (rankᴵⁿ w))
  dispatchᴵⁿ ((sg , sf) , inj₁ q) i =
    Supp-bind (Dropsᴵⁿ 1) i _ _ (Supp-all _ (λ where (_ , inj₂ _) → Supp-return _ _ (s≤s z≤n)) i _)
  dispatchᴵⁿ ((sg , sf) , inj₂ a) i =
    Supp-bind (Dropsᴵⁿ 0) i _ _ (ideal-up _ (λ _ _ → Supp-return _ _ tt) sg a i)

rankedᴵⁿ : Lp.Ranked ideal resource Kⁱ Kᵒ ideal-settles res-settles rankᴵⁿ
rankedᴵⁿ = ranked-from-kᴳ ideal resource Kⁱ Kᵒ ideal-settles res-settles rankᴵⁿ dispatchᴵⁿ

boundᴵⁿ : (w : (⊤ᵛ × RState) × (Neg Resᴵ ⊎ Pos Resᴵ)) → rankᴵⁿ w < 2
boundᴵⁿ (_ , inj₁ _) = s≤s (s≤s z≤n)
boundᴵⁿ (_ , inj₂ _) = s≤s z≤n

-- `F_com` installed on the resource, as one machine with a kernel.
Fcom : Col.MC.Machine (⊥ ⊎ Neg (Lkᴵ ⊗ᴵ Honᴵ)) (⊥ ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ))
Fcom = traceᴳ ideal resource Kⁱ Kᵒ ideal-settles res-settles

Kᶠ : ⊤ᵛ × RState → ⊥ ⊎ Neg (Lkᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ ((⊤ᵛ × RState) × (⊥ ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ)))
Kᶠ m z = K∘ ideal resource Kⁱ Kᵒ ideal-settles res-settles rankᴵⁿ rankedᴵⁿ 2 boundᴵⁿ (m , z)

Fcom-settles : (m : ⊤ᵛ × RState) (z : ⊥ ⊎ Neg (Lkᴵ ⊗ᴵ Honᴵ))
             → Σ[ i ∈ ℕ ] Settles i (step Fcom (m , z)) (Kᶠ m z)
Fcom-settles m z = compose-settles ideal resource Kⁱ Kᵒ ideal-settles res-settles
                                   rankᴵⁿ rankedᴵⁿ 2 boundᴵⁿ (m , z)

------------------------------------------------------------------------
-- The extracting simulator in front of it

simᴵ : Proc (Lkᴵ ⊗ᴵ Honᴵ) (Advᴵ ⊗ᴵ Honᴵ)
simᴵ = subᴵ simulator {Honᴵ}

Kˢ : SSt → Pos (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ (SSt × (Neg (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
Kˢ s (inj₁ (inj₁ (digˢ d)))    = case s of λ where
  (relayˢ x L m)     → return⊥ (waitˢ ((x , d) ∷ L) m , inj₂ (inj₁ (ansᴬ d)))
  (checkˢ x b L c e) → return⊥ ( waitˢ ((x , d) ∷ L) (just (c , e))
                               , inj₁ (inj₁ (release ⌊ d ≟ c ⌋ (not (b xor e)))) )
  (waitˢ _ _)        → return-ℚ nothing
Kˢ s (inj₁ (inj₂ a))           = return⊥ (s , inj₂ (inj₂ a))
Kˢ s (inj₂ (inj₁ (queryᴬ x)))  = case s of λ where
  (waitˢ L m) → return⊥ (relayˢ x L m , inj₁ (inj₁ (hashˢ x)))
  _           → return-ℚ nothing
Kˢ s (inj₂ (inj₁ (commitᴬ c))) = case s of λ where
  (waitˢ L nothing) → return⊥ ( waitˢ L (just (c , extract c L))
                              , inj₁ (inj₁ (commitˢ (extract c L))) )
  _                 → return-ℚ nothing
Kˢ s (inj₂ (inj₁ (openᴬ b r))) = case s of λ where
  (waitˢ L (just (c , e))) → return⊥ ( checkˢ (b ∷ᵛ r) b L c e
                                     , inj₁ (inj₁ (hashˢ (b ∷ᵛ r))) )
  _                        → return-ℚ nothing
Kˢ s (inj₂ (inj₂ ()))

sub-settles : (m : SSt) (y : Pos (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
            → Σ[ i ∈ ℕ ] Settles i (step simᴵ (m , y)) (Kˢ m y)
sub-settles (waitˢ _ _)      (inj₁ (inj₁ (digˢ _))) = 0 , Settles-bot⋆ _
sub-settles (relayˢ _ _ _)   (inj₁ (inj₁ (digˢ _))) = Settles-ret⋆ _ _ _ (1 , Settles-return _)
sub-settles (checkˢ _ _ _ _ _) (inj₁ (inj₁ (digˢ _))) = Settles-ret⋆ _ _ _ (1 , Settles-return _)
sub-settles _ (inj₁ (inj₂ _)) = 1 , Settles-return _
sub-settles (waitˢ _ _)        (inj₂ (inj₁ (queryᴬ _))) = Settles-ret⋆ _ _ _ (1 , Settles-return _)
sub-settles (relayˢ _ _ _)     (inj₂ (inj₁ (queryᴬ _))) = 0 , Settles-bot⋆ _
sub-settles (checkˢ _ _ _ _ _) (inj₂ (inj₁ (queryᴬ _))) = 0 , Settles-bot⋆ _
sub-settles (waitˢ _ nothing)  (inj₂ (inj₁ (commitᴬ _))) = Settles-ret⋆ _ _ _ (1 , Settles-return _)
sub-settles (waitˢ _ (just _)) (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot⋆ _
sub-settles (relayˢ _ _ _)     (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot⋆ _
sub-settles (checkˢ _ _ _ _ _) (inj₂ (inj₁ (commitᴬ _))) = 0 , Settles-bot⋆ _
sub-settles (waitˢ _ (just _)) (inj₂ (inj₁ (openᴬ _ _))) = Settles-ret⋆ _ _ _ (1 , Settles-return _)
sub-settles (waitˢ _ nothing)  (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot⋆ _
sub-settles (relayˢ _ _ _)     (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot⋆ _
sub-settles (checkˢ _ _ _ _ _) (inj₂ (inj₁ (openᴬ _ _))) = 0 , Settles-bot⋆ _
sub-settles _ (inj₂ (inj₂ ()))

-- What the simulator does with an answer from below: it exits, or it owes one
-- fewer downward message than it did.  `Φˢ` is `Examples.ROCommitment.UC`'s
-- allowance ledger, which measures exactly that.
sub-up : (s : SSt) (Φ : SSt × (Neg (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) → Set)
       → ((s′ : SSt) (c : Pos (Advᴵ ⊗ᴵ Honᴵ)) → Φ (s′ , inj₂ c))
       → ((s′ : SSt) (q : Neg (Lkᴵ ⊗ᴵ Honᴵ)) → Φˢ s′ < Φˢ s → Φ (s′ , inj₁ q))
       → (w : Pos (Lkᴵ ⊗ᴵ Honᴵ)) (i : ℕ) → Supp i (step simᴵ (s , inj₁ w)) Φ
sub-up (waitˢ _ _) Φ ex dn (inj₁ (digˢ _)) i =
  Supp-bind Φ i _ _ (Supp-bot _ i)
sub-up (relayˢ _ _ _) Φ ex dn (inj₁ (digˢ _)) i =
  Supp-bind Φ i _ _ (Supp-return _ _ (Supp-return Φ _ (ex _ _)) i)
sub-up (checkˢ _ _ _ _ _) Φ ex dn (inj₁ (digˢ _)) i =
  Supp-bind Φ i _ _ (Supp-return _ _ (Supp-return Φ _ (dn _ _ (s≤s z≤n))) i)
sub-up s Φ ex dn (inj₂ a) = Supp-return Φ _ (ex _ _)

------------------------------------------------------------------------
-- …and the round-trip bound at the ideal composite

-- Twice the simulator's allowance, plus one while the query is still in
-- flight: a query owes an answer, and the answer may owe one more query.
rankᴵ : (SSt × (⊤ᵛ × RState)) × (Neg (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ)) → ℕ
rankᴵ ((sg , _) , inj₁ _) = suc (Φˢ sg + Φˢ sg)
rankᴵ ((sg , _) , inj₂ _) = Φˢ sg + Φˢ sg

private
  Dropsᴵ : ℕ → (SSt × (⊤ᵛ × RState))
             × ((⊥ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) ⊎ (Neg (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ))) → Set
  Dropsᴵ = Lp.Drops simᴵ Fcom Kˢ Kᶠ sub-settles Fcom-settles rankᴵ

  -- `a < b` in the simulator's own ledger is the doubled drop the loop needs.
  double : {a b : ℕ} → a < b → suc (a + a) < b + b
  double {a} {b} lt = subst (λ z → z ≤ b + b) (cong suc (+-suc a a)) (+-mono-≤ lt lt)

  dispatchᴵ : (w : (SSt × (⊤ᵛ × RState)) × (Neg (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ))) (i : ℕ)
            → Supp i (Col.kᴳ simᴵ Fcom (proj₁ w , inj₂ (proj₂ w))) (Dropsᴵ (rankᴵ w))
  dispatchᴵ ((sg , sf) , inj₁ q) i =
    Supp-bind (Dropsᴵ (suc (Φˢ sg + Φˢ sg))) i _ _
      (Supp-all _ (λ where (_ , inj₂ _) → Supp-return _ _ ≤-refl) i _)
  dispatchᴵ ((sg , sf) , inj₂ a) i =
    Supp-bind (Dropsᴵ (Φˢ sg + Φˢ sg)) i _ _
      (sub-up sg _ (λ _ _ → Supp-return _ _ tt) (λ _ _ lt → Supp-return _ _ (double lt)) a i)

rankedᴵ : Lp.Ranked simᴵ Fcom Kˢ Kᶠ sub-settles Fcom-settles rankᴵ
rankedᴵ = ranked-from-kᴳ simᴵ Fcom Kˢ Kᶠ sub-settles Fcom-settles rankᴵ dispatchᴵ

boundᴵ : (w : (SSt × (⊤ᵛ × RState)) × (Neg (Lkᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Lkᴵ ⊗ᴵ Honᴵ))) → rankᴵ w < 4
boundᴵ ((waitˢ _ _ , _)        , inj₁ _) = s≤s (s≤s z≤n)
boundᴵ ((relayˢ _ _ _ , _)     , inj₁ _) = s≤s (s≤s z≤n)
boundᴵ ((checkˢ _ _ _ _ _ , _) , inj₁ _) = s≤s (s≤s (s≤s (s≤s z≤n)))
boundᴵ ((waitˢ _ _ , _)        , inj₂ _) = s≤s z≤n
boundᴵ ((relayˢ _ _ _ , _)     , inj₂ _) = s≤s z≤n
boundᴵ ((checkˢ _ _ _ _ _ , _) , inj₂ _) = s≤s (s≤s (s≤s z≤n))

-- The closed simulated-ideal system's kernel.
Kᴵ : SSt × (⊤ᵛ × RState) → Neg (Advᴵ ⊗ᴵ Honᴵ)
   → Dist⊥ ((SSt × (⊤ᵛ × RState)) × Pos (Advᴵ ⊗ᴵ Honᴵ))
Kᴵ = Kᶜˡ simᴵ Fcom Kˢ Kᶠ sub-settles Fcom-settles rankᴵ rankedᴵ 4 boundᴵ
