{-# OPTIONS --safe --guardedness #-}

--------------------------------------------------------------------------------
-- Merkle–Damgård's query count, as a `UC.QueryBound` certificate.
--
-- `md` makes exactly one compression call per block and every message is `k`
-- blocks, so `morphism md` is `k`-bounded in the amortised sense `QBᵢ` means:
-- one activation from above causes at most `k` completed activations below.
--
-- The potential CANNOT be read off `Protocol.Machine.MSt`: its `wait` holds
-- the parked continuation as a FUNCTION, and no `Φ : MSt → ℕ` can recover from
-- it how many calls are left.  That is what `QB`'s `≈ᴹ`-closure is for: the
-- certificate is carried by `mdᴹ`, the same relay named by its RESIDUAL BLOCK
-- LIST (a query while suspended, or an answer while idle, diverges), whose
-- potential is that list's length.  `Pw.simFn θᴰ` is the simulation onto
-- `morphism md`, definitional at every node because `θᴰ` rebuilds precisely
-- the continuation `chainᶜ` parked.
--------------------------------------------------------------------------------

open import Data.Bool.Base
open import Data.Fin.Base using (Fin)
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Data.Vec.Base using (Vec)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Examples.MerkleDamgard
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.MerkleDamgard.QueryBound
  (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

open MD n k IV

------------------------------------------------------------------------
-- The relay named by its residual block list

-- Idle, or (party, next block index, remaining blocks).
MDState : Set
MDState = Maybe (Fin p × ℕ × List Blk)

private
  resume : Fin p → ℕ → List Blk → Pos Compᴵ → Calls Compᴵ (⊤ × Pos Generalᴵ)
  resume i idx bs o = chainᶜ (proj₂ o) bs idx >>=ᶜ λ v → ret (tt , (i , v))

  advance : Fin p → ℕ → List Blk → CV → MDState × (Comp.Input ⊎ General.Output)
  advance i idx []       h = nothing                 , inj₂ (i , h)
  advance i idx (b ∷ bs) h = just (i , suc idx , bs) , inj₁ (i₀ , pack h b idx)

  stepᴰ : MDState × (Pos Compᴵ ⊎ Neg Generalᴵ) → Dₚ (MDState × (Neg Compᴵ ⊎ Pos Generalᴵ))
  stepᴰ (nothing            , inj₂ (i , M)) = returnₚ (advance i 1 (toBlocks M) IV)
  stepᴰ (just (i , idx , bs) , inj₁ (_ , h)) = returnₚ (advance i idx bs h)
  stepᴰ (nothing            , inj₁ _)       = botₚ
  stepᴰ (just _             , inj₂ _)       = botₚ

  stateᴰ : MC.State
  stateᴰ = initˢ MDState nothing

mdᴹ : Proc Compᴵ Generalᴵ
mdᴹ = MC.mk stateᴰ stepᴰ

------------------------------------------------------------------------
-- The certificate

private
  Φᴰ : MDState → ℕ
  Φᴰ nothing             = 0
  Φᴰ (just (_ , _ , bs)) = length bs

  Answer = Ans Φᴰ (Neg Compᴵ) (Pos Generalᴵ)

  -- Entering deposits `k` units and spends one on the first block; the block
  -- list has length `k`, which is where the rate comes from.
  onEnter : (i : Fin p) (bs : List Blk) → length bs ≡ k → Dₚ (Answer k)
  onEnter i []       e = returnₚ (inj₂ ((nothing , z≤n) , (i , IV)))
  onEnter i (b ∷ bs) e = returnₚ (inj₁ ((just (i , 2 , bs) , ≤-reflexive e) , (i₀ , pack IV b 1)))

  onEnter-coh : (i : Fin p) (bs : List Blk) (e : length bs ≡ k)
              → mapₚ forget (onEnter i bs e) ≈ₚ returnₚ (advance i 1 bs IV)
  onEnter-coh i []       e = >>=ₚ-identityˡ _ _
  onEnter-coh i (b ∷ bs) e = >>=ₚ-identityˡ _ _

  onAdvance : (i : Fin p) (idx : ℕ) (bs : List Blk) (h : CV) → Dₚ (Answer (length bs))
  onAdvance i idx []       h = returnₚ (inj₂ ((nothing , z≤n) , (i , h)))
  onAdvance i idx (b ∷ bs) h = returnₚ (inj₁ ((just (i , suc idx , bs) , ≤-refl) , (i₀ , pack h b idx)))

  onAdvance-coh : (i : Fin p) (idx : ℕ) (bs : List Blk) (h : CV)
                → mapₚ forget (onAdvance i idx bs h) ≈ₚ returnₚ (advance i idx bs h)
  onAdvance-coh i idx []       h = >>=ₚ-identityˡ _ _
  onAdvance-coh i idx (b ∷ bs) h = >>=ₚ-identityˡ _ _

certifiedᴹᴰ : Certified k mdᴹ
certifiedᴹᴰ = record
  { Φ      = Φᴰ
  ; pointᵍ = returnₚ (nothing , z≤n)
  ; coh₀   = >>=ₚ-identityˡ _ _
  ; onLᵍ   = λ where
      nothing               _       → botₚ
      (just (i , idx , bs)) (_ , h) → onAdvance i idx bs h
  ; onRᵍ   = λ where
      nothing  (i , M) → onEnter i (toBlocks M) (toBlocks-length M)
      (just _) _       → botₚ
  ; cohL   = λ where
      nothing               _       → bot-bind-≈ₚ _
      (just (i , idx , bs)) (_ , h) → onAdvance-coh i idx bs h
  ; cohR   = λ where
      nothing  (i , M) → onEnter-coh i (toBlocks M) (toBlocks-length M)
      (just _) _       → bot-bind-≈ₚ _
  }

------------------------------------------------------------------------
-- …and it is a certificate for `morphism md`

private
  θᴰ : MDState → MSt md
  θᴰ nothing              = idle tt
  θᴰ (just (i , idx , bs)) = wait (resume i idx bs)

  -- The point is passed explicitly: left to a meta, `θᴰ`'s constructor-headed
  -- clauses invert and strand `resume`'s arguments.
  advance-drive : (i : Fin p) (idx : ℕ) (bs : List Blk) (h : CV)
                → (returnₚ (advance i idx bs h) >>=ₚ λ r → returnₚ (θᴰ (proj₁ r) , proj₂ r))
                  ≈ₚ drive md (chainᶜ h bs idx >>=ᶜ λ v → ret (tt , (i , v)))
  advance-drive i idx []       h = >>=ₚ-identityˡ (advance i idx [] h) _
  advance-drive i idx (b ∷ bs) h = >>=ₚ-identityˡ (advance i idx (b ∷ bs) h) _

  θ-step : (z : MDState × (Pos Compᴵ ⊎ Neg Generalᴵ))
         → (stepᴰ z >>=ₚ Pw.padϕ θᴰ) ≈ₚ stepᴹ md (θᴰ (proj₁ z) , proj₂ z)
  θ-step (nothing , inj₂ (i , M))            = advance-drive i 1 (toBlocks M) IV
  θ-step (just (i , idx , bs) , inj₁ (_ , h)) = advance-drive i idx bs h
  θ-step (nothing , inj₁ a)                  = bot-bind-≈ₚ _
  θ-step (just (i , idx , bs) , inj₂ b)      = bot-bind-≈ₚ _

qbᴹᴰ : QB k (morphism md)
qbᴹᴰ = mdᴹ , certifiedᴹᴰ
  , S.≲⇒≈ᴹ (Pw.simFn θᴰ (λ _ → >>=ₚ-identityˡ nothing _) θ-step)

