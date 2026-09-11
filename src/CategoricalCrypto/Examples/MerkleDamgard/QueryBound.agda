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
-- it how many calls are left.  That is exactly what `QB`'s `≈ᴹ`-closure is
-- for.  The certificate is carried by `mdᴹ`, the same relay named by its
-- RESIDUAL BLOCK LIST (`Core.MDState`, the machine-era state, with the
-- protocol's discipline added: a query while suspended, or an answer while
-- idle, diverges), whose potential is that list's length; `θ-sim` is the
-- simulation onto `morphism md`, and it is definitional at every node because
-- `θᴰ` rebuilds precisely the continuation `chainᶜ` parked.
--
-- Warm single-module typecheck: ~11 s (measured 2026-09-10, `+RTS -M3G -H1G`).
--------------------------------------------------------------------------------

open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)

import Categories.Category.Kleisli.Discrete as KD
import Categories.Category.Kleisli.Discrete.Pure as KDP

open import Data.Bool.Base using (Bool)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; z≤n; NonZero)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Data.Vec.Base using (Vec)
open import Data.Vec.Properties using (length-toList)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Examples.MerkleDamgard
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.QueryBound

import CategoricalCrypto.Machines.Pointwise as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.MerkleDamgard.QueryBound
  (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module V  = SymmetricMonoidalCategory (𝒱ₚ 0ℓ)
  module K  = KD (Dₚ-DiscreteMonad {0ℓ})
  module KP = KDP (Dₚ-DiscreteMonad {0ℓ})

open MD n k IV

------------------------------------------------------------------------
-- The relay named by its residual block list

private
  -- What `chainᶜ` parks: the rest of the chain, at the party the general query
  -- carried.  `θᴰ` below rebuilds exactly this.
  resume : Fin p → ℕ → List Blk → Pos Compᴵ → Calls Compᴵ (⊤ × Pos Generalᴵ)
  resume i idx bs o = chainᶜ (proj₂ o) bs idx >>=ᶜ λ v → ret (tt , (i , v))

  -- A compression answer arrives mid-chain: fire the next block, or finish.
  advance : Fin p → ℕ → List Blk → CV → MDState × (Comp.Input ⊎ General.Output)
  advance i idx []       h = nothing                 , inj₂ (i , h)
  advance i idx (b ∷ bs) h = just (i , suc idx , bs) , inj₁ (i₀ , pack h b idx)

  -- A general query arrives: fire block 1 at index 1.
  enter : Fin p → List Blk → MDState × (Comp.Input ⊎ General.Output)
  enter i []       = nothing            , inj₂ (i , IV)
  enter i (b ∷ bs) = just (i , 2 , bs)  , inj₁ (i₀ , pack IV b 1)

  stepᴰ : MDState × (Pos Compᴵ ⊎ Neg Generalᴵ) → Dₚ (MDState × (Neg Compᴵ ⊎ Pos Generalᴵ))
  stepᴰ (nothing            , inj₂ (i , M)) = returnₚ (enter i (toBlocks M))
  stepᴰ (just (i , idx , bs) , inj₁ (_ , h)) = returnₚ (advance i idx bs h)
  stepᴰ (nothing            , inj₁ _)       = botₚ
  stepᴰ (just _             , inj₂ _)       = botₚ

  stateᴰ : MC.State
  stateᴰ = record
    { obj = MDState ; point = λ _ → returnₚ nothing ; discard = λ _ → returnₚ ttᵛ }

mdᴹ : Proc Compᴵ Generalᴵ
mdᴹ = MC.mk stateᴰ stepᴰ

------------------------------------------------------------------------
-- The certificate

private
  Φᴰ : MDState → ℕ
  Φᴰ nothing             = 0
  Φᴰ (just (_ , _ , bs)) = length bs

  blk-len : (M : Vec Bool (k * n)) → length (toBlocks M) ≡ k
  blk-len M = length-toList (chunk k M)

  Answer = Ans Φᴰ (Neg Compᴵ) (Pos Generalᴵ)

  -- Entering deposits `k` units and spends one on the first block; the block
  -- list has length `k`, which is where the rate comes from.
  onEnter : (i : Fin p) (bs : List Blk) → length bs ≡ k → Dₚ (Answer k)
  onEnter i []       e = returnₚ (inj₂ ((nothing , z≤n) , (i , IV)))
  onEnter i (b ∷ bs) e = returnₚ (inj₁ ((just (i , 2 , bs) , ≤-reflexive e) , (i₀ , pack IV b 1)))

  onEnter-coh : (i : Fin p) (bs : List Blk) (e : length bs ≡ k)
              → mapₚ forget (onEnter i bs e) ≈ₚ returnₚ (enter i bs)
  onEnter-coh i []       e = >>=ₚ-identityˡ _ _
  onEnter-coh i (b ∷ bs) e = >>=ₚ-identityˡ _ _

  -- A compression answer spends one unit, or returns without spending.
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
  ; onLᵍ   = onL
  ; onRᵍ   = onR
  ; cohL   = cohL
  ; cohR   = cohR
  }
  where
    onL : (s : MDState) (a : Pos Compᴵ) → Dₚ (Answer (Φᴰ s))
    onL nothing             _       = botₚ
    onL (just (i , idx , bs)) (_ , h) = onAdvance i idx bs h

    onR : (s : MDState) (b : Neg Generalᴵ) → Dₚ (Answer (Φᴰ s + k))
    onR nothing  (i , M) = onEnter i (toBlocks M) (blk-len M)
    onR (just _) _       = botₚ

    cohL : (s : MDState) (a : Pos Compᴵ) → mapₚ forget (onL s a) ≈ₚ stepᴰ (s , inj₁ a)
    cohL nothing             _       = bot-bind-≈ₚ _
    cohL (just (i , idx , bs)) (_ , h) = onAdvance-coh i idx bs h

    cohR : (s : MDState) (b : Neg Generalᴵ) → mapₚ forget (onR s b) ≈ₚ stepᴰ (s , inj₂ b)
    cohR nothing  (i , M) = onEnter-coh i (toBlocks M) (blk-len M)
    cohR (just _) _       = bot-bind-≈ₚ _

------------------------------------------------------------------------
-- …and it is a certificate for `morphism md`

private
  θᴰ : MDState → MSt md
  θᴰ nothing              = idle tt
  θᴰ (just (i , idx , bs)) = wait (resume i idx bs)

  -- Both drives park the SAME continuation: `θᴰ` is `resume`, which is the
  -- subtree `chainᶜ` hands to `call`.  The point is passed to `⊗-pureˡ`
  -- explicitly: left to a meta, `θᴰ`'s constructor-headed clauses invert and
  -- strand `resume`'s arguments.
  enter-drive : (i : Fin p) (bs : List Blk)
              → (returnₚ (enter i bs) >>=ₚ (K.pureᵏ θᴰ V.⊗₁ V.id))
                ≈ₚ drive md (chainᶜ IV bs 1 >>=ᶜ λ v → ret (tt , (i , v)))
  enter-drive i []       = >>=ₚ-identityˡ (enter i []) _
                         ⟨≈⟩ Col.⊗-pureˡ θᴰ (enter i [])
  enter-drive i (b ∷ bs) = >>=ₚ-identityˡ (enter i (b ∷ bs)) _
                         ⟨≈⟩ Col.⊗-pureˡ θᴰ (enter i (b ∷ bs))

  advance-drive : (i : Fin p) (idx : ℕ) (bs : List Blk) (h : CV)
                → (returnₚ (advance i idx bs h) >>=ₚ (K.pureᵏ θᴰ V.⊗₁ V.id))
                  ≈ₚ drive md (chainᶜ h bs idx >>=ᶜ λ v → ret (tt , (i , v)))
  advance-drive i idx []       h = >>=ₚ-identityˡ (advance i idx [] h) _
                                 ⟨≈⟩ Col.⊗-pureˡ θᴰ (advance i idx [] h)
  advance-drive i idx (b ∷ bs) h = >>=ₚ-identityˡ (advance i idx (b ∷ bs) h) _
                                  ⟨≈⟩ Col.⊗-pureˡ θᴰ (advance i idx (b ∷ bs) h)

  θ-step : (z : MDState × (Pos Compᴵ ⊎ Neg Generalᴵ))
         → (stepᴰ z >>=ₚ (K.pureᵏ θᴰ V.⊗₁ V.id))
         ≈ₚ ((K.pureᵏ θᴰ V.⊗₁ V.id) z >>=ₚ stepᴹ md)
  θ-step (nothing , inj₂ (i , M)) =
    enter-drive i (toBlocks M)
    ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴰ (nothing , inj₂ (i , M)))
              ⟨≈⟩ >>=ₚ-identityˡ (idle tt , inj₂ (i , M)) _)
  θ-step (just (i , idx , bs) , inj₁ (j , h)) =
    advance-drive i idx bs h
    ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴰ (just (i , idx , bs) , inj₁ (j , h)))
              ⟨≈⟩ >>=ₚ-identityˡ (wait (resume i idx bs) , inj₁ (j , h)) _)
  θ-step (nothing , inj₁ a) =
    bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴰ (nothing , inj₁ a))
              ⟨≈⟩ >>=ₚ-identityˡ (idle tt , inj₁ a) _)
  θ-step (just (i , idx , bs) , inj₂ b) =
    bot-bind-≈ₚ _
    ⟨≈⟩ ≈sym (bindˣ (Col.⊗-pureˡ θᴰ (just (i , idx , bs) , inj₂ b))
              ⟨≈⟩ >>=ₚ-identityˡ (wait (resume i idx bs) , inj₂ b) _)

  θ-sim : mdᴹ S.≲ morphism md
  θ-sim = S.sim (K.pureᵏ θᴰ) (KP.structural θᴰ)
                (λ r → >>=ₚ-identityˡ (θᴰ r) _)
                (λ _ → >>=ₚ-identityˡ nothing _)
                θ-step

-- Merkle–Damgård costs at most `k` compression activations per message.
qbᴹᴰ : QB k (morphism md)
qbᴹᴰ = mdᴹ , certifiedᴹᴰ , S.≲⇒≈ᴹ θ-sim

