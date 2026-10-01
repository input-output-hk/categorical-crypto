{-# OPTIONS --safe #-}

--------------------------------------------------------------------------------
-- MERKLE–DAMGÅRD as a protocol, and its concrete-security theorem: SINGLE-
-- ORACLE indistinguishability with the compression function HIDDEN.  The
-- distinguisher is a `Strat (Neg Generalᴵ) (Pos Generalᴵ)` — `Sys = md ∘ᵖ comp`
-- closes `comp` off, so there is no compression-oracle interface — and there is
-- no simulator anywhere.  That is strictly weaker than indifferentiability,
-- i.e. than "MD is a random oracle".
--
-- `md`'s step is a `Calls` tree with one `call` per block (`chainᶜ`), so one
-- activation of the composite IS the core's `mdRun`, by induction on the block
-- list (`graft-chain`).  The cryptography is `Examples.MerkleDamgard.Core`;
-- `indistinguishable` hands its `ghost-erase`, `ideal-marginal` and `md-cert`
-- to `GamePlaying.Hop.hop-bound`, so this module adds only the seam between
-- `Protocol.Observe.runObs` and `Interaction.runWith`.
--------------------------------------------------------------------------------

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using () renaming (_-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Unit.Base
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as RS

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Advantage
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Examples.MerkleDamgard.Core as Core

module CategoricalCrypto.Examples.MerkleDamgard where

------------------------------------------------------------------------
-- The three protocols

module MD (n k : ℕ) ⦃ _ : NonZero k ⦄ (IV : Vec Bool n) where

  open Core.MD n k IV public

  Compᴵ Generalᴵ : Iface
  Compᴵ    = Comp.Output    ⇿ Comp.Input
  Generalᴵ = General.Output ⇿ General.Input

  comp : Protocol unitᴵ Compᴵ
  comp = Comp.Lazy.oracle

  general : Protocol unitᴵ Generalᴵ
  general = General.Lazy.oracle

  -- `p = 1`, so a compression query carries the party `i₀`, as `Core.mdRun`
  -- does.
  chainᶜ : CV → List Blk → ℕ → Calls Compᴵ CV
  chainᶜ h []       idx = ret h
  chainᶜ h (b ∷ bs) idx = call (i₀ , pack h b idx) λ o → chainᶜ (proj₂ o) bs (suc idx)

  md : Protocol Compᴵ Generalᴵ
  md = record { St = ⊤ ; init = tt ;
                step = λ _ (i , M) → chainᶜ IV (toBlocks M) 1 >>=ᶜ λ h → ret (tt , (i , h)) }

  Sys : Protocol unitᴵ Generalᴵ
  Sys = md ∘ᵖ comp

  ------------------------------------------------------------------------
  -- One activation is the crypto core's kernel

  private
    Go : (Comp.Output → Calls Compᴵ (⊤ × General.Output))
       → Comp.Table × Comp.Output → Dist⊥ ((⊤ × Comp.Table) × General.Output)
    Go κ o = evalC (graft md comp (κ (proj₂ o)) (proj₁ o))

    Kret : Fin p → Comp.Table × CV → Dist⊥ ((⊤ × Comp.Table) × General.Output)
    Kret i o = return⊥ ((tt , proj₁ o) , (i , proj₂ o))

    graft-chain : ∀ i sc h bs idx
                → evalC (graft md comp (chainᶜ h bs idx >>=ᶜ λ v → ret (tt , (i , v))) sc)
                  ≈Mℚ (mdRun sc h bs idx >>=ᴹ Kret i)
    graft-chain i sc h []       idx =
      Mℚ.sym {x = return-ℚ (sc , h) >>=ᴹ Kret i} {y = Kret i (sc , h)}
        (>>=ᴹ-identityˡ (sc , h) (Kret i))
    graft-chain i sc h (b ∷ bs) idx = begin
      evalC (serve md comp κ (Comp.Lazy.answer sc (i₀ , pack h b idx)
                                                (Comp.lookup-bs sc (pack h b idx))))
        ≈⟨ Comp.Lazy.answer-eval (λ t → evalC (serve md comp κ t)) (λ _ _ _ → refl) (Go κ)
                                 (λ _ _ → refl) sc i₀ (pack h b idx) ⟩
      (Comp.step (sc , i₀ , pack h b idx) >>=ᴹ Go κ)
        ≈⟨ >>=ᴹ-congˡ (Comp.step (sc , i₀ , pack h b idx)) (Go κ) (λ o → MR o >>=ᴹ Kret i)
             (λ o → graft-chain i (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx)) ⟩
      (Comp.step (sc , i₀ , pack h b idx) >>=ᴹ λ o → (MR o >>=ᴹ Kret i))
        ≈˘⟨ >>=ᴹ-assoc (Comp.step (sc , i₀ , pack h b idx)) MR (Kret i) ⟩
      (mdRun sc h (b ∷ bs) idx >>=ᴹ Kret i)
        ∎
      where
        κ  = λ o → chainᶜ (proj₂ o) bs (suc idx) >>=ᶜ λ v → ret (tt , (i , v))
        MR = λ (o : Comp.Table × Comp.Output) → mdRun (proj₁ o) (proj₂ (proj₂ o)) bs (suc idx)
        open RS (Mℚ-setoid _)

    sysStep : ∀ sc q → kernel Sys (tt , sc) q
                       ≈Mℚ (respR sc q >>=ᴹ λ o → return⊥ ((tt , proj₁ o) , proj₂ o))
    sysStep sc (i , M) = begin
      kernel Sys (tt , sc) (i , M)
        ≈⟨ graft-chain i sc IV (toBlocks M) 1 ⟩
      (mdRun sc IV (toBlocks M) 1 >>=ᴹ Kret i)
        ≈˘⟨ >>=ᴹ-congˡ (mdRun sc IV (toBlocks M) 1) (λ sh → Rw sh >>=ᴹ KE) (Kret i)
              (λ sh → >>=ᴹ-identityˡ (proj₁ sh , (i , proj₂ sh)) KE) ⟩
      (mdRun sc IV (toBlocks M) 1 >>=ᴹ λ sh → (Rw sh >>=ᴹ KE))
        ≈˘⟨ >>=ᴹ-assoc (mdRun sc IV (toBlocks M) 1) Rw KE ⟩
      (respR sc (i , M) >>=ᴹ KE)
        ∎
      where
        Rw = λ (sh : Comp.Table × CV) → return-ℚ (proj₁ sh , (i , proj₂ sh))
        KE = λ (o : Comp.Table × General.Output) → return⊥ ((tt , proj₁ o) , proj₂ o)
        open RS (Mℚ-setoid _)

  run-general : ∀ d → runObs general d ≈Mℚ Dmap just (runWith respG [] d)
  run-general = runWith⊥-emb respG (kernel general) (λ sg → sg)
    (λ sg (i , M) → General.Lazy.answer-eval evalC (λ _ _ _ → refl)
                      (λ o → return⊥ (proj₁ o , proj₂ o)) (λ _ _ → refl) sg i M) []

  run-Sys : ∀ d → runObs Sys d ≈Mℚ Dmap just (runWith respR [] d)
  run-Sys = runWith⊥-emb respR (kernel Sys) (tt ,_) sysStep []

  -- Neither run diverges, so at either verdict the `false` reading is the
  -- complement of the `true` one and `advᵇ⊥-just` collapses them.
  indistinguishable : general ≈adv[ bound ] Sys
  indistinguishable b q d le =
    subst (_≤ℚ bound q) (sym advEq)
          (hop-bound proj₁ respB respR respG (false , [] , []) [] []
                     (ghost-erase false [] []) (λ d′ → sym (ideal-marginal d′))
                     md-cert q d le)
    where
      advEq : advᵇ⊥ b (runObs general d) (runObs Sys d)
            ≡ ∣ Pr₁ (runWith respG [] d) -ℚ Pr₁ (runWith respR [] d) ∣ℚ
      advEq =
        trans (cong₂ (λ x y → ∣ x -ℚ y ∣ℚ)
                (run-general d (maybeℚ (indᵇ b))) (run-Sys d (maybeℚ (indᵇ b))))
              (advᵇ⊥-just b (runWith respG [] d) (runWith respR [] d))

