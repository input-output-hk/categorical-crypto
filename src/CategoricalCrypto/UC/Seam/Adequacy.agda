{-# OPTIONS --safe --without-K --guardedness #-}

-- `Adequacy`: an embedded strategy, run as an environment against a closed
-- process, observes what layer 1's own run observes.
--
-- The ⊕-trace solves its loop WITHIN one step, so the composite's single
-- activation — the verdict interface's tick — runs the whole interaction, and
-- `iter` performs one pass per message on the plugged interface.  That is what
-- the induction unrolls: an `ask` of the strategy costs two passes, the process
-- answering and the environment resuming, and `iterₚ-fix` supplies each.
--
-- The G-composite's structural wiring is already collapsed in
-- `UC.Seam.Adequacy.Wiring`, whose `kᵂ` is the loop's one-pass dispatch, and
-- the tick that enters the loop is `UC.Seam.Plug`'s, at an arbitrary such
-- dispatch.  What is left here is `Dₚ` arithmetic and the strategy tree.

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base using (tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy.Wiring
open import CategoricalCrypto.UC.Seam.Plug

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.UC.Seam.Adequacy where

private module MC = Core (𝒱ₚ 0ℓ)

module _ (B : Iface) (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B)) where

  -- The traced wire carries both polarities of the plugged interface, and the
  -- paired state is the environment's tree beside the process's own.
  open Tick (Neg B ⊎ Pos B) (stateˢ B d MC.⊛ MC.state u) (kᵂ B u)

  point-red : (x : ⊤ᵛ) → MC.point (stateˢ B d MC.⊛ MC.state u) x
                        ≈ₚ (MC.point (MC.state u) x >>=ₚ λ su → returnₚ (play d , su))
  point-red x = >>=ₚ-identityˡ (ttᵛ , x) _ ⟨≈⟩ >>=ₚ-identityˡ (play d) _

  -- The induction: an environment about to play `e` against `u` in state `su`
  -- observes layer 1's run of `u` on `e`.  Each `ask` costs two loop passes.
  play-run : (su : MC.St u) (e : Strat (Neg B) (Pos B))
           → (playˢ B e >>=ₚ λ q → cont ((proj₁ q , su) , outE B (proj₂ q)))
             ≈ₚ runᴹFrom u su e
  play-run su (out v)    = >>=ₚ-identityˡ (play (out v) , inj₂ v) _
  play-run su (coin μ k) =
      >>=ₚ-assoc (coinₚ μ) (λ c → playˢ B (k c)) _
    ⟨≈⟩ bindᶠ (λ c → play-run su (k c))
  play-run su (ask q k)  =
      >>=ₚ-identityˡ (susp k , inj₁ q) _
    ⟨≈⟩ bindˣ (iterₚ-fix body ((susp k , su) , inj₁ q))
    ⟨≈⟩ bindˣ (>>=ₚ-assoc (MC.step u (su , inj₂ q)) _ (contᵢ body))
    ⟨≈⟩ >>=ₚ-assoc (MC.step u (su , inj₂ q)) _ verdict
    ⟨≈⟩ bindᶠ resume-loop
    where
    -- The process's answer resumes the environment: the second pass.
    resume-loop : (r : MC.St u × (⊥ ⊎ Pos B))
                → ((returnₚ ((susp k , proj₁ r) , outU B (proj₂ r)) >>=ₚ contᵢ body)
                    >>=ₚ verdict)
                  ≈ₚ resumeᴹ u (λ su′ p → runᴹFrom u su′ (k p)) r
    resume-loop (_   , inj₁ e) = ⊥-elim e
    resume-loop (su′ , inj₂ p) =
        bindˣ (>>=ₚ-identityˡ ((susp k , su′) , inj₂ (inj₂ p)) (contᵢ body))
      ⟨≈⟩ cont-red ((susp k , su′) , inj₂ (inj₂ p))
      ⟨≈⟩ bindˣ (iterₚ-fix body ((susp k , su′) , inj₂ p))
      ⟨≈⟩ bindˣ (>>=ₚ-assoc (playˢ B (k p)) _ (contᵢ body))
      ⟨≈⟩ >>=ₚ-assoc (playˢ B (k p)) _ verdict
      ⟨≈⟩ bindᶠ (λ w → bindˣ (>>=ₚ-identityˡ ((proj₁ w , su′) , outE B (proj₂ w))
                                             (contᵢ body))
                 ⟨≈⟩ cont-red ((proj₁ w , su′) , outE B (proj₂ w)))
      ⟨≈⟩ play-run su′ (k p)

  -- …and the composite's one activation enters that induction at the tick.
  step-run : (su : MC.St u)
           → runᴹFrom (pairedᴹ B d u) (play d , su) (ask tt out) ≈ₚ runᴹFrom u su d
  step-run su =
      tick-run (play d , su)
    ⟨≈⟩ >>=ₚ-assoc (playˢ B d) _ cont
    ⟨≈⟩ bindᶠ (λ q → >>=ₚ-identityˡ ((proj₁ q , su) , outE B (proj₂ q)) cont)
    ⟨≈⟩ play-run su d

adequacy : Adequacy
adequacy B u d =
    runᴹ-resp-≈ᴹ {Ωᴵ} (compose-≈ᴹ B d u) (ask tt out)
  ⟨≈⟩ bindˣ (point-red B u d ttᵛ)
  ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state u) ttᵛ) _ _
  ⟨≈⟩ bindᶠ (λ su → >>=ₚ-identityˡ (play d , su) _)
  ⟨≈⟩ bindᶠ (step-run B u d)
