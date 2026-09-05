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
-- `UC.Seam.Adequacy.Wiring`, whose `kᵂ` is the loop's one-pass dispatch; what is
-- left here is `Dₚ` arithmetic and the strategy tree.

open import Data.Bool.Base
open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base using (⊤; tt)
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Level

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Seam
open import CategoricalCrypto.UC.Seam.Adequacy.Wiring

import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Trace as Trace

module CategoricalCrypto.UC.Seam.Adequacy where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module MT = Trace (𝒱ₚ 0ℓ) (distₚ 0ℓ) (𝒫ₚ 0ℓ) (Elgotₚ 0ℓ)

private
  variable A′ B′ : Set

  infixr 5 _⟨≈⟩_

  -- The library's lemmas take their subjects explicitly; see the note in
  -- `UC.Machine.Run` for why a transparent chain strands them as metas.
  _⟨≈⟩_ : {x y z : Dₚ A′} → x ≈ₚ y → y ≈ₚ z → x ≈ₚ z
  _⟨≈⟩_ {x = x} {y} {z} = ≈ₚ-trans x y z

  ≈refl : {x : Dₚ A′} → x ≈ₚ x
  ≈refl {x = x} = ≈ₚ-refl x

  bindᶠ : {x : Dₚ A′} {k l : A′ → Dₚ B′} → ((a : A′) → k a ≈ₚ l a)
        → (x >>=ₚ k) ≈ₚ (x >>=ₚ l)
  bindᶠ {x = x} {k} {l} h = >>=ₚ-cong x x k l ≈refl h

  bindˣ : {x y : Dₚ A′} {k : A′ → Dₚ B′} → x ≈ₚ y → (x >>=ₚ k) ≈ₚ (y >>=ₚ k)
  bindˣ {x = x} {y} {k} h = >>=ₚ-cong x y k k h λ _ → ≈refl

module _ (B : Iface) (u : Proc unitᴵ B) (d : Strat (Neg B) (Pos B)) where

  -- The traced wire carries both polarities of the plugged interface, and the
  -- paired state is the environment's tree beside the process's own.
  Loopᵂ : Set
  Loopᵂ = Neg B ⊎ Pos B

  Stᵂ : Set
  Stᵂ = EnvSt B × MC.St u

  -- One pass of the loop: `kᵂ` entered on the loop summand.
  bodyᵂ : Body Stᵂ Loopᵂ (⊥ ⊎ Bool)
  bodyᵂ p = kᵂ B u (proj₁ p , inj₂ (proj₂ p))

  verdictᵂ : Stᵂ × (⊥ ⊎ Bool) → Dₚ Bool
  verdictᵂ (_ , inj₁ e) = ⊥-elim e
  verdictᵂ (_ , inj₂ v) = returnₚ v

  -- What a pass's output means: leave with the verdict, or keep solving.
  contᵂ : Stᵂ × ((⊥ ⊎ Bool) ⊎ Loopᵂ) → Dₚ Bool
  contᵂ (st , inj₁ o) = verdictᵂ (st , o)
  contᵂ (st , inj₂ x) = iterₚ bodyᵂ (st , x) >>=ₚ verdictᵂ

  private
    Sᴹ : MC.State
    Sᴹ = stateˢ B d MC.⊛ MC.state u

    solveᵂ : Stᵂ × ((⊥ ⊎ Bool) ⊎ Loopᵂ) → Dₚ (Stᵂ × (⊥ ⊎ Bool))
    solveᵂ = MT.solve Sᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) Loopᵂ (kᵂ B u)

    bodyᴹ : Body Stᵂ Loopᵂ (⊥ ⊎ Bool)
    bodyᴹ = MT.loopBody Sᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) Loopᵂ (kᵂ B u)

    -- The junctions the Kleisli tensor spends on a pure relabelling.
    loop-red : (p : Stᵂ × Loopᵂ) → bodyᴹ p ≈ₚ bodyᵂ p
    loop-red (st , x) = bindˣ (>>=ₚ-identityˡ st _)
                  ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (inj₂ x) _)
                  ⟨≈⟩ >>=ₚ-identityˡ (st , inj₂ x) (kᵂ B u)

    trace-red : (st : Stᵂ) (y : ⊥ ⊎ ⊤)
              → MT.traceStep Sᴹ (⊥ ⊎ ⊤) (⊥ ⊎ Bool) Loopᵂ (kᵂ B u) (st , y)
                ≈ₚ (kᵂ B u (st , inj₁ y) >>=ₚ solveᵂ)
    trace-red st y = bindˣ (bindˣ (>>=ₚ-identityˡ st _)
                       ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (inj₁ y) _)
                       ⟨≈⟩ >>=ₚ-identityˡ (st , inj₁ y) (kᵂ B u))

    resume-red : (p : Stᵂ × (⊥ ⊎ Bool))
               → resumeᴹ (pairedᴹ B d u) (λ _ r → returnₚ r) p ≈ₚ verdictᵂ p
    resume-red (_ , inj₁ e) = ⊥-elim e
    resume-red (_ , inj₂ _) = ≈refl

    -- The distributor's case split IS the loop's continuation.
    solve-red : (r : Stᵂ × ((⊥ ⊎ Bool) ⊎ Loopᵂ)) → solveᵂ r ≈ₚ contᵢ bodyᴹ r
    solve-red (st , inj₁ o) = >>=ₚ-identityˡ (inj₁ (st , o)) _
    solve-red (st , inj₂ x) = >>=ₚ-identityˡ (inj₂ (st , x)) _

    solve-cont : (r : Stᵂ × ((⊥ ⊎ Bool) ⊎ Loopᵂ)) → (solveᵂ r >>=ₚ verdictᵂ) ≈ₚ contᵂ r
    solve-cont (st , inj₁ o) = bindˣ (solve-red (st , inj₁ o))
                         ⟨≈⟩ >>=ₚ-identityˡ (st , o) verdictᵂ
    solve-cont (st , inj₂ x) =
      bindˣ (solve-red (st , inj₂ x)
        ⟨≈⟩ iterₚ-cong bodyᴹ bodyᵂ loop-red (st , x))

    cont-red : (r : Stᵂ × ((⊥ ⊎ Bool) ⊎ Loopᵂ)) → (contᵢ bodyᵂ r >>=ₚ verdictᵂ) ≈ₚ contᵂ r
    cont-red (st , inj₁ o) = >>=ₚ-identityˡ (st , o) verdictᵂ
    cont-red (_  , inj₂ _) = ≈refl

  point-red : (x : ⊤ᵛ) → MC.point Sᴹ x
                        ≈ₚ (MC.point (MC.state u) x >>=ₚ λ su → returnₚ (play d , su))
  point-red x = >>=ₚ-identityˡ (ttᵛ , x) _ ⟨≈⟩ >>=ₚ-identityˡ (play d) _

  -- The induction: an environment about to play `e` against `u` in state `su`
  -- observes layer 1's run of `u` on `e`.  Each `ask` costs two loop passes.
  play-run : (su : MC.St u) (e : Strat (Neg B) (Pos B))
           → (playˢ B e >>=ₚ λ q → contᵂ ((proj₁ q , su) , outE B (proj₂ q)))
             ≈ₚ runᴹFrom u su e
  play-run su (out v)    = >>=ₚ-identityˡ (play (out v) , inj₂ v) _
  play-run su (coin μ k) =
      >>=ₚ-assoc (coinₚ μ) (λ c → playˢ B (k c)) _
    ⟨≈⟩ bindᶠ (λ c → play-run su (k c))
  play-run su (ask q k)  =
      >>=ₚ-identityˡ (susp k , inj₁ q) _
    ⟨≈⟩ bindˣ (iterₚ-fix bodyᵂ ((susp k , su) , inj₁ q))
    ⟨≈⟩ bindˣ (>>=ₚ-assoc (MC.step u (su , inj₂ q)) _ (contᵢ bodyᵂ))
    ⟨≈⟩ >>=ₚ-assoc (MC.step u (su , inj₂ q)) _ verdictᵂ
    ⟨≈⟩ bindᶠ resume-loop
    where
    -- The process's answer resumes the environment: the second pass.
    resume-loop : (r : MC.St u × (⊥ ⊎ Pos B))
                → ((returnₚ ((susp k , proj₁ r) , outU B (proj₂ r)) >>=ₚ contᵢ bodyᵂ)
                    >>=ₚ verdictᵂ)
                  ≈ₚ resumeᴹ u (λ su′ p → runᴹFrom u su′ (k p)) r
    resume-loop (_   , inj₁ e) = ⊥-elim e
    resume-loop (su′ , inj₂ p) =
        bindˣ (>>=ₚ-identityˡ ((susp k , su′) , inj₂ (inj₂ p)) (contᵢ bodyᵂ))
      ⟨≈⟩ cont-red ((susp k , su′) , inj₂ (inj₂ p))
      ⟨≈⟩ bindˣ (iterₚ-fix bodyᵂ ((susp k , su′) , inj₂ p))
      ⟨≈⟩ bindˣ (>>=ₚ-assoc (playˢ B (k p)) _ (contᵢ bodyᵂ))
      ⟨≈⟩ >>=ₚ-assoc (playˢ B (k p)) _ verdictᵂ
      ⟨≈⟩ bindᶠ (λ w → bindˣ (>>=ₚ-identityˡ ((proj₁ w , su′) , outE B (proj₂ w))
                                             (contᵢ bodyᵂ))
                 ⟨≈⟩ cont-red ((proj₁ w , su′) , outE B (proj₂ w)))
      ⟨≈⟩ play-run su′ (k p)

  -- …and the composite's one activation enters that induction at the tick.
  step-run : (su : MC.St u)
           → runᴹFrom (pairedᴹ B d u) (play d , su) (ask tt out) ≈ₚ runᴹFrom u su d
  step-run su =
      bindᶠ resume-red
    ⟨≈⟩ bindˣ (trace-red (play d , su) (inj₂ tt))
    ⟨≈⟩ >>=ₚ-assoc (kᵂ B u ((play d , su) , inj₁ (inj₂ tt))) solveᵂ verdictᵂ
    ⟨≈⟩ bindᶠ solve-cont
    ⟨≈⟩ >>=ₚ-assoc (playˢ B d) _ contᵂ
    ⟨≈⟩ bindᶠ (λ q → >>=ₚ-identityˡ ((proj₁ q , su) , outE B (proj₂ q)) contᵂ)
    ⟨≈⟩ play-run su d

adequacy : Adequacy
adequacy B u d =
    runᴹ-resp-≈ᴹ {Ωᴵ} (compose-≈ᴹ B d u) (ask tt out)
  ⟨≈⟩ bindˣ (point-red B u d ttᵛ)
  ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state u) ttᵛ) _ _
  ⟨≈⟩ bindᶠ (λ su → >>=ₚ-identityˡ (play d , su) _)
  ⟨≈⟩ bindᶠ (step-run B u d)
