{-# OPTIONS --safe --without-K --guardedness #-}

-- `prAgree`: past a budget the machine image's cumulative mass IS layer 1's
-- verdict probability.  It is `Protocol.Machine.Raw.rawPr` at the image, whose
-- step kernel is layer 1's `kernel` read on idle states: each activation
-- settles by induction on the call tree it drives (`drive-settles`), and the
-- kernel's run is layer 1's run by a bisimulation on `idle`.

open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Nat.Base as ℕ
open import Data.Product.Base
open import Data.Rational as ℚ
open import Data.Rational.Properties
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality

import Data.Nat.Properties as ℕP

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Settle

open import CategoricalCrypto.GamePlaying.Partial
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine
open import CategoricalCrypto.Protocol.Machine.Raw
open import CategoricalCrypto.Protocol.Observe
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Machine.Agree where

module _ {B : Iface} (P : Protocol unitᴵ B) where

  -- The image's step kernel: layer 1's on an idle state, divergence on a
  -- suspended one (`stepᴹ`'s off-protocol case).
  Kᴾ : MSt P → Neg B → Dist⊥ (MSt P × Pos B)
  Kᴾ (idle s) q = Dmap⊥ (map₁ idle) (kernel P s q)
  Kᴾ (wait _) q = return-ℚ nothing

  private
    tgt : Dist⊥ (St P × Pos B) → Dist⊥ (MSt P × (⊥ ⊎ Pos B))
    tgt μ = Dmap⊥ ansᴹ (Dmap⊥ (map₁ idle) μ)

    reading : (μ : Dist⊥ (St P × Pos B)) (G : MSt P × (⊥ ⊎ Pos B) → ℚ)
            → E⊥ (tgt μ) G ≡ E⊥ μ (λ sr → G (idle (proj₁ sr) , inj₂ (proj₂ sr)))
    reading μ G = trans (E⊥-map ansᴹ (Dmap⊥ (map₁ idle) μ) G)
                        (E⊥-map (map₁ idle) μ (λ p → G (ansᴹ p)))

    nothing₀ : {X : Set} (G : X → ℚ) → E⊥ (return-ℚ nothing) G ≡ 0ℚ
    nothing₀ G = lookupᴰℚ-return nothing (maybeℚ G)

  drive-settles : (T : Calls unitᴵ (St P × Pos B))
                → Σ[ n ∈ ℕ ] Settles n (drive P T) (tgt (evalC T))
  drive-settles (ret (s , r)) =
    1 , Settles-resp (return⊥ (idle s , inj₂ r)) (tgt (return⊥ (s , r)))
          (λ G → trans (E⊥-return (idle s , inj₂ r) G)
                   (sym (trans (reading (return⊥ (s , r)) G)
                               (E⊥-return (s , r) (λ sr → G (idle (proj₁ sr) , inj₂ (proj₂ sr)))))))
          (Settles-return (idle s , inj₂ r))
  drive-settles (call q _) = ⊥-elim q
  drive-settles (coin μ k) =
    let n , st = Settles-bind⋆ 2 (coinₚ μ) (λ c → drive P (k c)) (Dmap just μ)
                   (λ c → tgt (evalC (k c))) (Settles-coin μ) (λ c → drive-settles (k c))
    in n , Settles-resp (Dmap just μ >>=⊥ λ c → tgt (evalC (k c))) (tgt (evalC (coin μ k)))
             (λ G → trans (E⊥-coin μ (λ c → tgt (evalC (k c))) G)
                   (trans (E-bind μ (λ c → tgt (evalC (k c))) (maybeℚ G))
                   (trans (lookupᴰℚ-cong-P (entries μ) λ c → reading (evalC (k c)) G)
                   (sym (trans (reading (evalC (coin μ k)) G)
                               (E-bind μ (λ c → evalC (k c))
                                  (maybeℚ λ sr → G (idle (proj₁ sr) , inj₂ (proj₂ sr)))))))))
             st
  drive-settles dead =
    0 , Settles-resp (return-ℚ nothing) (tgt (return-ℚ nothing))
          (λ G → trans (nothing₀ G)
                   (sym (trans (reading (return-ℚ nothing) G)
                               (nothing₀ λ sr → G (idle (proj₁ sr) , inj₂ (proj₂ sr))))))
          Settles-bot

  ker : StepSettles (morphism P) Kᴾ
  ker (idle s) q = drive-settles (step P s q)
  ker (wait _) q =
    0 , Settles-resp (return-ℚ nothing) (Dmap⊥ ansᴹ (return-ℚ nothing))
          (λ G → trans (nothing₀ G)
                   (sym (trans (E⊥-map ansᴹ (return-ℚ nothing) G) (nothing₀ (λ p → G (ansᴹ p))))))
          Settles-bot

-- The interaction is finite — the strategy tree bounds it and every call tree
-- is inductive — so past some depth the cumulative mass is *exactly* layer 1's
-- verdict probability.  It is asked at EITHER verdict, since that is what the
-- observation relation compares (`Dp.Advantage`'s header); `indᵇ b` is never
-- inspected, so both are one induction.
prAgree : {B : Iface} (b : Bool) (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B))
        → Σ[ n ∈ ℕ ] ((m : ℕ) → cum (n ℕ.+ m) (runᴹ (morphism P) d) (indᵇ b) ≡ Prᵇ P b d)
prAgree b P d =
  let n , h = rawPr (morphism P) (Kᴾ P) (ker P) (return⊥ (idle (init P))) 1
                    (Settles-return _) b d
  in n , λ m → trans (h m)
       (trans (>>=⊥-identityˡ (idle (init P)) (λ s → runWith⊥ (Kᴾ P) s d) (maybeℚ (indᵇ b)))
              (runWith⊥-bisim (Kᴾ P) (kernel P) (λ m s → m ≡ idle s)
                 (λ { .(idle s) s refl q F F′ h →
                      trans (E⊥-map (map₁ idle) (kernel P s q) F)
                            (E⊥-cong-P (kernel P s q) _ F′ λ t → h _ t refl refl) })
                 d (idle (init P)) (init P) refl (indᵇ b)))

------------------------------------------------------------------------
-- Layer 1's verdict probability and the machine image's run

-- Layer 1's verdict probability bounds EVERY finite approximant of the machine
-- image's run: `prAgree` reads it off past one budget and `Pr≤` is monotone.
upper-run : {B : Iface} (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B)) {r : ℚ}
          → Pr P d ℚ.≤ r → Upper (runᴹ (morphism P) d) r
upper-run P d bnd k =
  let n , h = prAgree true P d
  in ≤-trans (≤-trans (Pr≤-mono true (runᴹ (morphism P) d) (ℕP.m≤n+m k n))
                      (≤-reflexive (h k)))
             bnd

-- …and back, at the one depth `prAgree` names: layer 1's verdict probability
-- IS an approximant of the machine image's run, so bounding every approximant
-- bounds it.
run-upper : {B : Iface} (P : Protocol unitᴵ B) (d : Strat (Neg B) (Pos B)) {r : ℚ}
          → Upper (runᴹ (morphism P) d) r → Pr P d ℚ.≤ r
run-upper P d up =
  let n , h = prAgree true P d in ≤-trans (≤-reflexive (sym (h 0))) (up (n ℕ.+ 0))
