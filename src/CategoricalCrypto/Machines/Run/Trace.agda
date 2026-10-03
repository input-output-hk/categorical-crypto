{-# OPTIONS --safe --without-K --guardedness #-}

-- `Machines.Run.Raw`'s hypothesis discharged at a TRACED machine, and then
-- at a G-COMPOSITE, which is a traced machine whose step has a kernel.
--
-- `Machines.Trace.traceStep` is `solve ∘ k ∘ id ⊗₁ i₁`: the two wirings are
-- pure, so `Settles-ret⋆` takes them one step at a time, and the loop is
-- `Dp.Settle.Iter.Settles-iter`, which needs a round-trip bound.
--
-- Everything is built at the literal `traceStep` term, which IS the bind chain
-- below definitionally: `Settles` carries a syntactic `Halts` and a supremum can
-- be approached without being reached, so no `Settles` fact rides an `_≈ₚ_`
-- rearrangement or a `_≈ᴹ_` (`docs/fcom-uc.md` §1).
--
-- A G-composite's step is `Machines.Collapse.kᴳ`, whose kernel is the two
-- factors' kernels routed the same way (`Kᴳ`).  What `𝒢ₚ` hands over is only
-- `MS.≈ᴹ`-equal to that trace, so the crossing happens once, at the settled
-- reading of a CLOSED run: `rawPr` is applied to the collapsed machine and
-- `Dp.Settle.Attains-≈ₚ` carries its `cum` family over to `g 𝒢.∘ f`.

open import Data.Bool.Base using (Bool)
open import Data.Empty
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational using (ℚ)
open import Data.Sum.Base
open import Data.Unit.Polymorphic.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Settle.Iter

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Run
open import CategoricalCrypto.Machines.Run.Raw
open import CategoricalCrypto.Machines.Run.Sim
open import CategoricalCrypto.Strategy

import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.Machines.Run.Trace where

open Col using (module 𝒢)

------------------------------------------------------------------------
-- A traced machine's kernel

module _ (S : MC.State) (A B X : Set)
         (Kk : MC.obj S × (A ⊎ X) → Dist⊥ (MC.obj S × (B ⊎ X)))
  where

  module Lk = Loop (λ (w : MC.obj S × X) → Kk (proj₁ w , inj₂ (proj₂ w)))

  Ktrace : ℕ → MC.obj S × A → Dist⊥ (MC.obj S × B)
  Ktrace f z = Kk (proj₁ z , inj₁ (proj₂ z)) >>=⊥ Lk.exitK f

  module _ (k  : MC.obj S × (A ⊎ X) → Dₚ (MC.obj S × (B ⊎ X)))
           (kS : (z : MC.obj S × (A ⊎ X)) → Σ[ i ∈ ℕ ] Settles i (k z) (Kk z))
    where

    open Lk

    -- `id ⊗₁ pureᵏ h` at a point is three `returnₚ`s and nothing else.
    private
      ⊗S : {Y Z : Set} (h : Y → Z) (m : MC.obj S) (y : Y)
         → Σ[ i ∈ ℕ ] Settles i ((V.id V.⊗₁ K.pureᵏ h) (m , y)) (return⊥ (m , h y))
      ⊗S h m y = Settles-ret⋆ m _ (return⊥ (m , h y))
                   (Settles-ret⋆ (h y) _ (return⊥ (m , h y)) (1 , Settles-return (m , h y)))

      -- One pass of the loop: the same junction, then the body.
      lbS : (w : MC.obj S × X)
          → Σ[ i ∈ ℕ ] Settles i (MT.loopBody S A B X k w) (Kk (proj₁ w , inj₂ (proj₂ w)))
      lbS (m , x) =
        let i , s = ⊗S inj₂ m x
            j , t = Settles-bind⋆ i _ k (return⊥ (m , inj₂ x)) Kk s kS
        in j , Settles-resp (return⊥ (m , inj₂ x) >>=⊥ Kk) (Kk (m , inj₂ x))
                            (λ Q → >>=⊥-identityˡ (m , inj₂ x) Kk (maybeℚ Q)) t

    -- The round-trip bound: a rank that drops on every pass, strictly below `f`
    -- on the whole state space.  At a G-composite it counts the messages the upper
    -- factor has still to bounce off the lower one.
    module _ (rank : MC.obj S × X → ℕ) (rk : Ranked rank (MT.loopBody S A B X k))
             (f : ℕ) (rb : (w : MC.obj S × X) → rank w < f) where

      private
        solveS : (r : MC.obj S × (B ⊎ X))
               → Σ[ i ∈ ℕ ] Settles i (MT.solve S A B X k r) (exitK f r)
        solveS (m , inj₁ b) =
          Settles-ret⋆ (inj₁ (m , b)) _ (return⊥ (m , b)) (1 , Settles-return (m , b))
        solveS (m , inj₂ x) =
          Settles-ret⋆ (inj₂ (m , x)) _ (loopK f (m , x))
                       (Settles-iter (MT.loopBody S A B X k) _ lbS rank rk f (m , x) (rb (m , x)))

      trace-settles : (z : MC.obj S × A)
                    → Σ[ i ∈ ℕ ] Settles i (MT.traceStep S A B X k z) (Ktrace f z)
      trace-settles (m , a) =
        let i , s = ⊗S inj₁ m a
            j , t = Settles-bind⋆ i _ k (return⊥ (m , inj₁ a)) Kk s kS
            l , v = Settles-bind⋆ j _ (MT.solve S A B X k)
                                  (return⊥ (m , inj₁ a) >>=⊥ Kk) (exitK f) t solveS
        in l , Settles-resp ((return⊥ (m , inj₁ a) >>=⊥ Kk) >>=⊥ exitK f) (Ktrace f (m , a))
                            (λ Q → >>=⊥-congʳ (exitK f) (return⊥ (m , inj₁ a) >>=⊥ Kk) (Kk (m , inj₁ a))
                                               (>>=⊥-identityˡ (m , inj₁ a) Kk) (maybeℚ Q))
                            v

------------------------------------------------------------------------
-- The collapsed step's kernel

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
         (g : MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
  where

  traceᴳ : MC.Machine (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)
  traceᴳ = MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (MC.mk (Col.Sᴳ g f) (Col.kᴳ g f))

  -- `Machines.Collapse`'s routings with their object implicits pinned; left
  -- open they are four metas per clause and none of them solves.
  outF : A⁻ ⊎ B⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  outF = Col.outᶠ

  outG : B⁻ ⊎ C⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
  outG = Col.outᵍ

  loopᴳ : Body (MC.St g × MC.St f) (B⁻ ⊎ B⁺) (A⁻ ⊎ C⁺)
  loopᴳ = MT.loopBody (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (Col.kᴳ g f)

  -- …read at the dispatch itself: `loopBody` is `kᴳ` behind the two `returnₚ`
  -- junctions `id ⊗₁ i₂` spends, and those reach the one point.
  ranked-from-kᴳ : (rank : (MC.St g × MC.St f) × (B⁻ ⊎ B⁺) → ℕ)
                 → ((w : (MC.St g × MC.St f) × (B⁻ ⊎ B⁺)) (i : ℕ)
                    → Supp i (Col.kᴳ g f (proj₁ w , inj₂ (proj₂ w))) (Drops rank (rank w)))
                 → Ranked rank loopᴳ
  ranked-from-kᴳ rank h (m , x) i =
    Supp-bind _ i _ (Col.kᴳ g f)
      (Supp-bind _ i (returnₚ m) _
        (Supp-return _ m
          (λ j → Supp-bind _ j (returnₚ (inj₂ x)) _
                   (Supp-return _ (inj₂ x) (Supp-return _ (m , inj₂ x) (h (m , x))) j))
          i))

  module _ (Kg : MC.St g → B⁺ ⊎ C⁻ → Dist⊥ (MC.St g × (B⁻ ⊎ C⁺)))
           (Kf : MC.St f → A⁺ ⊎ B⁻ → Dist⊥ (MC.St f × (A⁻ ⊎ B⁺)))
    where

    Kᴳ : (MC.St g × MC.St f) × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺))
       → Dist⊥ ((MC.St g × MC.St f) × ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)))
    Kᴳ ((sg , sf) , inj₁ (inj₁ a)) =
      Kf sf (inj₁ a) >>=⊥ λ r → return⊥ ((sg , proj₁ r) , outF (proj₂ r))
    Kᴳ ((sg , sf) , inj₁ (inj₂ c)) =
      Kg sg (inj₂ c) >>=⊥ λ r → return⊥ ((proj₁ r , sf) , outG (proj₂ r))
    Kᴳ ((sg , sf) , inj₂ (inj₁ b)) =
      Kf sf (inj₂ b) >>=⊥ λ r → return⊥ ((sg , proj₁ r) , outF (proj₂ r))
    Kᴳ ((sg , sf) , inj₂ (inj₂ b)) =
      Kg sg (inj₁ b) >>=⊥ λ r → return⊥ ((proj₁ r , sf) , outG (proj₂ r))

    dispatch-f : (sg : MC.St g) (sf : MC.St f) (z : A⁺ ⊎ B⁻)
                 (Q : (MC.St g × MC.St f) × ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)) → ℚ)
               → E⊥ (Kf sf z >>=⊥ λ r → return⊥ ((sg , proj₁ r) , outF (proj₂ r))) Q
                 ≡ E⊥ (Kf sf z) (λ r → Q ((sg , proj₁ r) , outF (proj₂ r)))
    dispatch-f sg sf z Q = E⊥-map (λ r → (sg , proj₁ r) , outF (proj₂ r)) (Kf sf z) Q

    dispatch-g : (sg : MC.St g) (sf : MC.St f) (y : B⁺ ⊎ C⁻)
                 (Q : (MC.St g × MC.St f) × ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)) → ℚ)
               → E⊥ (Kg sg y >>=⊥ λ r → return⊥ ((proj₁ r , sf) , outG (proj₂ r))) Q
                 ≡ E⊥ (Kg sg y) (λ r → Q ((proj₁ r , sf) , outG (proj₂ r)))
    dispatch-g sg sf y Q = E⊥-map (λ r → (proj₁ r , sf) , outG (proj₂ r)) (Kg sg y) Q

    module Lp = Lk (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) Kᴳ

    K∘ : ℕ → (MC.St g × MC.St f) × (A⁺ ⊎ C⁻) → Dist⊥ ((MC.St g × MC.St f) × (A⁻ ⊎ C⁺))
    K∘ = Ktrace (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) Kᴳ

    -- The three steps an activation is read by: it enters the dispatch, and
    -- each answer either leaves the loop or re-enters it a round shorter.
    K∘-enter : (fuel : ℕ) (z : (MC.St g × MC.St f) × (A⁺ ⊎ C⁻))
               (Q : (MC.St g × MC.St f) × (A⁻ ⊎ C⁺) → ℚ)
             → E⊥ (K∘ fuel z) Q
               ≡ E⊥ (Kᴳ (proj₁ z , inj₁ (proj₂ z))) (λ w → E⊥ (Lp.exitK fuel w) Q)
    K∘-enter fuel z Q = E⊥-bind (Kᴳ (proj₁ z , inj₁ (proj₂ z))) (Lp.exitK fuel) Q

    exit-out : (j : ℕ) (s : MC.St g × MC.St f) (o : A⁻ ⊎ C⁺)
               (Q : (MC.St g × MC.St f) × (A⁻ ⊎ C⁺) → ℚ)
             → E⊥ (Lp.exitK j (s , inj₁ o)) Q ≡ Q (s , o)
    exit-out j s o Q = E⊥-return (s , o) Q

    exit-loop : (j : ℕ) (s : MC.St g × MC.St f) (x : B⁻ ⊎ B⁺)
                (Q : (MC.St g × MC.St f) × (A⁻ ⊎ C⁺) → ℚ)
              → E⊥ (Lp.exitK (suc j) (s , inj₂ x)) Q
                ≡ E⊥ (Kᴳ (s , inj₂ x)) (λ w → E⊥ (Lp.exitK j w) Q)
    exit-loop j s x Q = E⊥-bind (Kᴳ (s , inj₂ x)) (Lp.exitK j) Q

    module _ (gS : (m : MC.St g) (y : B⁺ ⊎ C⁻)
                 → Σ[ i ∈ ℕ ] Settles i (MC.step g (m , y)) (Kg m y))
             (fS : (m : MC.St f) (z : A⁺ ⊎ B⁻)
                 → Σ[ i ∈ ℕ ] Settles i (MC.step f (m , z)) (Kf m z))
      where

      kᴳ-settles : (z : (MC.St g × MC.St f) × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)))
                 → Σ[ i ∈ ℕ ] Settles i (Col.kᴳ g f z) (Kᴳ z)
      kᴳ-settles ((sg , sf) , inj₁ (inj₁ a)) = Settles-map⋆ (λ r → (sg , proj₁ r) , outF (proj₂ r)) (fS sf (inj₁ a))
      kᴳ-settles ((sg , sf) , inj₁ (inj₂ c)) = Settles-map⋆ (λ r → (proj₁ r , sf) , outG (proj₂ r)) (gS sg (inj₂ c))
      kᴳ-settles ((sg , sf) , inj₂ (inj₁ b)) = Settles-map⋆ (λ r → (sg , proj₁ r) , outF (proj₂ r)) (fS sf (inj₂ b))
      kᴳ-settles ((sg , sf) , inj₂ (inj₂ b)) = Settles-map⋆ (λ r → (proj₁ r , sf) , outG (proj₂ r)) (gS sg (inj₁ b))

      compose-settles : (rank : (MC.St g × MC.St f) × (B⁻ ⊎ B⁺) → ℕ) (rk : Ranked rank loopᴳ)
                        (fuel : ℕ) (rb : (w : (MC.St g × MC.St f) × (B⁻ ⊎ B⁺)) → rank w < fuel)
                        (z : (MC.St g × MC.St f) × (A⁺ ⊎ C⁻))
                      → Σ[ i ∈ ℕ ] Settles i (MC.step traceᴳ z) (K∘ fuel z)
      compose-settles = trace-settles (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) Kᴳ
                                      (Col.kᴳ g f) kᴳ-settles

------------------------------------------------------------------------
-- …and at a CLOSED composite, where the run lives

-- The domain summand is empty, so the trace's answers are all on the right and
-- the kernel is `Machines.Run.Raw`'s.
module _ {B⁺ B⁻ : Set} {C : Iface}
         (g : MC.Machine (B⁺ ⊎ Neg C) (B⁻ ⊎ Pos C)) (f : MC.Machine (⊥ ⊎ B⁻) (⊥ ⊎ B⁺))
         (Kg : MC.St g → B⁺ ⊎ Neg C → Dist⊥ (MC.St g × (B⁻ ⊎ Pos C)))
         (Kf : MC.St f → ⊥ ⊎ B⁻ → Dist⊥ (MC.St f × (⊥ ⊎ B⁺)))
         (fuel : ℕ)
  where

  private
    Stᴳ : Set
    Stᴳ = MC.St g × MC.St f

    -- The trace's codomain summand `⊥ ⊎ Pos C` read back as `Pos C`; `ansᴹ`
    -- is its inverse everywhere the type is inhabited.
    shed : Stᴳ × (⊥ ⊎ Pos C) → Stᴳ × Pos C
    shed (s , inj₂ p) = s , p

    trᴳ : Stᴳ × (⊥ ⊎ Neg C) → Dist⊥ (Stᴳ × (⊥ ⊎ Pos C))
    trᴳ = K∘ g f Kg Kf fuel

  Kᶜˡ : Stᴳ → Neg C → Dist⊥ (Stᴳ × Pos C)
  Kᶜˡ m q = Dmap⊥ shed (trᴳ (m , inj₂ q))

  -- …and read at the trace, where the domain summand is still in the way.
  Kᶜˡ-read : (m : Stᴳ) (q : Neg C) (Q : Stᴳ × Pos C → ℚ) (Q′ : Stᴳ × (⊥ ⊎ Pos C) → ℚ)
           → ((s : Stᴳ) (p : Pos C) → Q (s , p) ≡ Q′ (s , inj₂ p))
           → E⊥ (Kᶜˡ m q) Q ≡ E⊥ (trᴳ (m , inj₂ q)) Q′
  Kᶜˡ-read m q Q Q′ pt =
    trans (E⊥-map shed (trᴳ (m , inj₂ q)) Q) (E⊥-cong-P (trᴳ (m , inj₂ q)) _ Q′ point)
    where
    point : (w : Stᴳ × (⊥ ⊎ Pos C)) → Q (shed w) ≡ Q′ w
    point (s , inj₂ p) = pt s p

  module _ (gS : (m : MC.St g) (y : B⁺ ⊎ Neg C)
               → Σ[ i ∈ ℕ ] Settles i (MC.step g (m , y)) (Kg m y))
           (fS : (m : MC.St f) (z : ⊥ ⊎ B⁻)
               → Σ[ i ∈ ℕ ] Settles i (MC.step f (m , z)) (Kf m z))
           (rank : (MC.St g × MC.St f) × (B⁻ ⊎ B⁺) → ℕ) (rk : Ranked rank (loopᴳ g f))
           (rb : (w : (MC.St g × MC.St f) × (B⁻ ⊎ B⁺)) → rank w < fuel)
    where

    compose-StepSettles : StepSettles (traceᴳ g f) Kᶜˡ
    compose-StepSettles m q =
      proj₁ raw , Settles-resp (trᴳ (m , inj₂ q)) (Dmap⊥ ansᴹ (Kᶜˡ m q)) value (proj₂ raw)
      where
      raw = compose-settles g f Kg Kf gS fS rank rk fuel rb (m , inj₂ q)

      value : (Q : Stᴳ × (⊥ ⊎ Pos C) → ℚ)
            → E⊥ (trᴳ (m , inj₂ q)) Q ≡ E⊥ (Dmap⊥ ansᴹ (Kᶜˡ m q)) Q
      value Q = sym (trans (E⊥-map ansᴹ (Kᶜˡ m q) Q) (Kᶜˡ-read m q _ Q λ _ _ → refl))

    compose-pr : (σ₀ : Dist⊥ Stᴳ) (n₀ : ℕ)
                 (pt : Settles n₀ (MC.point (Col.Sᴳ g f) tt) σ₀)
                 (b : Bool) (d : Strat (Neg C) (Pos C))
               → Attains (runᴹ (𝒢._∘_ g f) d) (indᵇ b) (E⊥ (σ₀ >>=⊥ λ m → runWith⊥ Kᶜˡ m d) (indᵇ b))
    compose-pr σ₀ n₀ pt b d =
      Attains-≈ₚ (runᴹ (traceᴳ g f) d) _ (indᵇ b) (indᵇ-nn b)
        (E⊥ (σ₀ >>=⊥ λ m → runWith⊥ Kᶜˡ m d) (indᵇ b))
        (rawPr (traceᴳ g f) Kᶜˡ compose-StepSettles σ₀ n₀ pt b d)
        (runᴹ-resp-≈ᴹ (Col.collapse≈ g f) d)
