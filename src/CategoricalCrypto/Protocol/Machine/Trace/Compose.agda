{-# OPTIONS --safe --without-K --guardedness #-}

-- `Protocol.Machine.Trace` at a G-COMPOSITE: `𝒢ₚ`'s `_∘_` identified with a
-- traced machine whose step has a kernel.
--
-- `Machines.Collapse` reads the composite's step off as `kᴳ`, a four-way
-- dispatch sending each letter to the factor that owns it.  Its kernel is the
-- two factors' kernels routed the same way (`Kᴳ`), and the loop between them
-- is `trace-settles`'s, at a rank counting the messages the upper factor still
-- has to bounce off the lower one.
--
-- What `𝒢ₚ` hands over is `S.≈ᴹ`-equal to that trace, not definitionally it,
-- and a `Settles` witness cannot ride an `_≈ₚ_` (`docs/fcom-uc.md` §1).  What
-- can is the settled READING a CLOSED run produces, so the crossing happens
-- once, at the end: `rawPr` is applied to the collapsed machine and
-- `Dp.Settle.cum-settled-≈ₚ` carries its `cum` family over to `g 𝒢.∘ f`.

open import Categories.Category using (Category)

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_; _<_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (tt)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform using (indᵇ)
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (indᵇ-nn)
open import ProbabilisticLogic.Dp.Settle
open import ProbabilisticLogic.Dp.Support

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction using (runWith⊥)
open import CategoricalCrypto.Machines.Base using (𝒢ₚ)
open import CategoricalCrypto.Protocol.Machine using (runᴹ)
open import CategoricalCrypto.Protocol.Machine.Raw
open import CategoricalCrypto.Protocol.Machine.Trace
open import CategoricalCrypto.Strategy using (Strat)
open import CategoricalCrypto.UC.Machine.Run using (runᴹ-resp-≈ᴹ)

import CategoricalCrypto.Machines.Collapse as Col

module CategoricalCrypto.Protocol.Machine.Trace.Compose where

private module 𝒢 = Category (𝒢ₚ 0ℓ)

------------------------------------------------------------------------
-- The collapsed step's kernel

module _ {A⁺ A⁻ B⁺ B⁻ C⁺ C⁻ : Set}
         (g : Col.MC.Machine (B⁺ ⊎ C⁻) (B⁻ ⊎ C⁺)) (f : Col.MC.Machine (A⁺ ⊎ B⁻) (A⁻ ⊎ B⁺))
         (Kg : Col.MC.St g → B⁺ ⊎ C⁻ → Dist⊥ (Col.MC.St g × (B⁻ ⊎ C⁺)))
         (Kf : Col.MC.St f → A⁺ ⊎ B⁻ → Dist⊥ (Col.MC.St f × (A⁻ ⊎ B⁺)))
         (gS : (m : Col.MC.St g) (y : B⁺ ⊎ C⁻)
             → Σ[ i ∈ ℕ ] Settles i (Col.MC.step g (m , y)) (Kg m y))
         (fS : (m : Col.MC.St f) (z : A⁺ ⊎ B⁻)
             → Σ[ i ∈ ℕ ] Settles i (Col.MC.step f (m , z)) (Kf m z))
  where

  -- The composite as ONE traced machine with product state.
  traceᴳ : Col.MC.Machine (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺)
  traceᴳ = Col.MT.traceᴹ (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (Col.MC.mk (Col.Sᴳ g f) (Col.kᴳ g f))

  collapse≈ : traceᴳ Col.S.≈ᴹ 𝒢._∘_ {A⁺ , A⁻} {B⁺ , B⁻} {C⁺ , C⁻} g f
  collapse≈ = Col.S.⟺ᴹ (Col.collapseᵀ g f) Col.S.○ᴹ Col.compose-raw≈∘ᴳ g f

  -- `Machines.Collapse`'s routings with their object implicits pinned; left
  -- open they are four metas per clause and none of them solves.
  private
    outF : A⁻ ⊎ B⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
    outF = Col.outᶠ

    outG : B⁻ ⊎ C⁺ → (A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)
    outG = Col.outᵍ

  Kᴳ : (Col.MC.St g × Col.MC.St f) × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺))
     → Dist⊥ ((Col.MC.St g × Col.MC.St f) × ((A⁻ ⊎ C⁺) ⊎ (B⁻ ⊎ B⁺)))
  Kᴳ ((sg , sf) , inj₁ (inj₁ a)) =
    Kf sf (inj₁ a) >>=⊥ λ r → return⊥ ((sg , proj₁ r) , outF (proj₂ r))
  Kᴳ ((sg , sf) , inj₁ (inj₂ c)) =
    Kg sg (inj₂ c) >>=⊥ λ r → return⊥ ((proj₁ r , sf) , outG (proj₂ r))
  Kᴳ ((sg , sf) , inj₂ (inj₁ b)) =
    Kf sf (inj₂ b) >>=⊥ λ r → return⊥ ((sg , proj₁ r) , outF (proj₂ r))
  Kᴳ ((sg , sf) , inj₂ (inj₂ b)) =
    Kg sg (inj₁ b) >>=⊥ λ r → return⊥ ((proj₁ r , sf) , outG (proj₂ r))

  private
    dispF : (sg : Col.MC.St g) (sf : Col.MC.St f) (z : A⁺ ⊎ B⁻)
          → Σ[ i ∈ ℕ ] Settles i
              (Col.MC.step f (sf , z) >>=ₚ λ r → returnₚ ((sg , proj₁ r) , outF (proj₂ r)))
              (Kf sf z >>=⊥ λ r → return⊥ ((sg , proj₁ r) , outF (proj₂ r)))
    dispF sg sf z =
      Settles-bind⋆ (proj₁ (fS sf z)) (Col.MC.step f (sf , z)) _ (Kf sf z) _ (proj₂ (fS sf z))
        λ r → 1 , Settles-return ((sg , proj₁ r) , outF (proj₂ r))

    dispG : (sg : Col.MC.St g) (sf : Col.MC.St f) (y : B⁺ ⊎ C⁻)
          → Σ[ i ∈ ℕ ] Settles i
              (Col.MC.step g (sg , y) >>=ₚ λ r → returnₚ ((proj₁ r , sf) , outG (proj₂ r)))
              (Kg sg y >>=⊥ λ r → return⊥ ((proj₁ r , sf) , outG (proj₂ r)))
    dispG sg sf y =
      Settles-bind⋆ (proj₁ (gS sg y)) (Col.MC.step g (sg , y)) _ (Kg sg y) _ (proj₂ (gS sg y))
        λ r → 1 , Settles-return ((proj₁ r , sf) , outG (proj₂ r))

  kᴳ-settles : (z : (Col.MC.St g × Col.MC.St f) × ((A⁺ ⊎ C⁻) ⊎ (B⁻ ⊎ B⁺)))
             → Σ[ i ∈ ℕ ] Settles i (Col.kᴳ g f z) (Kᴳ z)
  kᴳ-settles ((sg , sf) , inj₁ (inj₁ a)) = dispF sg sf (inj₁ a)
  kᴳ-settles ((sg , sf) , inj₁ (inj₂ c)) = dispG sg sf (inj₂ c)
  kᴳ-settles ((sg , sf) , inj₂ (inj₁ b)) = dispF sg sf (inj₂ b)
  kᴳ-settles ((sg , sf) , inj₂ (inj₂ b)) = dispG sg sf (inj₁ b)

  -- The round-trip bound, at the composite's loop.
  module Lp = I (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (Col.kᴳ g f) Kᴳ kᴳ-settles

  -- …read at the dispatch itself: `loopBody` is `kᴳ` behind the two `returnₚ`
  -- junctions `id ⊗₁ i₂` spends, and those reach the one point.
  ranked-from-kᴳ : (rank : (Col.MC.St g × Col.MC.St f) × (B⁻ ⊎ B⁺) → ℕ)
                 → ((w : (Col.MC.St g × Col.MC.St f) × (B⁻ ⊎ B⁺)) (i : ℕ)
                    → Supp i (Col.kᴳ g f (proj₁ w , inj₂ (proj₂ w))) (Lp.Drops rank (rank w)))
                 → Lp.Ranked rank
  ranked-from-kᴳ rank h (m , x) i =
    Supp-bind _ i _ (Col.kᴳ g f)
      (Supp-bind _ i (returnₚ m) _
        (Supp-return _ m
          (λ j → Supp-bind _ j (returnₚ (inj₂ x)) _
                   (Supp-return _ (inj₂ x) (Supp-return _ (m , inj₂ x) (h (m , x))) j))
          i))

  module _ (rank : (Col.MC.St g × Col.MC.St f) × (B⁻ ⊎ B⁺) → ℕ) (rk : Lp.Ranked rank)
           (fuel : ℕ) (rb : (w : (Col.MC.St g × Col.MC.St f) × (B⁻ ⊎ B⁺)) → rank w < fuel)
    where

    K∘ : (Col.MC.St g × Col.MC.St f) × (A⁺ ⊎ C⁻)
       → Dist⊥ ((Col.MC.St g × Col.MC.St f) × (A⁻ ⊎ C⁺))
    K∘ = Ktrace (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺) (Col.kᴳ g f) Kᴳ kᴳ-settles
                rank rk fuel rb

    compose-settles : (z : (Col.MC.St g × Col.MC.St f) × (A⁺ ⊎ C⁻))
                    → Σ[ i ∈ ℕ ] Settles i (Col.MC.step traceᴳ z) (K∘ z)
    compose-settles = trace-settles (Col.Sᴳ g f) (A⁺ ⊎ C⁻) (A⁻ ⊎ C⁺) (B⁻ ⊎ B⁺)
                                    (Col.kᴳ g f) Kᴳ kᴳ-settles rank rk fuel rb

------------------------------------------------------------------------
-- …and at a CLOSED composite, where the run lives

-- The domain summand is empty, so the trace's answers are all on the right and
-- the kernel is `Protocol.Machine.Raw`'s.
module _ {B⁺ B⁻ : Set} {C : Iface}
         (g : Col.MC.Machine (B⁺ ⊎ Neg C) (B⁻ ⊎ Pos C)) (f : Col.MC.Machine (⊥ ⊎ B⁻) (⊥ ⊎ B⁺))
         (Kg : Col.MC.St g → B⁺ ⊎ Neg C → Dist⊥ (Col.MC.St g × (B⁻ ⊎ Pos C)))
         (Kf : Col.MC.St f → ⊥ ⊎ B⁻ → Dist⊥ (Col.MC.St f × (⊥ ⊎ B⁺)))
         (gS : (m : Col.MC.St g) (y : B⁺ ⊎ Neg C)
             → Σ[ i ∈ ℕ ] Settles i (Col.MC.step g (m , y)) (Kg m y))
         (fS : (m : Col.MC.St f) (z : ⊥ ⊎ B⁻)
             → Σ[ i ∈ ℕ ] Settles i (Col.MC.step f (m , z)) (Kf m z))
         (rank : (Col.MC.St g × Col.MC.St f) × (B⁻ ⊎ B⁺) → ℕ)
         (rk : Lp.Ranked g f Kg Kf gS fS rank)
         (fuel : ℕ) (rb : (w : (Col.MC.St g × Col.MC.St f) × (B⁻ ⊎ B⁺)) → rank w < fuel)
  where

  private
    Stᴳ : Set
    Stᴳ = Col.MC.St g × Col.MC.St f

    -- The trace's codomain summand `⊥ ⊎ Pos C` read back as `Pos C`; `ansᴹ`
    -- is its inverse everywhere the type is inhabited.
    shed : Stᴳ × (⊥ ⊎ Pos C) → Stᴳ × Pos C
    shed (s , inj₂ p) = s , p

    trᴳ : Stᴳ × (⊥ ⊎ Neg C) → Dist⊥ (Stᴳ × (⊥ ⊎ Pos C))
    trᴳ = K∘ g f Kg Kf gS fS rank rk fuel rb

  Kᶜˡ : Stᴳ → Neg C → Dist⊥ (Stᴳ × Pos C)
  Kᶜˡ m q = Dmap⊥ shed (trᴳ (m , inj₂ q))

  compose-StepSettles : StepSettles (traceᴳ g f Kg Kf gS fS) Kᶜˡ
  compose-StepSettles m q =
    proj₁ raw , Settles-resp (trᴳ (m , inj₂ q)) (Dmap⊥ ansᴹ (Kᶜˡ m q)) value (proj₂ raw)
    where
    raw = compose-settles g f Kg Kf gS fS rank rk fuel rb (m , inj₂ q)

    value : (Q : Stᴳ × (⊥ ⊎ Pos C) → ℚ)
          → E⊥ (trᴳ (m , inj₂ q)) Q ≡ E⊥ (Dmap⊥ ansᴹ (Kᶜˡ m q)) Q
    value Q = sym (trans (E⊥-map ansᴹ (Kᶜˡ m q) Q)
                         (trans (E⊥-map shed (trᴳ (m , inj₂ q)) (λ p → Q (ansᴹ p)))
                                (E⊥-cong-P (trᴳ (m , inj₂ q)) _ Q point)))
      where
      point : (w : Stᴳ × (⊥ ⊎ Pos C)) → Q (ansᴹ (shed w)) ≡ Q w
      point (s , inj₂ p) = refl

  -- The closed composite's verdict mass, past a budget of its own: `rawPr` at
  -- the collapsed machine, read at `𝒢ₚ`'s own composite.
  compose-pr : (σ₀ : Dist⊥ Stᴳ) (n₀ : ℕ)
               (pt : Settles n₀ (Col.MC.point (Col.Sᴳ g f) tt) σ₀)
               (b : Bool) (d : Strat (Neg C) (Pos C))
             → Σ[ n ∈ ℕ ] ((i : ℕ)
                 → cum (n + i) (runᴹ (𝒢._∘_ {⊥ , ⊥} {B⁺ , B⁻} {Pos C , Neg C} g f) d) (indᵇ b)
                 ≡ E⊥ (σ₀ >>=⊥ λ m → runWith⊥ Kᶜˡ m d) (indᵇ b))
  compose-pr σ₀ n₀ pt b d =
    cum-settled-≈ₚ (runᴹ (traceᴳ g f Kg Kf gS fS) d) _ (indᵇ b) (indᵇ-nn b)
      (E⊥ (σ₀ >>=⊥ λ m → runWith⊥ Kᶜˡ m d) (indᵇ b)) (proj₁ raw) (proj₂ raw)
      (runᴹ-resp-≈ᴹ (collapse≈ g f Kg Kf gS fS) d)
    where raw = rawPr (traceᴳ g f Kg Kf gS fS) Kᶜˡ compose-StepSettles σ₀ n₀ pt b d
