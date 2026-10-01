{-# OPTIONS --safe --without-K #-}

-- Observing a closed protocol: play a strategy against it and read the verdict
-- distribution.  `hitRun` samples the state only at activation boundaries: a
-- protocol step is atomic, so a bad state entered and left inside one step is
-- not observed.

open import Data.Bool.Base
open import Data.Empty
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational renaming (_≤_ to _≤ℚ_)
open import Data.Unit.Base
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as RS

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Advantage
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid
open import ProbabilisticLogic.Distribution.Uniform

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Observe where

private variable X : Set
                 A B : Iface

------------------------------------------------------------------------
-- Reading call trees
------------------------------------------------------------------------

evalC : Calls unitᴵ X → Dist⊥ X
evalC (ret x)    = return⊥ x
evalC (call q _) = ⊥-elim q
evalC (coin μ k) = μ >>=ᴹ λ b → evalC (k b)
evalC dead       = return-ℚ nothing

-- Stated at any coin-homomorphic reading rather than at `evalC`, so that it
-- also covers a step seen through a caller's `serve` (`evalC-serve-uniformVec`).
uniformVec-bind : {Z : Set} (⟦_⟧ : Calls A X → Dist-ℚ Z)
                → (∀ μ g → ⟦ coin μ g ⟧ ≈Mℚ (μ >>=ᴹ λ b → ⟦ g b ⟧))
                → ∀ m (f : Vec Bool m → Calls A X)
                → ⟦ uniformVec m f ⟧ ≈Mℚ (uniform-Vec m >>=ᴹ λ v → ⟦ f v ⟧)
uniformVec-bind ⟦_⟧ hom zero    f =
  Mℚ.sym {x = uniform-Vec zero >>=ᴹ (λ v → ⟦ f v ⟧)} {y = ⟦ f [] ⟧}
    (>>=ᴹ-identityˡ [] (λ v → ⟦ f v ⟧))
uniformVec-bind ⟦_⟧ hom (suc m) f = begin
  ⟦ uniformVec (suc m) f ⟧
    ≈⟨ hom uniform-Bool (λ b → uniformVec m λ v → f (b ∷ v)) ⟩
  (uniform-Bool >>=ᴹ Fb)
    ≈⟨ >>=ᴹ-congˡ uniform-Bool Fb Hb
         (λ b → uniformVec-bind ⟦_⟧ hom m (λ v → f (b ∷ v))) ⟩
  (uniform-Bool >>=ᴹ Hb)
    ≈˘⟨ >>=ᴹ-congˡ uniform-Bool Db Hb (λ b → Dmap->>= (b ∷_) (uniform-Vec m) G) ⟩
  (uniform-Bool >>=ᴹ Db)
    ≈˘⟨ >>=ᴹ-assoc uniform-Bool (λ b → Dmap (b ∷_) (uniform-Vec m)) G ⟩
  (uniform-Vec (suc m) >>=ᴹ G) ∎
  where
    G  = λ v → ⟦ f v ⟧
    Fb = λ b → ⟦ uniformVec m (λ v → f (b ∷ v)) ⟧
    Hb = λ b → uniform-Vec m >>=ᴹ λ v → G (b ∷ v)
    Db = λ b → Dmap (b ∷_) (uniform-Vec m) >>=ᴹ G
    open RS (Mℚ-setoid _)

------------------------------------------------------------------------
-- What a step can reach
------------------------------------------------------------------------

-- `dead` has no leaf, so a safety invariant is never owed at a deadlock
-- (`evalC-support` sends it to the `nothing` sink's `⊤`).
AllLeaves : (X → Set) → Calls A X → Set
AllLeaves P (ret x)    = P x
AllLeaves P (call _ k) = ∀ r → AllLeaves P (k r)
AllLeaves P (coin _ k) = ∀ b → AllLeaves P (k b)
AllLeaves P dead       = ⊤

evalC-support : {P : X → Set} (t : Calls unitᴵ X) → AllLeaves P t → OnSupport⊥ P (evalC t)
evalC-support (ret x)    p = OnSupport-return p
evalC-support (call q _) _ = ⊥-elim q
evalC-support (coin μ k) p = OnSupport-bind μ (λ b → evalC (k b))
                               (All.universal (λ _ → tt) _)
                               (λ b _ → evalC-support (k b) (p b))
evalC-support dead       _ = OnSupport-return tt

-- Through a caller's `serve`, the shape a composite's step has.  `serve`
-- commutes with the coin structure only up to an equality of continuations,
-- so the commutation is stated at the reading and at the leaves, never as a
-- tree equation.
module _ {B C : Iface} (P₂ : Protocol B C) (P₁ : Protocol unitᴵ B) where

  private
    Cont : Set
    Cont = Pos B → Calls B (St P₂ × Pos C)

  AllLeaves-serve-uniformVec :
      {P : (St P₂ × St P₁) × Pos C → Set} (k : Cont) (m : ℕ)
      (f : Vec Bool m → Calls unitᴵ (St P₁ × Pos B))
    → (∀ v → AllLeaves P (serve P₂ P₁ k (f v)))
    → AllLeaves P (serve P₂ P₁ k (uniformVec m f))
  AllLeaves-serve-uniformVec k zero    f h = h []
  AllLeaves-serve-uniformVec k (suc m) f h b =
    AllLeaves-serve-uniformVec k m (λ v → f (b ∷ v)) (λ v → h (b ∷ v))

  evalC-serve-uniformVec :
      (k : Cont) (m : ℕ) (f : Vec Bool m → Calls unitᴵ (St P₁ × Pos B))
    → evalC (serve P₂ P₁ k (uniformVec m f))
      ≈Mℚ (uniform-Vec m >>=ᴹ λ v → evalC (serve P₂ P₁ k (f v)))
  evalC-serve-uniformVec k = uniformVec-bind (λ t → evalC (serve P₂ P₁ k t)) (λ _ _ _ → refl)

module _ (P : Protocol unitᴵ B) where

  kernel : St P → Neg B → Dist⊥ (St P × Pos B)
  kernel s q = evalC (step P s q)

  runFrom : St P → Strat (Neg B) (Pos B) → Dist⊥ Bool
  runFrom = runWith⊥ kernel

  runObs : Strat (Neg B) (Pos B) → Dist⊥ Bool
  runObs = runFrom (init P)

  Prᵇ : Bool → Strat (Neg B) (Pos B) → ℚ
  Prᵇ b d = Prᵇ⊥ b (runObs d)

  Pr : Strat (Neg B) (Pos B) → ℚ
  Pr = Prᵇ true

  -- Divergence weighs 0, so this is the COMPLETED-RUN hit
  -- (`docs/state-event-contract.md` §1, row 11): a run that hits and then
  -- deadlocks does not count, the prefix that stops at the hit does.
  module _ (Bad : St P → Bool) where

    hitFrom : Bool → St P → Strat (Neg B) (Pos B) → Dist⊥ Bool
    hitFrom acc s (out _)    = return⊥ acc
    hitFrom acc s (ask q k)  = kernel s q >>=⊥ λ (s′ , r) → hitFrom (acc ∨ Bad s′) s′ (k r)
    hitFrom acc s (coin μ k) = μ >>=ᴹ λ b → hitFrom acc s (k b)

    hitRun : Strat (Neg B) (Pos B) → Dist⊥ Bool
    hitRun = hitFrom (Bad (init P)) (init P)

    PrHit : Strat (Neg B) (Pos B) → ℚ
    PrHit d = Pr₁⊥ (hitRun d)

------------------------------------------------------------------------
-- Statements
------------------------------------------------------------------------

Bounded : (P : Protocol unitᴵ B)
        → (Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)) → (ℕ → ℚ) → Set
Bounded {B} P bad ε = (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → Pr P (bad d) ≤ℚ ε q

BoundedHit : (P : Protocol unitᴵ B) → (St P → Bool) → (ℕ → ℚ) → Set
BoundedHit {B} P Bad ε = (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → PrHit P Bad d ≤ℚ ε q

infix 4 _≈adv[_]_

-- No budget-`q` strategy separates the two systems by more than `δ q`, at
-- EITHER verdict: at a fixed `b` divergence moves the advantage exactly as a
-- `¬ b` answer does, so it is the `false` reading that tells an implementation
-- which answers `false` from one which diverges (`docs/rewrite-verdict.md`,
-- Addendum 4, item 2).
_≈adv[_]_ : Protocol unitᴵ B → (ℕ → ℚ) → Protocol unitᴵ B → Set
_≈adv[_]_ {B} P δ P′ =
  (b : Bool) (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
  → advᵇ⊥ b (runObs P d) (runObs P′ d) ≤ℚ δ q
