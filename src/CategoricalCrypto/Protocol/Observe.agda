{-# OPTIONS --safe --without-K #-}

-- Observing a closed protocol: play a strategy against it and read the verdict
-- distribution.  Everything is total structural recursion — the strategy tree
-- bounds the interaction, so no budget, level, or clock appears anywhere.
--
--   run    — the strategy's own verdict
--   hitRun — "was a bad state ever reached", the observable safety properties
--            are stated over (the state is sampled at activation boundaries;
--            protocol steps are atomic)
--
-- and the statement vocabulary: `Bounded`/`BoundedHit` (a safety bound against
-- every budget-`q` strategy), `_≈adv[_]_` (indistinguishability at advantage
-- `δ`, read at BOTH verdicts so that an implementation which answers `false` is
-- not identified with one which diverges), and `transfer` — a bound on one
-- system becomes a bound on an indistinguishable one with `δ` added, which is
-- how a UC emulation carries a safety property from the ideal world to the real
-- one.

open import Data.Bool.Base
open import Data.Empty
import Data.List.Relation.Unary.All as All
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product.Base
open import Data.Rational renaming (_+_ to _+ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as RS

open import ProbabilisticLogic.Prelude
open import ProbabilisticLogic.Distribution.RationalDist using
  (OnSupport; OnSupport-bind; OnSupport-return)

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Strategy

module CategoricalCrypto.Protocol.Observe where

private variable X : Set
                 A B : Iface

------------------------------------------------------------------------
-- Running a strategy
------------------------------------------------------------------------

-- A closed call tree has no one to call: it collapses to a distribution.
evalC : Calls unitᴵ X → Dist⊥ X
evalC (ret x)    = return⊥ x
evalC (call q _) = ⊥-elim q
evalC (coin μ k) = μ >>=ᴹ λ b → evalC (k b)
evalC dead       = return-ℚ nothing

-- Any reading of call trees that turns a coin node into a bind reads a
-- `uniformVec` cascade as the uniform distribution on bit vectors.  Stated at
-- the reading rather than at `evalC` because an example needs it twice: once
-- for a closed oracle's own step, and once for that step seen through the
-- `serve` of a caller grafted onto it (`Examples.MerkleDamgard`).
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
    ≈˘⟨ >>=ᴹ-congˡ uniform-Bool Db Hb (λ b → Mℚ.trans
          {i = Db b}
          {j = uniform-Vec m >>=ᴹ λ v → (return-ℚ (b ∷ v) >>=ᴹ G)}
          {k = Hb b}
          (>>=ᴹ-assoc (uniform-Vec m) (λ v → return-ℚ (b ∷ v)) G)
          (>>=ᴹ-congˡ (uniform-Vec m) (λ v → return-ℚ (b ∷ v) >>=ᴹ G) (λ v → G (b ∷ v))
            (λ v → >>=ᴹ-identityˡ (b ∷ v) G))) ⟩
  (uniform-Bool >>=ᴹ Db)
    ≈˘⟨ >>=ᴹ-assoc uniform-Bool (λ b → Dmap (b ∷_) (uniform-Vec m)) G ⟩
  (uniform-Vec (suc m) >>=ᴹ G)
    ∎
  where
    G  = λ v → ⟦ f v ⟧
    Fb = λ b → ⟦ uniformVec m (λ v → f (b ∷ v)) ⟧
    Hb = λ b → uniform-Vec m >>=ᴹ λ v → G (b ∷ v)
    Db = λ b → Dmap (b ∷_) (uniform-Vec m) >>=ᴹ G
    open RS (Mℚ-setoid _)

------------------------------------------------------------------------
-- What a step can reach
------------------------------------------------------------------------

-- A predicate at every leaf of a call tree.  `dead` has no leaf, so
-- divergence is vacuously fine, and `evalC-support` turns that into the
-- `nothing` sink's `⊤`: a safety invariant is never owed at a deadlock.
AllLeaves : (X → Set) → Calls A X → Set
AllLeaves P (ret x)    = P x
AllLeaves P (call _ k) = ∀ r → AllLeaves P (k r)
AllLeaves P (coin _ k) = ∀ b → AllLeaves P (k b)
AllLeaves P dead       = ⊤

Reached : (X → Set) → Maybe X → Set
Reached P (just x) = P x
Reached P nothing  = ⊤

evalC-support : {P : X → Set} (t : Calls unitᴵ X)
              → AllLeaves P t → OnSupport (Reached P) (evalC t)
evalC-support (ret x)    p = OnSupport-return p
evalC-support (call q _) _ = ⊥-elim q
evalC-support (coin μ k) p = OnSupport-bind μ (λ b → evalC (k b))
                               (All.universal (λ _ → tt) _)
                               (λ b _ → evalC-support (k b) (p b))
evalC-support dead       _ = OnSupport-return tt

AllLeaves-uniformVec : {P : X → Set} (m : ℕ) (f : Vec Bool m → Calls A X)
                     → (∀ v → AllLeaves P (f v)) → AllLeaves P (uniformVec m f)
AllLeaves-uniformVec zero    f h = h []
AllLeaves-uniformVec (suc m) f h b =
  AllLeaves-uniformVec m (λ v → f (b ∷ v)) (λ v → h (b ∷ v))

-- The same two facts through the `serve` of a caller grafted onto the
-- sampling protocol, which is the shape a COMPOSITE's step has (a sampling
-- resource is reached through its client).  `serve` commutes with the coin
-- structure, but the trees differ by an equality of continuations, so the
-- commutation is available at the reading and at the leaves, never as a tree
-- equation.
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
  evalC-serve-uniformVec k =
    uniformVec-bind (λ t → evalC (serve P₂ P₁ k t)) (λ _ _ _ → refl)

module _ (P : Protocol unitᴵ B) where

  runFrom : St P → Strat (Neg B) (Pos B) → Dist⊥ Bool
  runFrom s (out b)    = return⊥ b
  runFrom s (ask q k)  = evalC (step P s q) >>=⊥ λ (s′ , r) → runFrom s′ (k r)
  runFrom s (coin μ k) = μ >>=ᴹ λ b → runFrom s (k b)

  run : Strat (Neg B) (Pos B) → Dist⊥ Bool
  run = runFrom (init P)

  -- The mass of verdict `b`.  `Pr` is the `true` reading, which is the one a
  -- probability-of-event statement (`Bounded`) asks for; `_≈adv[_]_` compares
  -- both, divergence weighing 0 under either indicator.
  Prᵇ : Bool → Strat (Neg B) (Pos B) → ℚ
  Prᵇ b d = Prᵇ⊥ b (run d)

  Pr : Strat (Neg B) (Pos B) → ℚ
  Pr = Prᵇ true

  -- The verdict is "a state satisfying `Bad` was reached", regardless of what
  -- the strategy outputs; divergence weighs 0 (a violation must be reached).
  module _ (Bad : St P → Bool) where

    hitFrom : Bool → St P → Strat (Neg B) (Pos B) → Dist⊥ Bool
    hitFrom acc s (out _)    = return⊥ acc
    hitFrom acc s (ask q k)  =
      evalC (step P s q) >>=⊥ λ (s′ , r) → hitFrom (acc ∨ Bad s′) s′ (k r)
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
-- which answers `false` from one which diverges (proposal §1,
-- `docs/kb/frontier/15-probabilistic-uc-model.typ`).
_≈adv[_]_ : Protocol unitᴵ B → (ℕ → ℚ) → Protocol unitᴵ B → Set
_≈adv[_]_ {B} P δ P′ =
  (b : Bool) (q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d
  → advᵇ⊥ b (run P d) (run P′ d) ≤ℚ δ q

private
  ≤-shift : (x y a b : ℚ) → x ≤ℚ a → ∣ y -ℚ x ∣ℚ ≤ℚ b → y ≤ℚ (a +ℚ b)
  ≤-shift x y a b xa yb = begin
    y                 ≡⟨ sym (−-+-cancel y x) ⟩
    (y -ℚ x) +ℚ x     ≤⟨ +-mono-≤ (p≤∣p∣ (y -ℚ x)) xa ⟩
    ∣ y -ℚ x ∣ℚ +ℚ a  ≤⟨ +-monoˡ-≤ a yb ⟩
    b +ℚ a            ≡⟨ +-comm b a ⟩
    a +ℚ b            ∎
    where open ≤-Reasoning

-- A bound on `P` becomes a bound on an indistinguishable `P′`, at `ε + δ`.
transfer : {P P′ : Protocol unitᴵ B}
           {bad : Strat (Neg B) (Pos B) → Strat (Neg B) (Pos B)} {ε δ : ℕ → ℚ}
         → ((q : ℕ) (d : Strat (Neg B) (Pos B)) → asks≤ q d → asks≤ q (bad d))
         → P ≈adv[ δ ] P′ → Bounded P bad ε → Bounded P′ bad (λ q → ε q +ℚ δ q)
transfer {P = P} {P′} {bad} {ε} {δ} bad-asks near bound q d a =
  ≤-shift (Pr P (bad d)) (Pr P′ (bad d)) (ε q) (δ q) (bound q d a)
    (subst (_≤ℚ δ q) (adv⊥-sym (run P (bad d)) (run P′ (bad d)))
           (near true q (bad d) (bad-asks q d a)))
