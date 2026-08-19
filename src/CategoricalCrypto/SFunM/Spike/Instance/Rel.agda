{-# OPTIONS --safe --without-K #-}

-- Certifies `CategoricalCrypto.SFunM.Spike.Mealy` at `𝒱 = Rels`: a machine's step
-- is an honest relation `S × A ⇸ S × B` with no monad in sight, and the possibility
-- monad's kernels embed into it by list membership.

open import Categories.Category.Instance.Rels using (Rels)
open import Categories.Category.Monoidal.Bundle using (SymmetricMonoidalCategory)
open import Categories.Category.Monoidal.Instance.Rels using (Rels-Monoidal; Rels-Symmetric)

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List)
open import Data.List.Effectful using (monad)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (>>=-∈↔)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic.Base using (⊤; tt)
open import Effect.Monad using (RawMonad)
open import Function.Bundles using (Inverse)
open import Level using (0ℓ; Lift; lift)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

import CategoricalCrypto.SFunM.Spike.Mealy as Mealy

module CategoricalCrypto.SFunM.Spike.Instance.Rel where

Rel-SMC : SymmetricMonoidalCategory (Level.suc 0ℓ) (Level.suc 0ℓ) 0ℓ
Rel-SMC = record { U = Rels 0ℓ 0ℓ ; monoidal = Rels-Monoidal ; symmetric = Rels-Symmetric }

open Mealy Rel-SMC
open RawMonad (monad {0ℓ}) using (_>>=_; pure)
open SymmetricMonoidalCategory Rel-SMC
open Machine
open State

private variable A B C S Msg : Obj

------------------------------------------------------------------------
-- What the instance means

step-on-Rels : (f : Machine A B) → (St f ⊗₀ A ⇒ St f ⊗₀ B) ≡ (St f × A → St f × B → Set)
step-on-Rels _ = refl

pow-on-Rels : pow 2 A ≡ (A × A × ⊤)
pow-on-Rels = refl

-- An initial state is an arbitrary subset of the state space, and the discard is an
-- arbitrary subset too; neither is forced, unlike at a cartesian `𝒱`.
point-on-Rels : (unit ⇒ S) ≡ (⊤ → S → Set)
point-on-Rels = refl

discard-on-Rels : (S ⇒ unit) ≡ (S → ⊤ → Set)
discard-on-Rels = refl

------------------------------------------------------------------------
-- Membership witnesses for `run` and `eval`

pattern r₃ = lift refl , lift refl , lift refl

run-suc : (f : Machine A B) (n : ℕ) {s s′ s″ : St f} {a : A} {b : B}
          {as : pow n A} {bs : pow n B}
        → step f (s , a) (s′ , b) → run f n (s′ , as) (s″ , bs)
        → run f (suc n) (s , a , as) (s″ , b , bs)
run-suc _ _ h r = _ , (_ , (_ , r₃ , (h , lift refl)) , r₃)
                    , (_ , (_ , (_ , r₃ , r₃) , (r , lift refl)) , (_ , r₃ , r₃))

-- The base case is inlined rather than a `run f 0` lemma of its own: `pow 0 A = unit`
-- erases `A`, so such a lemma would leave the interface object undetermined.
run-one : (f : Machine A B) {s s′ : St f} {a : A} {b : B} {u : pow 0 A}
        → step f (s , a) (s′ , b) → run f 1 (s , a , u) (s′ , b , u)
run-one f h = run-suc f 0 h (lift refl)

eval-intro : (f : Machine A B) (n : ℕ) {s s′ : St f} {as : pow n A} {bs : pow n B}
           → point (state f) tt s → run f n (s , as) (s′ , bs) → discard (state f) s′ tt
           → eval f n as bs
eval-intro _ _ p r d =
  _ , (_ , (_ , (_ , lift refl , (p , lift refl)) , r) , (d , lift refl)) , lift refl

-- The converses.  Every intermediate object has to be split for the structural
-- shuffles to reduce, hence the wildcard tuples.
run-suc-inv : (f : Machine A B) (n : ℕ) {s s″ : St f} {a : A} {b : B}
              {as : pow n A} {bs : pow n B}
            → run f (suc n) (s , a , as) (s″ , b , bs)
            → ∃ λ s′ → step f (s , a) (s′ , b) × run f n (s′ , as) (s″ , bs)
run-suc-inv _ _ ( (_ , _ , _)
                , ( ((_ , _) , _) , (((_ , _) , _) , r₃ , (h , lift refl)) , r₃ )
                , ( ((_ , _) , _)
                  , ( ((_ , _) , _) , ((_ , _ , _) , r₃ , r₃) , (r , lift refl) )
                  , ( (_ , _ , _) , r₃ , r₃ ) ) ) = _ , h , r

eval-inv : (f : Machine A B) (n : ℕ) {as : pow n A} {bs : pow n B} → eval f n as bs
         → ∃ λ s → ∃ λ s′ →
             point (state f) tt s × run f n (s , as) (s′ , bs) × discard (state f) s′ tt
eval-inv _ _ ( (_ , _)
             , ( (_ , _)
               , ( (_ , _) , ((_ , _) , lift refl , (p , lift refl)) , r )
               , (d , lift refl) )
             , lift refl ) = _ , _ , p , r , d

------------------------------------------------------------------------
-- A nondeterministic cut

-- The first round commits to forwarding (`just true`) or dropping (`just false`);
-- afterwards the link is deterministic.  `CategoricalCrypto.Examples.Possibilistic.Cut`
-- is the same machine written with the possibility monad.
data CutStep {Msg : Set} : REL (Maybe Bool × Maybe Msg) (Maybe Bool × Maybe Msg) 0ℓ where
  commit-pass : {m : Maybe Msg} → CutStep (nothing    , m) (just true  , m)
  commit-drop : {m : Maybe Msg} → CutStep (nothing    , m) (just false , nothing)
  pass        : {m : Maybe Msg} → CutStep (just true  , m) (just true  , m)
  drop        : {m : Maybe Msg} → CutStep (just false , m) (just false , nothing)

Cut : Machine (Maybe Msg) (Maybe Msg)
Cut = record
  { state = record { obj = Maybe Bool ; point = λ _ s → s ≡ nothing ; discard = λ _ _ → ⊤ }
  ; step  = CutStep
  }

Cut-passes : {m₁ m₂ : Msg} → eval Cut 2 (just m₁ , just m₂ , tt) (just m₁ , just m₂ , tt)
Cut-passes = eval-intro Cut 2 refl
  (run-suc Cut 1 commit-pass (run-one Cut pass)) tt

Cut-drops : {m₁ m₂ : Msg} → eval Cut 2 (just m₁ , just m₂ , tt) (nothing , nothing , tt)
Cut-drops = eval-intro Cut 2 refl
  (run-suc Cut 1 commit-drop (run-one Cut drop)) tt

-- …and those are the only two behaviours.
Cut-rounds : {m₁ m₂ : Msg} {y₁ y₂ : Maybe Msg} {s s′ s″ : Maybe Bool}
           → s ≡ nothing → CutStep (s , just m₁) (s′ , y₁) → CutStep (s′ , just m₂) (s″ , y₂)
           → y₁ ≡ just m₁ × y₂ ≡ just m₂ ⊎ y₁ ≡ nothing × y₂ ≡ nothing
Cut-rounds refl commit-pass pass = inj₁ (refl , refl)
Cut-rounds refl commit-drop drop = inj₂ (refl , refl)

Cut-only : {m₁ m₂ : Msg} {y₁ y₂ : Maybe Msg} {u : pow 0 (Maybe Msg)}
         → eval Cut 2 (just m₁ , just m₂ , tt) (y₁ , y₂ , u)
         → y₁ ≡ just m₁ × y₂ ≡ just m₂ ⊎ y₁ ≡ nothing × y₂ ≡ nothing
Cut-only e =
  let _ , _ , p  , r  , _ = eval-inv Cut 2 e
      _ , h₁ , r₁         = run-suc-inv Cut 1 r
      _ , h₂ , _          = run-suc-inv Cut 0 r₁
  in Cut-rounds p h₁ h₂

------------------------------------------------------------------------
-- The possibilistic layer inside the relational one

-- `CategoricalCrypto.Examples.Possibilistic.kernel-on-Types` pins the elementwise
-- kernel to `S × A → List (S × B)`; membership turns it into a relation.
⟦_⟧ : (S × A → List (S × B)) → REL (S × A) (S × B) 0ℓ
⟦ k ⟧ x y = y ∈ k x

-- `Rels`' hom equality is pointwise set equality of the two kernels, so `⟦_⟧` is
-- faithful for exactly the quotient the elementwise layer uses.
hom-≈-is-set-equality : {k k′ : S × A → List (S × B)}
  → (⟦ k ⟧ ≈ ⟦ k′ ⟧) ≡ ((∀ {x y} → y ∈ k x → y ∈ k′ x) × (∀ {x y} → y ∈ k′ x → y ∈ k x))
hom-≈-is-set-equality = refl

⟦pure⟧ : {g : S × A → S × B} → ⟦ (λ x → pure (g x)) ⟧ ≈ (λ x y → y ≡ g x)
⟦pure⟧ = (λ { (here p) → p ; (there ()) }) , here

⟦>>=⟧ : {k : S × A → List (S × B)} {k′ : S × B → List (S × C)}
      → ⟦ (λ x → k x >>= k′) ⟧ ≈ ⟦ k′ ⟧ ∘ ⟦ k ⟧
⟦>>=⟧ {k = k} {k′} = (λ {x} {y} → Inverse.from (>>=-∈↔ {xs = k x} {k′} {y}))
                   , (λ {x} {y} → Inverse.to (>>=-∈↔ {xs = k x} {k′} {y}))
