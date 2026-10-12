{-# OPTIONS --safe --without-K --guardedness #-}

-- Both observations below use one resolver, including its eager initial state.
-- A resolver cannot compensate for the deferred half-terminating branch draw.

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Bundle

open import Data.Bool.Base
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Sum.Base
open import Data.Unit.Base using (⊤; tt)
import Data.Unit.Polymorphic.Base as Unit
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no; toWitness; toWitnessFalse)
open import Relation.Nullary.Negation using (¬_)

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Mass
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.ND.PM.Choice
open import CategoricalCrypto.ND.PM.Choice.Initialization
open import CategoricalCrypto.ND.PM.Choice.Initialization.Graded
open import CategoricalCrypto.ND.PM.Factor
open import CategoricalCrypto.ND.PM.Setup
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Behaviour
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.Model.Symmetric
open import CategoricalCrypto.UC.RandomSystems.FullAbstraction using (playᵒ; cupᵒ; play-cup; unhomᵒ)

import CategoricalCrypto.Machines.Core as Core

module CategoricalCrypto.ND.PM.Choice.Initialization.Example where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module P = Category 𝒫ᴵ
  module G = SymmetricMonoidalCategory 𝔾ˢ
  module Ap = AllPositive ℚ-refinement Approximationᴹ

Activation Bit : Iface
Activation = ⊤ ⇿ ⊥
Bit = Bool ⇿ ⊥

half : {X : Set} → X → Dₚ X
half x = coinₚ uniform-Bool >>=ₚ λ where
  true → returnₚ x
  false → botₚ

half-process : Proc Activation Bit
half-process = MC.mk (record { obj = Unit.⊤ ; point = λ _ → half Unit.tt }) λ where
  (k , inj₁ _) → returnₚ (k , inj₂ true)
  (_ , inj₂ ())

half-branches : ⊤ → Proc⁺ [] Activation Bit
half-branches _ = plain half-process

half-choice : Proc⁺ (⊤ ∷ []) Activation Bit
half-choice = choose {⊤} {[]} {Activation} {Bit} half-branches

zero-query one-query : Strat (Pos Activation ⊎ Neg Bit) (Neg Activation ⊎ Pos Bit)
zero-query = out true
one-query = ask (inj₁ tt) λ _ → out true

private
  half-bind : {X Y : Set} (x : X) (f : X → Dₚ Y) →
    (half x >>=ₚ f) ≈ₚ (coinₚ uniform-Bool >>=ₚ λ where true → f x ; false → botₚ)
  half-bind x f = >>=ₚ-assoc (coinₚ uniform-Bool) _ _
    ⟨≈⟩ bindᶠ (λ where true → >>=ₚ-identityˡ x f ; false → bot-bind-≈ₚ f)

  slack-bound : (x y : ℚ) → ((δ : ℚ) → 0ℚ ℚ.< δ → x ℚ.≤ y ℚ.+ δ) → x ℚ.≤ y
  slack-bound x y h = case x ℚ.≤? y of λ where
    (yes le) → le
    (no not-le) →
      let r , y<r , r<x = <-dense (≰⇒> not-le)
          pos = subst (λ z → z ℚ.< r ℚ.- y) (+-inverseʳ y) (+-monoˡ-< (ℚ.- y) y<r)
          x≤r = ≤-trans (h (r ℚ.- y) pos)
            (≤-reflexive (trans (+-comm y (r ℚ.- y)) (−-+-cancel r y)))
      in ⊥-elim (<-irrefl refl (≤-<-trans x≤r r<x))

half-zero half-one : Dₚ Bool
half-zero = runˢ half-process zero-query
half-one = runˢ half-process one-query

half-zero-law : half-zero ≈ₚ half true
half-zero-law = half-bind Unit.tt _ ⟨≈⟩ bindᶠ (λ where true → ≈refl ; false → ≈refl)

half-one-law : half-one ≈ₚ half true
half-one-law = bindᶠ (λ _ → >>=ₚ-identityˡ (Unit.tt , inj₂ true) _)
  ⟨≈⟩ half-bind Unit.tt _
  ⟨≈⟩ bindᶠ (λ where true → ≈refl ; false → ≈refl)

half-attained : Pr≤ 3 (half true) ≡ ½
half-attained = refl

private
  half-outcome : Bool → Dₚ Bool
  half-outcome true = returnₚ true
  half-outcome false = botₚ

  half-cum : (n : ℕ) → Pr≤ (suc (suc n)) (half true)
    ≡ ½ ℚ.* Pr≤ n (returnₚ true) ℚ.+ ½ ℚ.* Pr≤ n botₚ
  half-cum n = cong₂ ℚ._+_
    (cong (½ ℚ.*_) (>>=ₚ-identityˡ-cum n true half-outcome (indᵇ true)))
    (cong (½ ℚ.*_) (>>=ₚ-identityˡ-cum n false half-outcome (indᵇ true)))

half-upper : Upper (half true) ½
half-upper zero = toWitness {a? = 0ℚ ℚ.≤? ½} _
half-upper (suc zero) = ≤-trans (≤-reflexive (cum-1-bind (coinₚ uniform-Bool) half-outcome (indᵇ true)))
  (toWitness {a? = 0ℚ ℚ.≤? ½} _)
half-upper (suc (suc n)) = ≤-trans (≤-reflexive (half-cum n))
  (≤-trans (node-mono ½ ½ 0≤½ 0≤½ (cum-≤1 n (returnₚ true) (indᵇ true) (indᵇ-≤1 true))
    (≤-reflexive (botₚ-cum n (indᵇ true))))
    (≤-reflexive (trans (cong₂ ℚ._+_ (*-identityʳ ½) (*-zeroʳ ½)) (+-identityʳ ½))))

module SameResolver (resolver : Proc (Cᶠ (⊤ ∷ [])) 𝟭ᴵ) where
  module R = Resolution {⊤} {Activation} {Bit} half-branches resolver

  initial-verdict : Dₚ Bool
  initial-verdict = MC.point (MC.state resolver) Unit.tt >>=ₚ λ _ → returnₚ true

  activated-verdict : Dₚ Bool
  activated-verdict = MC.point (MC.state resolver) Unit.tt >>=ₚ λ k →
    MC.step resolver (k , inj₁ (inj₁ tt)) >>=ₚ λ _ → half true

  zero-law : runˢ R.plugged zero-query ≈ₚ initial-verdict
  zero-law = runˢ-resp-≈ᴹ R.plugged-machine zero-query ⟨≈⟩ R.run-init zero-query

  one-law : P._≈_ {Activation} {Bit} (R.branch tt) half-process → runˢ R.plugged one-query ≈ₚ activated-verdict
  one-law branch-law = runˢ-resp-≈ᴹ R.plugged-machine one-query ⟨≈⟩ R.run-init one-query
    ⟨≈⟩ bindᶠ (λ k → bindˣ (R.step-fresh k (inj₁ tt))
      ⟨≈⟩ >>=ₚ-assoc (MC.step resolver (k , inj₁ (inj₁ tt))) _ _
      ⟨≈⟩ bindᶠ (λ where
        (_ , inj₁ (inj₁ _ , tt)) → >>=ₚ-assoc (MC.point (MC.state (half-branches tt)) Unit.tt) _ _
          ⟨≈⟩ bindᶠ (λ t → bind-map (MC.step (half-branches tt) (t , R.inject (inj₁ tt))) _ _
            ⟨≈⟩ ≈sym (bind-map (MC.step (half-branches tt) (t , R.inject (inj₁ tt))) _ _))
          ⟨≈⟩ runˢ-resp-≈ᴹ branch-law one-query ⟨≈⟩ half-one-law
        (_ , inj₁ (inj₂ () , _))
        (_ , inj₂ ())))

  private
    ε : ℚ
    ε = ½ ℚ.* ½ ℚ.* ½

    ε-positive : 0ℚ ℚ.< ε
    ε-positive = toWitness {a? = 0ℚ ℚ.<? ε} _

    initial-bound : half-zero Ap.∼ᵃ initial-verdict → (δ : ℚ) → 0ℚ ℚ.< δ → (n : ℕ) →
      mass n (MC.point (MC.state resolver) Unit.tt) ℚ.≤ ½ ℚ.+ δ
    initial-bound equality δ positive n = ≤-trans
      (≤-reflexive (sym (mapₚ-cum n (λ _ → true) (MC.point (MC.state resolver) Unit.tt) (indᵇ true))))
      (bound (suc n))
      where

      bound : Upper initial-verdict (½ ℚ.+ δ)
      bound = upper-≼[] (proj₂ (≈ₚ[]-resp half-zero-law ≈refl (equality δ positive))) half-upper

    activated-bound : (r : ℚ) → ((n : ℕ) → mass n (MC.point (MC.state resolver) Unit.tt) ℚ.≤ r)
                    → Upper activated-verdict (½ ℚ.* r)
    activated-bound r initial n = ≤-trans
      (>>=ₚ-boundA n (MC.point (MC.state resolver) Unit.tt) _ (indᵇ true) (indᵇ-nn true))
      (≤-trans (cum-mono-P n (MC.point (MC.state resolver) Unit.tt) _ (λ _ → ½)
        (λ k → cum-bindʳ n (MC.step resolver (k , inj₁ (inj₁ tt))) _
          (indᵇ true) (indᵇ-nn true) ½ 0≤½ (λ _ → half-upper n)))
      (≤-trans (≤-reflexive (cum-const n (MC.point (MC.state resolver) Unit.tt) ½))
      (≤-trans (*-monoʳ-≤-nonNeg ½ ⦃ ℚ.nonNegative 0≤½ ⦄ (initial n))
        (≤-reflexive (*-comm r ½)))))

  initial-mass≤½ : half-zero Ap.∼ᵃ initial-verdict → (n : ℕ) →
    mass n (MC.point (MC.state resolver) Unit.tt) ℚ.≤ ½
  initial-mass≤½ equality n = slack-bound (mass n (MC.point (MC.state resolver) Unit.tt)) ½
    (λ δ positive → initial-bound equality δ positive n)

  activated-mass≤¼ : half-zero Ap.∼ᵃ initial-verdict → Upper activated-verdict (½ ℚ.* ½)
  activated-mass≤¼ equality = activated-bound ½ (initial-mass≤½ equality)

  no-two-strategy-match : ¬ ((half-zero Ap.∼ᵃ initial-verdict) × (half-one Ap.∼ᵃ activated-verdict))
  no-two-strategy-match (zero-match , one-match) =
    toWitnessFalse {a? = ½ ℚ.≤? (½ ℚ.* ½) ℚ.+ ε} _
      (≤-trans (≤-reflexive (sym half-attained))
        (upper-≼[] (proj₁ (≈ₚ[]-resp half-one-law ≈refl (one-match ε ε-positive)))
          (activated-mass≤¼ zero-match) 3))

half-initialization-≰UC-B : ¬ (AbstractUC._≤UC_ NDB
  {A = ifaceᵒ Activation} {X = G.unit , []} {B = ifaceᵒ Bit} {Y = G.unit , ⊤ ∷ []}
  (at [] (plain half-process)) (at (⊤ ∷ []) half-choice))
half-initialization-≰UC-B emulation =
  let resolver , equality = B-emulation⇒closed-resolver {Activation} {Bit} {⊤ ∷ []}
        half-process half-choice emulation
      module W = SameResolver resolver
      branch-law = plain-branch {Activation} {Bit} {⊤} half-process tt resolver
  in W.no-two-strategy-match
    ((λ ε pos → ≈ₚ[]-resp ≈refl W.zero-law (equality zero-query ε pos))
    , λ ε pos → ≈ₚ[]-resp ≈refl (W.one-law branch-law) (equality one-query ε pos))

------------------------------------------------------------------------
-- A total, activation-sensitive branch with a retained state update
------------------------------------------------------------------------

stateful-branch : Bool → Proc⁺ [] Bit Bit
stateful-branch b = MC.mk (initˢ Bool b) λ where
  (t , inj₁ a) → returnₚ (not t , inj₂ (inj₂ (a xor t)))
  (_ , inj₂ (inj₁ (() , _)))
  (_ , inj₂ (inj₂ ()))

stateful-choice : Proc⁺ (Bool ∷ []) Bit Bit
stateful-choice = choose {Bool} {[]} {Bit} {Bit} stateful-branch

stateful-total : Constant.TotalInitialization stateful-branch true
stateful-total = astotal-returnₚ true

stateful-≤UC-B : AbstractUC._≤UC_ NDB
  {A = ifaceᵒ Bit} {X = G.unit , []} {B = ifaceᵒ Bit} {Y = G.unit , Bool ∷ []}
  (at [] (stateful-branch true)) (at (Bool ∷ []) stateful-choice)
stateful-≤UC-B = constant-pick-≤UC-B stateful-branch true stateful-total

stateful-strategy : Strat (Pos Bit ⊎ Neg Bit) (Neg Bit ⊎ Pos Bit)
stateful-strategy = ask (inj₁ false) λ where
  (inj₁ ())
  (inj₂ first) → ask (inj₁ true) λ where
    (inj₁ ())
    (inj₂ second) → out (first ∧ second)

private module Stateful = Constant {Bool} {Bit} {Bit} stateful-branch true
private module StatefulRun = Resolution {Bool} {Bit} {Bit} stateful-branch (constant-pick true)

stateful-branch-run : runˢ (StatefulRun.branch true) stateful-strategy ≈ₚ returnₚ true
stateful-branch-run = >>=ₚ-identityˡ true _
  ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (false , inj₂ (inj₂ true)) _)
  ⟨≈⟩ >>=ₚ-identityˡ (false , inj₂ true) _
  ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (true , inj₂ (inj₂ true)) _)
  ⟨≈⟩ >>=ₚ-identityˡ (true , inj₂ true) _

stateful-closed-run : runˢ StatefulRun.plugged stateful-strategy Ap.∼ᵃ returnₚ true
stateful-closed-run ε pos = ≈ₚ[]-resp ≈refl stateful-branch-run
  (Stateful.constant-pick-≈ᴿ stateful-total stateful-strategy ε pos)

opaque
  unfolding 𝔾ᵒ sealᵒ ifaceᵒ objᵒ procᵒ unhomᵒ

  stateful-test : Strat
    (Pos (objᵒ (ifaceᵒ Bit)) ⊎ Neg (objᵒ (ifaceᵒ Bit)))
    (Neg (objᵒ (ifaceᵒ Bit)) ⊎ Pos (objᵒ (ifaceᵒ Bit)))
  stateful-test = stateful-strategy

  stateful-observed-run : Obs
    ((playᵒ (ifaceᵒ Bit) (ifaceᵒ Bit) stateful-test
      G.∘ (G.id G.⊗₁ procᵒ StatefulRun.plugged)) G.∘ cupᵒ (ifaceᵒ Bit))
    Ap.∼ᵃ returnₚ true
  stateful-observed-run ε pos = ≈ₚ[]-resp
    (≈sym (play-cup (ifaceᵒ Bit) (ifaceᵒ Bit) (procᵒ StatefulRun.plugged) stateful-test))
    ≈refl (stateful-closed-run ε pos)
