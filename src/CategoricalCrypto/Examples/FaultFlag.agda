{-# OPTIONS --safe --without-K --guardedness #-}

-- A persistent fault flag, sampled once rather than on each read, so arbitrary
-- adaptive repetition cannot amplify the initialization error.  The adversary
-- reads a version tag; the simulator translates that encoding by one revision.
-- See docs/uc-setup-random-systems.md §4.6 for the SECURITY-ONLY UC statement.

open import Categories.Category

open import Data.Bool.Base
open import Data.Empty
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ; 1ℚ; ½)
open import Data.Rational.Properties
open import Data.Rational.Properties.Ext
open import Data.Rational.Solver
open import Data.Sum.Base as Sum hiding (map₂)
open import Data.Unit.Base
open import Data.Unit.Polymorphic.Base using () renaming (tt to ttᵛ)
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage
open import ProbabilisticLogic.Dp.Mass
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise using (simFn; point-⊛)
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Machine.Wire
open import CategoricalCrypto.UC.Machine.Wire.Algebra
open import CategoricalCrypto.UC.RandomSystems.Advantage

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Examples.FaultFlag where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)
  module P = Category 𝒫ᴵ

------------------------------------------------------------------------
-- Cached randomness and version translation

data Tag : Set where
  original previous latest : Tag

previousTag : Tag → Tag
previousTag original = latest
previousTag previous = original
previousTag latest = previous

Advᴵ Honᴵ : Iface
Advᴵ = Tag ⇿ ⊤
Honᴵ = Bool ⇿ ⊤

simulator : Proc Advᴵ Advᴵ
simulator = wireᴹ previousTag id

¼ ¾ : ℚ
¼ = (+ 1) ℚ./ 4
¾ = (+ 3) ℚ./ 4

0<¼ : 0ℚ ℚ.< ¼
0<¼ = toWitness {a? = 0ℚ ℚ.<? ¼} tt

0≤¼ : 0ℚ ℚ.≤ ¼
0≤¼ = <⇒≤ 0<¼

half quarter : Dₚ Bool
half = choiceₚ ½ ½ nn nn refl (returnₚ true) (returnₚ false)
  where nn = toWitness {a? = 0ℚ ℚ.≤? ½} tt
quarter = choiceₚ ¼ ¾ 0≤¼ (toWitness {a? = 0ℚ ℚ.≤? ¾} tt) refl (returnₚ true) (returnₚ false)

cacheStep : Tag → Bool × (Pos unitᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
          → Dₚ (Bool × (Neg unitᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
cacheStep c (b , inj₁ ())
cacheStep c (b , inj₂ (inj₁ _)) = returnₚ (b , inj₂ (inj₁ c))
cacheStep c (b , inj₂ (inj₂ _)) = returnₚ (b , inj₂ (inj₂ b))

cache : Dₚ Bool → Tag → Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)
cache μ c = MC.mk (record { obj = Bool ; point = λ _ → μ }) (cacheStep c)

cleanStep : Tag → ⊤ᵛ × (Pos unitᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ))
          → Dₚ (⊤ᵛ × (Neg unitᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
cleanStep c (s , inj₁ ())
cleanStep c (s , inj₂ (inj₁ _)) = returnₚ (s , inj₂ (inj₁ c))
cleanStep c (s , inj₂ (inj₂ _)) = returnₚ (s , inj₂ (inj₂ false))

clean : Tag → Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)
clean c = MC.mk MC.Iˢ (cleanStep c)

real middle ideal : Proc unitᴵ (Advᴵ ⊗ᴵ Honᴵ)
real = cache half original
middle = cache quarter previous
ideal = clean latest

------------------------------------------------------------------------
-- Uniform positive error, from finite cumulative masses

private
  blend : ℚ → ℚ → ℚ → ℚ
  blend q x y = q ℚ.* x ℚ.+ (1ℚ ℚ.- q) ℚ.* y

  half-offset : (x y : ℚ) → blend ½ x y ≡ blend ¼ x y ℚ.+ ¼ ℚ.* (x ℚ.- y)
  half-offset = solve 2 (λ x y →
    con ½ :* x :+ (con 1ℚ :- con ½) :* y :=
    (con ¼ :* x :+ (con 1ℚ :- con ¼) :* y) :+ con ¼ :* (x :- y)) refl
    where open +-*-Solver

  quarter-offset : (x y : ℚ) → blend ¼ x y ≡ blend ½ x y ℚ.+ ¼ ℚ.* (y ℚ.- x)
  quarter-offset = solve 2 (λ x y →
    con ¼ :* x :+ (con 1ℚ :- con ¼) :* y :=
    (con ½ :* x :+ (con 1ℚ :- con ½) :* y) :+ con ¼ :* (y :- x)) refl
    where open +-*-Solver

  false-offset : (x y : ℚ) → blend ¼ x y ≡ y ℚ.+ ¼ ℚ.* (x ℚ.- y)
  false-offset = solve 2 (λ x y →
    con ¼ :* x :+ (con 1ℚ :- con ¼) :* y := y :+ con ¼ :* (x :- y)) refl
    where open +-*-Solver

  unblend-offset : (x y : ℚ) → y ≡ blend ¼ x y ℚ.+ ¼ ℚ.* (y ℚ.- x)
  unblend-offset = solve 2 (λ x y → y :=
    (con ¼ :* x :+ (con 1ℚ :- con ¼) :* y) :+ con ¼ :* (y :- x)) refl
    where open +-*-Solver

  offset-bound : (z x y : ℚ) → x ℚ.≤ 1ℚ → 0ℚ ℚ.≤ y
               → z ℚ.+ ¼ ℚ.* (x ℚ.- y) ℚ.≤ z ℚ.+ ¼
  offset-bound z x y x≤1 0≤y = +-monoʳ-≤ z
    (≤-trans (*-monoˡ-≤-nonNeg ¼ {{ℚ.nonNegative 0≤¼}}
               (≤-trans (x-y≤x x 0≤y) x≤1)) (≤-reflexive (*-identityʳ ¼)))

  test≤1 : (b v : Bool) → indᵇ b v ℚ.≤ 1ℚ
  test≤1 true true = ≤-refl
  test≤1 true false = 0≤1ℚ
  test≤1 false true = 0≤1ℚ
  test≤1 false false = ≤-refl

  half-cum : (k : Bool → Dₚ Bool) (b : Bool) (n : ℕ)
           → Pr≤[ b ] (suc (suc n)) (half >>=ₚ k)
             ≡ blend ½ (Pr≤[ b ] n (k true)) (Pr≤[ b ] n (k false))
  half-cum k b n = cong₂ ℚ._+_
    (cong (½ ℚ.*_) (>>=ₚ-identityˡ-cum n true k (indᵇ b)))
    (cong (½ ℚ.*_) (>>=ₚ-identityˡ-cum n false k (indᵇ b)))

  quarter-cum : (k : Bool → Dₚ Bool) (b : Bool) (n : ℕ)
              → Pr≤[ b ] (suc (suc n)) (quarter >>=ₚ k)
                ≡ blend ¼ (Pr≤[ b ] n (k true)) (Pr≤[ b ] n (k false))
  quarter-cum k b n = cong₂ ℚ._+_
    (cong (¼ ℚ.*_) (>>=ₚ-identityˡ-cum n true k (indᵇ b)))
    (cong (¾ ℚ.*_) (>>=ₚ-identityˡ-cum n false k (indᵇ b)))

  half-quarter : (k : Bool → Dₚ Bool) → (half >>=ₚ k) ≈ₚ[ ¼ ] (quarter >>=ₚ k)
  half-quarter k = forward , backward
    where
    forward : (half >>=ₚ k) ≼ₚ[ ¼ ] (quarter >>=ₚ k)
    forward b zero = 0 , 0≤¼
    forward b (suc zero) = 0 , ≤-trans (≤-reflexive (cum-1-bind half k (indᵇ b))) 0≤¼
    forward b (suc (suc n)) = suc (suc n) , ≤-trans
      (≤-reflexive (trans (half-cum k b n)
        (trans (half-offset x y) (cong (ℚ._+ (¼ ℚ.* (x ℚ.- y))) (sym (quarter-cum k b n))))))
      (offset-bound (Pr≤[ b ] (suc (suc n)) (quarter >>=ₚ k)) x y
        (cum-≤1 n (k true) _ (test≤1 b)) (cum-nn n (k false) _ (indᵇ-nn b)))
      where x = Pr≤[ b ] n (k true)
            y = Pr≤[ b ] n (k false)

    backward : (quarter >>=ₚ k) ≼ₚ[ ¼ ] (half >>=ₚ k)
    backward b zero = 0 , 0≤¼
    backward b (suc zero) = 0 , ≤-trans (≤-reflexive (cum-1-bind quarter k (indᵇ b))) 0≤¼
    backward b (suc (suc n)) = suc (suc n) , ≤-trans
      (≤-reflexive (trans (quarter-cum k b n)
        (trans (quarter-offset x y) (cong (ℚ._+ (¼ ℚ.* (y ℚ.- x))) (sym (half-cum k b n))))))
      (offset-bound (Pr≤[ b ] (suc (suc n)) (half >>=ₚ k)) y x
        (cum-≤1 n (k false) _ (test≤1 b)) (cum-nn n (k true) _ (indᵇ-nn b)))
      where x = Pr≤[ b ] n (k true)
            y = Pr≤[ b ] n (k false)

  quarter-false : (k : Bool → Dₚ Bool) → (quarter >>=ₚ k) ≈ₚ[ ¼ ] k false
  quarter-false k = forward , backward
    where
    forward : (quarter >>=ₚ k) ≼ₚ[ ¼ ] k false
    forward b zero = 0 , 0≤¼
    forward b (suc zero) = 0 , ≤-trans (≤-reflexive (cum-1-bind quarter k (indᵇ b))) 0≤¼
    forward b (suc (suc n)) = n , ≤-trans
      (≤-reflexive (trans (quarter-cum k b n) (false-offset x y)))
      (offset-bound y x y (cum-≤1 n (k true) _ (test≤1 b)) (cum-nn n (k false) _ (indᵇ-nn b)))
      where x = Pr≤[ b ] n (k true)
            y = Pr≤[ b ] n (k false)

    backward : k false ≼ₚ[ ¼ ] (quarter >>=ₚ k)
    backward b n = suc (suc n) , ≤-trans
      (≤-reflexive (trans (unblend-offset x y)
        (cong (ℚ._+ (¼ ℚ.* (y ℚ.- x))) (sym (quarter-cum k b n)))))
      (offset-bound (Pr≤[ b ] (suc (suc n)) (quarter >>=ₚ k)) y x
        (cum-≤1 n (k false) _ (test≤1 b)) (cum-nn n (k true) _ (indᵇ-nn b)))
      where x = Pr≤[ b ] n (k true)
            y = Pr≤[ b ] n (k false)

  cache-runFrom : (μ ν : Dₚ Bool) (c : Tag) (b : Bool)
                (d : Strat (Pos unitᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)) (Neg unitᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)))
               → runFromˢ (cache μ c) b d ≈ₚ runFromˢ (cache ν c) b d
  cache-runFrom μ ν c = runFromˢ-ϕ id λ where
    (b , inj₁ ())
    (b , inj₂ (inj₁ _)) → >>=ₚ-identityˡ (b , inj₂ (inj₁ c)) _
    (b , inj₂ (inj₂ _)) → >>=ₚ-identityˡ (b , inj₂ (inj₂ b)) _

half-quarter-cache : (c : Tag) → cache half c ≈ᴿ[ ¼ ] cache quarter c
half-quarter-cache c d = Verdict.≈⇒≈̄
  (≈ₚ[]-resp (≈sym (bindᶠ λ b → cache-runFrom half quarter c b d)) ≈refl
    (half-quarter (λ b → runFromˢ (cache quarter c) b d)))

quarter-false-cache : (c : Tag) → cache quarter c ≈ᴿ[ ¼ ] cache (returnₚ false) c
quarter-false-cache c d = Verdict.≈⇒≈̄
  (≈ₚ[]-resp (≈sym (bindᶠ λ b → cache-runFrom quarter (returnₚ false) c b d))
             (≈sym (>>=ₚ-identityˡ false _))
    (quarter-false (λ b → runFromˢ (cache (returnₚ false) c) b d)))

false-cache-clean : (c : Tag) → cache (returnₚ false) c S.≈ᴹ clean c
false-cache-clean c = S.≲⇒≈ᴹ˘ (simFn (λ _ → false)
  (λ _ → >>=ₚ-identityˡ ttᵛ _) λ where
    (s , inj₁ ())
    (s , inj₂ (inj₁ _)) → >>=ₚ-identityˡ (s , inj₂ (inj₁ c)) _
    (s , inj₂ (inj₂ _)) → >>=ₚ-identityˡ (s , inj₂ (inj₂ false)) _)

------------------------------------------------------------------------
-- The simulator actually changes the adversary's replies

cache-simulates : (μ : Dₚ Bool) (c : Tag)
                → P._≈_ {unitᴵ} {Advᴵ ⊗ᴵ Honᴵ}
                    (cache μ (previousTag c)) (P._∘_ (subᴵ {A = Honᴵ} simulator) (cache μ c))
cache-simulates μ c = S.⟺ᴹ
  (P.∘-resp-≈ˡ (sub-wire previousTag id)
    S.○ᴹ wire-∘ᴹ (Sum.map previousTag id) (Sum.map id id) (cache μ c)
    S.○ᴹ S.≲⇒≈ᴹ (S.mk-cong λ where
      (b , inj₁ ())
      (b , inj₂ (inj₁ _)) → >>=ₚ-identityˡ (b , inj₂ (inj₁ c)) _
      (b , inj₂ (inj₂ _)) → >>=ₚ-identityˡ (b , inj₂ (inj₂ b)) _))

honestRead : Strat (Pos unitᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)) (Neg unitᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ))
honestRead = ask (inj₂ (inj₂ tt)) λ where
  (inj₁ ())
  (inj₂ (inj₁ _)) → out false
  (inj₂ (inj₂ b)) → out b

cache-read : (μ : Dₚ Bool) (c : Tag) → runˢ (cache μ c) honestRead ≈ₚ μ
cache-read μ c = bindᶠ (λ b → >>=ₚ-identityˡ (b , inj₂ (inj₂ b)) _) ⟨≈⟩ >>=ₚ-identityʳ μ

clean-read : (c : Tag) → runˢ (clean c) honestRead ≈ₚ returnₚ false
clean-read c = >>=ₚ-identityˡ ttᵛ _ ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₂ (inj₂ false)) _

------------------------------------------------------------------------
-- A simulator cannot manufacture an honest fault

module _ (s : Proc Advᴵ Advᴵ) (c : Tag) where

  private
    relay : Proc (Advᴵ ⊗ᴵ Honᴵ) (Advᴵ ⊗ᴵ Honᴵ)
    relay = subᴵ s

    module L = Col.Loop
      (Pos unitᴵ ⊎ Neg (Advᴵ ⊗ᴵ Honᴵ)) (Neg unitᴵ ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ))
      (Neg (Advᴵ ⊗ᴵ Honᴵ) ⊎ Pos (Advᴵ ⊗ᴵ Honᴵ)) (Col.Sᴳ relay (clean c)) (Col.kᴳ relay (clean c))

    expanded-eq : L.tracedᴹ S.≈ᴹ P._∘_ relay (clean c)
    expanded-eq = S.⟺ᴹ (Col.collapseᵀ relay (clean c)) S.○ᴹ Col.compose-raw≈∘ᴳ relay (clean c)

    honest-step : (st : MC.St s)
                 → MC.step L.tracedᴹ ((st , ttᵛ) , inj₂ (inj₂ tt))
                   ≈ₚ returnₚ ((st , ttᵛ) , inj₂ (inj₂ false))
    honest-step st =
        L.step-red (st , ttᵛ) (inj₂ (inj₂ tt))
      ⟨≈⟩ bindˣ (>>=ₚ-identityˡ (st , inj₁ (inj₂ tt)) _)
      ⟨≈⟩ >>=ₚ-identityˡ ((st , ttᵛ) , inj₂ (inj₁ (inj₂ tt))) _
      ⟨≈⟩ L.loop-pass (st , ttᵛ) (inj₁ (inj₂ tt)) (st , ttᵛ)
              (inj₂ (inj₂ (inj₂ false))) (>>=ₚ-identityˡ (ttᵛ , inj₂ (inj₂ false)) _)
      ⟨≈⟩ L.loop-pass (st , ttᵛ) (inj₂ (inj₂ false)) (st , ttᵛ)
              (inj₁ (inj₂ (inj₂ false))) (>>=ₚ-identityˡ (st , inj₂ (inj₂ false)) _)

  simulated-clean-read : runˢ (P._∘_ relay (clean c)) honestRead
                       ≈ₚ (MC.point (MC.state s) ttᵛ >>=ₚ λ _ → returnₚ false)
  simulated-clean-read =
      runˢ-resp-≈ᴹ (S.⟺ᴹ expanded-eq) honestRead
    ⟨≈⟩ bindᶠ (λ where
          (st , ttᵛ) → bindˣ (honest-step st) ⟨≈⟩ >>=ₚ-identityˡ ((st , ttᵛ) , inj₂ (inj₂ false)) _)
    ⟨≈⟩ bindˣ (point-⊛ (MC.state s) MC.Iˢ ttᵛ)
    ⟨≈⟩ >>=ₚ-assoc (MC.point (MC.state s) ttᵛ)
            (λ st → returnₚ ttᵛ >>=ₚ λ u → returnₚ (st , u)) (λ _ → returnₚ false)
    ⟨≈⟩ bindᶠ (λ st → bindˣ (>>=ₚ-identityˡ ttᵛ _) ⟨≈⟩ >>=ₚ-identityˡ (st , ttᵛ) _)

  simulated-clean-no-true : Upper (runˢ (P._∘_ relay (clean c)) honestRead) 0ℚ
  simulated-clean-no-true = upper-≈ simulated-clean-read λ n →
    cum-bindʳ n (MC.point (MC.state s) ttᵛ) (λ _ → returnₚ false) (indᵇ true) (indᵇ-nn true) 0ℚ ≤-refl
      (λ _ → returnₚ-cum-≤ n false (indᵇ true) (indᵇ-nn true))

half-true : Pr≤ 2 half ≡ ½
half-true = refl

quarter-true : Pr≤ 2 quarter ≡ ¼
quarter-true = refl

initialization-mass : mass 2 half ≡ 1ℚ × mass 2 quarter ≡ 1ℚ
initialization-mass = refl , refl

component-gap : Pr≤ 2 half ℚ.- Pr≤ 2 quarter ≡ ¼
component-gap = refl

no-small-simulation : {ε : ℚ} → ε ℚ.< ½ → (s : Proc Advᴵ Advᴵ)
                    → ¬ (real ≈ᴿ[ ε ] P._∘_ (subᴵ {A = Honᴵ} s) ideal)
no-small-simulation {ε} small s =
  let r , ε<r , r<½ = <-dense small
      δ = r ℚ.- ε
      pos = subst (ℚ._< δ) (+-inverseʳ ε) (+-monoˡ-< (ℚ.- ε) ε<r)
      offset = trans (+-comm ε δ) (−-+-cancel r ε)
  in λ e →
    let near = ≈ₚ[]-resp (cache-read half original) ≈refl (Verdict.≈̄⇒≈ (e honestRead) δ pos)
        bd = ≤-trans (≤-reflexive (sym half-true))
          (≤-trans (upper-≈[] near (simulated-clean-no-true s latest) 2)
                    (≤-reflexive (trans (+-identityˡ (ε ℚ.+ δ)) offset)))
    in <-irrefl refl (≤-<-trans bd r<½)

------------------------------------------------------------------------
-- Live simulator transactions, including the composed simulator

versionProbe : (Tag → Bool) → Strat (Pos Advᴵ ⊎ Neg Advᴵ) (Neg Advᴵ ⊎ Pos Advᴵ)
versionProbe p = ask (inj₂ tt) λ where
  (inj₁ _) → ask (inj₁ latest) λ where
    (inj₁ _) → out false
    (inj₂ c) → out (p c)
  (inj₂ _) → out false

isPrevious isOriginal : Tag → Bool
isPrevious previous = true
isPrevious _ = false
isOriginal original = true
isOriginal _ = false

wire-probe : (up : Tag → Tag) (p : Tag → Bool)
            → runˢ (wireᴹ {Advᴵ} {Advᴵ} up id) (versionProbe p) ≈ₚ returnₚ (p (up latest))
wire-probe up p =
    >>=ₚ-identityˡ ttᵛ _
  ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₁ tt) _
  ⟨≈⟩ >>=ₚ-identityˡ (ttᵛ , inj₂ (up latest)) _

doubleSimulator : Proc Advᴵ Advᴵ
doubleSimulator = P._∘_ simulator simulator

simulator-reply : runˢ simulator (versionProbe isPrevious) ≈ₚ returnₚ true
simulator-reply = wire-probe previousTag isPrevious

double-simulator-reply : runˢ doubleSimulator (versionProbe isOriginal) ≈ₚ returnₚ true
double-simulator-reply =
  runˢ-resp-≈ᴹ (wire∘wire previousTag id previousTag id) (versionProbe isOriginal)
  ⟨≈⟩ wire-probe (previousTag ∘′ previousTag) isOriginal

private
  id-probe : (p : Tag → Bool) → runˢ (P.id {Advᴵ}) (versionProbe p) ≈ₚ returnₚ (p latest)
  id-probe p = runˢ-resp-≈ᴹ (S.⟺ᴹ wire-id) (versionProbe p) ⟨≈⟩ wire-probe id p

  reject-zero : {f g : Proc Advᴵ Advᴵ} (d : Strat (Pos Advᴵ ⊎ Neg Advᴵ) (Neg Advᴵ ⊎ Pos Advᴵ))
               → runˢ f d ≈ₚ returnₚ true → runˢ g d ≈ₚ returnₚ false → ¬ (f ≈ᴿ[ 0ℚ ] g)
  reject-zero d l r e =
    let m , bd = proj₁ (≈ₚ[]-resp l r
          (Verdict.≈̄⇒≈ (e d) ½ (toWitness {a? = 0ℚ ℚ.<? ½} tt))) true 1
    in 1≰½ (≤-trans (≤-reflexive (sym (returnₚ-cum 0 true (indᵇ true))))
      (≤-trans bd (≤-trans
        (+-monoˡ-≤ ½ (returnₚ-cum-≤ m false (indᵇ true) (indᵇ-nn true)))
        (≤-reflexive (+-identityˡ ½)))))

simulator-not-identity : ¬ (simulator ≈ᴿ[ 0ℚ ] P.id {Advᴵ})
simulator-not-identity = reject-zero (versionProbe isPrevious) simulator-reply (id-probe isPrevious)

double-simulator-not-identity : ¬ (doubleSimulator ≈ᴿ[ 0ℚ ] P.id {Advᴵ})
double-simulator-not-identity =
  reject-zero (versionProbe isOriginal) double-simulator-reply (id-probe isOriginal)
