{-# OPTIONS --safe --without-K #-}

-- A two-component hidden-bit linker, not SSP package composition.
-- Both residuals consult the same persistent store before each small step.
module CategoricalCrypto.IPDL.Linker where

open import Data.Bool.Base hiding (_<_; _≤_)
open import Data.Empty
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.Uniform
open import CategoricalCrypto.IPDL.Native
open import CategoricalCrypto.IPDL.SSP
open import CategoricalCrypto.IPDL.Syntax
open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; toss; coins)
open import CategoricalCrypto.SSP.Iface hiding (flat)
open import CategoricalCrypto.SSP.Observation
import CategoricalCrypto.SSP.Protocol as P
import CategoricalCrypto.SSP.Protocol.Category as PC

Bit : Ctx
Bit = bit ∷ []

module Paired (I : Ctx) (n m : ℕ)
  (out : Rxn (I ++ (Bit ++ Bit)) bit n)
  (hidden : Rxn (I ++ (Bit ++ Bit)) bit m) where

  Global : Ctx
  Global = I ++ (Bit ++ Bit)

  State : Set
  State = Store I × Cell Global bit × Cell Global bit

  initial : State
  initial = empty I , waiting n out , waiting m hidden

  env : State → Environment Global
  env (i , a , b) = lookup Global (append I (Bit ++ Bit) i (value a , value b , tt))

  work₂ : State → ℕ
  work₂ (_ , a , b) = cost a + cost b

  choose₂ : (s : State) → Maybe (Coins (Σ State (λ t → work₂ t < work₂ s)))
  choose₂ s@(i , a , b) with cellStep (env s) a
  ... | just κ = just (mapCoins (λ (a′ , p) → (i , a′ , b) , +-monoˡ-< (cost b) p) κ)
  ... | nothing with cellStep (env s) b
  ...   | nothing = nothing
  ...   | just κ = just (mapCoins (λ (b′ , p) → (i , a , b′) , +-monoʳ-< (cost a) p) κ)

  saturate₂ : (fuel : ℕ) (s : State) → work₂ s ≤ fuel → Coins State
  saturate₂ zero s le with choose₂ s
  ... | nothing = done s
  ... | just κ = bindCoins κ λ (t , lt) → ⊥-elim (n≮0 (≤-trans lt le))
  saturate₂ (suc fuel) s le with choose₂ s
  ... | nothing = done s
  ... | just κ = bindCoins κ λ (t , lt) → saturate₂ fuel t (s≤s⁻¹ (≤-trans lt le))

  before₂ : State → (c : Port I Bit) → Query I Bit c → State × Reply I Bit c
  before₂ (i , a , b) (Input c) v = (assign I i c v , a , b) , tt
  before₂ s@(_ , a , _) (Get zero) _ = s , value a
  before₂ s Step _ = s , tt

  turn₂ : State → (c : Port I Bit) → Query I Bit c → Coins (State × Reply I Bit c)
  turn₂ s c q = mapCoins (_, proj₂ pre) (saturate₂ (work₂ (proj₁ pre)) (proj₁ pre) ≤-refl)
    where pre = before₂ s c q

  linked : P.Protocol unitᴵ (API I Bit)
  linked = record { St = State ; init = initial ; step = λ s c q → coins (turn₂ s c q) }

  flat : Net I Bit
  flat = record { H = Bit ; def = (n , out) , (m , hidden) , tt }

module Shared where
  module L = Paired [] 2 1
    (read (suc zero) λ b → read (suc zero) λ _ → ret b)
    (coin uniform-Bool ret)

  canonical : P.Protocol unitᴵ (API [] Bit)
  canonical = record
    { St = Maybe Bool ; init = nothing
    ; step = λ where
        nothing (Get zero) _ → P.coin uniform-Bool λ b → P.ret (just b , nothing)
        nothing Step _ → P.coin uniform-Bool λ b → P.ret (just b , tt)
        s@(just b) (Get zero) _ → P.ret (s , just b)
        s@(just _) Step _ → P.ret (s , tt) }

  paired : Maybe Bool → L.State
  paired nothing = L.initial
  paired (just b) = tt , assigned b , assigned b

  flattened : Maybe Bool → Residual.State L.flat
  flattened nothing = Residual.initial L.flat
  flattened (just b) = tt , assigned b , assigned b , tt

  canonical≲paired : canonical P.≲ᵖ L.linked
  canonical≲paired = record { θ = paired ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ paired) (P.step canonical s c q) P.≈ᶜ P.step L.linked (paired s) c q
    square nothing (Get zero) q = P.coin λ b → P.ret refl
    square nothing Step q = P.coin λ b → P.ret refl
    square (just b) (Get zero) q = P.ret refl
    square (just b) Step q = P.ret refl

  canonical≲flat : canonical P.≲ᵖ resource L.flat
  canonical≲flat = record { θ = flattened ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ flattened) (P.step canonical s c q) P.≈ᶜ P.step (resource L.flat) (flattened s) c q
    square nothing (Get zero) q = P.coin λ b → P.ret refl
    square nothing Step q = P.coin λ b → P.ret refl
    square (just b) (Get zero) q = P.ret refl
    square (just b) Step q = P.ret refl

  hidden-channel-square : L.linked ≈ᵈ resource L.flat
  hidden-channel-square = ≈ᵈ.trans (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲paired))) (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲flat))

  adaptive-square : (a : Strategy [] Bit Bool)
                  → runᵖ (tester a P.∘ᵖ L.linked) ≈Mℚ (Experiment.run L.flat a >>=ᴹ return⊥)
  adaptive-square a ξ = trans
    (sym (runᵖ-sim (PC.∘ᵖ-resp-≲ᵖ (P.≲ᵖ-refl {P = tester a}) canonical≲paired) ξ))
    (trans (runᵖ-sim (PC.∘ᵖ-resp-≲ᵖ (P.≲ᵖ-refl {P = tester a}) canonical≲flat) ξ)
      (Correspondence.agreement L.flat a ξ))

module Identity where
  module L = Paired Bit 1 1 (read (suc (suc zero)) ret) (read zero ret)

  copy : Net Bit Bit
  copy = record { H = [] ; def = (1 , read zero ret) , tt }

  canonical : P.Protocol unitᴵ (API Bit Bit)
  canonical = record
    { St = Maybe Bool ; init = nothing
    ; step = λ where
        nothing (Input zero) b → P.ret (just b , tt)
        s@(just _) (Input zero) _ → P.ret (s , tt)
        s (Get zero) _ → P.ret (s , s)
        s Step _ → P.ret (s , tt) }

  paired : Maybe Bool → L.State
  paired nothing = L.initial
  paired (just b) = (just b , tt) , assigned b , assigned b

  flattened : Maybe Bool → Residual.State L.flat
  flattened nothing = Residual.initial L.flat
  flattened (just b) = (just b , tt) , assigned b , assigned b , tt

  copied : Maybe Bool → Residual.State copy
  copied nothing = Residual.initial copy
  copied (just b) = (just b , tt) , assigned b , tt

  canonical≲paired : canonical P.≲ᵖ L.linked
  canonical≲paired = record { θ = paired ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ paired) (P.step canonical s c q) P.≈ᶜ P.step L.linked (paired s) c q
    square nothing (Input zero) q = P.ret refl
    square (just b) (Input zero) q = P.ret refl
    square nothing (Get zero) q = P.ret refl
    square (just b) (Get zero) q = P.ret refl
    square nothing Step q = P.ret refl
    square (just b) Step q = P.ret refl

  canonical≲flat : canonical P.≲ᵖ resource L.flat
  canonical≲flat = record { θ = flattened ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ flattened) (P.step canonical s c q) P.≈ᶜ P.step (resource L.flat) (flattened s) c q
    square nothing (Input zero) q = P.ret refl
    square (just b) (Input zero) q = P.ret refl
    square nothing (Get zero) q = P.ret refl
    square (just b) (Get zero) q = P.ret refl
    square nothing Step q = P.ret refl
    square (just b) Step q = P.ret refl

  canonical≲copy : canonical P.≲ᵖ resource copy
  canonical≲copy = record { θ = copied ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ copied) (P.step canonical s c q) P.≈ᶜ P.step (resource copy) (copied s) c q
    square nothing (Input zero) q = P.ret refl
    square (just b) (Input zero) q = P.ret refl
    square nothing (Get zero) q = P.ret refl
    square (just b) (Get zero) q = P.ret refl
    square nothing Step q = P.ret refl
    square (just b) Step q = P.ret refl

  identity-square : L.linked ≈ᵈ resource copy
  identity-square = ≈ᵈ.trans (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲paired))) (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲copy))

  flatten-square : L.linked ≈ᵈ resource L.flat
  flatten-square = ≈ᵈ.trans (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲paired))) (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲flat))

module Feedback where
  module L = Paired Bit 2 1
    (read zero λ seed → if seed then ret true else read (suc (suc zero)) ret)
    (read (suc zero) ret)

  canonical : P.Protocol unitᴵ (API Bit Bit)
  canonical = record
    { St = Maybe Bool ; init = nothing
    ; step = λ where
        nothing (Input zero) b → P.ret (just b , tt)
        s@(just _) (Input zero) _ → P.ret (s , tt)
        s (Get zero) _ → P.ret (s , result s)
        s Step _ → P.ret (s , tt) }
    where
    result : Maybe Bool → Maybe Bool
    result (just true) = just true
    result _ = nothing

  paired : Maybe Bool → L.State
  paired nothing = L.initial
  paired (just false) = (just false , tt) , waiting 1 (read (suc (suc zero)) ret) , waiting 1 (read (suc zero) ret)
  paired (just true) = (just true , tt) , assigned true , assigned true

  flattened : Maybe Bool → Residual.State L.flat
  flattened nothing = Residual.initial L.flat
  flattened (just false) = (just false , tt) , waiting 1 (read (suc (suc zero)) ret) , waiting 1 (read (suc zero) ret) , tt
  flattened (just true) = (just true , tt) , assigned true , assigned true , tt

  canonical≲paired : canonical P.≲ᵖ L.linked
  canonical≲paired = record { θ = paired ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ paired) (P.step canonical s c q) P.≈ᶜ P.step L.linked (paired s) c q
    square nothing (Input zero) false = P.ret refl
    square nothing (Input zero) true = P.ret refl
    square (just false) (Input zero) q = P.ret refl
    square (just true) (Input zero) q = P.ret refl
    square nothing (Get zero) q = P.ret refl
    square (just false) (Get zero) q = P.ret refl
    square (just true) (Get zero) q = P.ret refl
    square nothing Step q = P.ret refl
    square (just false) Step q = P.ret refl
    square (just true) Step q = P.ret refl

  canonical≲flat : canonical P.≲ᵖ resource L.flat
  canonical≲flat = record { θ = flattened ; θ-init = refl ; θ-step = square }
    where
    square : ∀ s c q → P.mapᶜ (map₁ flattened) (P.step canonical s c q) P.≈ᶜ P.step (resource L.flat) (flattened s) c q
    square nothing (Input zero) false = P.ret refl
    square nothing (Input zero) true = P.ret refl
    square (just false) (Input zero) q = P.ret refl
    square (just true) (Input zero) q = P.ret refl
    square nothing (Get zero) q = P.ret refl
    square (just false) (Get zero) q = P.ret refl
    square (just true) (Get zero) q = P.ret refl
    square nothing Step q = P.ret refl
    square (just false) Step q = P.ret refl
    square (just true) Step q = P.ret refl

  seeded-feedback-square : L.linked ≈ᵈ resource L.flat
  seeded-feedback-square = ≈ᵈ.trans (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲paired))) (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲flat))

  seed-test : Bool → Strategy Bit Bit (Maybe Bool)
  seed-test b = ask (Input zero) b λ _ → ask (Get zero) tt finish

  seed-releases-cycle : entries (Experiment.run L.flat (seed-test true)) ≡ entries (return-ℚ (just true))
  seed-releases-cycle = refl

  unseeded-cycle-blocks : entries (Experiment.run L.flat (seed-test false)) ≡ entries (return-ℚ nothing)
  unseeded-cycle-blocks = refl
