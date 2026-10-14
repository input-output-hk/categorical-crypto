{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.IPDL.ReadOrder where

open import Class.DecEq
open import Data.Bool.Base
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Unit.Base
open import Function.Base using (const)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import CategoricalCrypto.IPDL.Native
open import CategoricalCrypto.IPDL.SSP
open import CategoricalCrypto.IPDL.Syntax
open import CategoricalCrypto.SSP.Dist
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
import CategoricalCrypto.SSP.Protocol as P
import CategoricalCrypto.SSP.Protocol.Category as PC

Inputs Output : Ctx
Inputs = bit ∷ bit ∷ []
Output = bit ∷ []

left right : Net Inputs Output
left = record { H = [] ; def = (2 , read zero λ a → read (suc zero) λ _ → ret a) , tt }
right = record { H = [] ; def = (2 , read (suc zero) λ _ → read zero ret) , tt }

joint : Store Inputs → Maybe Bool
joint (just a , just _ , _) = just a
joint _ = nothing

canonical : P.Protocol unitᴵ (API Inputs Output)
canonical = record
  { St = Store Inputs ; init = empty Inputs
  ; step = λ where
      s (Input c) q → P.ret (assign Inputs s c q , tt)
      s (Get zero) _ → P.ret (s , joint s)
      s Step _ → P.ret (s , tt) }

realizeˡ : Store Inputs → Residual.State left
realizeˡ s@(nothing , _ , _) = s , P.init (resource left) .proj₂
realizeˡ s@(just a , nothing , _) = s , waiting 1 (read (suc zero) λ _ → ret a) , tt
realizeˡ s@(just a , just _ , _) = s , assigned a , tt

realizeʳ : Store Inputs → Residual.State right
realizeʳ s@(_ , nothing , _) = s , P.init (resource right) .proj₂
realizeʳ s@(nothing , just _ , _) = s , waiting 1 (read zero ret) , tt
realizeʳ s@(just a , just _ , _) = s , assigned a , tt

canonical≲left : canonical P.≲ᵖ resource left
canonical≲left = record { θ = realizeˡ ; θ-init = refl ; θ-step = square }
  where
  square : ∀ s c q → P.mapᶜ (map₁ realizeˡ) (P.step canonical s c q)
                    P.≈ᶜ P.step (resource left) (realizeˡ s) c q
  square (nothing , nothing , tt) (Input zero) q = P.ret refl
  square (nothing , just b , tt) (Input zero) q = P.ret refl
  square (just a , nothing , tt) (Input zero) q = P.ret refl
  square (just a , just b , tt) (Input zero) q = P.ret refl
  square (nothing , nothing , tt) (Input (suc zero)) q = P.ret refl
  square (nothing , just b , tt) (Input (suc zero)) q = P.ret refl
  square (just a , nothing , tt) (Input (suc zero)) q = P.ret refl
  square (just a , just b , tt) (Input (suc zero)) q = P.ret refl
  square (nothing , nothing , tt) (Get zero) q = P.ret refl
  square (nothing , just b , tt) (Get zero) q = P.ret refl
  square (just a , nothing , tt) (Get zero) q = P.ret refl
  square (just a , just b , tt) (Get zero) q = P.ret refl
  square (nothing , nothing , tt) Step q = P.ret refl
  square (nothing , just b , tt) Step q = P.ret refl
  square (just a , nothing , tt) Step q = P.ret refl
  square (just a , just b , tt) Step q = P.ret refl

canonical≲right : canonical P.≲ᵖ resource right
canonical≲right = record { θ = realizeʳ ; θ-init = refl ; θ-step = square }
  where
  square : ∀ s c q → P.mapᶜ (map₁ realizeʳ) (P.step canonical s c q)
                    P.≈ᶜ P.step (resource right) (realizeʳ s) c q
  square (nothing , nothing , tt) (Input zero) q = P.ret refl
  square (nothing , just b , tt) (Input zero) q = P.ret refl
  square (just a , nothing , tt) (Input zero) q = P.ret refl
  square (just a , just b , tt) (Input zero) q = P.ret refl
  square (nothing , nothing , tt) (Input (suc zero)) q = P.ret refl
  square (nothing , just b , tt) (Input (suc zero)) q = P.ret refl
  square (just a , nothing , tt) (Input (suc zero)) q = P.ret refl
  square (just a , just b , tt) (Input (suc zero)) q = P.ret refl
  square (nothing , nothing , tt) (Get zero) q = P.ret refl
  square (nothing , just b , tt) (Get zero) q = P.ret refl
  square (just a , nothing , tt) (Get zero) q = P.ret refl
  square (just a , just b , tt) (Get zero) q = P.ret refl
  square (nothing , nothing , tt) Step q = P.ret refl
  square (nothing , just b , tt) Step q = P.ret refl
  square (just a , nothing , tt) Step q = P.ret refl
  square (just a , just b , tt) Step q = P.ret refl

read-order : resource left ≈ᵈ resource right
read-order = ≈ᵈ.trans (≈ᵈ.sym (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲left))) (≈ᵖ⇒≈ᵈ (P.≲⇒≈ᵖ canonical≲right))

all-strategies : (a : Strategy Inputs Output Bool)
               → (Experiment.run left a >>=ᴹ return⊥) ≈Mℚ (Experiment.run right a >>=ᴹ return⊥)
all-strategies a ξ = trans (sym (Correspondence.agreement left a ξ)) (trans
  (sym (runᵖ-sim (PC.∘ᵖ-resp-≲ᵖ (P.≲ᵖ-refl {P = tester a}) canonical≲left) ξ)) (trans
  (runᵖ-sim (PC.∘ᵖ-resp-≲ᵖ (P.≲ᵖ-refl {P = tester a}) canonical≲right) ξ)
  (Correspondence.agreement right a ξ)))

-- The demand-exposing compiler really does leak this order; the Fig. 9
-- interpreter above never calls these two environment-controlled oracles.
Demand : Iface
Demand = record { Ch = Fin 2 ; Q = const ⊤ ; R = const Bool ; Ch-dec = DecEq-Fin }

order-oracle : P.Protocol unitᴵ Demand
order-oracle = record { St = Bool ; init = true ; step = λ s _ _ → P.ret (false , s) }

pullˡ pullʳ : P.Protocol Demand Ωᴵ
pullˡ = record { St = ⊤ ; init = tt ; step = λ _ _ _ → P.call zero tt λ a → P.call (suc zero) tt λ _ → P.ret (tt , a) }
pullʳ = record { St = ⊤ ; init = tt ; step = λ _ _ _ → P.call (suc zero) tt λ _ → P.call zero tt λ a → P.ret (tt , a) }

pull-left : entries (runᵖ (pullˡ P.∘ᵖ order-oracle)) ≡ entries (return⊥ true)
pull-left = refl

pull-right : entries (runᵖ (pullʳ P.∘ᵖ order-oracle)) ≡ entries (return⊥ false)
pull-right = refl
