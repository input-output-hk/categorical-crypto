{-# OPTIONS --safe --without-K --guardedness #-}

-- An ITM activation as a `Dₚ` process.  Running until `send` is Elgot
-- iteration of the table lookup (`ProbabilisticLogic.Dp.Iter`), which spends a
-- guarded delay per pass, so a machine that never sends is `≈ₚ botₚ`.

module CategoricalCrypto.ITM.Run where

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base
open import Data.Product.Base
open import Data.Sum.Base hiding (map₂)
open import Data.Unit.Base
open import Function.Base
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.UC.Machine

import CategoricalCrypto.Machines.Core as Core

private module MC = Core (𝒱ₚ 0ℓ)

module _ {I O : Set} (M : TM I O) where
  open Conf
  open TM M

  act : Conf M → Instr (Fin #Q) O → Dₚ (Conf M × ((Mem M × (O × Bits)) ⊎ ⊤))
  act c (run q w mʷ mⁱ b) = returnₚ (exec M q w mʷ mⁱ b c , inj₂ tt)
  act c (flip q₀ q₁)      = mapₚ (λ x → goto M (if x then q₁ else q₀) c , inj₂ tt) (coinₚ uniform-Bool)
  act c (send o q)        = returnₚ (c , inj₁ ((q , work c) , o , reverse (buf c)))

  body : Body (Conf M) ⊤ (Mem M × (O × Bits))
  body (c , _) = act c (δ-at M c)

  runᵀᴹ : Mem M × (I × Bits) → Dₚ (Mem M × (O × Bits))
  runᵀᴹ (m , x) = mapₚ proj₂ (iterₚ body (load M m x , tt))

  runᵀᴹ-send : ∀ {m x o q} → δ-at M (load M m x) ≡ send o q
             → runᵀᴹ (m , x) ≈ₚ returnₚ ((q , proj₂ m) , o , [])
  runᵀᴹ-send {m} {x} {o} {q} eq =
        map-arg proj₂ (iterₚ-fix body (c , tt)
                       ⟨≈⟩ bindˣ (≡⇒≈ₚ (cong (act c) eq))
                       ⟨≈⟩ >>=ₚ-identityˡ (c , inj₁ r) (contᵢ body))
    ⟨≈⟩ >>=ₚ-identityˡ (c , r) (returnₚ ∘′ proj₂)
    where
    c : Conf M
    c = load M m x
    r : Mem M × (O × Bits)
    r = (q , proj₂ m) , o , []

runᴾ : {A B : Ports} → Gen A B → Proc ⟦ A ⟧ ⟦ B ⟧
runᴾ {A} {B} M = MC.mk (initˢ (Mem M) (blank M)) λ (m , x) →
  mapₚ (map₂ (encodeᴼ A B)) (runᵀᴹ M (m , decodeᴵ A B x))
