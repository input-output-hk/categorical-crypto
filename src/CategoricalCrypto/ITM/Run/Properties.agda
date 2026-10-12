{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.ITM.Run.Properties where

open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Base hiding (flip)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Distribution.Uniform
open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.ITM.Core
open import CategoricalCrypto.ITM.Run

module _ {I O : Set} (M : TM I O) where
  open TM M
  open Conf

  activateᵀᴹ : Conf M → Dₚ (Mem M × (O × Bits))
  activateᵀᴹ c = mapₚ proj₂ (iterₚ (body M) (c , tt))

  activate-run : (c : Conf M) (q : Fin #Q) (w : Sym) (mʷ mⁱ : Move) (b : Maybe Bool)
               → δ-at M c ≡ run q w mʷ mⁱ b
               → activateᵀᴹ c ≈ₚ activateᵀᴹ (exec M q w mʷ mⁱ b c)
  activate-run c q w mʷ mⁱ b eq = map-arg proj₂
    (iterₚ-fix (body M) (c , tt)
     ⟨≈⟩ bindˣ (≡⇒≈ₚ (cong (act M c) eq))
     ⟨≈⟩ >>=ₚ-identityˡ (exec M q w mʷ mⁱ b c , inj₂ tt) (contᵢ (body M)))

  activate-flip : (c : Conf M) (q₀ q₁ : Fin #Q)
                → δ-at M c ≡ flip q₀ q₁
                → activateᵀᴹ c ≈ₚ (coinₚ uniform-Bool >>=ₚ λ b → activateᵀᴹ (goto M (if b then q₁ else q₀) c))
  activate-flip c q₀ q₁ eq =
    map-arg proj₂
      (iterₚ-fix (body M) (c , tt)
       ⟨≈⟩ bindˣ (≡⇒≈ₚ (cong (act M c) eq))
       ⟨≈⟩ bind-map (coinₚ uniform-Bool)
                     (λ b → goto M (if b then q₁ else q₀) c , inj₂ tt) (contᵢ (body M)))
    ⟨≈⟩ map-bind (coinₚ uniform-Bool)
                   (λ b → iterₚ (body M) (goto M (if b then q₁ else q₀) c , tt)) proj₂

  activate-send : (c : Conf M) (o : O) (q : Fin #Q)
                → δ-at M c ≡ send o q
                → activateᵀᴹ c ≈ₚ returnₚ ((q , work c) , o , reverse (buf c))
  activate-send c o q eq =
    map-arg proj₂
      (iterₚ-fix (body M) (c , tt)
       ⟨≈⟩ bindˣ (≡⇒≈ₚ (cong (act M c) eq))
       ⟨≈⟩ >>=ₚ-identityˡ (c , inj₁ ((q , work c) , o , reverse (buf c))) (contᵢ (body M)))
    ⟨≈⟩ >>=ₚ-identityˡ (c , ((q , work c) , o , reverse (buf c))) (returnₚ ∘′ proj₂)
