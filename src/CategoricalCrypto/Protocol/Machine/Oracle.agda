{-# OPTIONS --safe --without-K --guardedness #-}

-- A protocol image over a CLOSED machine is the oracle machine: on an idle
-- state it runs the protocol's call tree, each call answered by one step of the
-- machine below (`orun`).  The machine below has no interface of its own, so it
-- is activated only by the protocol's calls and every activation ends in an
-- answer: the composite's loop is solved within the call tree.
--
-- `Protocol.Machine.Compose`'s technique: `Machines.Collapse` reads `𝒢ₚ`'s
-- composite as one traced machine, and the oracle machine, on the same states,
-- simulates it along the identity.

open import Categories.Category

open import Data.Empty
open import Data.Product.Base
open import Data.Sum.Base
open import Level
open import Relation.Nullary using (¬_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Coin
open import ProbabilisticLogic.Dp.Iter
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Protocol
open import CategoricalCrypto.Protocol.Machine

import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Pointwise as Pw
import CategoricalCrypto.Machines.Sim as Sim

module CategoricalCrypto.Protocol.Machine.Oracle where

private
  module MC = Core (𝒱ₚ 0ℓ)
  module S  = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

-- `E⁺`/`E⁻` are the closed machine's own polarities, empty but not necessarily
-- `⊥`: a flattened SSP interface spells them `Σ ⊥ _`.
module _ {E⁺ E⁻ : Set} (e⁺ : ¬ E⁺) (e⁻ : ¬ E⁻) {A B : Iface} (P : Protocol A B)
         (c : MC.Machine (E⁺ ⊎ Neg A) (E⁻ ⊎ Pos A)) where

  Sᴼ : MC.State
  Sᴼ = Col.Sᴳ {E⁺} {E⁻} (morphism P) c

  mutual
    orun : Calls A (St P × Pos B) → MC.St c → Dₚ ((MSt P × MC.St c) × (E⁻ ⊎ Pos B))
    orun (ret (s , b⁺)) sc = returnₚ ((idle s , sc) , inj₂ b⁺)
    orun (call a k)     sc = MC.step c (sc , inj₂ a) >>=ₚ answer k
    orun (coin μ k)     sc = coinₚ μ >>=ₚ λ b → orun (k b) sc
    orun dead           sc = botₚ

    answer : (Pos A → Calls A (St P × Pos B)) → MC.St c × (E⁻ ⊎ Pos A)
           → Dₚ ((MSt P × MC.St c) × (E⁻ ⊎ Pos B))
    answer k (_   , inj₁ x) = ⊥-elim (e⁻ x)
    answer k (sc′ , inj₂ r) = orun (k r) sc′

  stepᴼ : (MSt P × MC.St c) × (E⁺ ⊎ Neg B) → Dₚ ((MSt P × MC.St c) × (E⁻ ⊎ Pos B))
  stepᴼ (_              , inj₁ x) = ⊥-elim (e⁺ x)
  stepᴼ ((idle s , sc)  , inj₂ q) = orun (step P s q) sc
  stepᴼ ((wait _ , _)   , inj₂ _) = botₚ

  oracleᴹ : MC.Machine (E⁺ ⊎ Neg B) (E⁻ ⊎ Pos B)
  oracleᴹ = MC.mk Sᴼ stepᴼ

  private
    open Col.Loop (E⁺ ⊎ Neg B) (E⁻ ⊎ Pos B) (Neg A ⊎ Pos A) Sᴼ
                  (Col.kᴳ {E⁺} {E⁻} {Pos A} {Neg A} {Pos B} {Neg B} (morphism P) c)

    exit : (MSt P × MC.St c) × ((E⁻ ⊎ Pos B) ⊎ (Neg A ⊎ Pos A)) → Dₚ ((MSt P × MC.St c) × (E⁻ ⊎ Pos B))
    exit = contᵢ body

    mutual
      orun-drive : (T : Calls A (St P × Pos B)) (sc : MC.St c)
                 → orun T sc ≈ₚ (drive P T >>=ₚ λ r → exit ((proj₁ r , sc) , Col.outᵍ (proj₂ r)))
      orun-drive (ret (s , b⁺)) sc = ≈sym (>>=ₚ-identityˡ (idle s , inj₂ b⁺) _)
      orun-drive (call a k)     sc =
        bindᶠ (answer-drive k)
        ⟨≈⟩ ≈sym ( >>=ₚ-identityˡ (wait k , inj₁ a) _
                 ⟨≈⟩ iterₚ-fix body ((wait k , sc) , inj₁ a)
                 ⟨≈⟩ >>=ₚ-assoc (MC.step c (sc , inj₂ a)) _ _
                 ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((wait k , proj₁ r) , Col.outᶠ (proj₂ r)) exit))
      orun-drive (coin μ k)     sc = bindᶠ (λ b → orun-drive (k b) sc) ⟨≈⟩ ≈sym (>>=ₚ-assoc (coinₚ μ) _ _)
      orun-drive dead           sc = ≈sym (bot-bind-≈ₚ _)

      answer-drive : (k : Pos A → Calls A (St P × Pos B)) (r : MC.St c × (E⁻ ⊎ Pos A))
                   → answer k r ≈ₚ exit ((wait k , proj₁ r) , Col.outᶠ (proj₂ r))
      answer-drive k (_   , inj₁ x)  = ⊥-elim (e⁻ x)
      answer-drive k (sc′ , inj₂ r⁺) =
        orun-drive (k r⁺) sc′
        ⟨≈⟩ ≈sym ( iterₚ-fix body ((wait k , sc′) , inj₂ r⁺)
                 ⟨≈⟩ >>=ₚ-assoc (drive P (k r⁺)) _ _
                 ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , sc′) , Col.outᵍ (proj₂ r)) exit))

    stepᴼ-traced : (z : (MSt P × MC.St c) × (E⁺ ⊎ Neg B))
                 → (stepᴼ z >>=ₚ Pw.padϕ (λ s → s)) ≈ₚ MC.step tracedᴹ z
    stepᴼ-traced (_ , inj₁ x) = ⊥-elim (e⁺ x)
    stepᴼ-traced ((idle s , sc) , inj₂ q) =
      >>=ₚ-identityʳ _ ⟨≈⟩ orun-drive (step P s q) sc
      ⟨≈⟩ ≈sym ( step-red (idle s , sc) (inj₂ q)
               ⟨≈⟩ >>=ₚ-assoc (drive P (step P s q)) _ _
               ⟨≈⟩ bindᶠ (λ r → >>=ₚ-identityˡ ((proj₁ r , sc) , Col.outᵍ (proj₂ r)) exit))
    stepᴼ-traced ((wait k , sc) , inj₂ q) =
      bot-bind-≈ₚ _ ⟨≈⟩ ≈sym (step-red (wait k , sc) (inj₂ q) ⟨≈⟩ bindˣ (bot-bind-≈ₚ _) ⟨≈⟩ bot-bind-≈ₚ exit)

    oracle-sim : oracleᴹ S.≲ tracedᴹ
    oracle-sim = Pw.simFn (λ s → s) (λ x → >>=ₚ-identityʳ (MC.point Sᴼ x)) stepᴼ-traced

  oracle≈∘ : oracleᴹ S.≈ᴹ Category._∘_ (𝒢ₚ 0ℓ) {E⁺ , E⁻} {Pos A , Neg A} {Pos B , Neg B} (morphism P) c
  oracle≈∘ =
         S.≲⇒≈ᴹ oracle-sim
    S.○ᴹ S.⟺ᴹ (Col.collapseᵀ {E⁺} {E⁻} {Pos A} {Neg A} {Pos B} {Neg B} (morphism P) c)
    S.○ᴹ Col.compose-raw≈∘ᴳ {E⁺} {E⁻} {Pos A} {Neg A} {Pos B} {Neg B} (morphism P) c
