{-# OPTIONS --safe --guardedness #-}

-- Arbitrary native relations admit exact-value guards without a decision
-- procedure.  Composition with such guards tests literal positive support.
module CategoricalCrypto.Machine.Relational.Presentation.Guard where

open import Axiom.Extensionality.Propositional
open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Maybe.Properties using (just-injective)
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Sum.Properties using (inj₁-injective; inj₂-injective)
open import Data.Unit.Polymorphic.Base
open import Level using (0ℓ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Positive
open import ProbabilisticLogic.Dp.Positive.Composition
open import ProbabilisticLogic.Dp.Positive.Decidability
import CategoricalCrypto.Channel.Core as Ch
import CategoricalCrypto.Iface as I
import CategoricalCrypto.Machine.Core as M
open import CategoricalCrypto.Machine.Relational
open import CategoricalCrypto.Machine.Relational.Presentation.Descent
import CategoricalCrypto.Machine.Relational.Wiring as W
import CategoricalCrypto.UC.Machine as UC
import CategoricalCrypto.UC.Model.Seal as Seal

private variable
  X : Set
  d : Dₚ X
  x y : X

opaque
  unfolding Ch._⊗₀_

  guard : X → Initialized (X Ch.⇿ ⊥) (Bool Ch.⇿ ⊥)
  guard x = singleton (M.MkMachine {State = ⊤} λ _ i o _ →
    (i ≡ inj₁ x) × (o ≡ just (inj₂ true))) tt

  Success : Initialized (⊤ Ch.⇿ ⊥) (Bool Ch.⇿ ⊥) → Set
  Success P = ∃ λ s → initial P s × ∃ λ s′ →
    M.Machine.stepRel (machine P) s (inj₁ tt) (just (inj₂ true)) s′

module _ (d : Dₚ X) (x : X) where
  private
    source = canonical (emit d)
    pre = W.modify M.∘σ (source W.⊗₁ guard x)

  opaque
    unfolding Ch._⊗₀_ Ch.destruct-⊗ Ch.construct-⊗ Ch.⊗-sym Ch.⊗-right-assoc Ch.⊗-left-assoc
              Ch.⊗-right-intro Ch.⊗-ᵀ-distrib Ch.⊗-ᵀ-factor Ch.⊗-right-neutral Ch.⊗-fusion Ch.⊗-combine
              canonical guard Success

    guarded-support : Success (guard x W.∘ source) → Positive d x
    guarded-support (_ , _ , _ , run) = go run
      where
      raw : Maybe ((⊥ ⊎ ⊥) ⊎ (Bool ⊎ X)) → Maybe ((⊥ ⊎ X) ⊎ (⊥ ⊎ Bool))
      raw o = Data.Maybe.Base.map
        (Ch.app (M.⊗σ {⊤ Ch.⇿ ⊥} {X Ch.⇿ ⊥} {X Ch.⇿ ⊥} {Bool Ch.⇿ ⊥} {Ch.Out}))
        (Data.Maybe.Base.map (Ch.app (M.∘σ {⊤ Ch.⇿ ⊥} {X Ch.⇿ ⊥} {Bool Ch.⇿ ⊥} {Ch.Out})) o)

      first : ∀ {s s′ o} → M.Machine.stepRel (machine pre) s (inj₁ (inj₁ tt)) o s′
        → ∃ λ z → Positive d z × (raw o ≡ just (inj₁ (inj₂ z)))
      first step with M.comp-view step
      ... | inj₂ (_ , _ , () , _)
      ... | inj₁ (_ , nothing , _ , _ , _ , ())
      ... | inj₁ (_ , just (inj₁ ()) , _)
      ... | inj₁ (_ , just (inj₂ z) , _ , eq , _ , path) =
        let y , py , yz = map-unpath (λ y → _ , inj₂ y) path
        in z , subst (Positive d) (inj₂-injective (cong proj₂ yz)) py , eq

      second : ∀ {s s′ o z} → M.Machine.stepRel (machine pre) s (inj₁ (inj₂ z)) o s′
        → (x ≡ z) × (raw o ≡ just (inj₂ (inj₂ true)))
      second step with M.comp-view step
      ... | inj₁ (_ , _ , () , _)
      ... | inj₂ (_ , _ , ieq , oeq , _ , refl , refl) =
        sym (inj₁-injective (inj₂-injective ieq)) , oeq

      finish : ∀ {s s′ z} → M.TraceRel (machine pre) s (inj₁ (inj₂ z))
        (just (inj₂ (inj₁ true))) s′ → x ≡ z
      finish M.Trace[ step ] = proj₁ (second {o = just (inj₂ (inj₁ true))} step)
      finish (M._Trace∷ₒ_ {outC = ()} step rest)
      finish (M._Trace∷ᵢ_ {inC = z} step rest) with second {o = just (inj₂ (inj₂ z))} step
      ... | _ , ()

      go : ∀ {s s′} → M.TraceRel (machine pre) s (inj₁ (inj₁ tt))
        (just (inj₂ (inj₁ true))) s′ → Positive d x
      go M.Trace[ step ] with first {o = just (inj₂ (inj₁ true))} step
      ... | _ , _ , ()
      go (M._Trace∷ₒ_ {outC = ()} step rest)
      go (M._Trace∷ᵢ_ {inC = z} step rest) =
        let y , py , yz = first {o = just (inj₂ (inj₂ z))} step
            xz = finish rest
            zy = inj₂-injective (inj₁-injective (just-injective yz))
        in subst (Positive d) (trans (sym zy) (sym xz)) py

    support-guarded : Positive d x → Success (guard x W.∘ source)
    support-guarded path = (tt , tt) , (positive-return tt , refl) , (tt , tt) ,
      (M.Tensor.Step₁ (map-path (λ x → tt , inj₂ x) path)
        M.Trace∷ᵢ M.Trace[ M.Tensor.Step₂ (refl , refl) ])

-- Only left composition and preservation of one Boolean success are needed;
-- no bisimulation law, category structure, or equality of hidden states is used.
record ObservationalDescent : Set₂ where
  private module P = MonoidalCategory Seal.𝔾ᵒ
  field
    Equivalent : ∀ {A B} → Initialized A B → Initialized A B → Set₁
    descend : ∀ {A B} {f g : UC.Proc A B}
      → Seal.procᵒ {A} {B} f P.≈ Seal.procᵒ {A} {B} g
      → Equivalent (canonical {A} {B} f) (canonical {A} {B} g)
    compose : ∀ {A B C} {R S : Initialized A B} (T : Initialized B C)
      → Equivalent R S → Equivalent (T W.∘ R) (T W.∘ S)
    success-to : {R S : Initialized (⊤ Ch.⇿ ⊥) (Bool Ch.⇿ ⊥)}
      → Equivalent R S → Success R → Success S

  literal-support : LiteralSupportCongruence 0ℓ
  literal-support {d = d} {e} {x} eq path = guarded-support e x
    (success-to (compose (guard x) (descend {⊤ I.⇿ ⊥} {_ I.⇿ ⊥} (emit-resp eq)))
      (support-guarded d x path))

  stable-equality : ¬ ¬ (x ≡ y) → x ≡ y
  stable-equality = literal-support-congruence⇒stable-equality literal-support

  decidable-equality : Extensionality 0ℓ 0ℓ → DecidableEquality X
  decidable-equality ext = literal-support⇒decidable-equality ext literal-support
