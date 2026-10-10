{-# OPTIONS --safe --without-K #-}

-- Compilation commutes with composition and tensor up to regrouping the choice
-- factors (`docs/uc-setup-nondeterministic.md` §2.4).  With `split` ND_B's
-- comparison φ and `join` its inverse (`split∘join`), and `_∙_`, `sub` those of
-- `SSP.Setup` at the curried tensor (`g ∙ f = α⇐ ∘ (id ⊗ g) ∘ f`,
-- `sub u = u ⊗ id`, pinned in `Choice.Pin`):
--
--     sub join ∘ ⌈ g ∘⁺ f ⌉  ≈  ⌈ g ⌉ ∙ ⌈ f ⌉                       (`⌈⌉-∘`)
--     sub join ∘ ⌈ P ⊗⁺ P′ ⌉  ≈  interchange ∘ (⌈ P ⌉ ⊗ ⌈ P′ ⌉)      (`⌈⌉-⊗`)
--
-- and so ⌈ g ∘⁺ f ⌉ ≈ sub split ∘ (⌈ g ⌉ ∙ ⌈ f ⌉) (`⌈⌉-∘-split`, `⌈⌉-⊗-split`).
-- `⌈⌉-∘` and `⌈⌉-⊗` are one simulation each, splitting the composite's queues
-- (`splitQ`): a pick reaches its own factor's queue, and a `choose` pops the
-- same pick on both sides — per-site queues keep the factors' schedules apart.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
import Categories.Morphism.Reasoning as MR

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Category using (∘ᵖ-assoc; wireᵖ-identityˡ)
open import CategoricalCrypto.SSP.Protocol.Monoidal using (Protᴹ; ⊗ᵖ-homomorphism; ⊗ᵖ-identity; ⊗ᵖ-resp-≈ᵖ)
open import CategoricalCrypto.SSP.Protocol.Wire

module CategoricalCrypto.ND.SSP.Choice.Compose where

private variable
  A B C D : Iface
  S : Set
  S⃗ T⃗ : List Set

------------------------------------------------------------------------
-- The queues of a concatenation
------------------------------------------------------------------------

splitQ : (S⃗ T⃗ : List Set) → Queues (S⃗ ++ T⃗) → Queues S⃗ × Queues T⃗
splitQ []      T⃗ qs       = tt , qs
splitQ (S ∷ S⃗) T⃗ (q , qs) = map₁ (q ,_) (splitQ S⃗ T⃗ qs)

splitQ-empty : (S⃗ T⃗ : List Set) → splitQ S⃗ T⃗ (empty (S⃗ ++ T⃗)) ≡ (empty S⃗ , empty T⃗)
splitQ-empty []      T⃗ = refl
splitQ-empty (S ∷ S⃗) T⃗ = cong (map₁ ([] ,_)) (splitQ-empty S⃗ T⃗)

push-joinˡ : (S⃗ T⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) (p : Q Cᴵ⟦ S⃗ ⟧ i) (qs : Queues (S⃗ ++ T⃗))
           → splitQ S⃗ T⃗ (push (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₁ i)) (qu (join S⃗ T⃗) {inj₁ i} p) qs)
             ≡ map₁ (push S⃗ i p) (splitQ S⃗ T⃗ qs)
push-joinˡ (S ∷ S⃗) T⃗ (inj₁ _) p (q , qs) = refl
push-joinˡ (S ∷ S⃗) T⃗ (inj₂ i) p (q , qs) = cong (map₁ (q ,_)) (push-joinˡ S⃗ T⃗ i p qs)

push-joinʳ : (S⃗ T⃗ : List Set) (j : Ch Cᴵ⟦ T⃗ ⟧) (p : Q Cᴵ⟦ T⃗ ⟧ j) (qs : Queues (S⃗ ++ T⃗))
           → splitQ S⃗ T⃗ (push (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₂ j)) (qu (join S⃗ T⃗) {inj₂ j} p) qs)
             ≡ map₂ (push T⃗ j p) (splitQ S⃗ T⃗ qs)
push-joinʳ []      T⃗ j p qs       = refl
push-joinʳ (S ∷ S⃗) T⃗ j p (q , qs) = cong (map₁ (q ,_)) (push-joinʳ S⃗ T⃗ j p qs)

private
  -- Two pops agree: both fail, or both succeed with related picks and queues.
  data PopRel {P P′ U U′ : Set} (f : P → P′) (_~_ : U → U′ → Set)
              : Maybe (P × U) → Maybe (P′ × U′) → Set where
    nothing : PopRel f _~_ nothing nothing
    just    : ∀ {p u u′} → u ~ u′ → PopRel f _~_ (just (p , u)) (just (f p , u′))

  popˡ : (S⃗ T⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) {qs : Queues (S⃗ ++ T⃗)} → ∀ {qS qT} → splitQ S⃗ T⃗ qs ≡ (qS , qT)
       → PopRel (↓ˡ S⃗ T⃗ {i}) (λ qs′ qS′ → splitQ S⃗ T⃗ qs′ ≡ (qS′ , qT))
                (pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₁ i)) qs) (pop S⃗ i qS)
  popˡ (S ∷ S⃗) T⃗ (inj₁ _) {[] , qs}    refl = nothing
  popˡ (S ∷ S⃗) T⃗ (inj₁ _) {p ∷ q , qs} refl = just refl
  popˡ (S ∷ S⃗) T⃗ (inj₂ i) {q , qs}     refl
    with pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₁ i)) qs | pop S⃗ i (proj₁ (splitQ S⃗ T⃗ qs)) | popˡ S⃗ T⃗ i {qs} refl
  ... | _ | _ | nothing = nothing
  ... | _ | _ | just e  = just (cong (map₁ (q ,_)) e)

  popʳ : (S⃗ T⃗ : List Set) (j : Ch Cᴵ⟦ T⃗ ⟧) {qs : Queues (S⃗ ++ T⃗)} → ∀ {qS qT} → splitQ S⃗ T⃗ qs ≡ (qS , qT)
       → PopRel (↓ʳ S⃗ T⃗ {j}) (λ qs′ qT′ → splitQ S⃗ T⃗ qs′ ≡ (qS , qT′))
                (pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₂ j)) qs) (pop T⃗ j qT)
  popʳ []      T⃗ j {qs} refl with pop T⃗ j qs
  ... | nothing = nothing
  ... | just _  = just refl
  popʳ (S ∷ S⃗) T⃗ j {q , qs} refl
    with pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₂ j)) qs | pop T⃗ j (proj₂ (splitQ S⃗ T⃗ qs)) | popʳ S⃗ T⃗ j {qs} refl
  ... | _ | _ | nothing = nothing
  ... | _ | _ | just e  = just (cong (map₁ (q ,_)) e)

------------------------------------------------------------------------
-- The regrouping is invertible
------------------------------------------------------------------------

split∘join : (S⃗ T⃗ : List Set) → ⌜ split S⃗ T⃗ ⌝ ∘ᵖ ⌜ join S⃗ T⃗ ⌝ ≈ᵖ wireᵖ
split∘join []      T⃗ = ≲⇒≈ᵖ (≲ᵖ-const λ _ _ _ → ≈ᶜ-refl)
split∘join (S ∷ S⃗) T⃗ = begin
  ⌜ split (S ∷ S⃗) T⃗ ⌝ ∘ᵖ ⌜ join (S ∷ S⃗) T⃗ ⌝
    ≈⟨ ⟺ (⌜⌝-∘ α⁻ s) ⟩∘⟨ ⟺ (⌜⌝-∘ j α) ⟩
  (⌜ s ⌝ ∘ᵖ ⌜ α⁻ ⌝) ∘ᵖ (⌜ α ⌝ ∘ᵖ ⌜ j ⌝)
    ≈⟨ ≲⇒≈ᵖ (∘ᵖ-assoc ⌜ s ⌝ ⌜ α⁻ ⌝ (⌜ α ⌝ ∘ᵖ ⌜ j ⌝)) ⟩
  ⌜ s ⌝ ∘ᵖ (⌜ α⁻ ⌝ ∘ᵖ (⌜ α ⌝ ∘ᵖ ⌜ j ⌝))
    ≈⟨ refl⟩∘⟨_ {f = ⌜ s ⌝} (⟺ (≲⇒≈ᵖ (∘ᵖ-assoc ⌜ α⁻ ⌝ ⌜ α ⌝ ⌜ j ⌝))) ⟩
  ⌜ s ⌝ ∘ᵖ ((⌜ α⁻ ⌝ ∘ᵖ ⌜ α ⌝) ∘ᵖ ⌜ j ⌝)
    ≈⟨ refl⟩∘⟨_ {f = ⌜ s ⌝} (_⟩∘⟨refl {g = ⌜ j ⌝} (associator.isoʳ {Cᴵ S} {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧})) ⟩
  ⌜ s ⌝ ∘ᵖ (wireᵖ ∘ᵖ ⌜ j ⌝)
    ≈⟨ refl⟩∘⟨_ {f = ⌜ s ⌝} (≲⇒≈ᵖ (wireᵖ-identityˡ ⌜ j ⌝)) ⟩
  ⌜ s ⌝ ∘ᵖ ⌜ j ⌝
    ≈⟨ ⟺ (⌜⌝-⊗ idᴵ (split S⃗ T⃗)) ⟩∘⟨ ⟺ (⌜⌝-⊗ idᴵ (join S⃗ T⃗)) ⟩
  wireᵖ ⊗ᵖ ⌜ split S⃗ T⃗ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ⌜ join S⃗ T⃗ ⌝
    ≈⟨ ⟺ (≲⇒≈ᵖ (⊗ᵖ-homomorphism wireᵖ wireᵖ ⌜ split S⃗ T⃗ ⌝ ⌜ join S⃗ T⃗ ⌝)) ⟩
  (wireᵖ ∘ᵖ wireᵖ) ⊗ᵖ (⌜ split S⃗ T⃗ ⌝ ∘ᵖ ⌜ join S⃗ T⃗ ⌝)
    ≈⟨ ⊗ᵖ-resp-≈ᵖ (≲⇒≈ᵖ (wireᵖ-identityˡ wireᵖ)) (split∘join S⃗ T⃗) ⟩
  wireᵖ ⊗ᵖ wireᵖ
    ≈⟨ ≲⇒≈ᵖ ⊗ᵖ-identity ⟩
  wireᵖ ∎
  where
  α  = αᴵ {Cᴵ S} {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧}
  α⁻ = αᴵ⁻¹ {Cᴵ S} {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧}
  s  = idᴵ {Cᴵ S} ⊗ᴵᴵ split S⃗ T⃗
  j  = idᴵ {Cᴵ S} ⊗ᴵᴵ join S⃗ T⃗
  open MonoidalCategory Protᴹ using (module associator; module HomReasoning)
  open HomReasoning

unsplit : (S⃗ T⃗ : List Set) → ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ {B} ∘ᵖ ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ≈ᵖ wireᵖ
unsplit S⃗ T⃗ = begin
  ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ
    ≈⟨ ⟺ (≲⇒≈ᵖ (⊗ᵖ-homomorphism ⌜ split S⃗ T⃗ ⌝ ⌜ join S⃗ T⃗ ⌝ wireᵖ wireᵖ)) ⟩
  (⌜ split S⃗ T⃗ ⌝ ∘ᵖ ⌜ join S⃗ T⃗ ⌝) ⊗ᵖ (wireᵖ ∘ᵖ wireᵖ)
    ≈⟨ ⊗ᵖ-resp-≈ᵖ (split∘join S⃗ T⃗) (≲⇒≈ᵖ (wireᵖ-identityˡ wireᵖ)) ⟩
  wireᵖ ⊗ᵖ wireᵖ
    ≈⟨ ≲⇒≈ᵖ ⊗ᵖ-identity ⟩
  wireᵖ ∎
  where open MonoidalCategory Protᴹ using (module HomReasoning); open HomReasoning

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

module _ (g : Protocol⁺ T⃗ B C) (f : Protocol⁺ S⃗ A B) where

  private
    θ∘ : (⊤ × ⊤) × (St g × St f) × Queues (S⃗ ++ T⃗) → (⊤ × ⊤ × St g × Queues T⃗) × St f × Queues S⃗
    θ∘ (_ , (sg , sf) , qs) = (tt , tt , sg , proj₂ (splitQ S⃗ T⃗ qs)) , sf , proj₁ (splitQ S⃗ T⃗ qs)

    W = ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ {C}
    G = wireᵖ {Cᴵ⟦ S⃗ ⟧} ⊗ᵖ ⌈ g ⌉
    Λ = ⌜ αᴵ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {C} ⌝

    mutual
      graft-res : {c : Ch C} (t : Calls⁺ B T⃗ (St g × R C c)) (sf : St f) (qs : Queues (S⃗ ++ T⃗)) → ∀ {qS qT}
                → splitQ S⃗ T⃗ qs ≡ (qS , qT)
                → mapᶜ (map₁ θ∘) (serve W ⌈ g ∘⁺ f ⌉ {b = inj₂ c} (λ r → ret ((tt , tt) , r))
                                     (resolve qs (graft⁺ g f t sf)))
                  ≈ᶜ graft (Λ ∘ᵖ G) ⌈ f ⌉
                       (serve Λ G {b = inj₂ (inj₂ c)} (λ r → ret (tt , r))
                          (mapᶜ (map₁ (tt ,_)) (reindex ι₂ (resolve qT t))))
                       (sf , qS)
      graft-res (ret (sg , y)) sf qs e = ret (cong (λ z → ((tt , tt , sg , proj₂ z) , sf , proj₁ z) , y) e)
      graft-res (call b q k)   sf qs e = serve-res k (step f sf b q) qs e
      graft-res (coin _ k)     sf qs e = coin λ x → graft-res (k x) sf qs e
      graft-res dead           sf qs e = dead
      graft-res (choose j k)   sf qs {qT = qT} e
        with pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₂ j)) qs | pop T⃗ j qT | popʳ S⃗ T⃗ j e
      ... | _ | _ | nothing           = dead
      ... | _ | _ | just {p} {qs′} e′ = graft-res (k (↓ʳ S⃗ T⃗ p)) sf qs′ e′

      serve-res : {c : Ch C} {b : Ch B} (k : R B b → Calls⁺ B T⃗ (St g × R C c))
                  (u : Calls⁺ A S⃗ (St f × R B b)) (qs : Queues (S⃗ ++ T⃗)) → ∀ {qS qT}
                → splitQ S⃗ T⃗ qs ≡ (qS , qT)
                → mapᶜ (map₁ θ∘) (serve W ⌈ g ∘⁺ f ⌉ {b = inj₂ c} (λ r → ret ((tt , tt) , r))
                                     (resolve qs (serve⁺ g f k u)))
                  ≈ᶜ serve (Λ ∘ᵖ G) ⌈ f ⌉ {b = inj₂ b}
                       (λ r → serve Λ G {b = inj₂ (inj₂ c)} (λ r′ → ret (tt , r′))
                                (mapᶜ (map₁ (tt ,_)) (reindex ι₂ (resolve qT (k r)))))
                       (resolve qS u)
      serve-res k (ret (sf , r)) qs e = graft-res (k r) sf qs e
      serve-res k (call _ _ k′)  qs e = call λ r → serve-res k (k′ r) qs e
      serve-res k (coin _ k′)    qs e = coin λ x → serve-res k (k′ x) qs e
      serve-res k dead           qs e = dead
      serve-res k (choose i k′)  qs {qS} e
        with pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₁ i)) qs | pop S⃗ i qS | popˡ S⃗ T⃗ i e
      ... | _ | _ | nothing           = dead
      ... | _ | _ | just {p} {qs′} e′ = serve-res k (k′ (↓ˡ S⃗ T⃗ p)) qs′ e′

  ⌈⌉-∘ : ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ ⌈ g ∘⁺ f ⌉ ≈ᵖ ⌜ αᴵ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ⌈ g ⌉ ∘ᵖ ⌈ f ⌉
  ⌈⌉-∘ = ≲⇒≈ᵖ record
    { θ      = θ∘
    ; θ-init = cong (λ z → (tt , tt , init g , proj₂ z) , init f , proj₁ z) (splitQ-empty S⃗ T⃗)
    ; θ-step = λ where
        (_ , (sg , sf) , qs) (inj₁ (inj₁ i)) p →
          ret (cong₂ _,_ (cong (λ z → (tt , tt , sg , proj₂ z) , sf , proj₁ z) (push-joinˡ S⃗ T⃗ i p qs))
                         (tt⟦⟧-unique S⃗ _))
        (_ , (sg , sf) , qs) (inj₁ (inj₂ j)) p →
          ret (cong₂ _,_ (cong (λ z → (tt , tt , sg , proj₂ z) , sf , proj₁ z) (push-joinʳ S⃗ T⃗ j p qs))
                         (tt⟦⟧-unique T⃗ _))
        (_ , (sg , sf) , qs) (inj₂ c) q → graft-res (step g sg c q) sf qs refl }

  ⌈⌉-∘-split : ⌈ g ∘⁺ f ⌉ ≈ᵖ ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ (⌜ αᴵ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ⌈ g ⌉ ∘ᵖ ⌈ f ⌉)
  ⌈⌉-∘-split = begin
    ⌈ g ∘⁺ f ⌉
      ≈⟨ insertˡ {h = ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ} {i = ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ} (unsplit S⃗ T⃗) ⟩
    ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ (⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ ⌈ g ∘⁺ f ⌉)
      ≈⟨ refl⟩∘⟨_ {f = ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ} ⌈⌉-∘ ⟩
    ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ (⌜ αᴵ ⌝ ∘ᵖ wireᵖ ⊗ᵖ ⌈ g ⌉ ∘ᵖ ⌈ f ⌉) ∎
    where open MonoidalCategory Protᴹ using (U; module HomReasoning); open HomReasoning; open MR U

------------------------------------------------------------------------
-- Tensor
------------------------------------------------------------------------

module _ (P : Protocol⁺ S⃗ A B) (P′ : Protocol⁺ T⃗ C D) where

  private
    θ⊗ : (⊤ × ⊤) × (St P × St P′) × Queues (S⃗ ++ T⃗) → ⊤ × (St P × Queues S⃗) × St P′ × Queues T⃗
    θ⊗ (_ , (s , t) , qs) = tt , (s , proj₁ (splitQ S⃗ T⃗ qs)) , t , proj₂ (splitQ S⃗ T⃗ qs)

    W = ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ {B ⊗ᴵ D}
    I = ⌜ interchangeᴵ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {B} {D} ⌝

    left : {b : Ch B} (u : Calls⁺ A S⃗ (St P × R B b)) (t : St P′) (qs : Queues (S⃗ ++ T⃗)) → ∀ {qS qT}
         → splitQ S⃗ T⃗ qs ≡ (qS , qT)
         → mapᶜ (map₁ θ⊗) (serve W ⌈ P ⊗⁺ P′ ⌉ {b = inj₂ (inj₁ b)} (λ r → ret ((tt , tt) , r))
                              (resolve qs (mapᶜ⁺ (map₁ (_, t))
                                (reindex⁺ ι₁ (relocate (ch (join S⃗ T⃗) ∘ inj₁) (↓ˡ S⃗ T⃗) u)))))
           ≈ᶜ serve I (⌈ P ⌉ ⊗ᵖ ⌈ P′ ⌉) {b = inj₁ (inj₂ b)} (λ r → ret (tt , r))
                (mapᶜ (map₁ (_, t , qT)) (reindex ι₁ (resolve qS u)))
    left (ret (s , r)) t qs e = ret (cong (λ z → (tt , (s , proj₁ z) , t , proj₂ z) , r) e)
    left (call _ _ k)  t qs e = call λ r → left (k r) t qs e
    left (coin _ k)    t qs e = coin λ x → left (k x) t qs e
    left dead          t qs e = dead
    left (choose i k)  t qs {qS} e
      with pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₁ i)) qs | pop S⃗ i qS | popˡ S⃗ T⃗ i e
    ... | _ | _ | nothing           = dead
    ... | _ | _ | just {p} {qs′} e′ = left (k (↓ˡ S⃗ T⃗ p)) t qs′ e′

    right : {d : Ch D} (u : Calls⁺ C T⃗ (St P′ × R D d)) (s : St P) (qs : Queues (S⃗ ++ T⃗)) → ∀ {qS qT}
          → splitQ S⃗ T⃗ qs ≡ (qS , qT)
          → mapᶜ (map₁ θ⊗) (serve W ⌈ P ⊗⁺ P′ ⌉ {b = inj₂ (inj₂ d)} (λ r → ret ((tt , tt) , r))
                               (resolve qs (mapᶜ⁺ (map₁ (s ,_))
                                 (reindex⁺ ι₂ (relocate (ch (join S⃗ T⃗) ∘ inj₂) (↓ʳ S⃗ T⃗) u)))))
            ≈ᶜ serve I (⌈ P ⌉ ⊗ᵖ ⌈ P′ ⌉) {b = inj₂ (inj₂ d)} (λ r → ret (tt , r))
                 (mapᶜ (map₁ ((s , qS) ,_)) (reindex ι₂ (resolve qT u)))
    right (ret (t , r)) s qs e = ret (cong (λ z → (tt , (s , proj₁ z) , t , proj₂ z) , r) e)
    right (call _ _ k)  s qs e = call λ r → right (k r) s qs e
    right (coin _ k)    s qs e = coin λ x → right (k x) s qs e
    right dead          s qs e = dead
    right (choose j k)  s qs {qT = qT} e
      with pop (S⃗ ++ T⃗) (ch (join S⃗ T⃗) (inj₂ j)) qs | pop T⃗ j qT | popʳ S⃗ T⃗ j e
    ... | _ | _ | nothing           = dead
    ... | _ | _ | just {p} {qs′} e′ = right (k (↓ʳ S⃗ T⃗ p)) s qs′ e′

  ⌈⌉-⊗ : ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ ⌈ P ⊗⁺ P′ ⌉ ≈ᵖ ⌜ interchangeᴵ ⌝ ∘ᵖ ⌈ P ⌉ ⊗ᵖ ⌈ P′ ⌉
  ⌈⌉-⊗ = ≲⇒≈ᵖ record
    { θ      = θ⊗
    ; θ-init = cong (λ z → tt , (init P , proj₁ z) , init P′ , proj₂ z) (splitQ-empty S⃗ T⃗)
    ; θ-step = λ where
        (_ , (s , t) , qs) (inj₁ (inj₁ i)) p →
          ret (cong₂ _,_ (cong (λ z → tt , (s , proj₁ z) , t , proj₂ z) (push-joinˡ S⃗ T⃗ i p qs))
                         (tt⟦⟧-unique S⃗ _))
        (_ , (s , t) , qs) (inj₁ (inj₂ j)) p →
          ret (cong₂ _,_ (cong (λ z → tt , (s , proj₁ z) , t , proj₂ z) (push-joinʳ S⃗ T⃗ j p qs))
                         (tt⟦⟧-unique T⃗ _))
        (_ , (s , t) , qs) (inj₂ (inj₁ b)) q → left (step P s b q) t qs refl
        (_ , (s , t) , qs) (inj₂ (inj₂ d)) q → right (step P′ t d q) s qs refl }

  ⌈⌉-⊗-split : ⌈ P ⊗⁺ P′ ⌉ ≈ᵖ ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ (⌜ interchangeᴵ ⌝ ∘ᵖ ⌈ P ⌉ ⊗ᵖ ⌈ P′ ⌉)
  ⌈⌉-⊗-split = begin
    ⌈ P ⊗⁺ P′ ⌉
      ≈⟨ insertˡ {h = ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ} {i = ⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ} (unsplit S⃗ T⃗) ⟩
    ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ (⌜ join S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ ⌈ P ⊗⁺ P′ ⌉)
      ≈⟨ refl⟩∘⟨_ {f = ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ} ⌈⌉-⊗ ⟩
    ⌜ split S⃗ T⃗ ⌝ ⊗ᵖ wireᵖ ∘ᵖ (⌜ interchangeᴵ ⌝ ∘ᵖ ⌈ P ⌉ ⊗ᵖ ⌈ P′ ⌉) ∎
    where open MonoidalCategory Protᴹ using (U; module HomReasoning); open HomReasoning; open MR U
