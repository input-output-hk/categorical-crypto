{-# OPTIONS --safe --without-K #-}

-- ND_B and ND_A at SSP (`docs/uc-setup-nondeterministic.md` §2.2, §3.2, §4):
-- `ND.Grade` and `ND.A` at (Protˢ, Cᴵ) with SSP's tests.  The relabelling
-- wires `⌈_⌉ʳ` meet `ND.A.Relabelling`: the regrouping `C++` is, up to ≈ᵖ,
-- the wire pair ⌜ split ⌝, ⌜ join ⌝ of `ND.SSP.Choice` (`C++≈split`,
-- `C++≈join`), and the regroupings of C⟦ S⃗ ++ [] ⟧ and of a triple
-- concatenation are single wires along container maps with left inverses on
-- sites, hence relabellings (`Relabel.wireʳ`).

module CategoricalCrypto.ND.SSP.Setup where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function.Base using (id; _∘_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Level using (suc; 0ℓ)
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import CategoricalCrypto.Abstract2
import CategoricalCrypto.ND.A as A
import CategoricalCrypto.ND.Grade as Grade
open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.ND.SSP.Choice
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol
open import CategoricalCrypto.SSP.Protocol.Monoidal
open import CategoricalCrypto.SSP.Protocol.Wire
open import CategoricalCrypto.SSP.Setup using (ℰᵖ; _≤UC_; _≈ᵁ_)
open import CategoricalCrypto.UCSetup

private
  module G = Grade Protˢ Cᴵ
  module 𝔸 = A Protˢ Cᴵ
  open MonoidalCategory Protᴹ using (assoc; module Equiv; module HomReasoning)
  open HomReasoning

open G using (Grade; ⌊_⌋)

------------------------------------------------------------------------
-- The regroupings are Choice's wires
------------------------------------------------------------------------

C++≈split : (S⃗ T⃗ : List Set) → G.C++.from S⃗ T⃗ ≈ᵖ ⌜ split S⃗ T⃗ ⌝
C++≈split []      T⃗ = Equiv.refl
C++≈split (S ∷ S⃗) T⃗ =
  _⟩∘⟨refl {g = ⌜ α ⌝} (⊗ᵖ-resp-≈ᵖ (Equiv.refl {x = ⌜ I ⌝}) (C++≈split S⃗ T⃗) ○ ⌜⌝-⊗ I (split S⃗ T⃗))
  ○ ⌜⌝-∘ α (I ⊗ᴵᴵ split S⃗ T⃗)
  where
  I = idᴵ {Cᴵ S}
  α = αᴵ⁻¹ {Cᴵ S} {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧}

C++≈join : (S⃗ T⃗ : List Set) → G.C++.to S⃗ T⃗ ≈ᵖ ⌜ join S⃗ T⃗ ⌝
C++≈join []      T⃗ = Equiv.refl
C++≈join (S ∷ S⃗) T⃗ =
  refl⟩∘⟨_ {f = ⌜ α ⌝} (⊗ᵖ-resp-≈ᵖ (Equiv.refl {x = ⌜ I ⌝}) (C++≈join S⃗ T⃗) ○ ⌜⌝-⊗ I (join S⃗ T⃗))
  ○ ⌜⌝-∘ (I ⊗ᴵᴵ join S⃗ T⃗) α
  where
  I = idᴵ {Cᴵ S}
  α = αᴵ {Cᴵ S} {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧}

private
  unitʳᴵ : (S⃗ : List Set) → Cᴵ⟦ S⃗ ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ++ [] ⟧
  unitʳᴵ S⃗ = join S⃗ [] ∘ᴵ ι₁ {Cᴵ⟦ S⃗ ⟧} {unitᴵ}

  unitʳᴵ⁻¹ : (S⃗ : List Set) → Cᴵ⟦ S⃗ ++ [] ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ⟧
  unitʳᴵ⁻¹ S⃗ = ρᴵ {Cᴵ⟦ S⃗ ⟧} ∘ᴵ split S⃗ []

  assocᴵ : (S⃗ T⃗ U⃗ : List Set) → Cᴵ⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧ ⇒ᴵ Cᴵ⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧
  assocᴵ S⃗ T⃗ U⃗ = join (S⃗ ++ T⃗) U⃗ ∘ᴵ (join S⃗ T⃗ ⊗ᴵᴵ idᴵ) ∘ᴵ αᴵ⁻¹ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {Cᴵ⟦ U⃗ ⟧}
                ∘ᴵ (idᴵ ⊗ᴵᴵ split T⃗ U⃗) ∘ᴵ split S⃗ (T⃗ ++ U⃗)

  assocᴵ⁻¹ : (S⃗ T⃗ U⃗ : List Set) → Cᴵ⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧
  assocᴵ⁻¹ S⃗ T⃗ U⃗ = join S⃗ (T⃗ ++ U⃗) ∘ᴵ (idᴵ ⊗ᴵᴵ join T⃗ U⃗) ∘ᴵ αᴵ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {Cᴵ⟦ U⃗ ⟧}
                  ∘ᴵ (split S⃗ T⃗ ⊗ᴵᴵ idᴵ) ∘ᴵ split (S⃗ ++ T⃗) U⃗

  map-inv : {A B C D : Set} {f : A → B} (g : B → A) {h : C → D} (k : D → C)
          → (∀ a → g (f a) ≡ a) → (∀ c → k (h c) ≡ c) → ∀ x → Sum.map g k (Sum.map f h x) ≡ x
  map-inv g k p q (inj₁ a) = cong inj₁ (p a)
  map-inv g k p q (inj₂ c) = cong inj₂ (q c)

  assocʳˡ : {A B C : Set} (x : A ⊎ B ⊎ C) → Sum.assocʳ (Sum.assocˡ x) ≡ x
  assocʳˡ (inj₁ _)        = refl
  assocʳˡ (inj₂ (inj₁ _)) = refl
  assocʳˡ (inj₂ (inj₂ _)) = refl

  assocˡʳ : {A B C : Set} (x : (A ⊎ B) ⊎ C) → Sum.assocˡ (Sum.assocʳ x) ≡ x
  assocˡʳ (inj₁ (inj₁ _)) = refl
  assocˡʳ (inj₁ (inj₂ _)) = refl
  assocˡʳ (inj₂ _)        = refl

  unitʳ-inv : (S⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) → ch (unitʳᴵ⁻¹ S⃗) (ch (unitʳᴵ S⃗) i) ≡ i
  unitʳ-inv S⃗ i = cong [ id , ⊥-elim ]′ (split-join S⃗ [] (inj₁ i))

  unitʳ⁻¹-inv : (S⃗ : List Set) (c : Ch Cᴵ⟦ S⃗ ++ [] ⟧) → ch (unitʳᴵ S⃗) (ch (unitʳᴵ⁻¹ S⃗) c) ≡ c
  unitʳ⁻¹-inv S⃗ c = trans (cong (ch (join S⃗ [])) (unρ (ch (split S⃗ []) c))) (join-split S⃗ [] c)
    where
    unρ : (x : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ unitᴵ)) → inj₁ ([ id , ⊥-elim ]′ x) ≡ x
    unρ (inj₁ _) = refl
    unρ (inj₂ ())

  assoc-inv : (S⃗ T⃗ U⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧) → ch (assocᴵ⁻¹ S⃗ T⃗ U⃗) (ch (assocᴵ S⃗ T⃗ U⃗) i) ≡ i
  assoc-inv S⃗ T⃗ U⃗ i =
    trans (cong (λ x → j₄ (Sum.map id j₃ (Sum.assocʳ (Sum.map s₁ id x)))) (split-join (S⃗ ++ T⃗) U⃗ y₂))
   (trans (cong (λ x → j₄ (Sum.map id j₃ (Sum.assocʳ x))) (map-inv s₁ id (split-join S⃗ T⃗) (λ _ → refl) y₃))
   (trans (cong (λ x → j₄ (Sum.map id j₃ x)) (assocʳˡ y₄))
   (trans (cong j₄ (map-inv id j₃ (λ _ → refl) (join-split T⃗ U⃗) (s₄ i))) (join-split S⃗ (T⃗ ++ U⃗) i))))
    where
    s₁ = ch (split S⃗ T⃗)
    s₄ = ch (split S⃗ (T⃗ ++ U⃗))
    j₃ = ch (join T⃗ U⃗)
    j₄ = ch (join S⃗ (T⃗ ++ U⃗))
    y₄ = Sum.map id (ch (split T⃗ U⃗)) (s₄ i)
    y₃ = Sum.assocˡ y₄
    y₂ = Sum.map (ch (join S⃗ T⃗)) id y₃

  assoc⁻¹-inv : (S⃗ T⃗ U⃗ : List Set) (c : Ch Cᴵ⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧)
              → ch (assocᴵ S⃗ T⃗ U⃗) (ch (assocᴵ⁻¹ S⃗ T⃗ U⃗) c) ≡ c
  assoc⁻¹-inv S⃗ T⃗ U⃗ c =
    trans (cong (λ x → j₂ (Sum.map j₁ id (Sum.assocˡ (Sum.map id s₃ x)))) (split-join S⃗ (T⃗ ++ U⃗) z₂))
   (trans (cong (λ x → j₂ (Sum.map j₁ id (Sum.assocˡ x))) (map-inv id s₃ (λ _ → refl) (split-join T⃗ U⃗) z₃))
   (trans (cong (λ x → j₂ (Sum.map j₁ id x)) (assocˡʳ z₄))
   (trans (cong j₂ (map-inv j₁ id (join-split S⃗ T⃗) (λ _ → refl) (s₂ c))) (join-split (S⃗ ++ T⃗) U⃗ c))))
    where
    j₁ = ch (join S⃗ T⃗)
    j₂ = ch (join (S⃗ ++ T⃗) U⃗)
    s₂ = ch (split (S⃗ ++ T⃗) U⃗)
    s₃ = ch (split T⃗ U⃗)
    z₄ = Sum.map (ch (split S⃗ T⃗)) id (s₂ c)
    z₃ = Sum.assocʳ z₄
    z₂ = Sum.map id (ch (join T⃗ U⃗)) z₃

  -- the regroupings of `ND.A`, as single wires
  unit++⇒ : (S⃗ : List Set) → 𝔸.unit++.from S⃗ ≈ᵖ ⌜ unitʳᴵ S⃗ ⌝
  unit++⇒ S⃗ = refl⟩∘⟨_ {f = ⌜ ι₁ {Cᴵ⟦ S⃗ ⟧} {unitᴵ} ⌝} (C++≈join S⃗ []) ○ ⌜⌝-∘ (join S⃗ []) ι₁

  unit++⇐ : (S⃗ : List Set) → 𝔸.unit++.to S⃗ ≈ᵖ ⌜ unitʳᴵ⁻¹ S⃗ ⌝
  unit++⇐ S⃗ = _⟩∘⟨refl {g = ⌜ ρᴵ {Cᴵ⟦ S⃗ ⟧} ⌝} (C++≈split S⃗ []) ○ ⌜⌝-∘ ρᴵ (split S⃗ [])

  assoc++⇒ : (S⃗ T⃗ U⃗ : List Set) → 𝔸.assoc++.from S⃗ T⃗ U⃗ ≈ᵖ ⌜ assocᴵ S⃗ T⃗ U⃗ ⌝
  assoc++⇒ S⃗ T⃗ U⃗ = begin
    𝔸.assoc++.from S⃗ T⃗ U⃗
      ≈⟨ C++≈split S⃗ (T⃗ ++ U⃗) ⟩∘⟨ (⊗ᵖ-resp-≈ᵖ (Equiv.refl {x = ⌜ I ⌝}) (C++≈split T⃗ U⃗) ○ ⌜⌝-⊗ I (split T⃗ U⃗))
           ⟩∘⟨ refl⟩∘⟨_ {f = ⌜ α ⌝} ((⊗ᵖ-resp-≈ᵖ (C++≈join S⃗ T⃗) (Equiv.refl {x = ⌜ I′ ⌝}) ○ ⌜⌝-⊗ (join S⃗ T⃗) I′)
                                     ⟩∘⟨ C++≈join (S⃗ ++ T⃗) U⃗) ⟩
    ⌜ split S⃗ (T⃗ ++ U⃗) ⌝ ∘ᵖ (⌜ I ⊗ᴵᴵ split T⃗ U⃗ ⌝ ∘ᵖ (⌜ α ⌝ ∘ᵖ (⌜ join S⃗ T⃗ ⊗ᴵᴵ I′ ⌝ ∘ᵖ ⌜ join (S⃗ ++ T⃗) U⃗ ⌝)))
      ≈˘⟨ ≲⇒≈ᵖ (≲ᵖ-const λ _ _ _ → ≈ᶜ-refl) ⟩
    ⌜ assocᴵ S⃗ T⃗ U⃗ ⌝ ∎
    where
    I = idᴵ {Cᴵ⟦ S⃗ ⟧}
    I′ = idᴵ {Cᴵ⟦ U⃗ ⟧}
    α = αᴵ⁻¹ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {Cᴵ⟦ U⃗ ⟧}

  assoc++⇐ : (S⃗ T⃗ U⃗ : List Set) → 𝔸.assoc++.to S⃗ T⃗ U⃗ ≈ᵖ ⌜ assocᴵ⁻¹ S⃗ T⃗ U⃗ ⌝
  assoc++⇐ S⃗ T⃗ U⃗ = begin
    𝔸.assoc++.to S⃗ T⃗ U⃗
      ≈⟨ (((C++≈split (S⃗ ++ T⃗) U⃗ ⟩∘⟨ (⊗ᵖ-resp-≈ᵖ (C++≈split S⃗ T⃗) (Equiv.refl {x = ⌜ I′ ⌝}) ○ ⌜⌝-⊗ (split S⃗ T⃗) I′))
             ⟩∘⟨ Equiv.refl {x = ⌜ α ⌝})
             ⟩∘⟨ (⊗ᵖ-resp-≈ᵖ (Equiv.refl {x = ⌜ I ⌝}) (C++≈join T⃗ U⃗) ○ ⌜⌝-⊗ I (join T⃗ U⃗)))
           ⟩∘⟨ C++≈join S⃗ (T⃗ ++ U⃗) ⟩
    ⌜ split (S⃗ ++ T⃗) U⃗ ⌝ ∘ᵖ ⌜ split S⃗ T⃗ ⊗ᴵᴵ I′ ⌝ ∘ᵖ ⌜ α ⌝ ∘ᵖ ⌜ I ⊗ᴵᴵ join T⃗ U⃗ ⌝ ∘ᵖ ⌜ join S⃗ (T⃗ ++ U⃗) ⌝
      ≈˘⟨ ≲⇒≈ᵖ (≲ᵖ-const λ _ _ _ → ≈ᶜ-refl) ⟩
    ⌜ assocᴵ⁻¹ S⃗ T⃗ U⃗ ⌝ ∎
    where
    I = idᴵ {Cᴵ⟦ S⃗ ⟧}
    I′ = idᴵ {Cᴵ⟦ U⃗ ⟧}
    α = αᴵ {Cᴵ⟦ S⃗ ⟧} {Cᴵ⟦ T⃗ ⟧} {Cᴵ⟦ U⃗ ⟧}

relabelling : 𝔸.Relabelling
relabelling = record
  { ⌈_⌉    = ⌈_⌉ʳ
  ; ⌈⌉-id  = λ {S⃗} → ≲⇒≈ᵖ (⌈⌉ʳ-id {S⃗})
  ; ⌈⌉-∘   = λ ρ′ ρ → ≲⇒≈ᵖ (⌈⌉ʳ-∘ ρ′ ρ)
  ; ⌈⌉-++  = λ {S⃗} {T⃗} {S⃗′} {T⃗′} ρ ρ′ →
      ⌈⌉ʳ-++ ρ ρ′ ○ assoc {f = ⌜ join T⃗ T⃗′ ⌝} {g = ⌈ ρ ⌉ʳ ⊗ᵖ ⌈ ρ′ ⌉ʳ} {h = ⌜ split S⃗ S⃗′ ⌝}
      ○ ⟺ (C++≈split S⃗ S⃗′) ⟩∘⟨ refl⟩∘⟨_ {f = ⌈ ρ ⌉ʳ ⊗ᵖ ⌈ ρ′ ⌉ʳ} (⟺ (C++≈join T⃗ T⃗′))
  ; unit⇒  = λ S⃗ → wireʳ (unitʳᴵ S⃗) (ch (unitʳᴵ⁻¹ S⃗)) (unitʳ-inv S⃗)
                 , (≲⇒≈ᵖ (⌈⌉ʳ-wire {S⃗} {S⃗ ++ []} (unitʳᴵ S⃗) (ch (unitʳᴵ⁻¹ S⃗)) (unitʳ-inv S⃗)) ○ ⟺ (unit++⇒ S⃗))
  ; unit⇐  = λ S⃗ → wireʳ (unitʳᴵ⁻¹ S⃗) (ch (unitʳᴵ S⃗)) (unitʳ⁻¹-inv S⃗)
                 , (≲⇒≈ᵖ (⌈⌉ʳ-wire {S⃗ ++ []} {S⃗} (unitʳᴵ⁻¹ S⃗) (ch (unitʳᴵ S⃗)) (unitʳ⁻¹-inv S⃗)) ○ ⟺ (unit++⇐ S⃗))
  ; assoc⇒ = λ S⃗ T⃗ U⃗ → wireʳ (assocᴵ S⃗ T⃗ U⃗) (ch (assocᴵ⁻¹ S⃗ T⃗ U⃗)) (assoc-inv S⃗ T⃗ U⃗)
                      , (≲⇒≈ᵖ (⌈⌉ʳ-wire {S⃗ ++ (T⃗ ++ U⃗)} {(S⃗ ++ T⃗) ++ U⃗} (assocᴵ S⃗ T⃗ U⃗) (ch (assocᴵ⁻¹ S⃗ T⃗ U⃗))
                                          (assoc-inv S⃗ T⃗ U⃗))
                         ○ ⟺ (assoc++⇒ S⃗ T⃗ U⃗))
  ; assoc⇐ = λ S⃗ T⃗ U⃗ → wireʳ (assocᴵ⁻¹ S⃗ T⃗ U⃗) (ch (assocᴵ S⃗ T⃗ U⃗)) (assoc⁻¹-inv S⃗ T⃗ U⃗)
                      , (≲⇒≈ᵖ (⌈⌉ʳ-wire {(S⃗ ++ T⃗) ++ U⃗} {S⃗ ++ (T⃗ ++ U⃗)} (assocᴵ⁻¹ S⃗ T⃗ U⃗) (ch (assocᴵ S⃗ T⃗ U⃗))
                                          (assoc⁻¹-inv S⃗ T⃗ U⃗))
                         ○ ⟺ (assoc++⇐ S⃗ T⃗ U⃗)) }

------------------------------------------------------------------------
-- The setups
------------------------------------------------------------------------

NDB : UCSetup (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) _ _
NDB = G.NDB ℰᵖ

NDA : UCSetup (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) (suc 0ℓ) _ _
NDA = 𝔸.NDA relabelling ℰᵖ

-- Generalized variables over these dependent types crash Agda 2.8.0 in
-- `EtaContract`, so the telescope is bound explicitly.  Each statement is
-- instantiated here, at variables; using one at concrete protocols, see
-- `ND.SSP.Laws.pick-≤UC`.
module _ {A B : Iface} {a b : Grade} {f : Protocol A (⌊ a ⌋ ⊗ᴵ B)} {g : Protocol A (⌊ b ⌋ ⊗ᴵ B)} where

  ≤UC-B⇔≤UC : AbstractUC._≤UC_ NDB {X = a} {Y = b} f g ⇔ f ≤UC g
  ≤UC-B⇔≤UC = G.≤UC-B⇔≤UC ℰᵖ {a = a} {b = b}

  A⇒B : AbstractUC._≤UC_ NDA {X = a} {Y = b} f g → AbstractUC._≤UC_ NDB {X = a} {Y = b} f g
  A⇒B = 𝔸.A⇒B relabelling ℰᵖ {a = a} {b = b}

  A⇒SSP : AbstractUC._≤UC_ NDA {X = a} {Y = b} f g → f ≤UC g
  A⇒SSP = Equivalence.to ≤UC-B⇔≤UC ∘ A⇒B

  relabel-≤UC : (s : Protocol ⌊ b ⌋ ⌊ a ⌋) → 𝔸.Relabels relabelling {b} {a} s
              → _≈ᵁ_ {X = ⌊ a ⌋} f (s ⊗ᵖ wireᵖ ∘ᵖ g) → AbstractUC._≤UC_ NDA {X = a} {Y = b} f g
  relabel-≤UC = 𝔸.relabel-≤UC relabelling ℰᵖ {A = A} {B = B} {a = a} {b = b} {f = f} {g = g}
