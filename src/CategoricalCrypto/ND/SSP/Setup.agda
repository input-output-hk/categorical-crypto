{-# OPTIONS --safe --without-K #-}

-- ND_B and ND_A at SSP (`docs/uc-setup-nondeterministic.md` §2.2, §3.2, §4):
-- `ND.Grade` and `ND.A` at (Protˢ, Cᴵ) with SSP's tests.  The relabelling
-- wires `⌈_⌉ʳ` meet `ND.A.Relabelling`: the regrouping `C++` is, up to ≈ᵖ,
-- the wire pair ⌜ split ⌝, ⌜ join ⌝ of `ND.SSP.Choice` (`C++≈split`,
-- `C++≈join`), and the regroupings of C⟦ S⃗ ++ [] ⟧ and of a triple
-- concatenation are single wires along container maps with left inverses on
-- sites, hence relabellings (`Relabel.unit⇒ʳ` … `assoc⇐ʳ`, each a `wireʳ`).
-- An A-emulation is one whose simulator is u ⊗ ⌈ ρ ⌉ up to SSP's U-kernel
-- (`relabel-≤UC`, `≤UC⇒relabel`).

module CategoricalCrypto.ND.SSP.Setup where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; Equivalence)
open import Level using (suc; 0ℓ)

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
  ; unit⇒  = λ S⃗ → unit⇒ʳ S⃗
                 , (≲⇒≈ᵖ (⌈⌉ʳ-wire {S⃗} {S⃗ ++ []} (unitʳᴵ S⃗) (ch (unitʳᴵ⁻¹ S⃗)) (unitʳ-inv S⃗)) ○ ⟺ (unit++⇒ S⃗))
  ; unit⇐  = λ S⃗ → unit⇐ʳ S⃗
                 , (≲⇒≈ᵖ (⌈⌉ʳ-wire {S⃗ ++ []} {S⃗} (unitʳᴵ⁻¹ S⃗) (ch (unitʳᴵ S⃗)) (unitʳ⁻¹-inv S⃗)) ○ ⟺ (unit++⇐ S⃗))
  ; assoc⇒ = λ S⃗ T⃗ U⃗ → assoc⇒ʳ S⃗ T⃗ U⃗
                      , (≲⇒≈ᵖ (⌈⌉ʳ-wire {S⃗ ++ (T⃗ ++ U⃗)} {(S⃗ ++ T⃗) ++ U⃗} (assocᴵ S⃗ T⃗ U⃗) (ch (assocᴵ⁻¹ S⃗ T⃗ U⃗))
                                          (assoc-inv S⃗ T⃗ U⃗))
                         ○ ⟺ (assoc++⇒ S⃗ T⃗ U⃗))
  ; assoc⇐ = λ S⃗ T⃗ U⃗ → assoc⇐ʳ S⃗ T⃗ U⃗
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
-- instantiated here, at variables, and passes `_≤UC_` its interfaces; using one
-- at concrete protocols, see `ND.SSP.Laws.pick-≤UC`.
module _ {A B : Iface} {a b : Grade} {f : Protocol A (⌊ a ⌋ ⊗ᴵ B)} {g : Protocol A (⌊ b ⌋ ⊗ᴵ B)} where

  ≤UC-B⇔≤UC : AbstractUC._≤UC_ NDB {A = A} {X = a} {B = B} {Y = b} f g ⇔ f ≤UC g
  ≤UC-B⇔≤UC = G.≤UC-B⇔≤UC ℰᵖ {a = a} {b = b}

  A⇒B : AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g → AbstractUC._≤UC_ NDB {A = A} {X = a} {B = B} {Y = b} f g
  A⇒B = 𝔸.A⇒B relabelling ℰᵖ {a = a} {b = b}

  A⇒SSP : AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g → f ≤UC g
  A⇒SSP = Equivalence.to ≤UC-B⇔≤UC ∘ A⇒B

  relabel-≤UC : (s : Protocol ⌊ b ⌋ ⌊ a ⌋) → 𝔸.Relabels relabelling {b} {a} s
              → _≈ᵁ_ {X = ⌊ a ⌋} f (s ⊗ᵖ wireᵖ ∘ᵖ g) → AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g
  relabel-≤UC = 𝔸.relabel-≤UC relabelling ℰᵖ {A = A} {B = B} {a = a} {b = b} {f = f} {g = g}

  ≤UC⇒relabel : AbstractUC._≤UC_ NDA {A = A} {X = a} {B = B} {Y = b} f g
              → Σ[ s ∈ Protocol ⌊ b ⌋ ⌊ a ⌋ ] 𝔸.Relabels relabelling {b} {a} s × _≈ᵁ_ {X = ⌊ a ⌋} f (s ⊗ᵖ wireᵖ ∘ᵖ g)
  ≤UC⇒relabel = 𝔸.≤UC⇒relabel relabelling ℰᵖ {A = A} {B = B} {a = a} {b = b} {f = f} {g = g}
