{-# OPTIONS --safe --without-K #-}

-- Model A (`docs/uc-setup-nondeterministic.md` §3.2, §4): the grade morphisms
-- of 𝒢B that are u ⊗ ⌈ ρ ⌉, u arbitrary and ρ a relabelling of choice sites.
-- `Relabelling` asks ⌈−⌉ to be a functor Alphᵒᵖ → 𝕄 on C⟦_⟧, monoidal through
-- `C++`, and to realize the regroupings of C⟦ S⃗ ++ [] ⟧ and of a triple
-- concatenation.  The class is then closed (`closedA`): under ⊗ᵗ by naturality
-- of the middle-four interchange, and the transported unitors and associator
-- are of the form by the interchange's unit and associativity laws (the
-- braiding's naturality and hexagon, §2.3).  𝒢A is wide in 𝒢B (`incl`), ND_A
-- is ND_B restricted along it, and an A-emulation is a B-emulation with the
-- same simulator (`A⇒B`: §1.3 (c) at identity comparisons).

open import Categories.Category.Monoidal.Bundle

module CategoricalCrypto.ND.A {o ℓ e} (𝕄 : SymmetricMonoidalCategory o ℓ e)
  (C : Set → SymmetricMonoidalCategory.Obj 𝕄) where

open import Data.List.Base using (List; []; _++_)
open import Data.Product
open import Data.Unit.Base
open import Level

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal.Interchange.Braided (SymmetricMonoidalCategory.braided 𝕄)
open import Categories.Category.Monoidal.Reasoning (SymmetricMonoidalCategory.monoidal 𝕄)
open import Categories.Category.Monoidal.Utilities (SymmetricMonoidalCategory.monoidal 𝕄)
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
import Categories.Morphism as Mor
open import Categories.Morphism.Properties (SymmetricMonoidalCategory.U 𝕄)
open import Categories.Morphism.Reasoning (SymmetricMonoidalCategory.U 𝕄)

open import CategoricalCrypto.Abstract2
import CategoricalCrypto.Abstract2.Regrade as Regrade
open import CategoricalCrypto.ND.Grade 𝕄 C
open import CategoricalCrypto.ND.Relabel
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.UCSetup

open SymmetricMonoidalCategory 𝕄
open Mor U
open Shorthands
open 𝒯

-- The regroupings that ρᵗ and αᵗ carry on the choice factors.
unit++ : (S⃗ : List Set) → C⟦ S⃗ ++ [] ⟧ ≅ C⟦ S⃗ ⟧
unit++ S⃗ = ≅.trans (≅.sym (C++ S⃗ [])) unitorʳ

assoc++ : (S⃗ T⃗ U⃗ : List Set) → C⟦ (S⃗ ++ T⃗) ++ U⃗ ⟧ ≅ C⟦ S⃗ ++ (T⃗ ++ U⃗) ⟧
assoc++ S⃗ T⃗ U⃗ = ≅.trans (≅.trans (≅.trans (≅.trans (≅.sym (C++ (S⃗ ++ T⃗) U⃗)) (≅.sym (C++ S⃗ T⃗) ⊗ᵢ ≅.refl))
                                         associator)
                                (≅.refl ⊗ᵢ C++ T⃗ U⃗))
                       (C++ S⃗ (T⃗ ++ U⃗))

module unit++ S⃗ = _≅_ (unit++ S⃗)
module assoc++ S⃗ T⃗ U⃗ = _≅_ (assoc++ S⃗ T⃗ U⃗)

record Relabelling : Set (ℓ ⊔ e ⊔ suc 0ℓ) where
  field ⌈_⌉    : ∀ {S⃗ T⃗} → S⃗ ⇝ T⃗ → C⟦ T⃗ ⟧ ⇒ C⟦ S⃗ ⟧
        ⌈⌉-id  : ∀ {S⃗} → ⌈ idʳ {S⃗} ⌉ ≈ id
        ⌈⌉-∘   : ∀ {S⃗ T⃗ U⃗} (ρ′ : T⃗ ⇝ U⃗) (ρ : S⃗ ⇝ T⃗) → ⌈ ρ′ ∘ʳ ρ ⌉ ≈ ⌈ ρ ⌉ ∘ ⌈ ρ′ ⌉
        ⌈⌉-++  : ∀ {S⃗ T⃗ S⃗′ T⃗′} (ρ : S⃗ ⇝ T⃗) (ρ′ : S⃗′ ⇝ T⃗′)
               → ⌈ ρ ++ʳ ρ′ ⌉ ≈ C++.from S⃗ S⃗′ ∘ ⌈ ρ ⌉ ⊗₁ ⌈ ρ′ ⌉ ∘ C++.to T⃗ T⃗′
        unit⇒  : (S⃗ : List Set) → Σ[ ρ ∈ S⃗ ⇝ S⃗ ++ [] ] ⌈ ρ ⌉ ≈ unit++.from S⃗
        unit⇐  : (S⃗ : List Set) → Σ[ ρ ∈ S⃗ ++ [] ⇝ S⃗ ] ⌈ ρ ⌉ ≈ unit++.to S⃗
        assoc⇒ : (S⃗ T⃗ U⃗ : List Set)
               → Σ[ ρ ∈ S⃗ ++ (T⃗ ++ U⃗) ⇝ (S⃗ ++ T⃗) ++ U⃗ ] ⌈ ρ ⌉ ≈ assoc++.from S⃗ T⃗ U⃗
        assoc⇐ : (S⃗ T⃗ U⃗ : List Set)
               → Σ[ ρ ∈ (S⃗ ++ T⃗) ++ U⃗ ⇝ S⃗ ++ (T⃗ ++ U⃗) ] ⌈ ρ ⌉ ≈ assoc++.to S⃗ T⃗ U⃗

private
  module φ {a b} = _≅_ (φ {a} {b})

  i⇒ : ∀ {W X Y Z} → (W ⊗₀ X) ⊗₀ (Y ⊗₀ Z) ⇒ (W ⊗₀ Y) ⊗₀ (X ⊗₀ Z)
  i⇒ = swapInner.from

  -- The transported structure maps, as 𝕄-maps on the ordinary part tensored
  -- with a regrouping of the choice factors.
  λᵗ-shape : ∀ {a} → λᵗ⇒ {a} ≈ λ⇒ ⊗₁ id
  λᵗ-shape {a} = cancel-fromʳ (≅.trans (υ ⊗ᵢ ≅.refl) (φ {𝟙} {a}))
    (unitaryˡᵗ {a} ○ ⟺ (refl⟩∘⟨ assoc ○ pullˡ (⟺ serialize₁₂) ○ swapInner-unitˡ))

  ρᵗ-shape : ∀ {a} → ρᵗ⇒ {a} ≈ ρ⇒ ⊗₁ unit++.from (proj₂ a)
  ρᵗ-shape {a} = cancel-fromʳ (≅.trans (≅.refl ⊗ᵢ υ) (φ {a} {𝟙}))
    (unitaryʳᵗ {a} ○ ⟺ (refl⟩∘⟨ assoc ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ cancelʳ (C++.isoˡ (proj₂ a) []))
                        ○ swapInner-unitʳ))

  αᵗ-shape : ∀ {a b c} → αᵗ⇒ {a} {b} {c} ≈ α⇒ ⊗₁ assoc++.from (proj₂ a) (proj₂ b) (proj₂ c)
  αᵗ-shape {a@(_ , S⃗)} {b@(_ , T⃗)} {c@(_ , U⃗)} =
    cancel-fromʳ (≅.trans (φ {a} {b} ⊗ᵢ ≅.refl) (φ {a ⊕ b} {c})) (associativityᵗ {a} {b} {c} ○ ⟺ (begin
    α⇒ ⊗₁ (P₄ ∘ id ⊗₁ P₃ ∘ α⇒ ∘ Q₁ ⊗₁ id ∘ Q₂) ∘ (id ⊗₁ P₂ ∘ i⇒) ∘ (id ⊗₁ P₁ ∘ i⇒) ⊗₁ id
      ≈⟨ refl⟩∘⟨ assoc ○ pullˡ (merge₂ʳ ○ refl⟩⊗⟨ pullʳ (pullʳ (pullʳ (cancelʳ (C++.isoˡ (S⃗ ++ T⃗) U⃗))))) ⟩
    α⇒ ⊗₁ (P₄ ∘ id ⊗₁ P₃ ∘ α⇒ ∘ Q₁ ⊗₁ id) ∘ i⇒ ∘ (id ⊗₁ P₁ ∘ i⇒) ⊗₁ id
      ≈⟨ (split₂ˡ ○ refl⟩∘⟨ (split₂ˡ ○ refl⟩∘⟨ split₂ʳ)) ⟩∘⟨ refl⟩∘⟨ split₁ˡ ⟩
    (id ⊗₁ P₄ ∘ id ⊗₁ (id ⊗₁ P₃) ∘ α⇒ ⊗₁ α⇒ ∘ id ⊗₁ (Q₁ ⊗₁ id)) ∘ i⇒ ∘ (id ⊗₁ P₁) ⊗₁ id ∘ i⇒ ⊗₁ id
      ≈⟨ assoc ○ refl⟩∘⟨ assoc ○ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    id ⊗₁ P₄ ∘ id ⊗₁ (id ⊗₁ P₃) ∘ α⇒ ⊗₁ α⇒ ∘ id ⊗₁ (Q₁ ⊗₁ id) ∘ i⇒ ∘ (id ⊗₁ P₁) ⊗₁ id ∘ i⇒ ⊗₁ id
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ sym-assoc
           ○ refl⟩∘⟨ ((refl⟩∘⟨ refl⟩⊗⟨ ⟺ ⊗.identity) ○ swapInner-natural) ⟩∘⟨refl
           ○ refl⟩∘⟨ assoc ○ pullˡ cancel ○ identityˡ) ⟩
    id ⊗₁ P₄ ∘ id ⊗₁ (id ⊗₁ P₃) ∘ α⇒ ⊗₁ α⇒ ∘ i⇒ ∘ i⇒ ⊗₁ id
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swapInner-assoc ⟩
    id ⊗₁ P₄ ∘ id ⊗₁ (id ⊗₁ P₃) ∘ i⇒ ∘ id ⊗₁ i⇒ ∘ α⇒
      ≈⟨ refl⟩∘⟨ ((⟺ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ○ pullˡ (⟺ swapInner-natural) ○ assoc
                 ○ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
    id ⊗₁ P₄ ∘ i⇒ ∘ id ⊗₁ (id ⊗₁ P₃) ∘ id ⊗₁ i⇒ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    id ⊗₁ P₄ ∘ i⇒ ∘ id ⊗₁ (id ⊗₁ P₃ ∘ i⇒) ∘ α⇒
      ≈˘⟨ assoc ⟩
    (id ⊗₁ P₄ ∘ i⇒) ∘ id ⊗₁ (id ⊗₁ P₃ ∘ i⇒) ∘ α⇒ ∎))
    where
    P₁ = C++.from S⃗ T⃗
    P₂ = C++.from (S⃗ ++ T⃗) U⃗
    P₃ = C++.from T⃗ U⃗
    P₄ = C++.from S⃗ (T⃗ ++ U⃗)
    Q₁ = C++.to S⃗ T⃗
    Q₂ = C++.to (S⃗ ++ T⃗) U⃗
    -- the inner φ's regrouping cancels against assoc++'s
    cancel = ⟺ ⊗.homomorphism
           ○ (identityˡ ○ ⊗.identity) ⟩⊗⟨ (⟺ ⊗.homomorphism ○ C++.isoˡ S⃗ T⃗ ⟩⊗⟨ identity² ○ ⊗.identity)
           ○ ⊗.identity

------------------------------------------------------------------------
-- The class, 𝒢A and A ⇒ B
------------------------------------------------------------------------

module _ (rel : Relabelling) where
  open Relabelling rel

  Relabels : ∀ {a b} → ⌊ a ⌋ ⇒ ⌊ b ⌋ → Set (ℓ ⊔ e)
  Relabels {X , S⃗} {Y , T⃗} f = Σ[ u ∈ X ⇒ Y ] Σ[ ρ ∈ T⃗ ⇝ S⃗ ] f ≈ u ⊗₁ ⌈ ρ ⌉

  closedA : Closed (λ {a} {b} → Relabels {a} {b})
  closedA = record
    { R-id = id , idʳ , ⟺ (refl⟩⊗⟨ ⌈⌉-id ○ ⊗.identity)
    ; R-∘  = λ (u , ρ , e) (u′ , ρ′ , e′) →
        u ∘ u′ , ρ′ ∘ʳ ρ , (∘-resp-≈ e e′ ○ ⟺ ⊗.homomorphism ○ refl⟩⊗⟨ ⟺ (⌈⌉-∘ ρ′ ρ))
    ; R-⊗  = λ {a} {b} {c} {d} → R-⊗′ {a} {b} {c} {d}
    ; R-λ⇒ = λ {a} → λ⇒ , idʳ , (λᵗ-shape {a} ○ refl⟩⊗⟨ ⟺ ⌈⌉-id)
    ; R-λ⇐ = λ {a} → λ⇐ , idʳ
                   , (Iso-≈ (λᵗ-shape {a}) (_≅_.iso (unitorˡᵗ {a})) (_≅_.iso (unitorˡ ⊗ᵢ ≅.refl))
                      ○ refl⟩⊗⟨ ⟺ ⌈⌉-id)
    ; R-ρ⇒ = λ {a} → ρ⇒ , proj₁ (unit⇒ (proj₂ a)) , (ρᵗ-shape {a} ○ refl⟩⊗⟨ ⟺ (proj₂ (unit⇒ (proj₂ a))))
    ; R-ρ⇐ = λ {a} → ρ⇐ , proj₁ (unit⇐ (proj₂ a))
                   , (Iso-≈ (ρᵗ-shape {a}) (_≅_.iso (unitorʳᵗ {a})) (_≅_.iso (unitorʳ ⊗ᵢ unit++ (proj₂ a)))
                      ○ refl⟩⊗⟨ ⟺ (proj₂ (unit⇐ (proj₂ a))))
    ; R-α⇒ = λ {a} {b} {c} → α⇒ , proj₁ (assoc⇒ (proj₂ a) (proj₂ b) (proj₂ c))
                           , (αᵗ-shape {a} {b} {c} ○ refl⟩⊗⟨ ⟺ (proj₂ (assoc⇒ (proj₂ a) (proj₂ b) (proj₂ c))))
    ; R-α⇐ = λ {a} {b} {c} → α⇐ , proj₁ (assoc⇐ (proj₂ a) (proj₂ b) (proj₂ c))
                           , (Iso-≈ (αᵗ-shape {a} {b} {c}) (_≅_.iso (associatorᵗ {a} {b} {c}))
                                    (_≅_.iso (associator ⊗ᵢ assoc++ (proj₂ a) (proj₂ b) (proj₂ c)))
                              ○ refl⟩⊗⟨ ⟺ (proj₂ (assoc⇐ (proj₂ a) (proj₂ b) (proj₂ c)))) }
    where
    R-⊗′ : ∀ {a b c d} {f : ⌊ a ⌋ ⇒ ⌊ b ⌋} {g : ⌊ c ⌋ ⇒ ⌊ d ⌋} → Relabels {a} {b} f → Relabels {c} {d} g
         → Relabels {a ⊕ c} {b ⊕ d} (_⊗ᵗ_ {a} {b} {c} {d} f g)
    R-⊗′ {X , S⃗} {Y , T⃗} {X′ , S⃗′} {Y′ , T⃗′} {f} {g} (u , ρ , e) (u′ , ρ′ , e′) = u ⊗₁ u′ , ρ ++ʳ ρ′ , (begin
      (id ⊗₁ C++.from T⃗ T⃗′ ∘ swapInner.from) ∘ f ⊗₁ g ∘ swapInner.to ∘ id ⊗₁ C++.to S⃗ S⃗′
        ≈⟨ refl⟩∘⟨ e ⟩⊗⟨ e′ ⟩∘⟨refl ⟩
      (id ⊗₁ C++.from T⃗ T⃗′ ∘ swapInner.from) ∘ (u ⊗₁ ⌈ ρ ⌉) ⊗₁ (u′ ⊗₁ ⌈ ρ′ ⌉) ∘ swapInner.to ∘ id ⊗₁ C++.to S⃗ S⃗′
        ≈⟨ assoc ○ refl⟩∘⟨ (pullˡ swapInner-natural ○ assoc ○ refl⟩∘⟨ cancelˡ swapInner.isoʳ) ⟩
      id ⊗₁ C++.from T⃗ T⃗′ ∘ (u ⊗₁ u′) ⊗₁ (⌈ ρ ⌉ ⊗₁ ⌈ ρ′ ⌉) ∘ id ⊗₁ C++.to S⃗ S⃗′
        ≈⟨ refl⟩∘⟨ merge₂ʳ ○ merge₂ˡ ⟩
      (u ⊗₁ u′) ⊗₁ (C++.from T⃗ T⃗′ ∘ ⌈ ρ ⌉ ⊗₁ ⌈ ρ′ ⌉ ∘ C++.to S⃗ S⃗′)
        ≈˘⟨ refl⟩⊗⟨ ⌈⌉-++ ρ ρ′ ⟩
      (u ⊗₁ u′) ⊗₁ ⌈ ρ ++ʳ ρ′ ⌉ ∎)

  private module 𝒜 = Restriction (λ {a} {b} → Relabels {a} {b}) closedA

  𝒢A : MonoidalCategory (o ⊔ suc 0ℓ) (ℓ ⊔ e) e
  𝒢A = 𝒜.transport

  incl : StrongMonoidalFunctor 𝒢A 𝒢B
  incl = weaken closedA closedB (λ _ → tt)

  module _ {cs ℓs : Level} (ℰ : Presheaf U (Setoids cs ℓs)) where
    private module NA = Regrade (NDB ℰ) (StrongMonoidalFunctor.monoidalFunctor incl)

    NDA : UCSetup (o ⊔ suc 0ℓ) (ℓ ⊔ e) e o ℓ e cs ℓs
    NDA = NA.regraded

    A⇒B : {A B : Obj} {a b : Grade} {f : A ⇒ ⌊ a ⌋ ⊗₀ B} {g : A ⇒ ⌊ b ⌋ ⊗₀ B}
        → NA.R._≤UC_ {X = a} {Y = b} f g → AbstractUC._≤UC_ (NDB ℰ) {X = a} {Y = b} f g
    A⇒B {a = a} {b} = NA.Preserves.unrestrict-≤UC (id , tt) identity² (λ c → c , Mor.≅.refl (MonoidalCategory.U 𝒢B))
                                                   {X = a} {Y = b}

    -- A simulator u ⊗ ⌈ ρ ⌉, up to Std(𝕄)'s U-kernel, is an A-emulation.
    relabel-≤UC : {A B : Obj} {a b : Grade} {f : A ⇒ ⌊ a ⌋ ⊗₀ B} {g : A ⇒ ⌊ b ⌋ ⊗₀ B}
                → (s : ⌊ b ⌋ ⇒ ⌊ a ⌋) → Relabels {b} {a} s
                → AbstractUC._≈ᵁ_ (StdUC.StdSetup monoidalCategory ℰ) f (s ⊗₁ id ∘ g)
                → NA.R._≤UC_ {X = a} {Y = b} f g
    relabel-≤UC {a = a} {b} s rs e = NA.R.dummy-complete {X = a} {Y = b}
      ((s , rs) , NA.≈ᵁ⇒≈ᵁ|ι {X = a}
                    (Regrade.≈ᵁ⇒≈ᵁ|ι (StdUC.StdSetup monoidalCategory ℰ) (StrongMonoidalFunctor.monoidalFunctor ιB)
                                     {X = a} e))
