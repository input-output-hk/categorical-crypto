{-# OPTIONS --safe --without-K #-}

-- The ε-contextual relation on families of morphisms, `_≈ctx[_]_` —
-- `UC.Quantitative.Contextual._≈ᵁᵠ[_]_` at every level — and the emulation
-- bound over it at a named simulator family and schedule, `_≤UC[_,_]_`, with
-- its composition laws at their error formulas (`seqError`, `composeError`).
-- Simulators are `Categories.LocallyGraded.Family` homs at `Poly⁺` schedules;
-- the compared morphisms carry no rate, and a morphism a law moves into a
-- context is asked for an `Image` certificate.  `_≤UC^ωᵉ_` hides the data and
-- classifies the schedule as negligible.  Design note:
-- `docs/quantitative-family.md`.

open import Categories.Category
open import Categories.Category.Instance.Rates
open import Categories.Category.Monoidal.Bundle
import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Category.Monoidal.Utilities as MonU
open import Categories.Functor.Monoidal.CurriedTensor
import Categories.Monad.Graded.FromMonad as FromMonad
import Categories.Morphism.Reasoning as MR

open import Categories.LocallyGraded
open import Categories.LocallyGraded.Family
open import Categories.LocallyGraded.Monoidal
open import Categories.LocallyGraded.SubCategory

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Positive
open import Data.Nat.Properties
open import Data.Product.Base
open import Data.Rational as ℚ using (ℚ; 0ℚ)
open import Level
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import CategoricalCrypto.Approx.Error
open import CategoricalCrypto.UC.Approximate

import Data.Rational.Properties as ℚₚ

module Rates = SymmetricMonoidalCategory Rates

module CategoricalCrypto.UC.Quantitative.Family
  {o ℓ e os ℓa qs : Level}
  (M : MonoidalCategory o ℓ e) (Rg : GradedSubCat Rates.monoidalCategory M qs)
  {Obs : Set os} (Ap : Approximation Obs ℚ-ordered ℓa)
  (𝟙 Ω : MonoidalCategory.Obj M)
  (⟦_⟧ : MonoidalCategory._⇒_ M 𝟙 Ω → Obs)
  (obs-resp : {u v : MonoidalCategory._⇒_ M 𝟙 Ω}
            → MonoidalCategory._≈_ M u v → Approximation._≈[_]_ Ap ⟦ u ⟧ 0ℚ ⟦ v ⟧)
  where

open import CategoricalCrypto.UC.Quantitative.Contextual M Rg Ap 𝟙 Ω ⟦_⟧ obs-resp

open MonoidalCategory M
open FromMonad (curriedTensor M)
open GradedSubCat Rg
open GradedMonoidal (monoidalᴸ Rates.braided) using () renaming (_⊗₁_ to _⊗ʰ_; α⇒ to α⇒ʰ; α⇐ to α⇐ʰ)
open MonR monoidal
open MonU.Shorthands monoidal
open MR U
open Families Rg ℕ (λ n → n) Poly⁺ poly⁺-1 (λ {s} {t} → poly⁺-· {s} {t})

private variable A A′ B C X Y Z P Q : ℕ → Obj

------------------------------------------------------------------------
-- The relation

Homᶠ : (A X B : ℕ → Obj) → Set ℓ
Homᶠ A X B = (n : ℕ) → A n ⇒ T₀ (X n) (B n)

infix 4 _≈ctx[_]_
infixr 9 _∙ᶠ_

_≈ctx[_]_ : Homᶠ A X B → (ℕ → ℕ → ℚ) → Homᶠ A X B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≈ctx[ ε ] g = (n : ℕ) → f n ≈ᵁᵠ[ ε n ] g n

≈C⇒≈ctx : {f g : Homᶠ A X B} → ((n : ℕ) → f n ≈ g n) → f ≈ctx[ (λ _ _ → 0ℚ) ] g
≈C⇒≈ctx e n = ctx-resp (λ _ → 0ℚ) Equiv.refl (e n) ctx-refl

≈ctx-resp : (ε : ℕ → ℕ → ℚ) {f f′ g g′ : Homᶠ A X B}
          → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
          → f ≈ctx[ ε ] g → f′ ≈ctx[ ε ] g′
≈ctx-resp ε ef eg h n = ctx-resp (ε n) (ef n) (eg n) (h n)

sim : Y ⇒^ω X → (n : ℕ) → Y n ⇒ X n
sim s n = ⌊ hom s n ⌋

subᶠ : Y ⇒^ω X → Homᶠ A Y B → Homᶠ A X B
subᶠ s g n = sub (sim s n) ∘ g n

_∙ᶠ_ : Homᶠ B P C → Homᶠ A X B → Homᶠ A (X ⊛ω P) C
_∙ᶠ_ {X = X} k f n = ext (X n) (k n) ∘ f n

------------------------------------------------------------------------
-- The three plugs, each a single-level absorption at every level

≈ctx-sub : (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A Y B} → f ≈ctx[ ε ] g
         → subᶠ s f ≈ctx[ (λ n q → ε n (scale q (schedOf s n))) ] subᶠ s g
≈ctx-sub s ε h n = ctx-sub (ε n) (schedOf s n) (hom s n , Equiv.refl) (h n)

≈ctx-ext : (k : Homᶠ B P C) (rk : ℕ → ℕ⁺) → ((n : ℕ) → Image forget (rk n) (k n))
         → (ε : ℕ → ℕ → ℚ) {f g : Homᶠ A X B} → f ≈ctx[ ε ] g
         → (k ∙ᶠ f) ≈ctx[ (λ n q → ε n (scale q (rk n))) ] (k ∙ᶠ g)
≈ctx-ext {X = X} k rk ck ε h n =
  ctx-absorb (ε n) (rk n) (λ W → id {W} ⊗₁ ext (X n) (k n)) (λ _ → cκ)
             (λ _ → split₂ʳ) (λ _ → split₂ʳ) (h n)
  where
  cκ : {W : Obj} → Image forget (rk n) (id {W} ⊗₁ ext (X n) (k n))
  cκ = L.sub[ ≤-reflexive (trans (*-identityˡ _) (trans (*-identityʳ _) (*-identityˡ _))) ]
         (L.id ⊗ʰ (α⇐ʰ L.∙ (L.id ⊗ʰ Tᵠ.certifiedᴴ (ck n))))
     , Equiv.refl

-- The earlier process goes into the closure, `W`'s context of `u ∙ f` being
-- `(W ⊗ X)`'s context of `u` along `id ⊗ α⇐ ∘ α⇒`.
≈ctx-pre : (f : Homᶠ A X B) (rf : ℕ → ℕ⁺) → ((n : ℕ) → Image forget (rf n) (f n))
         → (ε : ℕ → ℕ → ℚ) {u v : Homᶠ B P C} → u ≈ctx[ ε ] v
         → (u ∙ᶠ f) ≈ctx[ (λ n q → ε n (scale q (rf n))) ] (v ∙ᶠ f)
≈ctx-pre {X = X} {B = B} {P = P} {C = C} f rf cf ε {u} {v} h n =
  agree⇒ctx (λ q → ε n (scale q (rf n))) λ W →
    absorb-closureᵠ (ε n) (rf n) (cκ W) (cθ W) (λ _ → cut W (u n)) (λ _ → cut W (v n))
      (ctx⇒agree (ε n) (h n) (W ⊗₀ X n))
  where
  cκ : (W : Obj) → Image forget 1⁺ (id {W} ⊗₁ α⇐ {X n} {P n} {C n} ∘ α⇒)
  cκ W = L.sub[ ≤-refl ] ((L.id ⊗ʰ α⇐ʰ) L.∙ α⇒ʰ) , Equiv.refl

  cθ : (W : Obj) → Image forget (rf n) (α⇐ {W} {X n} {B n} ∘ id ⊗₁ f n)
  cθ W = L.sub[ ≤-reflexive (trans (*-identityʳ _) (*-identityˡ _)) ]
           (α⇐ʰ L.∙ (L.id ⊗ʰ Tᵠ.certifiedᴴ (cf n)))
       , Equiv.refl

  slide : (W : Obj) (x : B n ⇒ P n ⊗₀ C n)
        → α⇒ ∘ id {W ⊗₀ X n} ⊗₁ x ∘ α⇐ ≈ id ⊗₁ (id ⊗₁ x)
  slide W x = begin
    α⇒ ∘ id ⊗₁ x ∘ α⇐         ≈⟨ refl⟩∘⟨ (⟺ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    α⇒ ∘ (id ⊗₁ id) ⊗₁ x ∘ α⇐ ≈⟨ pullˡ assoc-commute-from ⟩
    (id ⊗₁ (id ⊗₁ x) ∘ α⇒) ∘ α⇐ ≈⟨ cancelʳ associator.isoʳ ⟩
    id ⊗₁ (id ⊗₁ x)           ∎

  cut : (W : Obj) (x : B n ⇒ P n ⊗₀ C n) {E : W ⊗₀ ((X n ⊗₀ P n) ⊗₀ C n) ⇒ Ω}
      → E ∘ id ⊗₁ (ext (X n) x ∘ f n)
      ≈ ((E ∘ id ⊗₁ α⇐ ∘ α⇒) ∘ id ⊗₁ x) ∘ α⇐ ∘ id ⊗₁ f n
  cut W x {E} = begin
    E ∘ id ⊗₁ (ext (X n) x ∘ f n)
      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ (⟺ (μT x) ⟩∘⟨refl) ⟩
    E ∘ id ⊗₁ ((α⇐ ∘ id ⊗₁ x) ∘ f n)
      ≈⟨ refl⟩∘⟨ (split₂ʳ ○ (split₂ʳ ⟩∘⟨refl)) ⟩
    E ∘ (id ⊗₁ α⇐ ∘ id ⊗₁ (id ⊗₁ x)) ∘ id ⊗₁ f n
      ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ slide W x) ⟩∘⟨refl ⟩
    E ∘ (id ⊗₁ α⇐ ∘ α⇒ ∘ id ⊗₁ x ∘ α⇐) ∘ id ⊗₁ f n
      ≈⟨ (refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ assoc) ○ (refl⟩∘⟨ refl⟩∘⟨ assoc))) ○ ⟺ (assoc ○ assoc ○ (refl⟩∘⟨ assoc)) ⟩
    ((E ∘ id ⊗₁ α⇐ ∘ α⇒) ∘ id ⊗₁ x) ∘ α⇐ ∘ id ⊗₁ f n ∎

------------------------------------------------------------------------
-- Bounds at a named simulator and schedule, and the witness

infix 4 _≤UC[_,_]_ _≤UC^ωᵉ_

_≤UC[_,_]_ : Homᶠ A X B → Y ⇒^ω X → (ℕ → ℕ → ℚ) → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
f ≤UC[ s , ε ] g = f ≈ctx[ ε ] subᶠ s g

_≤UC^ωᵉ_ : Homᶠ A X B → Homᶠ A Y B → Set (o ⊔ ℓ ⊔ e ⊔ ℓa ⊔ qs)
_≤UC^ωᵉ_ {X = X} {Y = Y} f g =
  Σ[ s ∈ Y ⇒^ω X ] Σ[ ε ∈ (ℕ → ℕ → ℚ) ] NegligibleBound ε × f ≤UC[ s , ε ] g

≤UC^ωᵉ-resp : {f f′ : Homᶠ A X B} {g g′ : Homᶠ A Y B}
            → ((n : ℕ) → f n ≈ f′ n) → ((n : ℕ) → g n ≈ g′ n)
            → f ≤UC^ωᵉ g → f′ ≤UC^ωᵉ g′
≤UC^ωᵉ-resp ef eg (s , ε , neg , e) = s , ε , neg , ≈ctx-resp ε ef (λ n → ∘-resp-≈ʳ (eg n)) e

------------------------------------------------------------------------
-- The composition laws

seqError : Y ⇒^ω X → (ℕ → ℕ → ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
seqError s ε δ n q = ε n q ℚ.+ δ n (scale q (schedOf s n))

seqError-negligible : (s : Y ⇒^ω X) (ε δ : ℕ → ℕ → ℚ) → NegligibleBound ε → NegligibleBound δ
                    → NegligibleBound (seqError s ε δ)
seqError-negligible s ε δ nε nδ =
  GradedBound-+[ Negligible ] Negligible-+ ε (λ n q → δ n (scale q (schedOf s n))) nε
    (NegligibleBound-scale (schedOf s) (schedOf-adm s) δ nδ)

≤UC[]-trans : (s : Y ⇒^ω X) (t : Z ⇒^ω Y) (ε δ : ℕ → ℕ → ℚ)
              {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
            → f ≤UC[ s , ε ] g → g ≤UC[ t , δ ] h → f ≤UC[ Fam [ s ∘ t ] , seqError s ε δ ] h
≤UC[]-trans s _ ε δ e₁ e₂ n =
  at-trans (ε n) (δ n) (schedOf s n) (hom s n , Equiv.refl) (e₁ n) (e₂ n)

≤UC^ωᵉ-trans : {f : Homᶠ A X B} {g : Homᶠ A Y B} {h : Homᶠ A Z B}
             → f ≤UC^ωᵉ g → g ≤UC^ωᵉ h → f ≤UC^ωᵉ h
≤UC^ωᵉ-trans (s , ε , nε , e₁) (t , δ , nδ , e₂) =
  Fam [ s ∘ t ] , seqError s ε δ , seqError-negligible s ε δ nε nδ , ≤UC[]-trans s t ε δ e₁ e₂

-- A process plugged under the DOMAIN at rate `1⁺` costs nothing.
≤UC[]-dom : (p : (n : ℕ) → A′ n ⇒ A n) → ((n : ℕ) → Image forget 1⁺ (p n))
          → (s : Y ⇒^ω X) (ε : ℕ → ℕ → ℚ) {f : Homᶠ A X B} {g : Homᶠ A Y B}
          → f ≤UC[ s , ε ] g → (λ n → f n ∘ p n) ≤UC[ s , ε ] (λ n → g n ∘ p n)
≤UC[]-dom p cp s ε e n =
  ctx-resp (ε n) Equiv.refl assoc
    (ctx-mono (λ q → ε n (scale q 1⁺)) (ε n) (λ q → ℚₚ.≤-reflexive (cong (ε n) (scale-unit q)))
      (agree⇒ctx (λ q → ε n (scale q 1⁺)) λ W →
        absorb-closureᵠ (ε n) 1⁺ (L.id , Equiv.refl)
          (L.sub[ ≤-refl ] (L.id {W} ⊗ʰ Tᵠ.certifiedᴴ (cp n)) , Equiv.refl)
          (λ _ → cut) (λ _ → cut) (ctx⇒agree (ε n) (e n) W)))
  where
  cut : {W D : Obj} {x : _ ⇒ D} {E : W ⊗₀ D ⇒ Ω}
      → E ∘ id ⊗₁ (x ∘ p n) ≈ ((E ∘ id) ∘ id ⊗₁ x) ∘ id ⊗₁ p n
  cut = (refl⟩∘⟨ split₂ʳ) ○ sym-assoc ○ ((⟺ identityʳ ⟩∘⟨refl) ⟩∘⟨refl)

composeError : (rf rtv : ℕ → ℕ⁺) → (ℕ → ℕ → ℚ) → (ℕ → ℕ → ℚ) → ℕ → ℕ → ℚ
composeError rf rtv εf εu n q = εu n (scale q (rf n)) ℚ.+ εf n (scale q (rtv n))

composeError-negligible : (rf rtv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ) → Poly⁺ rf → Poly⁺ rtv
                        → NegligibleBound εf → NegligibleBound εu
                        → NegligibleBound (composeError rf rtv εf εu)
composeError-negligible rf rtv εf εu Prf Prtv nf nu =
  GradedBound-+[ Negligible ] Negligible-+
    (λ n q → εu n (scale q (rf n))) (λ n q → εf n (scale q (rtv n)))
    (NegligibleBound-scale rf Prf εu nu) (NegligibleBound-scale rtv Prtv εf nf)

-- The simulator of `u ∙ f` is the tensor of the two, `Famᴹ`'s own.
≤UC[]-compose :
    {f : Homᶠ A X B} {g : Homᶠ A Y B} {u : Homᶠ B P C} {v : Homᶠ B Q C}
    (sf : Y ⇒^ω X) (t : Q ⇒^ω P) (rf rv : ℕ → ℕ⁺) (εf εu : ℕ → ℕ → ℚ)
  → ((n : ℕ) → Image forget (rf n) (f n)) → ((n : ℕ) → Image forget (rv n) (v n))
  → f ≤UC[ sf , εf ] g → u ≤UC[ t , εu ] v
  → (u ∙ᶠ f) ≤UC[ sf ⊗^ω t , composeError rf (λ n → rv n · schedOf t n) εf εu ] (v ∙ᶠ g)
≤UC[]-compose {X = X} {Y = Y} {C = C} {f = f} {g} {v = v} sf t rf rv εf εu cf cv ef eu n =
  ctx-trans (λ q → εu n (scale q (rf n))) (λ q → εf n (scale q (rtv n)))
    (≈ctx-pre f rf cf εu eu n)
    (ctx-resp (λ q → εf n (scale q (rtv n))) Equiv.refl strict-final
              (≈ctx-ext (subᶠ t v) rtv ctv εf ef n))
  where
  rtv : ℕ → ℕ⁺
  rtv m = rv m · schedOf t m

  ctv : (m : ℕ) → Image forget (rtv m) (subᶠ t v m)
  ctv m = L.sub[ ≤-reflexive (cong (value (rv m) ℕ.*_) (*-identityʳ _)) ]
            ((hom t m ⊗ʰ L.id {C m}) L.∙ Tᵠ.certifiedᴴ (cv m))
        , Equiv.refl

  s₁ = sim sf n
  t₁ = sim t n

  strict-final : ext (X n) (sub t₁ ∘ v n) ∘ sub s₁ ∘ g n ≈ sub (s₁ ⊗₁ t₁) ∘ ext (Y n) (v n) ∘ g n
  strict-final = begin
    ext (X n) (sub t₁ ∘ v n) ∘ sub s₁ ∘ g n              ≈⟨ sub-commute₂ ⟩∘⟨refl ⟩
    (sub (id ⊗₁ t₁) ∘ ext (X n) (v n)) ∘ sub s₁ ∘ g n    ≈⟨ assoc ○ (refl⟩∘⟨ sym-assoc) ⟩
    sub (id ⊗₁ t₁) ∘ (ext (X n) (v n) ∘ sub s₁) ∘ g n    ≈⟨ refl⟩∘⟨ (sub-commute₁ ⟩∘⟨refl) ⟩
    sub (id ⊗₁ t₁) ∘ (sub (s₁ ⊗₁ id) ∘ ext (Y n) (v n)) ∘ g n
      ≈⟨ (refl⟩∘⟨ assoc) ○ sym-assoc ⟩
    (sub (id ⊗₁ t₁) ∘ sub (s₁ ⊗₁ id)) ∘ ext (Y n) (v n) ∘ g n
      ≈⟨ (⟺ sub-homomorphism ○ sub-resp-≈ (⟺ serialize₂₁)) ⟩∘⟨refl ⟩
    sub (s₁ ⊗₁ t₁) ∘ ext (Y n) (v n) ∘ g n               ∎
