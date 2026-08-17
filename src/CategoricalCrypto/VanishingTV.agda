{-# OPTIONS --safe --without-K #-}

-- The vanishing-TV layer over 𝒞^ω. Observation sequences are identified
-- (_∼ᵛ_) when their advantage vanishes asymptotically.  The environment
-- presheaf ℰᵗᵛ sends A to joint ancilla-tests (Y , E : Y ⊗ A ⇒ Δ Ω).
-- The kernel congruence of ℰᵗᵛ is exactly the adaptive single-environment
-- relation R (≈ℰ⇒R / R⇒≈ℰ), which is grade-stable by its own ancilla
-- quantifier.

open import Level

open import CategoricalCrypto.MachineAxioms

module CategoricalCrypto.VanishingTV
  {o ℓ e os ℓs qs : Level} (MA : MachineAxioms o ℓ e os ℓs qs) where

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Poly
import Data.Nat.Properties as ℕₚ
open import Data.Product
open import Data.Rational as ℚ using (ℚ; 0ℚ; ½)
open import Data.Rational.Properties
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonoidalR
import Categories.Category.Monoidal.Utilities as MonoidalUtilities
open import Categories.Functor.Presheaf
import Categories.KernelCongruence as KernelCong
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.FamilyCategory MA

open MachineAxioms MA
open MonoidalUtilities.Shorthands 𝕄.monoidal

module 𝒞ω = MonoidalCategory 𝒞^ω
private module Sω = MonoidalUtilities.Shorthands monoidal^ω

private variable
  A B Y : Obj^ω
  μ ν ρ : ℕ → Obs.Carrier

------------------------------------------------------------------------
-- Observation sequences and vanishing advantage
------------------------------------------------------------------------

run : 𝟙^ω ⇒^ω Δ Ω → ℕ → Obs.Carrier
run u n = ⟦ proj₁ u n ⟧

infix 4 _∼ᵛ_ _→0

_∼ᵛ_ : (μ ν : ℕ → Obs.Carrier) → Set
μ ∼ᵛ ν = ∀ ε → ε ℚ.> 0ℚ → Σ[ N ∈ ℕ ] ∀ n → N ℕ.≤ n → adv (μ n) (ν n) ℚ.≤ ε

_→0 : (ℕ → ℚ) → Set
s →0 = ∀ ε → ε ℚ.> 0ℚ → Σ[ N ∈ ℕ ] ∀ n → N ℕ.≤ n → s n ℚ.≤ ε

∼ᵛ-pointwise : (∀ n → μ n Obs.≈ ν n) → μ ∼ᵛ ν
∼ᵛ-pointwise h ε ε>0 = 0 , λ n _ → subst (ℚ._≤ ε) (sym (adv-≈⇒0 (h n))) (<⇒≤ ε>0)

∼ᵛ-refl : μ ∼ᵛ μ
∼ᵛ-refl = ∼ᵛ-pointwise λ _ → Obs.refl

∼ᵛ-sym : μ ∼ᵛ ν → ν ∼ᵛ μ
∼ᵛ-sym {μ} {ν} h ε ε>0 = let (N , b) = h ε ε>0 in
  N , λ n N≤n → subst (ℚ._≤ ε) (adv-sym (μ n) (ν n)) (b n N≤n)

private
  half-pos : {ε : ℚ} → ε ℚ.> 0ℚ → 0ℚ ℚ.< ½ ℚ.* ε
  half-pos {ε} ε>0 = subst (ℚ._< ½ ℚ.* ε) (*-zeroʳ ½) (*-monoʳ-<-pos ½ ε>0)

  half+half : ∀ ε → ½ ℚ.* ε ℚ.+ ½ ℚ.* ε ≡ ε
  half+half ε = trans (sym (*-distribʳ-+ ε ½ ½)) (*-identityˡ ε)

∼ᵛ-trans : μ ∼ᵛ ν → ν ∼ᵛ ρ → μ ∼ᵛ ρ
∼ᵛ-trans {μ} {ν} {ρ} h₁ h₂ ε ε>0 =
  let (N₁ , b₁) = h₁ (½ ℚ.* ε) (half-pos ε>0)
      (N₂ , b₂) = h₂ (½ ℚ.* ε) (half-pos ε>0)
  in N₁ ℕ.⊔ N₂ , λ n le → subst (λ q → adv (μ n) (ρ n) ℚ.≤ q) (half+half ε)
       (≤-trans (adv-triangle (μ n) (ν n) (ρ n))
                (+-mono-≤ (b₁ n (ℕₚ.≤-trans (ℕₚ.m≤m⊔n N₁ N₂) le))
                          (b₂ n (ℕₚ.≤-trans (ℕₚ.m≤n⊔m N₁ N₂) le))))

∼ᵛ-setoid : Setoid os 0ℓ
∼ᵛ-setoid = record { Carrier = ℕ → Obs.Carrier ; _≈_ = _∼ᵛ_
  ; isEquivalence = record { refl = ∼ᵛ-refl ; sym = ∼ᵛ-sym ; trans = ∼ᵛ-trans } }

∼ᵛ-resp : {u u′ v v′ : ∀ n → 𝕄.unit 𝕄.⇒ Ω}
       → (∀ n → u n 𝕄.≈ u′ n) → (∀ n → v n 𝕄.≈ v′ n)
       → (λ n → ⟦ u n ⟧) ∼ᵛ (λ n → ⟦ v n ⟧) → (λ n → ⟦ u′ n ⟧) ∼ᵛ (λ n → ⟦ v′ n ⟧)
∼ᵛ-resp eu ev huv = ∼ᵛ-trans (∼ᵛ-pointwise λ n → Obs.sym (⟦⟧-resp-≈ (eu n)))
                   (∼ᵛ-trans huv (∼ᵛ-pointwise λ n → ⟦⟧-resp-≈ (ev n)))

------------------------------------------------------------------------
-- ℰᵗᵛ: joint ancilla-tests up to vanishing advantage under all closures
------------------------------------------------------------------------

TVTest : Obj^ω → Set (o ⊔ ℓ ⊔ qs)
TVTest A = Σ[ Y ∈ Obj^ω ] Test^ω (Y 𝒞ω.⊗₀ A)

-- Tests agree iff running them on every closure gives vanishing advantage.
data SameTV (A : Obj^ω) : TVTest A → TVTest A → Set (o ⊔ ℓ ⊔ qs) where
  same : {Y : Obj^ω} {E₁ E₂ : Test^ω (Y 𝒞ω.⊗₀ A)}
       → (∀ (m : Closure^ω (Y 𝒞ω.⊗₀ A)) → run (E₁ 𝒞ω.∘ m) ∼ᵛ run (E₂ 𝒞ω.∘ m))
       → SameTV A (Y , E₁) (Y , E₂)

same-≈ : {E₁ E₂ : Test^ω (Y 𝒞ω.⊗₀ A)} → E₁ ≈^ω E₂ → SameTV A (Y , E₁) (Y , E₂)
same-≈ eq = same λ _ → ∼ᵛ-pointwise λ n → ⟦⟧-resp-≈ (𝕄.∘-resp-≈ˡ (eq n))

substCl : {Y Z : Obj^ω} → Y ≡ Z → Closure^ω (Y 𝒞ω.⊗₀ A) → Closure^ω (Z 𝒞ω.⊗₀ A)
substCl {A = A} p = subst (λ W → Closure^ω (W 𝒞ω.⊗₀ A)) p

SameTV-Σ : {x y : TVTest A} → SameTV A x y
  → Σ[ p ∈ proj₁ x ≡ proj₁ y ] (∀ m → run (proj₂ x 𝒞ω.∘ m) ∼ᵛ run (proj₂ y 𝒞ω.∘ substCl p m))
SameTV-Σ (same h) = refl , h

ℰᵗᵛ₀ : Obj^ω → Setoid (o ⊔ ℓ ⊔ qs) (o ⊔ ℓ ⊔ qs)
ℰᵗᵛ₀ A = record { Carrier = TVTest A ; _≈_ = SameTV A ; isEquivalence = record
  { refl  = same λ _ → ∼ᵛ-refl
  ; sym   = λ { (same h) → same λ m → ∼ᵛ-sym (h m) }
  ; trans = λ { (same h₁) (same h₂) → same λ m → ∼ᵛ-trans (h₁ m) (h₂ m) } } }

tv₁ : A ⇒^ω B → TVTest B → TVTest A
tv₁ f (Y , E) = Y , E 𝒞ω.∘ (𝒞ω.id 𝒞ω.⊗₁ f)

tv₁-cong : (f : A ⇒^ω B) {x y : TVTest B} → SameTV B x y → SameTV A (tv₁ f x) (tv₁ f y)
tv₁-cong f (same h) = same λ m →
  ∼ᵛ-resp (λ _ → 𝕄.sym-assoc) (λ _ → 𝕄.sym-assoc) (h ((𝒞ω.id 𝒞ω.⊗₁ f) 𝒞ω.∘ m))

ℰᵗᵛ : Presheaf Fam (Setoids (o ⊔ ℓ ⊔ qs) (o ⊔ ℓ ⊔ qs))
ℰᵗᵛ = record
  { F₀           = ℰᵗᵛ₀
  ; F₁           = λ f → record { to = tv₁ f ; cong = tv₁-cong f }
  ; identity     = same-≈ λ _ → elimʳ 𝕄.⊗.identity
  ; homomorphism = same-≈ λ _ → 𝕄.∘-resp-≈ʳ split₂ʳ ○ 𝕄.sym-assoc
  ; F-resp-≈     = λ f≈g → same-≈ λ n → 𝕄.∘-resp-≈ʳ (𝕄.⊗.F-resp-≈ (𝕄.Equiv.refl , f≈g n))
  }
  where
  open MR 𝕄.U
  open MonoidalR 𝕄.monoidal

------------------------------------------------------------------------
-- The kernel congruence is the adaptive single-environment relation R
------------------------------------------------------------------------

module KE = KernelCong 𝒞ω.op (Setoids (o ⊔ ℓ ⊔ qs) (o ⊔ ℓ ⊔ qs)) ℰᵗᵛ

open KE public using () renaming (_∼_ to _≈ℰ_)

R : (f g : A ⇒^ω B) → Set (o ⊔ ℓ ⊔ qs)
R {A = A} {B = B} f g =
  ∀ (Y : Obj^ω) (E′ : Test^ω (Y 𝒞ω.⊗₀ B)) (m : Closure^ω (Y 𝒞ω.⊗₀ A))
  → run (E′ 𝒞ω.∘ ((𝒞ω.id 𝒞ω.⊗₁ f) 𝒞ω.∘ m)) ∼ᵛ run (E′ 𝒞ω.∘ ((𝒞ω.id 𝒞ω.⊗₁ g) 𝒞ω.∘ m))

R⇒≈ℰ : {f g : A ⇒^ω B} → R f g → f ≈ℰ g
R⇒≈ℰ r = KE.mk∼ λ {x} → same λ m →
  ∼ᵛ-resp (λ _ → 𝕄.sym-assoc) (λ _ → 𝕄.sym-assoc) (r (proj₁ x) (proj₂ x) m)

private
  conj𝕄 : ∀ {w y a b} (E : (w 𝕄.⊗₀ (y 𝕄.⊗₀ b)) 𝕄.⇒ Ω) (K : a 𝕄.⇒ b)
            (M : 𝕄.unit 𝕄.⇒ (w 𝕄.⊗₀ (y 𝕄.⊗₀ a)))
        → ((E 𝕄.∘ α⇒) 𝕄.∘ ((𝕄.id 𝕄.⊗₁ K) 𝕄.∘ (α⇐ 𝕄.∘ M)))
            𝕄.≈ (E 𝕄.∘ ((𝕄.id 𝕄.⊗₁ (𝕄.id 𝕄.⊗₁ K)) 𝕄.∘ M))
  conj𝕄 E K M = center α-nat ○ (refl⟩∘⟨ cancelInner associator.isoʳ)
    where
    open 𝕄
    open MonoidalR monoidal
    open MR U
    α-nat = (refl⟩∘⟨ (⟺ ⊗.identity) ⟩⊗⟨refl) ○ assoc-commute-from

module _ (hom-triv : HomTransportTrivial) where
  private
    substCl-level : {Y Z : Obj^ω} (p : Y ≡ Z) (m : Closure^ω (Y 𝒞ω.⊗₀ A)) (n : ℕ)
                  → proj₁ (substCl p m) n
                    ≡ subst (𝕄.unit 𝕄.⇒_) (cong (λ W → W n 𝕄.⊗₀ A n) p) (proj₁ m n)
    substCl-level refl _ _ = refl

    substCl-loop : (p : Y ≡ Y) (m : Closure^ω (Y 𝒞ω.⊗₀ A)) → substCl p m ≈^ω m
    substCl-loop {Y = Y} {A = A} p m n =
      𝕄.Equiv.trans (𝕄.Equiv.reflexive (substCl-level p m n))
                    (hom-triv (cong (λ W → W n 𝕄.⊗₀ A n) p) (proj₁ m n))

  ≈ℰ⇒R : {f g : A ⇒^ω B} → f ≈ℰ g → R f g
  ≈ℰ⇒R e Y E′ m =
    let (p , s) = SameTV-Σ (KE.run∼ e {Y , E′})
    in ∼ᵛ-resp (λ _ → 𝕄.assoc)
              (λ n → 𝕄.Equiv.trans (𝕄.∘-resp-≈ʳ (substCl-loop p m n)) 𝕄.assoc)
              (s m)

  -- Grade stability: the ancilla quantifier absorbs the bypass wire.
  grade-stable : ∀ Y {h h′ : A ⇒^ω B} → h ≈ℰ h′ → 𝒞ω.id {Y} 𝒞ω.⊗₁ h ≈ℰ 𝒞ω.id {Y} 𝒞ω.⊗₁ h′
  grade-stable Y {h} {h′} e = R⇒≈ℰ stable
    where
    stable : R (𝒞ω.id {Y} 𝒞ω.⊗₁ h) (𝒞ω.id {Y} 𝒞ω.⊗₁ h′)
    stable W E′ m =
      ∼ᵛ-resp (λ n → conj𝕄 (proj₁ E′ n) (proj₁ h n) (proj₁ m n))
             (λ n → conj𝕄 (proj₁ E′ n) (proj₁ h′ n) (proj₁ m n))
             (≈ℰ⇒R e (W 𝒞ω.⊗₀ Y) (E′ 𝒞ω.∘ Sω.α⇒) (Sω.α⇐ 𝒞ω.∘ m))

------------------------------------------------------------------------
-- Ingestion: per-level advantage bounds with a polynomial query budget
------------------------------------------------------------------------

infix 4 _≈ℰ[_]_

-- `R` with the vanishing-advantage conclusion replaced by an explicit bound,
-- whose query budget `p` must be polynomial
_≈ℰ[_]_ : A ⇒^ω B → (ℕ → ℕ → ℚ) → A ⇒^ω B → Set (o ⊔ ℓ ⊔ qs)
_≈ℰ[_]_ {A = A} {B = B} f ε g =
  ∀ (Y : Obj^ω) (E′ : Test^ω (Y 𝒞ω.⊗₀ B)) (m : Closure^ω (Y 𝒞ω.⊗₀ A))
  → Σ[ p ∈ (ℕ → ℕ) ] Poly p ×
    (∀ n → adv (run (E′ 𝒞ω.∘ ((𝒞ω.id 𝒞ω.⊗₁ f) 𝒞ω.∘ m)) n)
               (run (E′ 𝒞ω.∘ ((𝒞ω.id 𝒞ω.⊗₁ g) 𝒞ω.∘ m)) n) ℚ.≤ ε n (p n))

VanishingBound : (ℕ → ℕ → ℚ) → Set
VanishingBound ε = ∀ p → Poly p → (λ n → ε n (p n)) →0

absorb : {f g : A ⇒^ω B} {ε : ℕ → ℕ → ℚ} → f ≈ℰ[ ε ] g → VanishingBound ε → f ≈ℰ g
absorb {f = f} {g} bnd van = R⇒≈ℰ lem
  where
  lem : R f g
  lem Y E′ m ε ε>0 =
    let (p , Pp , hp) = bnd Y E′ m
        (N , hN) = van p Pp ε ε>0
    in N , λ n N≤n → ≤-trans (hp n) (hN n N≤n)
