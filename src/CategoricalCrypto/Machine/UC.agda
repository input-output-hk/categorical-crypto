{-# OPTIONS --safe #-}

-- ============================================================================
-- The locally graded UC layer (`CategoricalCrypto.Abstract2`) run at the
-- concrete machines: 𝒞 = ℐ = the symmetric monoidal category of machines
-- under bisimulation, ℳ = the curried tensor, and ℰ = joint ancilla tests.
--
-- A test on a channel `A` is a pair `(Y , E)` of an ancilla channel `Y` and an
-- environment `E : Machine (A ⊗₀ Y) ℰ-Out`; a morphism `f : Machine B A` acts
-- by `E ↦ E ∘ (f ⊗₁ id {Y})`, and two tests are equal when they share the
-- ancilla and their environments are bisimilar.  The representable presheaf
-- `Hom[-, ℰ-Out ]` (no ancilla) is too small for `GradeStable`: a test on
-- `B ⊗₀ Y` with `Y` dangling is not a test on `B`.  With the ancilla the
-- quantifier absorbs the bypass wire, so `grade-stable` below is
-- hypothesis-free and, through `bridge`, the bare kernel `_≈ℰ_` coincides with
-- the compositional `_≈ᵁ_` (`≈ᵁ⇔≈ℰ`).  Taking the trivial ancilla `I` shows
-- that `_≈ℰ_` refines the environment equivalence `_≅ℰ_` of `Machine.Iso`
-- (`≈ℰ⇒≅ℰ`); the converse is not claimed.
-- ============================================================================

module CategoricalCrypto.Machine.UC where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.Bundles using (Setoid)
import Level

open import Categories.Category using (Category)
open import Categories.Category.Monoidal.Construction.Reverse using (Reverse-MonoidalCategory)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory)
open import Categories.Functor.Presheaf using (Presheaf)
import Categories.Functor.Monoidal.CurriedTensor.Properties as CurriedTensorProperties
import Categories.Morphism.Reasoning as MR

open import CategoricalCrypto.Channel.Core
-- `Machine.Core`'s own UC notions, and its copies of the categorical
-- operations, are shadowed by the abstract ones that `StdUC` brings in; the
-- two agree definitionally.
open import CategoricalCrypto.Machine.Core
  hiding (id; _∘_; ℰ; map-ℰ)
import CategoricalCrypto.Machine.Core as CC
open import CategoricalCrypto.Machine.Iso
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Monoidal
  using (⊗₁-id; ⊗₁-interchange; ρ⇒-natural; ρ-isoʳ; α-isoˡ)
open import CategoricalCrypto.Machine.MonoidalCategory
open import CategoricalCrypto.Standard2

open Category.HomReasoning MachineCategory
open MR MachineCategory

private
  module M = Monoidal machine-monoidal

-- ----------------------------------------------------------------------------
-- The environments: joint ancilla tests, compared up to `_≅ᴹ_`.  The ancilla
-- sits on the RIGHT, matching the reversed grade `T₁ Y h = h ⊗₁ id` below.
-- ----------------------------------------------------------------------------

Test : Channel → Type₁
Test A = Σ[ Y ∈ Channel ] Machine (A ⊗₀ Y) ℰ-Out

data SameTest {A : Channel} : Test A → Test A → Type₁ where
  same : ∀ {Y} {E₁ E₂ : Machine (A ⊗₀ Y) ℰ-Out}
       → E₁ ≅ᴹ E₂ → SameTest (Y , E₁) (Y , E₂)

-- The machine layer is `--safe` with K, so `same` inverts.
same⁻¹ : ∀ {A Y} {E₁ E₂ : Machine (A ⊗₀ Y) ℰ-Out}
       → SameTest (Y , E₁) (Y , E₂) → E₁ ≅ᴹ E₂
same⁻¹ (same e) = e

Test-setoid : Channel → Setoid (Level.suc 0ℓ) (Level.suc 0ℓ)
Test-setoid A = record
  { Carrier       = Test A
  ; _≈_           = SameTest
  ; isEquivalence = record
      { refl  = same ≅ᴹ-refl
      ; sym   = λ { (same e) → same (≅ᴹ-sym e) }
      ; trans = λ { (same e₁) (same e₂) → same (≅ᴹ-trans e₁ e₂) }
      }
  }

test-map : ∀ {A B} → Machine B A → Test A → Test B
test-map f t = proj₁ t , proj₂ t CC.∘ (f ⊗₁ CC.id)

test-map-cong : ∀ {A B} (f : Machine B A) {t t' : Test A}
              → SameTest t t' → SameTest (test-map f t) (test-map f t')
test-map-cong f (same e) = same (e ⟩∘⟨refl)

ℰ-tests : Presheaf MachineCategory (Setoids (Level.suc 0ℓ) (Level.suc 0ℓ))
ℰ-tests = record
  { F₀           = Test-setoid
  ; F₁           = λ f → record { to = test-map f ; cong = test-map-cong f }
  ; identity     = same (elimʳ ⊗₁-id)
  ; homomorphism = λ {_} {_} {_} {f} {g} → same (begin
      _ CC.∘ ((f CC.∘ g) ⊗₁ CC.id)
        ≈⟨ refl⟩∘⟨ ⊗₁-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-identityˡ-≅ᴹ) ⟩
      _ CC.∘ ((f CC.∘ g) ⊗₁ (CC.id CC.∘ CC.id))
        ≈⟨ refl⟩∘⟨ ⊗₁-interchange g f CC.id CC.id ⟩
      _ CC.∘ ((f ⊗₁ CC.id) CC.∘ (g ⊗₁ CC.id))
        ≈⟨ ≅ᴹ-sym ∘-assoc-≅ᴹ ⟩
      (_ CC.∘ (f ⊗₁ CC.id)) CC.∘ (g ⊗₁ CC.id) ∎)
  ; F-resp-≈     = λ e → same (refl⟩∘⟨ ⊗₁-resp-≅ᴹ e ≅ᴹ-refl)
  }

-- The tensor is REVERSED so that the grade sits on the right, as in
-- `Machine.Core`: `T₀ X B = B ⊗₀ X`, `sub c = id ⊗₁ c`, `T₁ Y h = h ⊗₁ id`.
machines : MonoidalCategory _ _ _
machines = Reverse-MonoidalCategory machine-monoidal-category

-- Machine types below use `Channel.Core`'s tensor; the reversed monoidal one
-- is hidden so that `B ⊗₀ X` reads as it does in `Machine.Core`.
open StdUC machines ℰ-tests public hiding (_⊗₀_; _⊗₁_)

-- ----------------------------------------------------------------------------
-- The kernel congruence, unfolded: `f ≈ℰ g` says exactly that every test
-- with every ancilla agrees on `f` and `g`.
-- ----------------------------------------------------------------------------

≈ℰ⇒tests : ∀ {A B} {f g : Machine A B} → f ≈ℰ g
         → ∀ Y (E : Machine (B ⊗₀ Y) ℰ-Out)
         → (E ∘ (f ⊗₁ id {Y})) ≅ᴹ (E ∘ (g ⊗₁ id {Y}))
≈ℰ⇒tests e Y E = same⁻¹ (KE.run∼ e {Y , E})

tests⇒≈ℰ : ∀ {A B} {f g : Machine A B}
         → (∀ Y (E : Machine (B ⊗₀ Y) ℰ-Out) → (E ∘ (f ⊗₁ id {Y})) ≅ᴹ (E ∘ (g ⊗₁ id {Y})))
         → f ≈ℰ g
tests⇒≈ℰ e = KE.mk∼ λ {t} → same (e (proj₁ t) (proj₂ t))

-- The trivial ancilla `I` recovers `Machine.Iso`'s environment equivalence.
≈ℰ⇒≅ℰ : ∀ {A B} {f g : Machine A B} → f ≈ℰ g → f ≅ℰ g
≈ℰ⇒≅ℰ {f = f} {g} e E = begin
    E ∘ f                                    ≈⟨ insertʳ ρ-isoʳ ⟩
    ((E ∘ f) ∘ CC.ρ⇒) ∘ CC.ρ⇐                ≈⟨ slide f ⟩∘⟨refl ⟩
    ((E ∘ CC.ρ⇒) ∘ (f ⊗₁ id)) ∘ CC.ρ⇐        ≈⟨ ≈ℰ⇒tests e I (E ∘ CC.ρ⇒) ⟩∘⟨refl ⟩
    ((E ∘ CC.ρ⇒) ∘ (g ⊗₁ id)) ∘ CC.ρ⇐        ≈⟨ ⟺ (slide g) ⟩∘⟨refl ⟩
    ((E ∘ g) ∘ CC.ρ⇒) ∘ CC.ρ⇐                ≈⟨ cancelʳ ρ-isoʳ ⟩
    E ∘ g                                    ∎
  where
  slide : ∀ k → (E ∘ k) ∘ CC.ρ⇒ ≅ᴹ (E ∘ CC.ρ⇒) ∘ (k ⊗₁ id {I})
  slide k = pullʳ (⟺ (ρ⇒-natural k)) ○ sym-assoc

-- ----------------------------------------------------------------------------
-- Grade stability.  The functorial action `T₁ Z h` of the curried tensor is
-- `h ⊗₁ id` up to bisimulation (not definitionally: `T₁` is built from `ext`,
-- `sub` and `return`), and a test `(Y , E)` on `B ⊗₀ Z` regroups into the
-- test `(Z ⊗₀ Y , E ∘ α⇐)` on `B`.
-- ----------------------------------------------------------------------------

open CurriedTensorProperties machines using (T₁-⊗)

T₁-⊗ʳ : ∀ Z {A B} (h : Machine A B) → T₁ Z h ≅ᴹ (h ⊗₁ id {Z})
T₁-⊗ʳ = T₁-⊗

private
  regroup : ∀ {A B Z Y} (k : Machine A B) (E : Machine ((B ⊗₀ Z) ⊗₀ Y) ℰ-Out)
          → (E ∘ ((k ⊗₁ id {Z}) ⊗₁ id {Y}))
            ≅ᴹ (((E ∘ ⊗-assoc⃖ {B} {Z} {Y}) ∘ (k ⊗₁ id {Z ⊗₀ Y})) ∘ ⊗-assoc {A} {Z} {Y})
  regroup {A} {B} {Z} {Y} k E = begin
      E ∘ ((k ⊗₁ id) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ introˡ (α-isoˡ {B} {Z} {Y}) ⟩
      E ∘ ((⊗-assoc⃖ ∘ ⊗-assoc) ∘ ((k ⊗₁ id) ⊗₁ id))
        ≈⟨ refl⟩∘⟨ pullʳ M.assoc-commute-from ⟩
      E ∘ (⊗-assoc⃖ ∘ ((k ⊗₁ (id ⊗₁ id)) ∘ ⊗-assoc))
        ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ (⊗₁-resp-≅ᴹ ≅ᴹ-refl ⊗₁-id ⟩∘⟨refl)) ⟩
      E ∘ (⊗-assoc⃖ ∘ ((k ⊗₁ id) ∘ ⊗-assoc))
        ≈⟨ sym-assoc ○ sym-assoc ⟩
      ((E ∘ ⊗-assoc⃖) ∘ (k ⊗₁ id)) ∘ ⊗-assoc ∎

grade-stable : GradeStable
grade-stable Z {h} {h′} e = tests⇒≈ℰ λ Y E → begin
    E ∘ (T₁ Z h ⊗₁ id)                          ≈⟨ refl⟩∘⟨ ⊗₁-resp-≅ᴹ (T₁-⊗ʳ Z h) ≅ᴹ-refl ⟩
    E ∘ ((h ⊗₁ id) ⊗₁ id)                       ≈⟨ regroup h E ⟩
    ((E ∘ ⊗-assoc⃖) ∘ (h ⊗₁ id)) ∘ ⊗-assoc      ≈⟨ ≈ℰ⇒tests e (Z ⊗₀ Y) (E ∘ ⊗-assoc⃖) ⟩∘⟨refl ⟩
    ((E ∘ ⊗-assoc⃖) ∘ (h′ ⊗₁ id)) ∘ ⊗-assoc     ≈⟨ ⟺ (regroup h′ E) ⟩
    E ∘ ((h′ ⊗₁ id) ⊗₁ id)                      ≈⟨ refl⟩∘⟨ ⊗₁-resp-≅ᴹ (≅ᴹ-sym (T₁-⊗ʳ Z h′)) ≅ᴹ-refl ⟩
    E ∘ (T₁ Z h′ ⊗₁ id)                         ∎

-- The bare kernel and the compositional U-kernel coincide.
≈ᵁ⇔≈ℰ : ∀ {A B X} {f g : Machine A (B ⊗₀ X)} → f ≈ᵁ g ⇔ f ≈ℰ g
≈ᵁ⇔≈ℰ {f = f} {g} = mk⇔ {B = f ≈ℰ g} ≈ᵁ⇒≈ℰ (bridge grade-stable)

-- ----------------------------------------------------------------------------
-- Sanity checks: the abstract notions land on plain machine types.  A protocol
-- with adversary interface `X` is a `Machine A (B ⊗₀ X)`, an adversary is a
-- machine `X ⇒ X′`, and the four metatheorems apply verbatim.
-- ----------------------------------------------------------------------------

private
  _ : ∀ {A B X} (f : Machine A (B ⊗₀ X)) → f ≤UC f
  _ = ≤UC-refl

  _ : ∀ {A B X Y Z} {f : Machine A (B ⊗₀ X)} {g : Machine A (B ⊗₀ Y)} {h : Machine A (B ⊗₀ Z)}
    → f ≤UC g → g ≤UC h → f ≤UC h
  _ = ≤UC-trans

  _ : ∀ {A B X Y} {f : Machine A (B ⊗₀ X)} {g : Machine A (B ⊗₀ Y)}
    → (∃[ s ] (f ≈ᵁ (sub s ∘ g))) → f ≤UC g
  _ = dummy-complete
