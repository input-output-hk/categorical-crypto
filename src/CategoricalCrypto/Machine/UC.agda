{-# OPTIONS --safe #-}

-- ============================================================================
-- `Standard2.StdUC` run at the concrete machines: 𝒞 = ℐ = the symmetric
-- monoidal category of machines under `_≅ᴹ_`, ℳ = the curried tensor,
-- ℰ = joint ancilla tests.
--
-- `_≈ℰ_` identifies `f` and `g` when every ancilla test yields *isomorphic*
-- composites.  That is strictly finer than indistinguishability, because
-- `_≅ᴹ_` entails a bijection of state spaces; so `_≤UC_` here is a stronger
-- claim than standard UC emulation, and a failure of it is not a
-- distinguishing attack.
--
-- The representable presheaf `Hom[-, ℰ-Out ]`, with no ancilla, does not
-- appear to support `GradeStable`: a test on `B ⊗₀ Y` with `Y` dangling is
-- not a test on `B`.  With the ancilla the quantifier absorbs the bypass
-- wire, `grade-stable` is hypothesis-free, and through `bridge` `_≈ℰ_`
-- coincides with `_≈ᵁ_`.  Taking the trivial ancilla `I` shows `_≈ℰ_`
-- refines `_≅ℰ_`; the converse is not claimed.
-- ============================================================================

module CategoricalCrypto.Machine.UC where

open import categorical-crypto.Prelude hiding (id; _∘_)
open import Function.Bundles
open import Relation.Binary.Bundles
import Level

open import Categories.Category
open import Categories.Category.Monoidal.Construction.Reverse
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor.Presheaf
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
open import CategoricalCrypto.Machine.Bisim
open import CategoricalCrypto.Machine.Category
open import CategoricalCrypto.Machine.Monoidal
  using (⊗₁-id; ⊗₁-interchange; ρ⇒-natural; ρ-isoʳ; α-isoˡ)
open import CategoricalCrypto.Machine.MonoidalCategory
open import CategoricalCrypto.Standard2

open Category.HomReasoning MachineCategory
open MR MachineCategory

private
  module M = Monoidal machine-monoidal

-- The environments: joint ancilla tests, compared up to `_≅ᴹ_`.  The ancilla
-- sits on the RIGHT, matching the reversed grade `T₁ Y h ≅ h ⊗₁ id` below.

Test : Channel → Type₁
Test A = Σ[ Y ∈ Channel ] Machine (A ⊗₀ Y) ℰ-Out

data SameTest {A : Channel} : Test A → Test A → Type₁ where
  same : ∀ {Y} {E₁ E₂ : Machine (A ⊗₀ Y) ℰ-Out}
       → E₁ ≈ᴮ E₂ → SameTest (Y , E₁) (Y , E₂)

-- The machine layer is `--safe` WITH K, so `same` inverts: matching it
-- deletes the reflexive equation on the shared ancilla `Y`, which
-- `--without-K` rejects.
same⁻¹ : ∀ {A Y} {E₁ E₂ : Machine (A ⊗₀ Y) ℰ-Out}
       → SameTest (Y , E₁) (Y , E₂) → E₁ ≈ᴮ E₂
same⁻¹ (same e) = e

Test-setoid : Channel → Setoid (Level.suc 0ℓ) (Level.suc 0ℓ)
Test-setoid A = record
  { Carrier       = Test A
  ; _≈_           = SameTest
  ; isEquivalence = record
      { refl  = same ≈ᴮ-refl
      ; sym   = λ { (same e) → same (≈ᴮ-sym e) }
      ; trans = λ { (same e₁) (same e₂) → same (≈ᴮ-trans e₁ e₂) }
      }
  }

test-map : ∀ {A B} → Machine B A → Test A → Test B
test-map f t = proj₁ t , proj₂ t CC.∘ (f ⊗₁ CC.id)

test-map-cong : ∀ {A B} (f : Machine B A) {t t' : Test A}
              → SameTest t t' → SameTest (test-map f t) (test-map f t')
test-map-cong f (same e) = same (∘-congˡ (f ⊗₁ CC.id) e)

ℰ-tests : Presheaf MachineCategory (Setoids (Level.suc 0ℓ) (Level.suc 0ℓ))
ℰ-tests = record
  { F₀           = Test-setoid
  ; F₁           = λ f → record { to = test-map f ; cong = test-map-cong f }
  ; identity     = same (≅ᴹ⇒≈ᴮ (elimʳ ⊗₁-id))
  ; homomorphism = λ {_} {_} {_} {f} {g} → same (≅ᴹ⇒≈ᴮ (begin
      _ CC.∘ ((f CC.∘ g) ⊗₁ CC.id)
        ≈⟨ refl⟩∘⟨ ⊗₁-resp-≅ᴹ ≅ᴹ-refl (≅ᴹ-sym ∘-identityˡ-≅ᴹ) ⟩
      _ CC.∘ ((f CC.∘ g) ⊗₁ (CC.id CC.∘ CC.id))
        ≈⟨ refl⟩∘⟨ ⊗₁-interchange g f CC.id CC.id ⟩
      _ CC.∘ ((f ⊗₁ CC.id) CC.∘ (g ⊗₁ CC.id))
        ≈⟨ ≅ᴹ-sym ∘-assoc-≅ᴹ ⟩
      (_ CC.∘ (f ⊗₁ CC.id)) CC.∘ (g ⊗₁ CC.id) ∎))
  ; F-resp-≈     = λ e → same (≅ᴹ⇒≈ᴮ (refl⟩∘⟨ ⊗₁-resp-≅ᴹ e ≅ᴹ-refl))
  }

-- The tensor is REVERSED so that the grade sits on the right, as in
-- `Machine.Core`: `T₀ X B = B ⊗₀ X`, `sub c = id ⊗₁ c`, `T₁ Y h ≅ h ⊗₁ id`.
machines : MonoidalCategory _ _ _
machines = Reverse-MonoidalCategory machine-monoidal-category

-- Machine types below use `Channel.Core`'s tensor; the reversed monoidal one
-- is hidden so that `B ⊗₀ X` reads as it does in `Machine.Core`.
open StdUC machines ℰ-tests public hiding (_⊗₀_; _⊗₁_)

-- The kernel congruence, unfolded: `f ≈ℰ g` says exactly that every test with
-- every ancilla agrees on `f` and `g`.

≈ℰ⇒tests : ∀ {A B} {f g : Machine A B} → f ≈ℰ g
         → ∀ Y (E : Machine (B ⊗₀ Y) ℰ-Out)
         → (E ∘ (f ⊗₁ id {Y})) ≈ᴮ (E ∘ (g ⊗₁ id {Y}))
≈ℰ⇒tests e Y E = same⁻¹ (KE.run∼ e {Y , E})

tests⇒≈ℰ : ∀ {A B} {f g : Machine A B}
         → (∀ Y (E : Machine (B ⊗₀ Y) ℰ-Out) → (E ∘ (f ⊗₁ id {Y})) ≈ᴮ (E ∘ (g ⊗₁ id {Y})))
         → f ≈ℰ g
tests⇒≈ℰ e = KE.mk∼ λ {t} → same (e (proj₁ t) (proj₂ t))

-- The trivial ancilla `I` recovers environment equivalence, at the same
-- relation the tests are compared by.
≈ℰ⇒≈ℰᴮ : ∀ {A B} {f g : Machine A B} → f ≈ℰ g → f ≈ℰᴮ g
≈ℰ⇒≈ℰᴮ {f = f} {g} e E =
  ≈ᴮ-trans (≅ᴹ⇒≈ᴮ (≅ᴹ-trans (insertʳ ρ-isoʳ) (slide f ⟩∘⟨refl)))
  (≈ᴮ-trans (∘-congˡ CC.ρ⇐ (≈ℰ⇒tests e I (E ∘ CC.ρ⇒)))
            (≅ᴹ⇒≈ᴮ (≅ᴹ-trans (⟺ (slide g) ⟩∘⟨refl) (cancelʳ ρ-isoʳ))))
  where
  slide : ∀ k → (E ∘ k) ∘ CC.ρ⇒ ≅ᴹ (E ∘ CC.ρ⇒) ∘ (k ⊗₁ id {I})
  slide k = pullʳ (⟺ (ρ⇒-natural k)) ○ sym-assoc

-- Grade stability.  A test `(Y , E)` on `B ⊗₀ Z` regroups into the test
-- `(Z ⊗₀ Y , E ∘ ⊗-assoc⃖)` on `B`.

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
grade-stable Z {h} {h′} e = tests⇒≈ℰ λ Y E →
  ≈ᴮ-trans (≅ᴹ⇒≈ᴮ (≅ᴹ-trans (refl⟩∘⟨ ⊗₁-resp-≅ᴹ (T₁-⊗ʳ Z h) ≅ᴹ-refl) (regroup h E)))
  (≈ᴮ-trans (∘-congˡ ⊗-assoc (≈ℰ⇒tests e (Z ⊗₀ Y) (E ∘ ⊗-assoc⃖)))
            (≅ᴹ⇒≈ᴮ (≅ᴹ-trans (⟺ (regroup h′ E))
                             (refl⟩∘⟨ ⊗₁-resp-≅ᴹ (≅ᴹ-sym (T₁-⊗ʳ Z h′)) ≅ᴹ-refl))))

≈ᵁ⇔≈ℰ : ∀ {A B X} {f g : Machine A (B ⊗₀ X)} → f ≈ᵁ g ⇔ f ≈ℰ g
≈ᵁ⇔≈ℰ {f = f} {g} = mk⇔ {B = f ≈ℰ g} ≈ᵁ⇒≈ℰ (bridge grade-stable)

-- Sanity checks: the abstract notions land on plain machine types.  A protocol
-- with adversary interface `X` is a `Machine A (B ⊗₀ X)`, and an adversary is a
-- machine `X ⇒ X′`.

private
  _ : ∀ {A B X} (f : Machine A (B ⊗₀ X)) → f ≤UC f
  _ = ≤UC-refl

  _ : ∀ {A B X Y Z} {f : Machine A (B ⊗₀ X)} {g : Machine A (B ⊗₀ Y)} {h : Machine A (B ⊗₀ Z)}
    → f ≤UC g → g ≤UC h → f ≤UC h
  _ = ≤UC-trans

  _ : ∀ {A B X Y} {f : Machine A (B ⊗₀ X)} {g : Machine A (B ⊗₀ Y)}
    → (∃[ s ] (f ≈ᵁ (sub s ∘ g))) → f ≤UC g
  _ = dummy-complete
