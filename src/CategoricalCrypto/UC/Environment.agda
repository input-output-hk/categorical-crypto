{-# OPTIONS --safe --without-K #-}

-- The environment layer: joint ancilla-tests, and when two processes are
-- indistinguishable to all of them.
--
-- The ancilla is a PARAMETER of `SameTV`, not part of its carrier.  The
-- reference arc bundled it existentially (`Σ[ Y ] Test (Y ⊗ A)`), so the
-- agreement constructor forced an ancilla equation; a consumer whose scrutinee
-- had a defined function in that index could not match it, and routing through
-- a Σ-projection instead handed back a loop `Y ≡ Y` that only axiom K can
-- consume.  That is the whole reason the reference needed
-- `HomTransportTrivial` — a hypothesis refuted under univalence at its own
-- instance, discharged in a two-module K island.  Here `SameTV Y A` is a
-- one-field record at a fixed ancilla: no equation is ever generated, `same` is
-- a projection that reduces by eta, and nothing in this file or below it leaves
-- `--without-K`.
--
-- For the same reason `_≈ℰ_` is the adaptive single-ancilla relation *by
-- definition* rather than the kernel congruence of the environment presheaf:
-- the reference had to prove the two equal (`≈ℰ⇒R`, the direction that needed
-- the hypothesis).  `ℰᵗᵛ` is still built, and the definition IS its kernel
-- relation ancilla by ancilla — `record { same = h Y E }` and `same` back.
-- `grade-stable` is then a theorem with no hypothesis under it.
--
-- Everything here consumes the QUALITATIVE observation alone; the ε-indexed
-- form of the relation and its collapse live in `UC.Environment.Approximate`.

open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Functor.Presheaf using (Presheaf)
import Categories.Morphism.Reasoning as MR

open import Level using (_⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import CategoricalCrypto.UC.Core using (UCBase)

module CategoricalCrypto.UC.Environment
  {o ℓ e os ℓs} (base : UCBase o ℓ e os ℓs) where

open UCBase base public
open HomReasoning
open MR 𝒞 using (cancelˡ; elimʳ)

private variable A B′ C′ X Y : Obj

------------------------------------------------------------------------
-- Tests, closures, and the presheaf the inherited doctrine asks for

-- Spending only the observation, so it is proved there — once for this layer,
-- the machine model (`UC.Model.Environment`) and the levelwise family (P6).
open import CategoricalCrypto.UC.Environment.Presheaf 𝒞 observation public

------------------------------------------------------------------------
-- Tests at a fixed ancilla

-- Two tests at the same ancilla agree when no closure separates them.
record SameTV (Y A : Obj) (E₁ E₂ : Test (Y ⊛ A)) : Set (ℓ ⊔ ℓs) where
  field same : (m : Closure (Y ⊛ A)) → obs E₁ m ∼ obs E₂ m

open SameTV public

same-≈ : {E₁ E₂ : Test (Y ⊛ A)} → E₁ ≈ E₂ → SameTV Y A E₁ E₂
same-≈ eq = record { same = λ m → ⟦⟧-resp-≈ (∘-resp-≈ˡ eq) }

Tests : (Y A : Obj) → Setoid ℓ (ℓ ⊔ ℓs)
Tests Y A = record
  { Carrier = Test (Y ⊛ A)
  ; _≈_ = SameTV Y A
  ; isEquivalence = record
    { refl  = record { same = λ _ → ∼-refl }
    ; sym   = λ h → record { same = λ m → ∼-sym (same h m) }
    ; trans = λ h k → record { same = λ m → ∼-trans (same h m) (same k m) }
    }
  }

-- Plugging a process into a test at a fixed ancilla.
tv₁ : (Y : Obj) {A B′ : Obj} → A ⇒ B′ → Test (Y ⊛ B′) → Test (Y ⊛ A)
tv₁ Y f E = E ∘ T₁ Y f

tv₁-cong : (Y : Obj) {A B′ : Obj} (f : A ⇒ B′) {E₁ E₂ : Test (Y ⊛ B′)}
         → SameTV Y B′ E₁ E₂ → SameTV Y A (tv₁ Y f E₁) (tv₁ Y f E₂)
tv₁-cong Y f h = record { same = λ m → ∼-cast sym-assoc sym-assoc (same h (T₁ Y f ∘ m)) }

-- The slide every carry performs: a stage of the process becomes a stage of the
-- test.  `UC.Audit.audit-carry` moves the simulator this way and
-- `UC.Robust.Observation.robust-sub` the same one with no arithmetic under it.
tv₁-∘ : (Y : Obj) {A B′ C′ : Obj} (k : B′ ⇒ C′) (g : A ⇒ B′) (E : Test (Y ⊛ C′))
      → tv₁ Y (k ∘ g) E ≈ tv₁ Y g (tv₁ Y k E)
tv₁-∘ Y k g E = ∘-resp-≈ʳ T₁-∘ ○ sym-assoc

ℰᵗᵛ : Obj → Presheaf 𝒞 (Setoids ℓ (ℓ ⊔ ℓs))
ℰᵗᵛ Y = record
  { F₀           = Tests Y
  ; F₁           = λ f → record { to = tv₁ Y f ; cong = tv₁-cong Y f }
  ; identity     = same-≈ (elimʳ T₁-id)
  ; homomorphism = same-≈ (∘-resp-≈ʳ T₁-∘ ○ sym-assoc)
  ; F-resp-≈     = λ eq → same-≈ (∘-resp-≈ʳ (T₁-resp-≈ eq))
  }

------------------------------------------------------------------------
-- Environment agreement

infix 4 _≈ℰ_

_≈ℰ_ : {A B′ : Obj} (f g : A ⇒ B′) → Set (o ⊔ ℓ ⊔ ℓs)
_≈ℰ_ {A} {B′} f g = (Y : Obj) (E : Test (Y ⊛ B′)) (m : Closure (Y ⊛ A))
                  → obs (tv₁ Y f E) m ∼ obs (tv₁ Y g E) m

≈ℰ-refl : {f : A ⇒ B′} → f ≈ℰ f
≈ℰ-refl _ _ _ = ∼-refl

≈ℰ-sym : {f g : A ⇒ B′} → f ≈ℰ g → g ≈ℰ f
≈ℰ-sym h Y E m = ∼-sym (h Y E m)

≈ℰ-trans : {f g h : A ⇒ B′} → f ≈ℰ g → g ≈ℰ h → f ≈ℰ h
≈ℰ-trans p q Y E m = ∼-trans (p Y E m) (q Y E m)

≈ℰ-isEquivalence : IsEquivalence (_≈ℰ_ {A} {B′})
≈ℰ-isEquivalence = record { refl = ≈ℰ-refl ; sym = ≈ℰ-sym ; trans = ≈ℰ-trans }

≈ℰ-setoid : (A B′ : Obj) → Setoid ℓ (o ⊔ ℓ ⊔ ℓs)
≈ℰ-setoid A B′ = record
  { Carrier = A ⇒ B′ ; _≈_ = _≈ℰ_ ; isEquivalence = ≈ℰ-isEquivalence }

≈⇒≈ℰ : {f g : A ⇒ B′} → f ≈ g → f ≈ℰ g
≈⇒≈ℰ eq _ _ _ = ⟦⟧-resp-≈ (∘-resp-≈ˡ (∘-resp-≈ʳ (T₁-resp-≈ eq)))

≈ℰ-congˡ : {A B′ C′ : Obj} (k : B′ ⇒ C′) {f g : A ⇒ B′} → f ≈ℰ g → (k ∘ f) ≈ℰ (k ∘ g)
≈ℰ-congˡ {A} {B′} k {f} {g} h Y E m = ∼-cast (step f) (step g) (h Y (E ∘ T₁ Y k) m)
  where
  step : (u : A ⇒ B′) → ((E ∘ T₁ Y k) ∘ T₁ Y u) ∘ m ≈ (E ∘ T₁ Y (k ∘ u)) ∘ m
  step u = ∘-resp-≈ˡ (assoc ○ ∘-resp-≈ʳ (⟺ T₁-∘))

≈ℰ-congʳ : {A B′ X : Obj} (l : X ⇒ A) {f g : A ⇒ B′} → f ≈ℰ g → (f ∘ l) ≈ℰ (g ∘ l)
≈ℰ-congʳ {A} {B′} l {f} {g} h Y E m = ∼-cast (step f) (step g) (h Y E (T₁ Y l ∘ m))
  where
  step : (u : A ⇒ B′) → (E ∘ T₁ Y u) ∘ (T₁ Y l ∘ m) ≈ (E ∘ T₁ Y (u ∘ l)) ∘ m
  step u = assoc ○ (refl⟩∘⟨ (sym-assoc ○ ∘-resp-≈ˡ (⟺ T₁-∘))) ○ sym-assoc

-- An agreement read at ONE context, presented uniformly in the process: if a
-- single ancilla, test and closure realize `k w` for every `w`, then closeness
-- of the two `k`-observations is the whole of it.  Stated over an arbitrary
-- base; the machine model uses `UC.Model.Bridge.≈ᴳ-at`, the same shape past the
-- seal, because a `∼-cast` between machine COMPOSITES is the eta cliff
-- `UC.Seam.Grounding`'s header measures.
≈ℰ-at : {A B′ : Obj} (Y : Obj) (Et : Test (Y ⊛ B′)) (m : Closure (Y ⊛ A))
        (k : A ⇒ B′ → 𝟙 ⇒ Ω) → ((w : A ⇒ B′) → (Et ∘ T₁ Y w) ∘ m ≈ k w)
      → {f g : A ⇒ B′} → f ≈ℰ g → ⟦ k f ⟧ ∼ ⟦ k g ⟧
≈ℰ-at Y Et m k eq {f} {g} r = ∼-cast (eq f) (eq g) (r Y Et m)

-- Grade stability: the ancilla quantifier absorbs a bypass wire.  Where the
-- reference needed `HomTransportTrivial` for this, here it is the associativity
-- of the action and nothing else.
grade-stable : {A B′ : Obj} (Y : Obj) {h h′ : A ⇒ B′} → h ≈ℰ h′ → T₁ Y h ≈ℰ T₁ Y h′
grade-stable {A} {B′} Y {h} {h′} r W E m =
  ∼-cast (step h) (step h′) (r (W ⊛ Y) (E ∘ a⇐) (a⇒ ∘ m))
  where
  step : (u : A ⇒ B′)
       → ((E ∘ a⇐) ∘ T₁ (W ⊛ Y) u) ∘ (a⇒ ∘ m) ≈ (E ∘ T₁ W (T₁ Y u)) ∘ m
  step u = begin
    ((E ∘ a⇐) ∘ T₁ (W ⊛ Y) u) ∘ (a⇒ ∘ m)   ≈⟨ assoc ⟩
    (E ∘ a⇐) ∘ (T₁ (W ⊛ Y) u ∘ (a⇒ ∘ m))   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    (E ∘ a⇐) ∘ ((T₁ (W ⊛ Y) u ∘ a⇒) ∘ m)   ≈⟨ refl⟩∘⟨ (a-nat ⟩∘⟨refl) ⟨
    (E ∘ a⇐) ∘ ((a⇒ ∘ T₁ W (T₁ Y u)) ∘ m)  ≈⟨ assoc ⟩
    E ∘ (a⇐ ∘ ((a⇒ ∘ T₁ W (T₁ Y u)) ∘ m))  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    E ∘ (a⇐ ∘ (a⇒ ∘ (T₁ W (T₁ Y u) ∘ m)))  ≈⟨ refl⟩∘⟨ cancelˡ a-isoˡ ⟩
    E ∘ (T₁ W (T₁ Y u) ∘ m)                ≈⟨ sym-assoc ⟩
    (E ∘ T₁ W (T₁ Y u)) ∘ m                ∎
