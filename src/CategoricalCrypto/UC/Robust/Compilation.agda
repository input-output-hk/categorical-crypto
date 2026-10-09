{-# OPTIONS --safe --without-K #-}

-- UC as robust compilation (`patrignani2024`, `patrignani2024csf`), stated as
-- theorems about `_≤UC_`; the dictionary is docs/uc-robust-compilation.md §3.
-- `Within` is one setup: environment-blind robustness is only outcome
-- inclusion (§4.1), robust preservation of every `≈ᵁ`-invariant property of
-- attacked protocols is `_≤UC_` (§4.2, CSF Thm 3), and environment-indexed
-- trace properties give the simulator-explicit form (§4.3).  `Along` carries
-- the property form along a `UCSetupMorphism` (§4.5).

open import categorical-crypto.Prelude using (PredS)
open import Data.Product
open import Data.Unit
open import Function.Bundles
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.Properties.Setoid.Ext as SetoidExt

open import Categories.Functor.Properties

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.Abstract2.Morphism
import CategoricalCrypto.UC.Robust as UCRobust
open import CategoricalCrypto.UCSetup
open import CategoricalCrypto.UCSetup.Morphism

module CategoricalCrypto.UC.Robust.Compilation where

module Within {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (setup : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where
  open UCRobust setup

  private variable
    A B : 𝒞.Obj
    X Y : ℐ.Obj
    d p : Level
    f h k : A 𝒞.⇒ T₀ X B
    g : A 𝒞.⇒ T₀ Y B

  infix 4 _⊆ᵒ_

  ------------------------------------------------------------------------
  -- Environment-blind properties see outcomes only

  _⊆ᵒ_ : A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ Y B → Set (o ⊔ cs ⊔ ℓs)
  _⊆ᵒ_ {X = X} {B = B} f g = ∀ W (e : Env (T₀ (W ⊗₀ X) B)) → ∃[ e′ ] run W f e Env.≈ run W g e′

  outcomes⇒robust : (P : Predℰ A p) → f ⊆ᵒ g → Robust P ⊤ᴬ g → Robust P ⊤ᴬ f
  outcomes⇒robust P incl rob W e _ =
    let e′ , u = incl W e in Equivalence.from (Func.cong (P W) u) (rob W e′ tt)

  -- ⇒ instantiates the predicate "is an outcome of g"
  robust⇔outcomes : ((P : Predℰ A (cs ⊔ ℓs)) → Robust P ⊤ᴬ g → Robust P ⊤ᴬ f) ⇔ f ⊆ᵒ g
  robust⇔outcomes {g = g} = mk⇔
    (λ pres W e → pres (λ V → record
        { to = λ x → ∃[ e′ ] x Env.≈ run V g e′
        ; cong = λ u → mk⇔ (λ (e′ , v) → e′ , Env.trans (Env.sym u) v)
                           (λ (e′ , v) → e′ , Env.trans u v) })
      (λ _ e _ → e , Env.refl) W e tt)
    (λ incl P → outcomes⇒robust P incl)

  ------------------------------------------------------------------------
  -- Hyperproperties: `_≤UC_` is robust hyperproperty preservation

  Predᵁ : (A B : 𝒞.Obj) (p : Level) → Set (o ⊔ ℓ′ ⊔ cs ⊔ ℓs ⊔ suc p)
  Predᵁ A B p = (X : ℐ.Obj) → PredS (≈ᵁ-setoid A B X) p

  Robustᵁ : Predᵁ A B p → A 𝒞.⇒ T₀ X B → Set (o ⊔ ℓ ⊔ p)
  Robustᵁ {X = X} H f = ∀ {X′} (a : X ℐ.⇒ X′) → H X′ ⟨$⟩ (sub a 𝒞.∘ f)

  -- `patrignani2024csf` §IV's Hyp(F): `Robustᵁ (Hyp g) f` unfolds to `f ≤UC g`
  Hyp : A 𝒞.⇒ T₀ Y B → Predᵁ A B (o ⊔ ℓ ⊔ cs ⊔ ℓs)
  Hyp {Y = Y} g X′ = record
    { to = λ h → Σ[ s ∈ Y ℐ.⇒ X′ ] h ≈ᵁ sub s 𝒞.∘ g
    ; cong = λ u → mk⇔ (λ (s , v) → s , ≈ᵁ-trans (≈ᵁ-sym u) v) (λ (s , v) → s , ≈ᵁ-trans u v) }

  liftᵁ : (q : Level) → Predᵁ A B p → Predᵁ A B (p ⊔ q)
  liftᵁ q H X = record
    { to = λ h → Lift q (H X ⟨$⟩ h)
    ; cong = λ u → let open Equivalence (Func.cong (H X) u) in
        mk⇔ (λ (lift x) → lift (to x)) (λ (lift x) → lift (from x)) }

  ≤UC⇒robustᵁ : f ≤UC g → (H : Predᵁ A B p) → Robustᵁ H g → Robustᵁ H f
  ≤UC⇒robustᵁ le H rob a = let s , u = le a in Equivalence.from (Func.cong (H _) u) (rob s)

  robustᵁ⇒≤UC : ((H : Predᵁ A B (o ⊔ ℓ ⊔ cs ⊔ ℓs)) → Robustᵁ H g → Robustᵁ H f) → f ≤UC g
  robustᵁ⇒≤UC {g = g} pres = pres (Hyp g) (≤UC-refl g)

  -- `patrignani2024` Thm 4 / `patrignani2024csf` Thm 3.  `∀ H` cannot range
  -- over every level inside `_⇔_` (that is `Setω`): ← needs the principal
  -- level, and `≤UC⇔robustᵁ↑` covers every level above it.
  ≤UC⇔robustᵁ : f ≤UC g ⇔ ((H : Predᵁ A B (o ⊔ ℓ ⊔ cs ⊔ ℓs)) → Robustᵁ H g → Robustᵁ H f)
  ≤UC⇔robustᵁ = mk⇔ ≤UC⇒robustᵁ robustᵁ⇒≤UC

  ≤UC⇔robustᵁ↑ : f ≤UC g ⇔ ((H : Predᵁ A B (o ⊔ ℓ ⊔ cs ⊔ ℓs ⊔ p)) → Robustᵁ H g → Robustᵁ H f)
  ≤UC⇔robustᵁ↑ {g = g} {p = p} = mk⇔ ≤UC⇒robustᵁ
    λ pres a → lower (pres (liftᵁ p (Hyp g)) (λ b → lift (≤UC-refl g b)) a)

  ------------------------------------------------------------------------
  -- Trace properties: the property may read the environment

  Traceℰ : (A B : 𝒞.Obj) (X : ℐ.Obj) (p : Level) → Set (o ⊔ cs ⊔ ℓs ⊔ suc p)
  Traceℰ A B X p = (W : ℐ.Obj) → Env (T₀ (W ⊗₀ X) B) → PredS (ℰ.₀ (T₀ W A)) p

  Robustᵗ : Traceℰ A B X p → Admissible B d → A 𝒞.⇒ T₀ X B → Set (o ⊔ cs ⊔ d ⊔ p)
  Robustᵗ {X = X} P Adm f = ∀ W e → Adm W X e → P W e ⟨$⟩ run W f e

  robust≡robustᵗ : (P : Predℰ A p) (Adm : Admissible B d) (f : A 𝒞.⇒ T₀ X B)
                 → Robust P Adm f ≡ Robustᵗ (λ W _ → P W) Adm f
  robust≡robustᵗ _ _ _ = refl

  robustᵗ-resp-≈ᵁ : (P : Traceℰ A B X p) (Adm : Admissible B d) → h ≈ᵁ k → Robustᵗ P Adm k → Robustᵗ P Adm h
  robustᵗ-resp-≈ᵁ P _ u rob W e adm = Equivalence.from (Func.cong (P W e) (KE.run∼ (u W))) (rob W e adm)

  -- ← instantiates the kernel-equality predicate `∼[ run W k e ]`
  ≈ᵁ⇔robustᵗ : h ≈ᵁ k ⇔ ((P : Traceℰ A B X ℓs) → Robustᵗ P ⊤ᴬ k → Robustᵗ P ⊤ᴬ h)
  ≈ᵁ⇔robustᵗ {k = k} = mk⇔ (λ u P → robustᵗ-resp-≈ᵁ P ⊤ᴬ u)
    λ pres W → KE.mk∼ λ {e} → Env.sym
      (pres (λ V d → SetoidExt.∼[_] (ℰ.₀ (T₀ V _)) (run V k d)) (λ _ _ _ → Env.refl) W e tt)

  -- The simulator stays explicit: a `Traceℰ` at grade X′ has no transport to g's grade Y
  ≤UC⇔robustᵗ : f ≤UC g ⇔ (∀ {X′} (a : X ℐ.⇒ X′) → Σ[ s ∈ Y ℐ.⇒ X′ ]
                  ((P : Traceℰ A B X′ ℓs) → Robustᵗ P ⊤ᴬ (sub s 𝒞.∘ g) → Robustᵗ P ⊤ᴬ (sub a 𝒞.∘ f)))
  ≤UC⇔robustᵗ = mk⇔ (λ le {X′} a → proj₁ (le {X′} a) , Equivalence.to ≈ᵁ⇔robustᵗ (proj₂ (le a)))
                    (λ pres {X′} a → proj₁ (pres {X′} a) , Equivalence.from ≈ᵁ⇔robustᵗ (proj₂ (pres a)))

------------------------------------------------------------------------
-- Two setups: the target 𝕊′ is the common trace model
------------------------------------------------------------------------

module Along {o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs : Level}
             {𝕊 : UCSetup o₁ ℓ₁ e₁ o₁′ ℓ₁′ e₁′ cs ℓs} {𝕊′ : UCSetup o₂ ℓ₂ e₂ o₂′ ℓ₂′ e₂′ cs ℓs}
             (𝕄 : UCSetupMorphism 𝕊 𝕊′) where
  private
    module S = AbstractUC 𝕊
    module S′ = AbstractUC 𝕊′
    module R′ = Within 𝕊′

    variable
      A B : S.𝒞.Obj
      X Y : S.ℐ.Obj
      p : Level
      f : A S.𝒞.⇒ S.T₀ X B
      g : A S.𝒞.⇒ S.T₀ Y B

  open UCSetupMorphism 𝕄
  open Transfer 𝕄

  -- Every target test on `F.₀ A` is a translated source test: backtranslation
  -- moved from contexts to environments by the dummy theorem
  robustᵁ-transfer : ν.Epi → S′.GradeStable → f S.≤UC g
                   → (H : R′.Predᵁ (F.₀ A) (F.₀ B) p) → R′.Robustᵁ H (G g) → R′.Robustᵁ H (G f)
  robustᵁ-transfer epi gs′ le = R′.≤UC⇒robustᵁ (transfer epi gs′ le)

  -- Target simulators backtranslate (`Full`), translated protocols stay apart (`κ-Mono`, `ν.Mono`)
  robustᵁ-reflect : Full Φ.F → κ-Mono → ν.Mono → S.GradeStable
                  → ((H : R′.Predᵁ (F.₀ A) (F.₀ B) (o₂ ⊔ ℓ₂ ⊔ cs ⊔ ℓs))
                     → R′.Robustᵁ H (G g) → R′.Robustᵁ H (G f))
                  → f S.≤UC g
  robustᵁ-reflect full κ-mono mono gs pres = reflects-≤UC full κ-mono mono gs (R′.robustᵁ⇒≤UC pres)

  ≤UC⇔robustᵁ-along : ν.Epi → S′.GradeStable → Full Φ.F → κ-Mono → ν.Mono → S.GradeStable
                    → f S.≤UC g ⇔ ((H : R′.Predᵁ (F.₀ A) (F.₀ B) (o₂ ⊔ ℓ₂ ⊔ cs ⊔ ℓs))
                                   → R′.Robustᵁ H (G g) → R′.Robustᵁ H (G f))
  ≤UC⇔robustᵁ-along epi gs′ full κ-mono mono gs =
    mk⇔ (robustᵁ-transfer epi gs′) (robustᵁ-reflect full κ-mono mono gs)
