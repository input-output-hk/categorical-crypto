{-# OPTIONS --safe --without-K --guardedness #-}

-- `fine→comp` has a CERTIFIED source, not the unrestricted `Fine.Sym≅`.
-- Each generator supplies a direct query-bound certificate for its actual
-- bitstring runtime. This is resource admissibility, not feasibility or crypto
-- soundness; see docs/uc-setup-symbolic.md §4.3.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Computational (𝔖 : Signature) where

open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor using (_∘F_)
open import Categories.Functor.Construction.LiftSetoids
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.LocallyGraded.SubCategory
open import Categories.NaturalTransformation using (ntHelper)
open import Data.Empty.Polymorphic as Empty
open import Data.Nat.Base using (ℕ)
open import Data.Nat.Poly
open import Data.Nat.Positive
open import Data.Product
open import Data.Unit
open import Level
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.Symbolic.Computational.Run 𝔖 public
open import CategoricalCrypto.Symbolic.Fine 𝔖 using (UnitFree)
open import CategoricalCrypto.Symbolic.Role 𝔖 using (Atom; Role; verdict)
open import CategoricalCrypto.UC.Core using (Observable; Evaluation)
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Enrichment
open import CategoricalCrypto.UC.Model.Family hiding (Test)
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UC.QueryBound
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Machines.Core as Core

private
  module G = MonoidalCategory 𝔾ᵒ
  module Fm = MonoidalCategory Famᴹ
  module MC = Core (𝒱ₚ 0ℓ)

open GradedSubCat gradingᵒ
open FreeMonoidalHelper Mon Atom

cast-pred : {A A′ B B′ : G.Obj} {r : ℕ⁺} (p : A ≡ A′) (q : B ≡ B′) {f : A G.⇒ B}
          → Pred r f → Pred r (subst₂ G._⇒_ p q f)
cast-pred refl refl h = h

deadᴾ : (B : Iface) → Proc (Empty.⊥ {0ℓ} ⇿ Empty.⊥ {0ℓ}) B
deadᴾ B = MC.mk (initˢ ⊤ tt) (λ _ → botₚ)

dead-certified : (B : Iface) → Certified 1 (deadᴾ B)
dead-certified B = qbᵢ-upward ⊤ (returnₚ tt) (λ _ → botₚ) (λ _ ()) (λ _ ())

deadᵒ : (B : G.Obj) → G.unit G.⇒ B
deadᵒ B = subst₂ G._⇒_ (sym unitᵒ) (ifaceᵒ-onto B) (procᵒ (deadᴾ (objᵒ B)))

dead-pred : (B : G.Obj) → Pred 1⁺ (deadᵒ B)
dead-pred B = cast-pred (sym unitᵒ) (ifaceᵒ-onto B) (qbᵒ (certified⇒QB (dead-certified (objᵒ B))))

deadᶠ : (B : Obj^ω) → Fm.unit Fm.⇒ B
deadᶠ B = unit^ω λ η → deadᵒ (B η) , dead-pred (B η)

module Closing {o ℓ e} (M : MonoidalCategory o ℓ e) where
  open MonoidalCategory M renaming (unit to I; _⊗₀_ to _⊗M_)
  open import Categories.Category.Monoidal.Utilities monoidal using (module Shorthands)
  open Shorthands
  open HomReasoning
  private variable A B Y : Obj

  close : I ⇒ Y → A ⇒ Y ⊗M A
  close d = d ⊗₁ id ∘ λ⇐

  close-natural : (d : I ⇒ Y) (f : B ⇒ A) → (id ⊗₁ f) ∘ close d ≈ close d ∘ f
  close-natural d f = sym-assoc ○ (left ⟩∘⟨refl) ○ (⟺ right ⟩∘⟨refl)
    ○ assoc ○ (refl⟩∘⟨ ⟺ unitorˡ-commute-to) ○ sym-assoc
    where
    left : (id ⊗₁ f) ∘ (d ⊗₁ id) ≈ d ⊗₁ f
    left = ⟺ ⊗.homomorphism ○ ⊗.F-resp-≈ (identityˡ , identityʳ)
    right : (d ⊗₁ id) ∘ (id ⊗₁ f) ≈ d ⊗₁ f
    right = ⟺ ⊗.homomorphism ○ ⊗.F-resp-≈ (identityʳ , identityˡ)

module CertifiedSource (sch : Scheme) where
  private module ByteRun = Execution sch

  record Generator (x y : ObjTerm) : Set where
    constructor certified
    field
      free-in : UnitFree x
      free-out : UnitFree y
      role : Role x y
      rate : ℕ⁺
      bounded : (η : ℕ) → Certified (value rate) (ByteRun.runᶜ η role)

  certData : FreeMonoidalData {0ℓ}
  certData = record { v = Mon ; X = Atom ; mor = Generator }

  module Src = FreeMonoidal certData
  open Src hiding (ObjTerm; unit; _⊗₀_; Var)

  𝔻𝕐ᶜ : MonoidalCategory 0ℓ 0ℓ 0ℓ
  𝔻𝕐ᶜ = FMC

  Test : ObjTerm → Set
  Test A = Σ[ Y ∈ ObjTerm ] HomTerm (Y ⊗₀ A) (Var verdict)

  pull : {A B : ObjTerm} → HomTerm B A → Test A → Test B
  pull f (Y , T) = Y , T ∘ (id ⊗₁ f)

  data SameTerm {A} : Test A → Test A → Set where
    same : ∀ {Y} {T T′ : HomTerm (Y ⊗₀ A) (Var verdict)} → T ≈Term T′ → SameTerm (Y , T) (Y , T′)

  ℰᵗᶜ : Presheaf (MonoidalCategory.U 𝔻𝕐ᶜ) (Setoids 0ℓ 0ℓ)
  ℰᵗᶜ = record
    { F₀ = λ A → record
      { Carrier = Test A ; _≈_ = SameTerm
      ; isEquivalence = record
        { refl = same ≈-Term-refl ; sym = λ { (same e) → same (≈-Term-sym e) }
        ; trans = λ { (same e) (same e′) → same (≈-Term-trans e e′) } } }
    ; F₁ = λ f → record { to = pull f ; cong = λ { (same e) → same (∘-resp-≈ e ≈-Term-refl) } }
    ; identity = same (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ)
    ; homomorphism = same (≈-Term-trans (∘-resp-≈ ≈-Term-refl (≈-Term-trans
        (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist)) (≈-Term-sym assoc))
    ; F-resp-≈ = λ e → same (∘-resp-≈ ≈-Term-refl (⊗-resp-≈ ≈-Term-refl e)) }

  ℰ≅ᶜ : Presheaf (MonoidalCategory.U 𝔻𝕐ᶜ) (Setoids (suc 0ℓ) (suc 0ℓ))
  ℰ≅ᶜ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵗᶜ

  module Sym≅ᶜ = StdUC 𝔻𝕐ᶜ ℰ≅ᶜ

  ⟦v⟧ᶠ : ⟦ Mon ⟧ᵥ
  ⟦v⟧ᶠ = fromMC Famᴹ noSymmetric

  atomᶠ : Atom → Obj^ω
  atomᶠ a = Δ (ByteRun.atomᵒ a)

  module Obj = FreeObjInterp Mon Atom ⟦v⟧ᶠ atomᶠ

  tree≡ : (x : ObjTerm) → UnitFree x → (η : ℕ) → Obj.⟦ x ⟧₀ η ≡ ifaceᵒ ByteRun.⟦ x ⟧ᴵ
  tree≡ (x ⊗₀ y) (ux , uy) η = trans (cong₂ G._⊗₀_ (tree≡ x ux η) (tree≡ y uy η)) (⊗ᵒ ByteRun.⟦ x ⟧ᴵ ByteRun.⟦ y ⟧ᴵ)
  tree≡ (Var _) _ η = refl
  tree≡ unit () η

  leafᶠ : {x y : ObjTerm} → Generator x y → Obj.⟦ x ⟧₀ ⇒^ω Obj.⟦ y ⟧₀
  leafᶠ {x} {y} (certified ux uy p r bounded) = (λ _ → r) , poly-const (value r) , λ η →
    subst₂ G._⇒_ (sym (tree≡ x ux η)) (sym (tree≡ y uy η)) (procᵒ (ByteRun.runᶜ η p)) ,
    cast-pred (sym (tree≡ x ux η)) (sym (tree≡ y uy η)) (qbᵒ (certified⇒QB (bounded η)))

  computational : FreeFunctorData certData
  computational = record { ⟦v⟧ = ⟦v⟧ᶠ ; ⟦_⟧ᵖ₀ = atomᶠ ; ⟦_⟧ᵖ₁ = leafᶠ }

  Fᶜ : StrongMonoidalFunctor 𝔻𝕐ᶜ Famᴹ
  Fᶜ = freeStrongMonoidal computational

  private
    module F = StrongMonoidalFunctor Fᶜ
    module Obs = Observable (Evaluation.observable Evaluationᴺ)
    module Close = Closing Famᴹ

  toᶜ : {A : ObjTerm} → Test A → F.₀ A Fm.⇒ Δ Ωᵒ
  toᶜ {A} (Y , T) = Fm._∘_ (F.₁ T)
    (Close.close {Y = F.₀ Y} {A = F.₀ A} (deadᶠ (F.₀ Y)))

  toᶜ-cong : {A : ObjTerm} {t t′ : Test A} → SameTerm t t′
           → Obs._≋_ {A = F.₀ A} (toᶜ t) (toᶜ t′)
  toᶜ-cong {A} {Y , T} {.Y , T′} (same e) = Obs.≈⇒≋ {A = F.₀ A}
    {t = toᶜ (Y , T)} {u = toᶜ (Y , T′)}
    (Fm.∘-resp-≈ˡ {A = F.₀ A} {B = F.₀ (Y ⊗₀ A)} {C = Δ Ωᵒ}
      {f = F.₁ T} {h = F.₁ T′}
      {g = Close.close {Y = F.₀ Y} {A = F.₀ A} (deadᶠ (F.₀ Y))}
      (F.F-resp-≈ {f = T} {g = T′} e))

  toᶜ-natural : {A B : ObjTerm} (f : HomTerm B A) (t : Test A)
              → Obs._≋_ {A = F.₀ B} (toᶜ (pull f t)) (Fm._∘_ (toᶜ t) (F.₁ f))
  toᶜ-natural {A} {B} f (Y , T) = Obs.≈⇒≋ {A = F.₀ B}
    {t = toᶜ (pull f (Y , T))} {u = Fm._∘_ (toᶜ (Y , T)) (F.₁ f)}
    (Fm.Equiv.trans {A = F.₀ B} {B = Δ Ωᵒ}
      {i = toᶜ (pull f (Y , T))}
      {j = Fm._∘_ (F.₁ T) (Fm._∘_ (Fm.id {F.₀ Y} Fm.⊗₁ F.₁ f) closeB)}
      {k = Fm._∘_ (toᶜ (Y , T)) (F.₁ f)}
      (Fm.assoc {f = closeB} {g = Fm.id {F.₀ Y} Fm.⊗₁ F.₁ f} {h = F.₁ T})
      (Fm.Equiv.trans {A = F.₀ B} {B = Δ Ωᵒ}
        {i = Fm._∘_ (F.₁ T) (Fm._∘_ (Fm.id {F.₀ Y} Fm.⊗₁ F.₁ f) closeB)}
        {j = Fm._∘_ (F.₁ T) (Fm._∘_ closeA (F.₁ f))}
        {k = Fm._∘_ (toᶜ (Y , T)) (F.₁ f)}
        (Fm.∘-resp-≈ʳ {A = F.₀ B} {B = F.₀ (Y ⊗₀ A)} {C = Δ Ωᵒ}
          {f = Fm._∘_ (Fm.id {F.₀ Y} Fm.⊗₁ F.₁ f) closeB}
          {h = Fm._∘_ closeA (F.₁ f)} {g = F.₁ T}
          (Close.close-natural {Y = F.₀ Y} {B = F.₀ B} {A = F.₀ A} (deadᶠ (F.₀ Y)) (F.₁ f)))
        (Fm.sym-assoc {f = F.₁ f} {g = closeA} {h = F.₁ T})))
    where
    closeA = Close.close {Y = F.₀ Y} {A = F.₀ A} (deadᶠ (F.₀ Y))
    closeB = Close.close {Y = F.₀ Y} {A = F.₀ B} (deadᶠ (F.₀ Y))

  νᶜ : PresheafMorphism F.F ℰ≅ᶜ Obs.ℰᴼ
  νᶜ = record { ν = ntHelper record
    { η = λ A → record { to = λ t → toᶜ {A} (lower t) ; cong = λ e → toᶜ-cong {A} (lower e) }
    ; commute = λ f {t} → toᶜ-natural f (lower t) } }

  fine→comp : UCSetupMorphism Sym≅ᶜ.StdSetup ucSetupᴺ
  fine→comp = StdUCMorphism 𝔻𝕐ᶜ Famᴹ ℰ≅ᶜ Obs.ℰᴼ Fᶜ νᶜ
