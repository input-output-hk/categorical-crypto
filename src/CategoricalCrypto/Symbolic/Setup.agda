{-# OPTIONS --safe --without-K --guardedness #-}

-- `Sym`, the symbolic UC setup `StdUC 𝔻𝕐 ℰˢʸᵐ`, and `fine→sym` from `Sym≅`
-- (docs/uc-setup-symbolic.md §3.6, §4.1).  A test is a role circuit with an
-- ancilla, as in `Sym≅`; two tests are equal when every closure of the ancilla
-- and the hole allows the same verdicts (`Semantics.eval`), so the kernel is DY
-- trace (may-testing) equivalence.  The ancilla absorbs the bypass wire, so
-- `grade-stable` needs no hypothesis.  `Sym` stays qualified, like `Sym≅`: its
-- category names clash with the term syntax.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Setup (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Axiom.UniquenessOfIdentityProofs
open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Construction.LiftSetoids
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation using (ntHelper)
open import Data.Bool.Base
open import Data.Product
open import Function.Bundles
open import Function.Properties.Equivalence using (⇔-isEquivalence)
open import Level
open import Relation.Binary.Bundles
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures using (IsEquivalence)

open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Standard2
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.Symbolic.Semantics 𝔖 E
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
open import CategoricalCrypto.UCSetup.Morphism

private
  module G = MonoidalCategory 𝔾ᵒ
  module ⇔ {ℓ} = IsEquivalence (⇔-isEquivalence {ℓ})

  variable
    A B C Y Z : ObjTerm

open Category.HomReasoning FreeMonoidal

------------------------------------------------------------------------
-- Tests, compared by their verdicts

Closure : ObjTerm → Set
Closure A = HomTerm (Var void) A

Agree : (T T′ : HomTerm (Y ⊗₀ A) (Var verdict)) → Set
Agree T T′ = ∀ (m : Closure _) b → eval (T ∘ m) b ⇔ eval (T′ ∘ m) b

data SameObs {A} : Test A → Test A → Set where
  same : {T T′ : HomTerm (Y ⊗₀ A) (Var verdict)} → Agree T T′ → SameObs (Y , T) (Y , T′)

-- `same` inverts by UIP on the ancilla, which `≟ObjTerm` decides.
same⁻¹ : {T T′ : HomTerm (Y ⊗₀ A) (Var verdict)} → SameObs (Y , T) (Y , T′) → Agree T T′
same⁻¹ {Y} {A} {T} {T′} s =
  let p , h = unsame s in subst (λ p → Agree T (subst Hole (sym p) T′)) (UIPᵒ p refl) h
  where
  Hole : ObjTerm → Set
  Hole Y = HomTerm (Y ⊗₀ A) (Var verdict)

  UIPᵒ : UIP ObjTerm
  UIPᵒ = Decidable⇒UIP.≡-irrelevant (FreeMonoidalHelper.≟ObjTerm Mon Atom _≟ᴬ_)

  unsame : {t t′ : Test A} → SameObs t t′
         → Σ[ p ∈ proj₁ t ≡ proj₁ t′ ] Agree (proj₂ t) (subst Hole (sym p) (proj₂ t′))
  unsame (same h) = refl , h

term⇒obs : {t t′ : Test A} → SameTerm t t′ → SameObs t t′
term⇒obs (same e) = same λ _ b → eval-cong (∘-resp-≈ e ≈-Term-refl) b

ℰᵒᵇˢ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids 0ℓ 0ℓ)
ℰᵒᵇˢ = record
  { F₀ = λ A → record
    { Carrier = Test A ; _≈_ = SameObs
    ; isEquivalence = record
      { refl  = same λ _ _ → ⇔.refl
      ; sym   = λ { (same h) → same λ m b → ⇔.sym (h m b) }
      ; trans = λ { (same h) (same h′) → same λ m b → ⇔.trans (h m b) (h′ m b) } } }
  ; F₁ = λ f → record
    { to   = pullᵗ f
    ; cong = λ { (same h) → same λ m b →
        ⇔.trans (eval-cong assoc b) (⇔.trans (h _ b) (eval-cong (≈-Term-sym assoc) b)) } }
  ; identity     = term⇒obs (Functor.identity ℰᵗ)
  ; homomorphism = term⇒obs (Functor.homomorphism ℰᵗ)
  ; F-resp-≈     = λ e → term⇒obs (Functor.F-resp-≈ ℰᵗ e)
  }

ℰˢʸᵐ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰˢʸᵐ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵒᵇˢ

module Sym = StdUC 𝔻𝕐 ℰˢʸᵐ

------------------------------------------------------------------------
-- The kernel

-- A test on `Z ⊗₀ C` with ancilla `Y` is the test `(Y ⊗₀ Z , T ∘ α⇒)` on `C`.
regroup : (T : HomTerm (Y ⊗₀ (Z ⊗₀ C)) (Var verdict)) (h : HomTerm B C) (m : Closure (Y ⊗₀ (Z ⊗₀ B)))
        → ((T ∘ α⇒) ∘ id ⊗₁ h) ∘ (α⇐ ∘ m) ≈Term (T ∘ id ⊗₁ (id ⊗₁ h)) ∘ m
regroup T h m = begin
  ((T ∘ α⇒) ∘ id ⊗₁ h) ∘ (α⇐ ∘ m)      ≈⟨ assoc ○ assoc ⟩
  T ∘ α⇒ ∘ id ⊗₁ h ∘ α⇐ ∘ m             ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ (⟺ assoc))) ○ (refl⟩∘⟨ (⟺ assoc)) ⟩
  T ∘ (α⇒ ∘ id ⊗₁ h ∘ α⇐) ∘ m           ≈⟨ refl⟩∘⟨ (conj ⟩∘⟨refl) ⟩
  T ∘ id ⊗₁ (id ⊗₁ h) ∘ m               ≈⟨ ⟺ assoc ⟩
  (T ∘ id ⊗₁ (id ⊗₁ h)) ∘ m             ∎
  where
  conj : α⇒ ∘ id ⊗₁ h ∘ α⇐ ≈Term id ⊗₁ (id ⊗₁ h)
  conj = (refl⟩∘⟨ (⊗-resp-≈ (⟺ id⊗id≈id) ≈-Term-refl ⟩∘⟨refl)) ○ α-conj id id h

grade-stable : Sym.GradeStable
grade-stable Z {h} {h′} e = Sym.KE.mk∼ λ { {lift (Y , T)} → lift (same λ m b →
  ⇔.trans (eval-cong (≈-Term-sym (regroup T h m)) b)
    (⇔.trans (same⁻¹ (lower (Sym.KE.run∼ e {lift (Y ⊗₀ Z , T ∘ α⇒)})) (α⇐ ∘ m) b)
      (eval-cong (regroup T h′ m) b))) }

≈ᵁ⇔≈ℰ : {X : ObjTerm} {f g : HomTerm A (X ⊗₀ B)} → f Sym.≈ᵁ g ⇔ f Sym.≈ℰ g
≈ᵁ⇔≈ℰ = mk⇔ Sym.≈ᵁ⇒≈ℰ (Sym.bridge grade-stable)

-- Leaves that run alike at every name supply are kernel-equal: occurrences are
-- counted by shape, so one naming serves both circuits.
leaf-≈ℰ : {x y : ObjTerm} {p q : UnitFree x × UnitFree y × Role x y}
        → (∀ κ → leafᵒ p κ G.≈ leafᵒ q κ) → var p Sym.≈ℰ var q
leaf-≈ℰ h = Sym.KE.mk∼ λ { {lift (_ , T)} → lift (same λ m b →
  mk⇔ (across h) (across λ κ → G.Equiv.sym (h κ))) }
  where
  across : {x y : ObjTerm} {p q : UnitFree x × UnitFree y × Role x y}
         {T : HomTerm (Y ⊗₀ y) (Var verdict)} {m : Closure (Y ⊗₀ x)} {b : Bool}
       → (∀ κ → leafᵒ p κ G.≈ leafᵒ q κ) → eval ((T ∘ id ⊗₁ var p) ∘ m) b → eval ((T ∘ id ⊗₁ var q) ∘ m) b
  across h (named ι inj o) =
    named ι inj (obs-resp (G.∘-resp-≈ˡ (G.∘-resp-≈ʳ (G.⊗.F-resp-≈ (G.Equiv.refl , G.Equiv.sym (h _))))) ⟨≈⟩ o)

------------------------------------------------------------------------
-- From `Sym≅`

coarse : PresheafMorphism idF ℰ≅ ℰˢʸᵐ
coarse = record { ν = ntHelper record
  { η = λ _ → record { to = λ t → t ; cong = λ { (lift s) → lift (term⇒obs s) } }
  ; commute = λ _ → Setoid.refl (Functor.₀ ℰˢʸᵐ _) } }

coarse-epi : PresheafMorphism.Epi coarse
coarse-epi t = t , Setoid.refl (Functor.₀ ℰˢʸᵐ _)

fine→sym : UCSetupMorphism Sym≅.StdSetup Sym.StdSetup
fine→sym = changeKernel ℰ≅ ℰˢʸᵐ coarse
