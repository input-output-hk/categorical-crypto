{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.UCSetup where

open import Level
open import Relation.Binary.Bundles

import Categories.KernelCongruence as KernelCong
import Categories.Monad.Graded.Ext as GradedExt
import Categories.Morphism.Reasoning as MR
open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Categories.Functor.Properties
open import Categories.Monad.Graded
open import Function.Bundles

record UCSetup (o ℓ e o′ ℓ′ e′ cs ℓs : Level) : Set (suc (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′ ⊔ cs ⊔ ℓs)) where
  field
    𝒞 : Category o′ ℓ′ e′
    ℐ : MonoidalCategory o ℓ e
    ℳ : GradedKleisliTriple ℐ 𝒞
    ℰ : Presheaf 𝒞 (Setoids cs ℓs)

  module 𝒞 where
    open Category 𝒞 public
    open HomReasoning public
    open MR 𝒞 public
  module ℐ = MonoidalCategory ℐ
  open GradedKleisliTriple ℳ public
  open GradedExt ℳ public
  open import Categories.Category.Monoidal.Utilities ℐ.monoidal public
  open Shorthands public

  open ℐ using (_⊗₀_; _⊗₁_) public

  -- 𝓔-observational equivalence
  module KE = KernelCong 𝒞.op (Setoids cs ℓs) ℰ

  open KE using () renaming
    ( _∼_ to _≈ℰ_; ∼-refl to ≈ℰ-refl; ∼-sym to ≈ℰ-sym; ∼-trans to ≈ℰ-trans
    ; ≈⇒∼ to ≈C⇒≈ℰ; ∼-congˡ to ≈ℰ-cong-pre; ∼-congʳ to ≈ℰ-cong-post ) public

  ≈ℰ-setoid : (A B : 𝒞.Obj) → Setoid ℓ′ (cs ⊔ ℓs)
  ≈ℰ-setoid A B = KE.∼-setoid B A

  private module E = Functor ℰ

  private variable
    A B C D D′ D″ : 𝒞.Obj
    W P X X′ Y : ℐ.Obj

  infixr 9 _∙_
  _∙_ : B 𝒞.⇒ T₀ Y C → A 𝒞.⇒ T₀ X B → A 𝒞.⇒ T₀ (X ⊗₀ Y) C
  h ∙ f = ext _ h 𝒞.∘ f

  ∙-return : (h : B 𝒞.⇒ T₀ X C) (w : A 𝒞.⇒ B)
           → sub λ⇒ 𝒞.∘ (h ∙ (return 𝒞.∘ w)) 𝒞.≈ h 𝒞.∘ w
  ∙-return h w = let open 𝒞 in begin
      sub λ⇒ ∘ ext ℐ.unit h ∘ return ∘ w    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      sub λ⇒ ∘ (ext ℐ.unit h ∘ return) ∘ w  ≈⟨ sym-assoc ⟩
      (sub λ⇒ ∘ ext ℐ.unit h ∘ return) ∘ w  ≈⟨ ext-identityʳ ⟩∘⟨refl ⟩
      h ∘ w                                 ∎

  ∙-decomp : (h : B 𝒞.⇒ T₀ P C) (f : A 𝒞.⇒ T₀ X B) (W : ℐ.Obj)
           → μ W (X ⊗₀ P) 𝒞.∘ T₁ W (h ∙ f)
             𝒞.≈ (sub α⇒ 𝒞.∘ ext (W ⊗₀ X) h) 𝒞.∘ μ W X 𝒞.∘ T₁ W f
  ∙-decomp {P = P} {X = X} h f W = let open 𝒞 in begin
      μ W (X ⊗₀ P) ∘ T₁ W (ext X h ∘ f)
        ≈⟨ refl⟩∘⟨ T-homomorphism ⟩
      μ W (X ⊗₀ P) ∘ T₁ W (ext X h) ∘ T₁ W f
        ≈⟨ sym-assoc ⟩
      (μ W (X ⊗₀ P) ∘ T₁ W (ext X h)) ∘ T₁ W f
        ≈⟨ μT (ext X h) ⟩∘⟨refl ⟩
      ext W (ext X h) ∘ T₁ W f
        ≈⟨ extassoc ⟩∘⟨refl ⟩
      (sub α⇒ ∘ ext (W ⊗₀ X) h ∘ μ W X) ∘ T₁ W f
        ≈⟨ sym-assoc ⟩∘⟨refl ⟩
      ((sub α⇒ ∘ ext (W ⊗₀ X) h) ∘ μ W X) ∘ T₁ W f
        ≈⟨ assoc ⟩
      (sub α⇒ ∘ ext (W ⊗₀ X) h) ∘ μ W X ∘ T₁ W f  ∎
    where extassoc : ext W (ext X h) 𝒞.≈ sub α⇒ 𝒞.∘ ext (W ⊗₀ X) h 𝒞.∘ μ W X
          extassoc = let open 𝒞 in ⟺ (ext-resp-≈ identityʳ) ○ ext-assoc

  sub-decomp : (c : X ℐ.⇒ X′) (x : A 𝒞.⇒ T₀ X B) (Y : ℐ.Obj)
             → μ Y X′ 𝒞.∘ T₁ Y (sub c 𝒞.∘ x) 𝒞.≈ sub (ℐ.id ⊗₁ c) 𝒞.∘ μ Y X 𝒞.∘ T₁ Y x
  sub-decomp {X = X} {X′} c x Y = let open 𝒞 in begin
      μ Y X′ ∘ T₁ Y (sub c ∘ x)              ≈⟨ refl⟩∘⟨ T-homomorphism ⟩
      μ Y X′ ∘ T₁ Y (sub c) ∘ T₁ Y x         ≈⟨ sym-assoc ⟩
      (μ Y X′ ∘ T₁ Y (sub c)) ∘ T₁ Y x       ≈⟨ μst ⟩∘⟨refl ⟩
      (sub (ℐ.id ⊗₁ c) ∘ μ Y X) ∘ T₁ Y x     ≈⟨ assoc ⟩
      sub (ℐ.id ⊗₁ c) ∘ μ Y X ∘ T₁ Y x       ∎
    where μst : μ Y X′ 𝒞.∘ T₁ Y (sub c) 𝒞.≈ sub (ℐ.id ⊗₁ c) 𝒞.∘ μ Y X
          μst = let open 𝒞 in (refl⟩∘⟨ introʳ sub-identity) ○ μ-sub-commute

  ------------------------------------------------------------------------
  -- Environments

  Env : 𝒞.Obj → Set cs
  Env D = Setoid.Carrier (E.F₀ D)

  module Env {D} = Setoid (E.F₀ D)

  pull : D 𝒞.⇒ D′ → Env D′ → Env D
  pull h e = E.F₁ h ⟨$⟩ e

  pull-cong : (h : D 𝒞.⇒ D′) {u v : Env D′} → u Env.≈ v → pull h u Env.≈ pull h v
  pull-cong h = Func.cong (E.F₁ h)

  pull-resp-≈ : {h k : D 𝒞.⇒ D′} → h 𝒞.≈ k → (e : Env D′) → pull h e Env.≈ pull k e
  pull-resp-≈ eq _ = E.F-resp-≈ eq

  pull-∘ : (v : D′ 𝒞.⇒ D″) (u : D 𝒞.⇒ D′) (e : Env D″)
         → pull (v 𝒞.∘ u) e Env.≈ pull u (pull v e)
  pull-∘ _ _ _ = E.homomorphism

  ------------------------------------------------------------------------
  -- The action on graded morphisms

  prefix : (W : ℐ.Obj) → A 𝒞.⇒ T₀ X B → T₀ W A 𝒞.⇒ T₀ (W ⊗₀ X) B
  prefix {X = X} W f = μ W X 𝒞.∘ T₁ W f

  run : (W : ℐ.Obj) (f : A 𝒞.⇒ T₀ X B) → Env (T₀ (W ⊗₀ X) B) → Env (T₀ W A)
  run W f e = pull (prefix W f) e

  regradeEnv : (W : ℐ.Obj) (s : Y ℐ.⇒ X) → Env (T₀ (W ⊗₀ X) B) → Env (T₀ (W ⊗₀ Y) B)
  regradeEnv W s e = pull (sub (ℐ.id ⊗₁ s)) e

  run-sub : (W : ℐ.Obj) (s : Y ℐ.⇒ X) (g : A 𝒞.⇒ T₀ Y B) (e : Env (T₀ (W ⊗₀ X) B))
          → run W (sub s 𝒞.∘ g) e Env.≈ run W g (regradeEnv W s e)
  run-sub W s g e = Env.trans (pull-resp-≈ (sub-decomp s g W) e)
                               (pull-∘ (sub (ℐ.id ⊗₁ s)) (prefix W g) e)
  ------------------------------------------------------------------------
  -- GradeStable

  GradeStable : Set (o ⊔ o′ ⊔ ℓ′ ⊔ cs ⊔ ℓs)
  GradeStable = ∀ {B C′} (Y : ℐ.Obj) {h h′ : B 𝒞.⇒ C′} → h ≈ℰ h′ → T₁ Y h ≈ℰ T₁ Y h′

  -- A faithful ℰ collapses `_≈ℰ_` to 𝒞-equality
  faithful⇒grade-stable : Faithful ℰ → GradeStable
  faithful⇒grade-stable faithful _ e = ≈C⇒≈ℰ (T-resp-≈ (KE.∼⇒≈ faithful e))

  -- `GradeStable` whenever the kernel is generated by a conjugation-closed
  -- relation _≋_ and μ has a retraction θ.
  module GradeStableFromTests {r : Level}
    (_≋_ : {A B : 𝒞.Obj} → A 𝒞.⇒ B → A 𝒞.⇒ B → Set r)
    (≋-resp-≈ : {A B : 𝒞.Obj} {f f′ g g′ : A 𝒞.⇒ B}
              → f 𝒞.≈ f′ → g 𝒞.≈ g′ → f ≋ g → f′ ≋ g′)
    (≋-conj : {A B C′ D : 𝒞.Obj} {k : B 𝒞.⇒ C′} {l : D 𝒞.⇒ A} {f g : A 𝒞.⇒ B}
            → f ≋ g → (k 𝒞.∘ f 𝒞.∘ l) ≋ (k 𝒞.∘ g 𝒞.∘ l))
    (≋⇒ℰ : {A B : 𝒞.Obj} {h h′ : A 𝒞.⇒ B}
         → ((V : ℐ.Obj) → T₁ V h ≋ T₁ V h′) → h ≈ℰ h′)
    (ℰ⇒≋ : {A B : 𝒞.Obj} {h h′ : A 𝒞.⇒ B}
         → h ≈ℰ h′ → (V : ℐ.Obj) → T₁ V h ≋ T₁ V h′)
    (θ : {X Y : ℐ.Obj} {A : 𝒞.Obj} → T₀ (X ⊗₀ Y) A 𝒞.⇒ T₀ X (T₀ Y A))
    (θ-μ : {X Y : ℐ.Obj} {A : 𝒞.Obj} → θ 𝒞.∘ μ X Y {A} 𝒞.≈ 𝒞.id)
    where

    grade-stable : GradeStable
    grade-stable Z {h} {h′} e =
      ≋⇒ℰ λ Y → ≋-resp-≈ (absorb Y h) (absorb Y h′) (≋-conj (ℰ⇒≋ e (Y ⊗₀ Z)))
      where
      absorb : {A B : 𝒞.Obj} (Y : ℐ.Obj) (k : A 𝒞.⇒ B)
             → θ 𝒞.∘ T₁ (Y ⊗₀ Z) k 𝒞.∘ μ Y Z 𝒞.≈ T₁ Y (T₁ Z k)
      absorb _ _ = let open 𝒞 in (refl⟩∘⟨ ⟺ μ-commute) ○ cancelˡ θ-μ
