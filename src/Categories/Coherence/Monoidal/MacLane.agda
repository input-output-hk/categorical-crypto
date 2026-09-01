{-# OPTIONS --safe --without-K #-}

module Categories.Coherence.Monoidal.MacLane where

--------------------------------------------------------------------------------
-- Mac Lane coherence for the FREE monoidal category (no generating
-- morphisms: `mor = λ _ _ → ⊥`, so every morphism is a composite of
-- structural isos).  `CoherenceThm.all-Comm` proves any two parallel
-- such morphisms are equal, via the normal-form functor `Nf` and the
-- natural iso `Nf≅id`; `Solver.solveM` discharges `⟦ f ⟧₁ ≈ ⟦ g ⟧₁` in any
-- target MonoidalCategory.  Monoidal coherence only, no braiding/symmetry.
--------------------------------------------------------------------------------

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Product
open import Categories.Functor as F hiding (id)
open import Categories.Functor.Bifunctor
open import Categories.Morphism
open import Categories.NaturalTransformation.NaturalIsomorphism as NI hiding (refl; trans; unitorˡ; unitorʳ; associator)
open import Categories.NaturalTransformation.NaturalIsomorphism.Properties

open import Categories.Discrete
open import Categories.FreeMonoidal
open import Categories.NaturalTransformationHelper
open import Categories.Properties

open import Data.Empty
open import Data.Fin hiding (_≟_)
open import Data.List using (List; []; _∷_)
import Data.List.Properties.Ext as ListExt
open import Data.Product
open import Data.Vec using (Vec; lookup)

open import Relation.Binary.Definitions
open import Class.DecEq
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst)
import Relation.Binary.Reasoning.Setoid as SetoidR

module CoherenceThm (X : Set) ⦃ _ : DecEq X ⦄ where
  open FreeMonoidal (record { v = Mon ; X = X ; mor = λ _ _ → ⊥ })

  open Commutation FreeMonoidal
  open Discrete (List X)

  -- UIP for the discrete-category objects `List X`, derived from decidable
  -- equality of `X` (Hedberg).
  private
    uipL : Irrelevant {A = List X} _≡_
    uipL = ListExt.≡-irrelevant _≟_

  private module FM where
    open Category FreeMonoidal public
    open Monoidal Monoidal-FreeMonoidal public
    open import Categories.Category.Monoidal.Utilities Monoidal-FreeMonoidal public
    open Shorthands public
    open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal public

  private module FMReasoning where
    open import Categories.Category.Monoidal.Reasoning Monoidal-FreeMonoidal public

  ⟦_⟧ : ObjTerm → List X → List X
  ⟦ unit ⟧ n = n
  ⟦ t ⊗₀ t₁ ⟧ n = ⟦ t ⟧ (⟦ t₁ ⟧ n)
  ⟦ Var x ⟧ n = x ∷ n

  hom⇒≡⟦⟧' : ∀ {A B x y} → HomTerm A B → x ≡ y → ⟦ A ⟧ x ≡ ⟦ B ⟧ y
  hom⇒≡⟦⟧' id refl = refl
  hom⇒≡⟦⟧' (h ∘ h') eq = trans (hom⇒≡⟦⟧' h' eq) (hom⇒≡⟦⟧' h refl)
  hom⇒≡⟦⟧' (h ⊗₁ h') eq = hom⇒≡⟦⟧' h (hom⇒≡⟦⟧' h' eq)
  hom⇒≡⟦⟧' λ⇒ refl = refl
  hom⇒≡⟦⟧' λ⇐ refl = refl
  hom⇒≡⟦⟧' ρ⇒ refl = refl
  hom⇒≡⟦⟧' ρ⇐ refl = refl
  hom⇒≡⟦⟧' α⇒ refl = refl
  hom⇒≡⟦⟧' α⇐ refl = refl

  -- the normalization bifunctor's action; `private` since `⟦_⟧₁` clashes with
  -- the FreeFunctor `⟦_⟧₁` the Solver re-exports.
  private
    ⟦_⟧₀ : ObjTerm × List X → List X
    ⟦_⟧₀ = uncurry ⟦_⟧
    ⟦_⟧₁ : ∀ {A B x y} → HomTerm A B × x ≡ y → ⟦ A ⟧ x ≡ ⟦ B ⟧ y
    ⟦_⟧₁ = uncurry hom⇒≡⟦⟧'

  private
    ι₀ : Discrete .Category.Obj → FreeMonoidal .Category.Obj
    ι₀ [] = unit
    ι₀ (x ∷ []) = Var x
    ι₀ (x ∷ x₁ ∷ x₂) = Var x ⊗₀ ι₀ (x₁ ∷ x₂)

    ι₁ : ∀ {A B} → Discrete [ A , B ] → FreeMonoidal [ ι₀ A , ι₀ B ]
    ι₁ refl = id

  opaque
    ⟦_⟧F : Bifunctor FreeMonoidal Discrete Discrete
    ⟦_⟧F = record { F₀ = ⟦_⟧₀ ; F₁ = ⟦_⟧₁ ; identity = _ ; homomorphism = _ ; F-resp-≈ = λ _ → _ }

    ι : Functor Discrete FreeMonoidal
    ι = record
      { F₀ = ι₀
      ; F₁ = ι₁
      ; identity = FM.Equiv.refl
      ; homomorphism = λ where {_} {_} {_} {refl} {refl} → FM.HomReasoning.⟺ FM.identityˡ
      ; F-resp-≈ = λ {_} {_} {f} {g} _ →
          subst (λ h → FM._≈_ (ι₁ f) (ι₁ h)) (uipL f g) FM.Equiv.refl
      }

  private
    Nf : Functor FreeMonoidal Discrete
    Nf = appʳ ⟦_⟧F []

  private module C where
    open import Categories.Category.Construction.Core FreeMonoidal public
    open Category Core public

  private
    F1 F2 : Bifunctor FreeMonoidal Discrete FreeMonoidal
    F1 = FM.⊗ ∘F (F.id ⁂ ι)
    F2 = ι ∘F ⟦_⟧F

  opaque
    unfolding ⟦_⟧F
    -- making the termination checker happy
    iso' : (x : ObjTerm) → (y : List X) → C.Core [ Functor.₀ F1 (x , y) , Functor.₀ F2 (x , y) ]
    iso' unit n = FM.unitorˡ
    iso' (a ⊗₀ b) n = iso' a (⟦ b ⟧ n) C.∘ (≅.refl _ FM.⊗ᵢ iso' b n) C.∘ FM.associator
    iso' (Var x) [] = FM.unitorʳ
    iso' (Var x) (x₁ ∷ n) = ≅.refl _

    iso : (X : ObjTerm × List X) → C.Core [ Functor.₀ F1 X , Functor.₀ F2 X ]
    iso = uncurry iso'

    iso₁ : (X : ObjTerm × List X) → FreeMonoidal [ Functor.₀ F1 X , Functor.₀ F2 X ]
    iso₁ X = _≅_.from (iso X)

  private
    P = Product FreeMonoidal Discrete

  module _ where opaque
    unfolding ⟦_⟧F ι iso
    open FMReasoning
    open import Categories.Morphism.Reasoning FreeMonoidal

    iso-comm-ty : Set
    iso-comm-ty = ∀ {A} {d₁} {d₂} {g : d₁ ≡ d₂}
           → iso₁ (A , d₂) ∘ id ⊗₁ ι₁ g
        FM.≈ ι₁ (hom⇒≡⟦⟧' (id {A}) g) ∘ iso₁ (A , d₁)

    iso-comm : iso-comm-ty
    iso-comm {g = refl} = elimʳ FM.⊗.identity ○ ⟺ idˡ

    -- the proof never inspects the left factor `e`, so it need not be an iso₁.
    cancel-⊗ˡ : ∀ {B C Z W} {e : HomTerm (C ⊗₀ Z) W} {f⇒ : HomTerm B C} {f⇐ : HomTerm C B}
      → f⇒ ∘ f⇐ FM.≈ id
      → e ∘ f⇒ ⊗₁ id ∘ f⇐ ⊗₁ id FM.≈ id ∘ e
    cancel-⊗ˡ isoR = refl⟩∘⟨ (merge₁ˡ ○ isoR ⟩⊗⟨refl ○ FM.⊗.identity) ○ id-comm

    -- Naturality of the inverse from naturality of the forward iso.  Like
    -- pentagon-conj/⊗-conj it is iso₁-independent, so its stored intermediates
    -- stay variable-sized.
    nat-inv : ∀ {B C Z W} {e₁ : HomTerm (C ⊗₀ Z) W} {e₂ : HomTerm (B ⊗₀ Z) W}
                {f⇒ : HomTerm B C} {f⇐ : HomTerm C B}
            → e₁ ∘ f⇒ ⊗₁ id FM.≈ id ∘ e₂
            → f⇒ ∘ f⇐ FM.≈ id
            → e₂ ∘ f⇐ ⊗₁ id FM.≈ id ∘ e₁
    nat-inv fwd isoR = (⟺ idˡ ⟩∘⟨refl ○ ⟺ fwd ⟩∘⟨refl ○ assoc) ○ cancel-⊗ˡ isoR

    ι-∘ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
        → ι₁ ⟦ f , ⟦ g , refl ⟧₁ ⟧₁
          FM.≈ ι₁ ⟦ id {A = B} , ⟦ g , refl ⟧₁ ⟧₁ ∘ ι₁ ⟦ f , refl {x = ⟦ C ⟧ d} ⟧₁
    ι-∘ d f g = begin
      ι₁ ⟦ f , ⟦ g , refl ⟧₁ ⟧₁
        ≈⟨ ι.F-resp-≈ _ ⟩
      ι₁ (⟦ id , ⟦ g , refl ⟧₁ ⟧₁ D.∘ ⟦ f , refl ⟧₁)
        ≈⟨ ι.homomorphism ⟩
      ι₁ ⟦ id , ⟦ g , refl ⟧₁ ⟧₁ ∘ ι₁ ⟦ f , refl ⟧₁ ∎
      where module ι = Functor ι
            module D = Category Discrete

    natural-id : ∀ {X} → iso₁ X ∘ Functor.F₁ F1 (id , refl) FM.≈ Functor.F₁ F2 (id , refl) ∘ iso₁ X
    natural-id = iso-comm

    natural-∘ : ∀ {A B C} d (g : HomTerm B C) (f : HomTerm A B)
      → iso₁ (C , d) ∘ Functor.F₁ F1 (g , refl) FM.≈ Functor.F₁ F2 (g , refl) ∘ iso₁ (B , d)
      → iso₁ (B , d) ∘ Functor.F₁ F1 (f , refl) FM.≈ Functor.F₁ F2 (f , refl) ∘ iso₁ (A , d)
      → iso₁ (C , d) ∘ Functor.F₁ F1 (g ∘ f , refl) FM.≈ Functor.F₁ F2 (g ∘ f , refl) ∘ iso₁ (A , d)
    natural-∘ {A} {B} {C} d g f Hg Hf = begin
      iso₁ (C , d) ∘ Functor.F₁ F1 (g ∘ f , refl)
        ≈⟨ refl⟩∘⟨ Functor.homomorphism F1 ⟩
      iso₁ (C , d) ∘ Functor.F₁ F1 (g , refl) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ extendʳ Hg ⟩
      Functor.F₁ F2 (g , refl) ∘ iso₁ (B , d) ∘ Functor.F₁ F1 (f , refl)
        ≈⟨ refl⟩∘⟨ Hf ⟩
      Functor.F₁ F2 (g , refl) ∘ Functor.F₁ F2 (f , refl) ∘ iso₁ (A , d)
        ≈⟨ pullˡ (⟺ (Functor.homomorphism F2 {f = f , refl} {g = g , refl})) ⟩
      Functor.F₁ F2 (g ∘ f , refl) ∘ iso₁ (A , d) ∎

    natural-⊗ : ∀ {A B C D} d (f : HomTerm A B) (g : HomTerm C D)
      → iso₁ (B , ⟦ C ⟧ d) ∘ Functor.F₁ F1 (f , refl) FM.≈ Functor.F₁ F2 (f , refl) ∘ iso₁ (A , ⟦ C ⟧ d)
      → iso₁ (D , d) ∘ Functor.F₁ F1 (g , refl) FM.≈ Functor.F₁ F2 (g , refl) ∘ iso₁ (C , d)
      → iso₁ (B ⊗₀ D , d) ∘ Functor.F₁ F1 (f ⊗₁ g , refl) FM.≈ Functor.F₁ F2 (f ⊗₁ g , refl) ∘ iso₁ (A ⊗₀ C , d)
    -- Everything iso₁/ι₁-specific enters through the four hypotheses, so the
    -- chain's stored intermediates are over variables.
    ⊗-conj : ∀ {A B C D N P P' Q Q' Q''}
             {f : HomTerm A B} {g : HomTerm C D}
             {e' : HomTerm (C ⊗₀ N) P} {e : HomTerm (D ⊗₀ N) P'}
             {a : HomTerm (B ⊗₀ P') Q'} {a' : HomTerm (B ⊗₀ P) Q}
             {iA : HomTerm (A ⊗₀ P) Q''}
             {u : HomTerm P P'} {v : HomTerm Q Q'} {w : HomTerm Q'' Q}
             {z : HomTerm Q'' Q'}
           → a' ∘ f ⊗₁ id FM.≈ w ∘ iA
           → e ∘ g ⊗₁ id FM.≈ u ∘ e'
           → a ∘ id ⊗₁ u FM.≈ v ∘ a'
           → z FM.≈ v ∘ w
           → (a ∘ id ⊗₁ e ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ id
          FM.≈ z ∘ iA ∘ id ⊗₁ e' ∘ α⇒
    ⊗-conj Hf Hg Hcomm Hfuse =
      (assoc²βε ○ refl⟩∘⟨ refl⟩∘⟨ FM.assoc-commute-from ○ refl⟩∘⟨ ⟺ assoc)
        ○ refl⟩∘⟨ (merge₂ˡ ○ (refl⟩⊗⟨ Hg) ○ split₂ˡ) ⟩∘⟨refl
        ○ assoc²δγ
        ○ Hcomm ⟩∘⟨refl
        ○ refl⟩∘⟨ pushˡ serialize₁₂
        ○ (assoc ○ refl⟩∘⟨ ⟺ assoc)
        ○ refl⟩∘⟨ Hf ⟩∘⟨refl
        ○ assoc²δγ
        ○ ⟺ Hfuse ⟩∘⟨refl

    natural-⊗ d f g Hf Hg = ⊗-conj Hf Hg iso-comm (ι-∘ d f g)

    natural-λ⇒ : ∀ {A d}
               → iso₁ (A , d) ∘ Functor.F₁ F1 (λ⇒ , refl)
            FM.≈ Functor.F₁ F2 (λ⇒ , refl) ∘ iso₁ (unit ⊗₀ A , d)
    natural-λ⇒ {A} {d} = begin
      iso₁ (A , d) ∘ λ⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.coherence₁ ⟩
      iso₁ (A , d) ∘ λ⇒ ∘ α⇒
        ≈⟨ ⟺ assoc ⟩
      (iso₁ (A , d) ∘ λ⇒) ∘ α⇒
        ≈⟨ ⟺ FM.unitorˡ-commute-from ⟩∘⟨refl ⟩
      (λ⇒ ∘ id ⊗₁ iso₁ (A , d)) ∘ α⇒
        ≈⟨ assoc ○ (⟺ idˡ) ⟩
      id ∘ λ⇒ ∘ id ⊗₁ iso₁ (A , d) ∘ α⇒ ∎

    natural-λ⇐ : ∀ {A d}
               → iso₁ (unit ⊗₀ A , d) ∘ Functor.F₁ F1 (λ⇐ , refl)
            FM.≈ Functor.F₁ F2 (λ⇐ , refl) ∘ iso₁ (A , d)
    natural-λ⇐ = nat-inv natural-λ⇒ FM.unitorˡ.isoʳ

    natural-ρ⇒ : ∀ {A d}
               → iso₁ (A , d) ∘ Functor.F₁ F1 (ρ⇒ , refl)
            FM.≈ Functor.F₁ F2 (ρ⇒ , refl) ∘ iso₁ (A ⊗₀ unit , d)
    natural-ρ⇒ {A} {d} = begin
      iso₁ (A , d) ∘ ρ⇒ ⊗₁ id
        ≈⟨ refl⟩∘⟨ ⟺ FM.triangle ⟩
      iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒
        ≈⟨ ⟺ idˡ ⟩
      id ∘ iso₁ (A , d) ∘ id ⊗₁ λ⇒ ∘ α⇒ ∎

    natural-ρ⇐ : ∀ {A d}
               → iso₁ (A ⊗₀ unit , d) ∘ Functor.F₁ F1 (ρ⇐ , refl)
            FM.≈ Functor.F₁ F2 (ρ⇐ , refl) ∘ iso₁ (A , d)
    natural-ρ⇐ = nat-inv natural-ρ⇒ FM.unitorʳ.isoʳ

    -- Nothing about iso₁ is used beyond its type; keeping a/b/c as variables
    -- keeps the stored intermediates small (the module's interface-size
    -- hotspot).
    pentagon-conj : ∀ {A B C N P Q R}
             (a : HomTerm (A ⊗₀ Q) R) (b : HomTerm (B ⊗₀ P) Q) (c : HomTerm (C ⊗₀ N) P)
           → (a ∘ id ⊗₁ (b ∘ id ⊗₁ c ∘ α⇒) ∘ α⇒) ∘ α⇒ ⊗₁ id
          FM.≈ id ∘ (a ∘ id ⊗₁ b ∘ α⇒) ∘ id ⊗₁ c ∘ α⇒
    pentagon-conj {A} a b c =
      assoc²βε
        ○ refl⟩∘⟨ ( Functor.homomorphism (A FM.⊗-) ⟩∘⟨refl
                  ○ (refl⟩∘⟨ Functor.homomorphism (A FM.⊗-)) ⟩∘⟨refl
                  ○ assoc²βε )
        ○ ⟺ assoc
        ○ refl⟩∘⟨ ( refl⟩∘⟨ FM.pentagon
                  ○ ⟺ assoc
                  ○ ⟺ FM.assoc-commute-from ⟩∘⟨refl
                  ○ (refl⟩∘⟨ FM.⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl
                  ○ assoc )
        ○ assoc ○ ⟺ assoc²βε ○ ⟺ idˡ

    natural-α⇒ : ∀ {A B C d}
               → iso₁ (A ⊗₀ B ⊗₀ C , d) ∘ Functor.F₁ F1 (α⇒ , refl)
            FM.≈ Functor.F₁ F2 (α⇒ , refl) ∘ iso₁ ((A ⊗₀ B) ⊗₀ C , d)
    natural-α⇒ {A} {B} {C} {d} = pentagon-conj (iso₁ (A , ⟦ B ⟧ (⟦ C ⟧ d))) (iso₁ (B , ⟦ C ⟧ d)) (iso₁ (C , d))

    natural-α⇐ : ∀ {A B C d}
               → iso₁ ((A ⊗₀ B) ⊗₀ C , d) ∘ Functor.F₁ F1 (α⇐ , refl)
            FM.≈ Functor.F₁ F2 (α⇐ , refl) ∘ iso₁ (A ⊗₀ B ⊗₀ C , d)
    natural-α⇐ = nat-inv natural-α⇒ FM.associator.isoʳ

  private
    natural₁ : ∀ d {X Y} (f : FreeMonoidal [ X , Y ])
             → FreeMonoidal [ FreeMonoidal [ iso₁ (Y , d) ∘ Functor.F₁ F1 (f , refl) ]
                            ≈ FreeMonoidal [ Functor.F₁ F2 (f , refl) ∘ iso₁ (X , d) ] ]
    natural₁ d id = natural-id
    natural₁ d (g ∘ f) = natural-∘ _ g f (natural₁ _ g) (natural₁ _ f)
    natural₁ d (f ⊗₁ g) = natural-⊗ _ f g (natural₁ _ f) (natural₁ _ g)
    natural₁ d λ⇒ = natural-λ⇒
    natural₁ d λ⇐ = natural-λ⇐
    natural₁ d ρ⇒ = natural-ρ⇒
    natural₁ d ρ⇐ = natural-ρ⇐
    natural₁ d α⇒ = natural-α⇒
    natural₁ d α⇐ = natural-α⇐

  opaque
    unfolding iso₁
    ⟦⟧≅⊗ : NaturalIsomorphism F2 F1
    ⟦⟧≅⊗ = NI.sym (pointwise-iso iso natural)
      where
        natural : ∀ {X Y} → (f : P [ X , Y ]) → FreeMonoidal [ iso₁ Y ∘ Functor.₁ F1 f ≈ Functor.₁ F2 f ∘ iso₁ X ]
        natural = natural-components F1 F2 iso₁ natural₁
          (λ c → Discrete-NaturalD {F = appˡ F1 c} {appˡ F2 c} (λ d → iso₁ (c , d)))

  opaque
    unfolding ι
    Nf≅id : NaturalIsomorphism (ι ∘F Nf) F.id
    Nf≅id = begin
      ι ∘F Nf ≈⟨ NI.associator (-× []) ⟦_⟧F ι ⟨
      (ι ∘F ⟦_⟧F) ∘F -× [] ≈⟨ ⟦⟧≅⊗ ⓘʳ (-× []) ⟩
      (FM.⊗ ∘F (F.id ⁂ ι)) ∘F -× [] ≈⟨ NI.associator (-× []) (F.id ⁂ ι) FM.⊗ ⟩
      FM.⊗ ∘F (F.id ⁂ ι) ∘F (-× []) ≈⟨ FM.⊗ ⓘˡ (⁂-× ι []) ⟩
      appʳ FM.⊗ unit ≈⟨ FM.unitorʳ-naturalIsomorphism ⟩
      F.id ∎
      where open SetoidR (Functor-NI-setoid FreeMonoidal FreeMonoidal)

  all-Comm : ∀ {A B} f g → [ A ⇒ B ]⟨ f ≈ g ⟩
  all-Comm f g = push-eq Nf≅id (ι.F-resp-≈ _)
    where module ι = Functor ι

module Solver {o ℓ e} (C : MonoidalCategory o ℓ e)
              {n} (vars : Vec (C .MonoidalCategory.Obj) n) where
  open MonoidalCategory
  private
    d : FreeMonoidalData
    d = record { v = Mon ; X = Fin n ; mor = λ _ _ → ⊥ }
  open FreeMonoidal d public
  open CoherenceThm (Fin n)
  open FreeFunctor {d = d} record { ⟦v⟧ = fromMC C noSymmetric ; ⟦_⟧ᵖ₀ = lookup vars ; ⟦_⟧ᵖ₁ = λ () } public

  opaque
    solveM : ∀ {X Y} → (f g : FreeMonoidal [ X , Y ]) → (C .U) [ ⟦ f ⟧₁ ≈ ⟦ g ⟧₁ ]
    solveM f g = Functor.F-resp-≈ freeFunctor (all-Comm f g)
  {-# INJECTIVE_FOR_INFERENCE solveM #-}
