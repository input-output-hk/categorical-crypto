{-# OPTIONS --safe --without-K #-}

-- The graded Kleisli category of a graded Kleisli triple ℳ over a monoidal ℐ:
-- objects ℐ.Obj × 𝒞.Obj, and a hom (i , c) ⇒ (j , d) is a grade k together with
-- 𝒞 [ c , T₀ k d ] and ℐ.U [ i ⊗ k , j ], quotiented by the `Slide` generator
-- that moves a grade morphism between the two components.  `U-functor` is the
-- forgetful functor to 𝒞 and `F⊣U` the resulting adjunction.

module Categories.GradedKleisli where

open import Level using (Level; _⊔_) renaming (suc to lsuc)

open import Categories.Adjoint
open import Categories.Category
open import Categories.Category.EquivClosureHelper
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonR
open import Categories.Coherence.Monoidal using (module MorAtoms; module MorSolve)
open import Categories.Coherence.Monoidal.Tactic
open import Categories.Functor using (Functor)
open import Categories.Monad.Graded
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation using (NaturalTransformation; ntHelper)
open import Categories.Tactic.Category

open import Data.Fin using (#_)
open import Data.Product
open import Data.Vec using (_∷_; [])

open import Relation.Binary.Construct.Closure.Equivalence as EqC using (gfold; symmetric)

module _ {o ℓ e o′ ℓ′ e′ : Level}
  (C : Category o′ ℓ′ e′) (I : MonoidalCategory o ℓ e) (M : GradedKleisliTriple I C) where
  module C where
    open Category C public
    open HomReasoning public
    open MR C public

  module I = MonoidalCategory I
  module Iᵁ where
    open Category I.U public
    open HomReasoning public
    open MR I.U public
  open I using (_⊗₀_; _⊗₁_; -⊗_; _⊗-; associator)
  open MonR (I.monoidal) using (_⟩⊗⟨refl; _⟩⊗⟨_)
  open Functor
  open GradedKleisliTriple M
  open import Categories.Category.Monoidal.Utilities (I.monoidal)
  open import Categories.Category.Monoidal.Properties (I.monoidal) using (coherence₃)
  open import Categories.Monad.Graded.Ext M
  open Shorthands

  private
    Objᴳ : Set (o ⊔ o′)
    Objᴳ = I.Obj × C.Obj

    -- ∫^k hom_C(c, T k d) × hom_I(i ⊗ k, j), with `_≈ᴳ_` the generator of the
    -- equivalence relation
    _⇒ᴳ_ : Objᴳ → Objᴳ → Set (o ⊔ ℓ ⊔ ℓ′)
    (i , c) ⇒ᴳ (j , d) = ∃[ k ] (C [ c , T₀ k d ]) × (I.U [ i ⊗₀ k , j ])

    _≈ᴳ_ : ∀ {A B} → (A ⇒ᴳ B) → (A ⇒ᴳ B) → Set (ℓ ⊔ e ⊔ e′)
    _≈ᴳ_ {ai , _} (i , f , α) (j , g , β) =
      Σ[ φ ∈ I.U [ i , j ] ] C [ sub φ C.∘ f ≈ g ] × I.U [ β I.∘ (₁ (ai ⊗-) φ) ≈ α ]

    idᴳ : ∀ {A} → A ⇒ᴳ A
    idᴳ = I.unit , return , ρ⇒

    _∘ᴳ_ : ∀ {A B D} → (B ⇒ᴳ D) → (A ⇒ᴳ B) → (A ⇒ᴳ D)
    (j , g , β) ∘ᴳ (i , f , α) = i ⊗₀ j , g ⊙ f , β I.∘ (₁ (-⊗ j) α) I.∘ α⇐

  GradedKleisli : Category (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
  GradedKleisli = categoryHelperᵉ record
    { Obj       = Objᴳ
    ; _⇒_       = _⇒ᴳ_
    ; _≈_       = _≈ᴳ_
    ; id        = idᴳ
    ; _∘_       = _∘ᴳ_
    ; assoc     = λ where
      {Xi , _} {Yi , _} {Zi , _} {Wi , _} {a , f₀ , φf} {b , g₀ , φg} {c , h₀ , φh} →
          α⇐
        , (let open C in (refl⟩∘⟨ ⊙-assoc)
             ○ cancelˡ (⟺ sub-homomorphism ○ sub-resp-≈ associator.isoˡ ○ sub-identity))
        , solve-mor I
    ; identityˡ = λ where
      {ai , _} {B , _} {i , _ , α} →
          ρ⇒
        , ⊙-identityˡ
        , solve-mor I
    ; identityʳ = λ where
      {ai , _} {B , _} {i , _ , α} →
          λ⇒
        , ⊙-identityʳ
        , solve-mor I
    ; ∘-resp-≈ = λ where
      {Ai , _} {Bi , _} {Ci , _}
        {fk , ff , fα} {hk , hf , hα} {gk , gf , gα} {ik , if′ , iα}
        (φ , cf , ifh) (ψ , cg , igi) →
          ψ ⊗₁ φ
        , (let open C in begin
             sub (ψ ⊗₁ φ) C.∘ (ext gk ff C.∘ gf)       ≈⟨ pullˡ (⟺ sub-commute) ⟩
             (ext ik (sub φ C.∘ ff) C.∘ sub ψ) C.∘ gf  ≈⟨ C.assoc ⟩
             ext ik (sub φ C.∘ ff) C.∘ (sub ψ C.∘ gf)  ≈⟨ ext-resp-≈ cf ⟩∘⟨ cg ⟩
             ext ik hf C.∘ if′ ∎)
        , (let open Category.HomReasoning (I.U)
           in begin
             (hα I.∘ (iα ⊗₁ I.id) I.∘ α⇐) I.∘ (I.id ⊗₁ (ψ ⊗₁ φ))
               ≈⟨ solve-mor I ⟩
             (hα I.∘ I.id ⊗₁ φ) I.∘ (iα I.∘ I.id ⊗₁ ψ) ⊗₁ I.id I.∘ α⇐
               ≈⟨ ifh ⟩∘⟨ (igi ⟩⊗⟨refl ⟩∘⟨refl) ⟩
             fα I.∘ (gα ⊗₁ I.id) I.∘ α⇐ ∎)
    }

  ≈-components : ∀ {i j k : I.Obj} {c d : C.Obj} {f g : C [ c , T₀ k d ]}
                 {α β : I.U [ i ⊗₀ k , j ]} → C [ f ≈ g ] → I.U [ α ≈ β ]
               → GradedKleisli [ (k , f , α) ≈ (k , g , β) ]
  ≈-components {i} f≈g α≈β = EqC.return
    ( I.id
    , (let open C in elimˡ sub-identity ○ f≈g)
    , (let open Iᵁ in elimʳ (identity (i ⊗-)) ○ ⟺ α≈β) )

  private module K = Category GradedKleisli

  U₀ : K.Obj → C.Obj
  U₀ (i , c) = T₀ i c

  U₁ : ∀ {A B} → GradedKleisli [ A , B ] → C [ U₀ A , U₀ B ]
  U₁ {i , _} (X , f , a) = sub a C.∘ μ i X C.∘ T₁ i f

  U-resp : ∀ {A B} {x y : GradedKleisli [ A , B ]} → x K.≈ y → C [ U₁ x ≈ U₁ y ]
  U-resp p = gfold C.equiv U₁ U-slide p
    where
      U-slide : ∀ {A B} {x y : A ⇒ᴳ B} → x ≈ᴳ y → C [ U₁ x ≈ U₁ y ]
      U-slide {ai , _} {x = i , f , α} {y = j , g , β} (φ , p , q) = let open C in begin
          sub α ∘ μ ai i ∘ T₁ ai f
            ≈⟨ ⟺ (sub-resp-≈ q) ⟩∘⟨refl ⟩
          sub (β I.∘ ₁ (ai ⊗-) φ) ∘ μ ai i ∘ T₁ ai f
            ≈⟨ pushˡ sub-homomorphism ⟩
          sub β ∘ sub (₁ (ai ⊗-) φ) ∘ μ ai i ∘ T₁ ai f
            ≈⟨ refl⟩∘⟨ pullˡ crux ⟩
          sub β ∘ (μ ai j ∘ T₁ ai (sub φ)) ∘ T₁ ai f
            ≈⟨ refl⟩∘⟨ tail ⟩
          sub β ∘ μ ai j ∘ T₁ ai g ∎
        where
          crux : C [ sub (₁ (ai ⊗-) φ) C.∘ μ ai i ≈ μ ai j C.∘ T₁ ai (sub φ) ]
          crux = let open C in ⟺ μ-sub-commute ○ (refl⟩∘⟨ elimʳ sub-identity)

          tail : C [ (μ ai j C.∘ T₁ ai (sub φ)) C.∘ T₁ ai f ≈ μ ai j C.∘ T₁ ai g ]
          tail = let open C in C.assoc ○ (refl⟩∘⟨ (⟺ T-homomorphism ○ T-resp-≈ p))

  U-∘ : ∀ {A B D} (x : GradedKleisli [ B , D ]) (y : GradedKleisli [ A , B ])
      → C [ U₁ (x K.∘ y) ≈ U₁ x C.∘ U₁ y ]
  U-∘ {P , cA} {Q , cB} {R , cD} (j , g , β) (i , f , α) = let open C in begin
      sub (β I.∘ ₁ (-⊗ j) α I.∘ α⇐) ∘ μ P (i ⊗₀ j) ∘ T₁ P (ext i g ∘ f)
        ≈⟨ refl⟩∘⟨ μT (ext i g ∘ f) ⟩
      sub (β I.∘ ₁ (-⊗ j) α I.∘ α⇐) ∘ ext P (ext i g ∘ f)
        ≈⟨ refl⟩∘⟨ ext-assoc ⟩
      sub (β I.∘ ₁ (-⊗ j) α I.∘ α⇐) ∘ sub α⇒ ∘ (ext (P ⊗₀ i) g ∘ ext P f)
        ≈⟨ pullˡ (⟺ sub-homomorphism) ⟩
      sub ((β I.∘ ₁ (-⊗ j) α I.∘ α⇐) I.∘ α⇒) ∘ (ext (P ⊗₀ i) g ∘ ext P f)
        ≈⟨ sub-resp-≈ I-eq ⟩∘⟨refl ⟩
      sub (β I.∘ ₁ (-⊗ j) α) ∘ (ext (P ⊗₀ i) g ∘ ext P f)
        ≈⟨ pushˡ sub-homomorphism ⟩
      sub β ∘ sub (₁ (-⊗ j) α) ∘ ext (P ⊗₀ i) g ∘ ext P f
        ≈⟨ refl⟩∘⟨ pullˡ (⟺ sub-commute₁) ⟩
      sub β ∘ (ext Q g ∘ sub α) ∘ ext P f
        ≈⟨ solve C ⟩
      (sub β ∘ ext Q g) ∘ (sub α ∘ ext P f)
        ≈⟨ (refl⟩∘⟨ ⟺ (μT g)) ⟩∘⟨ (refl⟩∘⟨ ⟺ (μT f)) ⟩
      (sub β ∘ μ Q j ∘ T₁ Q g) ∘ (sub α ∘ μ P i ∘ T₁ P f) ∎
    where
      I-eq : I.U [ (β I.∘ ₁ (-⊗ j) α I.∘ α⇐) I.∘ α⇒ ≈ β I.∘ ₁ (-⊗ j) α ]
      I-eq = solve-mor I

  U-functor : Functor GradedKleisli C
  U-functor = record
    { F₀ = U₀
    ; F₁ = U₁
    ; identity = μ-identityʳ
    ; homomorphism = λ {_ _ _ f g} → U-∘ g f
    ; F-resp-≈ = U-resp
    }

  private
    subλ⇐λ⇒ : ∀ {X A} → C [ sub (λ⇐ {X}) C.∘ sub λ⇒ ≈ C.id {T₀ (I.unit ⊗₀ X) A} ]
    subλ⇐λ⇒ = let open C in ⟺ sub-homomorphism ○ sub-resp-≈ I.unitorˡ.isoˡ ○ sub-identity

    subλ⇒λ⇐ : ∀ {X A} → C [ sub λ⇒ C.∘ sub (λ⇐ {X}) ≈ C.id {T₀ X A} ]
    subλ⇒λ⇐ = let open C in ⟺ sub-homomorphism ○ sub-resp-≈ I.unitorˡ.isoʳ ○ sub-identity

    μ-ret : ∀ {v A} → C [ μ I.unit v C.∘ return {T₀ v A} ≈ sub λ⇐ ]
    μ-ret = let open C in introˡ subλ⇐λ⇒ ○ assoc ○ (refl⟩∘⟨ μ-identityˡ) ○ identityʳ

    F-id₁ : ∀ {c} → C [ sub I.id C.∘ (return C.∘ C.id {c}) ≈ return ]
    F-id₁ = let open C in elimˡ sub-identity ○ identityʳ

    F-resp₁ : ∀ {c d} {f g : C [ c , d ]} → C [ f ≈ g ]
            → C [ sub I.id C.∘ (return C.∘ f) ≈ return C.∘ g ]
    F-resp₁ p = let open C in elimˡ sub-identity ○ (refl⟩∘⟨ p)

    F-hom₁ : ∀ {c d e} (f : C [ c , d ]) (g : C [ d , e ])
           → C [ sub λ⇐ C.∘ (return C.∘ (g C.∘ f)) ≈ (return C.∘ g) ⊙ (return C.∘ f) ]
    F-hom₁ f g = ⟺ (begin
        ext I.unit (return ∘ g) ∘ (return ∘ f)                   ≈⟨ sym-assoc ⟩
        (ext I.unit (return ∘ g) ∘ return) ∘ f                   ≈⟨ L ⟩∘⟨refl ⟩
        (sub λ⇐ ∘ (return ∘ g)) ∘ f                              ≈⟨ assoc ⟩
        sub λ⇐ ∘ ((return ∘ g) ∘ f)                              ≈⟨ refl⟩∘⟨ assoc ⟩
        sub λ⇐ ∘ (return ∘ (g ∘ f))                              ∎)
      where
        open C
        L : ext I.unit (return ∘ g) ∘ return ≈ sub λ⇐ ∘ (return ∘ g)
        L = begin
          ext I.unit (return ∘ g) ∘ return                              ≈⟨ introˡ subλ⇐λ⇒ ⟩
          (sub λ⇐ ∘ sub λ⇒) ∘ (ext I.unit (return ∘ g) ∘ return)        ≈⟨ assoc ⟩
          sub λ⇐ ∘ (sub λ⇒ ∘ (ext I.unit (return ∘ g) ∘ return))        ≈⟨ refl⟩∘⟨ ext-identityʳ ⟩
          sub λ⇐ ∘ (return ∘ g)                                         ∎

  F : Functor C GradedKleisli
  F = record
    { F₀ = I.unit ,_
    ; F₁ = λ f → I.unit , return C.∘ f , ρ⇒
    ; identity = EqC.return (I.id , F-id₁ , Iᵁ.elimʳ (identity (I.unit ⊗-)))
    ; homomorphism = λ {_ _ _ f g} → EqC.return (λ⇐ , F-hom₁ f g , (let open Iᵁ in begin
        (ρ⇒ ∘ (ρ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ λ⇐)  ≈⟨ assoc ⟩
        ρ⇒ ∘ ((ρ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ λ⇐)  ≈⟨ refl⟩∘⟨ assoc ⟩
        ρ⇒ ∘ (ρ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ λ⇐))  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ triangle-inv ⟩
        ρ⇒ ∘ (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)         ≈⟨ refl⟩∘⟨ ⟺ (homomorphism I.⊗) ⟩
        ρ⇒ ∘ (ρ⇒ ∘ ρ⇐) ⊗₁ (id ∘ id)          ≈⟨ refl⟩∘⟨ (I.unitorʳ.isoʳ ⟩⊗⟨ identity²) ⟩
        ρ⇒ ∘ id ⊗₁ id                         ≈⟨ elimʳ (identity I.⊗) ⟩
        ρ⇒                                     ∎))
    ; F-resp-≈ = λ p → EqC.return (I.id , F-resp₁ p , Iᵁ.elimʳ (identity (I.unit ⊗-)))
    }

  F⊣U : Adjoint F U-functor
  F⊣U = record
    { unit = ntHelper record
      { η       = λ _ → return
      ; commute = λ f → let open C in ⟺ (begin
          (sub ρ⇒ ∘ μ I.unit I.unit ∘ T₁ I.unit (return ∘ f)) ∘ return
            ≈⟨ (refl⟩∘⟨ μT (return ∘ f)) ⟩∘⟨refl ⟩
          T₁ I.unit f ∘ return  ≈⟨ ⟺ return-commute ⟩
          return ∘ f            ∎)
      }
    ; counit = ntHelper record
      { η       = λ where (j , d) → j , C.id , λ⇒
      ; commute = λ { {j , _} {j′ , d′} (kx , fx , φx) →
          symmetric _≈ᴳ_ (EqC.return (λ⇐ I.∘ φx
            , (let open C in
                 (begin
                   sub (λ⇐ I.∘ φx) ∘ (ext j fx ∘ id)
                     ≈⟨ pushˡ sub-homomorphism ⟩
                   sub λ⇐ ∘ sub φx ∘ (ext j fx ∘ id)
                     ≈⟨ refl⟩∘⟨ refl⟩∘⟨ identityʳ ⟩
                   sub λ⇐ ∘ (sub φx ∘ ext j fx) ∎)
               ○ ⟺ (begin
                   μ I.unit j′ ∘ (return ∘ (sub φx ∘ μ j kx ∘ T₁ j fx))
                     ≈⟨ refl⟩∘⟨ sym-assoc ⟩
                   μ I.unit j′ ∘ ((return ∘ sub φx) ∘ (μ j kx ∘ T₁ j fx))
                     ≈⟨ sym-assoc ⟩
                   (μ I.unit j′ ∘ (return ∘ sub φx)) ∘ (μ j kx ∘ T₁ j fx)
                     ≈⟨ (sym-assoc ○ (μ-ret ⟩∘⟨refl)) ⟩∘⟨refl ⟩
                   (sub λ⇐ ∘ sub φx) ∘ (μ j kx ∘ T₁ j fx)
                     ≈⟨ assoc ○ (refl⟩∘⟨ refl⟩∘⟨ μT fx) ⟩
                   sub λ⇐ ∘ (sub φx ∘ ext j fx) ∎))
            , (let vs = j ∷ kx ∷ j′ ∷ []
                   open MorAtoms I vs
                   open MorSolve I vs (((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , φx) ∷ [])
               in solveMor! ((S.λ⇒ S.∘ (S.ρ⇒ S.⊗₁ S.id) S.∘ S.α⇐) S.∘ S.id S.⊗₁ (S.λ⇐ S.∘ gen (# 0)))
                            (gen (# 0) S.∘ (S.λ⇒ S.⊗₁ S.id) S.∘ S.α⇐)))) }
      }
    ; zig = EqC.return (λ⇒
      , (let open C in begin
          sub λ⇒ ∘ (μ I.unit I.unit ∘ (return ∘ return))
            ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          sub λ⇒ ∘ ((μ I.unit I.unit ∘ return) ∘ return)
            ≈⟨ refl⟩∘⟨ (μ-ret ⟩∘⟨refl) ⟩
          sub λ⇒ ∘ (sub λ⇐ ∘ return)  ≈⟨ pullˡ subλ⇒λ⇐ ⟩
          id ∘ return                 ≈⟨ identityˡ ⟩
          return                      ∎)
      , (let open Iᵁ in begin
          ρ⇒ ∘ (id ⊗₁ λ⇒)  ≈⟨ ⟺ coherence₃ ⟩∘⟨refl ⟩
          λ⇒ ∘ (id ⊗₁ λ⇒)  ≈⟨ refl⟩∘⟨ (⟺ (cancelʳ associator.isoʳ) ○ (I.triangle ⟩∘⟨refl)) ⟩
          λ⇒ ∘ ((ρ⇒ ⊗₁ id) ∘ α⇐) ∎))
    ; zag = let open C in begin
        (sub λ⇒ ∘ μ I.unit _ ∘ T₁ I.unit id) ∘ return  ≈⟨ assoc ⟩
        sub λ⇒ ∘ (μ I.unit _ ∘ T₁ I.unit id) ∘ return  ≈⟨ refl⟩∘⟨ assoc ⟩
        sub λ⇒ ∘ μ I.unit _ ∘ (T₁ I.unit id ∘ return)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ elimˡ T-identity ⟩
        sub λ⇒ ∘ μ I.unit _ ∘ return                   ≈⟨ μ-identityˡ ⟩
        id                                              ∎
    }

