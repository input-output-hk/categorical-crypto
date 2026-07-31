{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The free ℐ-actegory on a locally ℐ-graded category L: the category ∮ L with
-- objects ℐ.Obj × L.Obj and hom (i , A) ⇒ (j , B) the Setoids coend
--
--   ∫^k  L.Hom k A B  ×  ℐ.U [ i ⊗ k , j ]
--
-- Classically, we have Wood's correspondence between ℐ-actegories and
-- locally ℐ-graded categories admitting powers by representables. We
-- can now extend the range to all locally ℐ-graded categories, and
-- ask ourselves if this is still a right adjoint.
--
-- Conjecture: it is, and its left adjoint is ∮-actegory. See η∮ below.
--------------------------------------------------------------------------------

module Categories.LocallyGraded.FreeActegory where

open import Level

open import Categories.Actegory
open import Categories.Actegory.Underlying
open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Instance.Setoids
open import Categories.Category.Monoidal
open import Categories.Coherence.Monoidal
open import Categories.Diagram.Coend.Setoids
open import Categories.FreeMonoidal
open import Categories.Functor
open import Categories.Functor.Bifunctor
open import Categories.Functor.Presheaf
open import Categories.LocallyGraded
import Categories.Morphism.Reasoning as MR
open import Categories.NaturalTransformation

open import Data.Fin
open import Data.Product
open import Data.Product.Relation.Binary.Pointwise.NonDependent
open import Data.Vec
open import Function.Bundles
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Equivalence

module _ {o ℓ e o′ ℓ′ e′} {ℐ : MonoidalCategory o ℓ e}
  (L : LocallyGradedCategory ℐ o′ ℓ′ e′) where

  private
    module L = LocallyGradedCategory L
    module ℐ = MonoidalCategory ℐ
    module ℐᵁ where
      open Category ℐ.U public
      open HomReasoning public
      open MR ℐ.U public

  open ℐ using (_⊗₀_; _⊗₁_; _⊗-; -⊗_; associator)
  open Functor
  open import Categories.Category.Monoidal.Properties ℐ.monoidal
  open import Categories.Category.Monoidal.Utilities ℐ.monoidal
  open Shorthands

  -- the ways a grade fits between i and j
  Fit : (i j : ℐ.Obj) → Presheaf ℐ.U (Setoids ℓ e)
  Fit i j = record
    { F₀           = λ u → ℐᵁ.hom-setoid {i ⊗₀ u} {j}
    ; F₁           = λ φ → record { to = ℐᵁ._∘ ₁ (i ⊗-) φ ; cong = ℐᵁ.∘-resp-≈ˡ }
    ; identity     = ℐᵁ.elimʳ (identity (i ⊗-))
    ; homomorphism = ℐᵁ.pushʳ (homomorphism (i ⊗-))
    ; F-resp-≈     = λ φ≈ → ℐᵁ.∘-resp-≈ʳ (F-resp-≈ (i ⊗-) φ≈)
    }

  -- the hom bifunctor at fixed endpoints
  GHom : (i j : ℐ.Obj) (A B : L.Obj)
       → Bifunctor (Category.op ℐ.U) ℐ.U (Setoids (ℓ ⊔ ℓ′) (e ⊔ e′))
  GHom i j A B = HomF L A B ×ᵈ Fit i j

  private
    ∮hom : (X Y : ℐ.Obj × L.Obj) → Setoid (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
    ∮hom (i , A) (j , B) = SetoidCoend.∫ (GHom i j A B)

  ∮Elt : (X Y : ℐ.Obj × L.Obj) → Set (o ⊔ ℓ ⊔ ℓ′)
  ∮Elt X Y = Setoid.Carrier (∮hom X Y)

  infixr 9 _∘∮_
  _∘∮_ : ∀ {X Y Z} → ∮Elt Y Z → ∮Elt X Y → ∮Elt X Z
  (l , g , β) ∘∮ (k , f , α) = k ⊗₀ l , g L.∙ f , β ℐᵁ.∘ ₁ (-⊗ l) α ℐᵁ.∘ α⇐

  module _ {i j r : ℐ.Obj} {A B C : L.Obj} where
    private
      module ∫f = SetoidCoend (GHom i j A B)
      module ∫g = SetoidCoend (GHom j r B C)
      module ∫∘ = SetoidCoend (GHom i r A C)

    -- _∘∮_ as a map out of both hom coends at once; dinaturality in either
    -- variable is L.interchange against the other's identity grade.
    ∘∮₂ : Func (∫g.∫ ×ₛ ∫f.∫) ∫∘.∫
    ∘∮₂ = copair₂ (GHom j r B C) (GHom i j A B) record
      { at         = λ l k → record
        { to   = λ ((g , β) , (f , α)) → (l , g , β) ∘∮ (k , f , α)
        ; cong = λ ((g≈ , β≈) , (f≈ , α≈)) → Func.cong (∫∘.ι (k ⊗₀ l))
            ( L.∙-resp-≈ g≈ f≈
            , ℐᵁ.∘-resp-≈ β≈ (ℐᵁ.∘-resp-≈ˡ (F-resp-≈ (-⊗ l) α≈)) ) }
      ; dinaturalˡ = λ where
          {X} {Y} ψ (g , β) {k} (f , α) → return
            ( ℐ.id ⊗₁ ψ
            , (g L.∙ f , β ℐᵁ.∘ ₁ (-⊗ Y) α ℐᵁ.∘ α⇐)
            , ( L.Equiv.trans L.sub-identity
                  (L.∙-resp-≈ (L.Equiv.sym L.sub-identity) L.Equiv.refl)
              , (let vs = i ∷ k ∷ j ∷ X ∷ Y ∷ r ∷ []
                     open MorAtoms ℐ vs
                     open MorSolve ℐ vs
                          ( ((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α)
                          ∷ ((V (# 2) ⊗ᵒ V (# 4) , V (# 5)) , β)
                          ∷ ((V (# 3) , V (# 4)) , ψ) ∷ [] )
                 in solveMor!
                      ((gen (# 1) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐)
                         S.∘ S.id S.⊗₁ (S.id S.⊗₁ gen (# 2)))
                      ((gen (# 1) S.∘ S.id S.⊗₁ gen (# 2)) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐)) )
            , ( L.Equiv.trans (L.Equiv.sym L.interchange)
                  (L.∙-resp-≈ L.Equiv.refl L.sub-identity)
              , (let open ℐᵁ in elimʳ (identity (i ⊗-))
                   ○ (⟺ (elimʳ (identity (j ⊗-))) ⟩∘⟨refl)) ) )
      ; dinaturalʳ = λ where
          {X} {Y} φ (f , α) {l} (g , β) → return
            ( φ ⊗₁ ℐ.id
            , (g L.∙ f , β ℐᵁ.∘ ₁ (-⊗ l) α ℐᵁ.∘ α⇐)
            , ( L.Equiv.trans L.sub-identity
                  (L.∙-resp-≈ L.Equiv.refl (L.Equiv.sym L.sub-identity))
              , (let vs = i ∷ X ∷ Y ∷ l ∷ j ∷ r ∷ []
                     open MorAtoms ℐ vs
                     open MorSolve ℐ vs
                          ( ((V (# 0) ⊗ᵒ V (# 2) , V (# 4)) , α)
                          ∷ ((V (# 4) ⊗ᵒ V (# 3) , V (# 5)) , β)
                          ∷ ((V (# 1) , V (# 2)) , φ) ∷ [] )
                 in solveMor!
                      ((gen (# 1) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐)
                         S.∘ S.id S.⊗₁ (gen (# 2) S.⊗₁ S.id))
                      (gen (# 1) S.∘ (gen (# 0) S.∘ S.id S.⊗₁ gen (# 2)) S.⊗₁ S.id S.∘ S.α⇐)) )
            , ( L.Equiv.trans (L.Equiv.sym L.interchange)
                  (L.∙-resp-≈ L.sub-identity L.Equiv.refl)
              , (let open ℐᵁ in elimʳ (identity (i ⊗-))
                   ○ (refl⟩∘⟨ (F-resp-≈ (-⊗ l) (⟺ (elimʳ (identity (i ⊗-)))) ⟩∘⟨refl))) ) )
      }

    ∘∮-resp-≈ : {y y′ : ∮Elt (j , B) (r , C)} {x x′ : ∮Elt (i , A) (j , B)}
              → Setoid._≈_ ∫g.∫ y y′ → Setoid._≈_ ∫f.∫ x x′
              → Setoid._≈_ ∫∘.∫ (y ∘∮ x) (y′ ∘∮ x′)
    ∘∮-resp-≈ y≈ x≈ = Func.cong ∘∮₂ (y≈ , x≈)

  ∮ : Category (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
  ∮ = categoryHelper record
    { Obj       = ℐ.Obj × L.Obj
    ; _⇒_       = ∮Elt
    ; _≈_       = λ {X} {Y} → Setoid._≈_ (∮hom X Y)
    ; id        = ℐ.unit , L.id , ρ⇒
    ; _∘_       = _∘∮_
    ; assoc     = λ where
        {Xi , _} {Yi , _} {Zi , _} {Wi , _} {a , f , φf} {b , g , φg} {c , h , φh} →
          return
            ( α⇐
            , ( (h L.∙ g) L.∙ f
              , φh ℐᵁ.∘ ₁ (-⊗ c) (φg ℐᵁ.∘ ₁ (-⊗ b) φf ℐᵁ.∘ α⇐) ℐᵁ.∘ α⇐ )
            , ( L.sub-identity
              , (let vs = Xi ∷ a ∷ b ∷ c ∷ Yi ∷ Zi ∷ Wi ∷ []
                     open MorAtoms ℐ vs
                     open MorSolve ℐ vs
                          ( ((V (# 0) ⊗ᵒ V (# 1) , V (# 4)) , φf)
                          ∷ ((V (# 4) ⊗ᵒ V (# 2) , V (# 5)) , φg)
                          ∷ ((V (# 5) ⊗ᵒ V (# 3) , V (# 6)) , φh) ∷ [] )
                 in solveMor!
                      ((gen (# 2) S.∘ (gen (# 1) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐) S.⊗₁ S.id S.∘ S.α⇐)
                         S.∘ S.id S.⊗₁ S.α⇐)
                      ((gen (# 2) S.∘ gen (# 1) S.⊗₁ S.id S.∘ S.α⇐) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐)) )
            , ( L.Equiv.trans (L.sub-resp-≈ ℐᵁ.Equiv.refl L.assoc)
                  (L.Equiv.trans (L.Equiv.sym L.sub-homomorphism)
                    (L.Equiv.trans (L.sub-resp-≈ associator.isoˡ L.Equiv.refl) L.sub-identity))
              , ℐᵁ.elimʳ (identity (Xi ⊗-)) ) )
    ; identityˡ = λ where
        {ai , _} {bj , _} {k , f , α} → return
          ( ρ⇒
          , (L.id L.∙ f , α)
          , ( L.sub-identity
            , (let vs = ai ∷ k ∷ bj ∷ []
                   open MorAtoms ℐ vs
                   open MorSolve ℐ vs (((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α) ∷ [])
               in solveMor! (gen (# 0) S.∘ S.id S.⊗₁ S.ρ⇒) (S.ρ⇒ S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐)) )
          , ( L.identityˡ , ℐᵁ.elimʳ (identity (ai ⊗-)) ) )
    ; identityʳ = λ where
        {ai , _} {bj , _} {k , f , α} → return
          ( λ⇒
          , (f L.∙ L.id , α)
          , ( L.sub-identity
            , (let vs = ai ∷ k ∷ bj ∷ []
                   open MorAtoms ℐ vs
                   open MorSolve ℐ vs (((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α) ∷ [])
               in solveMor! (gen (# 0) S.∘ S.id S.⊗₁ S.λ⇒) (gen (# 0) S.∘ S.ρ⇒ S.⊗₁ S.id S.∘ S.α⇐)) )
          , ( L.identityʳ , ℐᵁ.elimʳ (identity (ai ⊗-)) ) )
    ; equiv     = λ {X} {Y} → Setoid.isEquivalence (∮hom X Y)
    ; ∘-resp-≈  = ∘∮-resp-≈
    }

  --------------------------------------------------------------------------------
  -- The ℐ-action on ∮: x ∗ (i , A) = (x ⊗ i , A) — the actegory structure of
  -- the conjectured free-actegory universal property (see the module header).
  --------------------------------------------------------------------------------

  private
    module ∮C = Category ∮

    infix 4 _≈∮_
    _≈∮_ : ∀ {X Y} → ∮Elt X Y → ∮Elt X Y → Set (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)
    _≈∮_ {X} {Y} = Setoid._≈_ (∮hom X Y)

    ι-resp : ∀ {i j A B k} {f g : L.Hom k A B} {α β : (i ⊗₀ k) ℐᵁ.⇒ j}
           → f L.≈ g → α ℐᵁ.≈ β → (k , f , α) ≈∮ (k , g , β)
    ι-resp {i} {j} {A} {B} {k} f≈ α≈ = Func.cong (SetoidCoend.ι (GHom i j A B) k) (f≈ , α≈)

  reindex : ∀ {i i′ A} → i ℐᵁ.⇒ i′ → ∮Elt (i , A) (i′ , A)
  reindex c = ℐ.unit , L.id , c ℐᵁ.∘ ρ⇒

  reindex-resp-≈ : ∀ {i i′ A} {c c′ : i ℐᵁ.⇒ i′}
                 → c ℐᵁ.≈ c′ → reindex {A = A} c ≈∮ reindex c′
  reindex-resp-≈ c≈ = ι-resp L.Equiv.refl (ℐᵁ.∘-resp-≈ˡ c≈)

  reindex-id : ∀ {i A} → reindex ℐ.id ≈∮ ∮C.id {(i , A)}
  reindex-id = ι-resp L.Equiv.refl ℐᵁ.identityˡ

  reindex-∘ˡ : ∀ {i j j′ A B} (c : j ℐᵁ.⇒ j′) {k} (f : L.Hom k A B) (α : (i ⊗₀ k) ℐᵁ.⇒ j)
             → (reindex c ∘∮ (k , f , α)) ≈∮ (k , f , c ℐᵁ.∘ α)
  reindex-∘ˡ {i} {j} {j′} c {k} f α = return
    ( ρ⇒
    , (L.id L.∙ f , c ℐᵁ.∘ α)
    , ( L.sub-identity
      , (let vs = i ∷ k ∷ j ∷ j′ ∷ []
             open MorAtoms ℐ vs
             open MorSolve ℐ vs ( ((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α)
                                ∷ ((V (# 2) , V (# 3)) , c) ∷ [] )
         in solveMor! ((gen (# 1) S.∘ gen (# 0)) S.∘ S.id S.⊗₁ S.ρ⇒)
                      ((gen (# 1) S.∘ S.ρ⇒) S.∘ gen (# 0) S.⊗₁ S.id S.∘ S.α⇐)) )
    , ( L.identityˡ , ℐᵁ.elimʳ (identity (i ⊗-)) ) )

  reindex-∘ʳ : ∀ {i′ i j A B} {k} (f : L.Hom k A B) (α : (i ⊗₀ k) ℐᵁ.⇒ j) (d : i′ ℐᵁ.⇒ i)
             → ((k , f , α) ∘∮ reindex d) ≈∮ (k , f , α ℐᵁ.∘ ₁ (-⊗ k) d)
  reindex-∘ʳ {i′} {i} {j} {k = k} f α d = return
    ( λ⇒
    , (f L.∙ L.id , α ℐᵁ.∘ ₁ (-⊗ k) d)
    , ( L.sub-identity
      , (let vs = i′ ∷ i ∷ k ∷ j ∷ []
             open MorAtoms ℐ vs
             open MorSolve ℐ vs ( ((V (# 1) ⊗ᵒ V (# 2) , V (# 3)) , α)
                                ∷ ((V (# 0) , V (# 1)) , d) ∷ [] )
         in solveMor! ((gen (# 0) S.∘ gen (# 1) S.⊗₁ S.id) S.∘ S.id S.⊗₁ S.λ⇒)
                      (gen (# 0) S.∘ (gen (# 1) S.∘ S.ρ⇒) S.⊗₁ S.id S.∘ S.α⇐)) )
    , ( L.identityʳ , ℐᵁ.elimʳ (identity (i′ ⊗-)) ) )

  reindex-∘ : ∀ {i i′ i″ A} (c : i′ ℐᵁ.⇒ i″) (d : i ℐᵁ.⇒ i′)
            → (reindex {A = A} c ∘∮ reindex d) ≈∮ reindex (c ℐᵁ.∘ d)
  reindex-∘ c d = let open ∮C.HomReasoning in
    reindex-∘ˡ c L.id (d ℐᵁ.∘ ρ⇒) ○ ι-resp L.Equiv.refl ℐᵁ.sym-assoc

  -- the action on hom-classes: v ∗ [ k , f , α ] = [ k , f , (v ⊗₁ α) ∘ α⇒ ]
  ∗-nt : ∀ {x x′ i j A B} → x ℐᵁ.⇒ x′
       → NaturalTransformation (GHom i j A B) (GHom (x ⊗₀ i) (x′ ⊗₀ j) A B)
  ∗-nt {x} {x′} {i} {j} v = ntHelper record
    { η       = λ _ → record
        { to   = λ (f , α) → f , (v ⊗₁ α) ℐᵁ.∘ α⇒
        ; cong = λ (f≈ , α≈) → f≈ , ℐᵁ.∘-resp-≈ˡ (F-resp-≈ ℐ.⊗ (ℐᵁ.Equiv.refl , α≈)) }
    ; commute = λ where
        {u , _} {u′ , _} (φ , ψ) {f , α} →
          ( L.Equiv.refl
          , (let vs = x ∷ x′ ∷ i ∷ j ∷ u ∷ u′ ∷ []
                 open MorAtoms ℐ vs
                 open MorSolve ℐ vs ( ((V (# 2) ⊗ᵒ V (# 4) , V (# 3)) , α)
                                    ∷ ((V (# 5) , V (# 4)) , φ)
                                    ∷ ((V (# 0) , V (# 1)) , v) ∷ [] )
             in solveMor!
                  ((gen (# 2) S.⊗₁ (gen (# 0) S.∘ S.id S.⊗₁ gen (# 1))) S.∘ S.α⇒)
                  (((gen (# 2) S.⊗₁ gen (# 0)) S.∘ S.α⇒) S.∘ S.id S.⊗₁ gen (# 1))) )
    }

  infix 10 _∗∮_
  _∗∮_ : ∀ {x x′ i j A B} → x ℐᵁ.⇒ x′ → ∮Elt (i , A) (j , B) → ∮Elt (x ⊗₀ i , A) (x′ ⊗₀ j , B)
  v ∗∮ p = map∫ (∗-nt v) ⟨$⟩ p

  ∗∮-reindex : ∀ {x x′ i i′ A} (v : x ℐᵁ.⇒ x′) (c : i ℐᵁ.⇒ i′)
             → v ∗∮ reindex {A = A} c ≈∮ reindex (v ⊗₁ c)
  ∗∮-reindex {x} {x′} {i} {i′} v c = ι-resp L.Equiv.refl
    (let vs = x ∷ x′ ∷ i ∷ i′ ∷ []
         open MorAtoms ℐ vs
         open MorSolve ℐ vs ( ((V (# 0) , V (# 1)) , v)
                            ∷ ((V (# 2) , V (# 3)) , c) ∷ [] )
     in solveMor! ((gen (# 0) S.⊗₁ (gen (# 1) S.∘ S.ρ⇒)) S.∘ S.α⇒)
                  (gen (# 0) S.⊗₁ gen (# 1) S.∘ S.ρ⇒))

  ∗∮-id : ∀ {x x′ i A} (v : x ℐᵁ.⇒ x′)
        → v ∗∮ ∮C.id {(i , A)} ≈∮ reindex (v ⊗₁ ℐ.id)
  ∗∮-id {x} {x′} {i} v = ι-resp L.Equiv.refl
    (let vs = x ∷ x′ ∷ i ∷ []
         open MorAtoms ℐ vs
         open MorSolve ℐ vs (((V (# 0) , V (# 1)) , v) ∷ [])
     in solveMor! ((gen (# 0) S.⊗₁ S.ρ⇒ {V (# 2)}) S.∘ S.α⇒)
                  (gen (# 0) S.⊗₁ S.id {V (# 2)} S.∘ S.ρ⇒))

  ∮-actegory : Actegory ℐ ∮
  ∮-actegory = record
    { _∗₀_ = λ x (i , A) → x ⊗₀ i , A
    ; _∗₁_ = _∗∮_
    ; ∗-resp-≈ = λ where
        {v = v} {f′ = k , f , α} v≈ p≈ →
          let open ∮C.HomReasoning in
          Func.cong (map∫ (∗-nt v)) p≈
            ○ ι-resp L.Equiv.refl (ℐᵁ.∘-resp-≈ˡ (F-resp-≈ ℐ.⊗ (v≈ , ℐᵁ.Equiv.refl)))
    ; ∗-identity = ι-resp L.Equiv.refl coherence₂
    ; ∗-homomorphism = λ where
        {x} {x′} {x″} {i , _} {j , _} {r , _} {v} {w} {k , f , α} {l , g , β} →
          ι-resp L.Equiv.refl
            (let vs = x ∷ x′ ∷ x″ ∷ i ∷ k ∷ j ∷ l ∷ r ∷ []
                 open MorAtoms ℐ vs
                 open MorSolve ℐ vs ( ((V (# 0) , V (# 1)) , v)
                                    ∷ ((V (# 1) , V (# 2)) , w)
                                    ∷ ((V (# 3) ⊗ᵒ V (# 4) , V (# 5)) , α)
                                    ∷ ((V (# 5) ⊗ᵒ V (# 6) , V (# 7)) , β) ∷ [] )
             in solveMor!
                  (((gen (# 1) S.∘ gen (# 0)) S.⊗₁ (gen (# 3) S.∘ gen (# 2) S.⊗₁ S.id S.∘ S.α⇐)) S.∘ S.α⇒)
                  (((gen (# 1) S.⊗₁ gen (# 3)) S.∘ S.α⇒) S.∘ (gen (# 0) S.⊗₁ gen (# 2) S.∘ S.α⇒) S.⊗₁ S.id S.∘ S.α⇐))
    ; unitor = record
        { from = reindex λ⇒
        ; to   = reindex λ⇐
        ; iso  = record
          { isoˡ = let open ∮C.HomReasoning in
              reindex-∘ λ⇐ λ⇒ ○ reindex-resp-≈ (ℐ.unitorˡ.isoˡ) ○ reindex-id
          ; isoʳ = let open ∮C.HomReasoning in
              reindex-∘ λ⇒ λ⇐ ○ reindex-resp-≈ (ℐ.unitorˡ.isoʳ) ○ reindex-id } }
    ; multiplicator = record
        { from = reindex α⇒
        ; to   = reindex α⇐
        ; iso  = record
          { isoˡ = let open ∮C.HomReasoning in
              reindex-∘ α⇐ α⇒ ○ reindex-resp-≈ associator.isoˡ ○ reindex-id
          ; isoʳ = let open ∮C.HomReasoning in
              reindex-∘ α⇒ α⇐ ○ reindex-resp-≈ associator.isoʳ ○ reindex-id } }
    ; unitor-commute = λ where
        {i , _} {j , _} {k , f , α} →
          let open ∮C.HomReasoning in
          reindex-∘ˡ λ⇒ f ((ℐ.id ⊗₁ α) ℐᵁ.∘ α⇒)
            ○ ι-resp L.Equiv.refl
                (let vs = i ∷ k ∷ j ∷ []
                     open MorAtoms ℐ vs
                     open MorSolve ℐ vs (((V (# 0) ⊗ᵒ V (# 1) , V (# 2)) , α) ∷ [])
                 in solveMor! (S.λ⇒ S.∘ (S.id S.⊗₁ gen (# 0)) S.∘ S.α⇒)
                              (gen (# 0) S.∘ S.λ⇒ S.⊗₁ S.id))
            ○ ⟺ (reindex-∘ʳ f α λ⇒)
    ; multiplicator-commute = λ where
        {x} {x′} {y} {y′} {i , _} {j , _} {v} {w} {k , f , α} →
          let open ∮C.HomReasoning in
          reindex-∘ˡ α⇒ f (((v ⊗₁ w) ⊗₁ α) ℐᵁ.∘ α⇒)
            ○ ι-resp L.Equiv.refl
                (let vs = x ∷ x′ ∷ y ∷ y′ ∷ i ∷ k ∷ j ∷ []
                     open MorAtoms ℐ vs
                     open MorSolve ℐ vs ( ((V (# 0) , V (# 1)) , v)
                                        ∷ ((V (# 2) , V (# 3)) , w)
                                        ∷ ((V (# 4) ⊗ᵒ V (# 5) , V (# 6)) , α) ∷ [] )
                 in solveMor!
                      (S.α⇒ S.∘ ((gen (# 0) S.⊗₁ gen (# 1)) S.⊗₁ gen (# 2)) S.∘ S.α⇒)
                      (((gen (# 0) S.⊗₁ (gen (# 1) S.⊗₁ gen (# 2) S.∘ S.α⇒)) S.∘ S.α⇒) S.∘ S.α⇒ S.⊗₁ S.id))
            ○ ⟺ (reindex-∘ʳ f ((v ⊗₁ ((w ⊗₁ α) ℐᵁ.∘ α⇒)) ℐᵁ.∘ α⇒) α⇒)
    ; assoc-coherence = let open ∮C.HomReasoning in
        reindex-∘ α⇒ α⇒
          ○ ⟺ ( ∮C.∘-resp-≈ (∗∮-reindex ℐ.id α⇒)
                  (∮C.∘-resp-≈ʳ (∗∮-id α⇒) ○ reindex-∘ α⇒ (α⇒ ⊗₁ ℐ.id))
                ○ reindex-∘ (ℐ.id ⊗₁ α⇒) (α⇒ ℐᵁ.∘ α⇒ ⊗₁ ℐ.id)
                ○ reindex-resp-≈ ℐ.pentagon )
    ; unitˡ-coherence = let open ∮C.HomReasoning in
        reindex-∘ λ⇒ α⇒ ○ reindex-resp-≈ coherence₁ ○ ⟺ (∗∮-id λ⇒)
    ; unitʳ-coherence = let open ∮C.HomReasoning in
        ∮C.∘-resp-≈ˡ (∗∮-reindex ℐ.id λ⇒)
          ○ reindex-∘ (ℐ.id ⊗₁ λ⇒) α⇒
          ○ reindex-resp-≈ ℐ.triangle
          ○ ⟺ (∗∮-id ρ⇒)
    }

  -- the unit of the conjectured adjunction
  η∮ : LocallyGradedFunctor L (Ψ ∮-actegory)
  η∮ = record
    { F₀ = ℐ.unit ,_
    ; F₁ = λ {k} f → k , f , ρ⇐ ℐᵁ.∘ λ⇒
    ; F-resp-≈ = λ f≈ → ι-resp f≈ ℐᵁ.Equiv.refl
    ; F-sub = λ {k} {k′} {A} {B} {a} {f} →
        let open ∮C.HomReasoning in
        ⟺ ( ∮C.∘-resp-≈ˡ (∗∮-id a)
          ○ reindex-∘ˡ (a ⊗₁ ℐ.id) f (ρ⇐ ℐᵁ.∘ λ⇒)
          ○ return
              ( a
              , (f , ρ⇐ ℐᵁ.∘ λ⇒)
              , ( L.sub-identity
                , (let vs = k ∷ k′ ∷ []
                       open MorAtoms ℐ vs
                       open MorSolve ℐ vs (((V (# 0) , V (# 1)) , a) ∷ [])
                   in solveMor! ((S.ρ⇐ S.∘ S.λ⇒) S.∘ S.id S.⊗₁ gen (# 0))
                                (gen (# 0) S.⊗₁ S.id S.∘ S.ρ⇐ S.∘ S.λ⇒)) )
              , ( L.Equiv.refl , ℐᵁ.elimʳ (identity (ℐ.unit ⊗-)) ) ) )
    ; identity = ι-resp L.Equiv.refl
        (ℐᵁ.∘-resp-≈ (ℐᵁ.Equiv.sym coherence-inv₃) coherence₃)
    ; homomorphism = λ {k} {l} {A} {B} {C} {g} {f} →
        let open ∮C.HomReasoning in
        ⟺ ( reindex-∘ˡ α⇐ (g L.∙ f) _
          ○ ι-resp L.Equiv.refl
              (let vs = k ∷ l ∷ []
                   open MorAtoms ℐ vs
                   open MorSolve ℐ vs []
               in solveMor!
                    (S.α⇐ {V (# 0)} {V (# 1)} {unitᵒ}
                       S.∘ (S.id S.⊗₁ (S.ρ⇐ S.∘ S.λ⇒) S.∘ S.α⇒)
                       S.∘ ((S.ρ⇐ S.∘ S.λ⇒) S.⊗₁ S.id) S.∘ S.α⇐)
                    (S.ρ⇐ {V (# 0) ⊗ᵒ V (# 1)} S.∘ S.λ⇒)) )
    }
