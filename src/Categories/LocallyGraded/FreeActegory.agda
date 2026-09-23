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
open import Categories.Coherence.Monoidal.Tactic
open import Categories.Diagram.Coend.Ext.Setoids
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
              , solve-mor ℐ )
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
              , solve-mor ℐ )
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
              , solve-mor ℐ )
            , ( L.Equiv.trans (L.sub-resp-≈ ℐᵁ.Equiv.refl L.assoc)
                  (L.Equiv.trans (L.Equiv.sym L.sub-homomorphism)
                    (L.Equiv.trans (L.sub-resp-≈ associator.isoˡ L.Equiv.refl) L.sub-identity))
              , ℐᵁ.elimʳ (identity (Xi ⊗-)) ) )
    ; identityˡ = λ where
        {ai , _} {bj , _} {k , f , α} → return
          ( ρ⇒
          , (L.id L.∙ f , α)
          , ( L.sub-identity
            , solve-mor ℐ )
          , ( L.identityˡ , ℐᵁ.elimʳ (identity (ai ⊗-)) ) )
    ; identityʳ = λ where
        {ai , _} {bj , _} {k , f , α} → return
          ( λ⇒
          , (f L.∙ L.id , α)
          , ( L.sub-identity
            , solve-mor ℐ )
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
      , solve-mor ℐ )
    , ( L.identityˡ , ℐᵁ.elimʳ (identity (i ⊗-)) ) )

  reindex-∘ʳ : ∀ {i′ i j A B} {k} (f : L.Hom k A B) (α : (i ⊗₀ k) ℐᵁ.⇒ j) (d : i′ ℐᵁ.⇒ i)
             → ((k , f , α) ∘∮ reindex d) ≈∮ (k , f , α ℐᵁ.∘ ₁ (-⊗ k) d)
  reindex-∘ʳ {i′} {i} {j} {k = k} f α d = return
    ( λ⇒
    , (f L.∙ L.id , α ℐᵁ.∘ ₁ (-⊗ k) d)
    , ( L.sub-identity
      , solve-mor ℐ )
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
          , solve-mor ℐ )
    }

  infix 10 _∗∮_
  _∗∮_ : ∀ {x x′ i j A B} → x ℐᵁ.⇒ x′ → ∮Elt (i , A) (j , B) → ∮Elt (x ⊗₀ i , A) (x′ ⊗₀ j , B)
  v ∗∮ p = map∫ (∗-nt v) ⟨$⟩ p

  ∗∮-reindex : ∀ {x x′ i i′ A} (v : x ℐᵁ.⇒ x′) (c : i ℐᵁ.⇒ i′)
             → v ∗∮ reindex {A = A} c ≈∮ reindex (v ⊗₁ c)
  ∗∮-reindex {x} {x′} {i} {i′} v c = ι-resp L.Equiv.refl
    (solve-mor ℐ)

  ∗∮-id : ∀ {x x′ i A} (v : x ℐᵁ.⇒ x′)
        → v ∗∮ ∮C.id {(i , A)} ≈∮ reindex (v ⊗₁ ℐ.id)
  ∗∮-id {x} {x′} {i} v = ι-resp L.Equiv.refl
    (solve-mor ℐ)

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
            (solve-mor ℐ)
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
                (solve-mor ℐ)
            ○ ⟺ (reindex-∘ʳ f α λ⇒)
    ; multiplicator-commute = λ where
        {x} {x′} {y} {y′} {i , _} {j , _} {v} {w} {k , f , α} →
          let open ∮C.HomReasoning in
          reindex-∘ˡ α⇒ f (((v ⊗₁ w) ⊗₁ α) ℐᵁ.∘ α⇒)
            ○ ι-resp L.Equiv.refl
                (solve-mor ℐ)
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
                , solve-mor ℐ )
              , ( L.Equiv.refl , ℐᵁ.elimʳ (identity (ℐ.unit ⊗-)) ) ) )
    ; identity = ι-resp L.Equiv.refl
        (ℐᵁ.∘-resp-≈ (ℐᵁ.Equiv.sym coherence-inv₃) coherence₃)
    ; homomorphism = λ {k} {l} {A} {B} {C} {g} {f} →
        let open ∮C.HomReasoning in
        ⟺ ( reindex-∘ˡ α⇐ (g L.∙ f) _
          ○ ι-resp L.Equiv.refl
              (solve-mor ℐ) )
    }

  --------------------------------------------------------------------------------
  -- η∮ is fully faithful
  --------------------------------------------------------------------------------

  private variable
    i i′ : ℐ.Obj
    A B : L.Obj

  flatten : ∮Elt (ℐ.unit , A) (i , B) → L.Hom i A B
  flatten (k , f , α) = L.sub[ α ℐᵁ.∘ λ⇐ ] f

  unflatten : L.Hom i A B → ∮Elt (ℐ.unit , A) (i , B)
  unflatten {i = i} f = i , f , λ⇒

  flatten-resp-≈ : {x y : ∮Elt (ℐ.unit , A) (i , B)} → x ≈∮ y → flatten x L.≈ flatten y
  flatten-resp-≈ {A = A} {i = i} {B = B} = Func.cong (SetoidCoend.copair (GHom ℐ.unit i A B)
    {S = F₀ (HomF L A B) i} record
    { at        = λ k → record
        { to   = λ (f , α) → L.sub[ α ℐᵁ.∘ λ⇐ ] f
        ; cong = λ (f≈ , α≈) → L.sub-resp-≈ (ℐᵁ.∘-resp-≈ˡ α≈) f≈ }
    ; dinatural = λ φ (w , ω) →
        L.Equiv.trans (L.sub-resp-≈ ℐᵁ.Equiv.refl L.sub-identity)
          (L.Equiv.trans
            (L.sub-resp-≈
              (let open ℐᵁ in
               ⟺ (((elimʳ (identity (ℐ.unit ⊗-)) ⟩∘⟨refl) ⟩∘⟨refl) ○ assoc
                    ○ (refl⟩∘⟨ ℐ.unitorˡ-commute-to) ○ sym-assoc))
              L.Equiv.refl)
            L.sub-homomorphism)
    })

  unflatten-resp-≈ : {f g : L.Hom i A B} → f L.≈ g → unflatten f ≈∮ unflatten g
  unflatten-resp-≈ f≈ = ι-resp f≈ ℐᵁ.Equiv.refl

  flatten-unflatten : (f : L.Hom i A B) → flatten (unflatten f) L.≈ f
  flatten-unflatten f =
    L.Equiv.trans (L.sub-resp-≈ ℐ.unitorˡ.isoʳ L.Equiv.refl) L.sub-identity

  unflatten-flatten : (x : ∮Elt (ℐ.unit , A) (i , B)) → unflatten (flatten x) ≈∮ x
  unflatten-flatten (k , f , α) = ∮C.Equiv.sym (return
    ( α ℐᵁ.∘ λ⇐
    , (f , λ⇒)
    , ( L.sub-identity
      , (let open ℐᵁ in ℐ.unitorˡ-commute-from ○ assoc ○ elimʳ ℐ.unitorˡ.isoˡ) )
    , ( L.Equiv.refl , ℐᵁ.elimʳ (identity (ℐ.unit ⊗-)) ) ))

  flatten-inverse : Inverse (∮hom (ℐ.unit , A) (i , B)) (F₀ (HomF L A B) i)
  flatten-inverse = record
    { to        = flatten
    ; from      = unflatten
    ; to-cong   = flatten-resp-≈
    ; from-cong = unflatten-resp-≈
    ; inverse   = (λ y≈ → L.Equiv.trans (flatten-resp-≈ y≈) (flatten-unflatten _))
                , (λ y≈ → ∮C.Equiv.trans (unflatten-resp-≈ y≈) (unflatten-flatten _))
    }

  flatten-reindex : (c : i ℐᵁ.⇒ i′) (x : ∮Elt (ℐ.unit , A) (i , B))
                  → flatten (reindex c ∘∮ x) L.≈ L.sub[ c ] (flatten x)
  flatten-reindex c (k , f , α) = L.Equiv.trans (flatten-resp-≈ (reindex-∘ˡ c f α))
    (L.Equiv.trans (L.sub-resp-≈ ℐᵁ.assoc L.Equiv.refl) L.sub-homomorphism)

  unflatten-sub : (c : i ℐᵁ.⇒ i′) (f : L.Hom i A B)
                → unflatten (L.sub[ c ] f) ≈∮ reindex c ∘∮ unflatten f
  unflatten-sub c f = ∮C.Equiv.sym (∮C.Equiv.trans (reindex-∘ˡ c f λ⇒) (return
    ( c
    , (f , λ⇒)
    , ( L.sub-identity , ℐ.unitorˡ-commute-from )
    , ( L.Equiv.refl , ℐᵁ.elimʳ (identity (ℐ.unit ⊗-)) ) )))

  private module η = LocallyGradedFunctor η∮

  unflatten-η∮ : (f : L.Hom i A B) → unflatten f ≈∮ reindex ρ⇒ ∘∮ η.F₁ f
  unflatten-η∮ f = ∮C.Equiv.sym (∮C.Equiv.trans (reindex-∘ˡ ρ⇒ f (ρ⇐ ℐᵁ.∘ λ⇒))
    (ι-resp L.Equiv.refl (ℐᵁ.cancelˡ ℐ.unitorʳ.isoʳ)))

  η∮-unflatten : (f : L.Hom i A B) → reindex ρ⇐ ∘∮ unflatten f ≈∮ η.F₁ f
  η∮-unflatten f = reindex-∘ˡ ρ⇐ f λ⇒

  η∮-faithful : (f : L.Hom i A B) → flatten (reindex ρ⇒ ∘∮ η.F₁ f) L.≈ f
  η∮-faithful f = L.Equiv.trans (flatten-resp-≈ (∮C.Equiv.sym (unflatten-η∮ f)))
                                (flatten-unflatten f)

  η∮-full : (x : ∮Elt (ℐ.unit , A) (i ⊗₀ ℐ.unit , B))
          → η.F₁ (flatten (reindex ρ⇒ ∘∮ x)) ≈∮ x
  η∮-full x = let open ∮C.HomReasoning in
    ⟺ (η∮-unflatten _)
      ○ ∮C.∘-resp-≈ʳ (unflatten-flatten (reindex ρ⇒ ∘∮ x))
      ○ ∮C.sym-assoc
      ○ ∮C.∘-resp-≈ˡ (reindex-∘ ρ⇐ ρ⇒ ○ reindex-resp-≈ ℐ.unitorʳ.isoˡ ○ reindex-id)
      ○ ∮C.identityˡ

  η∮-fully-faithful : Inverse (F₀ (HomF L A B) i) (∮hom (ℐ.unit , A) (i ⊗₀ ℐ.unit , B))
  η∮-fully-faithful = record
    { to        = η.F₁
    ; from      = λ x → flatten (reindex ρ⇒ ∘∮ x)
    ; to-cong   = η.F-resp-≈
    ; from-cong = λ x≈ → flatten-resp-≈ (∮C.∘-resp-≈ʳ x≈)
    ; inverse   = (λ y≈ → ∮C.Equiv.trans (η.F-resp-≈ y≈) (η∮-full _))
                , (λ y≈ → L.Equiv.trans (flatten-resp-≈ (∮C.∘-resp-≈ʳ y≈)) (η∮-faithful _))
    }
