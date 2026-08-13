{-# OPTIONS --safe --without-K #-}

-- The category of graded monads on 𝒞 (the lax slice `GMon`) and the bundled
-- functor `Kl : GMon → Cats`, packaging the data + laws of `.Functorial`.
--
-- GMon's hom-equality is reflected from `Cats` along `Kl`: (Φ, ρ) ≈ (Φ′, ρ′)
-- iff KlMap (Φ, ρ) ≡F KlMap (Φ′, ρ′) — the coarsest equality making `Kl` a
-- functor, with `F-resp-≈` the identity.
--
-- Every clause is η-long with all implicits pinned and `GMon`/`Kl` are defined
-- by copatterns for performance reasons: as a `record{…}` this module exhausts a
-- 12 GB heap.  The laws are proved in an `unfolding` block, and GMon's field-type
-- conversions stay cheap because `.Functorial`'s `idG`/`∘G`/`KlMap` are `opaque`
-- (see there).

module Categories.GradedKleisli.Functorial.Category where

open import Level
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Categories.Category
open import Categories.Category.Instance.Cats
open import Categories.Category.Monoidal
open import Categories.Functor
open import Categories.Functor.Equivalence
open import Categories.Functor.Monoidal
open import Categories.GradedKleisli
import Categories.Morphism.Reasoning as MR

import Categories.GradedKleisli.Functorial as F

module _ {o ℓ e o′ ℓ′ e′ : Level} (𝒞 : Category o′ ℓ′ e′) where
  private
    Obj             = F.Obj             {o} {ℓ} {e} 𝒞
    Kl₀             = F.Kl₀             {o} {ℓ} {e} 𝒞
    Hom             = F.Hom             {o} {ℓ} {e} 𝒞
    KlMap           = F.KlMap           {o} {ℓ} {e} 𝒞
    idG             = F.idG             {o} {ℓ} {e} 𝒞
    ∘G              = F.∘G              {o} {ℓ} {e} 𝒞
    Kl-identity     = F.Kl-identity     {o} {ℓ} {e} 𝒞
    Kl-homomorphism = F.Kl-homomorphism {o} {ℓ} {e} 𝒞

    module ≡FE {C D : Category (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′)}
      = IsEquivalence (≡F-equiv {C = C} {D = D})

  opaque
    unfolding F.idG F.∘G F.KlMap

    GMon-identityˡ
      : ∀ {A B} {f : Hom A B}
      → _≡F_ {C = Kl₀ A} {D = Kl₀ B}
          (KlMap {A} {B} (∘G {A} {B} {B} (idG {B}) f)) (KlMap {A} {B} f)
    GMon-identityˡ {_} {ℐ , M} {Φ , ρ} = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ where
          (kx , fx , αx) →
            let open Category (Kl₀ (ℐ , M)); open HomReasoning in
            identityˡ
              ○ ≈-components 𝒞 ℐ M (CC.∘-resp-≈ˡ CC.identityˡ) (II.∘-resp-≈ʳ II.identityʳ)
              ○ ⟺ identityʳ
      }
      where
        module CC = Category 𝒞
        module II = MonoidalCategory ℐ

    GMon-identityʳ
      : ∀ {A B} {f : Hom A B}
      → _≡F_ {C = Kl₀ A} {D = Kl₀ B}
          (KlMap {A} {B} (∘G {A} {A} {B} f (idG {A}))) (KlMap {A} {B} f)
    GMon-identityʳ {_} {ℐ , M} {Φ , ρ} = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ where
          (kx , fx , αx) →
            let open Category (Kl₀ (ℐ , M)); open HomReasoning in
            identityˡ
              ○ ≈-components 𝒞 ℐ M (CC.∘-resp-≈ˡ CC.identityʳ) (II.∘-resp-≈ʳ (elimˡ Φ.identity))
              ○ ⟺ identityʳ
      }
      where
        module CC = Category 𝒞
        module II = MonoidalCategory ℐ
        module Φ  = MonoidalFunctor Φ
        open MR II.U

    GMon-assoc
      : ∀ {A B C D} {f : Hom A B} {g : Hom B C} {h : Hom C D}
      → _≡F_ {C = Kl₀ A} {D = Kl₀ D}
          (KlMap {A} {D} (∘G {A} {B} {D} (∘G {B} {C} {D} h g) f))
          (KlMap {A} {D} (∘G {A} {C} {D} h (∘G {A} {B} {C} g f)))
    GMon-assoc {_} {_} {_} {Jd , Md} {Φf , ρf} {Φg , ρg} {Φh , ρh} = record
      { eq₀ = λ _ → refl
      ; eq₁ = λ where
          (kx , fx , αx) →
            let open Category (Kl₀ (Jd , Md)); open HomReasoning in
            identityˡ
              ○ ≈-components 𝒞 Jd Md (CC.∘-resp-≈ˡ CC.assoc)
                  (II.∘-resp-≈ʳ (II.Equiv.sym (pushˡ Φh.homomorphism)))
              ○ ⟺ identityʳ
      }
      where
        module CC = Category 𝒞
        module II = MonoidalCategory Jd
        module Φh = MonoidalFunctor Φh
        open MR II.U

  GMon : Category (suc (o ⊔ ℓ ⊔ e) ⊔ o′ ⊔ ℓ′ ⊔ e′)
                  (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′)
                  (o ⊔ ℓ ⊔ ℓ′ ⊔ o′ ⊔ e ⊔ e′)
  GMon .Category.Obj = Obj
  GMon .Category._⇒_ = Hom
  GMon .Category._≈_ {A} {B} f g = _≡F_ {C = Kl₀ A} {D = Kl₀ B} (KlMap {A} {B} f) (KlMap {A} {B} g)
  GMon .Category.id = idG
  GMon .Category._∘_ {A} {B} {C} g f = ∘G {A} {B} {C} g f
  GMon .Category.assoc {A} {B} {C} {D} {f} {g} {h} = GMon-assoc {A} {B} {C} {D} {f} {g} {h}
  GMon .Category.sym-assoc {A} {B} {C} {D} {f} {g} {h} =
    ≡FE.sym {C = Kl₀ A} {D = Kl₀ D} (GMon-assoc {A} {B} {C} {D} {f} {g} {h})
  GMon .Category.identityˡ {A} {B} {f} = GMon-identityˡ {A} {B} {f}
  GMon .Category.identityʳ {A} {B} {f} = GMon-identityʳ {A} {B} {f}
  GMon .Category.identity² {A} = GMon-identityˡ {A} {A} {idG {A}}
  GMon .Category.equiv {A} {B} = record
    { refl  = ≡FE.refl  {C = Kl₀ A} {D = Kl₀ B}
    ; sym   = ≡FE.sym   {C = Kl₀ A} {D = Kl₀ B}
    ; trans = ≡FE.trans {C = Kl₀ A} {D = Kl₀ B}
    }
  GMon .Category.∘-resp-≈ {A} {B} {C} {f} {h} {g} {i} p q =
    ≡FE.trans {C = Kl₀ A} {D = Kl₀ C} (Kl-homomorphism {A} {B} {C} {f} {g})
      (≡FE.trans {C = Kl₀ A} {D = Kl₀ C} (∘F-resp-≡F p q)
        (≡FE.sym {C = Kl₀ A} {D = Kl₀ C} (Kl-homomorphism {A} {B} {C} {h} {i})))

  Kl : Functor GMon (Cats (o ⊔ o′) (o ⊔ ℓ ⊔ ℓ′) (o ⊔ ℓ ⊔ ℓ′ ⊔ e ⊔ e′))
  Kl .Functor.F₀ = Kl₀
  Kl .Functor.F₁ {A} {B} h = KlMap {A} {B} h
  Kl .Functor.identity {A} = _≡F_.natIso (Kl-identity {A})
  Kl .Functor.homomorphism {A} {B} {D} {f} {g} = _≡F_.natIso (Kl-homomorphism {A} {B} {D} {g} {f})
  Kl .Functor.F-resp-≈ p = _≡F_.natIso p
