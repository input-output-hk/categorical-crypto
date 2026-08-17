{-# OPTIONS --safe --without-K #-}

-- Restricting a UC setup to a wide subcategory 𝒲 ⊆ 𝒞 of admissible
-- computations — the general construction behind "feasible machines ⇒
-- computational security" and "Dolev–Yao-definable morphisms ⇒ symbolic
-- security".
--
-- `SetupSubcategory` is the closure data that makes 𝒲 carry the graded-Kleisli
-- structure again; a `Restriction` is the observational kernel, supplied
-- independently as a test presheaf ℰ′ on 𝒲 together with ν, the presentation
-- of ℰ′'s tests as ambient ones.

open import Level

open import CategoricalCrypto.UCSetup

module CategoricalCrypto.Abstract2.WideSubcategory
  {o ℓ e o′ ℓ′ e′ cs ℓs : Level} (𝕊 : UCSetup o ℓ e o′ ℓ′ e′ cs ℓs) where

open import Data.Product
open import Data.Unit

open import Categories.Category
open import Categories.Category.Instance.Setoids
open import Categories.Category.SubCategory (UCSetup.𝒞 𝕊)
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Construction.SubCategory (UCSetup.𝒞 𝕊)
open import Categories.Functor.Monoidal.Properties
open import Categories.Functor.Presheaf
open import Categories.Functor.Presheaf.Morphism
import Categories.KernelCongruence.Reindex as KernelReindex
open import Categories.Monad.Graded

open import CategoricalCrypto.Abstract2
open import CategoricalCrypto.Abstract2.Morphism
open import CategoricalCrypto.UCSetup.Morphism

open AbstractUC 𝕊

private variable
  w : Level
  A B C′ : 𝒞.Obj
  X Y : ℐ.Obj

------------------------------------------------------------------------
-- The closure data
------------------------------------------------------------------------

-- Like `SubCat`, but wide & with the extra structure to generate a `UCSetup`
record SetupSubcategory (w : Level) : Set (o ⊔ ℓ ⊔ o′ ⊔ ℓ′ ⊔ suc w) where
  field
    W        : A 𝒞.⇒ B → Set w
    W-id     : W (𝒞.id {A})
    W-∘      : {f : B 𝒞.⇒ C′} {g : A 𝒞.⇒ B} → W f → W g → W (f 𝒞.∘ g)
    W-return : W (return {A})
    W-sub    : (c : X ℐ.⇒ Y) → W (sub c {A})
    W-ext    : (V : ℐ.Obj) {f : A 𝒞.⇒ T₀ X B} → W f → W (ext V f)

  W-μ : W (μ X Y {A})
  W-μ {X = X} = W-ext X W-id

  W-T₁ : (V : ℐ.Obj) {f : A 𝒞.⇒ B} → W f → W (T₁ V f)
  W-T₁ V wf = W-∘ (W-sub ρ⇒) (W-ext V (W-∘ W-return wf))

  subCat : SubCat 𝒞.Obj
  subCat = record { U = λ A → A ; R = W ; Rid = W-id ; _∘R_ = W-∘ }

  𝒲 : Category o′ (ℓ′ ⊔ w) e′
  𝒲 = SubCategory subCat

  module 𝒲 = Category 𝒲

  ι : Functor 𝒲 𝒞
  ι = Sub subCat

  module ι = Functor ι

  ℳ|𝒲 : GradedKleisliTriple ℐ 𝒲
  ℳ|𝒲 = record
    { T₀               = T₀
    ; ext              = λ V f → ext V (proj₁ f) , W-ext V (proj₂ f)
    ; return           = return , W-return
    ; sub              = λ c → sub c , W-sub c
    ; ext-identityˡ    = ext-identityˡ
    ; ext-identityʳ    = ext-identityʳ
    ; ext-assoc        = ext-assoc
    ; ext-resp-≈       = ext-resp-≈
    ; sub-commute      = sub-commute
    ; sub-identity     = sub-identity
    ; sub-homomorphism = sub-homomorphism
    ; sub-resp-≈       = sub-resp-≈
    }

  -- The finest kernel 𝒲 may carry: the ambient tests, read along ι.
  ι*ℰ : Presheaf 𝒲 (Setoids cs ℓs)
  ι*ℰ = ℰ ∘F ι.op

  module Kι = KernelReindex ι.op ℰ

------------------------------------------------------------------------
-- The restricted setup
------------------------------------------------------------------------

-- A class of tests for 𝒲, presented as ambient ones by ν.
record Restriction (𝕎 : SetupSubcategory w)
                   : Set (o′ ⊔ ℓ′ ⊔ e′ ⊔ w ⊔ suc (cs ⊔ ℓs)) where
  open SetupSubcategory 𝕎

  field
    ℰ′ : Presheaf 𝒲 (Setoids cs ℓs)
    ν  : PresheafMorphism ι ℰ′ ℰ

  subSetup : UCSetup o ℓ e o′ (ℓ′ ⊔ w) e′ cs ℓs
  subSetup = record { 𝒞 = 𝒲 ; ℐ = ℐ ; ℳ = ℳ|𝒲 ; ℰ = ℰ′ }

  -- The inclusion 𝒲 ↪ 𝒞 as a morphism of setups
  inclusion : UCSetupMorphism subSetup 𝕊
  inclusion = record
    { effect = record
      { F = ι ; Φ = idF-Monoidal ℐ ; κ = 𝒞.id
      ; isGradedKleisliMorphism = record
        { κ-return = identityˡ ○ introˡ sub-identity
        ; κ-ext = λ _ → identityˡ ○ ext-resp-≈ (⟺ identityˡ) ○ ⟺ identityʳ
                                  ○ introˡ sub-identity
        ; κ-sub = λ _ → id-comm-sym
        }
      }
    ; ν = ν
    }
    where open 𝒞

-- The finest restriction
fine : (𝕎 : SetupSubcategory w) → Restriction 𝕎
fine 𝕎 = record { ℰ′ = ι*ℰ ; ν = pullbackᵛ ι ℰ }
  where open SetupSubcategory 𝕎

module Restrict (𝕎 : SetupSubcategory w) (𝕂 : Restriction 𝕎) where
  open SetupSubcategory 𝕎
  open Restriction 𝕂

  module R = AbstractUC subSetup
  module T = Transfer inclusion

  coarsen : PresheafMorphism idF ι*ℰ ℰ′
          → UCSetupMorphism (Restriction.subSetup (fine 𝕎)) subSetup
  coarsen = changeKernel ι*ℰ ℰ′

  epi⇒coarsens : (c : PresheafMorphism idF ι*ℰ ℰ′)
               → PresheafMorphism.Epi c → T.Reflects-≈ℰ
  epi⇒coarsens c epi e = epi⇒preserves c epi (Kι.∼⇒∼∘ e)

  module Coarsens (coarsens : T.Reflects-≈ℰ) where

    restrict-≈ᵁ : {f g : 𝒲 [ A , T₀ X B ]} → ι.₁ f ≈ᵁ ι.₁ g → f R.≈ᵁ g
    restrict-≈ᵁ e Y = coarsens (e Y)

    restrict-≤UC : {f : 𝒲 [ A , T₀ X B ]} {g : 𝒲 [ A , T₀ Y B ]}
                 → ι.₁ f ≤UC ι.₁ g → f R.≤UC g
    restrict-≤UC f≤g a = let (s , e) = f≤g a in s , restrict-≈ᵁ e

    restrict-dummy : {f : 𝒲 [ A , T₀ X B ]} {g : 𝒲 [ A , T₀ Y B ]}
                   → Σ[ s₀ ∈ Y ℐ.⇒ X ] ι.₁ f ≈ᵁ sub s₀ 𝒞.∘ ι.₁ g
                   → Σ[ s₀ ∈ Y ℐ.⇒ X ] f R.≈ᵁ R.sub s₀ 𝒲.∘ g
    restrict-dummy (s₀ , e) = s₀ , restrict-≈ᵁ e

  module Preserves (preserves : T.Preserves-≈ℰ) where

    unrestrict-≈ᵁ : {f g : 𝒲 [ A , T₀ X B ]} → f R.≈ᵁ g → ι.₁ f ≈ᵁ ι.₁ g
    unrestrict-≈ᵁ e Y = preserves (e Y)

    unrestrict-≤UC : {f : 𝒲 [ A , T₀ X B ]} {g : 𝒲 [ A , T₀ Y B ]}
                   → f R.≤UC g → ι.₁ f ≤UC ι.₁ g
    unrestrict-≤UC f≤g a = let (s , e) = f≤g a in s , unrestrict-≈ᵁ e

------------------------------------------------------------------------
-- The canonical supplier: ℰ′ = ι*ℰ
------------------------------------------------------------------------

module Fine (𝕎 : SetupSubcategory w) where
  open SetupSubcategory 𝕎
  open Restrict 𝕎 (fine 𝕎) public

  open Coarsens Kι.∼⇒∼∘ public
  open Preserves Kι.∼∘⇒∼ public

------------------------------------------------------------------------
-- The widest subcategory
------------------------------------------------------------------------

module Trivial where
  everything : SetupSubcategory 0ℓ
  everything = record
    { W = λ _ → ⊤ ; W-id = tt ; W-∘ = λ _ _ → tt
    ; W-return = tt ; W-sub = λ _ → tt ; W-ext = λ _ _ → tt }

  open Fine everything

  to : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → f ≤UC g → (f , tt) R.≤UC (g , tt)
  to = restrict-≤UC

  from : {f : A 𝒞.⇒ T₀ X B} {g : A 𝒞.⇒ T₀ Y B} → (f , tt) R.≤UC (g , tt) → f ≤UC g
  from = unrestrict-≤UC
