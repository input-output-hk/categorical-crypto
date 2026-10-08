{-# OPTIONS --safe --without-K #-}

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence
  (sig : APROPSignature) where

open APROP sig
open FreeMonoidalHelper Symm X using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-flatten-≈; unflatten-++-≅; bridge
        ; subst-id-cod; subst-id-dom; subst-id-cod-trans; subst-cod-cons; cast-cancel′; cod-cancel )

open import Categories.Category
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal using (module Kelly's)
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning FreeMonoidal using (cancelˡ; pullˡ; elim-center)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)

open import Data.Fin.Patterns
open import Data.List.Properties
import Data.List.Properties.Ext as ListExt
import Data.Vec as Vec

open Kelly's using (coherence₃)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

bridge-∘
  : ∀ {A B C} (g : HomTerm B C) (f : HomTerm A B)
  → bridge (g ∘ f) ≈Term bridge g ∘ bridge f
bridge-∘ {B = B} g f =
  ⟺ (cancel-mid-iso (_≅_.isoˡ (unflatten-flatten-≈ B)))

bridge-⊗
  : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
  → bridge (f ⊗₁ g)
  ≈Term _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
       ∘ (bridge f ⊗₁ bridge g)
       ∘ _≅_.from (unflatten-++-≅ (flatten A) (flatten C))
bridge-⊗ {A} {B} {C} {D} f g = solveMor! lhsᵗ rhsᵗ
  where
    open FinSetup FMC
      ( A Vec.∷ B Vec.∷ C Vec.∷ D
          Vec.∷ unflatten (flatten A) Vec.∷ unflatten (flatten B)
          Vec.∷ unflatten (flatten C) Vec.∷ unflatten (flatten D)
          Vec.∷ unflatten (flatten A ++ flatten C)
          Vec.∷ unflatten (flatten B ++ flatten D) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
    v5 = V 5F ; v6 = V 6F ; v7 = V 7F ; v8 = V 8F ; v9 = V 9F
    open Sig {8} (λ { 0F → v0 , v1
                    ; 1F → v2 , v3
                    ; 2F → v1 , v5
                    ; 3F → v3 , v7
                    ; 4F → v4 , v0
                    ; 5F → v6 , v2
                    ; 6F → v5 ⊗ᵒ v7 , v9
                    ; 7F → v8 , v4 ⊗ᵒ v6 })
    open WithGen (λ { (genS 0F) → f
                    ; (genS 1F) → g
                    ; (genS 2F) → _≅_.from (unflatten-flatten-≈ B)
                    ; (genS 3F) → _≅_.from (unflatten-flatten-≈ D)
                    ; (genS 4F) → _≅_.to   (unflatten-flatten-≈ A)
                    ; (genS 5F) → _≅_.to   (unflatten-flatten-≈ C)
                    ; (genS 6F) → _≅_.to   (unflatten-++-≅ (flatten B) (flatten D))
                    ; (genS 7F) → _≅_.from (unflatten-++-≅ (flatten A) (flatten C)) })
    gf = gen 0F ; gg = gen 1F ; gFB = gen 2F ; gFD = gen 3F
    gTA = gen 4F ; gTC = gen 5F ; gcBD = gen 6F ; gcAC = gen 7F
    lhsᵗ rhsᵗ : S.HomTerm v8 v9
    lhsᵗ = S._∘_ (S._∘_ gcBD (S._⊗₁_ gFB gFD))
                 (S._∘_ (S._⊗₁_ gf gg) (S._∘_ (S._⊗₁_ gTA gTC) gcAC))
    rhsᵗ = S._∘_ gcBD
                 (S._∘_ (S._⊗₁_ (S._∘_ gFB (S._∘_ gf gTA))
                                (S._∘_ gFD (S._∘_ gg gTC)))
                        gcAC)

bridge-id-is-id : ∀ A → bridge (id {A}) ≈Term id
bridge-id-is-id A = (refl⟩∘⟨ idˡ) ○ _≅_.isoʳ (unflatten-flatten-≈ A)

-- One-sided inverses pass through bridge; inv-resp derives ⇐ from ⇒ below.
bridge-resp-≈Term : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → bridge f ≈Term bridge g
bridge-resp-≈Term f≈g = refl⟩∘⟨ f≈g ⟩∘⟨refl

bridge-inv-id
  : ∀ {A B} (g : HomTerm B A) (f : HomTerm A B)
  → g ∘ f ≈Term id → bridge g ∘ bridge f ≈Term id
bridge-inv-id {A} g f e =
  ≈-Term-trans (≈-Term-sym (bridge-∘ g f))
    (≈-Term-trans (bridge-resp-≈Term e) (bridge-id-is-id A))

absorb-slide
  : ∀ {A₀ A₁ A₂ A₃ A₄ : ObjTerm}
      {W : HomTerm A₀ A₁} {V : HomTerm A₁ A₂} {U₁ : HomTerm A₂ A₃}
      {U₂ : HomTerm A₁ A₄} {T : HomTerm A₄ A₃} {F : HomTerm A₃ A₄}
  → U₁ ∘ V ≈Term T ∘ U₂ → F ∘ T ≈Term id
  → F ∘ U₁ ∘ V ∘ W ≈Term U₂ ∘ W
absorb-slide nat iso = (refl⟩∘⟨ pullˡ nat) ○ (refl⟩∘⟨ FM.assoc) ○ cancelˡ iso

bridge-λ⇒-is-id : ∀ A → bridge (λ⇒ {A}) ≈Term id
bridge-λ⇒-is-id A =
  absorb-slide λ⇒∘id⊗f≈f∘λ⇒ (_≅_.isoʳ (unflatten-flatten-≈ A)) ○ λ⇒∘λ⇐≈id

bridge-λ⇐-is-id : ∀ A → bridge (λ⇐ {A}) ≈Term id
bridge-λ⇐-is-id A =
  inv-resp (bridge-inv-id λ⇐ λ⇒ λ⇐∘λ⇒≈id) idˡ (bridge-λ⇒-is-id A)

bridge-ρ⇒-form
  : ∀ A → bridge (ρ⇒ {A})
       ≈Term ρ⇒ {unflatten (flatten A)}
              ∘ _≅_.from (unflatten-++-≅ (flatten A) [])
bridge-ρ⇒-form A =
  absorb-slide ρ⇒∘f⊗id≈f∘ρ⇒ (_≅_.isoʳ (unflatten-flatten-≈ A))

ρ⇒-coh-list
  : ∀ (xs : List X)
  → subst-id-cod (++-identityʳ xs)
    ≈Term ρ⇒ {unflatten xs} ∘ _≅_.from (unflatten-++-≅ xs [])
ρ⇒-coh-list []       = ⟺ λ⇒∘λ⇐≈id ○ (coherence₃ ⟩∘⟨refl)
ρ⇒-coh-list (y ∷ ys) = begin
  subst-id-cod (++-identityʳ (y ∷ ys))
    ≈⟨ ≈-Term-sym (subst-cod-cons (++-identityʳ ys)) ⟩
  id {Var y} ⊗₁ subst-id-cod (++-identityʳ ys)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (ρ⇒-coh-list ys) ⟩
  id ⊗₁ (ρ⇒ ∘ inner-from)
    ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
  ρ⇒ ∘ α⇐ ∘ id ⊗₁ inner-from ∎
  where
    inner-from = _≅_.from (unflatten-++-≅ ys [])

    open FinSetup FMC
      ( Var y Vec.∷ unflatten ys Vec.∷ unflatten (ys ++ []) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F
    open Sig {1} (λ { 0F → v2 , v1 ⊗ᵒ unitᵒ })
    open WithGen (λ { (genS 0F) → inner-from })
    g0 = gen 0F
    lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v2) (v0 ⊗ᵒ v1)
    lhsᵗ = S._⊗₁_ S.id (S._∘_ S.ρ⇒ g0)
    rhsᵗ = S._∘_ S.ρ⇒ (S._∘_ S.α⇐ (S._⊗₁_ S.id g0))

ρ⇒-coherence
  : ∀ A → subst-id-cod (++-identityʳ (flatten A)) ≈Term bridge (ρ⇒ {A})
ρ⇒-coherence A =
  ≈-Term-trans (ρ⇒-coh-list (flatten A)) (≈-Term-sym (bridge-ρ⇒-form A))

ρ⇐-coherence
  : ∀ A → subst-id-dom (++-identityʳ (flatten A)) ≈Term bridge (ρ⇐ {A})
ρ⇐-coherence A =
  inv-resp (cast-cancel′ (++-identityʳ (flatten A)))
           (bridge-inv-id ρ⇒ ρ⇐ ρ⇒∘ρ⇐≈id)
           (ρ⇒-coherence A)

--------------------------------------------------------------------------------
-- Associator coherence
--------------------------------------------------------------------------------
pentagon-rewrite
  : ∀ {A B C D}
  → α⇒ {A ⊗₀ B} {C} {D}
  ≈Term α⇐ {A} {B} {C ⊗₀ D}
        ∘ id {A} ⊗₁ α⇒ {B} {C} {D}
        ∘ α⇒ {A} {B ⊗₀ C} {D}
        ∘ α⇒ {A} {B} {C} ⊗₁ id {D}
pentagon-rewrite {A} {B} {C} {D} = solveMor! lhsᵗ rhsᵗ
  where
    open FinSetup FMC ( A Vec.∷ B Vec.∷ C Vec.∷ D Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F
    open Sig {0} (λ ())
    open WithGen (λ { (genS ()) })
    lhsᵗ rhsᵗ : S.HomTerm (((v0 ⊗ᵒ v1) ⊗ᵒ v2) ⊗ᵒ v3) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
    lhsᵗ = S.α⇒
    rhsᵗ = S._∘_ S.α⇐ (S._∘_ (S._⊗₁_ S.id S.α⇒) (S._∘_ S.α⇒ (S._⊗₁_ S.α⇒ S.id)))

-- The paired iso legs cancel outside the free-monoidal fragment solveMor! decides.

private
  -- Put the prefix last so both base cases share the same generator interpretation.
  module Setup6 (B C P : ObjTerm) where
    F-B = _≅_.from (unflatten-flatten-≈ B)
    F-C = _≅_.from (unflatten-flatten-≈ C)
    T-B = _≅_.to   (unflatten-flatten-≈ B)
    T-C = _≅_.to   (unflatten-flatten-≈ C)
    cBC-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten C))
    cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

    open FinSetup FMC
      ( B Vec.∷ C
          Vec.∷ unflatten (flatten B) Vec.∷ unflatten (flatten C)
          Vec.∷ unflatten (flatten B ++ flatten C) Vec.∷ P Vec.∷ Vec.[] )
      public using (V; _⊗ᵒ_; module Sig)
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F ; v5 = V 5F
    open Sig {6} (λ { 0F → v0 , v2
                    ; 1F → v1 , v3
                    ; 2F → v2 , v0
                    ; 3F → v3 , v1
                    ; 4F → v2 ⊗ᵒ v3 , v4
                    ; 5F → v4 , v2 ⊗ᵒ v3 })
      public using (module S; genS; gen; module WithGen)
    open WithGen (λ { (genS 0F) → F-B ; (genS 1F) → F-C
                    ; (genS 2F) → T-B ; (genS 3F) → T-C
                    ; (genS 4F) → cBC-to ; (genS 5F) → cBC-from })
      public using (solveMor!)
    gFB = gen 0F ; gFC = gen 1F ; gTB = gen 2F ; gTC = gen 3F
    gcto = gen 4F ; gcfrom = gen 5F

    collapse-c-FT : cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from ≈Term id
    collapse-c-FT =
      elim-center (⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ B))
                            (_≅_.isoʳ (unflatten-flatten-≈ C))
                   ○ id⊗id≈id)
      ○ _≅_.isoˡ (unflatten-++-≅ (flatten B) (flatten C))

bridge-α⇒-is-id-Var : ∀ x B C → bridge (α⇒ {Var x} {B} {C}) ≈Term id
bridge-α⇒-is-id-Var x B C = begin
  bridge (α⇒ {Var x} {B} {C})
    ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
  id {Var x} ⊗₁ (cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl collapse-c-FT ⟩
  id {Var x} ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎
  where
    open Setup6 B C (Var x)
    lhsᵗ rhsᵗ : S.HomTerm (v5 ⊗ᵒ v4) (v5 ⊗ᵒ v4)
    lhsᵗ = S._∘_
             (S._∘_ (S._∘_ (S._⊗₁_ S.id S.λ⇒) S.α⇒)
                    (S._⊗₁_ S.ρ⇐ (S._∘_ gcto (S._⊗₁_ gFB gFC))))
             (S._∘_ S.α⇒
               (S._∘_
                 (S._⊗₁_ (S._∘_ (S._⊗₁_ S.ρ⇒ gTB)
                                (S._∘_ S.α⇐ (S._⊗₁_ S.id S.λ⇐)))
                         gTC)
                 (S._∘_ S.α⇐ (S._⊗₁_ S.id gcfrom))))
    rhsᵗ = S._⊗₁_ S.id
             (S._∘_ gcto
               (S._∘_ (S._⊗₁_ (S._∘_ gFB gTB) (S._∘_ gFC gTC)) gcfrom))

bridge-α⇒-is-id-unit : ∀ B C → bridge (α⇒ {unit} {B} {C}) ≈Term id
bridge-α⇒-is-id-unit B C = begin
  bridge (α⇒ {unit} {B} {C})
    ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
  cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from
    ≈⟨ collapse-c-FT ⟩
  id ∎
  where
    open Setup6 B C unit
    lhsᵗ rhsᵗ : S.HomTerm v4 v4
    lhsᵗ = S._∘_
             (S._∘_ S.λ⇒
                    (S._⊗₁_ S.id (S._∘_ gcto (S._⊗₁_ gFB gFC))))
             (S._∘_ S.α⇒
               (S._∘_
                 (S._⊗₁_ (S._∘_ (S._⊗₁_ S.id gTB) S.λ⇐) gTC)
                 gcfrom))
    rhsᵗ = S._∘_ gcto (S._∘_ (S._⊗₁_ (S._∘_ gFB gTB) (S._∘_ gFC gTC)) gcfrom)

--------------------------------------------------------------------------------
-- Associator casts
--------------------------------------------------------------------------------

-- Morphism congruence rewrites individual cast legs without requiring
-- cancellation of trans at the equality-proof level.

private
  cto : (as bs : List X) → HomTerm (unflatten as ⊗₀ unflatten bs) (unflatten (as ++ bs))
  cto as bs = _≅_.to (unflatten-++-≅ as bs)

  cfrom : (as bs : List X) → HomTerm (unflatten (as ++ bs)) (unflatten as ⊗₀ unflatten bs)
  cfrom as bs = _≅_.from (unflatten-++-≅ as bs)

  bridge-⊗-resp
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
        {rf : HomTerm (unflatten (flatten A)) (unflatten (flatten B))}
        {rg : HomTerm (unflatten (flatten C)) (unflatten (flatten D))}
    → bridge f ≈Term rf → bridge g ≈Term rg
    → bridge (f ⊗₁ g)
      ≈Term cto (flatten B) (flatten D) ∘ (rf ⊗₁ rg) ∘ cfrom (flatten A) (flatten C)
  bridge-⊗-resp f g ef eg = bridge-⊗ f g ○ (refl⟩∘⟨ ⊗-resp-≈ ef eg ⟩∘⟨refl)

  cast-inʳ
    : ∀ (p : List X) {as bs : List X} (e : as ≡ bs)
    → cto p bs ∘ (id ⊗₁ subst-id-cod e) ∘ cfrom p as
      ≈Term subst-id-cod (cong (p ++_) e)
  cast-inʳ p refl = elim-center id⊗id≈id ○ _≅_.isoˡ (unflatten-++-≅ p _)

  cast-inˡ
    : ∀ {as bs : List X} (e : as ≡ bs) (p : List X)
    → cto bs p ∘ (subst-id-cod e ⊗₁ id) ∘ cfrom as p
      ≈Term subst-id-cod (cong (_++ p) e)
  cast-inˡ refl p = elim-center id⊗id≈id ○ _≅_.isoˡ (unflatten-++-≅ _ p)

  cast-≡
    : ∀ {as bs : List X} {e e' : as ≡ bs} → e ≡ e'
    → subst-id-cod e ≈Term subst-id-cod e'
  cast-≡ refl = ≈-Term-refl

private
  cast-pentagon
    : ∀ (p a b c : List X)
    → subst-id-cod (sym (++-assoc p a (b ++ c)))
      ∘ subst-id-cod (cong (p ++_) (++-assoc a b c))
      ∘ subst-id-cod (++-assoc p (a ++ b) c)
      ∘ subst-id-cod (cong (_++ c) (++-assoc p a b))
      ≈Term subst-id-cod (++-assoc (p ++ a) b c)
  cast-pentagon p a b c =
    (refl⟩∘⟨ refl⟩∘⟨ subst-id-cod-trans _ _)
    ○ (refl⟩∘⟨ subst-id-cod-trans _ _)
    ○ subst-id-cod-trans _ _
    ○ cast-≡ (ListExt.≡-irrelevant _≟X_ _ _)

module Worker where

  work
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
    ≈Term subst-id-cod (++-assoc (flatten A) (flatten B) (flatten C))

  -- The mutual work → derive-⇐ → work call descends to a structural
  -- subterm of the first argument.
  derive-⇐
    : ∀ A B C
    → bridge (α⇐ {A} {B} {C})
    ≈Term subst-id-cod (sym (++-assoc (flatten A) (flatten B) (flatten C)))
  derive-⇐ A B C =
    inv-resp (bridge-inv-id α⇐ α⇒ α⇐∘α⇒≈id)
             (cod-cancel (++-assoc (flatten A) (flatten B) (flatten C)))
             (work A B C)

  work unit    B C = bridge-α⇒-is-id-unit B C
  work (Var x) B C = bridge-α⇒-is-id-Var x B C

  -- Keep recursive calls in the matched clause so structural descent is visible.
  work (A₁ ⊗₀ A₂) B C = begin
    bridge (α⇒ {A₁ ⊗₀ A₂} {B} {C})
      ≈⟨ bridge-resp-≈Term pentagon-rewrite ⟩
    bridge ( α⇐ {A₁} {A₂} {B ⊗₀ C}
           ∘ id {A₁} ⊗₁ α⇒ {A₂} {B} {C}
           ∘ α⇒ {A₁} {A₂ ⊗₀ B} {C}
           ∘ α⇒ {A₁} {A₂} {B} ⊗₁ id {C} )
      ≈⟨ bridge-∘ _ _ ○ (refl⟩∘⟨ bridge-∘ _ _) ○ (refl⟩∘⟨ refl⟩∘⟨ bridge-∘ _ _) ⟩
    bridge (α⇐ {A₁} {A₂} {B ⊗₀ C})
      ∘ bridge (id {A₁} ⊗₁ α⇒ {A₂} {B} {C})
      ∘ bridge (α⇒ {A₁} {A₂ ⊗₀ B} {C})
      ∘ bridge (α⇒ {A₁} {A₂} {B} ⊗₁ id {C})
      ≈⟨ derive-⇐ A₁ A₂ (B ⊗₀ C)
         ⟩∘⟨ ( bridge-⊗-resp (id {A₁}) (α⇒ {A₂} {B} {C})
                             (bridge-id-is-id A₁) (work A₂ B C)
               ○ cast-inʳ (flatten A₁) (++-assoc (flatten A₂) (flatten B) (flatten C)) )
         ⟩∘⟨ work A₁ (A₂ ⊗₀ B) C
         ⟩∘⟨ ( bridge-⊗-resp (α⇒ {A₁} {A₂} {B}) (id {C})
                             (work A₁ A₂ B) (bridge-id-is-id C)
               ○ cast-inˡ (++-assoc (flatten A₁) (flatten A₂) (flatten B)) (flatten C) )
         ○ cast-pentagon (flatten A₁) (flatten A₂) (flatten B) (flatten C) ⟩
    subst-id-cod (++-assoc (flatten A₁ ++ flatten A₂) (flatten B) (flatten C)) ∎
