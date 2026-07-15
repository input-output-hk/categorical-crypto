{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Bridge-level coherence toolkit: bridge distributivity (`bridge-∘`,
-- `bridge-⊗`), the `bridge-X-is-id` lemmas, ρ/α bridge forms and
-- list-coherence, the α-form isos, and assorted Mac Lane / solver helpers.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.Category.Monoidal using (Monoidal; MonoidalCategory)

module Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence
  (sig : APROPSignature) where

open APROP sig
-- `bridge-∘` / `bridge-⊗` are the factored-out distributivity lemmas; we
-- re-export them so this module's downstream consumers (Strict/Boundary,
-- Discharge/Sub/HomTermTransport, Discharge/BridgeAlphaFormCompound) keep
-- resolving `bridge-∘` / `bridge-⊗` through `BridgeCoherence`.
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeOps sig
  using (bridge-∘; bridge-⊗) public
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig
  using (bridge)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (module Kelly's)
open Kelly's using (coherence₃)
-- Morphism-variable monoidal solver: discharges the structural-coherence /
-- naturality / interchange chases as single `solveMor!` calls at the free
-- monoidal category itself (cf. `Discharge/BridgeAlphaFormCompound.agda`).
open import Categories.Coherence.Monoidal.Frontend using (module FinSetup)
open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F)
import Data.Vec as Vec
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (subst-∘)

private
  module FM = Category FreeMonoidal

  -- the free monoidal category itself, as the solver's target bundle.
  FMC : MonoidalCategory _ _ _
  FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Foundation lemmas `bridge-∘` / `bridge-⊗` are re-exported from
-- `Soundness.BridgeOps` (see the import section above).

--------------------------------------------------------------------------------
-- `bridge (id {A}) ≈Term id`: the iso `unflatten-flatten-≈ A` cancels.

bridge-id-is-id : ∀ A → bridge (id {A}) ≈Term id
bridge-id-is-id A = begin
  _≅_.from (unflatten-flatten-≈ A) ∘ id ∘ _≅_.to (unflatten-flatten-≈ A)
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  _≅_.from (unflatten-flatten-≈ A) ∘ _≅_.to (unflatten-flatten-≈ A)
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩
  id ∎

--------------------------------------------------------------------------------
-- bridge (λ⇒) and bridge (λ⇐) reduce to `id`.

bridge-λ⇒-is-id : ∀ A → bridge (λ⇒ {A}) ≈Term id
bridge-λ⇒-is-id A = begin
  F-A ∘ λ⇒ ∘ (id ⊗₁ T-A) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-A ∘ (λ⇒ ∘ (id ⊗₁ T-A)) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
  F-A ∘ (T-A ∘ λ⇒) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  F-A ∘ T-A ∘ λ⇒ ∘ λ⇐
    ≈⟨ FM.sym-assoc ⟩
  (F-A ∘ T-A) ∘ λ⇒ ∘ λ⇐
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩∘⟨refl ⟩
  id ∘ λ⇒ ∘ λ⇐
    ≈⟨ idˡ ⟩
  λ⇒ ∘ λ⇐
    ≈⟨ λ⇒∘λ⇐≈id ⟩
  id ∎
  where
    F-A = _≅_.from (unflatten-flatten-≈ A)
    T-A = _≅_.to   (unflatten-flatten-≈ A)

bridge-λ⇐-is-id : ∀ A → bridge (λ⇐ {A}) ≈Term id
bridge-λ⇐-is-id A = begin
  (λ⇒ ∘ id ⊗₁ F-A) ∘ (λ⇐ ∘ T-A)
    ≈⟨ λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl ⟩
  (F-A ∘ λ⇒) ∘ (λ⇐ ∘ T-A)
    ≈⟨ FM.assoc ⟩
  F-A ∘ (λ⇒ ∘ (λ⇐ ∘ T-A))
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-A ∘ ((λ⇒ ∘ λ⇐) ∘ T-A)
    ≈⟨ refl⟩∘⟨ (λ⇒∘λ⇐≈id ⟩∘⟨refl) ⟩
  F-A ∘ (id ∘ T-A)
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  F-A ∘ T-A
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩
  id ∎
  where
    F-A = _≅_.from (unflatten-flatten-≈ A)
    T-A = _≅_.to   (unflatten-flatten-≈ A)

--------------------------------------------------------------------------------
-- Helpers for chaining `_≡_` and `≈Term`, and for transporting `≈Term`
-- across `subst₂`.

-- `≡⇒≈Term` lives in `Categories.FreeMonoidal`, reachable everywhere via
-- `open APROP sig`.

subst₂-resp-≈Term
  : ∀ {As Bs As' Bs' : List X} (eq-As : As ≡ As') (eq-Bs : Bs ≡ Bs')
      {f g : HomTerm (unflatten As) (unflatten Bs)}
  → f ≈Term g
  → subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) f
    ≈Term subst₂ HomTerm (cong unflatten eq-As) (cong unflatten eq-Bs) g
subst₂-resp-≈Term refl refl f≈g = f≈g

--------------------------------------------------------------------------------
-- `subst (cong unflatten _)`-of-`id` workhorses.

subst₂-refl-cod
  : ∀ {As As' : List X} (eq : As ≡ As')
  → subst₂ HomTerm refl (cong unflatten eq) (id {unflatten As})
  ≡ subst (λ z → HomTerm (unflatten As) (unflatten z)) eq id
subst₂-refl-cod refl = refl

subst₂-refl-dom
  : ∀ {As As' : List X} (eq : As ≡ As')
  → subst₂ HomTerm (cong unflatten eq) refl (id {unflatten As})
  ≡ subst (λ z → HomTerm (unflatten z) (unflatten As)) eq id
subst₂-refl-dom refl = refl

subst-cod-cons
  : ∀ (y : X) {as as' : List X} (eq : as ≡ as')
  → subst (λ z → HomTerm (Var y ⊗₀ unflatten as) (Var y ⊗₀ unflatten z)) eq id
  ≈Term id {Var y} ⊗₁ subst (λ z → HomTerm (unflatten as) (unflatten z)) eq id
subst-cod-cons y refl = ≈-Term-sym id⊗id≈id

subst-dom-cons
  : ∀ (y : X) {as as' : List X} (eq : as ≡ as')
  → subst (λ z → HomTerm (Var y ⊗₀ unflatten z) (Var y ⊗₀ unflatten as)) eq id
  ≈Term id {Var y} ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten as)) eq id
subst-dom-cons y refl = ≈-Term-sym id⊗id≈id

-- The shared first step of all four `*-coh-list` cons cases: push the
-- `cong (y ∷_)` of a `subst` through `unflatten` via `subst-∘`, re-binding
-- the substituted variable to the tail.  `L`/`R` are the dom/cod endpoints.
cons-coh-step
  : ∀ (y : X) {as as' : List X} (eq : as ≡ as') (L R : List X → ObjTerm)
      (m : HomTerm (L (y ∷ as)) (R (y ∷ as)))
  → subst (λ z → HomTerm (L z) (R z)) (cong (y ∷_) eq) m
    ≈Term subst (λ z → HomTerm (L (y ∷ z)) (R (y ∷ z))) eq m
cons-coh-step y eq L R m =
  ≡⇒≈Term (sym (subst-∘ {P = λ z → HomTerm (L z) (R z)} {f = y ∷_} eq))

--------------------------------------------------------------------------------
-- Bridge form for ρ⇒.

bridge-ρ⇒-form
  : ∀ A → bridge (ρ⇒ {A})
       ≈Term ρ⇒ {unflatten (flatten A)}
              ∘ _≅_.from (unflatten-++-≅ (flatten A) [])
bridge-ρ⇒-form A = begin
  F-A ∘ ρ⇒ ∘ (T-A ⊗₁ id) ∘ cAA-from
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  F-A ∘ (ρ⇒ ∘ (T-A ⊗₁ id)) ∘ cAA-from
    ≈⟨ refl⟩∘⟨ ρ⇒∘f⊗id≈f∘ρ⇒ ⟩∘⟨refl ⟩
  F-A ∘ (T-A ∘ ρ⇒) ∘ cAA-from
    ≈⟨ refl⟩∘⟨ FM.assoc ⟩
  F-A ∘ T-A ∘ ρ⇒ ∘ cAA-from
    ≈⟨ FM.sym-assoc ⟩
  (F-A ∘ T-A) ∘ ρ⇒ ∘ cAA-from
    ≈⟨ _≅_.isoʳ (unflatten-flatten-≈ A) ⟩∘⟨refl ⟩
  id ∘ ρ⇒ ∘ cAA-from
    ≈⟨ idˡ ⟩
  ρ⇒ ∘ cAA-from ∎
  where
    F-A = _≅_.from (unflatten-flatten-≈ A)
    T-A = _≅_.to   (unflatten-flatten-≈ A)
    cAA-from = _≅_.from (unflatten-++-≅ (flatten A) [])

--------------------------------------------------------------------------------
-- ρ⇐-naturality, derived from ρ⇒-naturality + iso laws.

ρ⇐-naturality : ∀ {A B} (f : HomTerm A B) → ρ⇐ {B} ∘ f ≈Term f ⊗₁ id ∘ ρ⇐ {A}
ρ⇐-naturality {A} {B} f = solveMor! lhsᵗ rhsᵗ
  where
    open FinSetup FMC ( A Vec.∷ B Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F
    open Sig {1} (λ { 0F → v0 , v1 })
    open WithGen (λ { (genS 0F) → f })
    g0 = gen 0F
    lhsᵗ rhsᵗ : S.HomTerm v0 (v1 ⊗ᵒ unitᵒ)
    lhsᵗ = S._∘_ S.ρ⇐ g0
    rhsᵗ = S._∘_ (S._⊗₁_ g0 S.id) S.ρ⇐

--------------------------------------------------------------------------------
-- Bridge form for ρ⇐.

bridge-ρ⇐-form
  : ∀ A → bridge (ρ⇐ {A})
       ≈Term _≅_.to (unflatten-++-≅ (flatten A) [])
              ∘ ρ⇐ {unflatten (flatten A)}
bridge-ρ⇐-form A = begin
  (cAA-to ∘ F-A ⊗₁ id) ∘ ρ⇐ ∘ T-A
    ≈⟨ FM.assoc ⟩
  cAA-to ∘ (F-A ⊗₁ id) ∘ (ρ⇐ ∘ T-A)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ρ⇐-naturality T-A ⟩
  cAA-to ∘ (F-A ⊗₁ id) ∘ (T-A ⊗₁ id ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  cAA-to ∘ ((F-A ⊗₁ id) ∘ T-A ⊗₁ id) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
  cAA-to ∘ (F-A ∘ T-A) ⊗₁ (id ∘ id) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ A)) idˡ ⟩∘⟨refl ⟩
  cAA-to ∘ id ⊗₁ id ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
  cAA-to ∘ id ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ idˡ ⟩
  cAA-to ∘ ρ⇐ ∎
  where
    F-A    = _≅_.from (unflatten-flatten-≈ A)
    T-A    = _≅_.to   (unflatten-flatten-≈ A)
    cAA-to = _≅_.to   (unflatten-++-≅ (flatten A) [])

--------------------------------------------------------------------------------
-- List-coherence for ρ⇒.

ρ⇒-coh-list
  : ∀ (xs : List X)
  → subst (λ z → HomTerm (unflatten (xs ++ [])) (unflatten z))
          (++-identityʳ xs) id
    ≈Term ρ⇒ {unflatten xs} ∘ _≅_.from (unflatten-++-≅ xs [])
ρ⇒-coh-list []       = begin
  id           ≈⟨ ≈-Term-sym λ⇒∘λ⇐≈id ⟩
  λ⇒ ∘ λ⇐      ≈⟨ coherence₃ ⟩∘⟨refl ⟩
  ρ⇒ ∘ λ⇐      ∎
ρ⇒-coh-list (y ∷ ys) = begin
  subst (λ z → HomTerm (Var y ⊗₀ unflatten (ys ++ [])) (unflatten z))
        (cong (y ∷_) (++-identityʳ ys)) id
    ≈⟨ cons-coh-step y (++-identityʳ ys)
         (λ _ → Var y ⊗₀ unflatten (ys ++ [])) (λ z → unflatten z) id ⟩
  subst (λ z → HomTerm (Var y ⊗₀ unflatten (ys ++ []))
                        (Var y ⊗₀ unflatten z))
        (++-identityʳ ys) id
    ≈⟨ subst-cod-cons y (++-identityʳ ys) ⟩
  id ⊗₁ subst (λ z → HomTerm (unflatten (ys ++ [])) (unflatten z))
              (++-identityʳ ys) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (ρ⇒-coh-list ys) ⟩
  id ⊗₁ (ρ⇒ ∘ inner-from)
    ≈⟨ ρ-slide ⟩
  ρ⇒ ∘ α⇐ ∘ id ⊗₁ inner-from ∎
  where
    inner-from = _≅_.from (unflatten-++-≅ ys [])

    ρ-slide : id {Var y} ⊗₁ (ρ⇒ ∘ inner-from) ≈Term ρ⇒ ∘ α⇐ ∘ id ⊗₁ inner-from
    ρ-slide = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ Var y, 1 ↦ unflatten ys, 2 ↦ unflatten (ys ++ [])
        open FinSetup FMC
          ( Var y Vec.∷ unflatten ys Vec.∷ unflatten (ys ++ []) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F
        open Sig {1} (λ { 0F → v2 , v1 ⊗ᵒ unitᵒ })
        open WithGen (λ { (genS 0F) → inner-from })
        g0 = gen 0F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v2) (v0 ⊗ᵒ v1)
        lhsᵗ = S._⊗₁_ S.id (S._∘_ S.ρ⇒ g0)
        rhsᵗ = S._∘_ S.ρ⇒ (S._∘_ S.α⇐ (S._⊗₁_ S.id g0))

--------------------------------------------------------------------------------
-- List-coherence for ρ⇐.

ρ⇐-coh-list
  : ∀ (xs : List X)
  → subst (λ z → HomTerm (unflatten z) (unflatten (xs ++ [])))
          (++-identityʳ xs) id
    ≈Term _≅_.to (unflatten-++-≅ xs []) ∘ ρ⇐ {unflatten xs}
ρ⇐-coh-list []       = begin
  id           ≈⟨ ≈-Term-sym ρ⇒∘ρ⇐≈id ⟩
  ρ⇒ ∘ ρ⇐      ≈⟨ ≈-Term-sym coherence₃ ⟩∘⟨refl ⟩
  λ⇒ ∘ ρ⇐      ∎
ρ⇐-coh-list (y ∷ ys) = begin
  subst (λ z → HomTerm (unflatten z) (Var y ⊗₀ unflatten (ys ++ [])))
        (cong (y ∷_) (++-identityʳ ys)) id
    ≈⟨ cons-coh-step y (++-identityʳ ys)
         (λ z → unflatten z) (λ _ → Var y ⊗₀ unflatten (ys ++ [])) id ⟩
  subst (λ z → HomTerm (Var y ⊗₀ unflatten z)
                        (Var y ⊗₀ unflatten (ys ++ [])))
        (++-identityʳ ys) id
    ≈⟨ subst-dom-cons y (++-identityʳ ys) ⟩
  id ⊗₁ subst (λ z → HomTerm (unflatten z) (unflatten (ys ++ [])))
              (++-identityʳ ys) id
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (ρ⇐-coh-list ys) ⟩
  id ⊗₁ (inner-to ∘ ρ⇐)
    ≈⟨ ρ-slide ⟩
  (id ⊗₁ inner-to ∘ α⇒) ∘ ρ⇐ ∎
  where
    inner-to = _≅_.to (unflatten-++-≅ ys [])

    ρ-slide : id {Var y} ⊗₁ (inner-to ∘ ρ⇐) ≈Term (id ⊗₁ inner-to ∘ α⇒) ∘ ρ⇐
    ρ-slide = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ Var y, 1 ↦ unflatten ys, 2 ↦ unflatten (ys ++ [])
        open FinSetup FMC
          ( Var y Vec.∷ unflatten ys Vec.∷ unflatten (ys ++ []) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F
        open Sig {1} (λ { 0F → v1 ⊗ᵒ unitᵒ , v2 })
        open WithGen (λ { (genS 0F) → inner-to })
        g0 = gen 0F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v1) (v0 ⊗ᵒ v2)
        lhsᵗ = S._⊗₁_ S.id (S._∘_ g0 S.ρ⇐)
        rhsᵗ = S._∘_ (S._∘_ (S._⊗₁_ S.id g0) S.α⇒) S.ρ⇐

--------------------------------------------------------------------------------
-- ρ⇒-coherence / ρ⇐-coherence: combine list-coherence with bridge-form.

ρ⇒-coherence
  : ∀ A → subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
       ≈Term bridge (ρ⇒ {A})
ρ⇒-coherence A = begin
  subst₂ HomTerm refl (cong unflatten (++-identityʳ (flatten A))) id
    ≈⟨ ≡⇒≈Term (subst₂-refl-cod (++-identityʳ (flatten A))) ⟩
  subst (λ z → HomTerm (unflatten (flatten A ++ [])) (unflatten z))
        (++-identityʳ (flatten A)) id
    ≈⟨ ρ⇒-coh-list (flatten A) ⟩
  ρ⇒ ∘ _≅_.from (unflatten-++-≅ (flatten A) [])
    ≈⟨ ≈-Term-sym (bridge-ρ⇒-form A) ⟩
  bridge (ρ⇒ {A}) ∎

ρ⇐-coherence
  : ∀ A → subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
       ≈Term bridge (ρ⇐ {A})
ρ⇐-coherence A = begin
  subst₂ HomTerm (cong unflatten (++-identityʳ (flatten A))) refl id
    ≈⟨ ≡⇒≈Term (subst₂-refl-dom (++-identityʳ (flatten A))) ⟩
  subst (λ z → HomTerm (unflatten z) (unflatten (flatten A ++ [])))
        (++-identityʳ (flatten A)) id
    ≈⟨ ρ⇐-coh-list (flatten A) ⟩
  _≅_.to (unflatten-++-≅ (flatten A) []) ∘ ρ⇐
    ≈⟨ ≈-Term-sym (bridge-ρ⇐-form A) ⟩
  bridge (ρ⇐ {A}) ∎

--------------------------------------------------------------------------------
-- α-form lists and their list-induction lemmas.

α⇒-form-list
  : (xs ys zs : List X)
  → HomTerm (unflatten ((xs ++ ys) ++ zs)) (unflatten (xs ++ ys ++ zs))
α⇒-form-list []       ys zs = id
α⇒-form-list (x ∷ xs) ys zs = id {Var x} ⊗₁ α⇒-form-list xs ys zs

α⇐-form-list
  : (xs ys zs : List X)
  → HomTerm (unflatten (xs ++ ys ++ zs)) (unflatten ((xs ++ ys) ++ zs))
α⇐-form-list []       ys zs = id
α⇐-form-list (x ∷ xs) ys zs = id {Var x} ⊗₁ α⇐-form-list xs ys zs

--------------------------------------------------------------------------------
-- α⇒-form / α⇐-form mutual inverses.

-- The composite of `id {Var w} ⊗₁ F` with `id {Var w} ⊗₁ G` collapses to
-- `id {Var w} ⊗₁ (F ∘ G)` — the cons summand shared by both α-form isos.
⊗-cons-step
  : ∀ {w} {A B : ObjTerm} (F : HomTerm A B) (G : HomTerm B A)
  → (id {Var w} ⊗₁ F) ∘ (id {Var w} ⊗₁ G) ≈Term id {Var w} ⊗₁ (F ∘ G)
⊗-cons-step F G = begin
  (id ⊗₁ F) ∘ (id ⊗₁ G)
    ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
  (id ∘ id) ⊗₁ (F ∘ G)
    ≈⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
  id ⊗₁ (F ∘ G) ∎

-- Both α-form isos are the same `id {Var x} ⊗₁`-distributing induction with the
-- two `*-form-list`s composed in opposite order; their cons cases share exactly
-- the `⊗-cons-step` collapse above.  (The composites are endo at different
-- objects — `unflatten ((xs ++ ys) ++ zs)` vs `unflatten (xs ++ ys ++ zs)` — so
-- a single dependently-typed helper would have to transport across that; we
-- instead keep the two short inductions and share their one nontrivial step.)
α⇒-α⇐-iso
  : ∀ (xs ys zs : List X)
  → α⇒-form-list xs ys zs ∘ α⇐-form-list xs ys zs ≈Term id
α⇒-α⇐-iso []       ys zs = idˡ
α⇒-α⇐-iso (x ∷ xs) ys zs = begin
  (id {Var x} ⊗₁ α⇒-form-list xs ys zs) ∘ (id {Var x} ⊗₁ α⇐-form-list xs ys zs)
    ≈⟨ ⊗-cons-step (α⇒-form-list xs ys zs) (α⇐-form-list xs ys zs) ⟩
  id ⊗₁ (α⇒-form-list xs ys zs ∘ α⇐-form-list xs ys zs)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇒-α⇐-iso xs ys zs) ⟩
  id ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎

α⇐-α⇒-iso
  : ∀ (xs ys zs : List X)
  → α⇐-form-list xs ys zs ∘ α⇒-form-list xs ys zs ≈Term id
α⇐-α⇒-iso []       ys zs = idˡ
α⇐-α⇒-iso (x ∷ xs) ys zs = begin
  (id {Var x} ⊗₁ α⇐-form-list xs ys zs) ∘ (id {Var x} ⊗₁ α⇒-form-list xs ys zs)
    ≈⟨ ⊗-cons-step (α⇐-form-list xs ys zs) (α⇒-form-list xs ys zs) ⟩
  id ⊗₁ (α⇐-form-list xs ys zs ∘ α⇒-form-list xs ys zs)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (α⇐-α⇒-iso xs ys zs) ⟩
  id ⊗₁ id
    ≈⟨ id⊗id≈id ⟩
  id ∎

--------------------------------------------------------------------------------
-- Mac Lane / solver helpers.

pentagon-rewrite
  : ∀ {X Y Z W}
  → α⇒ {X ⊗₀ Y} {Z} {W}
  ≈Term α⇐ {X} {Y} {Z ⊗₀ W}
        ∘ id {X} ⊗₁ α⇒ {Y} {Z} {W}
        ∘ α⇒ {X} {Y ⊗₀ Z} {W}
        ∘ α⇒ {X} {Y} {Z} ⊗₁ id {W}
pentagon-rewrite {X} {Y} {Z} {W} = solveMor! lhsᵗ rhsᵗ
  where
    open FinSetup FMC ( X Vec.∷ Y Vec.∷ Z Vec.∷ W Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F
    open Sig {0} (λ ())
    open WithGen (λ { (genS ()) })
    lhsᵗ rhsᵗ : S.HomTerm (((v0 ⊗ᵒ v1) ⊗ᵒ v2) ⊗ᵒ v3) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
    lhsᵗ = S.α⇒
    rhsᵗ = S._∘_ S.α⇐ (S._∘_ (S._⊗₁_ S.id S.α⇒) (S._∘_ S.α⇒ (S._⊗₁_ S.α⇒ S.id)))

--------------------------------------------------------------------------------
-- Shared iso-collapse for the two bridge-α⇒ base cases below: after the
-- solver shuffles all opaque generators adjacent, the paired
-- `unflatten-flatten-≈` / `unflatten-++-≅` legs cancel by the iso laws
-- (which lie OUTSIDE the free-monoidal fragment `solveMor!` decides).

private
  collapse-c-FT
    : ∀ B C
    → _≅_.to (unflatten-++-≅ (flatten B) (flatten C))
      ∘ (( _≅_.from (unflatten-flatten-≈ B) ∘ _≅_.to (unflatten-flatten-≈ B))
          ⊗₁ (_≅_.from (unflatten-flatten-≈ C) ∘ _≅_.to (unflatten-flatten-≈ C)))
      ∘ _≅_.from (unflatten-++-≅ (flatten B) (flatten C))
    ≈Term id
  collapse-c-FT B C = begin
    cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (_≅_.isoʳ (unflatten-flatten-≈ B))
                           (_≅_.isoʳ (unflatten-flatten-≈ C)) ⟩∘⟨refl ⟩
    cBC-to ∘ (id ⊗₁ id) ∘ cBC-from
      ≈⟨ refl⟩∘⟨ id⊗id≈id ⟩∘⟨refl ⟩
    cBC-to ∘ id ∘ cBC-from
      ≈⟨ refl⟩∘⟨ idˡ ⟩
    cBC-to ∘ cBC-from
      ≈⟨ _≅_.isoˡ (unflatten-++-≅ (flatten B) (flatten C)) ⟩
    id ∎
    where
      F-B = _≅_.from (unflatten-flatten-≈ B)
      F-C = _≅_.from (unflatten-flatten-≈ C)
      T-B = _≅_.to   (unflatten-flatten-≈ B)
      T-C = _≅_.to   (unflatten-flatten-≈ C)
      cBC-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten C))
      cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

--------------------------------------------------------------------------------
-- Var-base case of bridge-α⇒-form.

bridge-α⇒-form-Var
  : ∀ x B C → bridge (α⇒ {Var x} {B} {C})
            ≈Term α⇒-form-list (x ∷ []) (flatten B) (flatten C)
bridge-α⇒-form-Var x B C = begin
  bridge (α⇒ {Var x} {B} {C})
    ≈⟨ shuffle ⟩
  id {Var x} ⊗₁ (cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from)
    ≈⟨ ⊗-resp-≈ ≈-Term-refl (collapse-c-FT B C) ⟩
  id ⊗₁ id ∎
  where
    F-B = _≅_.from (unflatten-flatten-≈ B)
    F-C = _≅_.from (unflatten-flatten-≈ C)
    T-B = _≅_.to   (unflatten-flatten-≈ B)
    T-C = _≅_.to   (unflatten-flatten-≈ C)
    cBC-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten C))
    cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

    -- the free part of the chase: all coherence/naturality/interchange,
    -- bringing each `from`/`to` leg adjacent to its partner.
    shuffle
      : bridge (α⇒ {Var x} {B} {C})
      ≈Term id {Var x} ⊗₁ (cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from)
    shuffle = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ Var x, 1 ↦ B, 2 ↦ C, 3 ↦ uf B, 4 ↦ uf C,
        -- 5 ↦ unflatten (fB++fC)
        open FinSetup FMC
          ( Var x Vec.∷ B Vec.∷ C
              Vec.∷ unflatten (flatten B) Vec.∷ unflatten (flatten C)
              Vec.∷ unflatten (flatten B ++ flatten C) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
        v5 = V 5F
        -- generators: F-B, F-C, T-B, T-C, cBC-to, cBC-from
        open Sig {6} (λ { 0F → v1 , v3
                        ; 1F → v2 , v4
                        ; 2F → v3 , v1
                        ; 3F → v4 , v2
                        ; 4F → v3 ⊗ᵒ v4 , v5
                        ; 5F → v5 , v3 ⊗ᵒ v4 })
        open WithGen (λ { (genS 0F) → F-B ; (genS 1F) → F-C
                        ; (genS 2F) → T-B ; (genS 3F) → T-C
                        ; (genS 4F) → cBC-to ; (genS 5F) → cBC-from })
        gFB = gen 0F ; gFC = gen 1F ; gTB = gen 2F ; gTC = gen 3F
        gcto = gen 4F ; gcfrom = gen 5F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v5) (v0 ⊗ᵒ v5)
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

--------------------------------------------------------------------------------
-- Unit-base case of bridge-α⇒-form.

bridge-α⇒-form-unit
  : ∀ B C → bridge (α⇒ {unit} {B} {C})
          ≈Term α⇒-form-list [] (flatten B) (flatten C)
bridge-α⇒-form-unit B C = begin
  bridge (α⇒ {unit} {B} {C})
    ≈⟨ shuffle ⟩
  cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from
    ≈⟨ collapse-c-FT B C ⟩
  id ∎
  where
    F-B = _≅_.from (unflatten-flatten-≈ B)
    F-C = _≅_.from (unflatten-flatten-≈ C)
    T-B = _≅_.to   (unflatten-flatten-≈ B)
    T-C = _≅_.to   (unflatten-flatten-≈ C)
    cBC-to   = _≅_.to   (unflatten-++-≅ (flatten B) (flatten C))
    cBC-from = _≅_.from (unflatten-++-≅ (flatten B) (flatten C))

    -- the free part of the chase: all coherence/naturality/interchange,
    -- bringing each `from`/`to` leg adjacent to its partner.
    shuffle
      : bridge (α⇒ {unit} {B} {C})
      ≈Term cBC-to ∘ ((F-B ∘ T-B) ⊗₁ (F-C ∘ T-C)) ∘ cBC-from
    shuffle = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ B, 1 ↦ C, 2 ↦ uf B, 3 ↦ uf C, 4 ↦ unflatten (fB++fC)
        open FinSetup FMC
          ( B Vec.∷ C
              Vec.∷ unflatten (flatten B) Vec.∷ unflatten (flatten C)
              Vec.∷ unflatten (flatten B ++ flatten C) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
        -- generators: F-B, F-C, T-B, T-C, cBC-to, cBC-from
        open Sig {6} (λ { 0F → v0 , v2
                        ; 1F → v1 , v3
                        ; 2F → v2 , v0
                        ; 3F → v3 , v1
                        ; 4F → v2 ⊗ᵒ v3 , v4
                        ; 5F → v4 , v2 ⊗ᵒ v3 })
        open WithGen (λ { (genS 0F) → F-B ; (genS 1F) → F-C
                        ; (genS 2F) → T-B ; (genS 3F) → T-C
                        ; (genS 4F) → cBC-to ; (genS 5F) → cBC-from })
        gFB = gen 0F ; gFC = gen 1F ; gTB = gen 2F ; gTC = gen 3F
        gcto = gen 4F ; gcfrom = gen 5F
        lhsᵗ rhsᵗ : S.HomTerm v4 v4
        lhsᵗ = S._∘_
                 (S._∘_ S.λ⇒
                        (S._⊗₁_ S.id (S._∘_ gcto (S._⊗₁_ gFB gFC))))
                 (S._∘_ S.α⇒
                   (S._∘_
                     (S._⊗₁_ (S._∘_ (S._⊗₁_ S.id gTB) S.λ⇐) gTC)
                     gcfrom))
        rhsᵗ = S._∘_ gcto (S._∘_ (S._⊗₁_ (S._∘_ gFB gTB) (S._∘_ gFC gTC)) gcfrom)
