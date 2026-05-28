{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Constructive discharge of `c-iso-assoc-from-cons` from
-- `Completeness/DecodeRoundtrip.agda`.
--
-- This is the cons case of the c-iso pentagon (associativity of
-- `unflatten-++-≅` up to `++-assoc`).  Unblocks the α⇒/α⇐ cases of
-- axiom F (`decode-rel-≈-decode`).
--
-- Strategy (matching the comments in DecodeRoundtrip.agda:1166-1181):
--   1. `pentagon-rewrite` to expand `α⇒_{Vx ⊗ U₁', U₂, U-ys}`.
--   2. `⊗-∘-dist` + `α⇒∘α⇐≈id` + `idˡ` to cancel an inner pair.
--   3. `α-comm` to push α⇒ past `((id ⊗ c-1) ⊗ id)`.
--   4. `α⇒∘α⇐≈id` + `idˡ` to cancel another pair.
--   5. `id-⊗-respects-∘` (×2) to combine three `id ⊗ _` factors.
--   6. IH: `c-iso-assoc-from xs₁' xs₂ ys`.
--   7. `id-⊗-respects-∘` (×2) to break the `id ⊗ _` of the IH RHS apart.
--   8. `α⇐-comm-top` to push α⇐ past `id ⊗ (id ⊗ c-3)`.
--   9. `id⊗id≈id` to simplify `(id ⊗ id) ⊗ c-3`.
--  10. Definitional reduction: `α⇐ ∘ (id ⊗ c-4) = c-from (x∷xs₁') (xs₂++ys)`.
--  11. `id-⊗-subst-bridge` + `≡⇒≈Term (subst-∘ ...)` to convert the
--      `id ⊗ subst-id-xs₁'` to `subst-id-(x∷xs₁')`.
--
-- Per the task description, we cannot import the postulated
-- `c-iso-assoc-from-cons` from `DecodeRoundtrip.agda` (which is not
-- --safe).  Instead, we re-define `c-iso-assoc-from` here constructively
-- (mutual recursion with the cons-case body), importing only the
-- Mac-Lane fragment helpers from `CoherenceSolver` (`pentagon-rewrite`,
-- `α⇒-λ⇐-collapse`) and re-proving the small categorical helpers
-- (`λ⇐-naturality`, `α⇐-comm-top`, `id-⊗-respects-∘`,
-- `id-⊗-subst-bridge`) inline.
--
-- File is `--safe --with-K`-clean.  (The `--with-K` flag is needed
-- because `CoherenceSolver.agda` requires K transitively.)
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.CIsoAssocFromCons
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Completeness.Unflatten sig
  using (unflatten; unflatten-++-≅)
open import Categories.APROP.Hypergraph.Completeness.CoherenceSolver sig
  using (module 2-objs; module 4-objs)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-∘)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Local helpers (re-proved here to avoid depending on non-`--safe`
-- DecodeRoundtrip.agda).

-- `f ≡ g → f ≈Term g`.
≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

-- `pentagon-rewrite` from CoherenceSolver — solves the pentagon for
-- `α⇒_{X⊗Y, Z, W}`.
pentagon-rewrite
  : ∀ {X Y Z W}
  → α⇒ {X ⊗₀ Y} {Z} {W}
  ≈Term α⇐ {X} {Y} {Z ⊗₀ W}
        ∘ id {X} ⊗₁ α⇒ {Y} {Z} {W}
        ∘ α⇒ {X} {Y ⊗₀ Z} {W}
        ∘ α⇒ {X} {Y} {Z} ⊗₁ id {W}
pentagon-rewrite {X} {Y} {Z} {W} = lemma
  where
    open 4-objs X Y Z W renaming (pentagon-rewrite to lemma)

-- `α⇒-λ⇐-collapse` from CoherenceSolver.
α⇒-λ⇐-collapse
  : ∀ {X Y} → α⇒ {unit} {X} {Y} ∘ (λ⇐ {X} ⊗₁ id {Y}) ≈Term λ⇐ {X ⊗₀ Y}
α⇒-λ⇐-collapse {X} {Y} = lemma
  where
    open 2-objs X Y renaming (α⇒-λ⇐-collapse to lemma)

-- λ⇐-naturality (derived from λ⇒-naturality + iso laws).
λ⇐-naturality
  : ∀ {A B} (f : HomTerm A B) → λ⇐ {B} ∘ f ≈Term id ⊗₁ f ∘ λ⇐ {A}
λ⇐-naturality f = begin
  λ⇐ ∘ f
    ≈⟨ ≈-Term-sym idʳ ⟩
  (λ⇐ ∘ f) ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym λ⇒∘λ⇐≈id ⟩
  (λ⇐ ∘ f) ∘ λ⇒ ∘ λ⇐
    ≈⟨ FM.sym-assoc ⟩
  ((λ⇐ ∘ f) ∘ λ⇒) ∘ λ⇐
    ≈⟨ FM.assoc ⟩∘⟨refl ⟩
  (λ⇐ ∘ f ∘ λ⇒) ∘ λ⇐
    ≈⟨ (refl⟩∘⟨ ≈-Term-sym λ⇒∘id⊗f≈f∘λ⇒) ⟩∘⟨refl ⟩
  (λ⇐ ∘ λ⇒ ∘ id ⊗₁ f) ∘ λ⇐
    ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  ((λ⇐ ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐
    ≈⟨ (λ⇐∘λ⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (id ∘ id ⊗₁ f) ∘ λ⇐
    ≈⟨ idˡ ⟩∘⟨refl ⟩
  id ⊗₁ f ∘ λ⇐ ∎

-- id-⊗-respects-∘: `id ⊗ (g ∘ f) ≈ (id ⊗ g) ∘ (id ⊗ f)`.
id-⊗-respects-∘
  : ∀ {X A B C} (f : HomTerm A B) (g : HomTerm B C)
  → id {X} ⊗₁ (g ∘ f) ≈Term (id {X} ⊗₁ g) ∘ (id {X} ⊗₁ f)
id-⊗-respects-∘ f g = begin
  id ⊗₁ (g ∘ f)
    ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
  (id ∘ id) ⊗₁ (g ∘ f)
    ≈⟨ ⊗-∘-dist ⟩
  id ⊗₁ g ∘ id ⊗₁ f ∎

-- id-⊗-subst-bridge: relates `id ⊗ subst-id-along-e` to the subst-id
-- at the (Var x)-tensored predicate.  Provable by J on `e` (refl case
-- is `id⊗id≈id`).
id-⊗-subst-bridge
  : ∀ {x : X} {xs₁ ys'} (e : xs₁ ≡ ys')
  → (id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten xs₁) (unflatten z)) e id)
  ≈Term subst (λ z → HomTerm (Var x ⊗₀ unflatten xs₁) (Var x ⊗₀ unflatten z)) e id
id-⊗-subst-bridge refl = id⊗id≈id

-- α⇐-comm: α⇐'s naturality, derived from α-comm + α-iso laws.
α⇐-comm-top
  : ∀ {X Y Z X' Y' Z' : ObjTerm}
    (f : HomTerm X X') (g : HomTerm Y Y') (h : HomTerm Z Z')
  → α⇐ {X'} {Y'} {Z'} ∘ f ⊗₁ (g ⊗₁ h)
  ≈Term (f ⊗₁ g) ⊗₁ h ∘ α⇐ {X} {Y} {Z}
α⇐-comm-top f g h = begin
  α⇐ ∘ f ⊗₁ (g ⊗₁ h)
    ≈⟨ ≈-Term-sym idʳ ⟩
  (α⇐ ∘ f ⊗₁ (g ⊗₁ h)) ∘ id
    ≈⟨ refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩
  (α⇐ ∘ f ⊗₁ (g ⊗₁ h)) ∘ (α⇒ ∘ α⇐)
    ≈⟨ FM.assoc ⟩
  α⇐ ∘ f ⊗₁ (g ⊗₁ h) ∘ α⇒ ∘ α⇐
    ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
  α⇐ ∘ (f ⊗₁ (g ⊗₁ h) ∘ α⇒) ∘ α⇐
    ≈⟨ refl⟩∘⟨ ≈-Term-sym α-comm ⟩∘⟨refl ⟩
  α⇐ ∘ (α⇒ ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ FM.sym-assoc ⟩
  (α⇐ ∘ α⇒ ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ FM.sym-assoc ⟩∘⟨refl ⟩
  ((α⇐ ∘ α⇒) ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ (α⇐∘α⇒≈id ⟩∘⟨refl) ⟩∘⟨refl ⟩
  (id ∘ (f ⊗₁ g) ⊗₁ h) ∘ α⇐
    ≈⟨ idˡ ⟩∘⟨refl ⟩
  (f ⊗₁ g) ⊗₁ h ∘ α⇐ ∎

--------------------------------------------------------------------------------
-- The c-iso pentagon, by list induction on xs₁.

c-iso-assoc-from
  : ∀ xs₁ xs₂ ys
  → α⇒ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
    ∘ (_≅_.from (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
    ∘ _≅_.from (unflatten-++-≅ (xs₁ ++ xs₂) ys)
  ≈Term (id {unflatten xs₁} ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys))
        ∘ _≅_.from (unflatten-++-≅ xs₁ (xs₂ ++ ys))
        ∘ subst (λ z → HomTerm (unflatten ((xs₁ ++ xs₂) ++ ys)) (unflatten z))
                (++-assoc xs₁ xs₂ ys) id

-- Base case: xs₁ = [].
c-iso-assoc-from [] xs₂ ys = begin
  α⇒ ∘ (λ⇐ ⊗₁ id) ∘ _≅_.from (unflatten-++-≅ xs₂ ys)
    ≈⟨ FM.sym-assoc ⟩
  (α⇒ ∘ (λ⇐ ⊗₁ id)) ∘ _≅_.from (unflatten-++-≅ xs₂ ys)
    ≈⟨ α⇒-λ⇐-collapse ⟩∘⟨refl ⟩
  λ⇐ ∘ _≅_.from (unflatten-++-≅ xs₂ ys)
    ≈⟨ λ⇐-naturality (_≅_.from (unflatten-++-≅ xs₂ ys)) ⟩
  id ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys) ∘ λ⇐
    ≈⟨ refl⟩∘⟨ ≈-Term-sym idʳ ⟩
  (id ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys)) ∘ λ⇐ ∘ id ∎

-- Cons case: xs₁ = x ∷ xs₁'.
c-iso-assoc-from (x ∷ xs₁') xs₂ ys = body
  where
    U₁'   = unflatten xs₁'
    U₂    = unflatten xs₂
    U-ys  = unflatten ys
    U-12  = unflatten (xs₁' ++ xs₂)
    U-23  = unflatten (xs₂ ++ ys)
    Vx    = Var x

    c-1   = _≅_.from (unflatten-++-≅ xs₁' xs₂)
    c-2   = _≅_.from (unflatten-++-≅ (xs₁' ++ xs₂) ys)
    c-3   = _≅_.from (unflatten-++-≅ xs₂ ys)
    c-4   = _≅_.from (unflatten-++-≅ xs₁' (xs₂ ++ ys))

    e     = ++-assoc xs₁' xs₂ ys
    e'    = ++-assoc (x ∷ xs₁') xs₂ ys
    -- e' = cong (x ∷_) e definitionally.

    subst-id-xs₁' = subst (λ z → HomTerm (unflatten ((xs₁' ++ xs₂) ++ ys))
                                          (unflatten z)) e id

    -- IH on the recursive call.
    ih : α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2
       ≈Term (id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁'
    ih = c-iso-assoc-from xs₁' xs₂ ys

    body :
      α⇒ {unflatten (x ∷ xs₁')} {unflatten xs₂} {unflatten ys}
        ∘ (_≅_.from (unflatten-++-≅ (x ∷ xs₁') xs₂) ⊗₁ id)
        ∘ _≅_.from (unflatten-++-≅ ((x ∷ xs₁') ++ xs₂) ys)
      ≈Term (id {unflatten (x ∷ xs₁')} ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys))
            ∘ _≅_.from (unflatten-++-≅ (x ∷ xs₁') (xs₂ ++ ys))
            ∘ subst (λ z → HomTerm (unflatten (((x ∷ xs₁') ++ xs₂) ++ ys))
                                    (unflatten z))
                    (++-assoc (x ∷ xs₁') xs₂ ys) id
    body = begin
      -- Step 1: expand outer α⇒ via pentagon-rewrite.
      α⇒ {Vx ⊗₀ U₁'} {U₂} {U-ys}
        ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
        ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ pentagon-rewrite ⟩∘⟨refl ⟩
      (α⇐ {Vx} {U₁'} {U₂ ⊗₀ U-ys}
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁'} {U₂} ⊗₁ id)
        ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
        ∘ (α⇐ ∘ id ⊗₁ c-2)
        -- Associate to expose `(α⇒ ⊗ id) ∘ ((α⇐ ∘ id⊗c-1) ⊗ id)`.
          ≈⟨ FM.assoc ⟩
      α⇐
        ∘ ((id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
            ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
            ∘ α⇒ {Vx} {U₁'} {U₂} ⊗₁ id)
           ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
           ∘ (α⇐ ∘ id ⊗₁ c-2))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ ((α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
            ∘ α⇒ {Vx} {U₁'} {U₂} ⊗₁ id)
           ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
           ∘ (α⇐ ∘ id ⊗₁ c-2))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ ((α⇒ {Vx} {U₁'} {U₂} ⊗₁ id)
           ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
           ∘ (α⇐ ∘ id ⊗₁ c-2))
        -- Step 2: combine (α⇒ ⊗ id) ∘ ((α⇐ ∘ id⊗c-1) ⊗ id) via ⊗-∘-dist.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ ((α⇒ {Vx} {U₁'} {U₂} ⊗₁ id)
           ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id))
           ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩∘⟨refl ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ ((α⇒ {Vx} {U₁'} {U₂} ∘ (α⇐ ∘ id ⊗₁ c-1)) ⊗₁ (id ∘ id))
           ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ FM.sym-assoc idˡ ⟩∘⟨refl ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ (((α⇒ {Vx} {U₁'} {U₂} ∘ α⇐) ∘ id ⊗₁ c-1) ⊗₁ id)
           ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ (α⇒∘α⇐≈id ⟩∘⟨refl) ≈-Term-refl ⟩∘⟨refl ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ ((id ∘ id ⊗₁ c-1) ⊗₁ id)
           ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩∘⟨refl ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
        ∘ ((id ⊗₁ c-1) ⊗₁ id)
           ∘ (α⇐ ∘ id ⊗₁ c-2)
        -- Step 3: α-comm on α⇒_{Vx,U₁'⊗U₂,U-ys} ∘ ((id⊗c-1) ⊗ id).
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ (α⇒ {Vx} {U₁' ⊗₀ U₂} {U-ys}
           ∘ ((id ⊗₁ c-1) ⊗₁ id))
           ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α-comm ⟩∘⟨refl ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ ((id ⊗₁ (c-1 ⊗₁ id))
           ∘ α⇒ {Vx} {U-12} {U-ys})
           ∘ (α⇐ ∘ id ⊗₁ c-2)
        -- Step 4: cancel α⇒_{Vx,U-12,U-ys} ∘ α⇐_{Vx,U-12,U-ys} = id.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ id ⊗₁ (c-1 ⊗₁ id)
           ∘ α⇒ {Vx} {U-12} {U-ys}
           ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ id ⊗₁ (c-1 ⊗₁ id)
           ∘ (α⇒ {Vx} {U-12} {U-ys} ∘ α⇐)
           ∘ id ⊗₁ c-2
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ id ⊗₁ (c-1 ⊗₁ id)
           ∘ id
           ∘ id ⊗₁ c-2
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ id ⊗₁ (c-1 ⊗₁ id)
           ∘ id ⊗₁ c-2
        -- Step 5: combine three `id ⊗ _` factors via id-⊗-respects-∘.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym (id-⊗-respects-∘ c-2 (c-1 ⊗₁ id)) ⟩
      α⇐
        ∘ id ⊗₁ α⇒ {U₁'} {U₂} {U-ys}
        ∘ id ⊗₁ ((c-1 ⊗₁ id) ∘ c-2)
          ≈⟨ refl⟩∘⟨ ≈-Term-sym (id-⊗-respects-∘ ((c-1 ⊗₁ id) ∘ c-2)
                                                   (α⇒ {U₁'} {U₂} {U-ys})) ⟩
      α⇐
        ∘ id ⊗₁ (α⇒ {U₁'} {U₂} {U-ys} ∘ ((c-1 ⊗₁ id) ∘ c-2))
        -- Step 6: apply IH inside id ⊗ _ (note: `α⇒ ∘ (f ⊗ g) ∘ h` already
        -- parses as `α⇒ ∘ ((f ⊗ g) ∘ h)` via right-associative `_∘_`).
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
      α⇐
        ∘ id ⊗₁ ((id ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁')
        -- Step 7: distribute `id ⊗ _` over composition.
          ≈⟨ refl⟩∘⟨ id-⊗-respects-∘ (c-4 ∘ subst-id-xs₁') (id ⊗₁ c-3) ⟩
      α⇐
        ∘ (id ⊗₁ (id ⊗₁ c-3))
        ∘ id ⊗₁ (c-4 ∘ subst-id-xs₁')
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ id-⊗-respects-∘ subst-id-xs₁' c-4 ⟩
      α⇐
        ∘ (id ⊗₁ (id ⊗₁ c-3))
        ∘ (id ⊗₁ c-4)
        ∘ (id ⊗₁ subst-id-xs₁')
        -- Step 8: push α⇐ past (id ⊗ (id ⊗ c-3)) via α⇐-comm-top.
          ≈⟨ FM.sym-assoc ⟩
      (α⇐ ∘ (id ⊗₁ (id ⊗₁ c-3)))
        ∘ (id ⊗₁ c-4)
        ∘ (id ⊗₁ subst-id-xs₁')
          ≈⟨ α⇐-comm-top id id c-3 ⟩∘⟨refl ⟩
      ((id ⊗₁ id) ⊗₁ c-3 ∘ α⇐ {Vx} {U₁'} {U-23})
        ∘ (id ⊗₁ c-4)
        ∘ (id ⊗₁ subst-id-xs₁')
        -- Step 9: simplify (id ⊗ id) ⊗ c-3 to id ⊗ c-3.
          ≈⟨ (⊗-resp-≈ id⊗id≈id ≈-Term-refl ⟩∘⟨refl) ⟩∘⟨refl ⟩
      (id ⊗₁ c-3 ∘ α⇐ {Vx} {U₁'} {U-23})
        ∘ (id ⊗₁ c-4)
        ∘ (id ⊗₁ subst-id-xs₁')
        -- Step 10: re-associate so that `α⇐ ∘ id ⊗ c-4` is grouped (this
        --   is definitionally `_≅_.from (unflatten-++-≅ (x∷xs₁') (xs₂++ys))`).
          ≈⟨ FM.assoc ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23}
           ∘ (id ⊗₁ c-4)
           ∘ (id ⊗₁ subst-id-xs₁'))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ (id ⊗₁ subst-id-xs₁')
        -- Step 11: convert (id ⊗ subst-id-xs₁') to subst-id-(x∷xs₁').
        --   First id-⊗-subst-bridge to push the `id ⊗ subst` to a `subst`
        --   at the (Var x)-tensored predicate; then `subst-∘` to fold
        --   the `(x ∷_)` into the propositional equation.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ id-⊗-subst-bridge e ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ subst (λ z → HomTerm (Vx ⊗₀ unflatten ((xs₁' ++ xs₂) ++ ys))
                                (Vx ⊗₀ unflatten z)) e id
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨
             ≡⇒≈Term (subst-∘
                {P = λ z → HomTerm (Vx ⊗₀ unflatten ((xs₁' ++ xs₂) ++ ys))
                                   (unflatten z)}
                {f = x ∷_}
                e) ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ subst (λ z → HomTerm (Vx ⊗₀ unflatten ((xs₁' ++ xs₂) ++ ys))
                                (unflatten z)) e' id
        ∎

--------------------------------------------------------------------------------
-- The cons case, exposed as a top-level lemma matching the postulated
-- signature in `DecodeRoundtrip.agda:1189-1198`.

c-iso-assoc-from-cons
  : ∀ x xs₁' xs₂ ys
  → α⇒ {unflatten (x ∷ xs₁')} {unflatten xs₂} {unflatten ys}
    ∘ (_≅_.from (unflatten-++-≅ (x ∷ xs₁') xs₂) ⊗₁ id)
    ∘ _≅_.from (unflatten-++-≅ ((x ∷ xs₁') ++ xs₂) ys)
  ≈Term (id {unflatten (x ∷ xs₁')} ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys))
        ∘ _≅_.from (unflatten-++-≅ (x ∷ xs₁') (xs₂ ++ ys))
        ∘ subst (λ z → HomTerm (unflatten (((x ∷ xs₁') ++ xs₂) ++ ys))
                                (unflatten z))
                (++-assoc (x ∷ xs₁') xs₂ ys) id
c-iso-assoc-from-cons x xs₁' xs₂ ys = c-iso-assoc-from (x ∷ xs₁') xs₂ ys
