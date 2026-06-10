{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Constructive discharge of `c-iso-assoc-from-cons` from
-- `Soundness/DecodeRoundtrip.agda`.
--
-- The cons case of the c-iso pentagon (associativity of `unflatten-++-≅`
-- up to `++-assoc`); unblocks the α⇒/α⇐ cases of `decode-rel-≈-decode`.
--
-- `c-iso-assoc-from` is re-defined here constructively (rather than
-- importing the non-`--safe` `DecodeRoundtrip` postulate).  The base case
-- and the two free-monoidal segments of the cons case (everything except
-- the IH application and the final subst-folding) are discharged by the
-- morphism-variable solver `solveMor!` at the free monoidal category.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.CIsoAssocFromCons
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Unflatten sig
  using (unflatten; unflatten-++-≅)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Morphism FreeMonoidal using (_≅_)
-- Morphism-variable monoidal solver (cf. `BridgeAlphaFormCompound.agda`).
open import Categories.SolverFrontend using (module FinSetup)
open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F)
import Data.Vec as Vec
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; subst)
open import Relation.Binary.PropositionalEquality.Properties using (subst-∘)

private
  module FM = Category FreeMonoidal

  -- the free monoidal category itself, as the solver's target bundle.
  FMC : MonoidalCategory _ _ _
  FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Local helper (re-proved here to avoid depending on non-`--safe`
-- DecodeRoundtrip.agda).

-- Relates `id ⊗ subst-id-along-e` to the subst-id at the (Var x)-tensored
-- predicate (by J on `e`).
id-⊗-subst-bridge
  : ∀ {x : X} {xs₁ ys'} (e : xs₁ ≡ ys')
  → (id {Var x} ⊗₁ subst (λ z → HomTerm (unflatten xs₁) (unflatten z)) e id)
  ≈Term subst (λ z → HomTerm (Var x ⊗₀ unflatten xs₁) (Var x ⊗₀ unflatten z)) e id
id-⊗-subst-bridge refl = id⊗id≈id

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
c-iso-assoc-from [] xs₂ ys = solveMor! lhsᵗ rhsᵗ
  where
    -- atoms: 0 ↦ unflatten xs₂, 1 ↦ unflatten ys, 2 ↦ unflatten (xs₂ ++ ys)
    open FinSetup FMC
      ( unflatten xs₂ Vec.∷ unflatten ys Vec.∷ unflatten (xs₂ ++ ys) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F
    -- generator: c-3 = from (unflatten-++-≅ xs₂ ys)
    open Sig {1} (λ { 0F → v2 , v0 ⊗ᵒ v1 })
    open WithGen (λ { (genS 0F) → _≅_.from (unflatten-++-≅ xs₂ ys) })
    g0 = gen 0F
    lhsᵗ rhsᵗ : S.HomTerm v2 (unitᵒ ⊗ᵒ (v0 ⊗ᵒ v1))
    lhsᵗ = S._∘_ S.α⇒ (S._∘_ (S._⊗₁_ S.λ⇐ S.id) g0)
    rhsᵗ = S._∘_ (S._⊗₁_ S.id g0) (S._∘_ S.λ⇐ S.id)

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
    e'    = ++-assoc (x ∷ xs₁') xs₂ ys  -- = cong (x ∷_) e definitionally.

    subst-id-xs₁' = subst (λ z → HomTerm (unflatten ((xs₁' ++ xs₂) ++ ys))
                                          (unflatten z)) e id

    ih : α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2
       ≈Term (id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁'
    ih = c-iso-assoc-from xs₁' xs₂ ys

    -- The free pre-IH shuffle (old steps 1-5: pentagon-rewrite, ⊗-∘-dist,
    -- α-comm, α-iso cancellations, id-⊗ collection), as one solver call.
    shuffle₁
      : α⇒ {Vx ⊗₀ U₁'} {U₂} {U-ys}
          ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
          ∘ (α⇐ ∘ id ⊗₁ c-2)
      ≈Term α⇐ ∘ id ⊗₁ (α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2)
    shuffle₁ = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ Var x, 1 ↦ U₁', 2 ↦ U₂, 3 ↦ U-ys, 4 ↦ U-12,
        -- 5 ↦ unflatten ((xs₁' ++ xs₂) ++ ys)
        open FinSetup FMC
          ( Vx Vec.∷ U₁' Vec.∷ U₂ Vec.∷ U-ys Vec.∷ U-12
              Vec.∷ unflatten ((xs₁' ++ xs₂) ++ ys) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
        v5 = V 5F
        -- generators: c-1, c-2
        open Sig {2} (λ { 0F → v4 , v1 ⊗ᵒ v2
                        ; 1F → v5 , v4 ⊗ᵒ v3 })
        open WithGen (λ { (genS 0F) → c-1 ; (genS 1F) → c-2 })
        g1 = gen 0F ; g2 = gen 1F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v5) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
        lhsᵗ = S._∘_ S.α⇒
                 (S._∘_ (S._⊗₁_ (S._∘_ S.α⇐ (S._⊗₁_ S.id g1)) S.id)
                        (S._∘_ S.α⇐ (S._⊗₁_ S.id g2)))
        rhsᵗ = S._∘_ S.α⇐
                 (S._⊗₁_ S.id (S._∘_ S.α⇒ (S._∘_ (S._⊗₁_ g1 S.id) g2)))

    -- The free post-IH shuffle (old steps 7-10: id-⊗ distribution,
    -- α⇐-comm-top, regrouping), as one solver call.
    shuffle₂
      : α⇐ ∘ id ⊗₁ ((id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁')
      ≈Term id ⊗₁ c-3
            ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
            ∘ (id ⊗₁ subst-id-xs₁')
    shuffle₂ = solveMor! lhsᵗ rhsᵗ
      where
        -- atoms: 0 ↦ Var x, 1 ↦ U₁', 2 ↦ U₂, 3 ↦ U-ys, 4 ↦ U-23,
        -- 5 ↦ unflatten ((xs₁' ++ xs₂) ++ ys), 6 ↦ unflatten (xs₁' ++ xs₂ ++ ys)
        open FinSetup FMC
          ( Vx Vec.∷ U₁' Vec.∷ U₂ Vec.∷ U-ys Vec.∷ U-23
              Vec.∷ unflatten ((xs₁' ++ xs₂) ++ ys)
              Vec.∷ unflatten (xs₁' ++ xs₂ ++ ys) Vec.∷ Vec.[] )
        v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
        v5 = V 5F ; v6 = V 6F
        -- generators: c-3, c-4, subst-id-xs₁'
        open Sig {3} (λ { 0F → v4 , v2 ⊗ᵒ v3
                        ; 1F → v6 , v1 ⊗ᵒ v4
                        ; 2F → v5 , v6 })
        open WithGen (λ { (genS 0F) → c-3 ; (genS 1F) → c-4
                        ; (genS 2F) → subst-id-xs₁' })
        g3 = gen 0F ; g4 = gen 1F ; gs = gen 2F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v5) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
        lhsᵗ = S._∘_ S.α⇐
                 (S._⊗₁_ S.id (S._∘_ (S._⊗₁_ S.id g3) (S._∘_ g4 gs)))
        rhsᵗ = S._∘_ (S._⊗₁_ S.id g3)
                 (S._∘_ (S._∘_ S.α⇐ (S._⊗₁_ S.id g4)) (S._⊗₁_ S.id gs))

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
      -- Step 1 (solver): the free pre-IH shuffle — pentagon, α-naturality,
      -- interchange, and the structural-iso cancellations.
      α⇒ {Vx ⊗₀ U₁'} {U₂} {U-ys}
        ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
        ∘ (α⇐ ∘ id ⊗₁ c-2)
          ≈⟨ shuffle₁ ⟩
      α⇐
        ∘ id ⊗₁ (α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2)
        -- Step 2: apply IH inside id ⊗ _.
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl ih ⟩
      α⇐
        ∘ id ⊗₁ ((id ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁')
        -- Step 3 (solver): the free post-IH shuffle — α⇐-naturality +
        -- interchange, regrouping around the subst-id factor.
          ≈⟨ shuffle₂ ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ (id ⊗₁ subst-id-xs₁')
        -- Step 4: convert (id ⊗ subst-id-xs₁') to subst-id-(x∷xs₁') via
        --   id-⊗-subst-bridge then `subst-∘` (folding the `(x ∷_)`).
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
-- signature in `DecodeRoundtrip.agda`.

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
