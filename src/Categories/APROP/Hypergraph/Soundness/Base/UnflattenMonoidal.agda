{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Monoidal-coherence data for `unflatten`, viewed as the strong monoidal
-- functor
--
--   (List X, _++_, [])  ⟶  (ObjTerm, _⊗₀_, unit)     over `FreeMonoidal`.
--
-- NOTE: no `Functor` / `MonoidalFunctor` record is actually built here, and
-- this module carries only the ASSOCIATIVITY half of the coherence such a
-- functor would need — the UNIT half (`T a [] ∘ ρ⇐`, `ρ⇒ ∘ F a []`) is
-- private to `Strict/Embed`, which is also the only consumer here.  The object
-- map is `unflatten : List X → ObjTerm` (the right-associated, `unit`-padded
-- fold from `Soundness/Base/Unflatten.agda`) and the structure iso (laxator)
-- is `unflatten-++-≅`.  It gathers the associativity coherence (both
-- directions):
--   * `c-iso-assoc-from` — the `from`-side pentagon, by list induction on the
--     first argument, with the two free-monoidal segments of the cons case
--     discharged by the morphism-variable solver `solveMor!`;
--   * `c-iso-assoc-to`   — its `to`-side dual, by composite inversion.
-- The transported identities `subst-id-{dom,cod}` and their groupoid laws live
-- one level down, in `Soundness/Base/Unflatten.agda`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Base.UnflattenMonoidal
  (sig : APROPSignature) where

open APROP sig

-- The laxator and the transported-identity kit, from the leaf below.  NOT
-- re-exported: `Strict/Embed`, the only consumer, imports that leaf directly.
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using ( unflatten; unflatten-++-≅; _≅_
        ; subst-id-cod; subst-id-dom; cast-cancel′; subst-cod-cons )

open import Categories.Category using (Category)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)
-- Morphism-variable monoidal solver (cf. `Bridge/BridgeCoherence.agda`).
open import Categories.Coherence.Monoidal.Frontend using (module FinSetup)

open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F)
import Data.Vec as Vec
open import Data.List.Properties using (++-assoc)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- The c-iso pentagon, by list induction on xs₁.

c-iso-assoc-from
  : ∀ xs₁ xs₂ ys
  → α⇒ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
    ∘ (_≅_.from (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
    ∘ _≅_.from (unflatten-++-≅ (xs₁ ++ xs₂) ys)
  ≈Term (id {unflatten xs₁} ⊗₁ _≅_.from (unflatten-++-≅ xs₂ ys))
        ∘ _≅_.from (unflatten-++-≅ xs₁ (xs₂ ++ ys))
        ∘ subst-id-cod (++-assoc xs₁ xs₂ ys)

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

    subst-id-xs₁' = subst-id-cod e

    -- Solver atoms, shared by BOTH shuffles below — one `FinSetup`
    -- application instead of two: 0 ↦ Var x, 1 ↦ U₁', 2 ↦ U₂, 3 ↦ U-ys,
    -- 4 ↦ U-12, 5 ↦ U-23, 6 ↦ unflatten ((xs₁' ++ xs₂) ++ ys),
    -- 7 ↦ unflatten (xs₁' ++ xs₂ ++ ys).
    open FinSetup FMC
      ( Vx Vec.∷ U₁' Vec.∷ U₂ Vec.∷ U-ys Vec.∷ U-12 Vec.∷ U-23
          Vec.∷ unflatten ((xs₁' ++ xs₂) ++ ys)
          Vec.∷ unflatten (xs₁' ++ xs₂ ++ ys) Vec.∷ Vec.[] )
    v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F
    v4 = V 4F ; v5 = V 5F ; v6 = V 6F ; v7 = V 7F

    ih : α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2
       ≈Term (id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁'
    ih = c-iso-assoc-from xs₁' xs₂ ys

    -- The free pre-IH shuffle (the pentagon law, ⊗-∘-dist, α-comm,
    -- α-iso cancellations, id-⊗ collection), as one solver call.
    shuffle₁
      : α⇒ {Vx ⊗₀ U₁'} {U₂} {U-ys}
          ∘ ((α⇐ ∘ id ⊗₁ c-1) ⊗₁ id)
          ∘ (α⇐ ∘ id ⊗₁ c-2)
      ≈Term α⇐ ∘ id ⊗₁ (α⇒ {U₁'} {U₂} {U-ys} ∘ (c-1 ⊗₁ id) ∘ c-2)
    shuffle₁ = solveMor! lhsᵗ rhsᵗ
      where
        -- generators: c-1, c-2
        open Sig {2} (λ { 0F → v4 , v1 ⊗ᵒ v2 ; 1F → v6 , v4 ⊗ᵒ v3 })
        open WithGen (λ { (genS 0F) → c-1 ; (genS 1F) → c-2 })
        g1 = gen 0F ; g2 = gen 1F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v6) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
        lhsᵗ = S._∘_ S.α⇒
                 (S._∘_ (S._⊗₁_ (S._∘_ S.α⇐ (S._⊗₁_ S.id g1)) S.id)
                        (S._∘_ S.α⇐ (S._⊗₁_ S.id g2)))
        rhsᵗ = S._∘_ S.α⇐ (S._⊗₁_ S.id (S._∘_ S.α⇒ (S._∘_ (S._⊗₁_ g1 S.id) g2)))

    -- The free post-IH shuffle (id-⊗ distribution, α⇐-comm-top,
    -- regrouping), as one solver call.
    shuffle₂
      : α⇐ ∘ id ⊗₁ ((id {U₁'} ⊗₁ c-3) ∘ c-4 ∘ subst-id-xs₁')
      ≈Term id ⊗₁ c-3
            ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
            ∘ (id ⊗₁ subst-id-xs₁')
    shuffle₂ = solveMor! lhsᵗ rhsᵗ
      where
        -- generators: c-3, c-4, subst-id-xs₁'
        open Sig {3} (λ { 0F → v5 , v2 ⊗ᵒ v3 ; 1F → v7 , v1 ⊗ᵒ v5 ; 2F → v6 , v7 })
        open WithGen (λ { (genS 0F) → c-3 ; (genS 1F) → c-4
                        ; (genS 2F) → subst-id-xs₁' })
        g3 = gen 0F ; g4 = gen 1F ; gs = gen 2F
        lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v6) ((v0 ⊗ᵒ v1) ⊗ᵒ (v2 ⊗ᵒ v3))
        lhsᵗ = S._∘_ S.α⇐ (S._⊗₁_ S.id (S._∘_ (S._⊗₁_ S.id g3) (S._∘_ g4 gs)))
        rhsᵗ = S._∘_ (S._⊗₁_ S.id g3)
                 (S._∘_ (S._∘_ S.α⇐ (S._⊗₁_ S.id g4)) (S._⊗₁_ S.id gs))

    -- Pre-IH shuffle, IH, post-IH shuffle, then fold the `id {Var x} ⊗
    -- subst-id-cod e` frame into `subst-id-cod e'`.  The clause's own goal
    -- types the chain; ascribing it here would only restate it.
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
        -- interchange, regrouping around the transported-identity factor.
          ≈⟨ shuffle₂ ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ (id ⊗₁ subst-id-xs₁')
        -- Step 4: fold `id {Var x} ⊗ subst-id-cod e` into the transported
        -- identity along `cong (x ∷_) e`, which IS `e'`.
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ subst-cod-cons e ⟩
      id ⊗₁ c-3
        ∘ (α⇐ {Vx} {U₁'} {U-23} ∘ (id ⊗₁ c-4))
        ∘ subst-id-cod e'
        ∎

--------------------------------------------------------------------------------
-- Associativity coherence, `to`-side.
--
-- `c-iso-assoc-from` above is the `from`-side pentagon.  Its
-- `to`-side dual is that same equation between the two INVERSE composites:
-- each side is a 3-fold composite whose reverse cancels pairwise (`cancel₃`),
-- so `inv-resp` transports `Rhs ≈ Lhs` to `Rhsinv ≈ Lhsinv`.

c-iso-assoc-to
  : ∀ xs₁ xs₂ ys
  → _≅_.to (unflatten-++-≅ (xs₁ ++ xs₂) ys)
    ∘ (_≅_.to (unflatten-++-≅ xs₁ xs₂) ⊗₁ id)
    ∘ α⇐ {unflatten xs₁} {unflatten xs₂} {unflatten ys}
  ≈Term subst-id-dom (++-assoc xs₁ xs₂ ys)
        ∘ _≅_.to (unflatten-++-≅ xs₁ (xs₂ ++ ys))
        ∘ (id {unflatten xs₁} ⊗₁ _≅_.to (unflatten-++-≅ xs₂ ys))
c-iso-assoc-to xs₁ xs₂ ys =
  ⟺ (inv-resp RhsinvRhs LhsLhsinv (⟺ (c-iso-assoc-from xs₁ xs₂ ys)))
  where
    RhsinvRhs = cancel₃ (⊗-cancel idˡ (_≅_.isoˡ (unflatten-++-≅ xs₂ ys)))
                        (_≅_.isoˡ (unflatten-++-≅ xs₁ (xs₂ ++ ys)))
                        (cast-cancel′ (++-assoc xs₁ xs₂ ys))

    LhsLhsinv = cancel₃ (_≅_.isoʳ (unflatten-++-≅ (xs₁ ++ xs₂) ys))
                        (⊗-cancel (_≅_.isoʳ (unflatten-++-≅ xs₁ xs₂)) idˡ)
                        α⇒∘α⇐≈id
