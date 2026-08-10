{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `bridge`-form for `α⇒` at EVERY object:
--
--   bridge (α⇒ {A}{B}{C}) ≈Term α⇒-form-list (flatten A)(flatten B)(flatten C)
--
-- via a single structural recursion (`Worker.work`) on the first object
-- index.  The compound case `((A₁₁⊗A₁₂)⊗A₂)` applies `pentagon-rewrite`,
-- distributes via `bridge-∘`/`bridge-⊗`, and recurses on the structural
-- subterms `A₁₁⊗A₁₂` and `A₂`;
-- the α⇐ factor is derived non-recursively (`derive-⇐`).  The residual
-- bottoms out in a pure list-level Mac-Lane coherence (`list-collapse-gen`,
-- induction on the prefix list).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.BridgeAlphaFormCompound
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-flatten-≈; unflatten-++-≅; bridge)
open import Categories.APROP.Hypergraph.Soundness.Bridge.BridgeCoherence sig
  using ( bridge-∘
        ; bridge-⊗
        ; bridge-id-is-id
        ; bridge-inv-id
        ; bridge-resp-≈Term
        ; α⇒-form-list
        ; α⇐-form-list
        ; α⇒-α⇐-iso
        ; pentagon-rewrite
        ; bridge-α⇒-form-Var
        ; bridge-α⇒-form-unit
        )

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_)
open import Categories.Morphism.Reasoning.Ext FreeMonoidal using (inv-resp)
-- Morphism-variable monoidal solver: discharges the F-/T-decomp chases
-- (coherence + naturality + interchange around the opaque unflatten isos)
-- as single `solveMor!` calls at the free monoidal category itself.
open import Categories.Coherence.Monoidal.Frontend using (module FinSetup)
open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
import Data.Vec as Vec
open Vec using (Vec)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- F-decomp lemmas.

private
  -- F-((unit⊗A)⊗(B⊗C)) ≈ F-(A⊗(B⊗C)) ∘ (λ⇒ ⊗ id).
  F-decomp-unit
    : ∀ A B C
    → _≅_.from (unflatten-flatten-≈ ((unit ⊗₀ A) ⊗₀ (B ⊗₀ C)))
    ≈Term _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C)))
          ∘ (λ⇒ {A} ⊗₁ id {B ⊗₀ C})
  F-decomp-unit A B C = solveMor! lhsᵗ rhsᵗ
    where
      -- atoms: 0 ↦ A, 1 ↦ uf A, 2 ↦ B⊗C, 3 ↦ uf (B⊗C), 4 ↦ unflatten (fA++fBC)
      open FinSetup FMC
        ( A Vec.∷ unflatten (flatten A)
            Vec.∷ (B ⊗₀ C) Vec.∷ unflatten (flatten B ++ flatten C)
            Vec.∷ unflatten (flatten A ++ (flatten B ++ flatten C)) Vec.∷ Vec.[] )
      v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
      -- generators: F-A, F-BC, c-A,BC-to
      open Sig {3} (λ { 0F →  v0 , v1 ; 1F →  v2 , v3 ; 2F →  v1 ⊗ᵒ v3 , v4 })
      open WithGen (λ { (genS 0F) → _≅_.from (unflatten-flatten-≈ A)
                      ; (genS 1F) → _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
                      ; (genS 2F) →
                          _≅_.to (unflatten-++-≅ (flatten A) (flatten B ++ flatten C)) })
      gFA = gen 0F ; gFBC = gen 1F
      gc  = gen 2F
      lhsᵗ = S._∘_ gc (S._⊗₁_ (S._∘_ S.λ⇒ (S._⊗₁_ S.id gFA)) gFBC)
      rhsᵗ = S._∘_ (S._∘_ gc (S._⊗₁_ gFA gFBC)) (S._⊗₁_ S.λ⇒ S.id)

  -- T-(((unit⊗A)⊗B)⊗C) ≈ ((λ⇐ ⊗ id) ⊗ id) ∘ T-((A⊗B)⊗C).
  T-decomp-unit
    : ∀ A B C
    → _≅_.to (unflatten-flatten-≈ (((unit ⊗₀ A) ⊗₀ B) ⊗₀ C))
    ≈Term ((λ⇐ {A} ⊗₁ id {B}) ⊗₁ id {C})
          ∘ _≅_.to (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
  T-decomp-unit A B C = solveMor! lhsᵗ rhsᵗ
    where
      -- atoms: 0 ↦ A, 1 ↦ B, 2 ↦ C, 3-5 ↦ their unflattens, 6 ↦ unflatten
      -- (fA++fB), 7 ↦ unflatten ((fA++fB)++fC)
      open FinSetup FMC
        ( A Vec.∷ B Vec.∷ C
            Vec.∷ unflatten (flatten A) Vec.∷ unflatten (flatten B)
            Vec.∷ unflatten (flatten C)
            Vec.∷ unflatten (flatten A ++ flatten B)
            Vec.∷ unflatten ((flatten A ++ flatten B) ++ flatten C) Vec.∷ Vec.[] )
      v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
      v5 = V 5F ; v6 = V 6F ; v7 = V 7F
      -- generators: T-A, T-B, T-C, c-A,B-from, c-AB,C-from
      open Sig {5} (λ { 0F →  v3 , v0
                      ; 1F →  v4 , v1
                      ; 2F →  v5 , v2
                      ; 3F →  v6 , v3 ⊗ᵒ v4
                      ; 4F →  v7 , v6 ⊗ᵒ v5 })
      open WithGen (λ { (genS 0F) → _≅_.to (unflatten-flatten-≈ A)
                      ; (genS 1F) → _≅_.to (unflatten-flatten-≈ B)
                      ; (genS 2F) → _≅_.to (unflatten-flatten-≈ C)
                      ; (genS 3F) →
                          _≅_.from (unflatten-++-≅ (flatten A) (flatten B))
                      ; (genS 4F) →
                          _≅_.from (unflatten-++-≅ (flatten A ++ flatten B) (flatten C)) })
      gTA = gen 0F ; gTB = gen 1F ; gTC = gen 2F
      gcAB = gen 3F ; gcABC = gen 4F
      lhsᵗ rhsᵗ : S.HomTerm v7 (((unitᵒ ⊗ᵒ v0) ⊗ᵒ v1) ⊗ᵒ v2)
      lhsᵗ = S._∘_ (S._⊗₁_ (S._∘_ (S._⊗₁_ (S._∘_ (S._⊗₁_ S.id gTA) S.λ⇐) gTB) gcAB) gTC) gcABC
      rhsᵗ = S._∘_ (S._⊗₁_ (S._⊗₁_ S.λ⇐ S.id) S.id)
                   (S._∘_ (S._⊗₁_ (S._∘_ (S._⊗₁_ gTA gTB) gcAB) gTC) gcABC)

  -- F-((Var x ⊗ A)⊗(B⊗C)) ≈ (id ⊗ F-(A⊗(B⊗C))) ∘ α⇒_{Var x, A, B⊗C}.
  F-decomp-Var
    : ∀ x A B C
    → _≅_.from (unflatten-flatten-≈ ((Var x ⊗₀ A) ⊗₀ (B ⊗₀ C)))
    ≈Term (id {Var x} ⊗₁ _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C))))
          ∘ α⇒ {Var x} {A} {B ⊗₀ C}
  F-decomp-Var x A B C = solveMor! lhsᵗ rhsᵗ
    where
      -- atoms: 0 ↦ Var x, 1 ↦ A, 2 ↦ B⊗C, 3 ↦ uf A, 4 ↦ uf (B⊗C),
      -- 5 ↦ unflatten (fA++fBC)
      open FinSetup FMC
        ( Var x Vec.∷ A Vec.∷ (B ⊗₀ C)
            Vec.∷ unflatten (flatten A)
            Vec.∷ unflatten (flatten B ++ flatten C)
            Vec.∷ unflatten (flatten A ++ (flatten B ++ flatten C)) Vec.∷ Vec.[] )
      v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
      v5 = V 5F
      -- generators: F-A, F-BC, c-A,BC-to
      open Sig {3} (λ { 0F →  v1 , v3 ; 1F →  v2 , v4 ; 2F →  v3 ⊗ᵒ v4 , v5 })
      open WithGen (λ { (genS 0F) → _≅_.from (unflatten-flatten-≈ A)
                      ; (genS 1F) → _≅_.from (unflatten-flatten-≈ (B ⊗₀ C))
                      ; (genS 2F) →
                          _≅_.to (unflatten-++-≅ (flatten A) (flatten B ++ flatten C)) })
      gFA = gen 0F ; gFBC = gen 1F
      gc  = gen 2F
      lhsᵗ rhsᵗ : S.HomTerm ((v0 ⊗ᵒ v1) ⊗ᵒ v2) (v0 ⊗ᵒ v5)
      lhsᵗ = S._∘_ (S._∘_ (S._⊗₁_ S.id gc) S.α⇒)
                   (S._⊗₁_ (S._∘_ (S._∘_ (S._⊗₁_ S.id S.λ⇒) S.α⇒) (S._⊗₁_ S.ρ⇐ gFA)) gFBC)
      rhsᵗ = S._∘_ (S._⊗₁_ S.id (S._∘_ gc (S._⊗₁_ gFA gFBC))) S.α⇒

  -- T-(((Var x ⊗ A)⊗B)⊗C) ≈ (α⇐_{V,A,B} ⊗ id) ∘ α⇐_{V,A⊗B,C} ∘ (id ⊗ T-((A⊗B)⊗C)).
  T-decomp-Var
    : ∀ x A B C
    → _≅_.to (unflatten-flatten-≈ (((Var x ⊗₀ A) ⊗₀ B) ⊗₀ C))
    ≈Term (α⇐ {Var x} {A} {B} ⊗₁ id {C})
          ∘ α⇐ {Var x} {A ⊗₀ B} {C}
          ∘ (id {Var x} ⊗₁ _≅_.to (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C)))
  T-decomp-Var x A B C = solveMor! lhsᵗ rhsᵗ
    where
      -- atoms: 0 ↦ Var x, 1 ↦ A, 2 ↦ B, 3 ↦ C, 4-6 ↦ their unflattens,
      -- 7 ↦ unflatten (fA++fB), 8 ↦ unflatten ((fA++fB)++fC)
      open FinSetup FMC
        ( Var x Vec.∷ A Vec.∷ B Vec.∷ C
            Vec.∷ unflatten (flatten A) Vec.∷ unflatten (flatten B)
            Vec.∷ unflatten (flatten C)
            Vec.∷ unflatten (flatten A ++ flatten B)
            Vec.∷ unflatten ((flatten A ++ flatten B) ++ flatten C) Vec.∷ Vec.[] )
      v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
      v5 = V 5F ; v6 = V 6F ; v7 = V 7F ; v8 = V 8F
      -- generators: T-A, T-B, T-C, c-A,B-from, c-A⊗B,C-from
      open Sig {5} (λ { 0F →  v4 , v1
                      ; 1F →  v5 , v2
                      ; 2F →  v6 , v3
                      ; 3F →  v7 , v4 ⊗ᵒ v5
                      ; 4F →  v8 , v7 ⊗ᵒ v6 })
      open WithGen (λ { (genS 0F) → _≅_.to (unflatten-flatten-≈ A)
                      ; (genS 1F) → _≅_.to (unflatten-flatten-≈ B)
                      ; (genS 2F) → _≅_.to (unflatten-flatten-≈ C)
                      ; (genS 3F) →
                          _≅_.from (unflatten-++-≅ (flatten A) (flatten B))
                      ; (genS 4F) →
                          _≅_.from (unflatten-++-≅ (flatten A ++ flatten B) (flatten C)) })
      gTA = gen 0F ; gTB = gen 1F ; gTC = gen 2F
      gcAB = gen 3F ; gcABC = gen 4F
      lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v8) (((v0 ⊗ᵒ v1) ⊗ᵒ v2) ⊗ᵒ v3)
      lhsᵗ = S._∘_
               (S._⊗₁_
                 (S._∘_
                   (S._⊗₁_
                     (S._∘_ (S._⊗₁_ S.ρ⇒ gTA) (S._∘_ S.α⇐ (S._⊗₁_ S.id S.λ⇐)))
                     gTB)
                   (S._∘_ S.α⇐ (S._⊗₁_ S.id gcAB)))
                 gTC)
               (S._∘_ S.α⇐ (S._⊗₁_ S.id gcABC))
      rhsᵗ = S._∘_ (S._⊗₁_ S.α⇐ S.id)
                   (S._∘_ S.α⇐
                     (S._⊗₁_ S.id
                       (S._∘_ (S._⊗₁_ (S._∘_ (S._⊗₁_ gTA gTB) gcAB) gTC) gcABC)))

--------------------------------------------------------------------------------
-- `derive-⇐`: the α⇐-form derived from the α⇒-form result at the SAME
-- object, via the α⇒/α⇐ iso.  Non-recursive (takes the α⇒ result as an
-- explicit argument), so it stays outside the well-founded recursion.

private
  derive-⇐
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
      ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)
    → bridge (α⇐ {A} {B} {C})
      ≈Term α⇐-form-list (flatten A) (flatten B) (flatten C)
  derive-⇐ A B C =
    inv-resp (bridge-inv-id α⇐ α⇒ α⇐∘α⇒≈id)
             (α⇒-α⇐-iso (flatten A) (flatten B) (flatten C))

--------------------------------------------------------------------------------
-- `list-collapse-gen`: the pure list-level Mac-Lane coherence the compound
-- `pentagon-rewrite` decomposition bottoms out in.  Induction on the prefix
-- list `p`; every step is a unitor/associator/`⊗-∘-dist` rewrite.

private
  cto : (as bs : List X) → HomTerm (unflatten as ⊗₀ unflatten bs) (unflatten (as ++ bs))
  cto as bs = _≅_.to (unflatten-++-≅ as bs)

  cfrom : (as bs : List X) → HomTerm (unflatten (as ++ bs)) (unflatten as ⊗₀ unflatten bs)
  cfrom as bs = _≅_.from (unflatten-++-≅ as bs)

  -- the 4-fold composite `pentagon-rewrite` produces, at prefix `p`.
  collapse-lhs
    : ∀ (p a b c : List X)
    → HomTerm (unflatten (((p ++ a) ++ b) ++ c)) (unflatten ((p ++ a) ++ b ++ c))
  collapse-lhs p a b c =
    α⇐-form-list p a (b ++ c)
      ∘ ( cto p (a ++ b ++ c)
        ∘ (id ⊗₁ α⇒-form-list a b c)
        ∘ cfrom p ((a ++ b) ++ c) )
      ∘ α⇒-form-list p (a ++ b) c
      ∘ ( cto (p ++ a ++ b) c
        ∘ (α⇒-form-list p a b ⊗₁ id)
        ∘ cfrom ((p ++ a) ++ b) c )

  list-collapse-gen
    : ∀ (p a b c : List X)
    → collapse-lhs p a b c ≈Term α⇒-form-list (p ++ a) b c
  -- Base p = []:  all `α…-form-list [] …` are `id`, `cto [] = λ⇒`, `cfrom []
  -- = λ⇐`; one free shuffle collapses the unitor frames and brings the
  -- `cto/cfrom` legs adjacent; the iso law finishes.
  list-collapse-gen [] a b c = begin
    collapse-lhs [] a b c
      ≈⟨ shuffle ⟩
    α⇒-form-list a b c ∘ ( cto (a ++ b) c ∘ cfrom (a ++ b) c )
      ≈⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-++-≅ (a ++ b) c) ⟩
    α⇒-form-list a b c ∘ id
      ≈⟨ idʳ ⟩
    α⇒-form-list a b c ∎
    where
      shuffle
        : collapse-lhs [] a b c
        ≈Term α⇒-form-list a b c ∘ ( cto (a ++ b) c ∘ cfrom (a ++ b) c )
      shuffle = solveMor! lhsᵗ rhsᵗ
        where
          -- atoms: 0 ↦ uf (a++b), 1 ↦ uf c, 2 ↦ uf ((a++b)++c),
          -- 3 ↦ uf (a++(b++c))
          open FinSetup FMC
            ( unflatten (a ++ b) Vec.∷ unflatten c
                Vec.∷ unflatten ((a ++ b) ++ c)
                Vec.∷ unflatten (a ++ b ++ c) Vec.∷ Vec.[] )
          v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F
          -- generators: α⇒-form-list a b c, cto (a++b) c, cfrom (a++b) c
          open Sig {3} (λ { 0F → v2 , v3 ; 1F → v0 ⊗ᵒ v1 , v2 ; 2F → v2 , v0 ⊗ᵒ v1 })
          open WithGen (λ { (genS 0F) → α⇒-form-list a b c
                          ; (genS 1F) → cto (a ++ b) c
                          ; (genS 2F) → cfrom (a ++ b) c })
          gα = gen 0F ; gcto = gen 1F ; gcfrom = gen 2F
          lhsᵗ rhsᵗ : S.HomTerm v2 v3
          lhsᵗ = S._∘_ S.id
                   (S._∘_ (S._∘_ S.λ⇒ (S._∘_ (S._⊗₁_ S.id gα) S.λ⇐))
                          (S._∘_ S.id
                            (S._∘_ gcto (S._∘_ (S._⊗₁_ S.id S.id) gcfrom))))
          rhsᵗ = S._∘_ gα (S._∘_ gcto gcfrom)

  -- Cons p = x ∷ p':  peel `id{Var x} ⊗ _` off the whole 4-fold composite in
  -- one free shuffle (the `cto/cfrom (x∷_)` associator frames slide across the
  -- opaque factors and cancel), then the IH finishes.
  list-collapse-gen (x ∷ p') a b c = begin
    collapse-lhs (x ∷ p') a b c
      ≈⟨ peel ⟩
    id {Var x} ⊗₁ collapse-lhs p' a b c
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (list-collapse-gen p' a b c) ⟩
    id {Var x} ⊗₁ α⇒-form-list (p' ++ a) b c ∎
    where
      peel
        : collapse-lhs (x ∷ p') a b c
        ≈Term id {Var x} ⊗₁ collapse-lhs p' a b c
      peel = solveMor! lhsᵗ rhsᵗ
        where
          -- atoms: 0 ↦ Var x, 1 ↦ uf p', 2 ↦ uf ((a++b)++c),
          -- 3 ↦ uf (a++(b++c)), 4 ↦ uf c, 5 ↦ uf ((p'++a)++b),
          -- 6 ↦ uf (p'++(a++b)), 7 ↦ uf (((p'++a)++b)++c),
          -- 8 ↦ uf ((p'++(a++b))++c), 9 ↦ uf (p'++((a++b)++c)),
          -- 10 ↦ uf (p'++(a++(b++c))), 11 ↦ uf ((p'++a)++(b++c))
          open FinSetup FMC
            ( Var x Vec.∷ unflatten p'
                Vec.∷ unflatten ((a ++ b) ++ c)
                Vec.∷ unflatten (a ++ b ++ c)
                Vec.∷ unflatten c
                Vec.∷ unflatten ((p' ++ a) ++ b)
                Vec.∷ unflatten (p' ++ a ++ b)
                Vec.∷ unflatten (((p' ++ a) ++ b) ++ c)
                Vec.∷ unflatten ((p' ++ a ++ b) ++ c)
                Vec.∷ unflatten (p' ++ (a ++ b) ++ c)
                Vec.∷ unflatten (p' ++ a ++ b ++ c)
                Vec.∷ unflatten ((p' ++ a) ++ b ++ c) Vec.∷ Vec.[] )
          v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
          v5 = V 5F ; v6 = V 6F ; v7 = V 7F ; v8 = V 8F ; v9 = V 9F
          v10 = V (Fin.suc 9F) ; v11 = V (Fin.suc (Fin.suc 9F))
          -- generators: αfl-abc, α⇐fl-p', α⇒fl-p'-ab-c, α⇒fl-p'-a-b,
          -- cto p', cfrom p', cto (p'++a++b) c, cfrom ((p'++a)++b) c
          open Sig {8} (λ { 0F → v2 , v3
                          ; 1F → v10 , v11
                          ; 2F → v8 , v9
                          ; 3F → v5 , v6
                          ; 4F → v1 ⊗ᵒ v3 , v10
                          ; 5F → v9 , v1 ⊗ᵒ v2
                          ; 6F → v6 ⊗ᵒ v4 , v8
                          ; 7F → v7 , v5 ⊗ᵒ v4 })
          open WithGen (λ { (genS 0F) → α⇒-form-list a b c
                          ; (genS 1F) → α⇐-form-list p' a (b ++ c)
                          ; (genS 2F) → α⇒-form-list p' (a ++ b) c
                          ; (genS 3F) → α⇒-form-list p' a b
                          ; (genS 4F) → cto p' (a ++ b ++ c)
                          ; (genS 5F) → cfrom p' ((a ++ b) ++ c)
                          ; (genS 6F) → cto (p' ++ a ++ b) c
                          ; (genS 7F) → cfrom ((p' ++ a) ++ b) c })
          gαabc = gen 0F ; g⇐ = gen 1F ; g⇒₂ = gen 2F ; g⇒₃ = gen 3F
          gcto₁ = gen 4F ; gcfrom₁ = gen 5F ; gcto₂ = gen 6F ; gcfrom₂ = gen 7F
          lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v7) (v0 ⊗ᵒ v11)
          lhsᵗ = S._∘_ (S._⊗₁_ S.id g⇐)
                   (S._∘_
                     (S._∘_ (S._∘_ (S._⊗₁_ S.id gcto₁) S.α⇒)
                            (S._∘_ (S._⊗₁_ S.id gαabc)
                                   (S._∘_ S.α⇐ (S._⊗₁_ S.id gcfrom₁))))
                     (S._∘_ (S._⊗₁_ S.id g⇒₂)
                       (S._∘_ (S._∘_ (S._⊗₁_ S.id gcto₂) S.α⇒)
                              (S._∘_ (S._⊗₁_ (S._⊗₁_ S.id g⇒₃) S.id)
                                     (S._∘_ S.α⇐ (S._⊗₁_ S.id gcfrom₂))))))
          rhsᵗ = S._⊗₁_ S.id
                   (S._∘_ g⇐
                     (S._∘_ (S._∘_ gcto₁ (S._∘_ (S._⊗₁_ S.id gαabc) gcfrom₁))
                            (S._∘_ g⇒₂
                              (S._∘_ gcto₂
                                     (S._∘_ (S._⊗₁_ g⇒₃ S.id) gcfrom₂)))))

--------------------------------------------------------------------------------
-- The worker.  `work A B C` proves the α⇒-form for `A` by structural
-- recursion on `A`, pattern-matched to a depth exposing the prefix shape;
-- every recursive call is on a structural subterm of the first argument.

module Worker where

  work
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
    ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)

  work unit    B C = bridge-α⇒-form-unit B C
  work (Var x) B C = bridge-α⇒-form-Var x B C

  -- A₁ = unit: F/T-decomp expose the λ-frames; the entire λ-machinery
  -- collapse is one free shuffle around the opaque F/T legs; then recurse.
  work (unit ⊗₀ A₂) B C = begin
    bridge (α⇒ {unit ⊗₀ A₂} {B} {C})
      ≈⟨ F-decomp-unit A₂ B C ⟩∘⟨ refl⟩∘⟨ T-decomp-unit A₂ B C ⟩
    (F-A₂BC ∘ (λ⇒ ⊗₁ id)) ∘ α⇒-uA₂ ∘ (((λ⇐ ⊗₁ id) ⊗₁ id) ∘ T-A₂BC)
      ≈⟨ shuffle ⟩
    F-A₂BC ∘ α⇒-A₂ ∘ T-A₂BC
      ≈⟨ work A₂ B C ⟩
    α⇒-form-list (flatten A₂) (flatten B) (flatten C) ∎
    where
      F-A₂BC  = _≅_.from (unflatten-flatten-≈ (A₂ ⊗₀ (B ⊗₀ C)))
      T-A₂BC  = _≅_.to   (unflatten-flatten-≈ ((A₂ ⊗₀ B) ⊗₀ C))
      α⇒-uA₂  = α⇒ {unit ⊗₀ A₂} {B} {C}
      α⇒-A₂   = α⇒ {A₂} {B} {C}

      shuffle
        : (F-A₂BC ∘ (λ⇒ ⊗₁ id)) ∘ α⇒-uA₂ ∘ (((λ⇐ ⊗₁ id) ⊗₁ id) ∘ T-A₂BC)
        ≈Term F-A₂BC ∘ α⇒-A₂ ∘ T-A₂BC
      shuffle = solveMor! lhsᵗ rhsᵗ
        where
          -- atoms: 0 ↦ A₂, 1 ↦ B, 2 ↦ C, 3 ↦ uf (fl (A₂⊗(B⊗C))),
          -- 4 ↦ uf (fl ((A₂⊗B)⊗C))
          open FinSetup FMC
            ( A₂ Vec.∷ B Vec.∷ C
                Vec.∷ unflatten (flatten (A₂ ⊗₀ (B ⊗₀ C)))
                Vec.∷ unflatten (flatten ((A₂ ⊗₀ B) ⊗₀ C)) Vec.∷ Vec.[] )
          v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
          -- generators: F-A₂BC, T-A₂BC
          open Sig {2} (λ { 0F → v0 ⊗ᵒ (v1 ⊗ᵒ v2) , v3 ; 1F → v4 , (v0 ⊗ᵒ v1) ⊗ᵒ v2 })
          open WithGen (λ { (genS 0F) → F-A₂BC ; (genS 1F) → T-A₂BC })
          gF = gen 0F ; gT = gen 1F
          lhsᵗ rhsᵗ : S.HomTerm v4 v3
          lhsᵗ = S._∘_ (S._∘_ gF (S._⊗₁_ S.λ⇒ S.id))
                       (S._∘_ S.α⇒
                         (S._∘_ (S._⊗₁_ (S._⊗₁_ S.λ⇐ S.id) S.id) gT))
          rhsᵗ = S._∘_ gF (S._∘_ S.α⇒ gT)

  -- A₁ = Var x: similar, with a `Var x` prefix.  The pentagon + α-collapse
  -- machinery is one free shuffle around the opaque F/T legs; then recurse.
  work (Var x ⊗₀ A) B C = begin
    bridge (α⇒ {Var x ⊗₀ A} {B} {C})
      ≈⟨ F-decomp-Var x A B C ⟩∘⟨ refl⟩∘⟨ T-decomp-Var x A B C ⟩
    ((id ⊗₁ F-ABC) ∘ α⇒-V,A,BC) ∘ α⇒-V⊗A ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
      ≈⟨ shuffle ⟩
    id ⊗₁ (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (work A B C) ⟩
    id ⊗₁ α⇒-form-list (flatten A) (flatten B) (flatten C) ∎
    where
      F-ABC      = _≅_.from (unflatten-flatten-≈ (A ⊗₀ (B ⊗₀ C)))
      T-AB⊗C     = _≅_.to   (unflatten-flatten-≈ ((A ⊗₀ B) ⊗₀ C))
      α⇒-V,A,BC  = α⇒ {Var x} {A} {B ⊗₀ C}
      α⇒-V⊗A     = α⇒ {Var x ⊗₀ A} {B} {C}
      α⇒-A,B,C   = α⇒ {A} {B} {C}
      α⇐-A,B     = α⇐ {Var x} {A} {B}
      α⇐-AB,C    = α⇐ {Var x} {A ⊗₀ B} {C}

      shuffle
        : ((id ⊗₁ F-ABC) ∘ α⇒-V,A,BC) ∘ α⇒-V⊗A
            ∘ ((α⇐-A,B ⊗₁ id) ∘ α⇐-AB,C ∘ (id ⊗₁ T-AB⊗C))
        ≈Term id ⊗₁ (F-ABC ∘ α⇒-A,B,C ∘ T-AB⊗C)
      shuffle = solveMor! lhsᵗ rhsᵗ
        where
          -- atoms: 0 ↦ Var x, 1 ↦ A, 2 ↦ B, 3 ↦ C, 4 ↦ uf (fl (A⊗(B⊗C))),
          -- 5 ↦ uf (fl ((A⊗B)⊗C))
          open FinSetup FMC
            ( Var x Vec.∷ A Vec.∷ B Vec.∷ C
                Vec.∷ unflatten (flatten (A ⊗₀ (B ⊗₀ C)))
                Vec.∷ unflatten (flatten ((A ⊗₀ B) ⊗₀ C)) Vec.∷ Vec.[] )
          v0 = V 0F ; v1 = V 1F ; v2 = V 2F ; v3 = V 3F ; v4 = V 4F
          v5 = V 5F
          -- generators: F-ABC, T-AB⊗C
          open Sig {2} (λ { 0F → v1 ⊗ᵒ (v2 ⊗ᵒ v3) , v4 ; 1F → v5 , (v1 ⊗ᵒ v2) ⊗ᵒ v3 })
          open WithGen (λ { (genS 0F) → F-ABC ; (genS 1F) → T-AB⊗C })
          gF = gen 0F ; gT = gen 1F
          lhsᵗ rhsᵗ : S.HomTerm (v0 ⊗ᵒ v5) (v0 ⊗ᵒ v4)
          lhsᵗ = S._∘_ (S._∘_ (S._⊗₁_ S.id gF) S.α⇒)
                       (S._∘_ S.α⇒
                         (S._∘_ (S._⊗₁_ S.α⇐ S.id)
                                (S._∘_ S.α⇐ (S._⊗₁_ S.id gT))))
          rhsᵗ = S._⊗₁_ S.id (S._∘_ gF (S._∘_ S.α⇒ gT))

  -- A₁ = A₁₁ ⊗ A₁₂: the genuinely compound case, by `pentagon-rewrite` +
  -- `bridge-∘` + recursion on strictly-smaller-`sz` objects.
  -- The four recursive calls are hoisted here into the clause right-hand
  -- side, where the match on `(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂` is visible, so each is on a
  -- structural subterm of the first argument — the left child `P = A₁₁ ⊗₀ A₁₂`
  -- or the right child `A₂`.  They feed the non-recursive `compound-body`,
  -- which assembles the `pentagon-rewrite` decomposition.  (Placing them in
  -- `compound-body`'s own `where` block would hide the descent from the
  -- termination checker, which is why the earlier version threaded an
  -- accessibility certificate.)
  work (P@(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂) B C =
    compound-body (work P A₂ (B ⊗₀ C)) (work P (A₂ ⊗₀ B) C)
                  (work P A₂ B) (work A₂ B C)
    where
      p  = flatten A₁₁ ++ flatten A₁₂   -- = flatten P

      compound-body
          : bridge (α⇒ {P} {A₂} {B ⊗₀ C})
              ≈Term α⇒-form-list p (flatten A₂) (flatten B ++ flatten C)
          → bridge (α⇒ {P} {A₂ ⊗₀ B} {C})
              ≈Term α⇒-form-list p (flatten A₂ ++ flatten B) (flatten C)
          → bridge (α⇒ {P} {A₂} {B})
              ≈Term α⇒-form-list p (flatten A₂) (flatten B)
          → bridge (α⇒ {A₂} {B} {C})
              ≈Term α⇒-form-list (flatten A₂) (flatten B) (flatten C)
          → bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
          ≈Term α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                              (flatten B) (flatten C)
      compound-body br⇒-P br-mid br-low br-A₂ = begin
        bridge (α⇒ {(A₁₁ ⊗₀ A₁₂) ⊗₀ A₂} {B} {C})
          ≈⟨ bridge-resp-≈Term pentagon-rewrite ⟩
        bridge ( α⇐ {P} {A₂} {B ⊗₀ C}
               ∘ id {P} ⊗₁ α⇒ {A₂} {B} {C}
               ∘ α⇒ {P} {A₂ ⊗₀ B} {C}
               ∘ α⇒ {P} {A₂} {B} ⊗₁ id {C} )
          ≈⟨ bridge-∘4 ⟩
        bridge (α⇐ {P} {A₂} {B ⊗₀ C})
          ∘ bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
          ∘ bridge (α⇒ {P} {A₂ ⊗₀ B} {C})
          ∘ bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
          ≈⟨ br-⇐ ⟩∘⟨ bx-mid ⟩∘⟨ br-mid ⟩∘⟨ bx-low ⟩
        collapse-lhs p (flatten A₂) (flatten B) (flatten C)
          ≈⟨ list-collapse-gen p (flatten A₂) (flatten B) (flatten C) ⟩
        α⇒-form-list ((flatten A₁₁ ++ flatten A₁₂) ++ flatten A₂)
                     (flatten B) (flatten C) ∎
        where
          -- the α⇐-form at `P`, derived non-recursively from the α⇒-form
          -- result `br⇒-P` at the SAME object.
          br-⇐ : bridge (α⇐ {P} {A₂} {B ⊗₀ C})
               ≈Term α⇐-form-list p (flatten A₂) (flatten B ++ flatten C)
          br-⇐ = derive-⇐ P A₂ (B ⊗₀ C) br⇒-P

          c-to   = λ as bs → _≅_.to   (unflatten-++-≅ as bs)
          c-from = λ as bs → _≅_.from (unflatten-++-≅ as bs)

          bx-mid
            : bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
            ≈Term c-to p (flatten A₂ ++ flatten B ++ flatten C)
                 ∘ (id ⊗₁ α⇒-form-list (flatten A₂) (flatten B) (flatten C))
                 ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C)
          bx-mid = begin
            bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
              ≈⟨ bridge-⊗ (id {P}) (α⇒ {A₂} {B} {C}) ⟩
            c-to p (flatten A₂ ++ flatten B ++ flatten C)
              ∘ (bridge (id {P}) ⊗₁ bridge (α⇒ {A₂} {B} {C}))
              ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C)
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (bridge-id-is-id P) br-A₂ ⟩∘⟨refl ⟩
            c-to p (flatten A₂ ++ flatten B ++ flatten C)
              ∘ (id ⊗₁ α⇒-form-list (flatten A₂) (flatten B) (flatten C))
              ∘ c-from p ((flatten A₂ ++ flatten B) ++ flatten C) ∎

          bx-low
            : bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
            ≈Term c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
                 ∘ (α⇒-form-list p (flatten A₂) (flatten B) ⊗₁ id)
                 ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C)
          bx-low = begin
            bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
              ≈⟨ bridge-⊗ (α⇒ {P} {A₂} {B}) (id {C}) ⟩
            c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
              ∘ (bridge (α⇒ {P} {A₂} {B}) ⊗₁ bridge (id {C}))
              ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C)
              ≈⟨ refl⟩∘⟨ ⊗-resp-≈ br-low (bridge-id-is-id C) ⟩∘⟨refl ⟩
            c-to (p ++ flatten A₂ ++ flatten B) (flatten C)
              ∘ (α⇒-form-list p (flatten A₂) (flatten B) ⊗₁ id)
              ∘ c-from ((p ++ flatten A₂) ++ flatten B) (flatten C) ∎

          bridge-∘4
            : bridge ( α⇐ {P} {A₂} {B ⊗₀ C}
                     ∘ id {P} ⊗₁ α⇒ {A₂} {B} {C}
                     ∘ α⇒ {P} {A₂ ⊗₀ B} {C}
                     ∘ α⇒ {P} {A₂} {B} ⊗₁ id {C} )
            ≈Term bridge (α⇐ {P} {A₂} {B ⊗₀ C})
                ∘ bridge (id {P} ⊗₁ α⇒ {A₂} {B} {C})
                ∘ bridge (α⇒ {P} {A₂ ⊗₀ B} {C})
                ∘ bridge (α⇒ {P} {A₂} {B} ⊗₁ id {C})
          bridge-∘4 = begin
            bridge (f0 ∘ f1 ∘ f2 ∘ f3)
              ≈⟨ bridge-∘ f0 (f1 ∘ f2 ∘ f3) ⟩
            bridge f0 ∘ bridge (f1 ∘ f2 ∘ f3)
              ≈⟨ refl⟩∘⟨ bridge-∘ f1 (f2 ∘ f3) ⟩
            bridge f0 ∘ bridge f1 ∘ bridge (f2 ∘ f3)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ bridge-∘ f2 f3 ⟩
            bridge f0 ∘ bridge f1 ∘ bridge f2 ∘ bridge f3 ∎
            where
              f0 = α⇐ {P} {A₂} {B ⊗₀ C}
              f1 = id {P} ⊗₁ α⇒ {A₂} {B} {C}
              f2 = α⇒ {P} {A₂ ⊗₀ B} {C}
              f3 = α⇒ {P} {A₂} {B} ⊗₁ id {C}
