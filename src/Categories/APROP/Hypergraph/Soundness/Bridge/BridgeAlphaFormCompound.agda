{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The `bridge`-form for `α⇒` at EVERY object:
--
--   bridge (α⇒ {A}{B}{C}) ≈Term α⇒-form-list (flatten A)(flatten B)(flatten C)
--
-- via a single structural recursion (`Worker.work`) on the first object
-- index, with ONE tensor clause: `A₁ ⊗₀ A₂` applies `pentagon-rewrite`,
-- distributes via `bridge-∘`/`bridge-⊗`, and recurses on the structural
-- subterms `A₁` and `A₂` — the prefix `A₁` needs no case analysis because
-- every ingredient below is stated at an arbitrary prefix LIST.
-- The α⇐ factor is derived non-recursively (`derive-⇐`).  The residual
-- bottoms out in a pure list-level Mac-Lane coherence (`list-collapse-gen`,
-- induction on the prefix list).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Bridge.BridgeAlphaFormCompound
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig
  using (unflatten; unflatten-++-≅; bridge)
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
-- Morphism-variable monoidal solver: discharges the two `list-collapse-gen`
-- chases (coherence + naturality + interchange around the opaque `unflatten`
-- isos) as single `solveMor!` calls at the free monoidal category itself.
open import Categories.Coherence.Monoidal.Frontend using (module FinSetup)
open import Data.Product using (_,_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
import Data.Vec as Vec
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- `derive-⇐`: the α⇐-form derived from the α⇒-form result at the SAME
-- object, via the α⇒/α⇐ iso.  Non-recursive (takes the α⇒ result as an
-- explicit argument), so it stays outside `work`'s recursion.

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
-- `list-collapse-gen`: the pure list-level Mac-Lane coherence that `work`'s
-- `pentagon-rewrite` decomposition bottoms out in.  Induction on the prefix
-- list `p`; every step is a unitor/associator/`⊗-∘-dist` rewrite.

private
  cto : (as bs : List X) → HomTerm (unflatten as ⊗₀ unflatten bs) (unflatten (as ++ bs))
  cto as bs = _≅_.to (unflatten-++-≅ as bs)

  cfrom : (as bs : List X) → HomTerm (unflatten (as ++ bs)) (unflatten as ⊗₀ unflatten bs)
  cfrom as bs = _≅_.from (unflatten-++-≅ as bs)

  -- `bridge` of a tensor whose two factors are already known: `bridge-⊗`
  -- followed by the congruence in the middle.  Both `⊗`-factors of `work`'s
  -- tensor decomposition below are this shape (with `id` on one side).
  bridge-⊗-resp
    : ∀ {A B C D} (f : HomTerm A B) (g : HomTerm C D)
        {rf : HomTerm (unflatten (flatten A)) (unflatten (flatten B))}
        {rg : HomTerm (unflatten (flatten C)) (unflatten (flatten D))}
    → bridge f ≈Term rf → bridge g ≈Term rg
    → bridge (f ⊗₁ g)
      ≈Term cto (flatten B) (flatten D) ∘ (rf ⊗₁ rg) ∘ cfrom (flatten A) (flatten C)
  bridge-⊗-resp f g ef eg = bridge-⊗ f g ○ (refl⟩∘⟨ ⊗-resp-≈ ef eg ⟩∘⟨refl)

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
      ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
    α⇒-form-list a b c ∘ ( cto (a ++ b) c ∘ cfrom (a ++ b) c )
      ≈⟨ refl⟩∘⟨ _≅_.isoˡ (unflatten-++-≅ (a ++ b) c) ⟩
    α⇒-form-list a b c ∘ id
      ≈⟨ idʳ ⟩
    α⇒-form-list a b c ∎
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
      ≈⟨ solveMor! lhsᵗ rhsᵗ ⟩
    id {Var x} ⊗₁ collapse-lhs p' a b c
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (list-collapse-gen p' a b c) ⟩
    id {Var x} ⊗₁ α⇒-form-list (p' ++ a) b c ∎
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
-- recursion on `A`.

module Worker where

  work
    : ∀ A B C
    → bridge (α⇒ {A} {B} {C})
    ≈Term α⇒-form-list (flatten A) (flatten B) (flatten C)

  work unit    B C = bridge-α⇒-form-unit B C
  work (Var x) B C = bridge-α⇒-form-Var x B C

  -- `pentagon-rewrite` re-associates `α⇒ {A₁ ⊗₀ A₂}` into four legs whose
  -- bridges are the four recursive results; `bridge-∘`/`bridge-⊗` distribute,
  -- and the residue is the list-level `collapse-lhs`.  The prefix needs NO case
  -- analysis: every ingredient is stated at an arbitrary prefix LIST, so the
  -- one clause covers `A₁ = unit`, `A₁ = Var x` and `A₁` compound alike.
  -- Each recursive call is on a structural subterm of the matched first
  -- argument (`A₁` or `A₂`) and sits in the clause's right-hand side, where the
  -- match is visible to the termination checker.
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
      ≈⟨ derive-⇐ A₁ A₂ (B ⊗₀ C) (work A₁ A₂ (B ⊗₀ C))
         ⟩∘⟨ bridge-⊗-resp (id {A₁}) (α⇒ {A₂} {B} {C})
                           (bridge-id-is-id A₁) (work A₂ B C)
         ⟩∘⟨ work A₁ (A₂ ⊗₀ B) C
         ⟩∘⟨ bridge-⊗-resp (α⇒ {A₁} {A₂} {B}) (id {C})
                           (work A₁ A₂ B) (bridge-id-is-id C) ⟩
    collapse-lhs (flatten A₁) (flatten A₂) (flatten B) (flatten C)
      ≈⟨ list-collapse-gen (flatten A₁) (flatten A₂) (flatten B) (flatten C) ⟩
    α⇒-form-list (flatten A₁ ++ flatten A₂) (flatten B) (flatten C) ∎
