{-# OPTIONS --safe --without-K #-}

-- The user-facing convenience wrappers over the monoidal / symmetric solver
-- front-ends: `Structural` (MacLane coherence), `Mor` (monoidal morphism
-- solver, `solveMor!`) and `Symmetric` (symmetric morphism solver,
-- `solveMorσ!`).  Each packages a `FinSetup(σ)` / `Solver` instantiation into a
-- single vector-of-triples signature.
--
-- (On the reference branch these live in `Categories.Coherence.Monoidal`
-- itself; on this branch that module name is taken by the object-variable
-- `solveM` coherence solver, so the wrappers get their own home here.)

module Categories.Coherence.Monoidal.Api where

open import Level using (Level)
open import Data.Nat
open import Data.Fin
open import Data.Product
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric using () renaming (Symmetric to SymmetricStructure)

open import Categories.FreeMonoidal
open import Categories.Coherence.Monoidal.MacLane
open import Categories.Coherence.Monoidal.Frontend
open import Categories.Coherence.Monoidal.Frontend.Sigma

module Structural
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  {n} (vars : Vec (C .MonoidalCategory.Obj) n)
  where

  private module Impl = Solver C vars
  -- the free-monoidal term DSL (Var, _⊗₀_, _⊗₁_, id, ρ⇒, α⇐, ⟦_⟧₁, …)
  open Impl public hiding (solveM)

  -- | Discharge `⟦ f ⟧₁ ≈ ⟦ g ⟧₁` for parallel structural morphisms `f g`.
  solveM = Impl.solveM

module Mor
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  {nA} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  (let module Impl = FinSetup C vars)
  -- the signature is one vector of triples: source arity, target arity, and
  -- the generator's interpretation (typed by `Impl`'s generator-free `⟦_⟧ₒ`).
  {nG} (gens : Vec (Σ[ st ∈ Impl.ObjTerm × Impl.ObjTerm ]
                      (C .MonoidalCategory.U [ Impl.⟦ proj₁ st ⟧ₒ , Impl.⟦ proj₂ st ⟧ₒ ])) nG)
  (let module ImplS = Impl.Sig (λ i → proj₁ (lookup gens i)))
  where
  open Impl public hiding (module Sig; ⟦_⟧ₒ)
  open ImplS public hiding (module WithGen)

  private module ImplW = ImplS.WithGen (λ { (genS i) → proj₂ (lookup gens i) })
  open ImplW public using (⟦_⟧₁; ⟦⟧-resp-≈)

  -- | Discharge a goal between interpretations of parallel front-end terms.
  solveMor!       = ImplW.solveMor!
  -- | Fire a rule (a `C`-equation between term interpretations) in context.
  rewriteMor!     = ImplW.rewriteMor!
  rewriteMorₙ!    = ImplW.rewriteMorₙ!
  -- | …with the rule's context located automatically.
  rewriteMorAuto! = ImplW.rewriteMorAuto!

module Symmetric
  {o ℓ e} (C : MonoidalCategory o ℓ e)
  (Sym : SymmetricStructure (C .MonoidalCategory.monoidal))
  {nA} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  (let module Impl = FinSetupσ C Sym vars)
  {nG} (gens : Vec (Σ[ st ∈ Impl.ObjTerm × Impl.ObjTerm ]
                      (C .MonoidalCategory.U [ Impl.⟦ proj₁ st ⟧ₒ , Impl.⟦ proj₂ st ⟧ₒ ])) nG)
  (let module ImplS = Impl.Sig (λ i → proj₁ (lookup gens i)))
  where
  open Impl public hiding (module Sig; ⟦_⟧ₒ)
  open ImplS public hiding (module WithGen)

  private module ImplW = ImplS.WithGen (λ { (genS i) → proj₂ (lookup gens i) })
  open ImplW public using (⟦_⟧₁; ⟦⟧-resp-≈)

  -- | Discharge a goal in a symmetric monoidal category (σ allowed).
  solveMorσ!       = ImplW.solveMor!
  -- | Fire a rule (a `C`-equation between term interpretations) in context.
  rewriteMorσ!     = ImplW.rewriteMor!
  rewriteMorσₙ!    = ImplW.rewriteMorₙ!
  -- | …with the rule's context located automatically.
  rewriteMorσAuto! = ImplW.rewriteMorAuto!
