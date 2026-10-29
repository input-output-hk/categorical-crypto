{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The term-level solver behind `Coherence.Symmetric.Solver.solveH!`: split
-- shared syntactic structure before invoking the hypergraph solver. See
-- docs/smc-solver-performance.md, "Splitting as an automatic solver heuristic".
-- Conservative equality may miss the fast path, never soundness.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Solver.Split (sig : APROPSignature) where

open import Categories.APROP.Hypergraph.Model.Translation sig
open import Categories.APROP.Hypergraph.Solver.Match.FindIso sig
open import Categories.APROP.Hypergraph.Soundness sig
open import Categories.APROP.Internal.Prelude

open import Data.Bool.Base
open import Data.Maybe.Base as Maybe
open import Data.Maybe.Ext using (force!)
open import Data.Nat.Base

open import Relation.Nullary

open APROP sig

private
  variable
    A B C A' B' : ObjTerm

-- Shared index-constrained constructors get stuck under without-K. Compare
-- at general endpoints, then collapse reflexive proofs with uip-ObjTerm.

eqH? : (f : HomTerm A B) (g : HomTerm A' B')
       (p : A ≡ A') (q : B ≡ B')
     → Maybe (subst₂ HomTerm p q f ≡ g)
eqH? (Agen m) (Agen m') refl refl with m ≟-mor m'
... | yes r = just (cong Agen r)
... | no _  = nothing
eqH? id id refl q with uip-ObjTerm q refl
... | refl = just refl
eqH? (_∘_ {B = M} f₂ f₁) (_∘_ {B = N} g₂ g₁) refl refl with M ≟-ObjTerm N
... | no _     = nothing
... | yes refl = zipWith (cong₂ _∘_) (eqH? f₂ g₂ refl refl) (eqH? f₁ g₁ refl refl)
eqH? (f₁ ⊗₁ f₂) (g₁ ⊗₁ g₂) refl refl =
  zipWith (cong₂ _⊗₁_) (eqH? f₁ g₁ refl refl) (eqH? f₂ g₂ refl refl)
eqH? λ⇒ λ⇒ p refl with uip-ObjTerm p refl
... | refl = just refl
eqH? λ⇐ λ⇐ refl q with uip-ObjTerm q refl
... | refl = just refl
eqH? ρ⇒ ρ⇒ p refl with uip-ObjTerm p refl
... | refl = just refl
eqH? ρ⇐ ρ⇐ refl q with uip-ObjTerm q refl
... | refl = just refl
eqH? α⇒ α⇒ refl q with uip-ObjTerm q refl
... | refl = just refl
eqH? α⇐ α⇐ refl q with uip-ObjTerm q refl
... | refl = just refl
eqH? (σ ⦃ v≤v ⦄) (σ ⦃ v≤v ⦄) refl q with uip-ObjTerm q refl
... | refl = just refl
eqH? _ _ _ _ = nothing

eq? : (f g : HomTerm A B) → Maybe (f ≡ g)
eq? f g = eqH? f g refl refl

fallback : (f g : HomTerm A B) → Maybe (f ≈Term g)
fallback f g = Maybe.map (λ iso → soundness {f = f} {g = g} iso) (findIsoᵀ ⟪ f ⟫ ⟪ g ⟫)

-- `peel` splits one level and leaves the fallback to its caller; `solveSplit?`
-- falls back at the stuck decomposition level, preserving the smaller window.

private
  peel solveSplit? : (f g : HomTerm A B) → Maybe (f ≈Term g)
  peel f g with eq? f g
  peel f g | just refl = just ≈-Term-refl
  peel (_∘_ {B = M} f₂ f₁) (_∘_ {B = N} g₂ g₁) | nothing with M ≟-ObjTerm N
  ... | no _     = nothing
  ... | yes refl = zipWith ∘-resp-≈ (solveSplit? f₂ g₂) (solveSplit? f₁ g₁)
  peel (f₁ ⊗₁ f₂) (g₁ ⊗₁ g₂) | nothing = zipWith ⊗-resp-≈ (solveSplit? f₁ g₁) (solveSplit? f₂ g₂)
  peel f g | nothing = nothing

  solveSplit? f g = peel f g <∣> fallback f g

-- Pair the graft with its witness: a catch-all then handles non-compositions
-- without asking a separate proof to reduce at an abstract term.
private
  compS : (g : HomTerm B C) (f : HomTerm A B)
        → Σ (HomTerm A C) (λ h → h ≈Term g ∘ f)
  compS (h ∘ g) f with compS g f
  ... | gf , p = h ∘ gf , ≈-Term-trans (∘-resp-≈ ≈-Term-refl p) (≈-Term-sym assoc)
  compS h f = h ∘ f , ≈-Term-refl

  reassocS : (f : HomTerm A B) → Σ (HomTerm A B) (λ g → g ≈Term f)
  reassocS (g ∘ f) with reassocS g | reassocS f
  ... | g' , pg | f' , pf with compS g' f'
  ...   | gf , pc = gf , ≈-Term-trans pc (∘-resp-≈ pg pf)
  reassocS (f ⊗₁ g) with reassocS f | reassocS g
  ... | f' , pf | g' , pg = f' ⊗₁ g' , ⊗-resp-≈ pf pg
  reassocS f = f , ≈-Term-refl

-- Reassociation only exposes cuts for peeling; the top-level fallback searches
-- the caller's own spelling, since `findIsoᵀ` is much slower on right-nested
-- chains than on balanced ones (docs/smc-solver-performance.md, rebalancing).
-- Match each reassocS pair once; separate projections would repeat both the
-- structural recursion and its proof.

solveTerm? : (f g : HomTerm A B) → Maybe (f ≈Term g)
solveTerm? f g with reassocS f | reassocS g
... | f' , pf | g' , pg =
  Maybe.map (λ p → ≈-Term-trans (≈-Term-sym pf) (≈-Term-trans p pg)) (peel f' g')
  <∣> fallback f g

solveTerm! : (f g : HomTerm A B) → is-just (solveTerm? f g) ≡ true → f ≈Term g
solveTerm! f g ok = force! (solveTerm? f g) ok
