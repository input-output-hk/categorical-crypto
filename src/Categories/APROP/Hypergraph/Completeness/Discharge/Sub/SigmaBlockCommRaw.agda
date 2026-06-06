{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- `σ-block-comm-raw` — the bare iterated TWO-BLOCK braiding at `List X`:
--
--   to(unflatten-++-≅ ys xs) ∘ σ{unflatten xs}{unflatten ys}
--       ∘ from(unflatten-++-≅ xs ys)
--     ≈Term permute (++-comm xs ys)
--
-- The `BraidBlock`/`BraidPermute` "iteration + swap-core assembly"; consumed
-- by `Sub/BlockNFBraid.agda` as `σ-block-comm-raw`.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockCommRaw
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; unflatten-++-≅; permute; α⇐-comm)
open import Categories.FreeSMC.BraidBlock d
  using (σ-block)
open import Categories.FreeSMC.BraidPermute d
  using (rotate; σ-rotate; permute-rotate; permute-swap-refl-σ-block)
open import Categories.FreeSMC.SigmaBlockTensor d using (σ⊗-from-hexagon₂)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon d
  using (σ-block-natural₃; σ-block-natural₁; hexagon₂)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅; Iso)
open import Categories.MonoidalCoherence using (module Solver)
import Data.Vec as Vec
open Vec using (Vec)
open import Data.Fin using (Fin; zero; suc)
open import Categories.Category.Monoidal.Symmetric Monoidal-FreeMonoidal using (Symmetric)
open import Categories.Category.Monoidal.Braided.Properties
  (Symmetric.braided Symmetric-Monoidal)
  using (braiding-coherence; braiding-coherence-inv)
open import Categories.Category.Monoidal.Properties Monoidal-FreeMonoidal
  using (coherence₁; coherence₃; coherence-inv₂)

open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as LP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

-- `↭-sym (shift x ys xs) ≡ rotate x ys xs`.
shift-sym-rotate
  : ∀ (x : X) (ys xs : List X)
  → Perm.↭-sym (PermProp.shift x ys xs) ≡ rotate x ys xs
shift-sym-rotate x []        xs = refl
shift-sym-rotate x (b ∷ ys') xs =
  cong (λ r → Perm.trans (Perm.swap x b Perm.refl) (Perm.prep b r))
       (shift-sym-rotate x ys' xs)

--------------------------------------------------------------------------------
-- ## `permute-comm-cons` — `permute (++-comm (x∷xs') ys)` factors as the
-- single-atom rotation `σ-rotate x ys xs'` post-composed with the IH block.
-- Handles the smart `↭-trans` collapse at `ys = []` uniformly.

permute-comm-cons
  : (x : X) (xs' ys : List X)
  → permute (PermProp.++-comm (x ∷ xs') ys)
    ≈Term σ-rotate x ys xs' ∘ (id {A = Var x} ⊗₁ permute (PermProp.++-comm xs' ys))
permute-comm-cons x xs' []        = ≈-Term-sym idˡ
permute-comm-cons x xs' (b ∷ ys') = begin
    permute (PermProp.++-comm (x ∷ xs') (b ∷ ys'))
      ≡⟨⟩
    permute (Perm.↭-sym (PermProp.shift x (b ∷ ys') xs'))
      ∘ (id ⊗₁ permute (PermProp.++-comm xs' (b ∷ ys')))
      ≈⟨ ≡⇒≈Term (cong (λ r → permute r ∘ (id ⊗₁ permute (PermProp.++-comm xs' (b ∷ ys'))))
                   (shift-sym-rotate x (b ∷ ys') xs')) ⟩
    permute (rotate x (b ∷ ys') xs')
      ∘ (id ⊗₁ permute (PermProp.++-comm xs' (b ∷ ys')))
      ≈⟨ permute-rotate x (b ∷ ys') xs' ⟩∘⟨refl ⟩
    σ-rotate x (b ∷ ys') xs'
      ∘ (id ⊗₁ permute (PermProp.++-comm xs' (b ∷ ys')))
  ∎

--------------------------------------------------------------------------------
-- ## `peel` — the hexagon "atom-off-the-front-of-the-moving-block" peel.
-- Braiding `Var x ⊗ unflatten xs'` past `unflatten ys` splits into braiding
-- the atom `Var x` past `ys` (a `σ-block`) and braiding the tail block `xs'`
-- past `ys` (in the `id{Var x} ⊗ _` slot).  `σ⊗-from-hexagon₂` + α-iso cancel.

peel
  : (x : X) (xs' ys : List X)
  → σ {A = Var x ⊗₀ unflatten xs'} {B = unflatten ys}
      ∘ _≅_.from (unflatten-++-≅ (x ∷ xs') ys)
    ≈Term σ-block {Var x} {unflatten ys} {unflatten xs'}
            ∘ (id {A = Var x} ⊗₁ (σ {A = unflatten xs'} {B = unflatten ys}
                                    ∘ _≅_.from (unflatten-++-≅ xs' ys)))
peel x xs' ys = begin
    σ {A = Vx ⊗₀ Uxs'} {B = Uys} ∘ fromcons
      ≈⟨ σ⊗-from-hexagon₂ ⟩∘⟨refl ⟩
    (α⇒ ∘ ((σ {A = Vx} {B = Uys} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ {A = Uxs'} {B = Uys})) ∘ α⇒)
      ∘ (α⇐ ∘ (id ⊗₁ fromxs))
      ≈⟨ pull ⟩
    (α⇒ ∘ (σ {A = Vx} {B = Uys} ⊗₁ id) ∘ α⇐)
      ∘ (id ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs))
  ∎
  where
    Vx = Var x
    Uxs' = unflatten xs'
    Uys = unflatten ys
    fromxs = _≅_.from (unflatten-++-≅ xs' ys)
    fromcons = _≅_.from (unflatten-++-≅ (x ∷ xs') ys)
    pull
      : (α⇒ ∘ ((σ {A = Vx} {B = Uys} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ {A = Uxs'} {B = Uys})) ∘ α⇒)
          ∘ (α⇐ ∘ (id ⊗₁ fromxs))
        ≈Term (α⇒ ∘ (σ {A = Vx} {B = Uys} ⊗₁ id) ∘ α⇐)
                ∘ (id ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs))
    pull = begin
        (α⇒ ∘ ((S1 ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ S2)) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ F))
          ≈⟨ assoc ⟩
        α⇒ ∘ (((S1 ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ S2)) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ F))
          ≈⟨ refl⟩∘⟨ assoc ⟩
        α⇒ ∘ ((S1 ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ S2)) ∘ (α⇒ ∘ (α⇐ ∘ (id ⊗₁ F)))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
        α⇒ ∘ ((S1 ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ S2)) ∘ ((α⇒ ∘ α⇐) ∘ (id ⊗₁ F))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (α⇒∘α⇐≈id ⟩∘⟨refl) ⟩
        α⇒ ∘ ((S1 ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ S2)) ∘ (id ∘ (id ⊗₁ F))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        α⇒ ∘ ((S1 ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ S2)) ∘ (id ⊗₁ F)
          ≈⟨ refl⟩∘⟨ assoc ⟩
        α⇒ ∘ (S1 ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ S2)) ∘ (id ⊗₁ F))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
        α⇒ ∘ (S1 ⊗₁ id) ∘ (α⇐ ∘ ((id ⊗₁ S2) ∘ (id ⊗₁ F)))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist) ⟩
        α⇒ ∘ (S1 ⊗₁ id) ∘ (α⇐ ∘ ((id ∘ id) ⊗₁ (S2 ∘ F)))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (⊗-resp-≈ idˡ ≈-Term-refl) ⟩
        α⇒ ∘ (S1 ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (S2 ∘ F)))
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇒ ∘ (S1 ⊗₁ id)) ∘ (α⇐ ∘ (id ⊗₁ (S2 ∘ F)))
          ≈⟨ assoc ⟩
        α⇒ ∘ ((S1 ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ (S2 ∘ F))))
          ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
        α⇒ ∘ ((S1 ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (S2 ∘ F))
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇒ ∘ (S1 ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (S2 ∘ F))
      ∎
      where
        S1 = σ {A = Vx} {B = Uys}
        S2 = σ {A = Uxs'} {B = Uys}
        F = fromxs

--------------------------------------------------------------------------------
-- ## `rotate-cap` — the single-atom braid / cap coherence:
--
--   to(uf++ ys (x ∷ ts)) ∘ σ-block{Var x}{unflatten ys}{unflatten ts}
--     ≈ σ-rotate x ys ts ∘ (id{Var x} ⊗ to(uf++ ys ts))
--
-- Induction on `ys`.  The `ys=[]` base is unit-braiding coherence; the
-- `ys=b∷ys'` step is the hexagon iteration (peeling `Vb` off the FRONT of
-- the fixed block).

private
  _⟨≈≈⟩_ : ∀ {A B} {f g h : HomTerm A B} → f ≈Term g → g ≈Term h → f ≈Term h
  _⟨≈≈⟩_ = ≈-Term-trans
  infixr 4 _⟨≈≈⟩_

-- Bare second-arg-tensor decomposition of `σ`, from the `hexagon` axiom
-- (the genuine braiding content of the `ys`-step).
σ-Bmerge-bare
  : ∀ {A B₁ B₂ : ObjTerm}
  → σ {A = A} {B = B₁ ⊗₀ B₂}
    ≈Term α⇐ {A = B₁} {B = B₂} {C = A}
            ∘ (id {A = B₁} ⊗₁ σ {A = A} {B = B₂})
            ∘ α⇒ {A = B₁} {B = A} {C = B₂}
            ∘ (σ {A = A} {B = B₁} ⊗₁ id {A = B₂})
            ∘ α⇐ {A = A} {B = B₁} {C = B₂}
σ-Bmerge-bare {A} {B₁} {B₂} = ≈-Term-sym (begin
    α⇐ ∘ (idσ ∘ α⇒ ∘ σid ∘ α⇐)
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym assoc) ⟩
    α⇐ ∘ (idσ ∘ (α⇒ ∘ σid) ∘ α⇐)
      ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
    α⇐ ∘ ((idσ ∘ (α⇒ ∘ σid)) ∘ α⇐)
      ≈⟨ refl⟩∘⟨ (∘-resp-≈ (hexagon {A = A} {B = B₁} {C = B₂}) ≈-Term-refl) ⟩
    α⇐ ∘ ((α⇒ ∘ σ ∘ α⇒') ∘ α⇐)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ (α⇒ ∘ (σ ∘ α⇒') ∘ α⇐)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    α⇐ ∘ (α⇒ ∘ σ ∘ (α⇒' ∘ α⇐))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩
    α⇐ ∘ (α⇒ ∘ σ ∘ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idʳ ⟩
    α⇐ ∘ (α⇒ ∘ σ)
      ≈⟨ ≈-Term-sym assoc ⟩
    (α⇐ ∘ α⇒) ∘ σ
      ≈⟨ α⇐∘α⇒≈id ⟩∘⟨refl ⟩
    id ∘ σ
      ≈⟨ idˡ ⟩
    σ {A = A} {B = B₁ ⊗₀ B₂}
  ∎)
  where
    idσ = id {A = B₁} ⊗₁ σ {A = A} {B = B₂}
    σid = σ {A = A} {B = B₁} ⊗₁ id {A = B₂}
    α⇒' = α⇒ {A = A} {B = B₁} {C = B₂}

-- B-slot tensor decomposition of `σ-block`: the pure α-coherence wrapping of
-- `σ-Bmerge-bare`.  Both sides reduce to a common normal form `nf` in which
-- the two braid cells are framed by associators; `lhs≈nf` substitutes
-- `σ-Bmerge-bare` into the bare LHS and distributes `⊗ id{C}`, while `rhs≈nf`
-- slides the RHS associators across the two cells via `α-comm`/pentagon.
σ-block-Bmerge
  : ∀ {A B₁ B₂ C : ObjTerm}
  → σ-block {A} {B₁ ⊗₀ B₂} {C}
    ≈Term α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
            ∘ (id {A = B₁} ⊗₁ σ-block {A} {B₂} {C})
            ∘ σ-block {A} {B₁} {B₂ ⊗₀ C}
            ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
σ-block-Bmerge {A} {B₁} {B₂} {C} = ≈-Term-trans lhs≈nf (≈-Term-sym rhs≈nf)
  where
    σ₁ = σ {A = A} {B = B₁}
    σ₂ = σ {A = A} {B = B₂}

    -- `(f ∘ g) ⊗ id ≈ (f ⊗ id) ∘ (g ⊗ id)`.
    ⊗id-d : ∀ {Y₁ Y₂ Y₃ Z : ObjTerm} {f : HomTerm Y₂ Y₃} {g : HomTerm Y₁ Y₂}
          → (f ∘ g) ⊗₁ id {A = Z} ≈Term (f ⊗₁ id) ∘ (g ⊗₁ id)
    ⊗id-d = ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

    -- The common normal form: `σ-Bmerge-bare ⊗ id{C}` distributed, framed by
    -- the outer `α⇒/α⇐` of `σ-block{A}{B₁⊗B₂}{C}`.
    nf : HomTerm (A ⊗₀ ((B₁ ⊗₀ B₂) ⊗₀ C)) ((B₁ ⊗₀ B₂) ⊗₀ (A ⊗₀ C))
    nf = α⇒ {A = B₁ ⊗₀ B₂} {B = A} {C = C}
       ∘ (α⇐ {A = B₁} {B = B₂} {C = A} ⊗₁ id {A = C})
       ∘ ((id {A = B₁} ⊗₁ σ₂) ⊗₁ id {A = C})
       ∘ (α⇒ {A = B₁} {B = A} {C = B₂} ⊗₁ id {A = C})
       ∘ ((σ₁ ⊗₁ id {A = B₂}) ⊗₁ id {A = C})
       ∘ (α⇐ {A = A} {B = B₁} {C = B₂} ⊗₁ id {A = C})
       ∘ α⇐ {A = A} {B = B₁ ⊗₀ B₂} {C = C}

    -- LHS = σ-block{A}{B₁⊗B₂}{C} = α⇒ ∘ (σ{A}{B₁⊗B₂} ⊗ id) ∘ α⇐;
    -- rewrite σ{A}{B₁⊗B₂} via σ-Bmerge-bare and distribute `⊗ id{C}`.
    lhs≈nf : σ-block {A} {B₁ ⊗₀ B₂} {C} ≈Term nf
    lhs≈nf = begin
        α⇒ ∘ (σ {A = A} {B = B₁ ⊗₀ B₂} ⊗₁ id {A = C}) ∘ α⇐
          ≈⟨ refl⟩∘⟨ (⊗-resp-≈ σ-Bmerge-bare ≈-Term-refl ⟩∘⟨refl) ⟩
        α⇒
          ∘ ((α⇐ ∘ (id ⊗₁ σ₂) ∘ α⇒ ∘ (σ₁ ⊗₁ id) ∘ α⇐) ⊗₁ id {A = C}) ∘ α⇐
          ≈⟨ refl⟩∘⟨ (dist ⟩∘⟨refl) ⟩
        α⇒
          ∘ ((α⇐ ⊗₁ id)
              ∘ ((id ⊗₁ σ₂) ⊗₁ id)
              ∘ (α⇒ ⊗₁ id)
              ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
              ∘ (α⇐ ⊗₁ id)) ∘ α⇐
          ≈⟨ refl⟩∘⟨ assoc ⟩
        α⇒
          ∘ (α⇐ ⊗₁ id)
          ∘ (((id ⊗₁ σ₂) ⊗₁ id)
              ∘ (α⇒ ⊗₁ id)
              ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
              ∘ (α⇐ ⊗₁ id)) ∘ α⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
        α⇒
          ∘ (α⇐ ⊗₁ id)
          ∘ ((id ⊗₁ σ₂) ⊗₁ id)
          ∘ ((α⇒ ⊗₁ id)
              ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
              ∘ (α⇐ ⊗₁ id)) ∘ α⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
        α⇒
          ∘ (α⇐ ⊗₁ id)
          ∘ ((id ⊗₁ σ₂) ⊗₁ id)
          ∘ (α⇒ ⊗₁ id)
          ∘ (((σ₁ ⊗₁ id) ⊗₁ id)
              ∘ (α⇐ ⊗₁ id)) ∘ α⇐
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
        α⇒
          ∘ (α⇐ ⊗₁ id)
          ∘ ((id ⊗₁ σ₂) ⊗₁ id)
          ∘ (α⇒ ⊗₁ id)
          ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
          ∘ (α⇐ ⊗₁ id) ∘ α⇐
      ∎
      where
        -- (g₁ ∘ g₂ ∘ g₃ ∘ g₄ ∘ g₅) ⊗ id ≈ (g₁⊗id) ∘ ... ∘ (g₅⊗id)
        dist
          : (α⇐ {A = B₁} {B = B₂} {C = A} ∘ (id ⊗₁ σ₂) ∘ α⇒ {A = B₁} {B = A} {C = B₂}
              ∘ (σ₁ ⊗₁ id) ∘ α⇐ {A = A} {B = B₁} {C = B₂}) ⊗₁ id {A = C}
            ≈Term (α⇐ ⊗₁ id)
                ∘ ((id ⊗₁ σ₂) ⊗₁ id)
                ∘ (α⇒ ⊗₁ id)
                ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
                ∘ (α⇐ ⊗₁ id)
        dist = begin
            (α⇐ ∘ (id ⊗₁ σ₂) ∘ α⇒ ∘ (σ₁ ⊗₁ id) ∘ α⇐) ⊗₁ id
              ≈⟨ ⊗id-d ⟩
            (α⇐ ⊗₁ id) ∘ (((id ⊗₁ σ₂) ∘ α⇒ ∘ (σ₁ ⊗₁ id) ∘ α⇐) ⊗₁ id)
              ≈⟨ refl⟩∘⟨ ⊗id-d ⟩
            (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ₂) ⊗₁ id) ∘ ((α⇒ ∘ (σ₁ ⊗₁ id) ∘ α⇐) ⊗₁ id)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-d ⟩
            (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ₂) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ (((σ₁ ⊗₁ id) ∘ α⇐) ⊗₁ id)
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗id-d ⟩
            (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ₂) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
              ∘ ((σ₁ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)
          ∎

    -- Solver instance over the 4 atoms `B₁ B₂ A C` (in this order), used to
    -- discharge the three pure-associator framing identities E1/E2/E3 below
    -- (Mac-Lane coherence; no braiding).
    vars : Vec ObjTerm 4
    vars = B₁ Vec.∷ B₂ Vec.∷ A Vec.∷ C Vec.∷ Vec.[]

    open Solver (record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal })
                {n = 4} vars
      using (solveM)
      renaming (α⇒ to α⇒ˢ; α⇐ to α⇐ˢ; id to idˢ; _∘_ to _∘ˢ_;
                _⊗₁_ to _⊗₁ˢ_; _⊗₀_ to _⊗₀ˢ_; Var to Varˢ)

    b₁ b₂ a c : _
    b₁ = Varˢ zero
    b₂ = Varˢ (suc zero)
    a  = Varˢ (suc (suc zero))
    c  = Varˢ (suc (suc (suc zero)))

    -- E1: framing before the σ₂-cell.
    --   α⇐{B₁}{B₂}{A⊗C} ∘ (id{B₁}⊗α⇒{B₂}{A}{C}) ∘ α⇒{B₁}{B₂⊗A}{C}
    --     ≈ α⇒{B₁⊗B₂}{A}{C} ∘ (α⇐{B₁}{B₂}{A} ⊗ id{C})
    E1 : α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
           ∘ (id {A = B₁} ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
           ∘ α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
         ≈Term α⇒ {A = B₁ ⊗₀ B₂} {B = A} {C = C}
           ∘ (α⇐ {A = B₁} {B = B₂} {C = A} ⊗₁ id {A = C})
    E1 = solveM
      (α⇐ˢ {A = b₁} {b₂} {a ⊗₀ˢ c}
        ∘ˢ (idˢ ⊗₁ˢ α⇒ˢ {A = b₂} {a} {c})
        ∘ˢ α⇒ˢ {A = b₁} {b₂ ⊗₀ˢ a} {c})
      (α⇒ˢ {A = b₁ ⊗₀ˢ b₂} {a} {c}
        ∘ˢ (α⇐ˢ {A = b₁} {b₂} {a} ⊗₁ˢ idˢ))

    -- E2: framing between the σ₂-cell and the σ₁-cell.
    --   α⇐{B₁}{A⊗B₂}{C} ∘ (id{B₁}⊗α⇐{A}{B₂}{C}) ∘ α⇒{B₁}{A}{B₂⊗C} ∘ α⇒{B₁⊗A}{B₂}{C}
    --     ≈ (α⇒{B₁}{A}{B₂} ⊗ id{C})
    E2 : α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
           ∘ (id {A = B₁} ⊗₁ α⇐ {A = A} {B = B₂} {C = C})
           ∘ α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
           ∘ α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
         ≈Term (α⇒ {A = B₁} {B = A} {C = B₂} ⊗₁ id {A = C})
    E2 = solveM
      (α⇐ˢ {A = b₁} {a ⊗₀ˢ b₂} {c}
        ∘ˢ (idˢ ⊗₁ˢ α⇐ˢ {A = a} {b₂} {c})
        ∘ˢ α⇒ˢ {A = b₁} {a} {b₂ ⊗₀ˢ c}
        ∘ˢ α⇒ˢ {A = b₁ ⊗₀ˢ a} {b₂} {c})
      (α⇒ˢ {A = b₁} {a} {b₂} ⊗₁ˢ idˢ)

    -- E3: framing after the σ₁-cell.
    --   α⇐{A⊗B₁}{B₂}{C} ∘ α⇐{A}{B₁}{B₂⊗C} ∘ (id{A}⊗α⇒{B₁}{B₂}{C})
    --     ≈ (α⇐{A}{B₁}{B₂} ⊗ id{C}) ∘ α⇐{A}{B₁⊗B₂}{C}
    E3 : α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
           ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C}
           ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
         ≈Term (α⇐ {A = A} {B = B₁} {C = B₂} ⊗₁ id {A = C})
           ∘ α⇐ {A = A} {B = B₁ ⊗₀ B₂} {C = C}
    E3 = solveM
      (α⇐ˢ {A = a ⊗₀ˢ b₁} {b₂} {c}
        ∘ˢ α⇐ˢ {A = a} {b₁} {b₂ ⊗₀ˢ c}
        ∘ˢ (idˢ ⊗₁ˢ α⇒ˢ {A = b₁} {b₂} {c}))
      ((α⇐ˢ {A = a} {b₁} {b₂} ⊗₁ˢ idˢ)
        ∘ˢ α⇐ˢ {A = a} {b₁ ⊗₀ˢ b₂} {c})

    -- α-naturality to align the σ₂-cell: (id{B₁} ⊗ (σ₂ ⊗ id{C}))
    --   = α⇒ ∘ ((id{B₁} ⊗ σ₂) ⊗ id{C}) ∘ α⇐   (assoc-commute).
    sl₂ : (id {A = B₁} ⊗₁ (σ₂ ⊗₁ id {A = C}))
          ≈Term α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
              ∘ ((id {A = B₁} ⊗₁ σ₂) ⊗₁ id {A = C})
              ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
    sl₂ = begin
        id ⊗₁ (σ₂ ⊗₁ id)
          ≈⟨ ≈-Term-sym idˡ ⟩
        id ∘ (id ⊗₁ (σ₂ ⊗₁ id))
          ≈⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩∘⟨refl ⟩
        (α⇒ ∘ α⇐) ∘ (id ⊗₁ (σ₂ ⊗₁ id))
          ≈⟨ assoc ⟩
        α⇒ ∘ (α⇐ ∘ (id ⊗₁ (σ₂ ⊗₁ id)))
          ≈⟨ refl⟩∘⟨ ≈-Term-sym α⇐-nat ⟩
        α⇒ ∘ (((id ⊗₁ σ₂) ⊗₁ id) ∘ α⇐)
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇒ ∘ ((id ⊗₁ σ₂) ⊗₁ id)) ∘ α⇐
          ≈⟨ assoc ⟩
        α⇒ ∘ ((id ⊗₁ σ₂) ⊗₁ id) ∘ α⇐
      ∎
      where
        -- α⇐ ∘ (id ⊗ (f ⊗ id)) ≈ ((id ⊗ f) ⊗ id) ∘ α⇐  (shared `α⇐-comm`).
        α⇐-nat : ((id {A = B₁} ⊗₁ σ₂) ⊗₁ id {A = C}) ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
                 ≈Term α⇐ {A = B₁} {B = B₂ ⊗₀ A} {C = C} ∘ (id {A = B₁} ⊗₁ (σ₂ ⊗₁ id {A = C}))
        α⇐-nat = ≈-Term-sym (α⇐-comm {h = id} {i = σ₂} {j = id})

    -- α-naturality to align the σ₁-cell: (σ₁ ⊗ id{B₂⊗C})
    --   = α⇒ ∘ ((σ₁ ⊗ id{B₂}) ⊗ id{C}) ∘ α⇐.
    sl₁ : (σ₁ ⊗₁ id {A = B₂ ⊗₀ C})
          ≈Term α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
              ∘ ((σ₁ ⊗₁ id {A = B₂}) ⊗₁ id {A = C})
              ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
    sl₁ = begin
        σ₁ ⊗₁ id {A = B₂ ⊗₀ C}
          ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym id⊗id≈id) ⟩
        σ₁ ⊗₁ (id {A = B₂} ⊗₁ id {A = C})
          ≈⟨ ≈-Term-sym idˡ ⟩
        id ∘ (σ₁ ⊗₁ (id ⊗₁ id))
          ≈⟨ (≈-Term-sym α⇒∘α⇐≈id) ⟩∘⟨refl ⟩
        (α⇒ ∘ α⇐) ∘ (σ₁ ⊗₁ (id ⊗₁ id))
          ≈⟨ assoc ⟩
        α⇒ ∘ (α⇐ ∘ (σ₁ ⊗₁ (id ⊗₁ id)))
          ≈⟨ refl⟩∘⟨ (≈-Term-sym α⇐-nat₁) ⟩
        α⇒ ∘ (((σ₁ ⊗₁ id) ⊗₁ id) ∘ α⇐)
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇒ ∘ ((σ₁ ⊗₁ id) ⊗₁ id)) ∘ α⇐
          ≈⟨ assoc ⟩
        α⇒ ∘ ((σ₁ ⊗₁ id) ⊗₁ id) ∘ α⇐
      ∎
      where
        α⇐-nat₁ : ((σ₁ ⊗₁ id {A = B₂}) ⊗₁ id {A = C}) ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
                  ≈Term α⇐ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
                      ∘ (σ₁ ⊗₁ (id {A = B₂} ⊗₁ id {A = C}))
        α⇐-nat₁ = ≈-Term-sym (α⇐-comm {h = σ₁} {i = id} {j = id})

    -- `id ⊗ (f ∘ g ∘ h) ≈ (id⊗f) ∘ (id⊗g) ∘ (id⊗h)`.
    id⊗-d : ∀ {Z Y₁ Y₂ Y₃ Y₄ : ObjTerm}
              {f : HomTerm Y₃ Y₄} {g : HomTerm Y₂ Y₃} {h : HomTerm Y₁ Y₂}
          → id {A = Z} ⊗₁ (f ∘ g ∘ h)
            ≈Term (id ⊗₁ f) ∘ (id ⊗₁ g) ∘ (id ⊗₁ h)
    id⊗-d = ≈-Term-trans
              (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl)
              (≈-Term-trans ⊗-∘-dist
                (refl⟩∘⟨ (≈-Term-trans (⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl) ⊗-∘-dist)))

    rhs≈nf : α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
               ∘ (id {A = B₁} ⊗₁ σ-block {A} {B₂} {C})
               ∘ σ-block {A} {B₁} {B₂ ⊗₀ C}
               ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
             ≈Term nf
    rhs≈nf = begin
        -- expand `id ⊗ σ-block{A}{B₂}{C}` and `σ-block{A}{B₁}{B₂⊗C}`.
        α⇐ ∘ (id {A = B₁} ⊗₁ σ-block {A} {B₂} {C})
          ∘ σ-block {A} {B₁} {B₂ ⊗₀ C}
          ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
          ≈⟨ refl⟩∘⟨ (id⊗-d ⟩∘⟨refl) ⟩
        α⇐
          ∘ ((id ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
              ∘ (id ⊗₁ (σ₂ ⊗₁ id {A = C}))
              ∘ (id ⊗₁ α⇐ {A = A} {B = B₂} {C = C}))
          ∘ (α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
              ∘ (σ₁ ⊗₁ id {A = B₂ ⊗₀ C})
              ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C})
          ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
          -- substitute sl₂ and sl₁ for the two braid cells.
          ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (sl₂ ⟩∘⟨refl)) ⟩∘⟨ ((refl⟩∘⟨ (sl₁ ⟩∘⟨refl)) ⟩∘⟨refl)) ⟩
        α⇐
          ∘ ((id ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
              ∘ (α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
                  ∘ ((id ⊗₁ σ₂) ⊗₁ id)
                  ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C})
              ∘ (id ⊗₁ α⇐ {A = A} {B = B₂} {C = C}))
          ∘ (α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
              ∘ (α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
                  ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
                  ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C})
              ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C})
          ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
          -- flatten into a single right-associated chain.
          ≈⟨ flatten ⟩
        α⇐
          ∘ (id ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
          ∘ α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
          ∘ ((id ⊗₁ σ₂) ⊗₁ id)
          ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
          ∘ (id ⊗₁ α⇐ {A = A} {B = B₂} {C = C})
          ∘ α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
          ∘ α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
          ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
          ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
          ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C}
          ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
          -- collapse the three pure-associator framing blocks via E1/E2/E3.
          ≈⟨ collapse ⟩
        nf
      ∎
      where
        -- regroup the doubly-nested form into a flat right-associated chain.
        flatten
          : α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
              ∘ ((id ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
                  ∘ (α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
                      ∘ ((id ⊗₁ σ₂) ⊗₁ id)
                      ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C})
                  ∘ (id ⊗₁ α⇐ {A = A} {B = B₂} {C = C}))
              ∘ (α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
                  ∘ (α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
                      ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
                      ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C})
                  ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C})
              ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
            ≈Term
            α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
              ∘ (id ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
              ∘ α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
              ∘ ((id ⊗₁ σ₂) ⊗₁ id)
              ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
              ∘ (id ⊗₁ α⇐ {A = A} {B = B₂} {C = C})
              ∘ α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
              ∘ α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
              ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
              ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
              ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C}
              ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
        flatten = begin
            p0 ∘ ((p1 ∘ ((p2 ∘ (p3 ∘ p4)) ∘ p5)) ∘ ((p6 ∘ ((p7 ∘ (p8 ∘ p9)) ∘ p10)) ∘ p11))
              -- flatten the B₂ group `p1 ∘ ((p2∘(p3∘p4))∘p5)`.
              ≈⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (((p2 ∘ (p3 ∘ p4)) ∘ p5) ∘ Xt))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ ((p2 ∘ (p3 ∘ p4)) ∘ (p5 ∘ Xt)))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (p2 ∘ ((p3 ∘ p4) ∘ (p5 ∘ Xt))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (p2 ∘ (p3 ∘ (p4 ∘ (p5 ∘ Xt)))))
              -- now flatten `X = (p6 ∘ ((p7∘(p8∘p9))∘p10)) ∘ p11`.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (p2 ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (((p7 ∘ (p8 ∘ p9)) ∘ p10) ∘ p11)))))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (p2 ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ ((p7 ∘ (p8 ∘ p9)) ∘ (p10 ∘ p11))))))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (p2 ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ ((p8 ∘ p9) ∘ (p10 ∘ p11)))))))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
            p0 ∘ (p1 ∘ (p2 ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))))))
          ∎
          where
            p0  = α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
            p1  = id {A = B₁} ⊗₁ α⇒ {A = B₂} {B = A} {C = C}
            p2  = α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
            p3  = (id {A = B₁} ⊗₁ σ₂) ⊗₁ id {A = C}
            p4  = α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
            p5  = id {A = B₁} ⊗₁ α⇐ {A = A} {B = B₂} {C = C}
            p6  = α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
            p7  = α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
            p8  = (σ₁ ⊗₁ id {A = B₂}) ⊗₁ id {A = C}
            p9  = α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
            p10 = α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C}
            p11 = id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C}
            Xt  = (p6 ∘ ((p7 ∘ (p8 ∘ p9)) ∘ p10)) ∘ p11

        collapse
          : α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
              ∘ (id ⊗₁ α⇒ {A = B₂} {B = A} {C = C})
              ∘ α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
              ∘ ((id ⊗₁ σ₂) ⊗₁ id)
              ∘ α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
              ∘ (id ⊗₁ α⇐ {A = A} {B = B₂} {C = C})
              ∘ α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
              ∘ α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
              ∘ ((σ₁ ⊗₁ id) ⊗₁ id)
              ∘ α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
              ∘ α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C}
              ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
            ≈Term nf
        collapse = begin
            p0 ∘ (p1 ∘ (p2 ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))))))
              -- group head triple (p0 ∘ p1 ∘ p2) and apply E1.
              ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
            p0 ∘ ((p1 ∘ p2) ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11)))))))))
              ≈⟨ ≈-Term-sym assoc ⟩
            (p0 ∘ (p1 ∘ p2)) ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))))
              ≈⟨ E1 ⟩∘⟨refl ⟩
            (n0 ∘ n1) ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))))
              ≈⟨ assoc ⟩
            n0 ∘ (n1 ∘ (p3 ∘ (p4 ∘ (p5 ∘ (p6 ∘ (p7 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11)))))))))
              -- navigate under n0, n1, p3(=n2) and group quad (p4 ∘ p5 ∘ p6 ∘ p7).
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨
                   (refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym assoc)) ⟩
            n0 ∘ (n1 ∘ (p3 ∘ (p4 ∘ (p5 ∘ ((p6 ∘ p7) ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym assoc) ⟩
            n0 ∘ (n1 ∘ (p3 ∘ (p4 ∘ ((p5 ∘ (p6 ∘ p7)) ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11)))))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
            n0 ∘ (n1 ∘ (p3 ∘ ((p4 ∘ (p5 ∘ (p6 ∘ p7))) ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (E2 ⟩∘⟨refl) ⟩
            n0 ∘ (n1 ∘ (p3 ∘ (n3 ∘ (p8 ∘ (p9 ∘ (p10 ∘ p11))))))
              -- navigate under n3, p8(=n4); group tail triple (p9 ∘ p10 ∘ p11) and apply E3.
              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ E3 ⟩
            nf
          ∎
          where
            p0  = α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
            p1  = id {A = B₁} ⊗₁ α⇒ {A = B₂} {B = A} {C = C}
            p2  = α⇒ {A = B₁} {B = B₂ ⊗₀ A} {C = C}
            p3  = (id {A = B₁} ⊗₁ σ₂) ⊗₁ id {A = C}
            p4  = α⇐ {A = B₁} {B = A ⊗₀ B₂} {C = C}
            p5  = id {A = B₁} ⊗₁ α⇐ {A = A} {B = B₂} {C = C}
            p6  = α⇒ {A = B₁} {B = A} {C = B₂ ⊗₀ C}
            p7  = α⇒ {A = B₁ ⊗₀ A} {B = B₂} {C = C}
            p8  = (σ₁ ⊗₁ id {A = B₂}) ⊗₁ id {A = C}
            p9  = α⇐ {A = A ⊗₀ B₁} {B = B₂} {C = C}
            p10 = α⇐ {A = A} {B = B₁} {C = B₂ ⊗₀ C}
            p11 = id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C}
            n0  = α⇒ {A = B₁ ⊗₀ B₂} {B = A} {C = C}
            n1  = α⇐ {A = B₁} {B = B₂} {C = A} ⊗₁ id {A = C}
            n3  = α⇒ {A = B₁} {B = A} {C = B₂} ⊗₁ id {A = C}

-- The `rotate-cap` `ys = b∷ys'` step: iterate the IH past one fixed atom
-- `Vb`, assembled from `σ-block-Bmerge` (peel `Vb` off the front), the IH
-- (under `id{Vb} ⊗ _`), and `σ-block-natural₃` (slide the `to`-cap through
-- the residual `σ-block{Vx}{Vb}`).
rotate-cap-step
  : (x b : X) (ys' ts : List X)
  → _≅_.to (unflatten-++-≅ ys' (x ∷ ts)) ∘ σ-block {Var x} {unflatten ys'} {unflatten ts}
      ≈Term σ-rotate x ys' ts ∘ (id {A = Var x} ⊗₁ _≅_.to (unflatten-++-≅ ys' ts))
  → _≅_.to (unflatten-++-≅ (b ∷ ys') (x ∷ ts))
      ∘ σ-block {Var x} {unflatten (b ∷ ys')} {unflatten ts}
    ≈Term σ-rotate x (b ∷ ys') ts ∘ (id {A = Var x} ⊗₁ _≅_.to (unflatten-++-≅ (b ∷ ys') ts))
rotate-cap-step x b ys' ts ih = begin
    to-cons ∘ σ-block {Vx} {Vb ⊗₀ Uys'} {Uts}
      ≈⟨ refl⟩∘⟨ σ-block-Bmerge ⟩
    to-cons ∘ (α⇐ ∘ (id ⊗₁ σ-block {Vx} {Uys'} {Uts}) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒'))
      ≈⟨ pull-cap ⟩
    (id {A = Vb} ⊗₁ (to' ∘ σ-block {Vx} {Uys'} {Uts}))
      ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ (⊗-resp-≈ ≈-Term-refl ih) ⟩∘⟨refl ⟩
    (id {A = Vb} ⊗₁ (σ-rotate x ys' ts ∘ (id {A = Vx} ⊗₁ toxs)))
      ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩∘⟨refl ⟩
    ((id {A = Vb} ∘ id {A = Vb}) ⊗₁ (σ-rotate x ys' ts ∘ (id {A = Vx} ⊗₁ toxs)))
      ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
    ((id {A = Vb} ⊗₁ σ-rotate x ys' ts) ∘ (id {A = Vb} ⊗₁ (id {A = Vx} ⊗₁ toxs)))
      ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ regroup ⟩
    (id {A = Vb} ⊗₁ σ-rotate x ys' ts)
      ∘ ((id {A = Vb} ⊗₁ (id {A = Vx} ⊗₁ toxs)) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts})
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ refl⟩∘⟨ (≈-Term-sym σ-block-natural₃ ⟩∘⟨refl) ⟩
    (id {A = Vb} ⊗₁ σ-rotate x ys' ts)
      ∘ (σ-block {Vx} {Vb} {U-yt} ∘ (id {A = Vx} ⊗₁ (id {A = Vb} ⊗₁ toxs)))
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ regroup2 ⟩
    σ-rotate x (b ∷ ys') ts ∘ (id {A = Vx} ⊗₁ to-bys'-ts)
  ∎
  where
    Vx = Var x
    Vb = Var b
    Uys' = unflatten ys'
    Uts = unflatten ts
    U-yt = unflatten (ys' ++ ts)
    α⇒' = α⇒ {A = Vb} {B = Uys'} {C = Uts}
    to' = _≅_.to (unflatten-++-≅ ys' (x ∷ ts))
    toxs = _≅_.to (unflatten-++-≅ ys' ts)
    to-cons = _≅_.to (unflatten-++-≅ (b ∷ ys') (x ∷ ts))
    to-bys'-ts = _≅_.to (unflatten-++-≅ (b ∷ ys') ts)

    pull-cap
      : to-cons ∘ (α⇐ ∘ (id ⊗₁ σ-block {Vx} {Uys'} {Uts}) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒'))
        ≈Term (id {A = Vb} ⊗₁ (to' ∘ σ-block {Vx} {Uys'} {Uts}))
                ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
                ∘ (id {A = Vx} ⊗₁ α⇒')
    pull-cap = begin
        to-cons ∘ (α⇐ ∘ (id ⊗₁ σ-block {Vx} {Uys'} {Uts}) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒'))
          ≈⟨ ≈-Term-sym assoc ⟩
        (to-cons ∘ α⇐) ∘ ((id ⊗₁ σ-block {Vx} {Uys'} {Uts}) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒'))
          ≈⟨ cap-collapse ⟩∘⟨refl ⟩
        (id {A = Vb} ⊗₁ to') ∘ ((id ⊗₁ σ-block {Vx} {Uys'} {Uts}) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒'))
          ≈⟨ ≈-Term-sym assoc ⟩
        ((id {A = Vb} ⊗₁ to') ∘ (id ⊗₁ σ-block {Vx} {Uys'} {Uts})) ∘ (σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒'))
          ≈⟨ (≈-Term-sym ⊗-∘-dist ⟨≈≈⟩ ⊗-resp-≈ idˡ ≈-Term-refl) ⟩∘⟨refl ⟩
        (id {A = Vb} ⊗₁ (to' ∘ σ-block {Vx} {Uys'} {Uts})) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts} ∘ (id ⊗₁ α⇒')
      ∎
      where
        cap-collapse : to-cons ∘ α⇐ {A = Vb} {B = Uys'} {C = Vx ⊗₀ Uts} ≈Term id {A = Vb} ⊗₁ to'
        cap-collapse = begin
            ((id ⊗₁ to') ∘ α⇒) ∘ α⇐
              ≈⟨ assoc ⟩
            (id ⊗₁ to') ∘ (α⇒ ∘ α⇐)
              ≈⟨ refl⟩∘⟨ α⇒∘α⇐≈id ⟩
            (id ⊗₁ to') ∘ id
              ≈⟨ idʳ ⟩
            id {A = Vb} ⊗₁ to'
          ∎

    regroup
      : ((id {A = Vb} ⊗₁ σ-rotate x ys' ts) ∘ (id {A = Vb} ⊗₁ (id {A = Vx} ⊗₁ toxs)))
          ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
          ∘ (id {A = Vx} ⊗₁ α⇒')
        ≈Term (id {A = Vb} ⊗₁ σ-rotate x ys' ts)
                ∘ ((id {A = Vb} ⊗₁ (id {A = Vx} ⊗₁ toxs)) ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts})
                ∘ (id {A = Vx} ⊗₁ α⇒')
    regroup = begin
        (idσr ∘ idid) ∘ sb ∘ idα   ≈⟨ assoc ⟩
        idσr ∘ (idid ∘ sb ∘ idα)   ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
        idσr ∘ (idid ∘ sb) ∘ idα   ∎
      where
        idσr = id {A = Vb} ⊗₁ σ-rotate x ys' ts
        idid = id {A = Vb} ⊗₁ (id {A = Vx} ⊗₁ toxs)
        sb   = σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
        idα  = id {A = Vx} ⊗₁ α⇒'

    regroup2
      : (id {A = Vb} ⊗₁ σ-rotate x ys' ts)
          ∘ (σ-block {Vx} {Vb} {U-yt} ∘ (id {A = Vx} ⊗₁ (id {A = Vb} ⊗₁ toxs)))
          ∘ (id {A = Vx} ⊗₁ α⇒')
        ≈Term σ-rotate x (b ∷ ys') ts ∘ (id {A = Vx} ⊗₁ to-bys'-ts)
    regroup2 = begin
        idσr ∘ (sb ∘ idid2) ∘ idα
          ≈⟨ refl⟩∘⟨ assoc ⟩
        idσr ∘ sb ∘ (idid2 ∘ idα)
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist) ⟩
        idσr ∘ sb ∘ ((id {A = Vx} ∘ id {A = Vx}) ⊗₁ ((id {A = Vb} ⊗₁ toxs) ∘ α⇒'))
          ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl) ⟩
        idσr ∘ sb ∘ (id {A = Vx} ⊗₁ ((id {A = Vb} ⊗₁ toxs) ∘ α⇒'))
          ≈⟨ ≈-Term-sym assoc ⟩
        (idσr ∘ sb) ∘ (id {A = Vx} ⊗₁ to-bys'-ts)
      ∎
      where
        idσr = id {A = Vb} ⊗₁ σ-rotate x ys' ts
        idid2 = id {A = Vx} ⊗₁ (id {A = Vb} ⊗₁ toxs)
        sb   = σ-block {Vx} {Vb} {U-yt}
        idα  = id {A = Vx} ⊗₁ α⇒'

rotate-cap
  : (x : X) (ys ts : List X)
  → _≅_.to (unflatten-++-≅ ys (x ∷ ts))
      ∘ σ-block {Var x} {unflatten ys} {unflatten ts}
    ≈Term σ-rotate x ys ts ∘ (id {A = Var x} ⊗₁ _≅_.to (unflatten-++-≅ ys ts))
rotate-cap x []        ts = begin
    λ⇒ ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
      ≈⟨ ≈-Term-sym assoc ⟩
    (λ⇒ ∘ α⇒) ∘ ((σ ⊗₁ id) ∘ α⇐)
      ≈⟨ ∘-resp-≈ coherence₁ ≈-Term-refl ⟩
    (λ⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ∘ α⇐)
      ≈⟨ ≈-Term-sym assoc ⟩
    ((λ⇒ ⊗₁ id) ∘ (σ ⊗₁ id)) ∘ α⇐
      ≈⟨ ∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl ⟩
    ((λ⇒ ∘ σ) ⊗₁ (id ∘ id)) ∘ α⇐
      ≈⟨ ∘-resp-≈ (⊗-resp-≈ braiding-coherence idˡ) ≈-Term-refl ⟩
    (ρ⇒ ⊗₁ id) ∘ α⇐
      ≈⟨ ∘-resp-≈ (≈-Term-sym triangle) ≈-Term-refl ⟩
    (id ⊗₁ λ⇒ ∘ α⇒) ∘ α⇐
      ≈⟨ assoc ⟩
    (id ⊗₁ λ⇒) ∘ (α⇒ ∘ α⇐)
      ≈⟨ ∘-resp-≈ ≈-Term-refl α⇒∘α⇐≈id ⟩
    (id ⊗₁ λ⇒) ∘ id
      ≈⟨ idʳ ⟩
    id ⊗₁ λ⇒
      ≈⟨ ≈-Term-sym idˡ ⟩
    id ∘ (id ⊗₁ λ⇒)
  ∎
rotate-cap x (b ∷ ys') ts = rotate-cap-step x b ys' ts (rotate-cap x ys' ts)

--------------------------------------------------------------------------------
-- ## `xs=[]` base case: braiding the EMPTY moving block.  `σ{unit}{Uys} ∘
-- from(uf++ [] ys) ≈ ρ⇐` (braiding with unit), and `to(uf++ ys []) ∘ ρ⇐ ≈
-- permute(++-comm [] ys)` is the right-unit coherence (`rid-subst`), with
-- `permute(++-comm [] ys)` recognised as the transported identity.

permute-↭-sym-refl
  : ∀ {as bs : List X} (e : as ≡ bs)
  → permute (Perm.↭-sym (Perm.↭-reflexive e))
    ≡ subst₂ HomTerm refl (cong unflatten (sym e)) (id {A = unflatten bs})
permute-↭-sym-refl refl = refl

-- the right-unit coherence at the `≈Term` level, by induction on `ys`.
rid-subst
  : (ys : List X)
  → _≅_.to (unflatten-++-≅ ys []) ∘ ρ⇐ {A = unflatten ys}
    ≈Term subst₂ HomTerm refl (cong unflatten (sym (LP.++-identityʳ ys)))
            (id {A = unflatten ys})
rid-subst []        = begin
    λ⇒ ∘ ρ⇐  ≈⟨ ∘-resp-≈ coherence₃ ≈-Term-refl ⟩
    ρ⇒ ∘ ρ⇐  ≈⟨ ρ⇒∘ρ⇐≈id ⟩
    id       ∎
rid-subst (c ∷ ys') = begin
    ((id ⊗₁ to') ∘ α⇒) ∘ ρ⇐
      ≈⟨ assoc ⟩
    (id ⊗₁ to') ∘ (α⇒ ∘ ρ⇐)
      ≈⟨ refl⟩∘⟨ αρ ⟩
    (id ⊗₁ to') ∘ (id ⊗₁ ρ⇐)
      ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
    (id ∘ id) ⊗₁ (to' ∘ ρ⇐)
      ≈⟨ ⊗-resp-≈ idˡ (rid-subst ys') ⟩
    id {A = Var c} ⊗₁ subst₂ HomTerm refl (cong unflatten (sym e')) (id {A = unflatten ys'})
      ≈⟨ ≈-Term-sym (subst-push c e') ⟩
    subst₂ HomTerm refl (cong unflatten (sym (cong (c ∷_) e'))) (id {A = unflatten (c ∷ ys')})
  ∎
  where
    to' = _≅_.to (unflatten-++-≅ ys' [])
    e' = LP.++-identityʳ ys'
    αρ : α⇒ {A = Var c} {B = unflatten ys'} {C = unit} ∘ ρ⇐ {A = Var c ⊗₀ unflatten ys'}
         ≈Term id {A = Var c} ⊗₁ ρ⇐ {A = unflatten ys'}
    αρ = begin
        α⇒ ∘ ρ⇐
          ≈⟨ refl⟩∘⟨ ≈-Term-sym coherence-inv₂ ⟩
        α⇒ ∘ (α⇐ ∘ (id ⊗₁ ρ⇐))
          ≈⟨ ≈-Term-sym assoc ⟩
        (α⇒ ∘ α⇐) ∘ (id ⊗₁ ρ⇐)
          ≈⟨ α⇒∘α⇐≈id ⟩∘⟨refl ⟩
        id ∘ (id ⊗₁ ρ⇐)
          ≈⟨ idˡ ⟩
        id ⊗₁ ρ⇐
      ∎
    subst-push
      : ∀ (c : X) {as bs : List X} (e : as ≡ bs)
      → subst₂ HomTerm refl (cong unflatten (sym (cong (c ∷_) e))) (id {A = unflatten (c ∷ bs)})
        ≈Term id {A = Var c} ⊗₁ subst₂ HomTerm refl (cong unflatten (sym e)) (id {A = unflatten bs})
    subst-push c refl = ≈-Term-sym id⊗id≈id

block-comm-nil
  : (ys : List X)
  → _≅_.to (unflatten-++-≅ ys [])
      ∘ σ {A = unflatten []} {B = unflatten ys}
      ∘ _≅_.from (unflatten-++-≅ [] ys)
    ≈Term permute (PermProp.++-comm [] ys)
block-comm-nil ys = begin
    _≅_.to (unflatten-++-≅ ys [])
      ∘ σ {A = unflatten []} {B = unflatten ys}
      ∘ _≅_.from (unflatten-++-≅ [] ys)
      ≈⟨ refl⟩∘⟨ braiding-coherence-inv ⟩
    _≅_.to (unflatten-++-≅ ys []) ∘ ρ⇐
      ≈⟨ rid-subst ys ⟩
    subst₂ HomTerm refl (cong unflatten (sym (LP.++-identityʳ ys))) (id {A = unflatten ys})
      ≈⟨ ≡⇒≈Term (sym (permute-↭-sym-refl (LP.++-identityʳ ys))) ⟩
    permute (PermProp.++-comm [] ys)
  ∎

--------------------------------------------------------------------------------
-- ## THE GOAL.  Induction on `xs`.

σ-block-comm-raw
  : (xs ys : List X)
  → _≅_.to (unflatten-++-≅ ys xs)
      ∘ σ {A = unflatten xs} {B = unflatten ys}
      ∘ _≅_.from (unflatten-++-≅ xs ys)
    ≈Term permute (PermProp.++-comm xs ys)
σ-block-comm-raw []         ys = block-comm-nil ys
σ-block-comm-raw (x ∷ xs') ys = begin
    to-cons ∘ (σ {A = Vx ⊗₀ Uxs'} {B = Uys} ∘ fromcons)
      ≈⟨ refl⟩∘⟨ peel x xs' ys ⟩
    to-cons ∘ (σ-block {Vx} {Uys} {Uxs'} ∘ (id {A = Vx} ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs)))
      ≈⟨ ≈-Term-sym assoc ⟩
    (to-cons ∘ σ-block {Vx} {Uys} {Uxs'}) ∘ (id {A = Vx} ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs))
      ≈⟨ rotate-cap x ys xs' ⟩∘⟨refl ⟩
    (σ-rotate x ys xs' ∘ (id {A = Vx} ⊗₁ toxs)) ∘ (id {A = Vx} ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs))
      ≈⟨ assoc ⟩
    σ-rotate x ys xs' ∘ ((id {A = Vx} ⊗₁ toxs) ∘ (id {A = Vx} ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs)))
      ≈⟨ refl⟩∘⟨ ≈-Term-sym ⊗-∘-dist ⟩
    σ-rotate x ys xs' ∘ ((id ∘ id) ⊗₁ (toxs ∘ (σ {A = Uxs'} {B = Uys} ∘ fromxs)))
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ idˡ ≈-Term-refl ⟩
    σ-rotate x ys xs' ∘ (id {A = Vx} ⊗₁ (toxs ∘ σ {A = Uxs'} {B = Uys} ∘ fromxs))
      ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl (σ-block-comm-raw xs' ys) ⟩
    σ-rotate x ys xs' ∘ (id {A = Vx} ⊗₁ permute (PermProp.++-comm xs' ys))
      ≈⟨ ≈-Term-sym (permute-comm-cons x xs' ys) ⟩
    permute (PermProp.++-comm (x ∷ xs') ys)
  ∎
  where
    Vx = Var x
    Uxs' = unflatten xs'
    Uys = unflatten ys
    fromxs = _≅_.from (unflatten-++-≅ xs' ys)
    fromcons = _≅_.from (unflatten-++-≅ (x ∷ xs') ys)
    to-cons = _≅_.to (unflatten-++-≅ ys (x ∷ xs'))
    toxs = _≅_.to (unflatten-++-≅ ys xs')
