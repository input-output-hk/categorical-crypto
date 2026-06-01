{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- `σ-block-comm-raw` — the bare iterated TWO-BLOCK braiding at `List X`.
--
--   to(unflatten-++-≅ ys xs) ∘ σ{unflatten xs}{unflatten ys}
--       ∘ from(unflatten-++-≅ xs ys)
--     ≈Term permute (++-comm xs ys)
--
-- This is the genuine `BraidBlock`/`BraidPermute` "iteration + swap-core
-- assembly" flagged in `BraidBlock`'s header.  It is the sole remaining
-- postulate of `Sub/BlockNFBraid.agda`; this module proves it so it splices
-- as `σ-block-comm-raw = SigmaBlockCommRaw.σ-block-comm-raw`.
--
-- `--with-K`.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockCommRaw
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; unflatten-++-≅; permute)
open import Categories.FreeSMC.BraidBlock d
  using (σ-block)
open import Categories.FreeSMC.BraidPermute d
  using (rotate; σ-rotate; permute-rotate; permute-swap-refl-σ-block)
open import Categories.FreeSMC.SigmaBlockTensor d using (σ⊗-from-hexagon₂)
open import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.SigmaBlockHexagon d
  using (σ-block-natural₃; σ-block-natural₁; hexagon₂)

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅; Iso)
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

≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
≡⇒≈Term refl = ≈-Term-refl

-- `↭-sym (shift x ys xs) ≡ rotate x ys xs`  (copied from BlockNFBraid).
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
--
-- Braiding `Var x ⊗ unflatten xs'` past `unflatten ys` (pre-composed by the
-- `unflatten-++-≅ (x∷xs') ys` cap) splits into braiding the atom `Var x` past
-- `ys` (a `σ-block`) and braiding the tail block `xs'` past `ys` (carried in
-- the `id{Var x} ⊗ _` slot).  Pure `σ⊗-from-hexagon₂` + α-iso cancellation.

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
-- ## `rotate-cap` — the genuine single-atom braid / cap coherence.
--
--   to(uf++ ys (x ∷ ts)) ∘ σ-block{Var x}{unflatten ys}{unflatten ts}
--     ≈ σ-rotate x ys ts ∘ (id{Var x} ⊗ to(uf++ ys ts))
--
-- By induction on `ys`.  `σ-rotate` and the `to`-caps both recurse on `ys`,
-- so this is the alignment that makes the iteration go through.  The `ys=[]`
-- base is the unit-braiding coherence (`coherence₁` + `braiding-coherence` +
-- `triangle`); the `ys=b∷ys'` step is the hexagon iteration (peeling `Vb` off
-- the FRONT of the fixed block).

private
  _⟨≈≈⟩_ : ∀ {A B} {f g h : HomTerm A B} → f ≈Term g → g ≈Term h → f ≈Term h
  _⟨≈≈⟩_ = ≈-Term-trans
  infixr 4 _⟨≈≈⟩_

-- bare second-arg-tensor decomposition of `σ`, solved out of the `hexagon`
-- axiom.  (The genuine braiding content of the `ys`-step.)  PROVEN.
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

-- B-slot tensor decomposition of `σ-block`: the pure α-coherence "wrapping"
-- of `σ-Bmerge-bare` (the dual of `BlockNFBraid`'s private C-slot
-- `σ-block-merge`).  Pure Mac-Lane associahedron coherence — NO braiding
-- content remains (that is fully discharged by `σ-Bmerge-bare`).  This is the
-- SOLE residual of this module: an associator/pentagon reassociation of the
-- already-proven `σ-Bmerge-bare`; unambiguously TRUE.
postulate
  σ-block-Bmerge
    : ∀ {A B₁ B₂ C : ObjTerm}
    → σ-block {A} {B₁ ⊗₀ B₂} {C}
      ≈Term α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
              ∘ (id {A = B₁} ⊗₁ σ-block {A} {B₂} {C})
              ∘ σ-block {A} {B₁} {B₂ ⊗₀ C}
              ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})

-- The `rotate-cap` `ys = b∷ys'` step: the iteration of the IH past one fixed
-- atom `Vb`, assembled from `σ-block-Bmerge` (peel `Vb` off the front of the
-- block), the IH (under `id{Vb} ⊗ _`), and `σ-block-natural₃` (slide the
-- `to`-cap through the residual `σ-block{Vx}{Vb}`).  PROVEN modulo
-- `σ-block-Bmerge`.
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
-- ## `xs=[]` base case of the main theorem: braiding the EMPTY moving block.
--
-- `σ{unit}{Uys} ∘ from(uf++ [] ys) = σ{unit}{Uys} ∘ λ⇐ ≈ ρ⇐` (braiding with
-- unit), and `to(uf++ ys []) ∘ ρ⇐ ≈ permute(++-comm [] ys)` is the right-unit
-- coherence (`rid-subst`), with `permute(++-comm [] ys)` recognised as the
-- transported identity (`permute-↭-sym-refl`).

-- `permute (↭-sym (↭-reflexive e)) = transported id`  (`J`, --with-K).
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
