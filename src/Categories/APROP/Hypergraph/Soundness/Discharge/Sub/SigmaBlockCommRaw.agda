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

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SigmaBlockCommRaw
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

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅; Iso)
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.SolverSigmaFrontend using (module FinSetupσ)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F)
open import Data.Product using (_,_)
import Data.Vec as Vec
open Vec using (Vec)
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

  -- `Symm ≤ Symm` for the σ-solver front-end's own free SMC (its `Sσ.σ`
  -- carries the instance argument).
  instance
    S≤S : Symm ≤ Symm
    S≤S = v≤v

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
-- past `ys` (in the `id{Var x} ⊗ _` slot).  `σ⊗-from-hexagon₂` + a σ-solver
-- step for the α-iso cancel/regroup.

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
      ≈⟨ solveMorσ! lhsᵗ rhsᵗ ⟩
    σ-block {Vx} {Uys} {Uxs'}
      ∘ (id {A = Vx} ⊗₁ (σ {A = Uxs'} {B = Uys} ∘ fromxs))
  ∎
  where
    Vx = Var x
    Uxs' = unflatten xs'
    Uys = unflatten ys
    fromxs = _≅_.from (unflatten-++-≅ xs' ys)
    fromcons = _≅_.from (unflatten-++-≅ (x ∷ xs') ys)

    -- σ-solver setup: the pure α/assoc `pull` regrouping (both sides carry
    -- the same two crossings Vx/Uys and Uxs'/Uys).
    FMC : MonoidalCategory _ _ _
    FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

    open FinSetupσ FMC Symmetric-Monoidal
      (Vx Vec.∷ Uxs' Vec.∷ Uys Vec.∷ unflatten (xs' ++ ys) Vec.∷ Vec.[])

    aX  = V 0F
    aXs = V 1F
    aYs = V 2F
    aXY = V 3F

    open Sig {1} (λ { 0F → aXY , (aXs ⊗ᵒ aYs) })   -- fromxs
      renaming (module S to Sσ)
    open WithGen (λ { (genS 0F) → fromxs })

    open Sσ using ()
      renaming (_∘_ to infixr 9 _∘ᵗ_; _⊗₁_ to infixr 10 _⊗ᵗ_)

    fromxsᵗ = gen 0F

    σXᵗ : Sσ.HomTerm (aX ⊗ᵒ aYs) (aYs ⊗ᵒ aX)
    σXᵗ = Sσ.σ
    σXsᵗ : Sσ.HomTerm (aXs ⊗ᵒ aYs) (aYs ⊗ᵒ aXs)
    σXsᵗ = Sσ.σ

    lhsᵗ rhsᵗ : Sσ.HomTerm (aX ⊗ᵒ aXY) (aYs ⊗ᵒ (aX ⊗ᵒ aXs))
    lhsᵗ = (Sσ.α⇒ ∘ᵗ ((σXᵗ ⊗ᵗ Sσ.id) ∘ᵗ Sσ.α⇐ ∘ᵗ (Sσ.id ⊗ᵗ σXsᵗ)) ∘ᵗ Sσ.α⇒)
             ∘ᵗ (Sσ.α⇐ ∘ᵗ (Sσ.id ⊗ᵗ fromxsᵗ))
    rhsᵗ = (Sσ.α⇒ ∘ᵗ (σXᵗ ⊗ᵗ Sσ.id) ∘ᵗ Sσ.α⇐)
             ∘ᵗ (Sσ.id ⊗ᵗ (σXsᵗ ∘ᵗ fromxsᵗ))

--------------------------------------------------------------------------------
-- ## `rotate-cap` — the single-atom braid / cap coherence:
--
--   to(uf++ ys (x ∷ ts)) ∘ σ-block{Var x}{unflatten ys}{unflatten ts}
--     ≈ σ-rotate x ys ts ∘ (id{Var x} ⊗ to(uf++ ys ts))
--
-- Induction on `ys`.  The `ys=[]` base is unit-braiding coherence; the
-- `ys=b∷ys'` step is the hexagon iteration (peeling `Vb` off the FRONT of
-- the fixed block).

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

-- B-slot tensor decomposition of `σ-block`: substitute `σ-Bmerge-bare` for
-- the braid cell (the genuinely hexagon-class step), then ONE σ-solver call
-- (`solveMorσ!`, zero generators, the free SMC itself as target) discharges
-- the entire α/⊗-coherence reconciliation — the old `nf`/`lhs≈nf`/`rhs≈nf`
-- cascade with its `dist`/`sl₁`/`sl₂` slides and E1-E3 `solveM` framings.
-- Decidable because both sides carry the SAME two crossings (A vs B₁ and
-- A vs B₂); only `σ{A}{B₁⊗B₂}` itself needs the hexagon, once.
σ-block-Bmerge
  : ∀ {A B₁ B₂ C : ObjTerm}
  → σ-block {A} {B₁ ⊗₀ B₂} {C}
    ≈Term α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
            ∘ (id {A = B₁} ⊗₁ σ-block {A} {B₂} {C})
            ∘ σ-block {A} {B₁} {B₂ ⊗₀ C}
            ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C})
σ-block-Bmerge {A} {B₁} {B₂} {C} = begin
    α⇒ ∘ (σ {A = A} {B = B₁ ⊗₀ B₂} ⊗₁ id {A = C}) ∘ α⇐
      ≈⟨ refl⟩∘⟨ (⊗-resp-≈ σ-Bmerge-bare ≈-Term-refl ⟩∘⟨refl) ⟩
    α⇒ ∘ ((α⇐ ∘ (id ⊗₁ σ₂) ∘ α⇒ ∘ (σ₁ ⊗₁ id) ∘ α⇐) ⊗₁ id {A = C}) ∘ α⇐
      ≈⟨ solveMorσ! lhsᵗ rhsᵗ ⟩
    α⇐ {A = B₁} {B = B₂} {C = A ⊗₀ C}
      ∘ (id {A = B₁} ⊗₁ σ-block {A} {B₂} {C})
      ∘ σ-block {A} {B₁} {B₂ ⊗₀ C}
      ∘ (id {A = A} ⊗₁ α⇒ {A = B₁} {B = B₂} {C = C}) ∎
  where
    σ₁ = σ {A = A} {B = B₁}
    σ₂ = σ {A = A} {B = B₂}

    FMC : MonoidalCategory _ _ _
    FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

    open FinSetupσ FMC Symmetric-Monoidal (B₁ Vec.∷ B₂ Vec.∷ A Vec.∷ C Vec.∷ Vec.[])

    b₁ᵃ = V 0F
    b₂ᵃ = V 1F
    aᵃ  = V 2F
    cᵃ  = V 3F

    open Sig {0} (λ ()) renaming (module S to Sσ)
    open WithGen (λ { (genS ()) })

    open Sσ using ()
      renaming (_∘_ to infixr 9 _∘ᵗ_; _⊗₁_ to infixr 10 _⊗ᵗ_)

    -- `σ-block` at the term level, objects pinned through the signature.
    sbᵗ : ∀ P Q R → Sσ.HomTerm (P ⊗ᵒ (Q ⊗ᵒ R)) (Q ⊗ᵒ (P ⊗ᵒ R))
    sbᵗ P Q R = Sσ.α⇒ ∘ᵗ (Sσ.σ ⊗ᵗ Sσ.id) ∘ᵗ Sσ.α⇐

    σ₁ᵗ : Sσ.HomTerm (aᵃ ⊗ᵒ b₁ᵃ) (b₁ᵃ ⊗ᵒ aᵃ)
    σ₁ᵗ = Sσ.σ
    σ₂ᵗ : Sσ.HomTerm (aᵃ ⊗ᵒ b₂ᵃ) (b₂ᵃ ⊗ᵒ aᵃ)
    σ₂ᵗ = Sσ.σ
    idᶜᵗ : Sσ.HomTerm cᵃ cᵃ
    idᶜᵗ = Sσ.id

    -- the σ-Bmerge-bare RHS cell, term-side.
    bareᵗ : Sσ.HomTerm (aᵃ ⊗ᵒ (b₁ᵃ ⊗ᵒ b₂ᵃ)) ((b₁ᵃ ⊗ᵒ b₂ᵃ) ⊗ᵒ aᵃ)
    bareᵗ = Sσ.α⇐ ∘ᵗ (Sσ.id ⊗ᵗ σ₂ᵗ) ∘ᵗ Sσ.α⇒ ∘ᵗ (σ₁ᵗ ⊗ᵗ Sσ.id) ∘ᵗ Sσ.α⇐

    lhsᵗ rhsᵗ : Sσ.HomTerm (aᵃ ⊗ᵒ ((b₁ᵃ ⊗ᵒ b₂ᵃ) ⊗ᵒ cᵃ))
                           ((b₁ᵃ ⊗ᵒ b₂ᵃ) ⊗ᵒ (aᵃ ⊗ᵒ cᵃ))
    lhsᵗ = Sσ.α⇒ ∘ᵗ (bareᵗ ⊗ᵗ idᶜᵗ) ∘ᵗ Sσ.α⇐
    rhsᵗ = Sσ.α⇐
             ∘ᵗ (Sσ.id ⊗ᵗ sbᵗ aᵃ b₂ᵃ cᵃ)
             ∘ᵗ sbᵗ aᵃ b₁ᵃ (b₂ᵃ ⊗ᵒ cᵃ)
             ∘ᵗ (Sσ.id ⊗ᵗ Sσ.α⇒ {A = b₁ᵃ} {b₂ᵃ} {cᵃ})

-- The `rotate-cap` `ys = b∷ys'` step: iterate the IH past one fixed atom
-- `Vb`, assembled from `σ-block-Bmerge` (peel `Vb` off the front) and the IH
-- (under `id{Vb} ⊗ _`); the α-coherence glue and the cap-slide through the
-- residual `σ-block{Vx}{Vb}` (the old `σ-block-natural₃`) are σ-solver steps.
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
      ≈⟨ solveMorσ! pullᵗ groupᵗ ⟩
    (id {A = Vb} ⊗₁ (to' ∘ σ-block {Vx} {Uys'} {Uts}))
      ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ (⊗-resp-≈ ≈-Term-refl ih) ⟩∘⟨refl ⟩
    (id {A = Vb} ⊗₁ (σ-rotate x ys' ts ∘ (id {A = Vx} ⊗₁ toxs)))
      ∘ σ-block {Vx} {Vb} {Uys' ⊗₀ Uts}
      ∘ (id {A = Vx} ⊗₁ α⇒')
      ≈⟨ solveMorσ! slideᵗ capᵗ ⟩
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

    ------------------------------------------------------------------
    -- σ-solver setup: the two solver steps replace the old `pull-cap`/
    -- `cap-collapse`/`regroup`/`regroup2` α-coherence glue AND the
    -- `σ-block-natural₃` cap-slide (the `toxs` box through the FIXED
    -- crossing σ{Vx}{Vb} is inside the decidable fragment).  `to-cons`,
    -- `to-bys'-ts` and `σ-rotate x (b ∷ ys') ts` unfold definitionally
    -- into the atoms/generators below.
    FMC : MonoidalCategory _ _ _
    FMC = record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal }

    open FinSetupσ FMC Symmetric-Monoidal
      (Vx Vec.∷ Vb Vec.∷ Uys' Vec.∷ Uts Vec.∷ U-yt Vec.∷
       unflatten (ys' ++ (x ∷ ts)) Vec.∷ Vec.[])

    aX   = V 0F
    aB   = V 1F
    aYs  = V 2F
    aTs  = V 3F
    aYT  = V 4F
    aYXT = V 5F

    open Sig {3} (λ { 0F → (aYs ⊗ᵒ (aX ⊗ᵒ aTs)) , aYXT   -- to'
                    ; 1F → (aYs ⊗ᵒ aTs) , aYT            -- toxs
                    ; 2F → (aX ⊗ᵒ aYT) , aYXT })         -- σ-rotate x ys' ts
      renaming (module S to Sσ)

    open WithGen (λ { (genS 0F) → to'
                    ; (genS 1F) → toxs
                    ; (genS 2F) → σ-rotate x ys' ts })

    open Sσ using ()
      renaming (_∘_ to infixr 9 _∘ᵗ_; _⊗₁_ to infixr 10 _⊗ᵗ_)

    to'ᵗ  = gen 0F
    toxsᵗ = gen 1F
    σrᵗ   = gen 2F

    sbᵗ : ∀ P Q R → Sσ.HomTerm (P ⊗ᵒ (Q ⊗ᵒ R)) (Q ⊗ᵒ (P ⊗ᵒ R))
    sbᵗ P Q R = Sσ.α⇒ ∘ᵗ (Sσ.σ ⊗ᵗ Sσ.id) ∘ᵗ Sσ.α⇐

    idXᵗ : Sσ.HomTerm aX aX
    idXᵗ = Sσ.id
    idBᵗ : Sσ.HomTerm aB aB
    idBᵗ = Sσ.id
    α⇒'ᵗ : Sσ.HomTerm ((aB ⊗ᵒ aYs) ⊗ᵒ aTs) (aB ⊗ᵒ (aYs ⊗ᵒ aTs))
    α⇒'ᵗ = Sσ.α⇒
    to-consᵗ : Sσ.HomTerm ((aB ⊗ᵒ aYs) ⊗ᵒ (aX ⊗ᵒ aTs)) (aB ⊗ᵒ aYXT)
    to-consᵗ = (idBᵗ ⊗ᵗ to'ᵗ) ∘ᵗ Sσ.α⇒

    pullᵗ groupᵗ slideᵗ capᵗ
      : Sσ.HomTerm (aX ⊗ᵒ ((aB ⊗ᵒ aYs) ⊗ᵒ aTs)) (aB ⊗ᵒ aYXT)
    pullᵗ = to-consᵗ
              ∘ᵗ (Sσ.α⇐
                  ∘ᵗ (idBᵗ ⊗ᵗ sbᵗ aX aYs aTs)
                  ∘ᵗ sbᵗ aX aB (aYs ⊗ᵒ aTs)
                  ∘ᵗ (idXᵗ ⊗ᵗ α⇒'ᵗ))
    groupᵗ = (idBᵗ ⊗ᵗ (to'ᵗ ∘ᵗ sbᵗ aX aYs aTs))
               ∘ᵗ sbᵗ aX aB (aYs ⊗ᵒ aTs)
               ∘ᵗ (idXᵗ ⊗ᵗ α⇒'ᵗ)
    slideᵗ = (idBᵗ ⊗ᵗ (σrᵗ ∘ᵗ (idXᵗ ⊗ᵗ toxsᵗ)))
               ∘ᵗ sbᵗ aX aB (aYs ⊗ᵒ aTs)
               ∘ᵗ (idXᵗ ⊗ᵗ α⇒'ᵗ)
    capᵗ = ((idBᵗ ⊗ᵗ σrᵗ) ∘ᵗ sbᵗ aX aB aYT)
             ∘ᵗ (idXᵗ ⊗ᵗ ((idBᵗ ⊗ᵗ toxsᵗ) ∘ᵗ α⇒'ᵗ))

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
