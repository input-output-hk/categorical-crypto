{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The block-σ ↔ atom-`permute` bridge (heart of `swap-core`).
--
-- This module connects the two worlds the `swap-core` slide must span:
--   * `BraidBlock.σ-block` / `braid` — block braiding at the `ObjTerm`
--     level (where the generator-slide lemma `braid-natural` lives), and
--   * `permute` — the atom-level realisation of a list permutation
--     (where `permute-faithfulness` lives).
--
-- The ATOMIC identity proved here, `permute-swap-refl-σ-block`, is the
-- per-adjacent-transposition core: `permute` of a single front swap is
-- exactly `σ-block` on the two front atoms.  The full bridge (a generator
-- block sliding past an atom-`permute`) iterates this together with
-- `braid-natural`; that iteration + the `swap-core` assembly is the
-- remaining dedicated work.
--
-- `--safe`.  No postulates.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.BraidPermute
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d
open import Categories.FreeSMC.Steps d using (permute; unflatten)
open import Categories.FreeSMC.BraidBlock d using (σ-block)

open import Categories.Category using (Category)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## Atomic identity: `permute` of one front swap = `σ-block`.
--
-- `permute (swap x y refl)` unfolds (by the definition of `permute`) to
-- `(id ⊗ (id ⊗ id)) ∘ α⇒ ∘ (σ ⊗ id) ∘ α⇐`, and the leading `id`-tensor
-- collapses, leaving exactly `σ-block {Var x} {Var y} {unflatten xs}`.

permute-swap-refl-σ-block
  : ∀ {x y : X} {xs : List X}
  → permute (Perm.swap x y (Perm.refl {xs = xs}))
    ≈Term σ-block {Var x} {Var y} {unflatten xs}
permute-swap-refl-σ-block {x} {y} {xs} = begin
    (id ⊗₁ (id ⊗₁ id)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
      ≈⟨ ∘-resp-≈
           (≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id) id⊗id≈id)
           ≈-Term-refl ⟩
    id ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)
      ≈⟨ idˡ ⟩
    α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
  ∎

--------------------------------------------------------------------------------
-- ## The rotation permutation: move a front atom past a block.
--
-- `rotate a bs ts : a ∷ (bs ++ ts) ↭ bs ++ (a ∷ ts)`.  Built so that its
-- `permute` matches the `braid (Var a) (map Var bs) (unflatten ts)`
-- recursion step-for-step (front swap then `prep`), via the atomic
-- identity above.

rotate
  : (a : X) (bs ts : List X)
  → (a ∷ (bs ++ ts)) Perm.↭ (bs ++ (a ∷ ts))
rotate a []       ts = Perm.refl
rotate a (b ∷ bs) ts =
  Perm.trans (Perm.swap a b Perm.refl) (Perm.prep b (rotate a bs ts))

--------------------------------------------------------------------------------
-- ## `nest`-`unflatten` coherence (used to align `braid`'s type with
-- `permute`'s in the full single-atom bridge).

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.List using (map)
import Categories.FreeSMC.BraidBlock d as BB

nest-Var
  : ∀ (bs ts : List X)
  → BB.nest (map Var bs) (unflatten ts) ≡ unflatten (bs ++ ts)
nest-Var []       ts = refl
nest-Var (b ∷ bs) ts = cong (Var b ⊗₀_) (nest-Var bs ts)

--------------------------------------------------------------------------------
-- ## Multi-step bridge: `permute (rotate a bs ts) ≈ σ-rotate a bs ts`.
--
-- `σ-rotate` is the σ-block composite that moves the front atom `a` past
-- the block `bs`, stated directly at `unflatten` types (= `braid`
-- specialised to a single-atom A, with `nest` unfolded — so no transport
-- is needed).  `permute-rotate` shows it is exactly `permute (rotate …)`,
-- by iterating the atomic identity `permute-swap-refl-σ-block`.

σ-rotate
  : (a : X) (bs ts : List X)
  → HomTerm (unflatten (a ∷ (bs ++ ts))) (unflatten (bs ++ (a ∷ ts)))
σ-rotate a []       ts = id
σ-rotate a (b ∷ bs) ts =
  (id {A = Var b} ⊗₁ σ-rotate a bs ts) ∘ σ-block {Var a} {Var b} {unflatten (bs ++ ts)}

permute-rotate
  : (a : X) (bs ts : List X)
  → permute (rotate a bs ts) ≈Term σ-rotate a bs ts
permute-rotate a []       ts = ≈-Term-refl
permute-rotate a (b ∷ bs) ts =
  ∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (permute-rotate a bs ts))
           permute-swap-refl-σ-block
