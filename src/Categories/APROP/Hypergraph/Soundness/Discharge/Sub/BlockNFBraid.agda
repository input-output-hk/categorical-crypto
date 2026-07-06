{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The two pure-braiding residuals of `Sub/BlockNFVoutCoh.agda`, at the bare
-- `unflatten-++-≅` block level (no `view`/`σ⊗id` conjugation, no faithfulness):
--
--   * `σ-block-comm as bs` — the two-block braiding: `σ` of the two
--     `unflatten`-blocks `as`, `bs`, conjugated by the `unflatten-++-≅`
--     rebracketings, equals `permute (++-comm)`.  Proven from the raw
--     X-level residual `σ-block-comm-raw` (imported from SigmaBlockCommRaw)
--     via the `map-++`/`map⁺` transport bridge.
--
--   * `frame-ext es fs cs P` — residual-`cs` framing naturality (the `++⁺ʳ`
--     mirror of `FireMidEquivariant.permute-++⁺ˡ-slide`): a block `permute P`
--     framed by `unflatten-++-≅` over a fixed residual `cs` equals
--     `permute (++⁺ʳ cs P)`.
--
-- The `Aof`/`R-obj`/`uf++`/`pvl` abbreviations match `BlockNFVoutCoh` so the
-- lemmas splice in directly.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.BlockNFBraid
  (d : FreeMonoidalData)
  (_≟X_ : DecidableEquality (FreeMonoidalData.X d))
  ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; unflatten-++-≅; permute)
open import Categories.FreeSMC.Steps d using (permute-via-vlab)
open import Categories.FreeSMC.BraidBlock d using (σ-block)
open import Categories.FreeSMC.SigmaBlockHexagon d using (σ-block-natural₃)
open import Categories.FreeSMC.BraidPermute d
  using (rotate; σ-rotate; permute-rotate; permute-swap-refl-σ-block)
open import Categories.FreeSMC.SigmaBlockTensor d using (σ⊗-from-hexagon₂)
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.SigmaBlockCommRaw d as SBC

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅; Iso)

-- Mac-Lane coherence solver, used to discharge the pure-associator `pentagon⇐`
-- lemma below in one line.  Mirrors the setup in `Sub/SigmaBlockCommRaw.agda`.
open import Categories.Coherence.Monoidal using (module Solver)
import Data.Vec as Vec
open Vec using (Vec)

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Properties using () renaming (≡-dec to List-≡-dec)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
import Axiom.UniquenessOfIdentityProofs as UIPmod

private
  module FM = Category FreeMonoidal

-- Hedberg UIP on `List X`, from decidable equality on the atom type `X`.
uipX : ∀ {us vs : List X} (p q : us ≡ vs) → p ≡ q
uipX = UIPmod.Decidable⇒UIP.≡-irrelevant (List-≡-dec _≟X_)

open FM.HomReasoning

--------------------------------------------------------------------------------
-- Generic `subst₂ _↭_`/`map⁺` plumbing and the `HomTerm`/iso transport
-- combinators (`to-subst₂-≅`/`from-subst₂-≅`, `subst₂-resp-≈`,
-- `subst₂-∘-split`, `frame-transport`) live in `Sub/PermutationTransport`.
-- The monoidal layer is re-exported `public` for the `BNB.*` consumers.

import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.PermutationTransport
  as PT
open PT.Monoidal d public

--------------------------------------------------------------------------------
-- (A)  RAW (List X-level) `++⁺ʳ`-slide — the `++⁺ʳ` mirror of
-- `FireMidEquivariant.permute-++⁺ˡ-slide`:
--
--   permute (++⁺ʳ cs P)
--     ≈ to(unflatten-++-≅ fs cs) ∘ (permute P ⊗₁ id) ∘ from(unflatten-++-≅ es cs)
--
-- Pure `unflatten-++-≅` naturality on the first block argument, by
-- induction on `P : es ↭ fs`.

private
  -- A `swap x y R` derivation decomposes into the front-two-atom swap
  -- (refl tail) post-composed by the `R`-block.
  permute-swap-decomp
    : ∀ {x y : X} {es fs : List X} (R : es Perm.↭ fs)
    → permute (Perm.swap x y R)
      ≈Term (id {A = Var y} ⊗₁ (id {A = Var x} ⊗₁ permute R))
              ∘ permute (Perm.swap x y (Perm.refl {xs = es}))
  permute-swap-decomp {x} {y} {es} R = begin
      (id ⊗₁ (id ⊗₁ permute R)) ∘ α⇒ ∘ (σ ⊗₁ id) ∘ α⇐
        ≈⟨ refl⟩∘⟨ ≈-Term-sym idˡ ⟩
      (id ⊗₁ (id ⊗₁ permute R)) ∘ (id ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐))
        ≈⟨ refl⟩∘⟨ (≈-Term-sym (≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id) id⊗id≈id)
                     ⟩∘⟨refl) ⟩
      (id ⊗₁ (id ⊗₁ permute R))
        ∘ ((id ⊗₁ (id ⊗₁ id)) ∘ (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐)) ∎

  -- Dual pentagon (α⇐ form): (α⇐⊗id) ∘ α⇐ ∘ (id⊗α⇐) ≈ α⇐ ∘ α⇐.
  pentagon⇐
    : ∀ {A B C D : ObjTerm}
    → (α⇐ {A = A} {B = B} {C = C} ⊗₁ id {A = D})
        ∘ α⇐ {A = A} {B = B ⊗₀ C} {C = D}
        ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C} {C = D})
      ≈Term α⇐ {A = A ⊗₀ B} {B = C} {C = D} ∘ α⇐ {A = A} {B = B} {C = C ⊗₀ D}
  pentagon⇐ {A} {B} {C} {D} = solveM
      ((α⇐ˢ {A = a₀} {b₀} {c₀} ⊗₁ˢ idˢ)
        ∘ˢ α⇐ˢ {A = a₀} {b₀ ⊗₀ˢ c₀} {d₀}
        ∘ˢ (idˢ ⊗₁ˢ α⇐ˢ {A = b₀} {c₀} {d₀}))
      (α⇐ˢ {A = a₀ ⊗₀ˢ b₀} {c₀} {d₀} ∘ˢ α⇐ˢ {A = a₀} {b₀} {c₀ ⊗₀ˢ d₀})
    where
      vars : Vec ObjTerm 4
      vars = A Vec.∷ B Vec.∷ C Vec.∷ D Vec.∷ Vec.[]
      open Solver (record { U = FreeMonoidal ; monoidal = Monoidal-FreeMonoidal })
                  {n = 4} vars
        using (solveM)
        renaming (α⇐ to α⇐ˢ; id to idˢ; _∘_ to _∘ˢ_;
                  _⊗₁_ to _⊗₁ˢ_; _⊗₀_ to _⊗₀ˢ_; Var to Varˢ)
      a₀ b₀ c₀ d₀ : _
      a₀ = Varˢ zero
      b₀ = Varˢ (suc zero)
      c₀ = Varˢ (suc (suc zero))
      d₀ = Varˢ (suc (suc (suc zero)))

  -- σ-block C-slot merge: braiding over `C₁ ⊗ C₂` equals braiding over `C₁`
  -- (tensored with `id_{C₂}`) framed by associators that re-bracket `C₂` out.
  -- Pure Mac-Lane coherence (no hexagon, σ is untouched).
  --   σ-block{A}{B}{C₁⊗C₂}
  --     ≈ (id_B ⊗ α⇒) ∘ α⇒ ∘ ((σ-block{A}{B}{C₁}) ⊗ id_{C₂}) ∘ α⇐ ∘ (id_A ⊗ α⇐)
  σ-block-merge
    : ∀ {A B C₁ C₂ : ObjTerm}
    → σ-block {A} {B} {C₁ ⊗₀ C₂}
      ≈Term (id {A = B} ⊗₁ α⇒ {A = A} {B = C₁} {C = C₂})
              ∘ α⇒ {A = B} {B = A ⊗₀ C₁} {C = C₂}
              ∘ ((σ-block {A} {B} {C₁}) ⊗₁ id {A = C₂})
              ∘ α⇐ {A = A} {B = B ⊗₀ C₁} {C = C₂}
              ∘ (id {A = A} ⊗₁ α⇐ {A = B} {B = C₁} {C = C₂})
  σ-block-merge {A} {B} {C₁} {C₂} = ≈-Term-sym (begin
      (id ⊗₁ α⇒) ∘ α⇒ ∘ (σb₁ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (dist-σb ⟩∘⟨refl) ⟩
      (id ⊗₁ α⇒) ∘ α⇒
        ∘ ((α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id))
        ∘ α⇐ ∘ (id ⊗₁ α⇐)
        ≈⟨ regroup ⟩
      ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id))
        ∘ ((σ ⊗₁ id) ⊗₁ id)
        ∘ ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
        ≈⟨ ∘-resp-≈ pentagon (refl⟩∘⟨ pentagon⇐) ⟩
      (α⇒ ∘ α⇒)
        ∘ ((σ ⊗₁ id) ⊗₁ id)
        ∘ (α⇐ ∘ α⇐)
        ≈⟨ middle-collapse ⟩
      α⇒ ∘ (σ ⊗₁ id) ∘ α⇐ ∎)
    where
      σb₁ = σ-block {A} {B} {C₁}

      dist-σb : (σb₁ ⊗₁ id {A = C₂}) ≈Term (α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id)
      dist-σb = begin
        (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ⊗₁ id
          ≈⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩
        (α⇒ ∘ (σ ⊗₁ id) ∘ α⇐) ⊗₁ (id ∘ id)
          ≈⟨ ⊗-∘-dist ⟩
        (α⇒ ⊗₁ id) ∘ (((σ ⊗₁ id) ∘ α⇐) ⊗₁ id)
          ≈⟨ refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ) ⟩
        (α⇒ ⊗₁ id) ∘ (((σ ⊗₁ id) ∘ α⇐) ⊗₁ (id ∘ id))
          ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
        (α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id) ∎

      regroup
        : (id ⊗₁ α⇒) ∘ α⇒
            ∘ ((α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id))
            ∘ α⇐ ∘ (id ⊗₁ α⇐)
          ≈Term ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id))
                  ∘ ((σ ⊗₁ id) ⊗₁ id)
                  ∘ ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
      regroup = begin
        (id ⊗₁ α⇒) ∘ α⇒
          ∘ ((α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id))
          ∘ α⇐ ∘ (id ⊗₁ α⇐)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
        (id ⊗₁ α⇒) ∘ α⇒
          ∘ (α⇒ ⊗₁ id) ∘ (((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ⊗₁ id))
          ∘ α⇐ ∘ (id ⊗₁ α⇐)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
        (id ⊗₁ α⇒) ∘ α⇒
          ∘ (α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ ((α⇐ ⊗₁ id)
          ∘ α⇐ ∘ (id ⊗₁ α⇐))
          ≈⟨ ≈-Term-sym FM.assoc ⟩
        ((id ⊗₁ α⇒) ∘ α⇒)
          ∘ ((α⇒ ⊗₁ id) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ ((α⇐ ⊗₁ id)
          ∘ α⇐ ∘ (id ⊗₁ α⇐)))
          ≈⟨ ≈-Term-sym FM.assoc ⟩
        (((id ⊗₁ α⇒) ∘ α⇒) ∘ (α⇒ ⊗₁ id))
          ∘ (((σ ⊗₁ id) ⊗₁ id) ∘ ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)))
          ≈⟨ ∘-resp-≈ FM.assoc ≈-Term-refl ⟩
        ((id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id))
          ∘ (((σ ⊗₁ id) ⊗₁ id) ∘ ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))) ∎

      middle-collapse
        : (α⇒ ∘ α⇒) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇐)
          ≈Term α⇒ ∘ (σ ⊗₁ id {A = C₁ ⊗₀ C₂}) ∘ α⇐
      middle-collapse = begin
        (α⇒ ∘ α⇒) ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇐)
          ≈⟨ FM.assoc ⟩
        α⇒ ∘ (α⇒ ∘ ((σ ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ α⇐))
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        α⇒ ∘ ((α⇒ ∘ ((σ ⊗₁ id) ⊗₁ id)) ∘ (α⇐ ∘ α⇐))
          ≈⟨ refl⟩∘⟨ (α-comm ⟩∘⟨refl) ⟩
        α⇒ ∘ (((σ ⊗₁ (id ⊗₁ id)) ∘ α⇒) ∘ (α⇐ ∘ α⇐))
          ≈⟨ refl⟩∘⟨ (⊗-resp-≈ ≈-Term-refl id⊗id≈id ⟩∘⟨refl ⟩∘⟨refl) ⟩
        α⇒ ∘ (((σ ⊗₁ id) ∘ α⇒) ∘ (α⇐ ∘ α⇐))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        α⇒ ∘ ((σ ⊗₁ id) ∘ (α⇒ ∘ (α⇐ ∘ α⇐)))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        α⇒ ∘ ((σ ⊗₁ id) ∘ ((α⇒ ∘ α⇐) ∘ α⇐))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (α⇒∘α⇐≈id ⟩∘⟨refl) ⟩
        α⇒ ∘ ((σ ⊗₁ id) ∘ (id ∘ α⇐))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        α⇒ ∘ ((σ ⊗₁ id) ∘ α⇐) ∎

  -- σ/α base coherence: the front swap on `(x ∷ y ∷ es) ++ cs` equals the
  -- front swap on `(x ∷ y ∷ es)` framed by `uf++ · cs` (σ only touches the
  -- front two atoms, `cs` is passive).
  swap-refl-slide
    : ∀ (cs : List X) {x y : X} (es : List X)
    → permute (Perm.swap x y (Perm.refl {xs = es ++ cs}))
      ≈Term _≅_.to (unflatten-++-≅ (y ∷ x ∷ es) cs)
              ∘ (permute (Perm.swap x y (Perm.refl {xs = es})) ⊗₁ id {A = unflatten cs})
              ∘ _≅_.from (unflatten-++-≅ (x ∷ y ∷ es) cs)
  swap-refl-slide cs {x} {y} es = begin
      permute (Perm.swap x y (Perm.refl {xs = es ++ cs}))
        ≈⟨ permute-swap-refl-σ-block ⟩
      σ-block {Var x} {Var y} {unflatten (es ++ cs)}
        ≈⟨ core ⟩
      toYX ∘ ((σ-block {Var x} {Var y} {E} ⊗₁ id) ∘ fromXY)
        ≈⟨ refl⟩∘⟨ ((⊗-resp-≈ (≈-Term-sym permute-swap-refl-σ-block) ≈-Term-refl)
             ⟩∘⟨refl) ⟩
      toYX ∘ ((permute (Perm.swap x y (Perm.refl {xs = es})) ⊗₁ id) ∘ fromXY) ∎
    where
      E      = unflatten es
      Cc     = unflatten cs
      toE    = _≅_.to   (unflatten-++-≅ es cs)
      fromE  = _≅_.from (unflatten-++-≅ es cs)
      toYX   = _≅_.to   (unflatten-++-≅ (y ∷ x ∷ es) cs)
      fromXY = _≅_.from (unflatten-++-≅ (x ∷ y ∷ es) cs)
      σbE = σ-block {Var x} {Var y} {E}
      core
        : σ-block {Var x} {Var y} {unflatten (es ++ cs)}
          ≈Term toYX ∘ ((σbE ⊗₁ id) ∘ fromXY)
      core = begin
        σ-block {Var x} {Var y} {unflatten (es ++ cs)}
          ≈⟨ insert-iso ⟩
        (id ⊗₁ (id ⊗₁ toE))
          ∘ σ-block {Var x} {Var y} {E ⊗₀ Cc}
          ∘ (id ⊗₁ (id ⊗₁ fromE))
          ≈⟨ refl⟩∘⟨ (σ-block-merge ⟩∘⟨refl) ⟩
        (id ⊗₁ (id ⊗₁ toE))
          ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
          ∘ (id ⊗₁ (id ⊗₁ fromE))
          ≈⟨ assemble ⟩
        toYX ∘ ((σbE ⊗₁ id) ∘ fromXY) ∎
        where
          insert-iso
            : σ-block {Var x} {Var y} {unflatten (es ++ cs)}
              ≈Term (id ⊗₁ (id ⊗₁ toE))
                      ∘ σ-block {Var x} {Var y} {E ⊗₀ Cc}
                      ∘ (id ⊗₁ (id ⊗₁ fromE))
          insert-iso = begin
            σ-block {Var x} {Var y} {unflatten (es ++ cs)}
              ≈⟨ ≈-Term-sym idʳ ⟩
            σ-block {Var x} {Var y} {unflatten (es ++ cs)} ∘ id
              ≈⟨ refl⟩∘⟨ ≈-Term-sym idid ⟩
            σ-block {Var x} {Var y} {unflatten (es ++ cs)}
              ∘ ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ (id ⊗₁ fromE)))
              ≈⟨ FM.sym-assoc ⟩
            (σ-block {Var x} {Var y} {unflatten (es ++ cs)}
              ∘ (id ⊗₁ (id ⊗₁ toE))) ∘ (id ⊗₁ (id ⊗₁ fromE))
              ≈⟨ σ-block-natural₃ ⟩∘⟨refl ⟩
            ((id ⊗₁ (id ⊗₁ toE)) ∘ σ-block {Var x} {Var y} {E ⊗₀ Cc})
              ∘ (id ⊗₁ (id ⊗₁ fromE))
              ≈⟨ FM.assoc ⟩
            (id ⊗₁ (id ⊗₁ toE))
              ∘ σ-block {Var x} {Var y} {E ⊗₀ Cc}
              ∘ (id ⊗₁ (id ⊗₁ fromE)) ∎
            where
              idid : (id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ (id ⊗₁ fromE)) ≈Term id
              idid = begin
                (id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ (id ⊗₁ fromE))
                  ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
                (id ∘ id) ⊗₁ ((id ⊗₁ toE) ∘ (id ⊗₁ fromE))
                  ≈⟨ ⊗-resp-≈ idˡ (≈-Term-sym ⊗-∘-dist) ⟩
                id ⊗₁ ((id ∘ id) ⊗₁ (toE ∘ fromE))
                  ≈⟨ ⊗-resp-≈ ≈-Term-refl (⊗-resp-≈ idˡ
                       (Iso.isoˡ (_≅_.iso (unflatten-++-≅ es cs)))) ⟩
                id ⊗₁ (id ⊗₁ id)
                  ≈⟨ ≈-Term-trans (⊗-resp-≈ ≈-Term-refl id⊗id≈id) id⊗id≈id ⟩
                id ∎

          -- regroup the merge-form into toYX ∘ (σbE ⊗ id) ∘ fromXY
          assemble
            : (id ⊗₁ (id ⊗₁ toE))
                ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
                ∘ (id ⊗₁ (id ⊗₁ fromE))
              ≈Term toYX ∘ ((σbE ⊗₁ id) ∘ fromXY)
          assemble = begin
            (id ⊗₁ (id ⊗₁ toE))
              ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
              ∘ (id ⊗₁ (id ⊗₁ fromE))
              ≈⟨ shuffle ⟩
            ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒) ∘ α⇒)
              ∘ (σbE ⊗₁ id)
              ∘ (α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ fromE)))
              ≈⟨ ∘-resp-≈ (≈-Term-sym toYX-unfold)
                          (refl⟩∘⟨ (≈-Term-sym fromXY-unfold)) ⟩
            toYX ∘ ((σbE ⊗₁ id) ∘ fromXY) ∎
            where
              toYX-unfold : toYX ≈Term (id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒) ∘ α⇒
              toYX-unfold = begin
                toYX
                  ≡⟨⟩
                (id ⊗₁ ((id ⊗₁ toE) ∘ α⇒)) ∘ α⇒
                  ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩∘⟨refl ⟩
                ((id ∘ id) ⊗₁ ((id ⊗₁ toE) ∘ α⇒)) ∘ α⇒
                  ≈⟨ ⊗-∘-dist ⟩∘⟨refl ⟩
                ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒)) ∘ α⇒
                  ≈⟨ FM.assoc ⟩
                (id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∎

              fromXY-unfold : fromXY ≈Term α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ fromE))
              fromXY-unfold = begin
                fromXY
                  ≡⟨⟩
                α⇐ ∘ (id ⊗₁ (α⇐ ∘ (id ⊗₁ fromE)))
                  ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
                α⇐ ∘ ((id ∘ id) ⊗₁ (α⇐ ∘ (id ⊗₁ fromE)))
                  ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
                α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ fromE)) ∎

              -- reassociation moving the caps into the framing α's
              shuffle
                : (id ⊗₁ (id ⊗₁ toE))
                    ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
                    ∘ (id ⊗₁ (id ⊗₁ fromE))
                  ≈Term ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒) ∘ α⇒)
                          ∘ (σbE ⊗₁ id)
                          ∘ (α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ fromE)))
              shuffle = begin
                (id ⊗₁ (id ⊗₁ toE))
                  ∘ ((id ⊗₁ α⇒) ∘ α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐))
                  ∘ (id ⊗₁ (id ⊗₁ fromE))
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                (id ⊗₁ (id ⊗₁ toE))
                  ∘ (id ⊗₁ α⇒)
                  ∘ ((α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ fromE)))
                  ≈⟨ FM.sym-assoc ⟩
                ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒))
                  ∘ ((α⇒ ∘ (σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ fromE)))
                  ≈⟨ refl⟩∘⟨ FM.assoc ⟩
                ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒))
                  ∘ α⇒
                  ∘ (((σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ fromE)))
                  ≈⟨ FM.sym-assoc ⟩
                (((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒)) ∘ α⇒)
                  ∘ (((σbE ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ fromE)))
                  ≈⟨ ∘-resp-≈ FM.assoc (FM.assoc) ⟩
                ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒) ∘ α⇒)
                  ∘ ((σbE ⊗₁ id) ∘ ((α⇐ ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ (id ⊗₁ fromE))))
                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
                ((id ⊗₁ (id ⊗₁ toE)) ∘ (id ⊗₁ α⇒) ∘ α⇒)
                  ∘ (σbE ⊗₁ id)
                  ∘ (α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ fromE))) ∎

  -- The prep cons-step, factored out so the swap case can reuse it twice
  -- without extra recursion.  Lifts a slide of a tail morphism `m` to the
  -- slide of `id_{Var z} ⊗₁ m` (pure α-bracketing).
  prep-step
    : ∀ (cs : List X) (z : X) {es fs : List X}
        {block : HomTerm (unflatten es) (unflatten fs)}
        {m : HomTerm (unflatten (es ++ cs)) (unflatten (fs ++ cs))}
    → m ≈Term _≅_.to (unflatten-++-≅ fs cs)
                ∘ (block ⊗₁ id {A = unflatten cs})
                ∘ _≅_.from (unflatten-++-≅ es cs)
    → (id {A = Var z} ⊗₁ m)
      ≈Term _≅_.to (unflatten-++-≅ (z ∷ fs) cs)
              ∘ ((id {A = Var z} ⊗₁ block) ⊗₁ id {A = unflatten cs})
              ∘ _≅_.from (unflatten-++-≅ (z ∷ es) cs)
  prep-step cs z {es} {fs} {block} {m} m-eq = begin
      id ⊗₁ m
        ≈⟨ ⊗-resp-≈ ≈-Term-refl m-eq ⟩
      id ⊗₁ (toF ∘ bb ∘ fromE)
        ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
      (id ∘ id) ⊗₁ (toF ∘ bb ∘ fromE)
        ≈⟨ ⊗-∘-dist ⟩
      (id ⊗₁ toF) ∘ (id ⊗₁ (bb ∘ fromE))
        ≈⟨ refl⟩∘⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
      (id ⊗₁ toF) ∘ ((id ∘ id) ⊗₁ (bb ∘ fromE))
        ≈⟨ refl⟩∘⟨ ⊗-∘-dist ⟩
      (id ⊗₁ toF) ∘ (id ⊗₁ bb) ∘ (id ⊗₁ fromE)
        ≈⟨ refl⟩∘⟨ mid-assoc ⟩∘⟨refl ⟩
      (id ⊗₁ toF) ∘ (α⇒ ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ fromE)
        ≈⟨ reassoc ⟩
      ((id ⊗₁ toF) ∘ α⇒)
        ∘ ((id ⊗₁ block) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ fromE)) ∎
    where
      toF   = _≅_.to   (unflatten-++-≅ fs cs)
      fromE = _≅_.from (unflatten-++-≅ es cs)
      bb    = block ⊗₁ id {A = unflatten cs}

      mid-assoc : id ⊗₁ bb ≈Term α⇒ ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐
      mid-assoc = begin
        id ⊗₁ bb
          ≈⟨ ≈-Term-sym idʳ ⟩
        (id ⊗₁ bb) ∘ id
          ≈⟨ refl⟩∘⟨ ≈-Term-sym α⇒∘α⇐≈id ⟩
        (id ⊗₁ bb) ∘ α⇒ ∘ α⇐
          ≈⟨ FM.sym-assoc ⟩
        ((id ⊗₁ bb) ∘ α⇒) ∘ α⇐
          ≈⟨ ≈-Term-sym α-comm ⟩∘⟨refl ⟩
        (α⇒ ∘ ((id ⊗₁ block) ⊗₁ id)) ∘ α⇐
          ≈⟨ FM.assoc ⟩
        α⇒ ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐ ∎

      reassoc
        : (id ⊗₁ toF) ∘ (α⇒ ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ fromE)
          ≈Term ((id ⊗₁ toF) ∘ α⇒)
                  ∘ ((id ⊗₁ block) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ fromE))
      reassoc = begin
        (id ⊗₁ toF) ∘ (α⇒ ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ fromE)
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        (id ⊗₁ toF) ∘ α⇒ ∘ (((id ⊗₁ block) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ fromE)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.assoc ⟩
        (id ⊗₁ toF) ∘ α⇒ ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ fromE)
          ≈⟨ FM.sym-assoc ⟩
        ((id ⊗₁ toF) ∘ α⇒)
          ∘ ((id ⊗₁ block) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ fromE) ∎

  permute-++⁺ʳ-slide
    : ∀ (cs : List X) {es fs : List X} (P : es Perm.↭ fs)
    → permute (PermProp.++⁺ʳ cs P)
      ≈Term _≅_.to (unflatten-++-≅ fs cs)
              ∘ (permute P ⊗₁ id {A = unflatten cs})
              ∘ _≅_.from (unflatten-++-≅ es cs)
  permute-++⁺ʳ-slide cs {es} Perm.refl = begin
      id
        ≈⟨ ≈-Term-sym (Iso.isoˡ (_≅_.iso (unflatten-++-≅ es cs))) ⟩
      _≅_.to (unflatten-++-≅ es cs) ∘ _≅_.from (unflatten-++-≅ es cs)
        ≈⟨ refl⟩∘⟨ ≈-Term-sym idˡ ⟩
      _≅_.to (unflatten-++-≅ es cs)
        ∘ (id ∘ _≅_.from (unflatten-++-≅ es cs))
        ≈⟨ refl⟩∘⟨ (≈-Term-sym id⊗id≈id ⟩∘⟨refl) ⟩
      _≅_.to (unflatten-++-≅ es cs)
        ∘ ((id ⊗₁ id) ∘ _≅_.from (unflatten-++-≅ es cs)) ∎
  permute-++⁺ʳ-slide cs {x ∷ es} {x ∷ fs} (Perm.prep .x P) =
    prep-step cs x (permute-++⁺ʳ-slide cs P)
  permute-++⁺ʳ-slide cs {x ∷ y ∷ es} {y ∷ x ∷ fs} (Perm.swap .x .y P) = begin
      permute (Perm.swap x y (PermProp.++⁺ʳ cs P))
        ≈⟨ permute-swap-decomp (PermProp.++⁺ʳ cs P) ⟩
      ppB ∘ permute (Perm.swap x y (Perm.refl {xs = es ++ cs}))
        ≈⟨ ∘-resp-≈ ppB-slide (swap-refl-slide cs es) ⟩
      (toF2 ∘ (ppP ⊗₁ id) ∘ fromYX)
        ∘ (toYX ∘ (sw-es ⊗₁ id) ∘ fromE2)
        ≈⟨ collapse ⟩
      toF2 ∘ (permute (Perm.swap x y P) ⊗₁ id) ∘ fromE2 ∎
    where
      toF2  = _≅_.to   (unflatten-++-≅ (y ∷ x ∷ fs) cs)
      fromE2 = _≅_.from (unflatten-++-≅ (x ∷ y ∷ es) cs)
      toYX  = _≅_.to   (unflatten-++-≅ (y ∷ x ∷ es) cs)
      fromYX = _≅_.from (unflatten-++-≅ (y ∷ x ∷ es) cs)
      sw-es = permute (Perm.swap x y (Perm.refl {xs = es}))
      -- the prep-prep block, and its underlying `block`
      ppB   = id {A = Var y} ⊗₁ (id {A = Var x} ⊗₁ permute (PermProp.++⁺ʳ cs P))
      ppP   = id {A = Var y} ⊗₁ (id {A = Var x} ⊗₁ permute P)

      ppB-slide : ppB ≈Term toF2 ∘ (ppP ⊗₁ id) ∘ fromYX
      ppB-slide = prep-step cs y (prep-step cs x (permute-++⁺ʳ-slide cs P))

      collapse
        : (toF2 ∘ (ppP ⊗₁ id) ∘ fromYX) ∘ (toYX ∘ (sw-es ⊗₁ id) ∘ fromE2)
          ≈Term toF2 ∘ (permute (Perm.swap x y P) ⊗₁ id) ∘ fromE2
      collapse = begin
        (toF2 ∘ (ppP ⊗₁ id) ∘ fromYX) ∘ (toYX ∘ (sw-es ⊗₁ id) ∘ fromE2)
          ≈⟨ FM.assoc ⟩
        toF2 ∘ (((ppP ⊗₁ id) ∘ fromYX) ∘ (toYX ∘ (sw-es ⊗₁ id) ∘ fromE2))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        toF2 ∘ (ppP ⊗₁ id) ∘ (fromYX ∘ (toYX ∘ (sw-es ⊗₁ id) ∘ fromE2))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        toF2 ∘ (ppP ⊗₁ id) ∘ ((fromYX ∘ toYX) ∘ (sw-es ⊗₁ id) ∘ fromE2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (Iso.isoʳ (_≅_.iso (unflatten-++-≅ (y ∷ x ∷ es) cs))
               ⟩∘⟨refl) ⟩
        toF2 ∘ (ppP ⊗₁ id) ∘ (id ∘ (sw-es ⊗₁ id) ∘ fromE2)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        toF2 ∘ (ppP ⊗₁ id) ∘ ((sw-es ⊗₁ id) ∘ fromE2)
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        toF2 ∘ ((ppP ⊗₁ id) ∘ (sw-es ⊗₁ id)) ∘ fromE2
          ≈⟨ refl⟩∘⟨ fuse ⟩∘⟨refl ⟩
        toF2 ∘ (permute (Perm.swap x y P) ⊗₁ id) ∘ fromE2 ∎
        where
          fuse : (ppP ⊗₁ id) ∘ (sw-es ⊗₁ id) ≈Term permute (Perm.swap x y P) ⊗₁ id
          fuse = begin
            (ppP ⊗₁ id) ∘ (sw-es ⊗₁ id)
              ≈⟨ ≈-Term-sym ⊗-∘-dist ⟩
            (ppP ∘ sw-es) ⊗₁ (id ∘ id)
              ≈⟨ ⊗-resp-≈ (≈-Term-sym (permute-swap-decomp P)) idˡ ⟩
            permute (Perm.swap x y P) ⊗₁ id ∎
  permute-++⁺ʳ-slide cs {es} {fs} (Perm.trans {ys = gs} P Q) = begin
      permute (PermProp.++⁺ʳ cs Q) ∘ permute (PermProp.++⁺ʳ cs P)
        ≈⟨ ∘-resp-≈ (permute-++⁺ʳ-slide cs Q) (permute-++⁺ʳ-slide cs P) ⟩
      (toF ∘ (permute Q ⊗₁ id) ∘ fromG)
        ∘ (toG ∘ (permute P ⊗₁ id) ∘ fromE)
        ≈⟨ collapse ⟩
      toF ∘ (permute (Perm.trans P Q) ⊗₁ id) ∘ fromE ∎
    where
      toF   = _≅_.to   (unflatten-++-≅ fs cs)
      fromE = _≅_.from (unflatten-++-≅ es cs)
      toG   = _≅_.to   (unflatten-++-≅ gs cs)
      fromG = _≅_.from (unflatten-++-≅ gs cs)
      PP    = permute P ⊗₁ id {A = unflatten cs}
      QQ    = permute Q ⊗₁ id {A = unflatten cs}

      -- cancel `fromG ∘ toG = id` and fuse the two ⊗-blocks
      collapse
        : (toF ∘ QQ ∘ fromG) ∘ (toG ∘ PP ∘ fromE)
          ≈Term toF ∘ (permute (Perm.trans P Q) ⊗₁ id) ∘ fromE
      collapse = begin
        (toF ∘ QQ ∘ fromG) ∘ (toG ∘ PP ∘ fromE)
          ≈⟨ FM.assoc ⟩
        toF ∘ ((QQ ∘ fromG) ∘ (toG ∘ PP ∘ fromE))
          ≈⟨ refl⟩∘⟨ FM.assoc ⟩
        toF ∘ QQ ∘ (fromG ∘ (toG ∘ PP ∘ fromE))
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        toF ∘ QQ ∘ ((fromG ∘ toG) ∘ PP ∘ fromE)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (Iso.isoʳ (_≅_.iso (unflatten-++-≅ gs cs)) ⟩∘⟨refl) ⟩
        toF ∘ QQ ∘ (id ∘ PP ∘ fromE)
          ≈⟨ refl⟩∘⟨ refl⟩∘⟨ idˡ ⟩
        toF ∘ QQ ∘ (PP ∘ fromE)
          ≈⟨ refl⟩∘⟨ FM.sym-assoc ⟩
        toF ∘ (QQ ∘ PP) ∘ fromE
          ≈⟨ refl⟩∘⟨ fuse ⟩∘⟨refl ⟩
        toF ∘ ((permute Q ∘ permute P) ⊗₁ id) ∘ fromE ∎
        where
          fuse : QQ ∘ PP ≈Term (permute Q ∘ permute P) ⊗₁ id
          fuse = ≈-Term-trans (≈-Term-sym ⊗-∘-dist) (⊗-resp-≈ ≈-Term-refl idˡ)

  --------------------------------------------------------------------------
  -- (A2)  RAW two-block braiding = `permute (++-comm)`:
  --   to(unflatten-++-≅ ys xs) ∘ σ{unflatten xs}{unflatten ys}
  --       ∘ from(unflatten-++-≅ xs ys)
  --     ≈ permute (++-comm xs ys)
  -- Proven in `Sub/SigmaBlockCommRaw.agda`.
  σ-block-comm-raw
    : (xs ys : List X)
    → _≅_.to (unflatten-++-≅ ys xs)
        ∘ σ {A = unflatten xs} {B = unflatten ys}
        ∘ _≅_.from (unflatten-++-≅ xs ys)
      ≈Term permute (PermProp.++-comm xs ys)
  σ-block-comm-raw = SBC.σ-block-comm-raw

--------------------------------------------------------------------------------
-- (B)  The `map vlab` block level — the two residuals of `BlockNFVoutCoh`.
-- The `Aof`/`R-obj`/`uf++`/`pvl` abbreviations match `BlockNFVoutCoh`.

module _ {n : ℕ} (vlab : Fin n → X) where

  Aof : List (Fin n) → ObjTerm
  Aof xs = unflatten (map vlab xs)

  R-obj : List (Fin n) → ObjTerm
  R-obj cs = unflatten (map vlab cs)

  uf++ : (As Bs : List (Fin n))
       → unflatten (map vlab (As ++ Bs))
         ≅ unflatten (map vlab As) ⊗₀ unflatten (map vlab Bs)
  uf++ As Bs =
    subst₂ _≅_
      (cong unflatten (sym (map-++ vlab As Bs)))
      refl
      (unflatten-++-≅ (map vlab As) (map vlab Bs))

  pvl : {xs ys : List (Fin n)} → xs Perm.↭ ys
      → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
  pvl = permute-via-vlab vlab

  --------------------------------------------------------------------
  -- subst plumbing bridging `uf++` / `pvl (++⁺ʳ …)` to the raw forms.

  -- `subst₂ HomTerm` pushed through `permute` onto the `↭`.
  permute-subst₂
    : ∀ {xs xs' ys ys' : List X} (p : xs ≡ xs') (q : ys ≡ ys')
        (r : xs Perm.↭ ys)
    → subst₂ HomTerm (cong unflatten p) (cong unflatten q) (permute r)
      ≡ permute (subst₂ Perm._↭_ p q r)
  permute-subst₂ refl refl r = refl

  -- generic `map⁺`-commutation lemmas (Sub/PermutationTransport), at `vlab`
  private
    map⁺-++⁺ʳ    = PT.map⁺-++⁺ʳ vlab
    map⁺-++-comm = PT.map⁺-++-comm vlab uipX

  pvv-++⁺ʳ
    : ∀ (cs : List (Fin n)) {es fs : List (Fin n)} (P : es Perm.↭ fs)
    → pvl (PermProp.++⁺ʳ cs P)
      ≡ subst₂ HomTerm
          (cong unflatten (sym (map-++ vlab es cs)))
          (cong unflatten (sym (map-++ vlab fs cs)))
          (permute (PermProp.++⁺ʳ (map vlab cs) (PermProp.map⁺ vlab P)))
  pvv-++⁺ʳ cs {es} {fs} P =
    trans (cong permute (map⁺-++⁺ʳ cs P))
          (sym (permute-subst₂ (sym (map-++ vlab es cs)) (sym (map-++ vlab fs cs))
                  (PermProp.++⁺ʳ (map vlab cs) (PermProp.map⁺ vlab P))))

  --------------------------------------------------------------------
  -- `frame-ext` — residual `++⁺ʳ` framing (BlockNFVoutCoh residual 2).

  frame-ext
    : (es fs cs : List (Fin n)) (P : es Perm.↭ fs)
    → _≅_.to (uf++ fs cs) ∘ (pvl P ⊗₁ id {A = R-obj cs}) ∘ _≅_.from (uf++ es cs)
      ≈Term pvl (PermProp.++⁺ʳ cs P)
  frame-ext es fs cs P = ≈-Term-sym (begin
      pvl (PermProp.++⁺ʳ cs P)
        ≈⟨ ≡⇒≈Term (pvv-++⁺ʳ cs P) ⟩
      subst₂ HomTerm pE pF (permute (PermProp.++⁺ʳ (map vlab cs) (PermProp.map⁺ vlab P)))
        ≈⟨ subst₂-resp-≈ pE pF
             (permute-++⁺ʳ-slide (map vlab cs) (PermProp.map⁺ vlab P)) ⟩
      subst₂ HomTerm pE pF (rawTO ∘ (MID ∘ FROM))
        ≈⟨ frame-transport pE pF rawTO MID FROM to-eq mid-eq from-eq ⟩
      _≅_.to (uf++ fs cs) ∘ ((pvl P ⊗₁ id) ∘ _≅_.from (uf++ es cs)) ∎)
    where
      pE = cong unflatten (sym (map-++ vlab es cs))
      pF = cong unflatten (sym (map-++ vlab fs cs))
      rawTO = _≅_.to   (unflatten-++-≅ (map vlab fs) (map vlab cs))
      FROM  = _≅_.from (unflatten-++-≅ (map vlab es) (map vlab cs))
      MID   = permute (PermProp.map⁺ vlab P) ⊗₁ id {A = unflatten (map vlab cs)}
      TO    = rawTO

      to-eq : subst₂ HomTerm refl pF rawTO ≡ _≅_.to (uf++ fs cs)
      to-eq = sym (to-subst₂-≅ (cong unflatten (sym (map-++ vlab fs cs)))
                     (unflatten-++-≅ (map vlab fs) (map vlab cs)))

      from-eq : subst₂ HomTerm pE refl FROM ≡ _≅_.from (uf++ es cs)
      from-eq = sym (from-subst₂-≅ (cong unflatten (sym (map-++ vlab es cs)))
                       (unflatten-++-≅ (map vlab es) (map vlab cs)))

      mid-eq : subst₂ HomTerm refl refl MID ≡ pvl P ⊗₁ id {A = R-obj cs}
      mid-eq = refl


  pvv-++-comm
    : ∀ (as bs : List (Fin n))
    → pvl (PermProp.++-comm as bs)
      ≡ subst₂ HomTerm
          (cong unflatten (sym (map-++ vlab as bs)))
          (cong unflatten (sym (map-++ vlab bs as)))
          (permute (PermProp.++-comm (map vlab as) (map vlab bs)))
  pvv-++-comm as bs =
    trans (cong permute (map⁺-++-comm as bs))
          (sym (permute-subst₂ (sym (map-++ vlab as bs)) (sym (map-++ vlab bs as))
                  (PermProp.++-comm (map vlab as) (map vlab bs))))

  --------------------------------------------------------------------
  -- `σ-block-comm` — the two-block braiding (BlockNFVoutCoh residual 1):
  -- transports `σ-block-comm-raw` along the `map-++` substs (`uf++`, `pvl`).

  σ-block-comm
    : (as bs : List (Fin n))
    → _≅_.to (uf++ bs as)
        ∘ (σ {A = Aof as} {B = Aof bs})
        ∘ _≅_.from (uf++ as bs)
      ≈Term pvl (PermProp.++-comm as bs)
  σ-block-comm as bs = ≈-Term-sym (begin
      pvl (PermProp.++-comm as bs)
        ≈⟨ ≡⇒≈Term (pvv-++-comm as bs) ⟩
      subst₂ HomTerm pAB pBA
        (permute (PermProp.++-comm (map vlab as) (map vlab bs)))
        ≈⟨ subst₂-resp-≈ pAB pBA
             (≈-Term-sym (σ-block-comm-raw (map vlab as) (map vlab bs))) ⟩
      subst₂ HomTerm pAB pBA (rawTO ∘ (σm ∘ rawFROM))
        ≈⟨ frame-transport pAB pBA rawTO σm rawFROM to-eq σ-eq from-eq ⟩
      _≅_.to (uf++ bs as) ∘ ((σ {A = Aof as} {B = Aof bs}) ∘ _≅_.from (uf++ as bs)) ∎)
    where
      pAB = cong unflatten (sym (map-++ vlab as bs))
      pBA = cong unflatten (sym (map-++ vlab bs as))
      rawTO   = _≅_.to   (unflatten-++-≅ (map vlab bs) (map vlab as))
      rawFROM = _≅_.from (unflatten-++-≅ (map vlab as) (map vlab bs))
      σm = σ {A = unflatten (map vlab as)} {B = unflatten (map vlab bs)}

      to-eq : subst₂ HomTerm refl pBA rawTO ≡ _≅_.to (uf++ bs as)
      to-eq = sym (to-subst₂-≅ (cong unflatten (sym (map-++ vlab bs as)))
                     (unflatten-++-≅ (map vlab bs) (map vlab as)))

      from-eq : subst₂ HomTerm pAB refl rawFROM ≡ _≅_.from (uf++ as bs)
      from-eq = sym (from-subst₂-≅ (cong unflatten (sym (map-++ vlab as bs)))
                       (unflatten-++-≅ (map vlab as) (map vlab bs)))

      σ-eq : subst₂ HomTerm refl refl σm ≡ σ {A = Aof as} {B = Aof bs}
      σ-eq = refl
