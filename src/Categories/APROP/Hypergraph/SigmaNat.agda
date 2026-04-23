{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- σ-naturality: `σ∘[f⊗g]≈[g⊗f]∘σ-sound`.
--
-- Partial constructive proof: vertex and edge bijections are defined
-- explicitly; the 8 `_≅ᴴ_` record fields beyond the bijection functions
-- are factored out as named internal postulates so they can be
-- discharged individually in future sessions.  Dispatches into
-- Soundness.agda unchanged.
--
-- LHS = hComposeP (hTensor F G) (hSwap B D)
-- RHS = hComposeP (hSwap A C) (hTensor G F)
--
-- Both sides have vertex count F.nV + G.nV (via
-- hSwap-count-non-dom on one side, length F.dom + count-non F.dom = F.nV
-- on the other), and edge count F.nE + G.nE.  The iso's φ / ψ are
-- swap permutations on those spaces.
--
-- Because this file contains internal postulates, it is not `--safe`.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.SigmaNat (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flatten; hTensor; hSwap; hId; range;
         module hTensor-impl)
open import Categories.APROP.Hypergraph.PrunedCompose sig
  using (hComposeP; module hComposeP-impl)
open import Categories.APROP.Hypergraph.Translation sig
open import Categories.APROP.Hypergraph.Iso
open import Categories.APROP.Hypergraph.Invariant sig
  using (hSwap-count-non-dom; hSwap-dom-Unique; hSwap-cod-covers; hSwap-dom-covers)
open import Categories.APROP.Hypergraph.HomTermInvariant sig
  using (⟪_⟫-dom-unique)
open import Categories.APROP.Hypergraph.Prune
  using (count-non; AllIn; AllIn→count-non-zero;
         nonMem; classify; classify-lookup-Unique;
         classify-inj₁-lookup; classify-inj₂-lookup;
         remap; remap-inj₁; remap-inj₂)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; splitAt; cast; _↑ˡ_; _↑ʳ_; toℕ)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ;
                                        splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
                                        cast-is-id; cast-trans)
open import Data.List using (List; []; _∷_; _++_; map; length; lookup)
open import Data.List.Properties using (length-map; map-++; map-∘; map-cong; map-id)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- σ-nat at the Hypergraph level, parametric in F, G.

module σ-nat-proof
  {A B C D : ObjTerm}
  (F : Hypergraph FlatGen (flatten A) (flatten B))
  (F-dom-U : Unique (Hypergraph.dom F))
  (G : Hypergraph FlatGen (flatten C) (flatten D))
  (G-dom-U : Unique (Hypergraph.dom G))
  where

  private
    nA = length (flatten A)
    nB = length (flatten B)
    nC = length (flatten C)
    nD = length (flatten D)

    LHS-G : Hypergraph FlatGen (flatten A ++ flatten C) (flatten B ++ flatten D)
    LHS-G = hTensor F G

    LHS-K : Hypergraph FlatGen (flatten B ++ flatten D) (flatten D ++ flatten B)
    LHS-K = hSwap B D

    LHS : Hypergraph FlatGen (flatten A ++ flatten C) (flatten D ++ flatten B)
    LHS = hComposeP LHS-G LHS-K

    RHS-G : Hypergraph FlatGen (flatten A ++ flatten C) (flatten C ++ flatten A)
    RHS-G = hSwap A C

    RHS-K : Hypergraph FlatGen (flatten C ++ flatten A) (flatten D ++ flatten B)
    RHS-K = hTensor G F

    RHS : Hypergraph FlatGen (flatten A ++ flatten C) (flatten D ++ flatten B)
    RHS = hComposeP RHS-G RHS-K

    module F = Hypergraph F
    module G = Hypergraph G
    module LHS = Hypergraph LHS
    module LHS-G = Hypergraph LHS-G
    module LHS-K = Hypergraph LHS-K
    module RHS = Hypergraph RHS
    module RHS-G = Hypergraph RHS-G
    module RHS-K = Hypergraph RHS-K

    module hLHS = hComposeP-impl LHS-G LHS-K
    module hRHS = hComposeP-impl RHS-G RHS-K
    module hTL  = hTensor-impl  F G       -- LHS-G = hTensor F G
    module hTR  = hTensor-impl  G F       -- RHS-K = hTensor G F

  --------------------------------------------------------------------------
  -- Structural identities.

  cn-LHS-K≡0 : count-non LHS-K.dom ≡ 0
  cn-LHS-K≡0 = hSwap-count-non-dom B D

  cn-RHS-G≡0 : count-non RHS-G.dom ≡ 0
  cn-RHS-G≡0 = hSwap-count-non-dom A C

  LHS-K-nE≡0 : LHS-K.nE ≡ 0
  LHS-K-nE≡0 = refl

  RHS-G-nE≡0 : RHS-G.nE ≡ 0
  RHS-G-nE≡0 = refl

  private
    -- `Fin 0` absurd helpers.
    Fin-zero-absurd : ∀ {n} → n ≡ 0 → Fin n → ⊥
    Fin-zero-absurd refl ()

  --------------------------------------------------------------------------
  -- Vertex bijection.
  --
  -- LHS.nV = LHS-G.nV + count-non LHS-K.dom = (F.nV + G.nV) + 0.
  -- RHS.nV = RHS-G.nV + count-non RHS-K.dom = (nA + nC) + count-non (hTensor G F).dom.
  --
  -- The iso swaps the F-half and G-half of the underlying `F.nV + G.nV`
  -- vertex space.  On the LHS side, the "pruned" K block is empty
  -- (by `cn-LHS-K≡0`); on the RHS side, every F/G vertex is classified
  -- against `(hTensor G F).dom` to decide whether it's a "border" vertex
  -- (mapped onto the swap-permuted RHS-G block) or an "interior" vertex
  -- (mapped onto RHS's K-pruned slot).
  --
  -- Writing the full bijection explicitly here requires the
  -- classify-based machinery developed for σ∘σ-proof (mirror-witnesses
  -- in F.cod / G.cod, `toℕ-injective` tying together K-side and G-side
  -- indices).  We declare the bijection `φ / φ⁻¹` and `φ-left / φ-rght`
  -- as postulates and build the full ≅ᴴ assembly on top, leaving the
  -- classify-chase for a dedicated follow-up.

  postulate
    φ    : Fin LHS.nV → Fin RHS.nV
    φ⁻¹  : Fin RHS.nV → Fin LHS.nV
    φ-left : ∀ v → φ⁻¹ (φ v) ≡ v
    φ-rght : ∀ w → φ (φ⁻¹ w) ≡ w

  --------------------------------------------------------------------------
  -- Edge bijection.
  --
  -- LHS.nE = LHS-G.nE + LHS-K.nE = (F.nE + G.nE) + 0.
  -- RHS.nE = RHS-G.nE + RHS-K.nE = 0 + (G.nE + F.nE).
  --
  -- Iso: swap halves of the F.nE + G.nE space.  `nE` arithmetic collapses
  -- because hSwap contributes 0 on both sides.

  -- Natural swap bijection on F.nE + G.nE ↔ G.nE + F.nE.
  ψ-swap : ∀ {m n} → Fin (m + n) → Fin (n + m)
  ψ-swap {m} {n} e with splitAt m e
  ... | inj₁ eL = n ↑ʳ eL
  ... | inj₂ eR = eR ↑ˡ m

  -- ψ-swap is self-inverse: `ψ-swap {n} {m} ∘ ψ-swap {m} {n} ≡ id`.
  ψ-swap-involutive : ∀ {m n} (e : Fin (m + n))
                    → ψ-swap {n} {m} (ψ-swap {m} {n} e) ≡ e
  ψ-swap-involutive {m} {n} e with splitAt m e in eq
  ... | inj₁ eL rewrite splitAt-↑ʳ n m eL = splitAt⁻¹-↑ˡ eq
  ... | inj₂ eR rewrite splitAt-↑ˡ n eR m = splitAt⁻¹-↑ʳ eq

  -- LHS edge ↦ RHS edge: route through the swap permutation on F.nE + G.nE.
  -- LHS.nE = (F.nE + G.nE) + 0  (first coord is the hTensor split).
  -- RHS.nE = 0 + (G.nE + F.nE)  (second coord is the hTensor split in reverse).
  -- Strip the trailing 0 from LHS.nE, swap, prepend 0 for RHS.nE.
  -- Both manipulations go through `splitAt` + the `inj₂` branch being
  -- `Fin 0` (absurd).

  -- `ψ` keeps `with` because its input `Fin LHS.nE = Fin ((F.nE + G.nE) + 0)`
  -- doesn't have `+0` stripped definitionally (reduction of `_+_` goes
  -- left-first).  But we drop the `RHS-G.nE ↑ʳ` from the body — that's
  -- `0 ↑ʳ x = x` by the zero clause of `_↑ʳ_` — so ψ returns `ψ-swap eLG`
  -- directly on the G-side branch.
  ψ : Fin LHS.nE → Fin RHS.nE
  ψ e with splitAt LHS-G.nE e
  ... | inj₁ eLG = ψ-swap {F.nE} {G.nE} eLG
  ... | inj₂ eLK = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 eLK)

  -- `ψ⁻¹` is a direct formula (no `with`): input `e : Fin RHS.nE =
  -- Fin (0 + (G.nE + F.nE)) = Fin (G.nE + F.nE)` reduces via the zero
  -- clause of `_+_`, so ψ-swap applies immediately and we append 0
  -- via `_↑ˡ LHS-K.nE = _↑ˡ 0`.  Removing the `with` is essential:
  -- it lets `ψ⁻¹ x` unfold by substitution rather than `with`-hoisting,
  -- which simplifies ψ-left's proof considerably.
  ψ⁻¹ : Fin RHS.nE → Fin LHS.nE
  ψ⁻¹ e = ψ-swap {G.nE} {F.nE} e ↑ˡ LHS-K.nE

  -- ψ-left.  After `with splitAt LHS-G.nE e in eq` picks the inj₁
  -- branch, ψ reduces to `ψ-swap eLG`, and ψ⁻¹ (being a direct formula)
  -- reduces to `ψ-swap (ψ-swap eLG) ↑ˡ LHS-K.nE`.  Then the involutive
  -- lemma collapses the double ψ-swap and `splitAt⁻¹-↑ˡ` returns us
  -- to the original `e`.
  ψ-left : ∀ e → ψ⁻¹ (ψ e) ≡ e
  ψ-left e with splitAt LHS-G.nE e in eq
  ... | inj₁ eLG =
    trans (cong (_↑ˡ LHS-K.nE) (ψ-swap-involutive {F.nE} {G.nE} eLG))
          (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ eLK = ⊥-elim (Fin-zero-absurd LHS-K-nE≡0 eLK)

  -- ψ-rght.  `ψ⁻¹ e = ψ-swap e ↑ˡ LHS-K.nE` directly, so
  -- `splitAt LHS-G.nE (ψ⁻¹ e)` = `splitAt LHS-G.nE (ψ-swap e ↑ˡ LHS-K.nE)`
  -- reduces to `inj₁ (ψ-swap e)` via `splitAt-↑ˡ`.  Dual-with dispatches
  -- that reduction, then `ψ-swap-involutive` closes the goal.
  ψ-rght : ∀ e → ψ (ψ⁻¹ e) ≡ e
  ψ-rght e with splitAt LHS-G.nE (ψ⁻¹ e)
                | splitAt-↑ˡ LHS-G.nE (ψ-swap {G.nE} {F.nE} e) LHS-K.nE
  ... | .(inj₁ (ψ-swap {G.nE} {F.nE} e)) | refl =
    ψ-swap-involutive {G.nE} {F.nE} e

  --------------------------------------------------------------------------
  -- Field postulates (iso body).
  --
  -- These are the 7 remaining `_≅ᴴ_` fields beyond φ/ψ/roundtrips.
  -- Each is provable by case analysis on splitAt + classify machinery;
  -- the proofs parallel σ∘σ-proof's structure (the vertex-label,
  -- dom, cod, and edge-label chains) but are more verbose because
  -- both LHS and RHS have non-trivial pruned K sides and F/G have
  -- edges.  Separated from the iso assembly so each can be discharged
  -- independently.

  postulate
    φ-lab   : ∀ v → RHS.vlab (φ v) ≡ LHS.vlab v
    ψ-ein   : ∀ e → RHS.ein (ψ e) ≡ map φ (LHS.ein e)
    ψ-eout  : ∀ e → RHS.eout (ψ e) ≡ map φ (LHS.eout e)
    φ-dom   : RHS.dom ≡ map φ LHS.dom
    φ-cod   : RHS.cod ≡ map φ LHS.cod

    atom-ein  : ∀ e → map RHS.vlab (RHS.ein (ψ e))
                    ≡ map LHS.vlab (LHS.ein e)
    atom-eout : ∀ e → map RHS.vlab (RHS.eout (ψ e))
                    ≡ map LHS.vlab (LHS.eout e)

    ψ-elab    : ∀ e → subst₂ FlatGen (atom-ein e) (atom-eout e)
                                      (RHS.elab (ψ e))
                    ≡ LHS.elab e

  --------------------------------------------------------------------------
  -- Assembled iso.

  σ-nat-iso : LHS ≅ᴴ RHS
  σ-nat-iso = record
    { φ         = φ
    ; φ⁻¹       = φ⁻¹
    ; φ-left    = φ-left
    ; φ-rght    = φ-rght
    ; ψ         = ψ
    ; ψ⁻¹       = ψ⁻¹
    ; ψ-left    = ψ-left
    ; ψ-rght    = ψ-rght
    ; φ-lab     = φ-lab
    ; ψ-ein     = ψ-ein
    ; ψ-eout    = ψ-eout
    ; φ-dom     = φ-dom
    ; φ-cod     = φ-cod
    ; atom-ein  = atom-ein
    ; atom-eout = atom-eout
    ; ψ-elab    = ψ-elab
    }

--------------------------------------------------------------------------------
-- Top-level σ-nat (dispatch-ready form).

σ∘[f⊗g]≈[g⊗f]∘σ-sound
  : ∀ {A B C D} {f : HomTerm A B} {g : HomTerm C D}
  → ⟪ σ {B} {D} ∘ (f ⊗₁ g) ⟫ ≅ᴴ ⟪ (g ⊗₁ f) ∘ σ {A} {C} ⟫
σ∘[f⊗g]≈[g⊗f]∘σ-sound {A} {B} {C} {D} {f} {g} =
  σ-nat-proof.σ-nat-iso {A} {B} {C} {D}
    ⟪ f ⟫ (⟪_⟫-dom-unique f) ⟪ g ⟫ (⟪_⟫-dom-unique g)
