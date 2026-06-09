{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- SPIKE: is the hypergraph→term extractor `decode-attempt` directly usable by
-- the rewrite engine, and what coherence glue reconciles its output objects
-- with a source term's original `ObjTerm` bracketing?
--
-- FINDING (proved below):
--
--   * `decode-attempt ⟪ f ⟫ : Maybe (HomTerm (unflatten (domL ⟪ f ⟫))
--                                             (unflatten (codL ⟪ f ⟫)))`,
--     and `domL ⟪ f ⟫ ≡ flatten A`, `codL ⟪ f ⟫ ≡ flatten B` (the
--     `⟪⟫-domL`/`⟪⟫-codL` lemmas).  So the *object* type of the decoded
--     term is `unflatten (flatten A) → unflatten (flatten B)`, the right-
--     nested, `unit`-padded RE-BRACKETING of the source objects — NOT the
--     original `A → B`.
--
--   * The reconciliation glue is exactly the FreeMonoidal coherence iso
--     `unflatten-flatten-≈ A : A ≅ unflatten (flatten A)`, built from
--     associators/unitors.  It is packaged as `bridge`/`bridge⁻¹`.
--
--   * A FULLY PROVEN, `--safe`, postulate-free roundtrip already exists:
--       decode-roundtrip-rel : decode-rel f ≈Term bridge f
--       bridge-cancel        : bridge⁻¹ (bridge f) ≈Term f
--     where `decode-rel` is the structural decoder used by
--     `soundness-full-wired`.  Composing them recovers `f` from the
--     decoded term up to `≈Term`.
--
-- This module is a STANDALONE demonstration over an arbitrary signature; it
-- needs no concrete target SMC (the reconciliation lives entirely in the
-- free category, then transports along any interpreting functor — exactly
-- how `solveH!`/`rewriteH!` already work).
--------------------------------------------------------------------------------

module Categories.Coherence.DecodeSpike where

open import Categories.APROP

open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- A minimal signature: one atom `a`, one generator `g : Var a → Var a`.
-- `myMor` is at top level so its constructor `g` is in scope below.

data Atom : Set where
  a : Atom

module H = FreeMonoidalHelper Symm Atom

data myMor : H.ObjTerm → H.ObjTerm → Set where
  g : myMor (H.Var a) (H.Var a)

mySig : APROPSignature
mySig = record { X = Atom ; mor = myMor }

-- Decidable equality on atoms and generators (both trivial: single
-- inhabitants), to package `mySig` as an `APROPSignatureDec` (needed for the
-- `SoundnessFullWired` glue `bridge⁻¹`/`bridge-cancel`).
_≟A_ : DecidableEquality Atom
a ≟A a = yes refl

_≟myMor_ : ∀ {A B} → DecidableEquality (myMor A B)
g ≟myMor g = yes refl

mySigDec : APROPSignatureDec
mySigDec = record { sig = mySig ; _≟X_ = _≟A_ ; _≟-mor_ = _≟myMor_ }

open APROP mySig

--------------------------------------------------------------------------------
-- Imports of the decode machinery, all at `mySig`.

open import Categories.APROP.Hypergraph.FromAPROP mySig using (flatten)
open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Soundness.Unflatten mySig
  using (unflatten; unflatten-flatten-≈; _≅_)
open import Categories.APROP.Hypergraph.Soundness.Decode mySig
  using (decode-attempt)
open import Categories.APROP.Hypergraph.Soundness.DecodeAttempt mySig
  using (decode-attempt-Linear; bridge)
open import Categories.APROP.Hypergraph.Soundness.DecodeRel mySig
  using (decode-rel; decode-roundtrip-rel)
open import Categories.APROP.Hypergraph.SoundnessFullWired mySigDec
  using (bridge⁻¹; bridge-cancel)
open import Categories.Category using (Category)

private module FM = Category FreeMonoidal
open FM.HomReasoning

--------------------------------------------------------------------------------
-- The generator and a small NON-TRIVIAL test term.
--
--   gen  : HomTerm (Var a) (Var a)
--   f    = gen ⊗₁ gen : HomTerm (Var a ⊗₀ Var a) (Var a ⊗₀ Var a)
--
-- The `⊗₁` makes the bracketing question real: the source object is the
-- LEFT-nested `Var a ⊗₀ Var a`, whereas `decode`'s objects are the
-- `unit`-padded RIGHT-nested `unflatten [a,a] = Var a ⊗₀ (Var a ⊗₀ unit)`.

gen : HomTerm (Var a) (Var a)
gen = Agen g

f : HomTerm (Var a ⊗₀ Var a) (Var a ⊗₀ Var a)
f = gen ⊗₁ gen

--------------------------------------------------------------------------------
-- (1) The OBJECT TYPE of decode's output, made concrete.
--
-- `flatten (Var a ⊗₀ Var a)` reduces (definitionally) to `a ∷ a ∷ []`, and
-- `unflatten (a ∷ a ∷ [])` to `Var a ⊗₀ (Var a ⊗₀ unit)`.  Both equalities
-- hold by `refl`, exhibiting the re-bracketing explicitly.

flatten-f-dom : flatten (Var a ⊗₀ Var a) ≡ a ∷ a ∷ []
flatten-f-dom = refl

decode-obj-dom : unflatten (flatten (Var a ⊗₀ Var a)) ≡ (Var a ⊗₀ (Var a ⊗₀ unit))
decode-obj-dom = refl

-- The source object is NOT the decode object — they are *different*
-- `ObjTerm`s with the same flattening.  (This is the wrinkle the spike asks
-- about: `(Var a ⊗₀ Var a)` vs `Var a ⊗₀ (Var a ⊗₀ unit)`.)

--------------------------------------------------------------------------------
-- (2) `decode-attempt ⟪ f ⟫` is `just`, and its payload is exactly
-- `proj₁ (decode-attempt-Linear f)`, a term over the decode objects above.

decode-attempt-f-is-just
  : ∃[ t ] decode-attempt ⟪ f ⟫ ≡ just t
decode-attempt-f-is-just = decode-attempt-Linear f

-- The payload's type, spelled out: `HomTerm (unflatten (domL ⟪f⟫))
-- (unflatten (codL ⟪f⟫))`.  Naming it pins the object type the engine sees.
decoded-f : HomTerm (unflatten (domL ⟪ f ⟫)) (unflatten (codL ⟪ f ⟫))
decoded-f = proj₁ (decode-attempt-Linear f)

--------------------------------------------------------------------------------
-- (3) THE GLUE.  The coherence iso reconciling source objects with decode
-- objects, in BOTH directions.

-- Forward: `A ≅ unflatten (flatten A)`.
glue-dom : (Var a ⊗₀ Var a) ≅ unflatten (flatten (Var a ⊗₀ Var a))
glue-dom = unflatten-flatten-≈ (Var a ⊗₀ Var a)

-- `bridge f` re-types `f` onto the decode objects by pre/post-composing the
-- glue isos:  bridge f = (glue⁻¹ on cod) ∘ f ∘ (glue on dom).
bridged-f : HomTerm (unflatten (flatten (Var a ⊗₀ Var a)))
                    (unflatten (flatten (Var a ⊗₀ Var a)))
bridged-f = bridge f

--------------------------------------------------------------------------------
-- (4) THE RECONCILIATION, PROVEN.
--
-- (4a) The structural decoder agrees with the glued source term, up to the
-- free-category coherence `≈Term`.  This is `decode-roundtrip-rel` — fully
-- proven, postulate-free, `--safe`.  `decode-rel` is the very decoder
-- `soundness-full-wired` runs on; the algorithmic `decode-attempt` payload
-- agrees with it (proved elsewhere, modulo the assumptions record).

reconcile : decode-rel f ≈Term bridge f
reconcile = decode-roundtrip-rel f

-- (4b) The glue is INVERTIBLE: `bridge⁻¹ (bridge f) ≈Term f`, recovering the
-- ORIGINAL term (and its original bracketing) from the bridged/decoded one.
-- `bridge⁻¹`/`bridge-cancel` come straight from `SoundnessFullWired`.

recover-original : bridge⁻¹ (bridge f) ≈Term f
recover-original = bridge-cancel f

-- (4c) Chain: the decoded (structural) term, transported back through the
-- inverse glue, is `≈Term`-equal to the original `f`.  This is the clean
-- "decode's output is usable" statement: decode + glue⁻¹ = identity (mod ≈).

decode-then-unglue-is-id : bridge⁻¹ (decode-rel f) ≈Term f
decode-then-unglue-is-id = begin
  bridge⁻¹ (decode-rel f)
    ≈⟨ bridge⁻¹-resp-≈ reconcile ⟩
  bridge⁻¹ (bridge f)
    ≈⟨ recover-original ⟩
  f ∎
  where
    -- `bridge⁻¹` is congruent for `≈Term` (it is `to ∘ – ∘ from`).
    bridge⁻¹-resp-≈
      : ∀ {A B} {h k : HomTerm (unflatten (flatten A)) (unflatten (flatten B))}
      → h ≈Term k → bridge⁻¹ {A} {B} h ≈Term bridge⁻¹ {A} {B} k
    bridge⁻¹-resp-≈ p = ∘-resp-≈ ≈-Term-refl (∘-resp-≈ p ≈-Term-refl)
