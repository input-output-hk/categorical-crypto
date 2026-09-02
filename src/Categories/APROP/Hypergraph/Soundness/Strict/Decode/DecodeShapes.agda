{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Structural SHAPE LEMMAS of the strict decoder `decodePˢ`.  These feed the
-- eventual part-(I)ˢ roundtrip `st f ≈ˢ decodePˢ f`, which `PartI` assembles
-- from them constructor by constructor.
--
-- The strict Kelly residual is taken CONCRETELY from `Strict.Perm.PermK`
-- (discharged axiom-free for every vertex set, no parameter).  The
-- structural atoms pay NO rigidity at all: `⟪ atom ⟫` is a literal `hId`,
-- so the run and the final permutation both reduce to `idˢ`.  No
-- postulates, no holes.
--
-- Contents (in dependency order):
--   * the concrete atomic shapes
--       `decodePˢ-id`, `decodePˢ-λ⇒`, `decodePˢ-λ⇐`,
--       `decodePˢ-ρ⇒`, `decodePˢ-ρ⇐`, `decodePˢ-α⇒`, `decodePˢ-α⇐`
--     each `≈ˢ st (atom)` (idˢ / coe casts);
--   * a closing comment RECORDING the ⊗/∘/σ shape statements, which are
--     proved elsewhere (`TensorBraid`, `DecodeCompose`, `DecodeSigma`) —
--     not here.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes
  (sig : APROPSignature)
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (flatten)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪⟫-domL; ⟪⟫-codL)
import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig as DA

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig as PK

open import Data.List.Properties using (++-identityʳ; ++-assoc)

--------------------------------------------------------------------------------
-- A `↭-reflexive` derivation is the boundary cast of `idˢ`.  Needs neither the
-- K-faithfulness residual nor a `DecidableEquality`, hence its home ABOVE the
-- residual block: that is what `Scr` below can consume.

module Trivial (V : Set) (vlab : V → X) where
  open PK.Support V vlab

  refl-trivial
    : ∀ {xs ys : List V} (e : xs ≡ ys)
    → permuteˢ (Perm.↭-reflexive e)
      ≈ˢ castˢ refl (cong (map vlab) e) (idˢ {map vlab xs})
  refl-trivial refl = ≈-refl

--------------------------------------------------------------------------------
-- The canonical block-swap derivation's `permuteˢ ≈ σˢ` identity (the
-- vertex-level keystone).  Recursion on the LEFT block.
--
-- `bswap` itself is `DecodeAttempt`'s, re-exported: it IS the `hSwap`
-- totality witness, so `finalPermˢ (σ {A}{B})` REDUCES to it and the σ-shape
-- (`DecodeSigma`) pays no rigidity.

module Scr (V : Set) (vlab : V → X) where
  open PK.Support V vlab public
  open Trivial V vlab public
  open Restrict V vlab
    using (idᵛ; _⊗ᵛ_; σᵛ; _≈ᵛ_; permuteᵛ; castᵛ-cast; σ-unitᵛ)

  open DA using (bswap) public

  -- `permuteᵛ (↭-sym (shift v R L))` is the braiding of `v ∷ []` past the
  -- block `R`, framed by `idᵛ {L}` — stated in the `Restrict` layer, so the
  -- former `mdom`/`mcod` map-distribution endpoints are gone.  BASE proven
  -- here (both sides reduce to `idˢ`); the `(x ∷ R)` step is the `σ-hexˢʳ`
  -- reconciliation `Interchange.BlockSwapComm.shift-symᵛ`.
  permuteˢ-shift-sym-base
    : (v : V) (L : List V)
    → permuteᵛ (Perm.↭-sym (PermProp.shift v [] L))
      ≈ᵛ σᵛ (v ∷ []) [] ⊗ᵛ idᵛ {L}
  permuteˢ-shift-sym-base v L =
    ≈-sym (≈-trans (⊗-resp (σ-unitʳˢ (vlab v ∷ [])) ≈-refl) ⊗-id)

  -- `permuteᵛ (bswap L R) ≈ᵛ σᵛ L R`.  BASE proven; the `(v ∷ L)` step is the
  -- `σ-hexᵛ` reconciliation `Interchange.BlockSwapComm.block-swap-comm`.
  bswap-σ-base : (R : List V) → permuteᵛ (bswap [] R) ≈ᵛ σᵛ [] R
  bswap-σ-base R =
    ≈-trans (refl-trivial (sym (++-identityʳ R)))
      (≈-sym (≈-trans (σ-unitᵛ R)
                      (≡⇒≈ˢ (castᵛ-cast refl (sym (++-identityʳ R)) idᵛ))))

  -- The full block-swap identity (statement) — the strict vertex-level
  -- block-swap-commutes keystone.  `bswap-σ-base` is the [] case.
  BswapSig : Set
  BswapSig = ∀ (L R : List V) → permuteᵛ (bswap L R) ≈ᵛ σᵛ L R

--------------------------------------------------------------------------------
-- The structural-atom shapes.  Every structural atom translates to a literal
-- `hId`, which has `nE` literally `0` (so the run's term half IS `idˢ`) and
-- `dom` literally `cod` (so `finalPermˢ` — the `q-id` branch of
-- `decode-attempt-LinearP` — IS `Perm.↭-refl`, whose `permuteˢ` IS `idˢ`).
-- So `decodePˢ (atom)` REDUCES to `castˢ (⟪⟫-domL _) (⟪⟫-codL _) (idˢ ∘ˢ idˢ)`:
-- one unit law and one `cast`-of-`idˢ` is the whole proof, with NO rigidity
-- (K-faithfulness) payment and no `nE ≡ 0` / `dom ≡ cod` transport.
--
-- `st (id) = st λ⇒ = st λ⇐ = idˢ`, closed by `cast-id`; the other four are a
-- `coe` of a `List`-equality, closed by `cast-id-coe` and `coe-uip`.

-- a boundary cast of `idˢ` IS the corresponding object-coercion `coe`
cast-id-coe
  : ∀ {xs as bs} (p : xs ≡ as) (q : xs ≡ bs)
  → castˢ p q (idˢ {xs}) ≈ˢ coe (trans (sym p) q)
cast-id-coe refl q = ≈-refl

module _ {A : ObjTerm} where
  -- id, λ⇒, λ⇐  →  idˢ
  decodePˢ-id : decodePˢ (id {A}) ≈ˢ st (id {A})
  decodePˢ-id =
    ≈-trans (cast-resp (⟪⟫-domL (id {A})) (⟪⟫-codL (id {A})) idʳ)
            (cast-id (⟪⟫-domL (id {A})) (⟪⟫-codL (id {A})))

  decodePˢ-λ⇒ : decodePˢ (λ⇒ {A}) ≈ˢ st (λ⇒ {A})
  decodePˢ-λ⇒ =
    ≈-trans (cast-resp (⟪⟫-domL (λ⇒ {A})) (⟪⟫-codL (λ⇒ {A})) idʳ)
            (cast-id (⟪⟫-domL (λ⇒ {A})) (⟪⟫-codL (λ⇒ {A})))

  decodePˢ-λ⇐ : decodePˢ (λ⇐ {A}) ≈ˢ st (λ⇐ {A})
  decodePˢ-λ⇐ =
    ≈-trans (cast-resp (⟪⟫-domL (λ⇐ {A})) (⟪⟫-codL (λ⇐ {A})) idʳ)
            (cast-id (⟪⟫-domL (λ⇐ {A})) (⟪⟫-codL (λ⇐ {A})))

  -- ρ⇒, ρ⇐  →  coe (±++-identityʳ)
  decodePˢ-ρ⇒ : decodePˢ (ρ⇒ {A}) ≈ˢ st (ρ⇒ {A})
  decodePˢ-ρ⇒ =
    ≈-trans (cast-resp (⟪⟫-domL (ρ⇒ {A})) (⟪⟫-codL (ρ⇒ {A})) idʳ)
    (≈-trans (cast-id-coe (⟪⟫-domL (ρ⇒ {A})) (⟪⟫-codL (ρ⇒ {A})))
             (coe-uip _ (++-identityʳ (flatten A))))

  decodePˢ-ρ⇐ : decodePˢ (ρ⇐ {A}) ≈ˢ st (ρ⇐ {A})
  decodePˢ-ρ⇐ =
    ≈-trans (cast-resp (⟪⟫-domL (ρ⇐ {A})) (⟪⟫-codL (ρ⇐ {A})) idʳ)
    (≈-trans (cast-id-coe (⟪⟫-domL (ρ⇐ {A})) (⟪⟫-codL (ρ⇐ {A})))
             (coe-uip _ (sym (++-identityʳ (flatten A)))))

-- α⇒, α⇐  →  coe (±++-assoc)
module _ {A B C : ObjTerm} where
  decodePˢ-α⇒ : decodePˢ (α⇒ {A} {B} {C}) ≈ˢ st (α⇒ {A} {B} {C})
  decodePˢ-α⇒ =
    ≈-trans (cast-resp (⟪⟫-domL (α⇒ {A} {B} {C})) (⟪⟫-codL (α⇒ {A} {B} {C})) idʳ)
    (≈-trans (cast-id-coe (⟪⟫-domL (α⇒ {A} {B} {C})) (⟪⟫-codL (α⇒ {A} {B} {C})))
             (coe-uip _ (++-assoc (flatten A) (flatten B) (flatten C))))

  decodePˢ-α⇐ : decodePˢ (α⇐ {A} {B} {C}) ≈ˢ st (α⇐ {A} {B} {C})
  decodePˢ-α⇐ =
    ≈-trans (cast-resp (⟪⟫-domL (α⇐ {A} {B} {C})) (⟪⟫-codL (α⇐ {A} {B} {C})) idʳ)
    (≈-trans (cast-id-coe (⟪⟫-domL (α⇐ {A} {B} {C})) (⟪⟫-codL (α⇐ {A} {B} {C})))
             (coe-uip _ (sym (++-assoc (flatten A) (flatten B) (flatten C)))))

--------------------------------------------------------------------------------
-- COMPOUND AND σ SHAPES.  The boundary objects align DEFINITIONALLY (flatten
-- distributes over ⊗₀ as `_++_`), so these are cast-free statements:
--
--   decodePˢ-⊗-shape : decodePˢ (f ⊗₁ g) ≈ˢ decodePˢ f ⊗ˢ decodePˢ g
--   decodePˢ-∘-shape : decodePˢ (g ∘ f) ≈ˢ decodePˢ g ∘ˢ decodePˢ f
--   decodePˢ-σ       : decodePˢ (σ {A} {B}) ≈ˢ σˢ (flatten A) (flatten B)
--
-- discharged in `Strict/Decode/DecodeCompose`(+`DecodeComposeAssembly`),
-- `Tensor/TensorReconcile` + `TensorBraid`, and
-- `DecodeSigma`(+`Interchange/BlockSwapComm`) respectively.
--------------------------------------------------------------------------------
