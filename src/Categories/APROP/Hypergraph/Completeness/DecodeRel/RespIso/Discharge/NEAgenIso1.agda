{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge of `nE-Agen-iso-1` from `RespIso/AtomicCompound.agda`.
--
-- `⟪ Agen g ⟫ = hGen g` has `nE ≡ 1` definitionally, so the iso's edge
-- bijection `ψ : Fin 1 → Fin (nE ⟪h⟫)` is a bijection.  Such a bijection
-- exists iff `nE ⟪h⟫ ≡ 1`.
--
-- Proof by case split on `nE ⟪h⟫`:
--   * 0          : `ψ zero` lives in `Fin 0`, absurd.
--   * 1          : `refl`.
--   * suc (suc _): `Fin 1` has a unique inhabitant, so
--                  `ψ⁻¹ zero ≡ zero ≡ ψ⁻¹ (suc zero)`.  Applying `ψ`
--                  and using `ψ-rght` on both sides gives
--                  `zero ≡ suc zero` in `Fin (suc (suc _))`, absurd.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.NEAgenIso1
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen; ⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

private
  nE : Hypergraph FlatGen → ℕ
  nE = Hypergraph.nE

  -- Every inhabitant of `Fin 1` equals `zero`.
  Fin-1-unique : (i : Fin 1) → i ≡ zero
  Fin-1-unique zero = refl

  -- `zero ≢ suc _` in `Fin (suc (suc _))`.
  Fin-zero≢suc : ∀ {n} {i : Fin (suc n)} → _≡_ {A = Fin (suc (suc n))} zero (suc i) → ⊥
  Fin-zero≢suc ()

  -- Generic helper: a bijection `Fin 1 ↔ Fin n` forces `n ≡ 1`.
  fin-bij-1
    : ∀ (n : ℕ)
    → (ψ : Fin 1 → Fin n)
    → (ψ⁻¹ : Fin n → Fin 1)
    → (∀ i → ψ (ψ⁻¹ i) ≡ i)
    → n ≡ 1
  fin-bij-1 zero          ψ ψ⁻¹ ψ-rght with ψ zero
  ... | ()
  fin-bij-1 (suc zero)    ψ ψ⁻¹ ψ-rght = refl
  fin-bij-1 (suc (suc n)) ψ ψ⁻¹ ψ-rght =
    ⊥-elim (Fin-zero≢suc contradiction)
    where
      ψ⁻¹-z≡zero : ψ⁻¹ zero ≡ zero
      ψ⁻¹-z≡zero = Fin-1-unique (ψ⁻¹ zero)

      ψ⁻¹-s≡zero : ψ⁻¹ (suc zero) ≡ zero
      ψ⁻¹-s≡zero = Fin-1-unique (ψ⁻¹ (suc zero))

      contradiction : _≡_ {A = Fin (suc (suc n))} zero (suc zero)
      contradiction =
        trans (sym (ψ-rght zero))
        (trans (cong ψ (trans ψ⁻¹-z≡zero (sym ψ⁻¹-s≡zero)))
               (ψ-rght (suc zero)))

-- The discharge.  `Compound` is not needed — the proof is purely about
-- the edge bijection.
nE-Agen-iso-1
  : ∀ {A B} {g : mor A B} {h : HomTerm A B}
  → ⟪ Agen g ⟫ ≅ᴴ ⟪ h ⟫
  → nE ⟪ h ⟫ ≡ 1
nE-Agen-iso-1 {h = h} iso =
  fin-bij-1 (nE ⟪ h ⟫) ψ ψ⁻¹ ψ-rght
  where open _≅ᴴ_ iso
