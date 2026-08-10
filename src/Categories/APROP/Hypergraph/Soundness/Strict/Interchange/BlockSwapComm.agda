{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The strict block-swap-commutation residual `bswap-σ` of
-- `Strict/Decode/DecodeSigma.agda` (the parameter `BSwapσ : Scr.BswapSig`).
--
--   block-swap-comm : ∀ (L R : List V) → permuteᵛ (bswap L R) ≈ᵛ σᵛ L R
--
-- This is the strict, VERTEX-LEVEL twin of the non-strict keystone
-- `BNV.σ-block-comm` (`pvl (++-comm L R) ≈ σ-block`), proven entirely from the
-- `FreeStrictSMC.Build` axioms + the reusable `σ-hexˢʳ` (RIGHT-hexagon)
-- companion lemma and the `[]` base cases proven in `DecodeSigma`.
--
-- The whole module runs in the `Restrict` layer (F7): `HomV as bs = HomS
-- (map vlab as) (map vlab bs)`, whose `_⊗ᵛ_`/`σᵛ` absorb the `map-++`
-- transports.  `Scr.BswapSig` unfolds to `permuteᵛ (bswap L R) ≈ᵛ σᵛ L R` on
-- the nose, so the exported statement is unchanged; what disappears is the
-- endpoint bookkeeping (`Scr.mdom`/`Scr.mcod`, `cast-⊗-frame`, `cast-fuse`,
-- `cast-irrel`, `∘-cast-split`), because at the SINGLETON left frames this
-- induction produces every `List V` associator and every `map-++` reduces.
--
-- Proof structure (mirrors `BlockNFBraid.σ-block-comm` / `prep-step`):
--
--   * `hexᵛ v x R` — the RIGHT hexagon at the singleton frames `v ∷ []`,
--     `x ∷ []`, `R`, where all three associators collapse to `coe refl`;
--   * `shift-symᵛ v R L` — the FULL `permuteᵛ (↭-sym (shift v R L))` slide
--     (induction on `R`), base `Scr.permuteˢ-shift-sym-base`;
--   * `block-swap-comm L R` — induction on `L`, base `Scr.bswap-σ-base`,
--     step = `shift-symᵛ` composed with the framed IH against `σ-hexᵛ`;
--   * `swap-block` — the `++⁺ʳ Rl`-framed public face consumed by `PermCalc`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Interchange.BlockSwapComm
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using (coe; coe-id≈)
open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
  using (σ-hexˢʳ; module Scr)

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (refl; sym)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------

module _ (V : Set) (vlab : V → X) where

  open Scr V vlab
    using (bswap; permuteˢ-shift-sym-base; bswap-σ-base; BswapSig)
  open Restrict V vlab
    using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ; permuteᵛ-frame
          ; ⊗-respᵛ; interchangeᵛ; σ-hexᵛ; castᵛ-≈̂; ⊗-resp-≈̂ᵛ
          ; ⊗-assoc-≈̂ᵛ; box-suffix-≈̂ᵛ; σᵛ-≈̂; viaˢ )

  private
    m : List V → List X
    m = map vlab

  --------------------------------------------------------------------------
  -- (A)  The RIGHT hexagon at singleton frames.  `++-assoc (_ ∷ [])` is
  -- `refl` three times over, so `σ-hexˢʳ`'s three `coe`s collapse and the
  -- V-level statement is a bare two-block composite.

  hexᵛ
    : (v x : V) (R : List V)
    → σᵛ (v ∷ []) (x ∷ R)
      ≈ᵛ (idᵛ {x ∷ []} ⊗ᵛ σᵛ (v ∷ []) R) ∘ᵛ (σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R})
  hexᵛ v x R = viaˢ (σᵛ-≈̂ (v ∷ []) (x ∷ R)) hex' rhs
    where
      a b c : List X
      a = vlab v ∷ []
      b = vlab x ∷ []
      c = m R

      hex' : σˢ a (b ++ c) ≈ˢ (idˢ {b} ⊗ˢ σˢ a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c})
      hex' =
        ≈-trans (σ-hexˢʳ a b c)
        (≈-trans (∘-resp (coe-id≈ (sym (++-assoc b c a))) ≈-refl)
        (≈-trans idˡ
        (≈-trans (∘-resp ≈-refl (coe-id≈ (sym (++-assoc a b c))))
        (≈-trans idʳ
          (∘-resp ≈-refl
            (≈-trans (∘-resp (coe-id≈ (++-assoc b a c)) ≈-refl) idˡ))))))

      rhs : (idᵛ {x ∷ []} ⊗ᵛ σᵛ (v ∷ []) R) ∘ᵛ (σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R})
            ≈̂ (idˢ {b} ⊗ˢ σˢ a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c})
      rhs = ∘-resp-≈̂ (⊗-resp-≈̂ ≈̂-refl (σᵛ-≈̂ (v ∷ []) R)) ≈̂-refl

  --------------------------------------------------------------------------
  -- (B)  The full shift-sym slide, by induction on R.  The only surviving
  -- cast is the genuine `++-assoc R (v ∷ []) L` (the `map-++` layer is gone).

  shift-symᵛ
    : (v : V) (R L : List V)
    → permuteᵛ (Perm.↭-sym (PermProp.shift v R L))
      ≈ᵛ castᵛ refl (++-assoc R (v ∷ []) L) (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L})
  shift-symᵛ v []      L = permuteˢ-shift-sym-base v L
  shift-symᵛ v (x ∷ R) L =
    ≈̂⇒≈ˢ
      (≈̂-trans (∘-resp-≈̂ F1 F2)
      (≈̂-trans (≈ˢ⇒≈̂ interchangeᵛ)
      (≈̂-trans (⊗-resp-≈̂ᵛ (≈ˢ⇒≈̂ (≈-sym (hexᵛ v x R))) (≈ˢ⇒≈̂ idˡ))
               (≈̂-sym (castᵛ-≈̂ refl (++-assoc (x ∷ R) (v ∷ []) L)
                         (σᵛ (v ∷ []) (x ∷ R) ⊗ᵛ idᵛ {L}))))))
    where
      F1 : idᵛ {x ∷ []} ⊗ᵛ permuteᵛ (Perm.↭-sym (PermProp.shift v R L))
           ≈̂ (idᵛ {x ∷ []} ⊗ᵛ σᵛ (v ∷ []) R) ⊗ᵛ idᵛ {L}
      F1 =
        ≈̂-trans
          (⊗-resp-≈̂ ≈̂-refl
            (≈̂-trans (≈ˢ⇒≈̂ (shift-symᵛ v R L))
                     (castᵛ-≈̂ refl (++-assoc R (v ∷ []) L)
                        (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L}))))
          (≈̂-sym (⊗-assoc-≈̂ᵛ (idᵛ {x ∷ []}) (σᵛ (v ∷ []) R) (idᵛ {L})))

      F2 : σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R ++ L}
           ≈̂ (σᵛ (v ∷ []) (x ∷ []) ⊗ᵛ idᵛ {R}) ⊗ᵛ idᵛ {L}
      F2 = ≈̂-sym (box-suffix-≈̂ᵛ (σᵛ (v ∷ []) (x ∷ [])) R L)

  --------------------------------------------------------------------------
  -- (C)  The block-swap commutation, by induction on L.  `σ-hexᵛ` at the
  -- singleton left frame `v ∷ []` has BOTH its `++-assoc (v ∷ []) _ _`
  -- associators reduce, so it is a bare composite of the two factors
  -- `shift-symᵛ` and the framed IH produce.

  block-swap-comm : BswapSig
  block-swap-comm []      R = bswap-σ-base R
  block-swap-comm (v ∷ L) R = ≈̂⇒≈ˢ (≈̂-trans lhs (≈̂-sym rhs))
    where
      CORE : HomV (v ∷ L ++ R) ((R ++ (v ∷ [])) ++ L)
      CORE = (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L}) ∘ᵛ (idᵛ {v ∷ []} ⊗ᵛ σᵛ L R)

      lhs : permuteᵛ (bswap (v ∷ L) R) ≈̂ CORE
      lhs =
        ∘-resp-≈̂
          (≈̂-trans (≈ˢ⇒≈̂ (shift-symᵛ v R L))
                   (castᵛ-≈̂ refl (++-assoc R (v ∷ []) L)
                      (σᵛ (v ∷ []) R ⊗ᵛ idᵛ {L})))
          (⊗-resp-≈̂ ≈̂-refl (≈ˢ⇒≈̂ (block-swap-comm L R)))

      rhs : σᵛ (v ∷ L) R ≈̂ CORE
      rhs =
        ≈̂-trans (≈ˢ⇒≈̂ (σ-hexᵛ (v ∷ []) L R))
                (castᵛ-≈̂ refl (++-assoc R (v ∷ []) L) CORE)

  --------------------------------------------------------------------------
  -- (D)  The `++⁺ʳ Rl`-framed block-swap derivation is, under `permuteᵛ`, the
  -- strict block braiding framed by `idᵛ {Rl}` — the public face consumed by
  -- `PermCalc.⟦bswap⟧ᵛ`.  At V level this is `permuteᵛ-frame` + the keystone.

  swap-block
    : ∀ (L R Rl : List V)
    → permuteᵛ (PermProp.++⁺ʳ Rl (bswap L R)) ≈ᵛ σᵛ L R ⊗ᵛ idᵛ {Rl}
  swap-block L R Rl =
    ≈-trans (permuteᵛ-frame Rl (bswap L R))
            (⊗-respᵛ (block-swap-comm L R) ≈-refl)
