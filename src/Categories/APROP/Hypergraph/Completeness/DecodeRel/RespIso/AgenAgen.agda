{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Agen-Agen case of `decode-rel-resp-≅ᴴ`.
--
-- Given `g₁ g₂ : mor A B` and `⟪ Agen g₁ ⟫ ≅ᴴ ⟪ Agen g₂ ⟫`, show
-- `decode-rel (Agen g₁) ≈Term decode-rel (Agen g₂)`.
--
-- Strategy: `decode-rel (Agen g) = bridge (Agen g)`, so it suffices
-- to prove `g₁ ≡ g₂`.  `⟪ Agen g ⟫ = hGen g` has `nE = 1` and
-- `elab _ = subst₂ FlatGen lem-in lem-out (flat g)` where
-- `lem-in, lem-out` depend only on `A, B`.  The iso's `ψ-elab zero`
-- yields a propositional equation between subst₂'d `flat g₂` and
-- `flat g₁`, which UIP on `List X` (Hedberg from `_≟X_`) collapses
-- to `flat g₁ ≡ flat g₂`, hence `g₁ ≡ g₂` by injectivity of `flat`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.AgenAgen
  (sig-dec : APROPSignatureDec) where

open APROPSignatureDec sig-dec
  using (_≟X_; sig)
open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (FlatGen; flat)
open import Categories.APROP.Hypergraph.Translation sig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.Completeness.DecodeAttempt sig
  using (bridge)
open import Categories.APROP.Hypergraph.Completeness.DecodeRel sig
  using (decode-rel)

open import Axiom.UniquenessOfIdentityProofs using (UIP)
import Axiom.UniquenessOfIdentityProofs as UIP-mod

open import Data.Fin using (Fin; zero)
open import Data.List using (List)
open import Data.List.Properties using (≡-dec)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym; subst₂)

--------------------------------------------------------------------------------
-- UIP on `List X`, plus subst₂ helpers.

private
  _≟LX_ : DecidableEquality (List X)
  _≟LX_ = ≡-dec _≟X_

  UIP-ListX : UIP (List X)
  UIP-ListX = UIP-mod.Decidable⇒UIP.≡-irrelevant _≟LX_

  -- `subst₂ FlatGen p q z ≡ y` with `p, q : As ≡ As, Bs ≡ Bs` implies
  -- `z ≡ y`; UIP collapses `p, q` to `refl`.
  subst₂-eq-elim
    : ∀ {As Bs : List X} {x y : FlatGen As Bs}
        (p : As ≡ As) (q : Bs ≡ Bs)
    → subst₂ FlatGen p q x ≡ y → x ≡ y
  subst₂-eq-elim p q eq
    with UIP-ListX p refl | UIP-ListX q refl
  ... | refl | refl = eq

  -- `subst₂ FlatGen p q x ≡ subst₂ FlatGen p q y` implies `x ≡ y`,
  -- where `p, q` may witness equalities between any pair of lists.
  subst₂-injective
    : ∀ {As Bs Cs Ds : List X} {x y : FlatGen As Bs}
        (p : As ≡ Cs) (q : Bs ≡ Ds)
    → subst₂ FlatGen p q x ≡ subst₂ FlatGen p q y → x ≡ y
  subst₂-injective refl refl eq = eq

  flat-injective
    : ∀ {A B : ObjTerm} {f g : mor A B}
    → flat f ≡ flat g → f ≡ g
  flat-injective refl = refl

  Fin1-uniq : (x : Fin 1) → x ≡ zero
  Fin1-uniq zero = refl

  ≡⇒≈Term : ∀ {A B} {f g : HomTerm A B} → f ≡ g → f ≈Term g
  ≡⇒≈Term refl = ≈-Term-refl

--------------------------------------------------------------------------------
-- Main lemma.

decode-rel-resp-≅ᴴ-Agen-Agen
  : ∀ {A B} (g₁ g₂ : mor A B)
  → ⟪ Agen g₁ ⟫ ≅ᴴ ⟪ Agen g₂ ⟫
  → decode-rel (Agen g₁) ≈Term decode-rel (Agen g₂)
decode-rel-resp-≅ᴴ-Agen-Agen {A} {B} g₁ g₂ iso =
  ≡⇒≈Term (cong (λ z → bridge (Agen z)) g₁≡g₂)
  where
    open _≅ᴴ_ iso

    G = ⟪ Agen g₁ ⟫
    K = ⟪ Agen g₂ ⟫
    module G = Hypergraph G
    module K = Hypergraph K

    e₀ : Fin G.nE
    e₀ = zero

    -- ψ e₀ : Fin K.nE = Fin 1, so it is zero.
    ψ-zero : ψ e₀ ≡ zero
    ψ-zero = Fin1-uniq (ψ e₀)

    -- From the iso at e₀.
    elab-eq :
      subst₂ FlatGen (atom-ein e₀) (atom-eout e₀) (K.elab (ψ e₀))
      ≡ G.elab e₀
    elab-eq = ψ-elab e₀

    -- Rewrite K.elab (ψ e₀) to K.elab zero.
    elab-eq′ :
      subst₂ FlatGen (atom-ein e₀) (atom-eout e₀) (K.elab zero)
      ≡ G.elab e₀
    elab-eq′ = trans (cong (subst₂ FlatGen (atom-ein e₀) (atom-eout e₀))
                            (cong K.elab (sym ψ-zero)))
                     elab-eq

    -- Outer subst₂ peel: K.elab zero ≡ G.elab e₀.  Note `atom-ein e₀,
    -- atom-eout e₀ : (something) ≡ (same something)` because the type
    -- of `K.elab zero` and `G.elab e₀` reduce to the same FlatGen type
    -- once `vlab` is computed.
    K-elab-zero-eq-G-elab : K.elab zero ≡ G.elab e₀
    K-elab-zero-eq-G-elab =
      subst₂-eq-elim (atom-ein e₀) (atom-eout e₀) elab-eq′

    -- `K.elab zero = subst₂ FlatGen lem-in lem-out (flat g₂)` and
    -- `G.elab e₀ = subst₂ FlatGen lem-in lem-out (flat g₁)` definitionally
    -- (with the SAME `lem-in, lem-out`).  Apply subst₂-injective.
    flat-eq : flat g₂ ≡ flat g₁
    flat-eq = subst₂-injective _ _ K-elab-zero-eq-G-elab

    g₁≡g₂ : g₁ ≡ g₂
    g₁≡g₂ = sym (flat-injective flat-eq)
