{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The Agen (single-generator) SHAPE of the strict decoder `decodePˢ` — the
-- base case of part (I)ˢ:
--
--   decodePˢ-Agen : decodePˢ (Agen g) ≈ˢ st (Agen g)   ( = genˢ (flat g) )
--
-- `⟪ Agen g ⟫ = hGen g` has `nE ≡ 1`, ONE edge `e₀` with `ein e₀ = dom`,
-- `eout e₀ = cod`, `elab e₀ = subst₂ FlatGen lem-in lem-out (flat g)`.  Since
-- `ein e₀ = dom`, `extract-prefix dom dom` returns the EMPTY residual (by
-- `extract-prefix-self`), so the single fired layer is
--
--     (genˢ (elab e₀) ⊗ˢ idˢ {[]}) ∘ˢ permuteˢ perm
--
-- the final stack `s-finˢ ≡ cod`, and `finalPermˢ : cod ↭ cod`.  The run is
-- assembled in the `Restrict` layer (F7): the fired layer is `firedᵛ e₀ []
-- selfP` (`edge-step-firedᵛ` strips its two `map-++ … []` casts), both
-- locating permutations (`selfP` and `finalPermˢ`) collapse to identity via
-- `perm-rigidˢ` on the `Unique` codomain (the strict K-faithfulness
-- consumption point), `idᵛ {[]}` is absorbed by `⊗-unitʳᵛ`, and
-- `genˢ (elab e₀)` is reconciled with `genˢ (flat g)` by the `gen-cast` lemma
-- plus the boundary `castˢ`s `⟪⟫-domL`/`-codL`.
--
-- PROVEN HERE, postulate-free, holes-free, `--safe --without-K`; the concrete
-- `permˢ-K` (from `Strict.Perm.PermK`) is threaded directly (not as a
-- parameter),
-- exactly as the σ-shape does.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeGen
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flat; flatten; hGen; domL-hGen; codL-hGen; retype-≡)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-self)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  sig using (Linear⇒cod-Unique)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  sig using (⟪⟫-LinearP)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (hGen-dom-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using (st)
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin) renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _++_; map)
open import Data.List.Properties using (++-identityʳ; map-++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

--------------------------------------------------------------------------------
-- The concrete strict residual at the (Fin nV)-vertex sets, threaded
-- directly (NOT as a parameter), exactly as the σ-shape uses `permˢ-K`.

permˢ-K : ∀ (n : ℕ) (vlab : Fin n → X) → Support.PermK (Fin n) vlab
permˢ-K n vlab = PK.permˢ-K (Fin n) (_≟F_) vlab

--------------------------------------------------------------------------------
-- `genˢ` commutes with `castˢ` (boundary transport of a generator), proven
-- definitionally (`refl refl`); the strict twin of `subst₂`-on-`flat`.

gen-cast
  : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') (x : FlatGen as bs)
  → castˢ p q (genˢ x) ≡ genˢ (subst₂ FlatGen p q x)
gen-cast refl refl x = refl

--------------------------------------------------------------------------------
-- The Agen shape.

module Gen {A B : ObjTerm} (g : mor A B) where
  private
    f : HomTerm A B
    f = Agen g

    module RF = Run ⟪ f ⟫
    module Hf = Hypergraph ⟪ f ⟫
    open Support (Fin Hf.nV) Hf.vlab
    open Restrict (Fin Hf.nV) Hf.vlab
      using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; castᵛ; _≈ᵛ_; permuteᵛ
            ; castᵛ-cast; cast-flipᵛ; cast-respᵛ; cast-fuseᵛ; ∘-castᵛ; ⊗-unitʳᵛ )

    K : PermK
    K = permˢ-K Hf.nV Hf.vlab

    uniqCod : Unique Hf.cod
    uniqCod = Linear⇒cod-Unique ⟪ f ⟫ (⟪⟫-LinearP f)

    -- the single edge.
    e₀ : Fin Hf.nE
    e₀ = Data.Fin.zero

    -- the empty-residual self-search of `dom`.
    selfP : Hf.dom Perm.↭ Hf.dom ++ []
    selfP = proj₁ (extract-prefix-self Hf.dom)

    self-eq : extract-prefix Hf.dom Hf.dom ≡ just ([] , selfP)
    self-eq = proj₂ (extract-prefix-self Hf.dom)

  private
    -- the fired single-edge layer, with the residual forced to `[]`.
    layer : HomV Hf.dom (Hf.eout e₀ ++ [])
    layer = castˢ refl (sym (map-++ Hf.vlab (Hf.eout e₀) []))
              ((genˢ (Hf.elab e₀) ⊗ˢ idˢ {map Hf.vlab []})
                ∘ˢ castˢ refl (map-++ Hf.vlab (Hf.ein e₀) [])
                     (RF.permuteˢ selfP))

    -- the whole run (one edge): stack and term.
    s≡ : RF.s-finˢ ≡ Hf.eout e₀ ++ []
    s≡ rewrite self-eq = refl

    run-form
      : proj₂ RF.runˢ
        ≡ subst (λ z → HomS (map Hf.vlab Hf.dom) (map Hf.vlab z))
                (sym s≡) (idˢ ∘ˢ layer)
    run-form rewrite self-eq = refl

  --------------------------------------------------------------------------
  -- Abbreviations.  `e₀`-indexed boundaries are definitional for `hGen`.

  private
    G0 : HomV (Hf.ein e₀) (Hf.eout e₀)
    G0 = genˢ (Hf.elab e₀)

    -- `subst` over the codomain stack is a `castᵛ refl …` (UIP-trivial).
    subst-cod≡castᵛ
      : ∀ {u v v' : List (Fin Hf.nV)} (e : v ≡ v') (t : HomV u v)
      → subst (λ z → HomS (map Hf.vlab u) (map Hf.vlab z)) e t ≡ castᵛ refl e t
    subst-cod≡castᵛ refl t = refl

    -- rigidity AT a reindexing (the V-level face of `rigid-≈̂ ⨾ ⟦reflexive⟧`).
    rigid-reflexiveᵛ
      : ∀ {xs ys : List (Fin Hf.nV)} → Unique ys
      → (p : xs Perm.↭ ys) (e : xs ≡ ys)
      → permuteᵛ p ≈ᵛ castᵛ refl e (idᵛ {xs})
    rigid-reflexiveᵛ u p refl = perm-rigidˢ K u p Perm.refl

  --------------------------------------------------------------------------
  -- Step A: `proj₂ runˢ ≈ᵛ castᵛ refl (sym s≡) layer`.

  private
    run≈ : proj₂ RF.runˢ ≈ᵛ castᵛ refl (sym s≡) layer
    run≈ =
      ≈-trans (≡⇒≈ˢ (trans run-form (subst-cod≡castᵛ (sym s≡) (idˢ ∘ˢ layer))))
              (cast-respᵛ refl (sym s≡) idˡ)

  --------------------------------------------------------------------------
  -- Step B: the layer collapses to a single cast of `G0`.  It is the fired
  -- layer `firedᵛ e₀ [] selfP` (`edge-step-firedᵛ`), whose box factor loses
  -- its empty frame by `⊗-unitʳᵛ` and whose permute is the reflexive
  -- derivation `dom ↭ dom ++ []` (rigidity at `Unique (dom ++ [])`).

  private
    Qℓ : Hf.eout e₀ ≡ Hf.eout e₀ ++ []
    Qℓ = sym (++-identityʳ (Hf.eout e₀))

    uniqDom++ : Unique (Hf.dom ++ [])
    uniqDom++ = subst Unique (sym (++-identityʳ Hf.dom)) (hGen-dom-Unique g)

    layer≈ : layer ≈ᵛ castᵛ refl Qℓ G0
    layer≈ =
      ≈-trans (RF.edge-step-firedᵛ e₀ [] selfP)
      (≈-trans (∘-resp box≈ perm≈)
      (≈-trans (∘-castᵛ refl (sym (++-identityʳ (Hf.ein e₀))) Qℓ G0 idᵛ)
        (cast-respᵛ refl Qℓ idʳ)))
      where
        box≈ : (G0 ⊗ᵛ idᵛ {[]})
               ≈ᵛ castᵛ (sym (++-identityʳ (Hf.ein e₀))) Qℓ G0
        box≈ =
          cast-flipᵛ (++-identityʳ (Hf.ein e₀)) (++-identityʳ (Hf.eout e₀))
            (⊗-unitʳᵛ G0)

        perm≈ : permuteᵛ selfP
                ≈ᵛ castᵛ refl (sym (++-identityʳ (Hf.ein e₀))) (idᵛ {Hf.ein e₀})
        perm≈ = rigid-reflexiveᵛ uniqDom++ selfP (sym (++-identityʳ Hf.dom))

  --------------------------------------------------------------------------
  -- Step C: the run term, then `permuteˢ (finalPermˢ f)` killed by
  -- `perm-rigidˢ` into `Unique cod`.

  private
    Qrun : Hf.eout e₀ ≡ RF.s-finˢ
    Qrun = trans Qℓ (sym s≡)

    run-term≈ : proj₂ RF.runˢ ≈ᵛ castᵛ refl Qrun G0
    run-term≈ =
      ≈-trans run≈
      (≈-trans (cast-respᵛ refl (sym s≡) layer≈)
        (≡⇒≈ˢ (cast-fuseᵛ refl refl Qℓ (sym s≡) G0)))

    sc : RF.s-finˢ ≡ Hf.cod
    sc = trans s≡ (++-identityʳ Hf.cod)

    -- `coe q ∘ᵛ T ≈ᵛ castᵛ refl q T` for a codomain coercion.
    coe-absorbᵛ
      : ∀ {u v w : List (Fin Hf.nV)} (q : v ≡ w) (T : HomV u v)
      → castᵛ refl q (idᵛ {v}) ∘ᵛ T ≈ᵛ castᵛ refl q T
    coe-absorbᵛ refl T = idˡ

    inner≈ : RF.permuteˢ (finalPermˢ f) ∘ᵛ proj₂ RF.runˢ
             ≈ᵛ castᵛ refl (trans Qrun sc) G0
    inner≈ =
      ≈-trans (∘-resp finalP≈ run-term≈)
      (≈-trans (coe-absorbᵛ sc (castᵛ refl Qrun G0))
        (≡⇒≈ˢ (cast-fuseᵛ refl refl Qrun sc G0)))
      where
        finalP≈ : RF.permuteˢ (finalPermˢ f)
                  ≈ᵛ castᵛ refl sc (idᵛ {RF.s-finˢ})
        finalP≈ = rigid-reflexiveᵛ uniqCod (finalPermˢ f) sc

  --------------------------------------------------------------------------
  -- Step D: `genˢ (elab e₀) = genˢ (subst₂ FlatGen lem-in lem-out (flat g))`
  -- and the boundary cast collapse to `genˢ (flat g) = st (Agen g)`.

  private
    -- the FlatGen boundary equalities baked into `hGen`'s `elab`.
    Pin : flatten A ≡ map Hf.vlab Hf.dom
    Pin = sym (domL-hGen g)

    Pout : flatten B ≡ map Hf.vlab Hf.cod
    Pout = sym (codL-hGen g)

    -- UIP-irrelevance of the two boundary proofs in a `subst₂ FlatGen`.
    subst₂-irrel
      : ∀ {as as' bs bs'} (p p' : as ≡ as') (q q' : bs ≡ bs') (x : FlatGen as bs)
      → subst₂ FlatGen p q x ≡ subst₂ FlatGen p' q' x
    subst₂-irrel p p' q q' x rewrite uipL p p' | uipL q q' = refl

    -- `G0 = genˢ (elab e₀)` is `genˢ (flat g)` cast along `Pin`/`Pout`
    -- (modulo UIP on the two `FlatGen`-boundary proofs).
    G0≈ : G0 ≈ˢ castˢ Pin Pout (genˢ (flat g))
    G0≈ = ≡⇒≈ˢ (trans G0-elab (sym (gen-cast Pin Pout (flat g))))
      where
        -- `elab e₀` (built as `retype … (flat g)`) and
        -- `subst₂ FlatGen Pin Pout (flat g)` agree: `retype-≡` collapses the
        -- record-rebuild to a `subst₂ FlatGen`, then UIP on the boundary
        -- indices realigns the proofs to `Pin`/`Pout`.
        G0-elab : G0 ≡ genˢ (subst₂ FlatGen Pin Pout (flat g))
        G0-elab = cong genˢ
          (trans (retype-≡ _ _ (flat g)) (subst₂-irrel _ Pin _ Pout (flat g)))

  --------------------------------------------------------------------------
  -- Step E: the full Agen shape.

  private
    Qf : List X
    Qf = map Hf.vlab Hf.cod

    Qfˢ : map Hf.vlab (Hf.eout e₀) ≡ Qf
    Qfˢ = cong (map Hf.vlab) (trans Qrun sc)

  decodePˢ-Agen : decodePˢ f ≈ˢ st (Agen g)
  decodePˢ-Agen =
    ≈-trans (cast-resp (⟪⟫-domL f) (⟪⟫-codL f)
               (≈-trans inner≈
                 (≈-trans (≡⇒≈ˢ (castᵛ-cast refl (trans Qrun sc) G0))
                          (cast-resp refl Qfˢ G0≈))))
    (≈-trans (cast-resp (⟪⟫-domL f) (⟪⟫-codL f)
               (≡⇒≈ˢ (cast-fuse Pin refl Pout Qfˢ (genˢ (flat g)))))
      (≈-trans (≡⇒≈ˢ (cast-fuse (trans Pin refl) (⟪⟫-domL f)
                        (trans Pout Qfˢ) (⟪⟫-codL f) (genˢ (flat g))))
        (≡⇒≈ˢ (cast-irrel (trans (trans Pin refl) (⟪⟫-domL f)) refl
                          (trans (trans Pout Qfˢ) (⟪⟫-codL f)) refl
                          (genˢ (flat g))))))

--------------------------------------------------------------------------------
-- The exported Agen shape (the part-(I)ˢ base case).

decodePˢ-Agen : ∀ {A B} (g : mor A B) → decodePˢ (Agen g) ≈ˢ st (Agen g)
decodePˢ-Agen g = Gen.decodePˢ-Agen g
