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
-- (modulo the trivial `map-++ … []` casts), the final stack `s-finˢ ≡ cod`,
-- and `finalPermˢ : cod ↭ cod`.  Both locating permutations (`perm` and
-- `finalPermˢ`) collapse to identity via `perm-rigidˢ` on the `Unique`
-- codomain (the strict K-faithfulness consumption point), `idˢ {[]}` is
-- absorbed by `⊗-unitʳˢ`, and `genˢ (elab e₀)` is reconciled with
-- `genˢ (flat g)` by the `gen-cast` lemma plus the boundary `castˢ`s
-- `⟪⟫-domL`/`-codL`.
--
-- PROVEN HERE, postulate-free, holes-free, `--safe --without-K`; the concrete
-- `permˢ-K` (from `Strict.PermK`) is threaded directly (not as a parameter),
-- exactly as the σ-shape does.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeGen
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flat; flatten; hGen; domL-hGen; codL-hGen; retype-≡)
open import Categories.APROP.Hypergraph.Model.Translation sig
  using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig
  using (extract-prefix-self)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique
  sig using (Linear⇒cod-Unique)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  sig using (⟪⟫-LinearP)
open import Categories.APROP.Hypergraph.Model.Invariant sig using (hGen-dom-Unique)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using (st; coe)
import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermK sig _≟X_ as PK

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_) renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; map-++; ≡-dec)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ⁿ_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

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
    layer : HomS (map Hf.vlab Hf.dom) (map Hf.vlab (Hf.eout e₀ ++ []))
    layer = castˢ refl (sym (map-++ Hf.vlab (Hf.eout e₀) []))
              ((genˢ (Hf.elab e₀) ⊗ˢ idˢ {map Hf.vlab []})
                ∘ˢ castˢ refl (map-++ Hf.vlab (Hf.ein e₀) [])
                     (RF.permuteˢ selfP))

    -- `edge-stepˢ dom e₀` computes to (`eout e₀ ++ []`, `layer`).
    edge-form : RF.edge-stepˢ Hf.dom e₀ ≡ (Hf.eout e₀ ++ [] , layer)
    edge-form rewrite self-eq = refl

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
    md mc : List X
    md = map Hf.vlab Hf.dom          -- = map vlab (ein e₀)
    mc = map Hf.vlab Hf.cod          -- = map vlab (eout e₀)

    G0 : HomS md mc
    G0 = genˢ (Hf.elab e₀)

    -- `subst` over the codomain stack is a `castˢ refl …` (UIP-trivial).
    subst-cod≡cast
      : ∀ {a b b' : List X} (e : b ≡ b') (t : HomS a b)
      → subst (λ z → HomS a z) e t ≡ castˢ refl e t
    subst-cod≡cast refl t = refl

    subst-cod-cong
      : ∀ {u v v' : List (Fin Hf.nV)} (e : v ≡ v')
          (t : HomS (map Hf.vlab u) (map Hf.vlab v))
      → subst (λ z → HomS (map Hf.vlab u) (map Hf.vlab z)) e t
        ≡ subst (λ z → HomS (map Hf.vlab u) z) (cong (map Hf.vlab) e) t
    subst-cod-cong refl t = refl

  --------------------------------------------------------------------------
  -- Step A: `proj₂ runˢ ≈ castˢ refl (cong (map vlab) (sym s≡)) layer`.

  private
    run≈ : proj₂ RF.runˢ ≈ˢ castˢ refl (cong (map Hf.vlab) (sym s≡)) layer
    run≈ =
      ≈-trans (≡⇒≈ˢ (trans run-form
                       (trans (subst-cod-cong (sym s≡) (idˢ ∘ˢ layer))
                              (subst-cod≡cast
                                 (cong (map Hf.vlab) (sym s≡)) (idˢ ∘ˢ layer)))))
              (cast-resp refl (cong (map Hf.vlab) (sym s≡)) idˡ)

  --------------------------------------------------------------------------
  -- Step B: `layer ≈ castˢ … (G0 ∘ˢ permuteˢ selfP)` with `idˢ {[]}` killed.
  -- `map vlab [] = []`, so the framed `idˢ` is `idˢ {[]}` and `⊗-unitʳˢ`
  -- collapses `G0 ⊗ˢ idˢ {[]}` to `G0`.

  private
    -- `G0 ⊗ˢ idˢ {[]} ≈ castˢ (sym (++-identityʳ md)) (sym (++-identityʳ mc)) G0`
    g⊗id≈ : (G0 ⊗ˢ idˢ {[]})
            ≈ˢ castˢ (sym (++-identityʳ md)) (sym (++-identityʳ mc)) G0
    g⊗id≈ = cast-flip (++-identityʳ md) (++-identityʳ mc) (⊗-unitʳˢ G0)

    -- `permuteˢ selfP ≈ castˢ refl (cong (map vlab) (sym (++-identityʳ dom))) idˢ`
    -- (selfP : dom ↭ dom ++ [] killed against the reflexive derivation).
    uniqDom++ : Unique (Hf.dom ++ [])
    uniqDom++ = subst Unique (sym (++-identityʳ Hf.dom)) (hGen-dom-Unique g)

    refl-trivial
      : ∀ {xs ys : List (Fin Hf.nV)} (e : xs ≡ ys)
      → RF.permuteˢ (Perm.↭-reflexive e)
        ≈ˢ castˢ refl (cong (map Hf.vlab) e) (idˢ {map Hf.vlab xs})
    refl-trivial refl = ≈-refl

    selfP≈ : RF.permuteˢ selfP
             ≈ˢ castˢ refl (cong (map Hf.vlab) (sym (++-identityʳ Hf.dom)))
                  (idˢ {md})
    selfP≈ =
      ≈-trans (perm-rigidˢ K uniqDom++ selfP
                 (Perm.↭-reflexive (sym (++-identityʳ Hf.dom))))
              (refl-trivial (sym (++-identityʳ Hf.dom)))

  --------------------------------------------------------------------------
  -- Step C: collapse the layer to a single cast of `G0`.

  private
    -- the inner composite, with both factors replaced by casts of `G0`/`idˢ`.
    inner-layer≈
      : ((G0 ⊗ˢ idˢ {[]})
          ∘ˢ castˢ refl (map-++ Hf.vlab Hf.dom []) (RF.permuteˢ selfP))
        ≈ˢ castˢ refl (sym (++-identityʳ mc)) G0
    inner-layer≈ =
      ≈-trans
        (∘-resp g⊗id≈
          (≈-trans (cast-resp refl (map-++ Hf.vlab Hf.dom []) selfP≈)
          (≈-trans
            (≡⇒≈ˢ (cast-fuse refl refl
                     (cong (map Hf.vlab) (sym (++-identityʳ Hf.dom)))
                     (map-++ Hf.vlab Hf.dom []) (idˢ {md})))
            (≡⇒≈ˢ (cast-irrel refl refl
                     (trans (cong (map Hf.vlab) (sym (++-identityʳ Hf.dom)))
                            (map-++ Hf.vlab Hf.dom []))
                     (sym (++-identityʳ md)) (idˢ {md}))))))
      (≈-trans
        (≈-sym (∘-cast-split refl (sym (++-identityʳ md)) (sym (++-identityʳ mc))
                  G0 (idˢ {md})))
        (cast-resp refl (sym (++-identityʳ mc)) idʳ))

  --------------------------------------------------------------------------
  -- Step D: assemble `layer`, then the run term `proj₂ runˢ`.

  private
    Qℓ : mc ≡ map Hf.vlab (Hf.eout e₀ ++ [])
    Qℓ = trans (sym (++-identityʳ mc)) (sym (map-++ Hf.vlab (Hf.eout e₀) []))

    layer≈ : layer ≈ˢ castˢ refl Qℓ G0
    layer≈ =
      ≈-trans (cast-resp refl (sym (map-++ Hf.vlab (Hf.eout e₀) [])) inner-layer≈)
              (≡⇒≈ˢ (cast-fuse refl refl (sym (++-identityʳ mc))
                       (sym (map-++ Hf.vlab (Hf.eout e₀) [])) G0))

    Qrun : mc ≡ map Hf.vlab RF.s-finˢ
    Qrun = trans Qℓ (cong (map Hf.vlab) (sym s≡))

    run-term≈ : proj₂ RF.runˢ ≈ˢ castˢ refl Qrun G0
    run-term≈ =
      ≈-trans run≈
      (≈-trans (cast-resp refl (cong (map Hf.vlab) (sym s≡)) layer≈)
        (≡⇒≈ˢ (cast-fuse refl refl Qℓ (cong (map Hf.vlab) (sym s≡)) G0)))

  --------------------------------------------------------------------------
  -- Step E: kill `permuteˢ (finalPermˢ f)` via `perm-rigidˢ` into `Unique cod`.

  private
    sc : RF.s-finˢ ≡ Hf.cod
    sc = trans s≡ (++-identityʳ Hf.cod)

    finalP≈ : RF.permuteˢ (finalPermˢ f)
              ≈ˢ castˢ refl (cong (map Hf.vlab) sc) (idˢ {map Hf.vlab RF.s-finˢ})
    finalP≈ =
      ≈-trans (perm-rigidˢ K uniqCod (finalPermˢ f) (Perm.↭-reflexive sc))
              (refl-trivial sc)

  --------------------------------------------------------------------------
  -- Step F: the inner term `permuteˢ (finalPermˢ f) ∘ˢ proj₂ runˢ`.

  private
    -- `coe q ∘ˢ T ≈ castˢ refl q T` for a codomain coercion.
    coe-absorb
      : ∀ {a b c : List X} (q : b ≡ c) (T : HomS a b)
      → castˢ refl q (idˢ {b}) ∘ˢ T ≈ˢ castˢ refl q T
    coe-absorb q T =
      ≈-trans (≈-sym (∘-cast-split refl refl q (idˢ {_}) T))
              (cast-resp refl q idˡ)

    inner≈ : RF.permuteˢ (finalPermˢ f) ∘ˢ proj₂ RF.runˢ
             ≈ˢ castˢ refl (trans Qrun (cong (map Hf.vlab) sc)) G0
    inner≈ =
      ≈-trans (∘-resp finalP≈ run-term≈)
      (≈-trans (coe-absorb (cong (map Hf.vlab) sc) (castˢ refl Qrun G0))
        (≡⇒≈ˢ (cast-fuse refl refl Qrun (cong (map Hf.vlab) sc) G0)))

  --------------------------------------------------------------------------
  -- Step G: `genˢ (elab e₀) = genˢ (subst₂ FlatGen lem-in lem-out (flat g))`
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
  -- Step H: the full Agen shape.

  Qf : mc ≡ mc
  Qf = trans Qrun (cong (map Hf.vlab) sc)

  decodePˢ-Agen : decodePˢ f ≈ˢ st (Agen g)
  decodePˢ-Agen =
    ≈-trans (cast-resp (⟪⟫-domL f) (⟪⟫-codL f)
               (≈-trans inner≈ (cast-resp refl Qf G0≈)))
    (≈-trans (cast-resp (⟪⟫-domL f) (⟪⟫-codL f)
               (≡⇒≈ˢ (cast-fuse Pin refl Pout Qf (genˢ (flat g)))))
      (≈-trans (≡⇒≈ˢ (cast-fuse (trans Pin refl) (⟪⟫-domL f)
                        (trans Pout Qf) (⟪⟫-codL f) (genˢ (flat g))))
        (≡⇒≈ˢ (cast-irrel (trans (trans Pin refl) (⟪⟫-domL f)) refl
                          (trans (trans Pout Qf) (⟪⟫-codL f)) refl
                          (genˢ (flat g))))))

--------------------------------------------------------------------------------
-- The exported Agen shape (the part-(I)ˢ base case).

decodePˢ-Agen : ∀ {A B} (g : mor A B) → decodePˢ (Agen g) ≈ˢ st (Agen g)
decodePˢ-Agen g = Gen.decodePˢ-Agen g
