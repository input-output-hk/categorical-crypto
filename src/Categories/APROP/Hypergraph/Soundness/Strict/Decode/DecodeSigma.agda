{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-SHAPE of the strict decoder `decodePˢ`.
--
--   decodePˢ-σ : decodePˢ (σ {A}{B}) ≈ˢ σˢ (flatten A) (flatten B)
--
-- `⟪ σ {A}{B} ⟫ = hSwap A B` has `nE ≡ 0`, so (exactly as in
-- `DecodeShapes.Atom`) the run collapses to `idˢ` and `decodePˢ σ` reduces to
-- `castˢ (boundary) (permuteˢ (finalPermˢ σ))`.  `finalPermˢ σ` is a derivation
-- `dom(hSwap) ↭ cod(hSwap)` into the `Unique` codomain `cod`; via `perm-rigidˢ`
-- it is identified with the CANONICAL block-swap derivation `bswap Lblk Rblk`,
-- whose `permuteˢ` is the strict block braiding `σˢ` (`bswap-σ` below).
--
-- The two inductive steps `bswap-σ (v ∷ L)` / `permuteˢ-shift-sym v (x∷R)`
-- (the hexagon-reconciliation content) are reduced to the single clearly-typed
-- `≈ˢ` fact `bswap-σ` (`Scr.BswapSig`), threaded as a module parameter and
-- discharged in `Strict/Interchange/BlockSwapComm.agda`.  The
-- strict vertex-level block-swap-commutes keystone.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (flatten; range; module hGenSwap-impl)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Stack.StackUnique
  sig using (Linear⇒cod-Unique)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  sig using (⟪⟫-LinearP)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeShapes sig _≟X_
  as DShapes
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using ( coe; coe-uip; coe-conj
        ; coe-cancel; coe-cancelʳ )
open import Categories.Morphism.Reasoning SCat using (pullʳ; cancelˡ)
open import Categories.Morphism.Reasoning.Ext SCat using (inv-resp)

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- The RIGHT hexagon: `σˢ a (b ++ c)` decomposed.  Derived from the `σ-hexˢ`
-- axiom by the same inverse-uniqueness argument as `Braid`'s `hexagon` case (which
-- proves exactly this for `a,b,c = flatten _`); here generic on `List X`.

σ-hexˢʳ
  : ∀ (a b c : List X)
  → σˢ a (b ++ c)
    ≈ˢ coe (sym (++-assoc b c a))
        ∘ˢ (((idˢ {b} ⊗ˢ σˢ a c)
              ∘ˢ coe (++-assoc b a c) ∘ˢ (σˢ a b ⊗ˢ idˢ {c}))
            ∘ˢ coe (sym (++-assoc a b c)))
σ-hexˢʳ a b c = H
  where
    P = ++-assoc a b c
    Q = ++-assoc b c a
    R = ++-assoc b a c

    X₁ = σˢ a b ⊗ˢ idˢ {c}
    X₂ = idˢ {b} ⊗ˢ σˢ a c
    W₁ = σˢ b a ⊗ˢ idˢ {c}
    W₂ = idˢ {b} ⊗ˢ σˢ c a

    L : HomS ((a ++ b) ++ c) (b ++ c ++ a)
    L = X₂ ∘ˢ coe R ∘ˢ X₁

    step-σʳ : W₂ ∘ˢ X₂ ≈ˢ idˢ
    step-σʳ = ≈-trans interchangeˢ (≈-trans (⊗-resp idˡ σ-σˢ) ⊗-id)

    step-σˡ : W₁ ∘ˢ X₁ ≈ˢ idˢ
    step-σˡ = ≈-trans interchangeˢ (≈-trans (⊗-resp σ-σˢ idˡ) ⊗-id)

    u-form : σˢ (b ++ c) a ≈ˢ coe P ∘ˢ (W₁ ∘ˢ ((coe (sym R) ∘ˢ W₂) ∘ˢ coe Q))
    u-form =
      ≈-trans (σ-hexˢ b c a)
      (≈-trans (coe-conj (sym Q) P (W₁ ∘ˢ castˢ refl (sym R) W₂))
      (∘-resp ≈-refl
        (pullʳ (∘-resp (≈-trans (coe-conj refl (sym R) W₂) (∘-resp ≈-refl idʳ))
                       (coe-uip (sym (sym Q)) Q)))))

    M-nest : L ∘ˢ coe (sym P) ≈ˢ X₂ ∘ˢ (coe R ∘ˢ (X₁ ∘ˢ coe (sym P)))
    M-nest = pullʳ assocˢ

    cancel : σˢ (b ++ c) a ∘ˢ (coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))) ≈ˢ idˢ
    cancel =
      ≈-trans (∘-resp u-form ≈-refl)
      (≈-trans (pullʳ assocˢ)
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (cancelˡ (coe-cancelʳ Q)))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (∘-resp ≈-refl M-nest))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (cancelˡ step-σʳ))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (cancelˡ (coe-cancel R))))
      (≈-trans (∘-resp ≈-refl (cancelˡ step-σˡ))
        (coe-cancelʳ P)))))))))

    H : σˢ a (b ++ c) ≈ˢ coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))
    H = inv-resp σ-σˢ cancel ≈-refl

--------------------------------------------------------------------------------
-- The canonical block-swap derivation + its `permuteˢ ≈ σˢ` identity (the
-- vertex-level keystone).  Recursion on the LEFT block.

module Scr (V : Set) (vlab : V → X) where
  open Support V vlab public
  open DShapes.Trivial V vlab public
  open Restrict V vlab
    using (idᵛ; _⊗ᵛ_; σᵛ; _≈ᵛ_; permuteᵛ; castᵛ-cast; σ-unitᵛ)

  bswap : (L R : List V) → (L ++ R) ↭ (R ++ L)
  bswap []      R = Perm.↭-reflexive (sym (++-identityʳ R))
  bswap (v ∷ L) R = Perm.trans (Perm.prep v (bswap L R)) (Perm.↭-sym (PermProp.shift v R L))

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
-- The σ-shape, assembled from `bswap-σ` (the single residual) via the
-- `nE ≡ 0` collapse and `perm-rigidˢ`.

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) → Support.PermK V vlab)
  (bswap-σ : ∀ (V : Set) (vlab : V → X) → Scr.BswapSig V vlab)
  where

  ------------------------------------------------------------------------
  -- `nE = 0` collapse (shared with `DecodeShapes`).

  nE0-run = DShapes.nE0-run permˢ-K

  ------------------------------------------------------------------------
  -- The σ-shape.

  module Sigma (A B : ObjTerm) where
    private
      f : HomTerm (A ⊗₀ B) (B ⊗₀ A)
      f = σ {A} {B}

      module RF = Run ⟪ f ⟫
      module Hf = Hypergraph ⟪ f ⟫
      open Support (Fin Hf.nV) Hf.vlab
      open Restrict (Fin Hf.nV) Hf.vlab
        using (HomV; idᵛ; _∘ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ; ∘-castᵛ)

      K : PermK
      K = permˢ-K (Fin Hf.nV) _≟F_ Hf.vlab

      uniqCod : Unique Hf.cod
      uniqCod = Linear⇒cod-Unique ⟪ f ⟫ (⟪⟫-LinearP f)

      nE≡0 : Hf.nE ≡ 0
      nE≡0 = refl

      collapse = nE0-run ⟪ f ⟫ nE≡0
      s≡ : RF.s-finˢ ≡ Hf.dom
      s≡ = proj₁ collapse

      -- the canonical block-swap derivation, on the hSwap blocks.
      Lblk Rblk : List (Fin Hf.nV)
      Lblk = map (_↑ˡ length (flatten B)) (range (length (flatten A)))
      Rblk = map (length (flatten A) ↑ʳ_) (range (length (flatten B)))

      -- `Hf.dom = Lblk ++ Rblk`, `Hf.cod = Rblk ++ Lblk` (definitional).

      -- per-block vertex-label evaluations: `Hf.vlab` IS `hGenSwap-impl`'s
      -- `vlab-c` (`⟪ σ ⟫ = hSwap A B`), so its own `lem-L`/`lem-R` apply.
      open hGenSwap-impl A B using (lem-L; lem-R)

      -- the canonical derivation `dom ↭ cod`.
      bsw : Hf.dom ↭ Hf.cod
      bsw = Scr.bswap (Fin Hf.nV) Hf.vlab Lblk Rblk

      -- the algorithm's final permutation equals `bsw` under `permuteˢ`,
      -- by `perm-rigidˢ` into the `Unique` codomain (exactly where the
      -- non-strict proof invokes K-faithfulness).
      perm≈ : RF.permuteˢ (finalPermˢ f)
              ≈ˢ RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
      perm≈ = perm-rigidˢ K uniqCod (finalPermˢ f) (subst (Perm._↭ Hf.cod) (sym s≡) bsw)

    -- the block-swap identity at the hSwap blocks (the residual `bswap-σ`),
    -- V-level: `Hf.dom = Lblk ++ Rblk` and `Hf.cod = Rblk ++ Lblk` hold
    -- definitionally, so the braiding needs no frame cast.
    σ-block-≈ : RF.permuteˢ bsw ≈ᵛ σᵛ Lblk Rblk
    σ-block-≈ = bswap-σ (Fin Hf.nV) Hf.vlab Lblk Rblk

    private
      -- the run collapses to `coe` of the stack-equality (nE ≡ 0).
      subst-cod≡castᵛ
        : ∀ {u v v' : List (Fin Hf.nV)} (e : v ≡ v') (t : HomV u v)
        → subst (λ z → HomS (map Hf.vlab u) (map Hf.vlab z)) e t ≡ castᵛ refl e t
      subst-cod≡castᵛ refl t = refl

      run≡ : proj₂ RF.runˢ ≡ castᵛ refl (sym s≡) (idᵛ {Hf.dom})
      run≡ = trans (proj₂ collapse) (subst-cod≡castᵛ (sym s≡) idᵛ)

      -- `permuteᵛ` of the `s≡`-substituted canonical derivation is a `castᵛ`
      -- of `permuteᵛ bsw`.
      permsub≡ : RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
                 ≡ castᵛ (sym s≡) refl (permuteᵛ bsw)
      permsub≡ = permuteˢ-subst-dom (sym s≡) bsw
        where
          permuteˢ-subst-dom
            : ∀ {xs xs' ys : List (Fin Hf.nV)} (e : xs ≡ xs') (p : xs ↭ ys)
            → RF.permuteˢ (subst (Perm._↭ ys) e p)
              ≡ castᵛ e refl (permuteᵛ p)
          permuteˢ-subst-dom refl p = refl

    -- the inner term `permuteˢ (finalPermˢ σ) ∘ᵛ proj₂ runˢ` IS the block
    -- braiding: the two `s≡` transports meet at the collapsed run and cancel.
    inner≈ : RF.permuteˢ (finalPermˢ f) ∘ᵛ proj₂ RF.runˢ ≈ᵛ σᵛ Lblk Rblk
    inner≈ =
      ≈-trans (∘-resp (≈-trans perm≈ (≡⇒≈ˢ permsub≡)) (≡⇒≈ˢ run≡))
      (≈-trans (∘-castᵛ refl (sym s≡) refl (permuteᵛ bsw) idᵛ)
        (≈-trans idʳ σ-block-≈))

    private
      -- rewrite the block-label braiding to the `flatten` braiding; the cast
      -- endpoints fold to refl once the args are `flatten A`/`flatten B`.
      σblk≈ : castˢ (trans (sym (map-++ Hf.vlab Lblk Rblk)) (⟪⟫-domL f))
                    (trans (sym (map-++ Hf.vlab Rblk Lblk)) (⟪⟫-codL f))
                (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))
              ≈ˢ σˢ (flatten A) (flatten B)
      σblk≈ = go lem-L lem-R _ _
        where
          go : ∀ {ml mr} (eL : ml ≡ flatten A) (eR : mr ≡ flatten B)
                 (P : ml ++ mr ≡ flatten A ++ flatten B)
                 (Q : mr ++ ml ≡ flatten B ++ flatten A)
             → castˢ P Q (σˢ ml mr) ≈ˢ σˢ (flatten A) (flatten B)
          go refl refl P Q = ≡⇒≈ˢ (cast-irrel P refl Q refl (σˢ (flatten A) (flatten B)))

    -- the full σ-shape.
    decodePˢ-σ : decodePˢ f ≈ˢ σˢ (flatten A) (flatten B)
    decodePˢ-σ =
      ≈-trans (cast-resp (⟪⟫-domL f) (⟪⟫-codL f) inner≈)
      (≈-trans (≡⇒≈ˢ (cast-fuse (sym (map-++ Hf.vlab Lblk Rblk)) (⟪⟫-domL f)
                        (sym (map-++ Hf.vlab Rblk Lblk)) (⟪⟫-codL f)
                        (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))))
        σblk≈)

--------------------------------------------------------------------------------
-- The σ-shape is reduced to the single residual `bswap-σ` (`Scr.BswapSig`),
-- discharged in `Strict/Interchange/BlockSwapComm.agda` (the `[]` base is
-- `bswap-σ-base` here; the `(v ∷ L)` step is the σ-hexˢ reconciliation).  Fed
-- with `perm-rigidˢ` it collapses `finalPermˢ σ` onto `bswap`, giving
-- `decodePˢ (σ {A}{B}) ≈ σˢ (flatten A) (flatten B)`.
--------------------------------------------------------------------------------
