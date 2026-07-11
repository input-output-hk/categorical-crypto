{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-SHAPE of the strict decoder `decodePˢ` — the strict analogue of the
-- non-strict `DecodeAgenSigmaShape` (~1086 LOC).
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
-- `≈ˢ` fact `bswap-σ` (`Scr.BswapSig`), threaded as the module parameter
-- `BSwapσ` and discharged in `Strict/Interchange/BlockSwapComm.agda`.  Strict
-- vertex-level analogue of the non-strict keystone `BNV.σ-block-comm`.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph; domL; codL)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig
  using (FlatGen; flatten; range; map-lookup-range; hSwap)
open import Categories.APROP.Hypergraph.Model.Translation sig using (⟪_⟫; ⟪⟫-domL; ⟪⟫-codL)
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique
  sig using (Linear⇒cod-Unique)
open import Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  sig using (⟪⟫-LinearP)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.Boundary sig _≟X_
  using ( st; coe; coe-uip; coe-conj
        ; coe-cancel; coe-cancelʳ
        ; elim²; inv-uniqueˢ )

open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map; [_]; length; lookup)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++; map-∘; map-cong)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ⁿ_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

--------------------------------------------------------------------------------
-- The RIGHT hexagon: `σˢ a (b ++ c)` decomposed.  Derived from the `σ-hexˢ`
-- axiom by the same `inv-uniqueˢ` argument as `Braid`'s `hexagon` case (which
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
        (≈-trans assocˢ
          (∘-resp ≈-refl
            (∘-resp (≈-trans (coe-conj refl (sym R) W₂) (∘-resp ≈-refl idʳ))
                    (coe-uip (sym (sym Q)) Q))))))

    M-nest : L ∘ˢ coe (sym P) ≈ˢ X₂ ∘ˢ (coe R ∘ˢ (X₁ ∘ˢ coe (sym P)))
    M-nest = ≈-trans assocˢ (∘-resp ≈-refl assocˢ)

    cancel : σˢ (b ++ c) a ∘ˢ (coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))) ≈ˢ idˢ
    cancel =
      ≈-trans (∘-resp u-form ≈-refl)
      (≈-trans assocˢ
      (≈-trans (∘-resp ≈-refl assocˢ)
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (elim² (coe-cancelʳ Q)))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl assocˢ))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (∘-resp ≈-refl M-nest))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl
                 (∘-resp ≈-refl (elim² step-σʳ))))
      (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl (elim² (coe-cancel R))))
      (≈-trans (∘-resp ≈-refl (elim² step-σˡ))
        (coe-cancelʳ P))))))))))

    H : σˢ a (b ++ c) ≈ˢ coe (sym Q) ∘ˢ (L ∘ˢ coe (sym P))
    H = inv-uniqueˢ σ-σˢ cancel

--------------------------------------------------------------------------------
-- The canonical block-swap derivation + its `permuteˢ ≈ σˢ` identity (the
-- vertex-level keystone).  Recursion on the LEFT block.

module Scr (V : Set) (vlab : V → X) where
  open Support V vlab public

  bswap : (L R : List V) → (L ++ R) ↭ (R ++ L)
  bswap []      R = Perm.↭-reflexive (sym (++-identityʳ R))
  bswap (v ∷ L) R = Perm.trans (Perm.prep v (bswap L R)) (Perm.↭-sym (PermProp.shift v R L))

  refl-trivial
    : ∀ {xs ys : List V} (e : xs ≡ ys)
    → permuteˢ (Perm.↭-reflexive e)
      ≈ˢ castˢ refl (cong (map vlab) e) (idˢ {map vlab xs})
  refl-trivial refl = ≈-refl

  -- map-distribution endpoints of the shift braiding.
  mdom : (v : V) (R L : List V)
       → ((vlab v ∷ []) ++ map vlab R) ++ map vlab L
         ≡ vlab v ∷ map vlab (R ++ L)
  mdom v R L = sym (cong (vlab v ∷_) (map-++ vlab R L))

  mcod : (v : V) (R L : List V)
       → (map vlab R ++ (vlab v ∷ [])) ++ map vlab L
         ≡ map vlab (R ++ v ∷ L)
  mcod v R L = sym (trans (map-++ vlab R (v ∷ L))
                          (sym (++-assoc (map vlab R) (vlab v ∷ []) (map vlab L))))

  -- `permuteˢ (↭-sym (shift v R L))` is the braiding of `[vlab v]` past
  -- `map R`, framed by `idˢ {map L}` (modulo the map-distribution casts).
  -- BASE proven; the (x∷R) step is the σ-hexˢʳ reconciliation.
  permuteˢ-shift-sym-base
    : (v : V) (L : List V)
    → permuteˢ (Perm.↭-sym (PermProp.shift v [] L))
      ≈ˢ castˢ (mdom v [] L) (mcod v [] L)
          (σˢ (vlab v ∷ []) (map vlab []) ⊗ˢ idˢ {map vlab L})
  permuteˢ-shift-sym-base v L =
    ≈-sym
      (≈-trans (cast-resp (mdom v [] L) (mcod v [] L)
                  (⊗-resp (σ-unitʳˢ (vlab v ∷ [])) ≈-refl))
        (≈-trans (≡⇒≈ˢ (cast-⊗ˡ (sym (++-identityʳ (vlab v ∷ []))) refl idˢ))
          (≈-trans (≡⇒≈ˢ (cast-fuse _ (mdom v [] L) _ (mcod v [] L) (idˢ ⊗ˢ idˢ)))
            (≈-trans (cast-resp _ _ ⊗-id)
              (cast-id _ _)))))

  -- `permuteˢ (bswap L R) ≈ σˢ (map L) (map R)` (modulo map-distribution).
  -- BASE proven; the (v∷L) step is the σ-hexˢ reconciliation.
  bswap-σ-base
    : (R : List V)
    → permuteˢ (bswap [] R)
      ≈ˢ castˢ (sym (map-++ vlab [] R)) (sym (map-++ vlab R []))
          (σˢ (map vlab []) (map vlab R))
  bswap-σ-base R =
    ≈-trans (refl-trivial (sym (++-identityʳ R)))
    (≈-sym
      (≈-trans (cast-resp (sym (map-++ vlab [] R)) (sym (map-++ vlab R []))
                  (σ-unitˢ (map vlab R)))
        (≈-trans (≡⇒≈ˢ (cast-fuse refl (sym (map-++ vlab [] R))
                          (sym (++-identityʳ (map vlab R)))
                          (sym (map-++ vlab R [])) idˢ))
          (≡⇒≈ˢ (cast-irrel _ refl _ (cong (map vlab) (sym (++-identityʳ R)))
                   idˢ)))))

  -- The full block-swap identity (statement) — the strict vertex-level twin
  -- of `BNV.σ-block-comm`.  `bswap-σ-base` is the [] case.
  BswapSig : Set
  BswapSig =
    ∀ (L R : List V)
    → permuteˢ (bswap L R)
      ≈ˢ castˢ (sym (map-++ vlab L R)) (sym (map-++ vlab R L))
          (σˢ (map vlab L) (map vlab R))

--------------------------------------------------------------------------------
-- The σ-shape, assembled from `bswap-σ` (the single residual) via the
-- `nE ≡ 0` collapse and `perm-rigidˢ`.

module _
  (permˢ-K : ∀ (V : Set) (_≟V_ : DecidableEquality V) (vlab : V → X) → Support.PermK V vlab)
  (bswap-σ : ∀ (V : Set) (vlab : V → X) → Scr.BswapSig V vlab)
  where

  ------------------------------------------------------------------------
  -- `nE = 0` collapse (same as `DecodeShapes.nE0-run`).

  nE0-run
    : (H : Hypergraph FlatGen) → Hypergraph.nE H ≡ 0
    → Σ[ s≡ ∈ Run.s-finˢ H ≡ Hypergraph.dom H ]
        (proj₂ (Run.runˢ H)
         ≡ subst (λ z → HomS (map (Hypergraph.vlab H) (Hypergraph.dom H))
                              (map (Hypergraph.vlab H) z))
                 (sym s≡) idˢ)
  nE0-run
    record { nV = nV ; vlab = vlab ; nE = .0 ; ein = ein ; eout = eout
           ; elab = elab ; dom = dom ; cod = cod } refl = refl , refl

  ------------------------------------------------------------------------
  -- The σ-shape.

  module Sigma (A B : ObjTerm) where
    private
      f : HomTerm (A ⊗₀ B) (B ⊗₀ A)
      f = σ {A} {B}

      module RF = Run ⟪ f ⟫
      module Hf = Hypergraph ⟪ f ⟫
      open Support (Fin Hf.nV) Hf.vlab

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
      dom≡ : Hf.dom ≡ Lblk ++ Rblk
      dom≡ = refl

      cod≡ : Hf.cod ≡ Rblk ++ Lblk
      cod≡ = refl

      -- per-block vertex-label evaluations (re-derived as in FromAPROP).
      open import Data.Fin using (splitAt)
      open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
      open import Data.Sum using ([_,_]′)

      nA = length (flatten A)
      nB = length (flatten B)

      vlab-inL : ∀ (i : Fin nA) → Hf.vlab (i ↑ˡ nB) ≡ lookup (flatten A) i
      vlab-inL i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ˡ nA i nB)
      vlab-inR : ∀ (i : Fin nB) → Hf.vlab (nA ↑ʳ i) ≡ lookup (flatten B) i
      vlab-inR i = cong [ lookup (flatten A) , lookup (flatten B) ]′ (splitAt-↑ʳ nA nB i)

      mLblk≡ : map Hf.vlab Lblk ≡ flatten A
      mLblk≡ = trans (sym (map-∘ (range nA)))
                     (trans (map-cong vlab-inL (range nA))
                            (map-lookup-range (flatten A)))
      mRblk≡ : map Hf.vlab Rblk ≡ flatten B
      mRblk≡ = trans (sym (map-∘ (range nB)))
                     (trans (map-cong vlab-inR (range nB))
                            (map-lookup-range (flatten B)))

      -- the canonical derivation `dom ↭ cod`.
      bsw : Hf.dom ↭ Hf.cod
      bsw = Scr.bswap (Fin Hf.nV) Hf.vlab Lblk Rblk

      -- the algorithm's final permutation equals `bsw` under `permuteˢ`,
      -- by `perm-rigidˢ` into the `Unique` codomain (exactly where the
      -- non-strict proof invokes K-faithfulness).
      perm≈ : RF.permuteˢ (finalPermˢ f)
              ≈ˢ RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
      perm≈ = perm-rigidˢ K uniqCod (finalPermˢ f) (subst (Perm._↭ Hf.cod) (sym s≡) bsw)

    -- the block-swap identity at the hSwap blocks (the residual `bswap-σ`).
    σ-block-≈
      : RF.permuteˢ bsw
        ≈ˢ castˢ (sym (map-++ Hf.vlab Lblk Rblk))
                 (sym (map-++ Hf.vlab Rblk Lblk))
            (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))
    σ-block-≈ = bswap-σ (Fin Hf.nV) Hf.vlab Lblk Rblk

    private
      -- the run collapses to `coe` of the stack-equality (nE ≡ 0).
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

      run≡ : proj₂ RF.runˢ
             ≡ castˢ refl (cong (map Hf.vlab) (sym s≡)) (idˢ {map Hf.vlab Hf.dom})
      run≡ = trans (proj₂ collapse)
             (trans (subst-cod-cong (sym s≡) idˢ)
                    (subst-cod≡cast (cong (map Hf.vlab) (sym s≡)) idˢ))

      -- `permuteˢ` of the `s≡`-substituted canonical derivation is a cast of
      -- `permuteˢ bsw`.
      permsub≡ : RF.permuteˢ (subst (Perm._↭ Hf.cod) (sym s≡) bsw)
                 ≡ castˢ (cong (map Hf.vlab) (sym s≡)) refl (RF.permuteˢ bsw)
      permsub≡ = permuteˢ-subst-dom (sym s≡) bsw
        where
          -- permuteˢ of a domain-subst derivation (dom side) is a cast.
          permuteˢ-subst-dom
            : ∀ {xs xs' ys : List (Fin Hf.nV)} (e : xs ≡ xs') (p : xs ↭ ys)
            → RF.permuteˢ (subst (Perm._↭ ys) e p)
              ≡ castˢ (cong (map Hf.vlab) e) refl (RF.permuteˢ p)
          permuteˢ-subst-dom refl p = refl

    -- the inner term `permuteˢ (finalPermˢ σ) ∘ proj₂ runˢ` equals the
    -- block braiding (in vertex labels), modulo the run-collapse cast.
    private
      D0 : map Hf.vlab Lblk ++ map Hf.vlab Rblk ≡ map Hf.vlab RF.s-finˢ
      D0 = trans (sym (map-++ Hf.vlab Lblk Rblk)) (cong (map Hf.vlab) (sym s≡))

    inner≈
      : RF.permuteˢ (finalPermˢ f) ∘ˢ proj₂ RF.runˢ
        ≈ˢ castˢ D0 (sym (map-++ Hf.vlab Rblk Lblk))
            (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))
    inner≈ =
      ≈-trans (∘-resp perm≈ (≡⇒≈ˢ run≡))
      (≈-trans (∘-resp (≡⇒≈ˢ permsub≡) ≈-refl)
      (≈-trans (≈-sym (∘-cast-split (cong (map Hf.vlab) (sym s≡)) refl refl
                         (RF.permuteˢ bsw) idˢ))
        (≈-trans (cast-resp (cong (map Hf.vlab) (sym s≡)) refl idʳ)
          (≈-trans (cast-resp (cong (map Hf.vlab) (sym s≡)) refl σ-block-≈)
            (≈-trans
              (≡⇒≈ˢ (cast-fuse (sym (map-++ Hf.vlab Lblk Rblk))
                               (cong (map Hf.vlab) (sym s≡))
                               (sym (map-++ Hf.vlab Rblk Lblk)) refl
                               (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))))
              (≡⇒≈ˢ (cast-irrel _ D0 _ (sym (map-++ Hf.vlab Rblk Lblk))
                       (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk)))))))))

    private
      -- rewrite the block-label braiding to the `flatten` braiding; the cast
      -- endpoints fold to refl once the args are `flatten A`/`flatten B`.
      σblk≈ : castˢ (trans D0 (⟪⟫-domL f))
                    (trans (sym (map-++ Hf.vlab Rblk Lblk)) (⟪⟫-codL f))
                (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))
              ≈ˢ σˢ (flatten A) (flatten B)
      σblk≈ = go mLblk≡ mRblk≡ _ _
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
      (≈-trans (≡⇒≈ˢ (cast-fuse _ (⟪⟫-domL f) _ (⟪⟫-codL f)
                       (σˢ (map Hf.vlab Lblk) (map Hf.vlab Rblk))))
        (≈-trans (σblk≈)
          (≡⇒≈ˢ (cast-irrel _ refl _ refl
                   (σˢ (flatten A) (flatten B))))))

--------------------------------------------------------------------------------
-- The σ-shape is reduced to the single residual `bswap-σ` (`Scr.BswapSig`),
-- discharged in `Strict/Interchange/BlockSwapComm.agda` (the `[]` base is
-- `bswap-σ-base` here; the `(v ∷ L)` step is the σ-hexˢ reconciliation).  Fed
-- with `perm-rigidˢ` it collapses `finalPermˢ σ` onto `bswap`, giving
-- `decodePˢ (σ {A}{B}) ≈ σˢ (flatten A) (flatten B)`.
--------------------------------------------------------------------------------
