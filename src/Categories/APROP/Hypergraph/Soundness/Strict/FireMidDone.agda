{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- FINAL ASSEMBLY of part (II)ˢ — the UNCONDITIONAL `fire-mid-interchangeˢ` and
-- `run-interchange₀ˢ`.
--
-- This closes the last gap of `Strict.FireMidS{,2,3}`/`Strict.FireMidFinish`:
-- the per-order located normal forms `nf-genˢ` (a single, block-symmetric
-- single-order chase, the strict twin of `BlockNFNf2.block-bracket-pf`),
-- instantiated for the two firing orders, then threaded through `cross-NFˢ`
-- with the proven `vin-cohˢ`/`vout-cohˢ` (FireMidS2) to give the both-fire
-- core `fire-mid-interchangeˢ`.  Instantiating `SwapCoreRun.RunInterchange`
-- with it yields the UNCONDITIONAL `run-interchange₀ˢ`.
--
-- {-# OPTIONS --safe --without-K #-}, zero postulates, zero holes.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.FireMidDone
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig using (X)

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Linearity sig using (Linear)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency
  using (Dep)

open import Categories.APROP.Hypergraph.Soundness.Strict.Decoder sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.PermSupport sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.SwapCore sig _≟X_
open import Categories.APROP.Hypergraph.Soundness.Strict.FireMidS sig _≟X_
  using (cross-NFˢ; box-resid3ˢ)
import Categories.APROP.Hypergraph.Soundness.Strict.FireMidS2 sig _≟X_ as F2

import Categories.APROP.Hypergraph.Soundness.Strict.PermK sig _≟X_ as PK
import Categories.APROP.Hypergraph.Soundness.Strict.SwapCoreRun sig _≟X_ as SCR
import Categories.APROP.Hypergraph.Soundness.Strict.BlockSwapComm sig _≟X_ as BSC
import Categories.APROP.Hypergraph.Soundness.Strict.DecodeSigmaS sig _≟X_ as DSS

import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.FireMidInterchangeComb sig
  as FMIC
import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig
  as SU
open import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.CountCombinatorics sig
  using (++-cancelˡ)

open import Data.Fin using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++; ++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  open StrictDecoder H

  permˢ-K : Support.PermK (Fin H.nV) vl
  permˢ-K = PK.permˢ-K (Fin H.nV) _≟F_ vl

  -- SwapCore brick aliases.
  fire-termˢ′  = fire-termˢ H dih lin
  perm-rigidˢ′ = perm-rigidˢ H dih lin permˢ-K
  perm-frameˡ′ = permuteˢ-frameˡ H dih lin

  cross-NFˢ′   = cross-NFˢ H dih lin
  box-resid3ˢ′ = box-resid3ˢ H dih lin

  block-swap-comm = BSC.block-swap-comm (Fin H.nV) H.vlab
  open DSS.Scr (Fin H.nV) H.vlab using (bswap)

  private
    m : List (Fin H.nV) → List X
    m = map vl

  FireMidInterchangeˢ : Set
  FireMidInterchangeˢ = SCR.FireMidInterchangeˢ H dih lin

  ----------------------------------------------------------------------
  -- Generic cast helpers (mirroring FireMidFinish).
  ----------------------------------------------------------------------
  private
    permuteˢ-reflexive
      : ∀ {xs ys : List (Fin H.nV)} (eq : xs ≡ ys)
      → permuteˢ (Perm.↭-reflexive eq) ≈ˢ castˢ refl (cong m eq) (idˢ {m xs})
    permuteˢ-reflexive refl = ≈-refl

    cast-idˡ-∘
      : ∀ {as bs cs : List X} (Q : bs ≡ cs) (f : HomS as bs)
      → castˢ refl Q (idˢ {bs}) ∘ˢ f ≈ˢ castˢ refl Q f
    cast-idˡ-∘ refl f = idˡ

    cast-idʳ-∘
      : ∀ {as cs ds : List X} (Q : as ≡ cs) (f : HomS cs ds)
      → f ∘ˢ castˢ refl Q (idˢ {as}) ≈ˢ castˢ (sym Q) refl f
    cast-idʳ-∘ refl f = idʳ

    -- The `++⁺ʳ Rl`-framed block-swap derivation is the strict block braiding
    -- `σˢ (m L) (m R) ⊗ˢ idˢ{m Rl}` (re-derivation of F2's private swap-block).
    swap-block
      : ∀ (L R Rl : List (Fin H.nV))
      → permuteˢ (PermProp.++⁺ʳ Rl (bswap L R))
        ≈ˢ castˢ (trans (cong (_++ m Rl) (sym (map-++ vl L R)))
                        (sym (map-++ vl (L ++ R) Rl)))
                 (trans (cong (_++ m Rl) (sym (map-++ vl R L)))
                        (sym (map-++ vl (R ++ L) Rl)))
            (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl})
    swap-block L R Rl =
      ≈-trans (cast-flip (map-++ vl (L ++ R) Rl) (map-++ vl (R ++ L) Rl)
                 (permuteˢ-frame Rl (bswap L R)))
        (≈-trans (cast-resp (sym (map-++ vl (L ++ R) Rl))
                            (sym (map-++ vl (R ++ L) Rl))
                   (≈-trans (⊗-resp (block-swap-comm L R) ≈-refl)
                     (≡⇒≈ˢ (cast-⊗ˡ (sym (map-++ vl L R)) (sym (map-++ vl R L))
                              (σˢ (m L) (m R))))))
          (≡⇒≈ˢ (cast-fuse (cong (_++ m Rl) (sym (map-++ vl L R)))
                           (sym (map-++ vl (L ++ R) Rl))
                           (cong (_++ m Rl) (sym (map-++ vl R L)))
                           (sym (map-++ vl (R ++ L) Rl))
                           (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl}))))

    -- swap-block flipped (re-derivation of F2's private swap-block-sym).
    swap-block-sym
      : ∀ (L R Rl : List (Fin H.nV))
      → σˢ (m L) (m R) ⊗ˢ idˢ {m Rl}
        ≈ˢ castˢ (trans (map-++ vl (L ++ R) Rl)
                        (cong (_++ m Rl) (map-++ vl L R)))
                 (trans (map-++ vl (R ++ L) Rl)
                        (cong (_++ m Rl) (map-++ vl R L)))
            (permuteˢ (PermProp.++⁺ʳ Rl (bswap L R)))
    swap-block-sym L R Rl =
      ≈-sym
        (≈-trans (cast-resp dom' cod' (swap-block L R Rl))
        (≈-trans (≡⇒≈ˢ (cast-fuse dom-i dom' cod-i cod'
                          (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl})))
          (≡⇒≈ˢ (cast-irrel (trans dom-i dom') refl (trans cod-i cod') refl
                            (σˢ (m L) (m R) ⊗ˢ idˢ {m Rl})))))
      where
        dom-i = trans (cong (_++ m Rl) (sym (map-++ vl L R)))
                      (sym (map-++ vl (L ++ R) Rl))
        cod-i = trans (cong (_++ m Rl) (sym (map-++ vl R L)))
                      (sym (map-++ vl (R ++ L) Rl))
        dom' = trans (map-++ vl (L ++ R) Rl) (cong (_++ m Rl) (map-++ vl L R))
        cod' = trans (map-++ vl (R ++ L) Rl) (cong (_++ m Rl) (map-++ vl R L))

    -- Pure-SMC box merge: the back box `g'` brought to front by the block
    -- braid `σ B A'`, applied after the front box `g`, equals the both-boxes
    -- morphism `g ⊗ g'` (front box on the LEFT) precomposed with the OUTPUT
    -- braid `σ B B'`.  K-free (σ-naturality + interchange); strict twin of
    -- `both-as-fire`'s `σ-nat-b` + `bifun`.
    box-merge-σˢ
      : ∀ {A B A' B' : List X} (g : HomS A B) (g' : HomS A' B')
      → (g' ⊗ˢ idˢ {B}) ∘ˢ (σˢ B A' ∘ˢ (g ⊗ˢ idˢ {A'}))
        ≈ˢ σˢ B B' ∘ˢ (g ⊗ˢ g')
    box-merge-σˢ {A} {B} {A'} {B'} g g' =
      -- regroup to `((g'⊗id{B}) ∘ σ B A') ∘ (g⊗id{A'})`
      ≈-trans (≈-sym assocˢ)
      -- σ-nat (flipped): (g'⊗id{B}) ∘ σ B A' ≈ σ B B' ∘ (id{B}⊗g')
      (≈-trans (∘-resp (≈-sym σ-natˢ) ≈-refl)
      -- reassoc to σ B B' ∘ ((id{B}⊗g') ∘ (g⊗id{A'}))
      (≈-trans assocˢ
        (∘-resp ≈-refl
          (≈-trans interchangeˢ (⊗-resp idˡ idʳ)))))

    -- A single located fire box (re-derivation of FireMidS3's private
    -- fire-locatedˢ).
    fire-locatedˢ
      : ∀ (e : Fin H.nE) (s rest C Rl : List (Fin H.nV))
          (perm : s Perm.↭ H.ein e ++ rest) (q : rest Perm.↭ C ++ Rl)
      → fire-termˢ′ e s rest perm
        ≈ˢ castˢ refl (sym (map-++ vl (H.eout e) rest))
            ( (idˢ {m (H.eout e)} ⊗ˢ permuteˢ (Perm.↭-sym q))
                ∘ˢ ( (genˢ (H.elab e) ⊗ˢ idˢ {m (C ++ Rl)})
                       ∘ˢ castˢ refl (map-++ vl (H.ein e) (C ++ Rl))
                            (permuteˢ (Perm.trans perm
                              (PermProp.++⁺ˡ (H.ein e) q))) ) )
    fire-locatedˢ e s rest C Rl perm q =
      cast-resp refl (sym (map-++ vl (H.eout e) rest))
        (≈-trans (∘-resp (box-resid3ˢ′ e {rest} {C} {Rl} q) ≈-refl)
        (≈-trans assocˢ
          (∘-resp ≈-refl (≈-trans assocˢ in-reconcile))))
      where
        in-reconcile
          : ( (genˢ (H.elab e) ⊗ˢ idˢ {m (C ++ Rl)})
                ∘ˢ ( (idˢ {m (H.ein e)} ⊗ˢ permuteˢ q)
                       ∘ˢ castˢ refl (map-++ vl (H.ein e) rest)
                            (permuteˢ perm) ) )
            ≈ˢ ( (genˢ (H.elab e) ⊗ˢ idˢ {m (C ++ Rl)})
                   ∘ˢ castˢ refl (map-++ vl (H.ein e) (C ++ Rl))
                        (permuteˢ (Perm.trans perm
                          (PermProp.++⁺ˡ (H.ein e) q))) )
        in-reconcile = ∘-resp ≈-refl step
          where
            CIN  = map-++ vl (H.ein e) rest
            CIN' = map-++ vl (H.ein e) (C ++ Rl)
            framed : castˢ CIN CIN' (permuteˢ (PermProp.++⁺ˡ (H.ein e) q))
                     ≈ˢ idˢ {m (H.ein e)} ⊗ˢ permuteˢ q
            framed = perm-frameˡ′ (H.ein e) q
            step
              : (idˢ {m (H.ein e)} ⊗ˢ permuteˢ q)
                  ∘ˢ castˢ refl CIN (permuteˢ perm)
                ≈ˢ castˢ refl CIN'
                     (permuteˢ (Perm.trans perm (PermProp.++⁺ˡ (H.ein e) q)))
            step =
              ≈-sym
                (≈-trans (∘-cast-split refl CIN CIN'
                            (permuteˢ (PermProp.++⁺ˡ (H.ein e) q))
                            (permuteˢ perm))
                  (∘-resp framed ≈-refl))

    -- `(X ∘ Y) ⊗ id{R} ≈ (X ⊗ id{R}) ∘ (Y ⊗ id{R})`.
    ⊗id-distˢ
      : ∀ {as bs cs : List X} {ls} (Xt : HomS bs cs) (Yt : HomS as bs)
      → (Xt ∘ˢ Yt) ⊗ˢ idˢ {ls} ≈ˢ (Xt ⊗ˢ idˢ {ls}) ∘ˢ (Yt ⊗ˢ idˢ {ls})
    ⊗id-distˢ Xt Yt = ≈-trans (⊗-resp ≈-refl (≈-sym idˡ)) (≈-sym interchangeˢ)

    -- `box-suffix-ˢ` flipped: `b ⊗ id{rest ++ R}` is the assoc-cast of
    -- `(b ⊗ id{rest}) ⊗ id{R}`.
    box-unsuffixˢ
      : ∀ {as bs : List X} (b : HomS as bs) (rest R : List X)
      → b ⊗ˢ idˢ {rest ++ R}
        ≈ˢ castˢ (++-assoc as rest R) (++-assoc bs rest R)
            ((b ⊗ˢ idˢ {rest}) ⊗ˢ idˢ {R})
    box-unsuffixˢ b rest R = ≈-sym (box-suffix-ˢ b rest R)

    -- The residual-framed box merge: the back box `g'` brought to front by
    -- `σ B A'` (framed by `Rl`) after the front box `g` (framed by `Rl`)
    -- equals `(g ⊗ g') ⊗ id{Rl}` with the OUTPUT braid `σ B B' ⊗ id{Rl}`.
    -- The block-bracketed box merge.  The two located boxes (front box `g`
    -- on residual `A' ++ Rl`, back box `g'` on residual `B ++ Rl`) with the
    -- mid block-swap `σ B A' ⊗ id{Rl}` reassociated between them collapse to
    -- the side-by-side `(g ⊗ g') ⊗ id{Rl}` with the OUTPUT block-swap
    -- `σ B B' ⊗ id{Rl}`.  The four `++-assoc` casts are the re-bracketings
    -- the located residuals (`A++(A'++Rl)`) and the block frame
    -- (`(A++A')++Rl`) differ by.  K-free.
    box-merge-Rˢ
      : ∀ {A B A' B' : List X} (g : HomS A B) (g' : HomS A' B') (Rl : List X)
      → (g' ⊗ˢ idˢ {B ++ Rl})
          ∘ˢ ( castˢ (++-assoc B A' Rl) (++-assoc A' B Rl)
                 (σˢ B A' ⊗ˢ idˢ {Rl})
               ∘ˢ (g ⊗ˢ idˢ {A' ++ Rl}) )
        ≈ˢ castˢ (++-assoc A A' Rl) (++-assoc B' B Rl)
            ( (σˢ B B' ⊗ˢ idˢ {Rl}) ∘ˢ ((g ⊗ˢ g') ⊗ˢ idˢ {Rl}) )
    box-merge-Rˢ {A} {B} {A'} {B'} g g' Rl =
      -- reframe the two outer boxes (box-suffix), so every factor is
      -- `(box ⊗ id{·}) ⊗ id{Rl}` at the uniform `(·)++Rl` bracketing, with
      -- the casts on each factor.  Then the inner composite is the bare merge
      -- tensored with `id{Rl}` (distributed), and the outer casts collect to
      -- the stated assoc casts.
      ≈-trans (∘-resp (≈-sym (box-suffix-ˢ g' B Rl)) ≈-refl)
      (≈-trans (∘-resp ≈-refl
                  (∘-resp ≈-refl (≈-sym (box-suffix-ˢ g A' Rl))))
      lemma)
      where
        -- The boxes are now (cast-of) `(·)⊗id{Rl}` blocks; the merge happens
        -- at the bare level via `box-merge-σˢ` distributed by `⊗id-distˢ`.
        cBg' = box-suffix-ˢ g' B Rl
        lemma
          : castˢ (++-assoc A' B Rl) (++-assoc B' B Rl)
              ((g' ⊗ˢ idˢ {B}) ⊗ˢ idˢ {Rl})
            ∘ˢ ( castˢ (++-assoc B A' Rl) (++-assoc A' B Rl)
                   (σˢ B A' ⊗ˢ idˢ {Rl})
                 ∘ˢ castˢ (++-assoc A A' Rl) (++-assoc B A' Rl)
                      ((g ⊗ˢ idˢ {A'}) ⊗ˢ idˢ {Rl}) )
            ≈ˢ castˢ (++-assoc A A' Rl) (++-assoc B' B Rl)
                ( (σˢ B B' ⊗ˢ idˢ {Rl}) ∘ˢ ((g ⊗ˢ g') ⊗ˢ idˢ {Rl}) )
        lemma =
          -- inner composite: pull the σ-block's domain cast against the
          -- g-box cast (both meet at `(B++A')++Rl`), giving the bare
          -- `σ B A' ∘ (g⊗id{A'})` tensored with id{Rl}.
          ≈-trans
            (∘-resp ≈-refl
              (≈-trans (≈-sym (∘-cast-split (++-assoc A A' Rl) (++-assoc B A' Rl)
                                 (++-assoc A' B Rl)
                                 (σˢ B A' ⊗ˢ idˢ {Rl})
                                 ((g ⊗ˢ idˢ {A'}) ⊗ˢ idˢ {Rl})))
                (cast-resp (++-assoc A A' Rl) (++-assoc A' B Rl)
                  (≈-sym (⊗id-distˢ (σˢ B A') (g ⊗ˢ idˢ {A'}))))))
          -- now: castₒ X ∘ castₗ (Y ⊗ id{Rl}), with X = (g'⊗id{B})⊗id{Rl},
          -- Y = σ B A' ∘ (g⊗id{A'}); fuse to a single cast over a composite.
          (≈-trans
            (≈-sym (∘-cast-split (++-assoc A A' Rl) (++-assoc A' B Rl)
                      (++-assoc B' B Rl)
                      ((g' ⊗ˢ idˢ {B}) ⊗ˢ idˢ {Rl})
                      ((σˢ B A' ∘ˢ (g ⊗ˢ idˢ {A'})) ⊗ˢ idˢ {Rl})))
          -- the composite under the cast: ((g'⊗id{B})⊗id{Rl}) ∘ (Y⊗id{Rl})
          -- = ((g'⊗id{B}) ∘ Y) ⊗ id{Rl} = Mbar ⊗ id{Rl}; merge + redistribute.
          (cast-resp (++-assoc A A' Rl) (++-assoc B' B Rl)
            (≈-trans (≈-sym (⊗id-distˢ (g' ⊗ˢ idˢ {B})
                               (σˢ B A' ∘ˢ (g ⊗ˢ idˢ {A'}))))
              (≈-trans (⊗-resp (box-merge-σˢ g g') ≈-refl)
                (⊗id-distˢ (σˢ B B') (g ⊗ˢ g'))))))

  ----------------------------------------------------------------------
  -- The generic, block-symmetric single-order located normal form
  -- `nf-genˢ` — the strict twin of `BlockNFNf2.block-bracket-pf`.
  --
  -- For two edges `a` (fired first) then `b`, located simultaneously by a
  -- shared residual `R` (the residual permutes `ρ₁ : s₁ ↭ ein b ++ R`,
  -- `ρ₂ : s₂ ↭ eout a ++ R`, and the block frames `loc`/`vout-loc`), the
  -- two-fire composite is the `cross-NFˢ`-shaped located form.
  ----------------------------------------------------------------------

  module Gen
    (a b : Fin H.nE)
    (sp : List (Fin H.nV))
    (s₁ : List (Fin H.nV)) (q-first  : sp Perm.↭ H.ein a ++ s₁)
    (s₂ : List (Fin H.nV)) (q-second : H.eout a ++ s₁ Perm.↭ H.ein b ++ s₂)
    (R  : List (Fin H.nV))
    (ρ₁ : s₁ Perm.↭ H.ein b ++ R) (ρ₂ : s₂ Perm.↭ H.eout a ++ R)
    (loc      : sp Perm.↭ (H.ein a ++ H.ein b) ++ R)
    (vout-loc : (H.eout a ++ H.eout b) ++ R Perm.↭ H.eout b ++ s₂)
    (us-in-a : Unique (H.ein a ++ s₁))
    (us-mid  : Unique (H.ein b ++ s₂))
    (us-cod  : Unique (H.eout b ++ s₂))
    where

    -- block abbreviations.
    A  = m (H.ein a)  ; A' = m (H.ein b)
    B  = m (H.eout a) ; B' = m (H.eout b)
    Rl = m R
    g  : HomS A B
    g  = genˢ (H.elab a)
    g' : HomS A' B'
    g' = genˢ (H.elab b)

    -- the two simultaneously-located firing permutes.
    loc1' : sp Perm.↭ H.ein a ++ (H.ein b ++ R)
    loc1' = Perm.trans q-first (PermProp.++⁺ˡ (H.ein a) ρ₁)
    loc2' : H.eout a ++ s₁ Perm.↭ H.ein b ++ (H.eout a ++ R)
    loc2' = Perm.trans q-second (PermProp.++⁺ˡ (H.ein b) ρ₂)

    -- the located firings (residuals to the shared `R`).
    T1-loc
      : fire-termˢ′ a sp s₁ q-first
        ≈ˢ castˢ refl (sym (map-++ vl (H.eout a) s₁))
            ( (idˢ {B} ⊗ˢ permuteˢ (Perm.↭-sym ρ₁))
                ∘ˢ ( (g ⊗ˢ idˢ {m (H.ein b ++ R)})
                       ∘ˢ castˢ refl (map-++ vl (H.ein a) (H.ein b ++ R))
                            (permuteˢ loc1') ) )
    T1-loc = fire-locatedˢ a sp s₁ (H.ein b) R q-first ρ₁

    T2-loc
      : fire-termˢ′ b (H.eout a ++ s₁) s₂ q-second
        ≈ˢ castˢ refl (sym (map-++ vl (H.eout b) s₂))
            ( (idˢ {B'} ⊗ˢ permuteˢ (Perm.↭-sym ρ₂))
                ∘ˢ ( (g' ⊗ˢ idˢ {m (H.eout a ++ R)})
                       ∘ˢ castˢ refl (map-++ vl (H.ein b) (H.eout a ++ R))
                            (permuteˢ loc2') ) )
    T2-loc = fire-locatedˢ b (H.eout a ++ s₁) s₂ (H.eout a) R q-second ρ₂

    ------------------------------------------------------------------
    -- The MID reconciliation: the sequential mid composite (T2's input
    -- after T1's output relocate) is the pure block-swap `midD`, then the
    -- strict block braiding `σ B A' ⊗ id{Rl}`.
    ------------------------------------------------------------------
    private
      midD : H.eout a ++ (H.ein b ++ R) Perm.↭ H.ein b ++ (H.eout a ++ R)
      midD = PermProp.shifts (H.eout a) (H.ein b)

      mid-comp : H.eout a ++ (H.ein b ++ R) Perm.↭ H.ein b ++ (H.eout a ++ R)
      mid-comp = Perm.trans (PermProp.++⁺ˡ (H.eout a) (Perm.↭-sym ρ₁)) loc2'

      -- `Unique (ein b ++ (eout a ++ R))` — the common mid codomain — from
      -- `us-mid : Unique (ein b ++ s₂)` through the residual relocate `ρ₂`.
      us-mid-img : Unique (H.ein b ++ (H.eout a ++ R))
      us-mid-img =
        SU.Unique-resp-↭ (PermProp.++⁺ˡ (H.ein b) ρ₂) us-mid

      mid-rigid : permuteˢ mid-comp ≈ˢ permuteˢ midD
      mid-rigid = perm-rigidˢ′ us-mid-img mid-comp midD

      -- midD as the strict block braid (re-derivation of FireMidFinish's
      -- private `midD-σ`).
      bridgeD : H.eout a ++ (H.ein b ++ R) Perm.↭ H.ein b ++ (H.eout a ++ R)
      bridgeD =
        Perm.trans (Perm.↭-reflexive (sym (++-assoc (H.eout a) (H.ein b) R)))
        (Perm.trans (PermProp.++⁺ʳ R (bswap (H.eout a) (H.ein b)))
                    (Perm.↭-reflexive (++-assoc (H.ein b) (H.eout a) R)))

      midD-bridge : permuteˢ midD ≈ˢ permuteˢ bridgeD
      midD-bridge = perm-rigidˢ′ us-mid-img midD bridgeD

      Dsb = trans (cong (_++ Rl) (sym (map-++ vl (H.eout a) (H.ein b))))
                  (sym (map-++ vl (H.eout a ++ H.ein b) R))
      Csb = trans (cong (_++ Rl) (sym (map-++ vl (H.ein b) (H.eout a))))
                  (sym (map-++ vl (H.ein b ++ H.eout a) R))
      Casl = cong m (sym (++-assoc (H.eout a) (H.ein b) R))
      Casr = cong m (++-assoc (H.ein b) (H.eout a) R)

      sb : permuteˢ (PermProp.++⁺ʳ R (bswap (H.eout a) (H.ein b)))
           ≈ˢ castˢ Dsb Csb (σˢ B A' ⊗ˢ idˢ {Rl})
      sb = swap-block (H.eout a) (H.ein b) R

      asl : permuteˢ (Perm.↭-reflexive (sym (++-assoc (H.eout a) (H.ein b) R)))
            ≈ˢ castˢ refl Casl (idˢ {m (H.eout a ++ (H.ein b ++ R))})
      asl = permuteˢ-reflexive (sym (++-assoc (H.eout a) (H.ein b) R))

      asr : permuteˢ (Perm.↭-reflexive (++-assoc (H.ein b) (H.eout a) R))
            ≈ˢ castˢ refl Casr (idˢ {m ((H.ein b ++ H.eout a) ++ R)})
      asr = permuteˢ-reflexive (++-assoc (H.ein b) (H.eout a) R)

      midD-σ
        : permuteˢ midD
          ≈ˢ castˢ (trans Dsb (sym Casl)) (trans Csb Casr)
              (σˢ B A' ⊗ˢ idˢ {Rl})
      midD-σ =
        ≈-trans midD-bridge
        (≈-trans (∘-resp (∘-resp asr sb) asl)
        (≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl
                    (≈-trans (cast-idʳ-∘ Casl (castˢ Dsb Csb (σˢ B A' ⊗ˢ idˢ {Rl})))
                      (≡⇒≈ˢ (cast-fuse Dsb (sym Casl) Csb refl
                               (σˢ B A' ⊗ˢ idˢ {Rl})))))
        (≈-trans (cast-idˡ-∘ Casr
                    (castˢ (trans Dsb (sym Casl)) (trans Csb refl) (σˢ B A' ⊗ˢ idˢ {Rl})))
        (≈-trans (≡⇒≈ˢ (cast-fuse (trans Dsb (sym Casl)) refl (trans Csb refl) Casr
                          (σˢ B A' ⊗ˢ idˢ {Rl})))
          (≡⇒≈ˢ (cast-irrel (trans (trans Dsb (sym Casl)) refl) (trans Dsb (sym Casl))
                            (trans (trans Csb refl) Casr) (trans Csb Casr)
                            (σˢ B A' ⊗ˢ idˢ {Rl}))))))))

    ------------------------------------------------------------------
    -- The mid composite: T2's input permute `IN2` after T1's output
    -- relocate `OUT1` (wrapped by T1's outer cast) is `permuteˢ mid-comp`
    -- (modulo the two `map-++` boundary casts).
    ------------------------------------------------------------------
    private
      -- T1's output relocate, wrapped by T1's outer cast proof.
      OUT1c : HomS (B ++ m (H.ein b ++ R)) (m (H.eout a ++ s₁))
      OUT1c = castˢ refl (sym (map-++ vl (H.eout a) s₁))
                (idˢ {B} ⊗ˢ permuteˢ (Perm.↭-sym ρ₁))

      IN2 : HomS (m (H.eout a ++ s₁)) (A' ++ m (H.eout a ++ R))
      IN2 = castˢ refl (map-++ vl (H.ein b) (H.eout a ++ R)) (permuteˢ loc2')

      Pmid = map-++ vl (H.eout a) (H.ein b ++ R)
      Cmid = map-++ vl (H.ein b) (H.eout a ++ R)

      -- `OUT1` as a cast of `permuteˢ (++⁺ˡ (eout a)(↭-sym ρ₁))`.
      out1-perm
        : castˢ (map-++ vl (H.eout a) (H.ein b ++ R)) (map-++ vl (H.eout a) s₁)
            (permuteˢ (PermProp.++⁺ˡ (H.eout a) (Perm.↭-sym ρ₁)))
          ≈ˢ idˢ {B} ⊗ˢ permuteˢ (Perm.↭-sym ρ₁)
      out1-perm = perm-frameˡ′ (H.eout a) (Perm.↭-sym ρ₁)

      mid-eq : IN2 ∘ˢ OUT1c ≈ˢ castˢ Pmid Cmid (permuteˢ mid-comp)
      mid-eq =
        -- OUT1c = castˢ refl (sym map++ eout a s₁) OUT1, OUT1 ≈ cast(out1-perm)
        ≈-trans (∘-resp ≈-refl
          (cast-resp refl (sym (map-++ vl (H.eout a) s₁)) (≈-sym out1-perm)))
        -- OUT1c ≈ castˢ Pmid refl (permuteˢ (++⁺ˡ (eout a)(↭-sym ρ₁)))
        (≈-trans (∘-resp ≈-refl
          (≈-trans (≡⇒≈ˢ (cast-fuse Pmid refl (map-++ vl (H.eout a) s₁)
                            (sym (map-++ vl (H.eout a) s₁))
                            (permuteˢ (PermProp.++⁺ˡ (H.eout a) (Perm.↭-sym ρ₁)))))
            (≡⇒≈ˢ (cast-irrel (trans Pmid refl) Pmid
                     (trans (map-++ vl (H.eout a) s₁) (sym (map-++ vl (H.eout a) s₁))) refl
                     (permuteˢ (PermProp.++⁺ˡ (H.eout a) (Perm.↭-sym ρ₁)))))))
        -- IN2 ∘ castˢ Pmid refl (permuteˢ U) = castˢ Pmid Cmid (permuteˢ loc2' ∘ permuteˢ U)
        (≈-trans (≈-sym (∘-cast-split Pmid refl Cmid (permuteˢ loc2')
                           (permuteˢ (PermProp.++⁺ˡ (H.eout a) (Perm.↭-sym ρ₁)))))
          ≈-refl))

    ------------------------------------------------------------------
    -- Named pieces of the two located firings.
    ------------------------------------------------------------------
    private
      OUT1 = idˢ {B} ⊗ˢ permuteˢ (Perm.↭-sym ρ₁)
      Boxa = g ⊗ˢ idˢ {m (H.ein b ++ R)}
      IN1  = castˢ refl (map-++ vl (H.ein a) (H.ein b ++ R)) (permuteˢ loc1')
      OUT2 = idˢ {B'} ⊗ˢ permuteˢ (Perm.↭-sym ρ₂)
      Boxb = g' ⊗ˢ idˢ {m (H.eout a ++ R)}
      castₒ₁ : HomS (B ++ m s₁) (m (H.eout a ++ s₁))
      castₒ₁ = castˢ refl (sym (map-++ vl (H.eout a) s₁)) idˢ
      castₒ₂out = sym (map-++ vl (H.eout b) s₂)

      -- (Step A) push the two outer casts together, exposing the mid
      -- `IN2 ∘ OUT1c` as a single inner factor.
      phase-cast
        : fire-termˢ′ b (H.eout a ++ s₁) s₂ q-second
            ∘ˢ fire-termˢ′ a sp s₁ q-first
          ≈ˢ castˢ refl castₒ₂out
              ( OUT2 ∘ˢ ( Boxb ∘ˢ ( (IN2 ∘ˢ OUT1c) ∘ˢ ( Boxa ∘ˢ IN1 ) ) ) )
      phase-cast =
        ≈-trans (∘-resp T2-loc T1-loc)
        -- castₒ₂[OUT2∘(Boxb∘IN2)] ∘ castₒ₁'[OUT1∘(Boxa∘IN1)]
        -- (1) distribute T1's outer cast onto OUT1 → OUT1c.
        (≈-trans (∘-resp ≈-refl
          (∘-cast-split refl refl (sym (map-++ vl (H.eout a) s₁))
            OUT1 (Boxa ∘ˢ IN1)))
        -- now: castₒ₂[…] ∘ (OUT1c ∘ (Boxa∘IN1))
        (≈-trans (≈-sym (∘-cast-split refl refl castₒ₂out
                           (OUT2 ∘ˢ (Boxb ∘ˢ IN2))
                           (OUT1c ∘ˢ (Boxa ∘ˢ IN1))))
        -- regroup inside to expose (IN2 ∘ OUT1c) between Boxb and Boxa.
        (cast-resp refl castₒ₂out regroup)))
        where
          regroup
            : (OUT2 ∘ˢ (Boxb ∘ˢ IN2)) ∘ˢ (OUT1c ∘ˢ (Boxa ∘ˢ IN1))
              ≈ˢ OUT2 ∘ˢ ( Boxb ∘ˢ ( (IN2 ∘ˢ OUT1c) ∘ˢ ( Boxa ∘ˢ IN1 ) ) )
          regroup =
            ≈-trans assocˢ
            (∘-resp ≈-refl
              (≈-trans assocˢ
                (∘-resp ≈-refl (≈-sym assocˢ))))

    ------------------------------------------------------------------
    -- The mid block-swap, with the `map-++` bridges from the located
    -- residuals (`m(ein b ++ R)`, `m(eout a ++ R)`) to the block forms
    -- (`A'++Rl`, `B++Rl`), so it matches `box-merge-Rˢ`'s σ-block frame.
    ------------------------------------------------------------------
    private
      mb-in  : m (H.ein b ++ R) ≡ A' ++ Rl
      mb-in  = map-++ vl (H.ein b) R
      mb-out : m (H.eout a ++ R) ≡ B ++ Rl
      mb-out = map-++ vl (H.eout a) R

      -- `IN2 ∘ OUT1c` rewritten to the bracketed σ-block frame that
      -- `box-merge-Rˢ` consumes (domain `B ++ (A'++Rl)`, codomain
      -- `A' ++ (B++Rl)`), via `mid-eq` + `mid-rigid` + `midD-σ` and the two
      -- `map-++` boundary bridges.
      midσ-tgt
        : HomS (B ++ (A' ++ Rl)) (A' ++ (B ++ Rl))
      midσ-tgt = castˢ (++-assoc B A' Rl) (++-assoc A' B Rl) (σˢ B A' ⊗ˢ idˢ {Rl})

      MID-eq
        : IN2 ∘ˢ OUT1c
          ≈ˢ castˢ (cong (B ++_) (sym mb-in)) (cong (A' ++_) (sym mb-out))
              midσ-tgt
      MID-eq =
        ≈-trans mid-eq
        (≈-trans (cast-resp Pmid Cmid (≈-trans mid-rigid midD-σ))
        -- fuse the `midD-σ` cast with `Pmid/Cmid`, then `cast-irrel` to the
        -- bracketed (map-++)-bridged frame `castˢ … midσ-tgt`.
        (≈-trans (≡⇒≈ˢ (cast-fuse (trans Dsb (sym Casl)) Pmid (trans Csb Casr) Cmid
                          (σˢ B A' ⊗ˢ idˢ {Rl})))
          (≈-trans
            (≡⇒≈ˢ (cast-irrel
                     (trans (trans Dsb (sym Casl)) Pmid)
                     (trans (++-assoc B A' Rl) (cong (B ++_) (sym mb-in)))
                     (trans (trans Csb Casr) Cmid)
                     (trans (++-assoc A' B Rl) (cong (A' ++_) (sym mb-out)))
                     (σˢ B A' ⊗ˢ idˢ {Rl})))
            (≈-sym (≡⇒≈ˢ (cast-fuse (++-assoc B A' Rl) (cong (B ++_) (sym mb-in))
                            (++-assoc A' B Rl) (cong (A' ++_) (sym mb-out))
                            (σˢ B A' ⊗ˢ idˢ {Rl})))))))

    ------------------------------------------------------------------
    -- The box bridges: the located boxes `g ⊗ id{m(ein b ++ R)}` /
    -- `g' ⊗ id{m(eout a ++ R)}` rewritten to the `_++Rl` block forms.
    ------------------------------------------------------------------
    private
      Boxa-br : Boxa ≈ˢ castˢ (sym (cong (A ++_) mb-in)) (sym (cong (B ++_) mb-in))
                          (g ⊗ˢ idˢ {A' ++ Rl})
      Boxa-br =
        cast-flip (cong (A ++_) mb-in) (cong (B ++_) mb-in)
          (≈-trans
            (cast-⊗-frame g mb-in mb-in (idˢ {m (H.ein b ++ R)})
              (cong (A ++_) mb-in) (cong (B ++_) mb-in))
            (⊗-resp ≈-refl (cast-id mb-in mb-in)))

      Boxb-br : Boxb ≈ˢ castˢ (sym (cong (A' ++_) mb-out)) (sym (cong (B' ++_) mb-out))
                          (g' ⊗ˢ idˢ {B ++ Rl})
      Boxb-br =
        cast-flip (cong (A' ++_) mb-out) (cong (B' ++_) mb-out)
          (≈-trans
            (cast-⊗-frame g' mb-out mb-out (idˢ {m (H.eout a ++ R)})
              (cong (A' ++_) mb-out) (cong (B' ++_) mb-out))
            (⊗-resp ≈-refl (cast-id mb-out mb-out)))

    ------------------------------------------------------------------
    -- The central merge: the two located boxes around the mid block-swap
    -- collapse, via `box-merge-Rˢ`, to the side-by-side block
    -- `(g ⊗ g') ⊗ id{Rl}` with the OUTPUT braid `σ B B' ⊗ id{Rl}`.
    ------------------------------------------------------------------
    private
      -- the cast endpoints of the merged central region.
      Dc = sym (cong (A ++_) mb-in)            -- A ++ (A'++Rl)  ← A ++ m(ein b++R)  (flipped)
      Cc = sym (cong (B' ++_) mb-out)          -- B' ++ (B++Rl)  ← B' ++ m(eout a++R)

      central-eq
        : Boxb ∘ˢ ( (IN2 ∘ˢ OUT1c) ∘ˢ Boxa )
          ≈ˢ castˢ Dc Cc
              ( castˢ (++-assoc A A' Rl) (++-assoc B' B Rl)
                  ( (σˢ B B' ⊗ˢ idˢ {Rl}) ∘ˢ ((g ⊗ˢ g') ⊗ˢ idˢ {Rl}) ) )
      central-eq =
        -- (1) substitute the box bridges + MID-eq.
        ≈-trans (∘-resp Boxb-br (∘-resp MID-eq Boxa-br))
        -- (2) collapse the inner two casts (midσ ∘ castₐ box-a) to a single
        --     cast over `midσ-tgt ∘ (g⊗id{A'++Rl})`.
        (≈-trans (∘-resp ≈-refl
          (≈-trans (∘-resp ≈-refl
            (≡⇒≈ˢ (cast-irrel (sym (cong (A ++_) mb-in)) (sym (cong (A ++_) mb-in))
                     (sym (cong (B ++_) mb-in)) (cong (B ++_) (sym mb-in))
                     (g ⊗ˢ idˢ {A' ++ Rl}))))
            (≈-sym (∘-cast-split (sym (cong (A ++_) mb-in))
                      (cong (B ++_) (sym mb-in)) (cong (A' ++_) (sym mb-out))
                      midσ-tgt (g ⊗ˢ idˢ {A' ++ Rl})))))
        -- (3) collapse the outer two casts (box-b ∘ castₘ …) → single cast.
        (≈-trans
          (≈-trans (∘-resp ≈-refl
            (≡⇒≈ˢ (cast-irrel (sym (cong (A ++_) mb-in)) (sym (cong (A ++_) mb-in))
                     (cong (A' ++_) (sym mb-out)) (sym (cong (A' ++_) mb-out))
                     (midσ-tgt ∘ˢ (g ⊗ˢ idˢ {A' ++ Rl})))))
            (≈-sym (∘-cast-split (sym (cong (A ++_) mb-in))
                      (sym (cong (A' ++_) mb-out)) (sym (cong (B' ++_) mb-out))
                      (g' ⊗ˢ idˢ {B ++ Rl})
                      (midσ-tgt ∘ˢ (g ⊗ˢ idˢ {A' ++ Rl})))))
        -- (4) the body is now `box-merge-Rˢ`'s LHS; merge.
        (cast-resp Dc Cc (box-merge-Rˢ g g' Rl))))

    ------------------------------------------------------------------
    -- The block frames `Lin`/`Lout` the `cross-NFˢ` consumer expects.
    ------------------------------------------------------------------
    in-mc  : m ((H.ein a ++ H.ein b) ++ R) ≡ (A ++ A') ++ Rl
    in-mc  = trans (map-++ vl (H.ein a ++ H.ein b) R)
                   (cong (_++ Rl) (map-++ vl (H.ein a) (H.ein b)))
    out-mc : m ((H.eout a ++ H.eout b) ++ R) ≡ (B ++ B') ++ Rl
    out-mc = trans (map-++ vl (H.eout a ++ H.eout b) R)
                   (cong (_++ Rl) (map-++ vl (H.eout a) (H.eout b)))

    Lin : HomS (m sp) ((A ++ A') ++ Rl)
    Lin = castˢ refl in-mc (permuteˢ loc)
    Lout : HomS ((B ++ B') ++ Rl) (m (H.eout b ++ s₂))
    Lout = castˢ out-mc refl (permuteˢ vout-loc)

    ------------------------------------------------------------------
    -- INPUT reconciliation: the located input `IN1` re-bracketed through
    -- the central casts equals the block frame `Lin` precomposing the
    -- box block `(g⊗g')⊗id{Rl}`.  (perm-rigidˢ at the `us-in-a`-image.)
    ------------------------------------------------------------------
    private
      -- `loc` carried DOWN to the `ein a ++ (ein b ++ R)` codomain (assoc).
      loc-down : sp Perm.↭ H.ein a ++ (H.ein b ++ R)
      loc-down = Perm.trans loc
                   (Perm.↭-reflexive (++-assoc (H.ein a) (H.ein b) R))

      us-down : Unique (H.ein a ++ (H.ein b ++ R))
      us-down = SU.Unique-resp-↭ (PermProp.++⁺ˡ (H.ein a) ρ₁) us-in-a

      loc-rigid : permuteˢ loc1' ≈ˢ permuteˢ loc-down
      loc-rigid = perm-rigidˢ′ us-down loc1' loc-down

    ------------------------------------------------------------------
    -- OUTPUT reconciliation: the located output `OUT2` together with the
    -- merge's output braid `σ B B' ⊗ id{Rl}` equals `Lout`.  (swap-block +
    -- perm-rigidˢ at `us-cod`, mirroring `F2.vout-cohˢ`.)
    ------------------------------------------------------------------
    private
      swp-out : (H.eout a ++ H.eout b) ++ R Perm.↭ (H.eout b ++ H.eout a) ++ R
      swp-out = PermProp.++⁺ʳ R (bswap (H.eout a) (H.eout b))

      -- `vout-loc` against `trans swp-out (the residual-relocate of OUT2)`.
      -- OUT2's permute is `↭-sym ρ₂ : eout a ++ R ↭ s₂`, framed by `eout b`.
      out-reloc : H.eout b ++ (H.eout a ++ R) Perm.↭ H.eout b ++ s₂
      out-reloc = PermProp.++⁺ˡ (H.eout b) (Perm.↭-sym ρ₂)

      vout-comp : (H.eout a ++ H.eout b) ++ R Perm.↭ H.eout b ++ s₂
      vout-comp =
        Perm.trans (Perm.trans swp-out
                      (Perm.↭-reflexive (++-assoc (H.eout b) (H.eout a) R)))
                   out-reloc

      vout-rigid : permuteˢ vout-comp ≈ˢ permuteˢ vout-loc
      vout-rigid = perm-rigidˢ′ us-cod vout-comp vout-loc

    ------------------------------------------------------------------
    -- box-block + the fused central input cast, reconciled to `box-block ∘ Lin`.
    ------------------------------------------------------------------
    private
      box-block = (g ⊗ˢ g') ⊗ˢ idˢ {Rl}
      σ-out     = σˢ B B' ⊗ˢ idˢ {Rl}
      PD = trans (++-assoc A A' Rl) Dc
      CD = trans (++-assoc B' B Rl) Cc

      C1 = map-++ vl (H.ein a) (H.ein b ++ R)

      -- `IN1` codomain carried to `(A++A')++Rl` (the box-block domain), so it
      -- is `Lin` up to `loc-rigid`.
      in-eq
        : castˢ PD refl box-block ∘ˢ IN1
          ≈ˢ box-block ∘ˢ Lin
      in-eq =
        ≈-trans (∘-resp ≈-refl IN1-eq)
          (≈-sym (∘-cast-split refl PD refl box-block Lin))
        where
          Casr-in = cong m (++-assoc (H.ein a) (H.ein b) R)
          -- `IN1 ≈ castˢ refl PD Lin`  (reconcile loc1' → loc).
          IN1-eq : IN1 ≈ˢ castˢ refl PD Lin
          IN1-eq =
            -- LHS: castˢ refl C1 (permuteˢ loc1')  →  loc-down (loc-rigid)
            ≈-trans (cast-resp refl C1 loc-rigid)
            -- castˢ refl C1 (permuteˢ loc-down),  permuteˢ loc-down ≈
            --   castˢ refl Casr-in id ∘ permuteˢ loc ≈ castˢ refl Casr-in (permuteˢ loc)
            (≈-trans (cast-resp refl C1
                        (≈-trans (∘-resp (permuteˢ-reflexive
                                            (++-assoc (H.ein a) (H.ein b) R)) ≈-refl)
                          (cast-idˡ-∘ Casr-in (permuteˢ loc))))
            -- fuse C1 with Casr-in, then cast-irrel to (trans in-mc PD).
            (≈-trans (≡⇒≈ˢ (cast-fuse refl refl Casr-in C1 (permuteˢ loc)))
              (≈-trans
                (≡⇒≈ˢ (cast-irrel refl refl (trans Casr-in C1) (trans in-mc PD)
                         (permuteˢ loc)))
                (≈-sym (≡⇒≈ˢ (cast-fuse refl refl in-mc PD (permuteˢ loc)))))))

      ------------------------------------------------------------------
      -- OUTPUT reconciliation: T2's output relocate `OUT2` + the merge's
      -- output braid `σ B B' ⊗ id{Rl}` (with T2's outer cast) = `Lout`.
      ------------------------------------------------------------------
      out-part = castˢ refl CD σ-out

      Dso = trans (map-++ vl (H.eout a ++ H.eout b) R)
                  (cong (_++ Rl) (map-++ vl (H.eout a) (H.eout b)))
      Cso = trans (map-++ vl (H.eout b ++ H.eout a) R)
                  (cong (_++ Rl) (map-++ vl (H.eout b) (H.eout a)))

      σ-out-perm : σ-out ≈ˢ castˢ Dso Cso (permuteˢ swp-out)
      σ-out-perm = swap-block-sym (H.eout a) (H.eout b) R

      Cob = map-++ vl (H.eout b) (H.eout a ++ R)
      Qob = map-++ vl (H.eout b) s₂
      out2-perm
        : castˢ Cob Qob (permuteˢ out-reloc)
          ≈ˢ idˢ {B'} ⊗ˢ permuteˢ (Perm.↭-sym ρ₂)
      out2-perm = perm-frameˡ′ (H.eout b) (Perm.↭-sym ρ₂)

      AssocO = ++-assoc (H.eout b) (H.eout a) R
      CasO   = cong m AssocO

      out-eq
        : castˢ refl (sym Qob) (OUT2 ∘ˢ out-part)
          ≈ˢ Lout
      out-eq =
        -- (1) OUT2 ← out2-perm,  σ-out → σ-out-perm.
        ≈-trans (cast-resp refl (sym Qob)
          (∘-resp (≈-sym out2-perm)
            (cast-resp refl CD σ-out-perm)))
        -- (2) fuse the σ-block's two inner casts; reconcile its cod proof to
        --     `trans CasO Cob` (cast-irrel) — i.e. route through the assoc;
        --     then UNfuse so the assoc cast `CasO` becomes a separate factor
        --     `permuteˢ (↭-refl AssocO)` (cast-of-id), and `Cob` is the σ-out
        --     side's boundary — matching `OUT2`'s domain boundary `Cob`.
        (≈-trans (cast-resp refl (sym Qob)
          (∘-resp ≈-refl σ-side))
        -- (3) glue the two `permuteˢ` factors (shared boundary `Cob`) into
        --     `permuteˢ vout-comp`, then absorb the outer cast, reconcile by
        --     `vout-rigid`, and recast to `Lout`.
        (≈-trans (cast-resp refl (sym Qob) glue)
        (≈-trans (≡⇒≈ˢ (cast-fuse Dso refl Qob (sym Qob) (permuteˢ vout-comp)))
        (≈-trans (≡⇒≈ˢ (cast-irrel (trans Dso refl) out-mc
                          (trans Qob (sym Qob)) refl (permuteˢ vout-comp)))
          (cast-resp out-mc refl vout-rigid)))))
        where
          -- the σ-out side, with the assoc bridge exposed.
          σ-side
            : castˢ refl CD (castˢ Dso Cso (permuteˢ swp-out))
              ≈ˢ castˢ Dso Cob
                  (permuteˢ (Perm.trans swp-out (Perm.↭-reflexive AssocO)))
          -- `castˢ refl CasO (permuteˢ swp-out)` ≈ `permuteˢ (trans swp-out
          -- (↭-refl AssocO))` (the assoc-appended permute, cast-of-id).
          assoc-append
            : castˢ refl CasO (permuteˢ swp-out)
              ≈ˢ permuteˢ (Perm.trans swp-out (Perm.↭-reflexive AssocO))
          assoc-append =
            ≈-sym
              (≈-trans (∘-resp (permuteˢ-reflexive AssocO) ≈-refl)
                (cast-idˡ-∘ CasO (permuteˢ swp-out)))

          σ-side =
            ≈-trans
              (≡⇒≈ˢ (cast-fuse Dso refl Cso CD (permuteˢ swp-out)))
            (≈-trans
              (≡⇒≈ˢ (cast-irrel (trans Dso refl) Dso (trans Cso CD)
                       (trans CasO Cob) (permuteˢ swp-out)))
            (≈-trans
              (≡⇒≈ˢ (cast-irrel Dso (trans refl Dso) (trans CasO Cob) (trans CasO Cob)
                       (permuteˢ swp-out)))
            (≈-trans
              (≈-sym (≡⇒≈ˢ (cast-fuse refl Dso CasO Cob (permuteˢ swp-out))))
              (cast-resp Dso Cob assoc-append))))

          -- glue: out-reloc-cast ∘ σ-side ≈ castˢ Dso Qob (permuteˢ vout-comp)
          glue
            : castˢ Cob Qob (permuteˢ out-reloc)
                ∘ˢ castˢ Dso Cob
                     (permuteˢ (Perm.trans swp-out (Perm.↭-reflexive AssocO)))
              ≈ˢ castˢ Dso Qob (permuteˢ vout-comp)
          glue =
            ≈-sym (∘-cast-split Dso Cob Qob (permuteˢ out-reloc)
                     (permuteˢ (Perm.trans swp-out (Perm.↭-reflexive AssocO))))

    ------------------------------------------------------------------
    -- THE SINGLE-ORDER LOCATED NORMAL FORM.
    ------------------------------------------------------------------
    private
      box-part = castˢ PD refl box-block
      central-split
        : castˢ Dc Cc
            ( castˢ (++-assoc A A' Rl) (++-assoc B' B Rl)
                ( σ-out ∘ˢ box-block ) )
          ≈ˢ out-part ∘ˢ box-part
      central-split =
        ≈-trans (≡⇒≈ˢ (cast-fuse (++-assoc A A' Rl) Dc (++-assoc B' B Rl) Cc
                         (σ-out ∘ˢ box-block)))
          (∘-cast-split PD refl CD σ-out box-block)

    nf-genˢ
      : fire-termˢ′ b (H.eout a ++ s₁) s₂ q-second
          ∘ˢ fire-termˢ′ a sp s₁ q-first
        ≈ˢ Lout ∘ˢ ( box-block ∘ˢ Lin )
    nf-genˢ =
      ≈-trans phase-cast
      (≈-trans (cast-resp refl (sym (map-++ vl (H.eout b) s₂)) inner)
        out-cast)
      where
        -- reassoc + central-eq + central-split + in-eq, all under castₒ₂.
        inner
          : OUT2 ∘ˢ ( Boxb ∘ˢ ( (IN2 ∘ˢ OUT1c) ∘ˢ ( Boxa ∘ˢ IN1 ) ) )
            ≈ˢ (OUT2 ∘ˢ out-part) ∘ˢ ( box-block ∘ˢ Lin )
        inner =
          -- regroup to `OUT2 ∘ ((Boxb ∘ ((IN2∘OUT1c)∘Boxa)) ∘ IN1)`.
          ≈-trans (∘-resp ≈-refl
            (≈-trans (∘-resp ≈-refl (≈-sym assocˢ)) (≈-sym assocˢ)))
          -- central-eq on `Boxb ∘ ((IN2∘OUT1c)∘Boxa)`.
          (≈-trans (∘-resp ≈-refl (∘-resp central-eq ≈-refl))
          -- central-split, then expose box-part ∘ IN1.
          (≈-trans (∘-resp ≈-refl (∘-resp central-split ≈-refl))
          (≈-trans (∘-resp ≈-refl assocˢ)
          -- in-eq: box-part ∘ IN1 ≈ box-block ∘ Lin.
          (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl in-eq))
            (≈-sym assocˢ)))))
        -- absorb castₒ₂ onto `OUT2 ∘ out-part`, then `out-eq`.
        out-cast
          : castˢ refl (sym (map-++ vl (H.eout b) s₂))
              ( (OUT2 ∘ˢ out-part) ∘ˢ ( box-block ∘ˢ Lin ) )
            ≈ˢ Lout ∘ˢ ( box-block ∘ˢ Lin )
        out-cast =
          ≈-trans
            (∘-cast-split refl refl (sym (map-++ vl (H.eout b) s₂))
              (OUT2 ∘ˢ out-part) (box-block ∘ˢ Lin))
            (∘-resp out-eq ≈-refl)

  ----------------------------------------------------------------------
  -- THE BOTH-FIRE INTERCHANGE CORE — UNCONDITIONAL.
  --
  -- The two per-order located normal forms `nf-genˢ` (instantiated for the
  -- `e`-first / `e'`-first orders at the shared `SimLoc` residual) are threaded
  -- through the proven `cross-NFˢ` with `F2`'s coherences `vin-cohˢ`/`vout-cohˢ`.
  ----------------------------------------------------------------------

  fire-mid-interchangeˢ : FireMidInterchangeˢ
  fire-mid-interchangeˢ {e} {e'} inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
                        us-sp us-mid₁ us-mid₂ us-cod =
    r-stk , goal
    where
      open F2.Located H dih lin inc sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' us-sp us-cod
      open FMIC.SimLoc
        (FMIC.sim-loc H dih lin (proj₁ inc) (proj₂ inc)
           sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁')
        using (Rlist; loc₁; loc₂; vout-loc₁; vout-loc₂; r-stk)

      -- The residual relocates, derived from the located permutes
      -- (block-prefix cancellation), at the shared `Rlist`.
      ρ₁-nf₁ : r₁ Perm.↭ H.ein e' ++ Rlist
      ρ₁-nf₁ = ++-cancelˡ (H.ein e)
                 (Perm.trans (Perm.↭-sym p₁)
                   (Perm.trans loc₁
                     (Perm.↭-reflexive (++-assoc (H.ein e) (H.ein e') Rlist))))
      ρ₂-nf₁ : r₂ Perm.↭ H.eout e ++ Rlist
      ρ₂-nf₁ = ++-cancelˡ (H.ein e')
                 (Perm.trans (Perm.↭-sym p₂)
                   (Perm.trans (PermProp.++⁺ˡ (H.eout e) ρ₁-nf₁) eo-shift₁))
        where
          eo-shift₁ : H.eout e ++ (H.ein e' ++ Rlist)
                      Perm.↭ H.ein e' ++ (H.eout e ++ Rlist)
          eo-shift₁ = PermProp.shifts (H.eout e) (H.ein e')

      ρ₁-nf₂ : r₂' Perm.↭ H.ein e ++ Rlist
      ρ₁-nf₂ = ++-cancelˡ (H.ein e')
                 (Perm.trans (Perm.↭-sym p₂')
                   (Perm.trans loc₂
                     (Perm.↭-reflexive (++-assoc (H.ein e') (H.ein e) Rlist))))
      ρ₂-nf₂ : r₁' Perm.↭ H.eout e' ++ Rlist
      ρ₂-nf₂ = ++-cancelˡ (H.ein e)
                 (Perm.trans (Perm.↭-sym p₁')
                   (Perm.trans (PermProp.++⁺ˡ (H.eout e') ρ₁-nf₂) eo-shift₂))
        where
          eo-shift₂ : H.eout e' ++ (H.ein e ++ Rlist)
                      Perm.↭ H.ein e ++ (H.eout e' ++ Rlist)
          eo-shift₂ = PermProp.shifts (H.eout e') (H.ein e)

      -- The `Unique` witnesses for the two orders, bridged from the caller's.
      us-in-a-nf₁ : Unique (H.ein e ++ r₁)
      us-in-a-nf₁ = SU.Unique-resp-↭ p₁ us-sp
      us-mid-nf₁ : Unique (H.ein e' ++ r₂)
      us-mid-nf₁ = SU.Unique-resp-↭ p₂ us-mid₁
      us-cod-nf₁ : Unique (H.eout e' ++ r₂)
      us-cod-nf₁ = SU.Unique-resp-↭ (Perm.↭-sym r-stk) us-cod

      us-in-a-nf₂ : Unique (H.ein e' ++ r₂')
      us-in-a-nf₂ = SU.Unique-resp-↭ p₂' us-sp
      us-mid-nf₂ : Unique (H.ein e ++ r₁')
      us-mid-nf₂ = SU.Unique-resp-↭ p₁' us-mid₂
      us-cod-nf₂ : Unique (H.eout e ++ r₁')
      us-cod-nf₂ = us-cod

      module G1 = Gen e e' sp r₁ p₁ r₂ p₂ Rlist ρ₁-nf₁ ρ₂-nf₁
                    loc₁ vout-loc₁ us-in-a-nf₁ us-mid-nf₁ us-cod-nf₁
      module G2 = Gen e' e sp r₂' p₂' r₁' p₁' Rlist ρ₁-nf₂ ρ₂-nf₂
                    loc₂ vout-loc₂ us-in-a-nf₂ us-mid-nf₂ us-cod-nf₂

      -- the two located normal forms (frames match `F2`'s Lin/Lout).
      nf₁-eqˢ
        : fire-termˢ′ e' (H.eout e ++ r₁) r₂ p₂ ∘ˢ fire-termˢ′ e sp r₁ p₁
          ≈ˢ Lout₁ ∘ˢ ( ((genˢ (H.elab e) ⊗ˢ genˢ (H.elab e')) ⊗ˢ idˢ {Rl})
                          ∘ˢ Lin₁ )
      nf₁-eqˢ = G1.nf-genˢ

      nf₂-eqˢ
        : fire-termˢ′ e (H.eout e' ++ r₂') r₁' p₁' ∘ˢ fire-termˢ′ e' sp r₂' p₂'
          ≈ˢ Lout₂ ∘ˢ ( ((genˢ (H.elab e') ⊗ˢ genˢ (H.elab e)) ⊗ˢ idˢ {Rl})
                          ∘ˢ Lin₂ )
      nf₂-eqˢ = G2.nf-genˢ

      -- the cross-NFˢ relation between the two orders.
      cross
        : ( Lout₂ ∘ˢ ( ((genˢ (H.elab e') ⊗ˢ genˢ (H.elab e)) ⊗ˢ idˢ {Rl})
                         ∘ˢ Lin₂ ) )
          ≈ˢ Pr ∘ˢ ( Lout₁ ∘ˢ ( ((genˢ (H.elab e) ⊗ˢ genˢ (H.elab e')) ⊗ˢ idˢ {Rl})
                                  ∘ˢ Lin₁ ) )
      cross = cross-NFˢ′ (genˢ (H.elab e)) (genˢ (H.elab e'))
                Lin₁ Lin₂ Lout₁ Lout₂ Pr vin-cohˢ vout-cohˢ

      goal
        : ( fire-termˢ′ e (H.eout e' ++ r₂') r₁' p₁'
              ∘ˢ fire-termˢ′ e' sp r₂' p₂' )
          ≈ˢ permuteˢ r-stk
                ∘ˢ ( fire-termˢ′ e' (H.eout e ++ r₁) r₂ p₂
                       ∘ˢ fire-termˢ′ e sp r₁ p₁ )
      goal =
        ≈-trans nf₂-eqˢ
        (≈-trans cross
          (∘-resp ≈-refl (≈-sym nf₁-eqˢ)))

  ----------------------------------------------------------------------
  -- THE UNCONDITIONAL EMPTY-TAIL TWO-EDGE INTERCHANGE `run-interchange₀ˢ`,
  -- obtained by instantiating `SwapCoreRun.RunInterchange` with the now-proven
  -- both-fire core `fire-mid-interchangeˢ`.
  ----------------------------------------------------------------------

  module RunInterchangeˢ =
    SCR.RunInterchange H dih lin fire-mid-interchangeˢ

  -- Re-export the headline result.
  open RunInterchangeˢ using (run-interchange₀ˢ; build) public

