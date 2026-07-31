{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The K-block braid residual `KBlockσ` and its supporting lemmas, organised as
-- submodules TKB/TKB2/.../TKB6 (each carrying its own clash-free imports) plus
-- the top-level `KBlockDisjoint`.  `TensorKBlockFinal` stays separate to avoid
-- the `TensorBraid` import cycle.
--------------------------------------------------------------------------------

open import Categories.APROP
open import Relation.Binary using (DecidableEquality)

module Categories.APROP.Hypergraph.Soundness.Strict.Tensor.TensorKBlock
  (sig : APROPSignature)
  (_≟X_ : DecidableEquality (APROPSignature.X sig))
  where

open APROP sig

-- Hoisted (needed for every 'module TKBn (H : Hypergraph FlatGen)' header):
open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
-- Canonical Decoder alias for disambiguating 'open StrictDecoder':
import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decoder sig _≟X_ as Dec
-- The shared strict fired layer (`fire-termˢ`):
open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.EdgeStepRel sig _≟X_
  using (module EdgeStepView)

------------------------------------------------------------------------
-- The header shared verbatim by every `module TKBn (H : Hypergraph FlatGen)`:
-- the strict decoder + permute-support opens, the common stdlib vocabulary,
-- and the `H`/`Kmod`/`m` abbreviations.  Re-exported (`public`) so each
-- submodule replaces ~13 lines with `open TKBBase H` plus its own
-- specialised opens.  (The `Perm`/`PermProp` module aliases are re-exported
-- via `module _ = _`, since `import _ as _` aliases do not survive `open`.)
------------------------------------------------------------------------
module TKBBase (H : Hypergraph FlatGen) where
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.Decode sig _≟X_ public
  open import Categories.APROP.Hypergraph.Soundness.Strict.Perm.PermSupport sig _≟X_ public
  open import Data.Fin using (Fin) public
  open import Data.List using (List; []; _∷_; _++_; map) public
  open import Data.List.Properties using (map-++; ++-assoc) public
  open import Data.List.Relation.Unary.Unique.Propositional using (Unique) public
  open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂) public
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst) public
  import Data.List.Relation.Binary.Permutation.Propositional as PermI
  import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermPropI
  module Perm = PermI
  module PermProp = PermPropI
  open Perm using (_↭_) public

  module H = Hypergraph H

  open Dec.StrictDecoder H public

  module Kmod = Support (Fin H.nV) H.vlab

  m : List (Fin H.nV) → List X
  m = map vl

  --------------------------------------------------------------------
  -- The `idˢ{L}`-framed composite split (left-frame mirror of
  -- `FreeStrictSMC.⊗id-distˢ`; H-independent, so hoisted once here instead
  -- of being re-derived locally in both TKB2 and TKB4).
  --   idˢ{L} ⊗ˢ (g ∘ˢ f) ≈ (idˢ{L} ⊗ˢ g) ∘ˢ (idˢ{L} ⊗ˢ f)
  --------------------------------------------------------------------
  id⊗-distˢ
    : ∀ {as bs cs} (L : List X) (g : HomS bs cs) (f : HomS as bs)
    → idˢ {L} ⊗ˢ (g ∘ˢ f) ≈ˢ (idˢ {L} ⊗ˢ g) ∘ˢ (idˢ {L} ⊗ˢ f)
  id⊗-distˢ L g f = ≈-trans (⊗-resp (≈-sym idˡ) ≈-refl) (≈-sym interchangeˢ)

------------------------------------------------------------------------
-- ===== submodule TKB =====
------------------------------------------------------------------------
module TKB (H : Hypergraph FlatGen) where
  open TKBBase H

  ------------------------------------------------------------------------
  -- The strict fired layer (matching `edge-stepˢ`'s FIRE branch on the
  -- nose; shared via the `EdgeStepRel` leaf).
  ------------------------------------------------------------------------

  open EdgeStepView H public using (fire-termˢ)

  ------------------------------------------------------------------------
  -- ## The box-output left-slide (pure SMC, K-FREE).
  --
  -- The fired box's output block `genˢ ⊗ idˢ {L ++ rest}` (the box at the
  -- front, then the carried `L` and residual `rest`) equals the same box
  -- moved to AFTER `L` (`idˢ {L} ⊗ (genˢ ⊗ idˢ {rest})`) precomposed with
  -- the block braid `σˢ (map L) (map (eout e))` that swaps the box's output
  -- block past `L`.  Slide via `σ-natˢ`/`interchangeˢ`.
  ------------------------------------------------------------------------

  module _ (permˢ-K : Kmod.PermK) where
    open Kmod using (perm-rigidˢ)

    ----------------------------------------------------------------------
    -- ## The pure box left-slide (K-FREE).
    --
    -- The box `genˢ` with its residual `idˢ {map L ++ map rest}` to the
    -- right equals the box pushed to AFTER the carried block `map L`
    -- (`idˢ {map L} ⊗ˢ (genˢ ⊗ˢ idˢ {map rest})`), conjugated by the two
    -- one-sided block braids that swap the box's input / output block past
    -- `map L`.  Pure `σ-natˢ`/`interchangeˢ`; the maps are `m`-distributed.
    ----------------------------------------------------------------------

    private
      -- the σ-conjugation `g ⊗ idˢ{c} ≈ σ c b ∘ (idˢ{c} ⊗ g) ∘ σ a c`.
      box-conjˡ
        : ∀ {a b : List X} (g : HomS a b) (c : List X)
        → g ⊗ˢ idˢ {c} ≈ˢ σˢ c b ∘ˢ ((idˢ {c} ⊗ˢ g) ∘ˢ σˢ a c)
      box-conjˡ {a} {b} g c =
        ≈-sym
          (≈-trans (≈-sym assocˢ)
            (≈-trans (∘-resp σ-natˢ ≈-refl)
              (≈-trans assocˢ
                (≈-trans (∘-resp ≈-refl σ-σˢ) idʳ))))

    ----------------------------------------------------------------------
    -- ## `box-block-slideˢ` — the box residual-block slide with a right
    -- frame `R`.  The box `genˢ` carrying its full residual `(map L ++ R)`
    -- equals the box moved to AFTER the carried `map L`, conjugated by the
    -- output braid `σ (map L) B ⊗ idˢ{R}` and the input braid `σ A (map L) ⊗
    -- idˢ{R}` (`A = map ein e`, `B = map eout e`).  This is the genuine
    -- box-slide content.  K-FREE (`box-conjˡ` + `⊗id-distˢ`).
    ----------------------------------------------------------------------
    box-block-slideˢ
      : ∀ (e : Fin H.nE) (L : List (Fin H.nV)) (R : List X)
      → (genˢ (H.elab e) ⊗ˢ idˢ {m L}) ⊗ˢ idˢ {R}
        ≈ˢ ( (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {R})
               ∘ˢ ((idˢ {m L} ⊗ˢ genˢ (H.elab e)) ⊗ˢ idˢ {R}) )
             ∘ˢ (σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {R})
    box-block-slideˢ e L R =
      ≈-trans (⊗-resp (box-conjˡ (genˢ (H.elab e)) (m L)) ≈-refl)
        (≈-trans (⊗id-distˢ (σˢ (m L) (m (H.eout e)))
                   ((idˢ {m L} ⊗ˢ genˢ (H.elab e)) ∘ˢ σˢ (m (H.ein e)) (m L)))
          (≈-trans (∘-resp ≈-refl
                     (⊗id-distˢ (idˢ {m L} ⊗ˢ genˢ (H.elab e))
                               (σˢ (m (H.ein e)) (m L))))
            (≈-sym assocˢ)))

    ----------------------------------------------------------------------
    -- ## `box-slide-restˢ` — `box-block-slideˢ` lifted to the fired-layer
    -- residual `m (L ++ rest)`.  `box-suffix-ˢ` reframes `genˢ ⊗ idˢ {m L ++
    -- m rest}` into `(genˢ ⊗ idˢ {m L}) ⊗ idˢ {m rest}`; then
    -- `box-block-slideˢ e L (m rest)` slides the box past `m L`.  Pure cast
    -- kit + `box-block-slideˢ`.  K-FREE.
    ----------------------------------------------------------------------
    box-slide-restˢ
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → castˢ (cong (m (H.ein e) ++_) (map-++ vl L rest))
              (cong (m (H.eout e) ++_) (map-++ vl L rest))
          (genˢ (H.elab e) ⊗ˢ idˢ {m (L ++ rest)})
        ≈ˢ castˢ (++-assoc (m (H.ein e)) (m L) (m rest))
                 (++-assoc (m (H.eout e)) (m L) (m rest))
            ( ( (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest})
                  ∘ˢ ((idˢ {m L} ⊗ˢ genˢ (H.elab e)) ⊗ˢ idˢ {m rest}) )
                ∘ˢ (σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {m rest}) )
    box-slide-restˢ e L rest =
      ≈-trans
        (cast-⊗-frame (genˢ (H.elab e))
          (map-++ vl L rest) (map-++ vl L rest) (idˢ {m (L ++ rest)})
          (cong (m (H.ein e) ++_) (map-++ vl L rest))
          (cong (m (H.eout e) ++_) (map-++ vl L rest)))
      (≈-trans
        (⊗-resp ≈-refl (cast-id (map-++ vl L rest) (map-++ vl L rest)))
      (≈-trans
        (≈-sym (box-suffix-ˢ (genˢ (H.elab e)) (m L) (m rest)))
        (cast-resp (++-assoc (m (H.ein e)) (m L) (m rest))
                   (++-assoc (m (H.eout e)) (m L) (m rest))
                   (box-block-slideˢ e L (m rest)))))

------------------------------------------------------------------------
-- ===== submodule TKB2 =====
------------------------------------------------------------------------
module TKB2 (H : Hypergraph FlatGen) where
  open TKBBase H
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
    using (module Scr)
  import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.PermCalc sig _≟X_ as PC

  ------------------------------------------------------------------------
  -- The strict fired layer (matching `edge-stepˢ`'s FIRE branch on the
  -- nose; shared via the `EdgeStepRel` leaf).
  ------------------------------------------------------------------------

  open EdgeStepView H public using (fire-termˢ)

  module _ (permˢ-K : Kmod.PermK) where
    -- The thin wiring-groupoid calculus (F11): ⟦bswap⟧/⟦frameˡ⟧/⟦absorbˡ⟧ +
    -- rigid-≈̂.
    open PC.Kit H permˢ-K

    private
      module ScrH = Scr (Fin H.nV) H.vlab

    -- the canonical output block-braid: swap `L` past `eout e`, framed by
    -- `rest` on the right.  `(L ++ eout e) ++ rest ↭ (eout e ++ L) ++ rest`.
    obraid : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → ((L ++ H.eout e) ++ rest) Perm.↭ ((H.eout e ++ L) ++ rest)
    obraid e L rest = PermProp.++⁺ʳ rest (ScrH.bswap L (H.eout e))

    -- the canonical input block-braid: swap `ein e` past `L`, framed by
    -- `rest`.  `(ein e ++ L) ++ rest ↭ (L ++ ein e) ++ rest`.
    ibraid : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → ((H.ein e ++ L) ++ rest) Perm.↭ ((L ++ H.ein e) ++ rest)
    ibraid e L rest = PermProp.++⁺ʳ rest (ScrH.bswap (H.ein e) L)

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ`.
    --
    -- A single fired box on `L ++ xs` slides past the carried block `L`.
    -- The output block-braid is the canonical `permuteˢ (obraid e L rest)`;
    -- the input side reconciles `obraid`'s mate against the layer permute by
    -- `rigid-≈̂` on the `Unique` input stack `ein e ++ (L ++ rest)`.
    --
    -- (Decomposed: the box itself is `box-slide-restˢ′`; the two σ-blocks are
    -- bridged to `permuteˢ`s via `⟦bswap⟧` + `⟦frameˡ⟧`; the final permute
    -- reconciliation uses `rigid-≈̂`.)
    ----------------------------------------------------------------------

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ`.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ˢ castₒ (permuteˢ (obraid e L rest))
    --         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
    --
    -- where `castₒ` reframes the canonical output braid's endpoints onto the
    -- composite's.  Requires `Unique (ein e ++ L ++ rest)` (the layer's input
    -- multiset), supplied by linearity at the use site.
    ----------------------------------------------------------------------

    private
      gen' : ∀ (e : Fin H.nE) → HomS (m (H.ein e)) (m (H.eout e))
      gen' e = genˢ (H.elab e)

    -- The OUTPUT-braid reframing cast (assoc + map-distribution).
    odom : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((L ++ H.eout e) ++ rest) ≡ m L ++ m (H.eout e ++ rest)
    odom e L rest =
      trans (map-++ vl (L ++ H.eout e) rest)
        (trans (cong (_++ m rest) (map-++ vl L (H.eout e)))
          (trans (++-assoc (m L) (m (H.eout e)) (m rest))
            (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))))

    ocod : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((H.eout e ++ L) ++ rest) ≡ m (H.eout e ++ (L ++ rest))
    ocod e L rest =
      trans (map-++ vl (H.eout e ++ L) rest)
        (trans (cong (_++ m rest) (map-++ vl (H.eout e) L))
          (trans (++-assoc (m (H.eout e)) (m L) (m rest))
            (trans (cong (m (H.eout e) ++_) (sym (map-++ vl L rest)))
              (sym (map-++ vl (H.eout e) (L ++ rest))))))

    -- The MID box block `(idˢ{m L} ⊗ˢ genˢ) ⊗ˢ idˢ{m rest}` reassociates to
    -- `idˢ{m L} ⊗ˢ (genˢ ⊗ˢ idˢ{m rest})` (the box inside `idˢ{L} ⊗ fire`).
    mid-assoc
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → castˢ (++-assoc (m L) (m (H.ein e)) (m rest))
              (++-assoc (m L) (m (H.eout e)) (m rest))
          ((idˢ {m L} ⊗ˢ gen' e) ⊗ˢ idˢ {m rest})
        ≈ˢ idˢ {m L} ⊗ˢ (gen' e ⊗ˢ idˢ {m rest})
    mid-assoc e L rest = ⊗-assocˢ (idˢ {m L}) (gen' e) (idˢ {m rest})

    -- re-bracket `ein ++ (L ++ rest)` ⇝ `(ein ++ L) ++ rest`.
    brkIn : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → H.ein e ++ (L ++ rest) ≡ (H.ein e ++ L) ++ rest
    brkIn e L rest = sym (++-assoc (H.ein e) L rest)

    -- re-bracket `L ++ (ein ++ rest)` ⇝ `(L ++ ein) ++ rest`.
    brkL : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → L ++ (H.ein e ++ rest) ≡ (L ++ H.ein e) ++ rest
    brkL e L rest = sym (++-assoc L (H.ein e) rest)

    ----------------------------------------------------------------------
    -- ## The framed inner fire layer `FF = idˢ{m L} ⊗ˢ fire-termˢ e xs rest p`
    -- reduced to NF `castˢ (MID-frame ∘ (idˢ{L}⊗permuteˢ p))`.
    ----------------------------------------------------------------------

    -- FF reduced to `castˢ Pf Qf ((idˢ{L}⊗BOXx) ∘ (idˢ{L}⊗PERMx))`.
    framed-fire-split
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (p : xs Perm.↭ H.ein e ++ rest)
      → idˢ {m L} ⊗ˢ fire-termˢ e xs rest p
        ≈ˢ castˢ refl (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
            ( (idˢ {m L} ⊗ˢ (gen' e ⊗ˢ idˢ {m rest}))
              ∘ˢ (idˢ {m L} ⊗ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)) )
    framed-fire-split e L xs rest p =
      ≈-trans
        (≈-sym
          (cast-⊗-frame (idˢ {m L}) refl (sym (map-++ vl (H.eout e) rest))
            ((gen' e ⊗ˢ idˢ {m rest})
              ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p))
            (cong (m L ++_) refl) (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))))
      (≈-trans
        (≡⇒≈ˢ (cast-irrel (cong (m L ++_) refl) refl
                 (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
                 (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
                 (idˢ {m L} ⊗ˢ ((gen' e ⊗ˢ idˢ {m rest})
                   ∘ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)))))
        (cast-resp refl (cong (m L ++_) (sym (map-++ vl (H.eout e) rest)))
          (id⊗-distˢ (m L) (gen' e ⊗ˢ idˢ {m rest})
            (castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)))))

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ` — the single fired box slides past `L`.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ˢ castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
    --         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
    --
    -- Requires `Unique ((L ++ ein e) ++ rest)`.  The OUTPUT braid is the
    -- canonical block braid `obraid`; the input σ + layer permute collapse
    -- into the framed inner permute by `mid-in-canon`'s `in≈̂`.
    ----------------------------------------------------------------------

    -- The OUTPUT braid `castₒ (permuteˢ obraid)` reduced to the σ-block `OUT`.
    --   castˢ (odom)(ocod)(permuteˢ (obraid e L rest))
    --     ≈ castˢ ?? (σˢ (m L)(m eout) ⊗ˢ idˢ{m rest})
    out-braid-σ
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
        ≈ˢ castˢ (trans (trans (cong (_++ m rest) (sym (map-++ vl L (H.eout e))))
                               (sym (map-++ vl (L ++ H.eout e) rest)))
                        (odom e L rest))
                 (trans (trans (cong (_++ m rest) (sym (map-++ vl (H.eout e) L)))
                               (sym (map-++ vl (H.eout e ++ L) rest)))
                        (ocod e L rest))
            (σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest})
    out-braid-σ e L rest =
      ≈̂⇒≈ˢ (≈̂-trans cast-≈̂
              (≈̂-trans (⟦bswap⟧ L (H.eout e) rest) (≈̂-sym cast-≈̂)))


    ------------------------------------------------------------------
    -- The canonical composite both sides reduce to.
    --   OUT  = σˢ (m L)(m eout) ⊗ˢ idˢ{m rest}
    --   MIDᵢ = idˢ{m L} ⊗ˢ (gen' ⊗ˢ idˢ{m rest})
    --   INP  = idˢ{m L} ⊗ˢ castˢ refl (map-++ vl ein rest)(permuteˢ p)
    ------------------------------------------------------------------
    private
      OUTb : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomS ((m L ++ m (H.eout e)) ++ m rest) ((m (H.eout e) ++ m L) ++ m rest)
      OUTb e L rest = σˢ (m L) (m (H.eout e)) ⊗ˢ idˢ {m rest}

      -- the MID box in box-slide's native LEFT-assoc bracketing.
      MIDb : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomS ((m L ++ m (H.ein e)) ++ m rest) ((m L ++ m (H.eout e)) ++ m rest)
      MIDb e L rest = (idˢ {m L} ⊗ˢ gen' e) ⊗ˢ idˢ {m rest}

      MIDib : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
            → HomS (m L ++ m (H.ein e) ++ m rest) (m L ++ m (H.eout e) ++ m rest)
      MIDib e L rest = idˢ {m L} ⊗ˢ (gen' e ⊗ˢ idˢ {m rest})

      INPb : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
             (p : xs Perm.↭ H.ein e ++ rest)
           → HomS (m L ++ m xs) (m L ++ m (H.ein e) ++ m rest)
      INPb e L xs rest p = idˢ {m L} ⊗ˢ castˢ refl (map-++ vl (H.ein e) rest) (permuteˢ p)

    ------------------------------------------------------------------
    -- ## RHS reduction.
    --
    -- The RHS `castˢ (odom)(ocod)(permuteˢ obraid) ∘ˢ (idˢ{m L} ⊗ fire-termˢ)`
    -- reduces — via `out-braid-σ` (first factor → cast of OUT) and
    -- `framed-fire-split` (second factor → cast of MIDᵢ ∘ INP), then a single
    -- cast-fusion through the shared middle `m L ++ m(eout++rest)` — to
    -- `castˢ refl OC (OUT ∘ˢ (MIDᵢ ∘ˢ INP))`.
    ------------------------------------------------------------------

    private
      -- the OUTPUT codomain cast endpoint, as in `out-braid-σ`.
      OC : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (m (H.eout e) ++ m L) ++ m rest ≡ m (H.eout e ++ (L ++ rest))
      OC e L rest =
        trans (trans (cong (_++ m rest) (sym (map-++ vl (H.eout e) L)))
                     (sym (map-++ vl (H.eout e ++ L) rest)))
              (ocod e L rest)

      -- the codomain-cast `framed-fire-split` puts on its inner composite.
      QF : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m L ++ m (H.eout e) ++ m rest ≡ m L ++ m (H.eout e ++ rest)
      QF e L rest = cong (m L ++_) (sym (map-++ vl (H.eout e) rest))

    -- the assoc cast inserted between OUT and the right-assoc MIDᵢ∘INP.
    private
      ASout : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
            → m L ++ m (H.eout e) ++ m rest ≡ (m L ++ m (H.eout e)) ++ m rest
      ASout e L rest = sym (++-assoc (m L) (m (H.eout e)) (m rest))

    rhs-canon
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (p : xs Perm.↭ H.ein e ++ rest)
      → castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
          ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
        ≈ˢ castˢ refl (OC e L rest)
            (OUTb e L rest
              ∘ˢ castˢ refl (ASout e L rest)
                   (MIDib e L rest ∘ˢ INPb e L xs rest p))
    -- Heterogeneous rewrite (F8): `out-braid-σ`/`framed-fire-split` are chained
    -- in `≈̂`; `cast-≈̂` strips the OUT/QF casts and the QF↔ASout reassociation
    -- is a two-step `cast-≈̂`, so the former `∘-cast-split`/`cast-fuse`/`cast-irrel`
    -- endpoint plumbing (`OD`/`fuse`/`right-recast`) disappears.  Projected back
    -- to the byte-identical `castˢ`-shaped statement via `≈̂⇒≈ˢ`.
    rhs-canon e L xs rest p =
      ≈̂⇒≈ˢ (≈̂-trans
              (∘-resp-≈̂ (≈̂-trans (≈ˢ⇒≈̂ (out-braid-σ e L rest)) cast-≈̂)
                        (≈̂-trans (≈ˢ⇒≈̂ (framed-fire-split e L xs rest p)) qf→asout))
              (≈̂-sym cast-≈̂))
      where
        FF : HomS (m L ++ m xs) (m L ++ m (H.eout e) ++ m rest)
        FF = MIDib e L rest ∘ˢ INPb e L xs rest p

        -- the QF-reassociated inner composite equals the ASout-reassociated one
        -- (both strip to `FF` under `cast-≈̂`).
        qf→asout
          : castˢ refl (QF e L rest) FF ≈̂ castˢ refl (ASout e L rest) FF
        qf→asout = ≈̂-trans (cast-≈̂ {p = refl} {q = QF e L rest})
                           (≈̂-sym (cast-≈̂ {p = refl} {q = ASout e L rest}))

    ------------------------------------------------------------------
    -- ## LHS reduction.
    ------------------------------------------------------------------

    -- the box block-slide brick, inherited from TensorKBlock.
    box-slide-restˢ′ = TKB.box-slide-restˢ H permˢ-K

    private
      INσb : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomS ((m (H.ein e) ++ m L) ++ m rest) ((m L ++ m (H.ein e)) ++ m rest)
      INσb e L rest = σˢ (m (H.ein e)) (m L) ⊗ˢ idˢ {m rest}

      -- BOX as a back-cast of `(OUT ∘ MIDb) ∘ INσ` (box-slide-restˢ flipped,
      -- composed with the `cong (_ ++_)(map-++ L rest)` reframing flip).
      BOX : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → HomS (m (H.ein e) ++ m (L ++ rest)) (m (H.eout e) ++ m (L ++ rest))
      BOX e L rest = genˢ (H.elab e) ⊗ˢ idˢ {m (L ++ rest)}

    private
      Pi : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → m ((H.ein e ++ L) ++ rest) ≡ (m (H.ein e) ++ m L) ++ m rest
      Pi e L rest =
        sym (trans (cong (_++ m rest) (sym (map-++ vl (H.ein e) L)))
                   (sym (map-++ vl (H.ein e ++ L) rest)))

    ------------------------------------------------------------------
    -- ## MIDb → MIDib and INPb-core → INPb conversions.
    ------------------------------------------------------------------

    -- `idˢ{mL} ⊗ permuteˢ p` heterogeneously equal to `INPb` (the inner `castˢ`
    -- moved out of the ⊗ by `cast-⊗-frame`).
    inp-core→INPb
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (p : xs Perm.↭ H.ein e ++ rest)
      → (idˢ {m L} ⊗ˢ permuteˢ p) ≈̂ INPb e L xs rest p
    inp-core→INPb e L xs rest p =
        refl , cong (m L ++_) (map-++ vl (H.ein e) rest)
      , cast-⊗-frame (idˢ {m L}) refl (map-++ vl (H.ein e) rest) (permuteˢ p)
          refl (cong (m L ++_) (map-++ vl (H.ein e) rest))

    -- `MIDb` heterogeneously equal to `MIDib` (the `⊗-assocˢ` of `mid-assoc`).
    midb→midib
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → MIDb e L rest ≈̂ MIDib e L rest
    midb→midib e L rest =
        ++-assoc (m L) (m (H.ein e)) (m rest)
      , ++-assoc (m L) (m (H.eout e)) (m rest)
      , mid-assoc e L rest

    ------------------------------------------------------------------
    -- ## MID + IN reconciliation: the carried-block box composed with the
    -- input σ-block and layer permute collapses to the canonical
    -- `castˢ refl ASout (MIDib ∘ INPb)` (the RHS-canon inner-inner term).
    ------------------------------------------------------------------
    private
      INin : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
               (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
           → HomS (m (L ++ xs)) ((m (H.ein e) ++ m L) ++ m rest)
      INin e L xs rest perm' =
        castˢ refl (Pi e L rest)
          (castˢ refl (cong m (brkIn e L rest)) (permuteˢ perm'))

    mid-in-canon
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → MIDb e L rest ∘ˢ (INσb e L rest ∘ˢ INin e L xs rest perm')
        ≈ˢ castˢ (sym (map-++ vl L xs)) (ASout e L rest)
            (MIDib e L rest ∘ˢ INPb e L xs rest p)
    -- Heterogeneous rewrite (F1): the three sub-results are chained in `≈̂`,
    -- where transitivity/congruence absorb the endpoint bookkeeping, so the
    -- former `cast-fuse`/`cast-irrel`/`∘-cast-split`/`cast-irrel` reconciliation
    -- (the AFin'/AFout'/CFI endpoint plumbing) disappears; the final `≈̂⇒≈ˢ`
    -- projects back to the (byte-identical) `castˢ`-shaped statement.
    mid-in-canon e L xs rest perm' p uIn =
      ≈̂⇒≈ˢ (≈̂-trans (∘-resp-≈̂ (midb→midib e L rest)
                               (≈̂-trans in≈̂ (inp-core→INPb e L xs rest p)))
                    (≈̂-sym cast-≈̂))
      where
        -- The input σ-block after the (twice re-bracketed) layer permute, and
        -- the `L`-framed inner permute, are `permuteˢ` of two derivations into
        -- the SAME `Unique` stack (`uIn`): the wiring is rigid.  `cast-≈̂`
        -- strips both re-bracketing frames, `⟦absorbˡ⟧` absorbs the reindexing
        -- tails, `⟦bswap⟧` presents the σ-block and `⟦frameˡ⟧` the frame.
        in≈̂ : (INσb e L rest ∘ˢ INin e L xs rest perm') ≈̂ (idˢ {m L} ⊗ˢ permuteˢ p)
        in≈̂ =
          ≈̂-trans (∘-resp-≈̂ (≈̂-sym (⟦bswap⟧ (H.ein e) L rest))
                     (≈̂-trans (cast-≈̂ {p = refl} {q = Pi e L rest})
                       (≈̂-trans (cast-≈̂ {p = refl} {q = cong m (brkIn e L rest)})
                                (≈̂-sym (⟦absorbˡ⟧ (brkIn e L rest))))))
          (≈̂-trans
            (rigid-≈̂ uIn
              (Perm.trans (Perm.trans perm' (Perm.↭-reflexive (brkIn e L rest)))
                          (ibraid e L rest))
              (Perm.trans (PermProp.++⁺ˡ L p) (Perm.↭-reflexive (brkL e L rest))))
            (≈̂-trans (⟦absorbˡ⟧ (brkL e L rest)) (⟦frameˡ⟧ L p)))

    ------------------------------------------------------------------
    -- ## (b) `fire-slideˢ` — the gating brick.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ˢ castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
    --         ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p)
    --
    -- Requires `Unique ((L ++ ein e) ++ rest)`.  Both sides reduce to the
    -- canonical `castˢ refl OC (OUT ∘ˢ castˢ refl ASout (MIDib ∘ INPb))`:
    -- the LHS via `box-slide-restˢ′` + `mid-in-canon`, the RHS via
    -- `rhs-canon`.
    ------------------------------------------------------------------
    fire-slideˢ
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → fire-termˢ e (L ++ xs) (L ++ rest) perm'
        ≈ˢ castˢ (sym (map-++ vl L xs)) refl
            ( castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
                ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p) )
    -- Heterogeneous rewrite (F8): both the LHS (`fire-termˢ`, definitionally a
    -- `castˢ` of `BOX ∘ castP`) and the RHS reduce to the shared canonical
    -- `CANON`.  `cast-≈̂` strips every boundary cast content-first, so the LHS
    -- collapses via `box-slide-restˢ′` + two `assocˢ` + `mid-in-canon`, and the former
    -- `castP`/`INp`/`castP-recast`/`INp≡INin`/`Bd`/`Bc`/`SLID∘INp`-`slid-canon`/
    -- `reassoc-cast` cast-shuffle scaffold (the EXEC-5-skipped cast-first block)
    -- disappears: the domain `map-++` cast is never introduced, it is stripped.
    fire-slideˢ e L xs rest perm' p uIn =
      ≈̂⇒≈ˢ (≈̂-trans lhs≈̂canon (≈̂-sym rhs≈̂canon))
      where
        SLID : HomS ((m (H.ein e) ++ m L) ++ m rest) ((m (H.eout e) ++ m L) ++ m rest)
        SLID = (OUTb e L rest ∘ˢ MIDb e L rest) ∘ˢ INσb e L rest

        CANON : HomS (m L ++ m xs) ((m (H.eout e) ++ m L) ++ m rest)
        CANON = OUTb e L rest ∘ˢ castˢ refl (ASout e L rest) (MIDib e L rest ∘ˢ INPb e L xs rest p)

        -- BOX (heterogeneously) equals its slid composite SLID: `box-slide-restˢ′`
        -- with both its cast frames stripped by `cast-≈̂`.
        box≈̂SLID : BOX e L rest ≈̂ SLID
        box≈̂SLID =
          ≈̂-trans (≈̂-sym (cast-≈̂ {p = cong (m (H.ein e) ++_) (map-++ vl L rest)}
                                  {q = cong (m (H.eout e) ++_) (map-++ vl L rest)}))
                  (≈̂-trans (≈ˢ⇒≈̂ (box-slide-restˢ′ e L rest))
                           (cast-≈̂ {p = ++-assoc (m (H.ein e)) (m L) (m rest)}
                                   {q = ++-assoc (m (H.eout e)) (m L) (m rest)}))

        -- the raw input permute (= `fire-termˢ`'s FIRE-branch input) equals `INin`.
        castP≈̂INin
          : castˢ refl (map-++ vl (H.ein e) (L ++ rest)) (permuteˢ perm')
            ≈̂ INin e L xs rest perm'
        castP≈̂INin =
          ≈̂-trans (cast-≈̂ {p = refl} {q = map-++ vl (H.ein e) (L ++ rest)})
                  (≈̂-sym (≈̂-trans (cast-≈̂ {p = refl} {q = Pi e L rest})
                                  (cast-≈̂ {p = refl} {q = cong m (brkIn e L rest)})))

        -- MIDb ∘ (INσb ∘ INin) collapses to the canonical inner box, keeping only
        -- the ASout re-association cast (the domain `map-++` cast is stripped).
        mid-in-≈̂
          : (MIDb e L rest ∘ˢ (INσb e L rest ∘ˢ INin e L xs rest perm'))
            ≈̂ castˢ refl (ASout e L rest) (MIDib e L rest ∘ˢ INPb e L xs rest p)
        mid-in-≈̂ =
          ≈̂-trans (≈ˢ⇒≈̂ (mid-in-canon e L xs rest perm' p uIn))
                  (≈̂-trans (cast-≈̂ {p = sym (map-++ vl L xs)} {q = ASout e L rest})
                           (≈̂-sym (cast-≈̂ {p = refl} {q = ASout e L rest})))

        -- LHS: fire-termˢ ≈̂ BOX ∘ castP ≈̂ SLID ∘ INin ≈̂ CANON.
        lhs≈̂canon : fire-termˢ e (L ++ xs) (L ++ rest) perm' ≈̂ CANON
        lhs≈̂canon =
          ≈̂-trans (cast-≈̂ {p = refl} {q = sym (map-++ vl (H.eout e) (L ++ rest))})
          (≈̂-trans (∘-resp-≈̂ box≈̂SLID castP≈̂INin)
          (≈̂-trans (≈ˢ⇒≈̂ assocˢ)
          (≈̂-trans (≈ˢ⇒≈̂ assocˢ)
                   (∘-resp-≈̂ ≈̂-refl mid-in-≈̂))))

        -- RHS: strip the outer `map-++` cast, apply `rhs-canon`, strip its cast.
        rhs≈̂canon
          : castˢ (sym (map-++ vl L xs)) refl
              ( castˢ (odom e L rest) (ocod e L rest) (permuteˢ (obraid e L rest))
                  ∘ˢ (idˢ {m L} ⊗ˢ fire-termˢ e xs rest p) )
            ≈̂ CANON
        rhs≈̂canon =
          ≈̂-trans (cast-≈̂ {p = sym (map-++ vl L xs)} {q = refl})
                  (≈̂-trans (≈ˢ⇒≈̂ (rhs-canon e L xs rest p))
                           (cast-≈̂ {p = refl} {q = OC e L rest}))

------------------------------------------------------------------------
-- ===== submodule TKB4 =====
------------------------------------------------------------------------
module TKB4 (H : Hypergraph FlatGen) where
  open TKBBase H
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
    using (module EquivStep)
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
  open import Data.List.Relation.Unary.All using (All; []; _∷_)

  open Run H using (edge-stack-agree)
  open EquivStep H using (pvv-transˢ)

  module _ (permˢ-K : Kmod.PermK) where
    perm-rigidˢ = Kmod.perm-rigidˢ permˢ-K

    ----------------------------------------------------------------------
    -- ## The clean K-block frame.
    --
    -- `KCleanˢ es L s_R` is the clean target `idˢ {m L} ⊗ˢ <clean K-run on
    -- s_R>`, framed by the `map-++` casts (the strict twin of the non-strict
    -- `KClean`, where `BTC.uf++` is replaced by the trivial `map-++` cast — no
    -- `unflatten-++-≅` cone is needed in the strict world).
    --
    -- The clean K-run is `proj₂ (process-edgesˢ es s_R)` — the SAME `kblk`-run
    -- restricted to the pure-`s_R` stack.  Here `L` is the carried prefix and
    -- `s_R` the K-side stack; the actual mixed stack `↭`s `L ++ s_R`.

    KCleanˢ
      : ∀ (es : List (Fin H.nE)) (L s_R : List (Fin H.nV))
      → HomS (m (L ++ s_R))
             (m (L ++ proj₁ (process-edgesˢ es s_R)))
    KCleanˢ es L s_R =
      castˢ (sym (map-++ vl L s_R))
            (sym (map-++ vl L (proj₁ (process-edgesˢ es s_R))))
        (idˢ {m L} ⊗ˢ proj₂ (process-edgesˢ es s_R))

    ----------------------------------------------------------------------
    -- ## The per-edge HEAD reconciliation interface.
    --
    -- For a head C-edge `e` fired from the actual stack `s` (with the clean
    -- perm `pf : s ↭ L ++ s_R` and the advanced clean perm
    -- `pf1 : s1 ↭ L ++ s_R1`, where `s1`/`s_R1` are the post-edge actual /
    -- clean stacks), the actual head term `tH = proj₂ (edge-stepˢ s e)`
    -- reconciles to the clean single-edge block precomposed with the carried
    -- perm:
    --
    --   permuteˢ pf1 ∘ˢ tH ≈ˢ KCleanHeadˢ ∘ˢ permuteˢ pf
    --
    -- This packages the strict per-edge slide (`fire-slideˢ` — the carried-`L`
    -- prepend braid) together with the actual-→-clean routing
    -- (`process-edges-equivariantˢ` at a single edge).  It is supplied by the
    -- caller; the fold below is proven UNCONDITIONALLY against it.
    ----------------------------------------------------------------------

    HeadReconcileˢ
      : ∀ (e : Fin H.nE) (L s_R s s1 : List (Fin H.nV))
          (pf  : s  Perm.↭ L ++ s_R)
          (pf1 : s1 Perm.↭ L ++ proj₁ (edge-stepˢ s_R e))
          (KCleanHd : HomS (m (L ++ s_R))
                           (m (L ++ proj₁ (edge-stepˢ s_R e))))
          (tH : HomS (m s) (m s1))
      → Set
    HeadReconcileˢ e L s_R s s1 pf pf1 KCleanHd tH = permuteˢ pf1 ∘ˢ tH ≈ˢ KCleanHd ∘ˢ permuteˢ pf

    ----------------------------------------------------------------------
    -- ## `KCleanˢ` empty + cons telescoping.
    ----------------------------------------------------------------------

    -- `[]`: the clean block on `[]` edges collapses to a `map-++` round-trip
    -- cast of `idˢ {m L} ⊗ˢ idˢ` = `idˢ`.
    KCleanˢ-nil : ∀ (L s_R : List (Fin H.nV)) → KCleanˢ [] L s_R ≈ˢ idˢ {m (L ++ s_R)}
    KCleanˢ-nil L s_R =
      -- KCleanˢ [] L s_R = castˢ (sym map++)(sym map++) (idˢ{L} ⊗ˢ idˢ)
      ≈-trans (cast-resp (sym (map-++ vl L s_R)) (sym (map-++ vl L s_R)) ⊗-id)
        (cast-id (sym (map-++ vl L s_R)) (sym (map-++ vl L s_R)))

    ----------------------------------------------------------------------
    -- ## The clean single-edge head block.
    --
    -- `KCleanHeadˢ e L s_R` is the clean head: `idˢ {m L} ⊗ˢ <clean head term
    -- on s_R>`, framed by `map-++` casts.  The clean head term is
    -- `proj₂ (edge-stepˢ s_R e)`.
    ----------------------------------------------------------------------

    KCleanHeadˢ
      : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
      → HomS (m (L ++ s_R)) (m (L ++ proj₁ (edge-stepˢ s_R e)))
    KCleanHeadˢ e L s_R =
      castˢ (sym (map-++ vl L s_R))
            (sym (map-++ vl L (proj₁ (edge-stepˢ s_R e))))
        (idˢ {m L} ⊗ˢ proj₂ (edge-stepˢ s_R e))

    ----------------------------------------------------------------------
    -- ## `KCleanˢ` cons telescoping.
    --
    -- The clean run `KCleanˢ (e ∷ es) L s_R` factors as the clean tail
    -- `KCleanˢ es L (edge-stepˢ s_R e).₁` post-composed with the clean head
    -- `KCleanHeadˢ e L s_R`.  Both reduce to the SAME `idˢ{L} ⊗ˢ (-)` framed
    -- form; the strict twin of `KClean-cons`, via `interchangeˢ` (the
    -- `idˢ{L} ∘ˢ idˢ{L} = idˢ{L}` middle insertion) + cast fusion.
    ----------------------------------------------------------------------

    private
      s_R1 : (e : Fin H.nE) (s_R : List (Fin H.nV)) → List (Fin H.nV)
      s_R1 e s_R = proj₁ (edge-stepˢ s_R e)

      -- the cons-stack of the clean run.
      s_Rfin : (e : Fin H.nE) (es : List (Fin H.nE)) (s_R : List (Fin H.nV)) → List (Fin H.nV)
      s_Rfin e es s_R = proj₁ (process-edgesˢ es (s_R1 e s_R))

    KCleanˢ-cons
      : ∀ (e : Fin H.nE) (es : List (Fin H.nE)) (L s_R : List (Fin H.nV))
      → KCleanˢ (e ∷ es) L s_R
        ≈ˢ KCleanˢ es L (s_R1 e s_R) ∘ˢ KCleanHeadˢ e L s_R
    KCleanˢ-cons e es L s_R = goal
      where
        eh = proj₂ (edge-stepˢ s_R e)
        et = proj₂ (process-edgesˢ es (s_R1 e s_R))
        sR1 = s_R1 e s_R
        sRf = s_Rfin e es s_R

        -- the clean K-run on (e ∷ es) is `et ∘ˢ eh`.
        -- step 1: id{L} ⊗ (et ∘ eh) ≈ (id{L} ⊗ et) ∘ (id{L} ⊗ eh)  [id⊗-distˢ]

        Pi  = sym (map-++ vl L s_R)
        Po  = sym (map-++ vl L sRf)
        Pm  = sym (map-++ vl L sR1)

        goal : KCleanˢ (e ∷ es) L s_R ≈ˢ KCleanˢ es L sR1 ∘ˢ KCleanHeadˢ e L s_R
        goal =
          -- LHS = castˢ Pi Po (id{L} ⊗ (et ∘ eh))
          ≈-trans (cast-resp Pi Po (id⊗-distˢ (m L) et eh))
          -- castˢ Pi Po ((id{L}⊗et) ∘ (id{L}⊗eh))
          (∘-cast-split Pi Pm Po (idˢ {m L} ⊗ˢ et) (idˢ {m L} ⊗ˢ eh))

    ----------------------------------------------------------------------
    -- ## The K-prepend braid round-trip cancellation.
    --
    -- `permuteˢ Br ∘ˢ permuteˢ pf ≈ˢ idˢ` when `pf : s ↭ c` and `Br : c ↭ s`
    -- compose round-trip on a `Unique s`.  The single keystone use: the
    -- composite `↭-trans pf Br : s ↭ s` is identified with `↭-refl` by
    -- `perm-rigidˢ` on the `Unique` stack.
    ----------------------------------------------------------------------

    pvv-cancelˢ
      : ∀ {s c : List (Fin H.nV)} → Unique s
      → (pf : s Perm.↭ c) (Br : c Perm.↭ s)
      → permuteˢ Br ∘ˢ permuteˢ pf ≈ˢ idˢ {m s}
    pvv-cancelˢ uniq pf Br =
      ≈-trans (≈-sym (pvv-transˢ pf Br))
        (perm-rigidˢ uniq (Perm.trans pf Br) Perm.↭-refl)

    ----------------------------------------------------------------------
    -- ## The per-edge head PROVIDER.
    --
    -- A `HeadProviderRˢ D L` is a uniform family supplying, for ANY running
    -- configuration `(e, s_R, s, pf)` with `D e`, the advanced clean perm
    -- `pf1` and the head reconciliation `HeadReconcileˢ`.  It carries NO
    -- post-edge `Unique` component (the reservoir-threaded fold derives that
    -- for itself) and is GUARDED by a per-edge predicate `D e` (the
    -- disjointness `ein-disjⁱ e L`, supplied only for the edges actually
    -- fired — gblk-edge inputs are NOT disjoint from an `injL`-block, so the
    -- guard must NOT be universal), which lets it be supplied WITHOUT the
    -- FALSE per-edge `Unique`-preservation family `puq`.  Being closed over
    -- all configurations, it re-invokes on the advanced stacks inside the
    -- recursion with NO re-indexing.
    ----------------------------------------------------------------------

    HeadProviderRˢ : (D : Fin H.nE → Set) (L : List (Fin H.nV)) → Set
    HeadProviderRˢ D L =
      ∀ (e : Fin H.nE) → D e → (s_R s : List (Fin H.nV))
        (pf : s Perm.↭ L ++ s_R)
      → Unique s
      → Σ[ pf1 ∈ (proj₁ (edge-stepˢ s e))
                   Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
          HeadReconcileˢ e L s_R s (proj₁ (edge-stepˢ s e))
            pf pf1 (KCleanHeadˢ e L s_R) (proj₂ (edge-stepˢ s e))

    ----------------------------------------------------------------------
    -- ## `kfac-gen-resˢ` — the RESERVOIR-THREADED K-side perm-tracking fold.
    --
    --   proj₂ (process-edgesˢ es s)
    --     ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    --
    -- with the actual stack `s` only `↭`-ing the clean form (`pf`) and the
    -- codomain `↭`-ing the clean target (`Br`).  Induction on `es` mirroring
    -- `process-edgesˢ`: the head is rewritten by the `HeadProviderRˢ`, the tail
    -- by the IH, the clean blocks telescoped by `KCleanˢ-cons` (`Br` threads
    -- through the cons telescoping unchanged); the `[]` case collapses
    -- `permuteˢ Br ∘ permuteˢ pf` by `pvv-cancelˢ` and `KCleanˢ [] L s_R` by
    -- `KCleanˢ-nil`.
    --
    -- The threaded per-step `Unique` is DERIVED, not assumed: rather than
    -- carrying a `Unique s` advanced by a (FALSE-in-general) post-edge
    -- `Unique`, we carry the `StackUniqueReach.Reservoir≤1 H es s` freshness
    -- invariant along the run-order `es` at the running stack `s`.  Each step:
    --   * `Reservoir≤1⇒Unique` derives the round-trip `Unique s`;
    --   * the `HeadProviderRˢ` is invoked with that derived `Unique s` (it
    --     supplies `pf1` + the head reconciliation);
    --   * `edge-step-Reservoir≤1` advances the invariant one edge, bridged to
    --     the strict stack `proj₁ (edge-stepˢ s e)` by `edge-stack-agree`.
    -- This is the EXACT threading `process-edges-equivariantˢ` (StackEquiv) uses.
    ----------------------------------------------------------------------

    kfac-gen-resˢ
      : ∀ {D : Fin H.nE → Set}
          (L : List (Fin H.nV)) (hp : HeadProviderRˢ D L)
          (es : List (Fin H.nE)) → All D es
      → ∀ (s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
          (Br : (L ++ proj₁ (process-edgesˢ es s_R))
                Perm.↭ proj₁ (process-edgesˢ es s))
      → SUR.Reservoir≤1 H es s
      → proj₂ (process-edgesˢ es s)
        ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    kfac-gen-resˢ L hp [] [] s_R s pf Br res =
      ≈-sym
        (≈-trans (∘-resp ≈-refl (∘-resp (KCleanˢ-nil L s_R) ≈-refl))
        (≈-trans (∘-resp ≈-refl idˡ)
          (pvv-cancelˢ (SUR.Reservoir≤1⇒Unique H [] s res) pf Br)))
    kfac-gen-resˢ L hp (e ∷ es) (de ∷ des) s_R s pf Br res
      with hp e de s_R s pf (SUR.Reservoir≤1⇒Unique H (e ∷ es) s res)
    ... | pf1 , head =
      ≈-trans (∘-resp IH ≈-refl)
      (≈-trans assocˢ
        (∘-resp ≈-refl
          (≈-trans assocˢ
            (≈-trans (∘-resp ≈-refl head)
              (≈-trans (≈-sym assocˢ)
                (∘-resp (≈-sym (KCleanˢ-cons e es L s_R)) ≈-refl))))))
      where
        s1  = proj₁ (edge-stepˢ s e)
        sR1 = proj₁ (edge-stepˢ s_R e)

        res1 : SUR.Reservoir≤1 H es s1
        res1 = subst (SUR.Reservoir≤1 H es)
                     (sym (edge-stack-agree s e))
                     (SUR.edge-step-Reservoir≤1 H e es s res)

        IH : proj₂ (process-edgesˢ es s1) ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L sR1 ∘ˢ permuteˢ pf1)
        IH = kfac-gen-resˢ L hp es des sR1 s1 pf1 Br res1

------------------------------------------------------------------------
-- ===== submodule TKB5 =====
------------------------------------------------------------------------
module TKB5 (H : Hypergraph FlatGen) where
  open TKBBase H
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
    using (module EquivStep)

  open EquivStep H using ( pvv-transˢ; pvv-inverse-rightˢ
                         ; edge-stepˢ-graph; edge-step-equivariantˢ )

  module _ (permˢ-K : Kmod.PermK) where
    KCleanHeadˢ = TKB4.KCleanHeadˢ H permˢ-K
    HeadReconcileˢ = TKB4.HeadReconcileˢ H permˢ-K

    ----------------------------------------------------------------------
    -- ## The clean per-edge SLIDE interface.
    --
    -- For a head edge `e` whose inputs are disjoint from the carried block
    -- `L`, fired on the CLEAN stack `L ++ s_R`, there is a braid `β` from the
    -- clean post-edge stack to `L ++ (edge-stepˢ s_R e).₁` such that the clean
    -- fired head, braided by `β`, IS the framed clean head `KCleanHeadˢ`.
    --
    -- This is the genuine per-edge content (`fire-slideˢ` + the `↑ʳ`-disjoint
    -- skip/fire dispatch); the equivariance conjugation below is built on it.
    ----------------------------------------------------------------------

    HeadSlideˢ : (e : Fin H.nE) (L s_R : List (Fin H.nV)) → Set
    HeadSlideˢ e L s_R =
      Σ[ β ∈ (proj₁ (edge-stepˢ (L ++ s_R) e))
               Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
        ( permuteˢ β ∘ˢ proj₂ (edge-stepˢ (L ++ s_R) e)
          ≈ˢ KCleanHeadˢ e L s_R )

    ----------------------------------------------------------------------
    -- ## The equivariance conjugation glue.
    --
    -- Given `HeadSlideˢ` and the post-edge `Unique`, `HeadReconcileˢ` follows
    -- by conjugating the actual fired head onto the clean stack via
    -- `edge-step-equivariantˢ` and reassociating.
    ----------------------------------------------------------------------

    head-reconcile-from-slide
      : ∀ (e : Fin H.nE) (L s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
      → Unique s
      → HeadSlideˢ e L s_R
      → Σ[ pf1 ∈ (proj₁ (edge-stepˢ s e))
                   Perm.↭ (L ++ proj₁ (edge-stepˢ s_R e)) ]
          HeadReconcileˢ e L s_R s (proj₁ (edge-stepˢ s e))
            pf pf1 (KCleanHeadˢ e L s_R) (proj₂ (edge-stepˢ s e))
    head-reconcile-from-slide e L s_R s pf us (β , slide)
      with edge-step-equivariantˢ e pf
             (edge-stepˢ-graph (L ++ s_R) e) (edge-stepˢ-graph s e) us
    ... | ρf , eq =
      Perm.trans ρf β , goal
      where
        tH      = proj₂ (edge-stepˢ s e)
        tHclean = proj₂ (edge-stepˢ (L ++ s_R) e)

        -- eq : tH ≈ permuteˢ (↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf)
        -- goal : permuteˢ (trans ρf β) ∘ tH ≈ KCleanHeadˢ ∘ permuteˢ pf
        goal : permuteˢ (Perm.trans ρf β) ∘ˢ tH ≈ˢ KCleanHeadˢ e L s_R ∘ˢ permuteˢ pf
        goal =
          -- permuteˢ (trans ρf β) = permuteˢ β ∘ permuteˢ ρf  (definitional)
          ≈-trans (∘-resp (pvv-transˢ ρf β) ≈-refl)
          -- (permuteˢ β ∘ permuteˢ ρf) ∘ tH
          (≈-trans (∘-resp ≈-refl eq)
          -- (permuteˢ β ∘ permuteˢ ρf) ∘ (permuteˢ(↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans assocˢ
          -- permuteˢ β ∘ (permuteˢ ρf ∘ (permuteˢ(↭-sym ρf) ∘ (tHclean ∘ permuteˢ pf)))
          (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
          -- permuteˢ β ∘ ((permuteˢ ρf ∘ permuteˢ(↭-sym ρf)) ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans (∘-resp ≈-refl (∘-resp (pvv-inverse-rightˢ ρf) ≈-refl))
          -- permuteˢ β ∘ (idˢ ∘ (tHclean ∘ permuteˢ pf))
          (≈-trans (∘-resp ≈-refl idˡ)
          -- permuteˢ β ∘ (tHclean ∘ permuteˢ pf)
          (≈-trans (≈-sym assocˢ)
          -- (permuteˢ β ∘ tHclean) ∘ permuteˢ pf
          (∘-resp slide ≈-refl)))))))

------------------------------------------------------------------------
-- ===== submodule TKB6 =====
------------------------------------------------------------------------
module TKB6 (H : Hypergraph FlatGen) where
  open TKBBase H
  open import Categories.APROP.Hypergraph.Model.FromAPROP sig
    using (hTensor; module hTensor-impl)
  open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
    using (extract-elem; extract-prefix)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Interchange.StackEquiv sig _≟X_
    using (module EquivStep)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig _≟X_
    using (module StrictSep)
  open import Categories.APROP.Hypergraph.Soundness.Strict.Decode.DecodeSigma sig _≟X_
    using (module Scr)
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig as SU
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
  open import Data.Fin using (_↑ˡ_; _↑ʳ_; splitAt)
  open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
  import Data.Fin.Properties as FinP
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Nullary using (yes; no)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.Maybe using (Maybe; just; nothing)

  open StrictSep H using (extract-prefix-++ˡ-left; extract-prefix-++ˡ-left-nothing)
  open EquivStep H using (pvv-transˢ; pvv-inverse-leftˢ)

  private
    module ScrH = Scr (Fin H.nV) H.vlab

  -- an `idˢ` cast can move its single non-trivial endpoint to the other side.
  idcast-flip : ∀ {a b : List X} (q : a ≡ b) → castˢ refl q (idˢ {a}) ≈ˢ castˢ (sym q) refl (idˢ {b})
  idcast-flip refl = ≈-refl

  module _ (permˢ-K : Kmod.PermK) where
    KCleanHeadˢ = TKB5.KCleanHeadˢ H permˢ-K
    HeadSlideˢ  = TKB5.HeadSlideˢ  H permˢ-K
    fire-slideˢ = TKB2.fire-slideˢ H permˢ-K
    obraid      = TKB2.obraid      H permˢ-K
    odom        = TKB2.odom        H permˢ-K
    ocod        = TKB2.ocod        H permˢ-K
    fire-termˢ  = TKB2.fire-termˢ  H
    HeadProviderRˢ = TKB4.HeadProviderRˢ H permˢ-K
    head-reconcile-from-slide = TKB5.head-reconcile-from-slide H permˢ-K
    KCleanˢ   = TKB4.KCleanˢ   H permˢ-K
    kfac-gen-resˢ = TKB4.kfac-gen-resˢ H permˢ-K

    private
      ein-disjⁱ : Fin H.nE → List (Fin H.nV) → Set
      ein-disjⁱ e L = All (λ k → extract-elem k L ≡ nothing) (H.ein e)

    ----------------------------------------------------------------------
    -- ## SKIP case of `HeadSlideˢ`.
    --
    -- When `e` does NOT fire on the clean K-side `s_R` (and `H.ein e`
    -- disjoint from `L`), it does not fire on `L ++ s_R` either
    -- (`extract-prefix-++ˡ-left-nothing`); both `edge-stepˢ` are `idˢ`,
    -- `β = ↭-refl`, and `KCleanHeadˢ` collapses to `idˢ` by `⊗-id`/`cast-id`.
    ----------------------------------------------------------------------

    -- The SKIP `HeadSlideˢ`, stated against ABSTRACT edge-step results so the
    -- two propositional SKIP equalities can be discharged by pattern matching.
    -- With both edge-steps SKIPped (`proj₁ = its stack`, `proj₂ = idˢ`), the
    -- slide equation is `idˢ ∘ˢ idˢ ≈ KCleanHeadˢ`, and `KCleanHeadˢ` is a
    -- same-endpoint cast of `idˢ {m L} ⊗ˢ idˢ`, which collapses by `⊗-id`
    -- then `cast-id`.
    private
      -- With both `extract-prefix` calls rewritten to `nothing`, the two
      -- `edge-stepˢ`-`with` blocks reduce, exposing `proj₁ = its stack`,
      -- `proj₂ = idˢ`; `KCleanHeadˢ` becomes a same-endpoint cast of
      -- `idˢ {m L} ⊗ˢ idˢ`.
      head-slide-skip-core
        : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
        → extract-prefix (H.ein e) s_R ≡ nothing
        → extract-prefix (H.ein e) (L ++ s_R) ≡ nothing
        → HeadSlideˢ e L s_R
      head-slide-skip-core e L s_R eqn eqn-LR
        rewrite eqn | eqn-LR = Perm.↭-refl , slide
        where
          q : m (L ++ s_R) ≡ m L ++ m s_R
          q = map-++ vl L s_R

          slide
            : permuteˢ {xs = L ++ s_R} Perm.↭-refl ∘ˢ idˢ {m (L ++ s_R)}
              ≈ˢ castˢ (sym q) (sym q) (idˢ {m L} ⊗ˢ idˢ {m s_R})
          slide =
            ≈-trans idˡ
              (≈-sym (≈-trans (cast-resp (sym q) (sym q) ⊗-id)
                              (cast-id (sym q) (sym q))))

    head-slide-skip
      : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
      → ein-disjⁱ e L
      → extract-prefix (H.ein e) s_R ≡ nothing
      → HeadSlideˢ e L s_R
    head-slide-skip e L s_R disj eqn =
      head-slide-skip-core e L s_R eqn
        (extract-prefix-++ˡ-left-nothing (H.ein e) L s_R disj eqn)

    ----------------------------------------------------------------------
    -- ## FIRE case of `HeadSlideˢ`.
    --
    -- When `e` fires on the clean K-side `s_R` (residual `rest_R`, perm `p`)
    -- and `H.ein e` is disjoint from `L`, `extract-prefix-++ˡ-left` pins the
    -- `(L ++ s_R)`-fire to residual `L ++ rest_R` with derivation `D`, so
    -- `proj₂ (edge-stepˢ (L ++ s_R) e) = fire-termˢ e (L ++ s_R) (L ++ rest_R) D`
    -- DEFINITIONALLY.  `fire-slideˢ` factors this into the output block-braid
    -- `castₒ = castˢ (odom)(ocod)(permuteˢ (obraid e L rest_R))` composed with
    -- the framed clean head `idˢ {m L} ⊗ˢ fire-termˢ e s_R rest_R p` — and that
    -- framed factor IS the body of `KCleanHeadˢ`.  We absorb `castₒ` by the
    -- slide braid `β` whose `permuteˢ` is a cast of `permuteˢ (↭-sym obraid)`,
    -- collapsing `permuteˢ β ∘ˢ castₒ` to a pure cast by `pvv-inverse-leftˢ`.
    --
    -- Requires `Unique ((L ++ H.ein e) ++ rest_R)` (the `fire-slideˢ` side
    -- condition; sourced by the caller from the run reservoir freshness).
    ----------------------------------------------------------------------

    private
      -- the slide braid: move the fired output block `H.eout e` past `L`,
      -- framed by `rest_R` (assoc-glued `↭-sym (obraid e L rest_R)`).
      slideβ
        : (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → (H.eout e ++ (L ++ rest_R)) Perm.↭ (L ++ (H.eout e ++ rest_R))
      slideβ e L rest_R =
        Perm.trans (Perm.↭-reflexive (sym (++-assoc (H.eout e) L rest_R)))
          (Perm.trans (Perm.↭-sym (obraid e L rest_R))
                      (Perm.↭-reflexive (++-assoc L (H.eout e) rest_R)))

      ----------------------------------------------------------------------
      -- ## `slide-braid-cancel` — the slide braid absorbs `castₒ`.
      --
      -- `permuteˢ β ∘ˢ castˢ (odom)(ocod)(permuteˢ obraid)` collapses to a pure
      -- identity-cast, because `β`'s middle factor is `↭-sym obraid`, cancelled
      -- against `castₒ`'s `permuteˢ obraid` by `pvv-inverse-leftˢ`.  The
      -- surrounding `↭-reflexive` braids + `odom`/`ocod` casts combine (UIP) into
      -- the single endpoint cast `castˢ refl (sym (map-++ vl L (eout++rest))) idˢ`.
      ----------------------------------------------------------------------

      slide-braid-cancel
        : ∀ (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → permuteˢ (slideβ e L rest_R)
            ∘ˢ castˢ (odom e L rest_R) (ocod e L rest_R)
                     (permuteˢ (obraid e L rest_R))
          ≈ˢ castˢ refl (sym (map-++ vl L (H.eout e ++ rest_R)))
                   (idˢ {m L ++ m (H.eout e ++ rest_R)})
      slide-braid-cancel e L rest_R =
        -- permuteˢ β = permuteˢ C ∘ˢ (permuteˢ B ∘ˢ permuteˢ A)
        ≈-trans (∘-resp (pvv-transˢ (Perm.↭-reflexive (sym aEO))
                                    (Perm.trans B C)) ≈-refl)
        (≈-trans (∘-resp (∘-resp (pvv-transˢ B C) ≈-refl) ≈-refl)
        -- ((permuteˢ C ∘ permuteˢ B) ∘ permuteˢ A) ∘ castₒ : reassociate fully
        (≈-trans assocˢ
        (≈-trans assocˢ
          -- permuteˢ C ∘ (permuteˢ B ∘ (permuteˢ A ∘ castₒ))
          (≈-trans (∘-resp ≈-refl (∘-resp ≈-refl A∘castₒ))
          (≈-trans (∘-resp ≈-refl B∘rest)
            C∘rest)))))
        where
          EO  = H.eout e
          aEO = ++-assoc EO L rest_R
          aL  = ++-assoc L EO rest_R
          obr = obraid e L rest_R
          B   = Perm.↭-sym obr
          C   = Perm.↭-reflexive aL

          castₒ : HomS (m L ++ m (EO ++ rest_R)) (m (EO ++ (L ++ rest_R)))
          castₒ = castˢ (odom e L rest_R) (ocod e L rest_R) (permuteˢ obr)

          -- permuteˢ A ≈ castˢ (ocod) refl idˢ  (refl-trivial + idcast-flip + UIP).
          permA-cast
            : permuteˢ (Perm.↭-reflexive (sym aEO))
              ≈ˢ castˢ (ocod e L rest_R) refl (idˢ {m ((EO ++ L) ++ rest_R)})
          permA-cast =
            ≈-trans (ScrH.refl-trivial (sym aEO))
            (≈-trans (idcast-flip (cong m (sym aEO)))
              (≡⇒≈ˢ (cast-irrel (sym (cong m (sym aEO))) (ocod e L rest_R)
                       refl refl (idˢ {m ((EO ++ L) ++ rest_R)}))))

          -- permuteˢ A ∘ castₒ ≈ castˢ (odom) refl (permuteˢ obr)
          A∘castₒ
            : permuteˢ (Perm.↭-reflexive (sym aEO)) ∘ˢ castₒ
              ≈ˢ castˢ (odom e L rest_R) refl (permuteˢ obr)
          A∘castₒ =
            ≈-trans (∘-resp permA-cast ≈-refl)
            -- castˢ (ocod) refl idˢ ∘ castˢ (odom)(ocod)(permuteˢ obr)
            (≈-trans
              (≈-sym (∘-cast-split (odom e L rest_R) (ocod e L rest_R) refl
                        (idˢ {m ((EO ++ L) ++ rest_R)}) (permuteˢ obr)))
              (cast-resp (odom e L rest_R) refl idˡ))

          -- permuteˢ B ∘ castˢ (odom) refl (permuteˢ obr)
          --   ≈ castˢ (odom) refl idˢ   (pvv-inverse-leftˢ obr)
          B∘rest
            : permuteˢ B ∘ˢ castˢ (odom e L rest_R) refl (permuteˢ obr)
              ≈ˢ castˢ (odom e L rest_R) refl (idˢ {m ((L ++ EO) ++ rest_R)})
          B∘rest =
            ≈-trans
              (≈-sym (∘-cast-split (odom e L rest_R) refl refl
                        (permuteˢ B) (permuteˢ obr)))
              (cast-resp (odom e L rest_R) refl
                (≈-trans (∘-resp (≡⇒≈ˢ refl) ≈-refl)
                         (pvv-inverse-leftˢ obr)))

          -- permuteˢ C ∘ castˢ (odom) refl idˢ ≈ castˢ (odom)(cong m aL) idˢ.
          C∘rest
            : permuteˢ C ∘ˢ castˢ (odom e L rest_R) refl (idˢ {m ((L ++ EO) ++ rest_R)})
              ≈ˢ castˢ refl (sym (map-++ vl L (EO ++ rest_R)))
                       (idˢ {m L ++ m (EO ++ rest_R)})
          C∘rest =
            ≈-trans (∘-resp (ScrH.refl-trivial aL) ≈-refl)
            -- castˢ refl (cong m aL) idˢ ∘ castˢ (odom) refl idˢ  (merge, idˡ)
            (≈-trans
              (≈-sym (∘-cast-split (odom e L rest_R) refl (cong m aL)
                        (idˢ {m ((L ++ EO) ++ rest_R)})
                        (idˢ {m ((L ++ EO) ++ rest_R)})))
            (≈-trans
              (cast-resp (odom e L rest_R) (cong m aL) idˡ)
              -- castˢ (odom)(cong m aL) idˢ{X₀} → bridge to castᴵ via idˢ{Y₀}.
              end-bridge))
            where
              X₀ = m ((L ++ EO) ++ rest_R)
              Y₀ = m L ++ m (EO ++ rest_R)
              od = odom e L rest_R   -- od : X ≡ Y

              -- castˢ od (cong m aL) idˢ{X}
              --   ≈ castˢ refl (trans (sym od)(cong m aL)) (castˢ od od idˢ{X})
              --   ≈ castˢ refl (trans (sym od)(cong m aL)) idˢ{Y}
              --   ≈ castᴵ
              end-bridge
                : castˢ od (cong m aL) (idˢ {X₀})
                  ≈ˢ castˢ refl (sym (map-++ vl L (EO ++ rest_R))) (idˢ {Y₀})
              end-bridge =
                ≈-trans
                  (≡⇒≈ˢ (sym
                    (trans (cast-fuse od refl od (trans (sym od) (cong m aL))
                              (idˢ {X₀}))
                           (cast-irrel (trans od refl) od
                              (trans od (trans (sym od) (cong m aL))) (cong m aL)
                              (idˢ {X₀})))))
                (≈-trans
                  (cast-resp refl (trans (sym od) (cong m aL)) (cast-id od od))
                  (≡⇒≈ˢ (cast-irrel refl refl (trans (sym od) (cong m aL))
                           (sym (map-++ vl L (EO ++ rest_R))) (idˢ {Y₀}))))

    head-slide-fire
      : ∀ (e : Fin H.nE) (L s_R rest_R : List (Fin H.nV))
          (p : s_R Perm.↭ H.ein e ++ rest_R)
      → ein-disjⁱ e L
      → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
      → Unique ((L ++ H.ein e) ++ rest_R)
      → HeadSlideˢ e L s_R
    head-slide-fire e L s_R rest_R p disj eqR uIn with extract-prefix-++ˡ-left (H.ein e) L s_R disj eqR
    ... | D , eqLR
      rewrite eqR | eqLR = slideβ e L rest_R , slide-eq
      where
        EO   = H.eout e
        mLs  = map-++ vl L s_R
        mLo  = map-++ vl L (EO ++ rest_R)
        Xf   = idˢ {m L} ⊗ˢ fire-termˢ e s_R rest_R p
        castₒ : HomS (m L ++ m (EO ++ rest_R)) (m (EO ++ (L ++ rest_R)))
        castₒ = castˢ (odom e L rest_R) (ocod e L rest_R) (permuteˢ (obraid e L rest_R))

        slide-eq
          : permuteˢ (slideβ e L rest_R)
              ∘ˢ fire-termˢ e (L ++ s_R) (L ++ rest_R) D
            ≈ˢ castˢ (sym mLs) (sym mLo) Xf
        slide-eq =
          -- rewrite the fired layer by `fire-slideˢ`.
          ≈-trans (∘-resp ≈-refl (fire-slideˢ e L s_R rest_R D p uIn))
          -- permuteˢ β ∘ castˢ (sym mLs) refl (castₒ ∘ Xf)
          (≈-trans (∘-resp ≈-refl
                     (≈-trans (∘-cast-split (sym mLs) refl refl castₒ Xf)
                              (∘-resp (≡⇒≈ˢ refl) ≈-refl)))
          -- permuteˢ β ∘ (castₒ ∘ castˢ (sym mLs) refl X)
          (≈-trans (≈-sym assocˢ)
          -- (permuteˢ β ∘ castₒ) ∘ castˢ (sym mLs) refl X
          (≈-trans (∘-resp (slide-braid-cancel e L rest_R) ≈-refl)
          -- castᴵ ∘ castˢ (sym mLs) refl X  →  merge to castˢ (sym mLs)(sym mLo)(idˢ ∘ Xf)
          (≈-trans
            (≈-sym (∘-cast-split (sym mLs) refl (sym mLo)
                      (idˢ {m L ++ m (EO ++ rest_R)}) Xf))
            (cast-resp (sym mLs) (sym mLo) idˡ)))))

    ----------------------------------------------------------------------
    -- ## The FIRE/SKIP dispatcher → a uniform `HeadSlideˢ` family.
    --
    -- For a fixed disjoint block `L`, dispatch on whether `e` fires on `s_R`:
    -- FIRE uses `head-slide-fire` (needs `Unique ((L++ein e)++rest_R)`, supplied
    -- per-configuration by `fuq`), SKIP uses `head-slide-skip`.
    ----------------------------------------------------------------------

    head-slide
      : ∀ (L : List (Fin H.nV)) (e : Fin H.nE) (s_R : List (Fin H.nV))
      → ein-disjⁱ e L
      → (∀ (rest_R : List (Fin H.nV)) (p : s_R Perm.↭ H.ein e ++ rest_R)
         → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
         → Unique ((L ++ H.ein e) ++ rest_R))
      → HeadSlideˢ e L s_R
    head-slide L e s_R disj fuq = aux (extract-prefix (H.ein e) s_R) refl
      where
        aux : (w : Maybe (Σ[ rest ∈ List (Fin H.nV) ] s_R Perm.↭ H.ein e ++ rest))
            → extract-prefix (H.ein e) s_R ≡ w
            → HeadSlideˢ e L s_R
        aux (just (rest_R , p)) eqR = head-slide-fire e L s_R rest_R p disj eqR (fuq rest_R p eqR)
        aux nothing eqn = head-slide-skip e L s_R disj eqn

    private
      -- `s ↭ (L ++ ein e) ++ rest_R` from `pf : s ↭ L ++ s_R` and the fire perm.
      fire-stack-perm
        : ∀ (e : Fin H.nE) (L s_R s rest_R : List (Fin H.nV))
        → s Perm.↭ L ++ s_R → s_R Perm.↭ H.ein e ++ rest_R
        → s Perm.↭ (L ++ H.ein e) ++ rest_R
      fire-stack-perm e L s_R s rest_R pf p =
        Perm.trans pf
          (Perm.trans (PermProp.++⁺ˡ L p)
            (Perm.↭-reflexive (sym (++-assoc L (H.ein e) rest_R))))

    ----------------------------------------------------------------------
    -- ## `head-provider-res` — the SLIM `HeadProviderRˢ` from disjointness
    -- ALONE.  It needs NO post-edge `Unique` family
    -- `puq` (which is false in general): the reservoir-threaded fold derives
    -- each step's `Unique` itself.  The FIRE side-condition `Unique
    -- ((L++ein e)++rest_R)` is still derived in-place from the round-trip
    -- `Unique s` along `fire-stack-perm`.
    ----------------------------------------------------------------------

    head-provider-res : ∀ (L : List (Fin H.nV)) → HeadProviderRˢ (λ e → ein-disjⁱ e L) L
    head-provider-res L e disj s_R s pf us =
      let slide = head-slide L e s_R disj fuq
          pf1 , hr = head-reconcile-from-slide e L s_R s pf us slide
      in pf1 , hr
      where
        fuq : ∀ (rest_R : List (Fin H.nV)) (p : s_R Perm.↭ H.ein e ++ rest_R)
              → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
              → Unique ((L ++ H.ein e) ++ rest_R)
        fuq rest_R p _ = SU.Unique-resp-↭ (fire-stack-perm e L s_R s rest_R pf p) us

    ----------------------------------------------------------------------
    -- ## `kblock-factorize-res` — the WHOLE K-block run factorization,
    -- UNCONDITIONAL except for the disjointness + the run-order RESERVOIR
    -- freshness `SUR.Reservoir≤1 H es s` (a TRUE invariant along the actual
    -- run, sourced from linearity by `dom-reservoir-prov`/`reservoir-split`).
    -- This is the (d)-core with the false `puq` ELIMINATED: it feeds the slim
    -- `head-provider-res` to the reservoir-threaded fold `kfac-gen-resˢ`.
    ----------------------------------------------------------------------

    kblock-factorize-res
      : ∀ (L : List (Fin H.nV))
      → ∀ (es : List (Fin H.nE)) → All (λ e → ein-disjⁱ e L) es
      → ∀ (s_R s : List (Fin H.nV))
          (pf : s Perm.↭ L ++ s_R)
          (Br : (L ++ proj₁ (process-edgesˢ es s_R))
                Perm.↭ proj₁ (process-edgesˢ es s))
      → SUR.Reservoir≤1 H es s
      → proj₂ (process-edgesˢ es s)
        ≈ˢ permuteˢ Br ∘ˢ (KCleanˢ es L s_R ∘ˢ permuteˢ pf)
    kblock-factorize-res L es disj s_R s pf Br res =
      kfac-gen-resˢ L (head-provider-res L) es disj s_R s pf Br res

--------------------------------------------------------------------------------
-- ## K-block disjointness at the concrete `hTensor` layout.
--
-- The K-edge inputs `H.ein (ψK eK) = map injR (K.ein eK)` are disjoint from any
-- `injL`-block `map injL P` — the side condition `head-provider`/`head-slide`
-- need at `L = Lpre = map injL Gd.dom`, `e = ψK eK`.  Mirror of
-- `TensorBraid.Braid.g-disjoint`/`injL∉injRs`, on the K-side (`injR∉injLs`).
--------------------------------------------------------------------------------


------------------------------------------------------------------------
-- ===== submodule KBlockDisjoint =====
------------------------------------------------------------------------
open import Categories.APROP.Hypergraph.Model.FromAPROP sig hiding (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig using (extract-elem)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
import Data.Fin.Properties as FinP
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality

module KBlockDisjoint (G K : Hypergraph FlatGen) where
  private
    module G = Hypergraph G
    module K = Hypergraph K
    module C = Hypergraph (hTensor G K)
  open hTensor-impl G K using (injL; injR; ein-c-inj₂-red)
  open Dec.StrictDecoder (hTensor G K) using (vl)

  ψK : Fin K.nE → Fin C.nE
  ψK eK = G.nE ↑ʳ eK

  -- `injR j ≢ injL k` (split lands in `inj₂` vs `inj₁`).
  injR≢injL : ∀ {j : Fin K.nV} {k : Fin G.nV} → injR j ≡ injL k → ⊥
  injR≢injL {j} {k} eq with trans (sym (splitAt-↑ʳ G.nV K.nV j))
                            (trans (cong (splitAt G.nV) eq)
                                   (splitAt-↑ˡ G.nV k K.nV))
  ... | ()

  -- `injR j` is absent from any `injL`-block.
  injR∉injLs : ∀ (j : Fin K.nV) (P : List (Fin G.nV)) → extract-elem (injR j) (map injL P) ≡ nothing
  injR∉injLs j []       = refl
  injR∉injLs j (k ∷ ks) with injL k FinP.≟ injR j
  ... | yes p  = ⊥-elim (injR≢injL (sym p))
  ... | no  _  rewrite injR∉injLs j ks = refl

  -- `ein-disjⁱ (ψK eK) (map injL P)` at `H = hTensor G K`.
  kblock-ein-disjoint
    : ∀ (eK : Fin K.nE) (P : List (Fin G.nV))
    → All (λ k → extract-elem k (map injL P) ≡ nothing)
          (C.ein (ψK eK))
  kblock-ein-disjoint eK P =
    subst (λ ks → All (λ k → extract-elem k (map injL P) ≡ nothing) ks)
          (sym (ein-c-inj₂-red eK))
          (all-injR (K.ein eK))
    where
      all-injR : ∀ (js : List (Fin K.nV))
               → All (λ k → extract-elem k (map injL P) ≡ nothing)
                     (map injR js)
      all-injR []       = []
      all-injR (j ∷ js) = injR∉injLs j P ∷ all-injR js

