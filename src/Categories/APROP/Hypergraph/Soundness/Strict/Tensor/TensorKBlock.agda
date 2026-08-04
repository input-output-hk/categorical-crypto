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
  open import Data.List.Properties using (++-assoc) public
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

  open Restrict (Fin H.nV) vl public
    using ( HomV; idᵛ; _∘ᵛ_; _⊗ᵛ_; σᵛ; castᵛ; _≈ᵛ_; permuteᵛ; castᵛ-≈̂; castᵛ-perm
          ; ⊗-respᵛ; ⊗-idᵛ; id⊗-distᵛ; ⊗id-distᵛ; box-conjᵛ; ⊗-assoc-≈̂ᵛ
          ; box-suffix-≈̂ᵛ )

  module Kmod = Support (Fin H.nV) H.vlab

  m : List (Fin H.nV) → List X
  m = map vl

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
  -- The fired box's output block `gen' e ⊗ᵛ idᵛ {L ++ rest}` (the box at the
  -- front, then the carried `L` and residual `rest`) equals the same box
  -- moved to AFTER `L`, conjugated by the two one-sided block braids that
  -- swap the box's input / output block past `L`.  Pure `σ-natᵛ`/`σ-σᵛ`
  -- (`box-conjᵛ`) + `⊗id-distᵛ`; no endpoint is ever named.
  ------------------------------------------------------------------------

  module _ (permˢ-K : Kmod.PermK) where
    private
      gen' : ∀ (e : Fin H.nE) → HomV (H.ein e) (H.eout e)
      gen' e = genˢ (H.elab e)

    box-block-slideᵛ
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → (gen' e ⊗ᵛ idᵛ {L}) ⊗ᵛ idᵛ {rest}
        ≈ᵛ ( (σᵛ L (H.eout e) ⊗ᵛ idᵛ {rest})
               ∘ᵛ ((idᵛ {L} ⊗ᵛ gen' e) ⊗ᵛ idᵛ {rest}) )
             ∘ᵛ (σᵛ (H.ein e) L ⊗ᵛ idᵛ {rest})
    box-block-slideᵛ e L rest =
      ≈-trans (⊗-respᵛ (box-conjᵛ (gen' e) L) ≈-refl)
        (≈-trans (⊗id-distᵛ (σᵛ L (H.eout e))
                   ((idᵛ {L} ⊗ᵛ gen' e) ∘ᵛ σᵛ (H.ein e) L))
          (≈-trans (∘-resp ≈-refl
                     (⊗id-distᵛ (idᵛ {L} ⊗ᵛ gen' e) (σᵛ (H.ein e) L)))
            (≈-sym assocˢ)))

    -- the same slide on the fired layer's residual `L ++ rest`, re-bracketed
    -- by `box-suffix-≈̂ᵛ` (heterogeneous, so the re-bracketing is not named).
    box-slide-restˢ
      : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
      → gen' e ⊗ᵛ idᵛ {L ++ rest}
        ≈̂ ( (σᵛ L (H.eout e) ⊗ᵛ idᵛ {rest})
              ∘ᵛ ((idᵛ {L} ⊗ᵛ gen' e) ⊗ᵛ idᵛ {rest}) )
            ∘ᵛ (σᵛ (H.ein e) L ⊗ᵛ idᵛ {rest})
    box-slide-restˢ e L rest =
      ≈̂-trans (≈̂-sym (box-suffix-≈̂ᵛ (gen' e) L rest))
              (≈ˢ⇒≈̂ (box-block-slideᵛ e L rest))

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
    -- The thin wiring-groupoid calculus (F11): ⟦bswap⟧ᵛ/⟦frameˡ⟧ᵛ/⟦absorbˡ⟧ +
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

    -- The OUTPUT-braid reframings.  At V level they are plain `++`
    -- associativity: the `map`-distribution the label-level spelling needed
    -- is carried by `_⊗ᵛ_`/`σᵛ` themselves.
    odom : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (L ++ H.eout e) ++ rest ≡ L ++ (H.eout e ++ rest)
    odom e L rest = ++-assoc L (H.eout e) rest

    ocod : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → (H.eout e ++ L) ++ rest ≡ H.eout e ++ (L ++ rest)
    ocod e L rest = ++-assoc (H.eout e) L rest

    -- re-bracket `ein ++ (L ++ rest)` ⇝ `(ein ++ L) ++ rest`.
    brkIn : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → H.ein e ++ (L ++ rest) ≡ (H.ein e ++ L) ++ rest
    brkIn e L rest = sym (++-assoc (H.ein e) L rest)

    -- re-bracket `L ++ (ein ++ rest)` ⇝ `(L ++ ein) ++ rest`.
    brkL : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
         → L ++ (H.ein e ++ rest) ≡ (L ++ H.ein e) ++ rest
    brkL e L rest = sym (++-assoc L (H.ein e) rest)

    ----------------------------------------------------------------------
    -- ## The block algebra `fire-slideˢ` runs in, all at V level.
    --   OUT  = the output block braid            MID  = the box in `((-))`
    --   MIDi = the box in `(-(-))`               INP  = the framed layer perm
    --   INσ  = the input block braid            IN   = the located layer perm
    ----------------------------------------------------------------------

    private
      gen' : ∀ (e : Fin H.nE) → HomV (H.ein e) (H.eout e)
      gen' e = genˢ (H.elab e)

      box-slide-restᵛ = TKB.box-slide-restˢ H permˢ-K

      OUT : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → HomV ((L ++ H.eout e) ++ rest) ((H.eout e ++ L) ++ rest)
      OUT e L rest = σᵛ L (H.eout e) ⊗ᵛ idᵛ {rest}

      MID : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → HomV ((L ++ H.ein e) ++ rest) ((L ++ H.eout e) ++ rest)
      MID e L rest = (idᵛ {L} ⊗ᵛ gen' e) ⊗ᵛ idᵛ {rest}

      MIDi : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
           → HomV (L ++ (H.ein e ++ rest)) (L ++ (H.eout e ++ rest))
      MIDi e L rest = idᵛ {L} ⊗ᵛ (gen' e ⊗ᵛ idᵛ {rest})

      INP : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
              (p : xs Perm.↭ H.ein e ++ rest)
          → HomV (L ++ xs) (L ++ (H.ein e ++ rest))
      INP e L xs rest p = idᵛ {L} ⊗ᵛ permuteᵛ p

      INσ : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
          → HomV ((H.ein e ++ L) ++ rest) ((L ++ H.ein e) ++ rest)
      INσ e L rest = σᵛ (H.ein e) L ⊗ᵛ idᵛ {rest}

      IN : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
             (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
         → HomV (L ++ xs) ((H.ein e ++ L) ++ rest)
      IN e L xs rest perm' = castᵛ refl (brkIn e L rest) (permuteᵛ perm')

      -- the canonical composite both sides of `fire-slideˢ` reduce to.
      CANON : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
                (p : xs Perm.↭ H.ein e ++ rest)
            → HomV (L ++ xs) ((H.eout e ++ L) ++ rest)
      CANON e L xs rest p =
        OUT e L rest
          ∘ᵛ castᵛ refl (sym (odom e L rest))
               (MIDi e L rest ∘ᵛ INP e L xs rest p)

      -- The framed inner fire layer splits into the framed box and the framed
      -- layer permute: `edge-step-firedᵛ` presents the fired layer, then
      -- `id⊗-distᵛ` distributes the `idᵛ {L}` frame.
      framed-fire-split
        : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
            (p : xs Perm.↭ H.ein e ++ rest)
        → idᵛ {L} ⊗ᵛ fire-termˢ e xs rest p
          ≈ᵛ MIDi e L rest ∘ᵛ INP e L xs rest p
      framed-fire-split e L xs rest p =
        ≈-trans (⊗-respᵛ ≈-refl (edge-step-firedᵛ e rest p))
                (id⊗-distᵛ (gen' e ⊗ᵛ idᵛ {rest}) (permuteᵛ p))

      -- The OUTPUT braid IS the σ-block `OUT` (`⟦bswap⟧ᵛ`, cast peeled).
      out-braid-σ
        : ∀ (e : Fin H.nE) (L rest : List (Fin H.nV))
        → castᵛ (odom e L rest) (ocod e L rest) (permuteᵛ (obraid e L rest))
          ≈̂ OUT e L rest
      out-braid-σ e L rest =
        ≈̂-trans (castᵛ-≈̂ (odom e L rest) (ocod e L rest)
                   (permuteᵛ (obraid e L rest)))
                (≈ˢ⇒≈̂ (⟦bswap⟧ᵛ L (H.eout e) rest))

      -- RHS reduction: the output braid plus the framed inner fire layer is
      -- the canonical composite.
      rhs-canon
        : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
            (p : xs Perm.↭ H.ein e ++ rest)
        → castᵛ (odom e L rest) (ocod e L rest) (permuteᵛ (obraid e L rest))
            ∘ᵛ (idᵛ {L} ⊗ᵛ fire-termˢ e xs rest p)
          ≈̂ CANON e L xs rest p
      rhs-canon e L xs rest p =
        ∘-resp-≈̂ (out-braid-σ e L rest)
          (≈̂-trans (≈ˢ⇒≈̂ (framed-fire-split e L xs rest p))
                   (≈̂-sym (castᵛ-≈̂ refl (sym (odom e L rest))
                             (MIDi e L rest ∘ᵛ INP e L xs rest p))))

      -- MID + IN reconciliation: the carried-block box after the input σ-block
      -- and the located layer permute is the canonical inner box.  The box
      -- re-bracketing is `⊗-assoc-≈̂ᵛ`; the wiring is rigid (`rigid-≈̂` on the
      -- `Unique` input stack), with `⟦bswap⟧ᵛ` presenting the σ-block and
      -- `⟦frameˡ⟧ᵛ` the frame.
      mid-in-canon
        : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
            (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
            (p : xs Perm.↭ H.ein e ++ rest)
        → Unique ((L ++ H.ein e) ++ rest)
        → MID e L rest ∘ᵛ (INσ e L rest ∘ᵛ IN e L xs rest perm')
          ≈̂ castᵛ refl (sym (odom e L rest))
              (MIDi e L rest ∘ᵛ INP e L xs rest p)
      mid-in-canon e L xs rest perm' p uIn =
        ≈̂-trans (∘-resp-≈̂ (⊗-assoc-≈̂ᵛ (idᵛ {L}) (gen' e) (idᵛ {rest})) in≈̂)
                (≈̂-sym (castᵛ-≈̂ refl (sym (odom e L rest))
                          (MIDi e L rest ∘ᵛ INP e L xs rest p)))
        where
          in≈̂ : (INσ e L rest ∘ᵛ IN e L xs rest perm') ≈̂ INP e L xs rest p
          in≈̂ =
            ≈̂-trans (∘-resp-≈̂ (≈̂-sym (≈ˢ⇒≈̂ (⟦bswap⟧ᵛ (H.ein e) L rest)))
                       (≈̂-trans (castᵛ-≈̂ refl (brkIn e L rest) (permuteᵛ perm'))
                                (≈̂-sym (⟦absorbˡ⟧ (brkIn e L rest)))))
            (≈̂-trans
              (rigid-≈̂ uIn
                (Perm.trans (Perm.trans perm' (Perm.↭-reflexive (brkIn e L rest)))
                            (ibraid e L rest))
                (Perm.trans (PermProp.++⁺ˡ L p) (Perm.↭-reflexive (brkL e L rest))))
              (≈̂-trans (⟦absorbˡ⟧ (brkL e L rest))
                       (≈ˢ⇒≈̂ (⟦frameˡ⟧ᵛ L p))))

    ----------------------------------------------------------------------
    -- ## (b) `fire-slideˢ` — the single fired box slides past `L`.
    --
    --   fire-termˢ e (L ++ xs) (L ++ rest) perm'
    --     ≈ᵛ castᵛ (odom)(ocod) (permuteᵛ (obraid e L rest))
    --         ∘ᵛ (idᵛ {L} ⊗ᵛ fire-termˢ e xs rest p)
    --
    -- Requires `Unique ((L ++ ein e) ++ rest)`.  Both sides reduce to `CANON`:
    -- the LHS via `edge-step-firedᵛ` + `box-slide-restᵛ` + `mid-in-canon`, the
    -- RHS via `rhs-canon`.  The statement is cast-free apart from the two
    -- `++`-associativity transports of the output braid.
    ----------------------------------------------------------------------
    fire-slideˢ
      : ∀ (e : Fin H.nE) (L xs rest : List (Fin H.nV))
          (perm' : (L ++ xs) Perm.↭ H.ein e ++ (L ++ rest))
          (p : xs Perm.↭ H.ein e ++ rest)
      → Unique ((L ++ H.ein e) ++ rest)
      → fire-termˢ e (L ++ xs) (L ++ rest) perm'
        ≈ᵛ castᵛ (odom e L rest) (ocod e L rest) (permuteᵛ (obraid e L rest))
             ∘ᵛ (idᵛ {L} ⊗ᵛ fire-termˢ e xs rest p)
    fire-slideˢ e L xs rest perm' p uIn =
      ≈̂⇒≈ˢ (≈̂-trans lhs≈̂canon (≈̂-sym (rhs-canon e L xs rest p)))
      where
        lhs≈̂canon : fire-termˢ e (L ++ xs) (L ++ rest) perm' ≈̂ CANON e L xs rest p
        lhs≈̂canon =
          ≈̂-trans (≈ˢ⇒≈̂ (edge-step-firedᵛ e (L ++ rest) perm'))
          (≈̂-trans (∘-resp-≈̂ (box-slide-restᵛ e L rest)
                     (≈̂-sym (castᵛ-≈̂ refl (brkIn e L rest) (permuteᵛ perm'))))
          (≈̂-trans (≈ˢ⇒≈̂ assocˢ)
          (≈̂-trans (≈ˢ⇒≈̂ assocˢ)
                   (∘-resp-≈̂ ≈̂-refl (mid-in-canon e L xs rest perm' p uIn)))))
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
    -- `KCleanˢ es L s_R` is the clean target `idᵛ {L} ⊗ᵛ <clean K-run on s_R>`
    -- (the strict twin of the non-strict `KClean`, where `BTC.uf++` becomes the
    -- `⊗ᵛ` frame — no `unflatten-++-≅` cone is needed in the strict world).
    --
    -- The clean K-run is `proj₂ (process-edgesˢ es s_R)` — the SAME `kblk`-run
    -- restricted to the pure-`s_R` stack.  Here `L` is the carried prefix and
    -- `s_R` the K-side stack; the actual mixed stack `↭`s `L ++ s_R`.

    KCleanˢ
      : ∀ (es : List (Fin H.nE)) (L s_R : List (Fin H.nV))
      → HomV (L ++ s_R) (L ++ proj₁ (process-edgesˢ es s_R))
    KCleanˢ es L s_R = idᵛ {L} ⊗ᵛ proj₂ (process-edgesˢ es s_R)

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
          (KCleanHd : HomV (L ++ s_R) (L ++ proj₁ (edge-stepˢ s_R e)))
          (tH : HomV s s1)
      → Set
    HeadReconcileˢ e L s_R s s1 pf pf1 KCleanHd tH =
      permuteᵛ pf1 ∘ᵛ tH ≈ᵛ KCleanHd ∘ᵛ permuteᵛ pf

    ----------------------------------------------------------------------
    -- ## `KCleanˢ` empty + cons telescoping.
    ----------------------------------------------------------------------

    -- `[]`: the clean block on `[]` edges is `idᵛ {L} ⊗ᵛ idᵛ {s_R}`.
    KCleanˢ-nil : ∀ (L s_R : List (Fin H.nV)) → KCleanˢ [] L s_R ≈ᵛ idᵛ {L ++ s_R}
    KCleanˢ-nil L s_R = ⊗-idᵛ

    ----------------------------------------------------------------------
    -- ## The clean single-edge head block.
    --
    -- `KCleanHeadˢ e L s_R` is the clean head `idᵛ {L} ⊗ᵛ <clean head term on
    -- s_R>`; the clean head term is `proj₂ (edge-stepˢ s_R e)`.
    ----------------------------------------------------------------------

    KCleanHeadˢ
      : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
      → HomV (L ++ s_R) (L ++ proj₁ (edge-stepˢ s_R e))
    KCleanHeadˢ e L s_R = idᵛ {L} ⊗ᵛ proj₂ (edge-stepˢ s_R e)

    ----------------------------------------------------------------------
    -- ## `KCleanˢ` cons telescoping.
    --
    -- The clean run `KCleanˢ (e ∷ es) L s_R` factors as the clean tail
    -- `KCleanˢ es L (edge-stepˢ s_R e).₁` post-composed with the clean head
    -- `KCleanHeadˢ e L s_R`.  Both are `idᵛ {L} ⊗ᵛ (-)`, so this is exactly
    -- `id⊗-distᵛ` (the strict twin of `KClean-cons`).
    ----------------------------------------------------------------------

    private
      s_R1 : (e : Fin H.nE) (s_R : List (Fin H.nV)) → List (Fin H.nV)
      s_R1 e s_R = proj₁ (edge-stepˢ s_R e)

    KCleanˢ-cons
      : ∀ (e : Fin H.nE) (es : List (Fin H.nE)) (L s_R : List (Fin H.nV))
      → KCleanˢ (e ∷ es) L s_R
        ≈ᵛ KCleanˢ es L (s_R1 e s_R) ∘ᵛ KCleanHeadˢ e L s_R
    KCleanˢ-cons e es L s_R =
      id⊗-distᵛ (proj₂ (process-edgesˢ es (s_R1 e s_R))) (proj₂ (edge-stepˢ s_R e))

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
      → permuteᵛ Br ∘ᵛ permuteᵛ pf ≈ᵛ idᵛ {s}
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
        ≈ᵛ permuteᵛ Br ∘ᵛ (KCleanˢ es L s_R ∘ᵛ permuteᵛ pf)
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

        IH : proj₂ (process-edgesˢ es s1) ≈ᵛ permuteᵛ Br ∘ᵛ (KCleanˢ es L sR1 ∘ᵛ permuteᵛ pf1)
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
        ( permuteᵛ β ∘ᵛ proj₂ (edge-stepˢ (L ++ s_R) e)
          ≈ᵛ KCleanHeadˢ e L s_R )

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
        goal : permuteᵛ (Perm.trans ρf β) ∘ᵛ tH ≈ᵛ KCleanHeadˢ e L s_R ∘ᵛ permuteᵛ pf
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
  open import Categories.APROP.Hypergraph.Soundness.Strict.Separability sig
    using (extract-prefix-++ʳ; extract-prefix-++ʳ-nothing)
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUnique sig as SU
  import Categories.APROP.Hypergraph.Soundness.Discharge.Sub.StackUniqueReach sig as SUR
  open import Data.Fin using (_↑ˡ_; _↑ʳ_; splitAt)
  open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
  import Data.Fin.Properties as FinP
  open import Data.Empty using (⊥; ⊥-elim)
  open import Relation.Nullary using (yes; no)
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  open import Data.Maybe using (Maybe; just; nothing)

  open EquivStep H using (pvv-inverse-leftˢ)

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
    -- (`extract-prefix-++ʳ-nothing`); both `edge-stepˢ` are `idˢ`,
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
          slide
            : permuteᵛ {as = L ++ s_R} Perm.↭-refl ∘ᵛ idᵛ {L ++ s_R}
              ≈ᵛ idᵛ {L} ⊗ᵛ idᵛ {s_R}
          slide = ≈-trans idˡ (≈-sym ⊗-idᵛ)

    head-slide-skip
      : ∀ (e : Fin H.nE) (L s_R : List (Fin H.nV))
      → ein-disjⁱ e L
      → extract-prefix (H.ein e) s_R ≡ nothing
      → HeadSlideˢ e L s_R
    head-slide-skip e L s_R disj eqn =
      head-slide-skip-core e L s_R eqn
        (extract-prefix-++ʳ-nothing (H.ein e) L s_R disj eqn)

    ----------------------------------------------------------------------
    -- ## FIRE case of `HeadSlideˢ`.
    --
    -- When `e` fires on the clean K-side `s_R` (residual `rest_R`, perm `p`)
    -- and `H.ein e` is disjoint from `L`, `extract-prefix-++ʳ` pins the
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
      -- The output braid, presented on the box's own bracketing: the two
      -- `++`-associativity transports of `castₒ` are absorbed as reindexing
      -- factors of the derivation itself (`castᵛ-perm`).
      obraidᴬ
        : (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → (L ++ (H.eout e ++ rest_R)) Perm.↭ (H.eout e ++ (L ++ rest_R))
      obraidᴬ e L rest_R =
        Perm.trans (Perm.↭-reflexive (sym (odom e L rest_R)))
          (Perm.trans (obraid e L rest_R)
                      (Perm.↭-reflexive (ocod e L rest_R)))

      -- the slide braid: move the fired output block `H.eout e` back past `L`.
      slideβ
        : (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → (H.eout e ++ (L ++ rest_R)) Perm.↭ (L ++ (H.eout e ++ rest_R))
      slideβ e L rest_R = Perm.↭-sym (obraidᴬ e L rest_R)

      -- `slide-braid-cancel`: the slide braid IS the inverse of the (reindexed)
      -- output braid, so the round trip is `pvv-inverse-leftˢ`.
      slide-braid-cancel
        : ∀ (e : Fin H.nE) (L rest_R : List (Fin H.nV))
        → permuteᵛ (slideβ e L rest_R)
            ∘ᵛ castᵛ (odom e L rest_R) (ocod e L rest_R)
                     (permuteᵛ (obraid e L rest_R))
          ≈ᵛ idᵛ {L ++ (H.eout e ++ rest_R)}
      slide-braid-cancel e L rest_R =
        ≈-trans (∘-resp ≈-refl (castᵛ-perm (odom e L rest_R) (ocod e L rest_R)
                                  (obraid e L rest_R)))
                (pvv-inverse-leftˢ (obraidᴬ e L rest_R))

    head-slide-fire
      : ∀ (e : Fin H.nE) (L s_R rest_R : List (Fin H.nV))
          (p : s_R Perm.↭ H.ein e ++ rest_R)
      → ein-disjⁱ e L
      → extract-prefix (H.ein e) s_R ≡ just (rest_R , p)
      → Unique ((L ++ H.ein e) ++ rest_R)
      → HeadSlideˢ e L s_R
    head-slide-fire e L s_R rest_R p disj eqR uIn with extract-prefix-++ʳ (H.ein e) L s_R disj eqR
    ... | D , eqLR
      rewrite eqR | eqLR = slideβ e L rest_R , slide-eq
      where
        slide-eq
          : permuteᵛ (slideβ e L rest_R)
              ∘ᵛ fire-termˢ e (L ++ s_R) (L ++ rest_R) D
            ≈ᵛ idᵛ {L} ⊗ᵛ fire-termˢ e s_R rest_R p
        slide-eq =
          ≈-trans (∘-resp ≈-refl (fire-slideˢ e L s_R rest_R D p uIn))
          (≈-trans (≈-sym assocˢ)
                   (≈-trans (∘-resp (slide-braid-cancel e L rest_R) ≈-refl) idˡ))

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

