{-# OPTIONS --with-K #-}

--------------------------------------------------------------------------------
-- Generic OUTPUT-side block-braiding coherence underlying
-- `FireMidInterchange.vout-coh-eq′` (the dual of `vin-coh-eq′`).
--
-- ## What this module provides
--
-- A SINGLE generic block-braiding lemma `σ-block-app` (the keystone: the
-- braiding `σ` of two `unflatten` blocks `as`, `bs` — conjugated by the
-- `unflatten-++-≅` rebracketings — is exactly the `permute` of the
-- append-commutativity permutation `as ++ bs ↭ bs ++ as`), and from it two
-- consumer lemmas:
--
--   * `vin-coh`  — the FROM-orientation input-frame σ-coherence
--                  (the `vin-coh-eq′` content);
--   * `vout-coh` — the TO-orientation output-frame σ-coherence
--                  (the `vout-coh-eq′` content, the dual).
--
-- Both consumers are pure CONSEQUENCES of `σ-block-app` + faithfulness
-- (`FaithfulnessResidual.permute-resp-≅↭`): once the lone `σ ⊗ id` factor
-- is rewritten (via `σ-block-app`) into a `permute`, the entire equation
-- becomes a `permute`-vs-`permute` statement between two permutations with
-- the SAME endpoints, which faithfulness closes.
--
-- ## Generic setting
--
-- We work at the abstract `FreeMonoidalData d` level (as `BraidBlock` /
-- `BraidPermute` do), with an abstract vertex set `(n , vlab)` so that the
-- view frames are built from `permute-via-vlab` exactly as in
-- `FireMidInterchange`.  The three abstract block lists are
-- `as bs cs : List (Fin n)` — instantiated by `FireMidInterchange` at
-- `as = eout e`, `bs = eout e'`, `cs = Rlist`.
--
-- `--with-K`.  The only genuinely-axiomatic input is the supplied
-- `FaithfulnessResidual` (the standard `permute` coherence obligation,
-- already a parameter `K` of `FireMidInterchange`); `σ-block-app` and the
-- two consumers are proven structurally / postulate-free in this module.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFVoutCoh
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open FreeMonoidal d

open import Categories.PermuteCoherence.Faithfulness d
  using (unflatten; unflatten-++-≅; permute; FaithfulnessResidual)
open import Categories.PermuteCoherence.Canonical using (_≅↭_)
open import Categories.FreeSMC.Steps d using (permute-via-vlab)
import Categories.APROP.Hypergraph.Completeness.Discharge.Sub.BlockNFBraid d
  as BlockNFBraid

open import Categories.Category using (Category)
open import Categories.Morphism FreeMonoidal using (_≅_; module ≅; Iso)

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst₂)

private
  module FM = Category FreeMonoidal

open FM.HomReasoning

--------------------------------------------------------------------------------
-- ## The view-frame isos, REPLICATED VERBATIM from `FireMidInterchange`
-- (`R-obj`, `uf++`, `view-in≅`, `view-out≅`) so the consumer instantiations
-- are DEFINITIONALLY equal to the private definitions there.
--
-- These are parameterised over the abstract vertex set `(n , vlab)` and the
-- three abstract block lists; no hypergraph is needed.

module _ {n : ℕ} (vlab : Fin n → X) where

  Aof : List (Fin n) → ObjTerm
  Aof xs = unflatten (map vlab xs)

  R-obj : List (Fin n) → ObjTerm
  R-obj cs = unflatten (map vlab cs)

  -- Map-bridged `unflatten-++-≅` (FireMidInterchange's `uf++`).
  uf++ : (As Bs : List (Fin n))
       → unflatten (map vlab (As ++ Bs))
         ≅ unflatten (map vlab As) ⊗₀ unflatten (map vlab Bs)
  uf++ As Bs =
    subst₂ _≅_
      (cong unflatten (sym (map-++ vlab As Bs)))
      refl
      (unflatten-++-≅ (map vlab As) (map vlab Bs))

  -- Right-whisker an iso by `id` (FireMidInterchange's local `≅⊗id`).
  ≅⊗id : ∀ {Z : ObjTerm} {U V : ObjTerm} → U ≅ V → U ⊗₀ Z ≅ V ⊗₀ Z
  ≅⊗id {Z} i = record
    { from = _≅_.from i ⊗₁ id
    ; to   = _≅_.to   i ⊗₁ id
    ; iso  = record
      { isoˡ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                 (≈-Term-trans (⊗-resp-≈ (_≅_.isoˡ i) idˡ) id⊗id≈id)
      ; isoʳ = ≈-Term-trans (≈-Term-sym ⊗-∘-dist)
                 (≈-Term-trans (⊗-resp-≈ (_≅_.isoʳ i) idˡ) id⊗id≈id)
      }
    }

  -- Input/output view isos: identical shape on the corresponding blocks.
  view≅
    : (as bs cs : List (Fin n))
    → unflatten (map vlab ((as ++ bs) ++ cs))
      ≅ (Aof as ⊗₀ Aof bs) ⊗₀ R-obj cs
  view≅ as bs cs =
    ≅.trans (uf++ (as ++ bs) cs)
            (≅⊗id (uf++ as bs))

  -- Short alias.
  pvl : {xs ys : List (Fin n)} → xs Perm.↭ ys
      → HomTerm (unflatten (map vlab xs)) (unflatten (map vlab ys))
  pvl = permute-via-vlab vlab

  -- `permute-via-vlab` is a ↭-functor: it sends `trans` to `∘` (DEFINITIONALLY,
  -- since both `map⁺` and `permute` recurse on `trans`).
  pvl-trans
    : {xs ys zs : List (Fin n)} (p : xs Perm.↭ ys) (q : ys Perm.↭ zs)
    → pvl (Perm.trans p q) ≈Term pvl q ∘ pvl p
  pvl-trans p q = ≈-Term-refl

  -- The canonical block-swap permutation that the braiding realises:
  -- swap the two front blocks `as`, `bs`, keeping the residual `cs` fixed.
  app-swap : (as bs cs : List (Fin n))
           → (as ++ bs) ++ cs Perm.↭ (bs ++ as) ++ cs
  app-swap as bs cs = PermProp.++⁺ʳ cs (PermProp.++-comm as bs)

  --------------------------------------------------------------------
  -- ## The two PURE structural residuals the keystone reduces to.
  --
  -- These are stated WITHOUT any `view`/`σ⊗id` conjugation, `vl₁/vl₂`,
  -- `r-stk`, or faithfulness — they are exactly the `unflatten-++-≅`
  -- block-rebracketing facts (the `BraidBlock`/`BraidPermute`-shaped
  -- coherence), isolated.
  --
  --   * `σ-block-comm`  — the bare two-block braiding: the braiding of the
  --                       two `unflatten` blocks, conjugated by the
  --                       `unflatten-++-≅` rebrackets, is the `permute` of
  --                       the append-commutativity permutation.  This is
  --                       the genuine `BraidPermute` content (iterated
  --                       `σ-rotate`), at the `map vlab` block level.
  --   * `frame-ext`     — the residual-`cs` framing: a block `permute P`
  --                       (on the front `(as++bs)`-portion) tensored with
  --                       `id` on `cs`, conjugated by `unflatten-++-≅`, is
  --                       the `permute` of `P` extended over `cs`
  --                       (`++⁺ʳ cs P`).  Pure `unflatten-++-≅` naturality.
  σ-block-comm
    : (as bs : List (Fin n))
    → _≅_.to (uf++ bs as) ∘ (σ {Aof as} {Aof bs}) ∘ _≅_.from (uf++ as bs)
      ≈Term pvl (PermProp.++-comm as bs)
  σ-block-comm = BlockNFBraid.σ-block-comm vlab

  frame-ext
    : (es fs cs : List (Fin n)) (P : es Perm.↭ fs)
    → _≅_.to (uf++ fs cs) ∘ (pvl P ⊗₁ id {A = R-obj cs}) ∘ _≅_.from (uf++ es cs)
      ≈Term pvl (PermProp.++⁺ʳ cs P)
  frame-ext = BlockNFBraid.frame-ext vlab

  --------------------------------------------------------------------
  -- ## The KEYSTONE (BraidBlock core), now PROVEN from the two pure
  -- residuals by the `≅⊗id` / `⊗-∘-dist` conjugation algebra (the
  -- braiding-glue, fully mechanized here): the `σ ⊗ id` factor conjugated
  -- by the two swapped-order view frames is the `permute` of the canonical
  -- block-swap.  TO-orientation; shared by `vin-coh` and `vout-coh`.

  σ-frame-app-to
    : (as bs cs : List (Fin n))
    → _≅_.to (view≅ bs as cs)
        ∘ (σ {Aof as} {Aof bs} ⊗₁ id {A = R-obj cs})
        ∘ _≅_.from (view≅ as bs cs)
      ≈Term pvl (app-swap as bs cs)
  σ-frame-app-to as bs cs = begin
      -- view≅ unfolds (definitionally) into the outer `uf++ (·) cs` frame
      -- composed with the inner `≅⊗id (uf++ · ·)` whisker; `to`/`from` of
      -- `≅⊗id` are `(· ⊗₁ id)`.  First reassociate to expose the inner
      -- `(· ⊗ id)` chain to `collapse`.
      (_≅_.to (uf++ (bs ++ as) cs) ∘ (_≅_.to (uf++ bs as) ⊗₁ id))
        ∘ ((σ ⊗₁ id)
        ∘ ((_≅_.from (uf++ as bs) ⊗₁ id) ∘ _≅_.from (uf++ (as ++ bs) cs)))
        ≈⟨ assoc ⟩
      _≅_.to (uf++ (bs ++ as) cs)
        ∘ ((_≅_.to (uf++ bs as) ⊗₁ id)
        ∘ ((σ ⊗₁ id)
        ∘ ((_≅_.from (uf++ as bs) ⊗₁ id) ∘ _≅_.from (uf++ (as ++ bs) cs))))
        ≈⟨ refl⟩∘⟨ collapse ⟩
      _≅_.to (uf++ (bs ++ as) cs)
        ∘ ((_≅_.to (uf++ bs as) ∘ σ ∘ _≅_.from (uf++ as bs)) ⊗₁ id)
        ∘ _≅_.from (uf++ (as ++ bs) cs)
        ≈⟨ refl⟩∘⟨ (⊗-resp-≈ (σ-block-comm as bs) ≈-Term-refl ⟩∘⟨refl) ⟩
      _≅_.to (uf++ (bs ++ as) cs)
        ∘ (pvl (PermProp.++-comm as bs) ⊗₁ id)
        ∘ _≅_.from (uf++ (as ++ bs) cs)
        ≈⟨ frame-ext (as ++ bs) (bs ++ as) cs (PermProp.++-comm as bs) ⟩
      pvl (app-swap as bs cs)
    ∎
    where
      -- `(g₃ ⊗ id) ∘ (g₂ ⊗ id) ∘ ((g₁ ⊗ id) ∘ h) ≈ ((g₃ ∘ g₂ ∘ g₁) ⊗ id) ∘ h`.
      collapse
        : ∀ {U V W Y Z : ObjTerm}
            {g₃ : HomTerm W Y} {g₂ : HomTerm V W} {g₁ : HomTerm U V}
            {h : HomTerm Z (U ⊗₀ R-obj cs)}
        → (g₃ ⊗₁ id {A = R-obj cs}) ∘ (g₂ ⊗₁ id) ∘ ((g₁ ⊗₁ id) ∘ h)
          ≈Term ((g₃ ∘ g₂ ∘ g₁) ⊗₁ id {A = R-obj cs}) ∘ h
      collapse {g₃ = g₃} {g₂} {g₁} {h} = begin
          (g₃ ⊗₁ id) ∘ (g₂ ⊗₁ id) ∘ ((g₁ ⊗₁ id) ∘ h)
            ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
          (g₃ ⊗₁ id) ∘ ((g₂ ⊗₁ id) ∘ (g₁ ⊗₁ id)) ∘ h
            ≈⟨ ≈-Term-sym assoc ⟩
          ((g₃ ⊗₁ id) ∘ ((g₂ ⊗₁ id) ∘ (g₁ ⊗₁ id))) ∘ h
            ≈⟨ (refl⟩∘⟨ (≈-Term-sym ⊗-∘-dist)) ⟩∘⟨refl ⟩
          ((g₃ ⊗₁ id) ∘ ((g₂ ∘ g₁) ⊗₁ (id ∘ id))) ∘ h
            ≈⟨ (refl⟩∘⟨ ⊗-resp-≈ ≈-Term-refl idˡ) ⟩∘⟨refl ⟩
          ((g₃ ⊗₁ id) ∘ ((g₂ ∘ g₁) ⊗₁ id)) ∘ h
            ≈⟨ (≈-Term-sym ⊗-∘-dist) ⟩∘⟨refl ⟩
          ((g₃ ∘ (g₂ ∘ g₁)) ⊗₁ (id ∘ id)) ∘ h
            ≈⟨ ⊗-resp-≈ ≈-Term-refl idˡ ⟩∘⟨refl ⟩
          ((g₃ ∘ (g₂ ∘ g₁)) ⊗₁ id) ∘ h
            ≈⟨ ⊗-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩∘⟨refl ⟩
          (((g₃ ∘ g₂) ∘ g₁) ⊗₁ id) ∘ h
            ≈⟨ ⊗-resp-≈ assoc ≈-Term-refl ⟩∘⟨refl ⟩
          ((g₃ ∘ g₂ ∘ g₁) ⊗₁ id) ∘ h
        ∎

  --------------------------------------------------------------------
  -- ## (★)  The keystone re-stated with the braiding on the LEFT of the
  -- FROM-frame (input orientation), derived from `σ-frame-app-to` by
  -- cancelling one view-iso.  Shared by `vin-coh`.

  σ-frame-app-from
    : (as bs cs : List (Fin n))
    → (σ {Aof bs} {Aof as} ⊗₁ id {A = R-obj cs}) ∘ _≅_.from (view≅ bs as cs)
      ≈Term _≅_.from (view≅ as bs cs) ∘ pvl (app-swap bs as cs)
  σ-frame-app-from as bs cs = begin
      (σ ⊗₁ id) ∘ _≅_.from (view≅ bs as cs)
        ≈⟨ ≈-Term-sym idˡ ⟩
      id ∘ ((σ ⊗₁ id) ∘ _≅_.from (view≅ bs as cs))
        ≈⟨ (≈-Term-sym (Iso.isoʳ (_≅_.iso (view≅ as bs cs)))) ⟩∘⟨refl ⟩
      (_≅_.from (view≅ as bs cs) ∘ _≅_.to (view≅ as bs cs))
        ∘ ((σ ⊗₁ id) ∘ _≅_.from (view≅ bs as cs))
        ≈⟨ assoc ⟩
      _≅_.from (view≅ as bs cs)
        ∘ (_≅_.to (view≅ as bs cs) ∘ ((σ ⊗₁ id) ∘ _≅_.from (view≅ bs as cs)))
        ≈⟨ refl⟩∘⟨ σ-frame-app-to bs as cs ⟩
      _≅_.from (view≅ as bs cs) ∘ pvl (app-swap bs as cs)
    ∎

  --------------------------------------------------------------------
  -- ## The keystone with the trailing `from`-iso cancelled (TO-orientation),
  -- the form `vout-coh` consumes directly:
  --
  --   to(view≅ bs as cs) ∘ (σ ⊗ id)  ≈  pvl(app-swap) ∘ to(view≅ as bs cs)
  --
  -- (post-compose `σ-frame-app-to` with `to(view≅ as bs cs)` and cancel
  -- `from ∘ to = id`).

  σ-frame-app-to′
    : (as bs cs : List (Fin n))
    → _≅_.to (view≅ bs as cs) ∘ (σ {Aof as} {Aof bs} ⊗₁ id {A = R-obj cs})
      ≈Term pvl (app-swap as bs cs) ∘ _≅_.to (view≅ as bs cs)
  σ-frame-app-to′ as bs cs = begin
      _≅_.to (view≅ bs as cs) ∘ (σ ⊗₁ id)
        ≈⟨ ≈-Term-sym idʳ ⟩
      (_≅_.to (view≅ bs as cs) ∘ (σ ⊗₁ id)) ∘ id
        ≈⟨ refl⟩∘⟨ ≈-Term-sym (Iso.isoʳ (_≅_.iso (view≅ as bs cs))) ⟩
      (_≅_.to (view≅ bs as cs) ∘ (σ ⊗₁ id))
        ∘ (_≅_.from (view≅ as bs cs) ∘ _≅_.to (view≅ as bs cs))
        ≈⟨ middle4 ⟩
      (_≅_.to (view≅ bs as cs) ∘ (σ ⊗₁ id) ∘ _≅_.from (view≅ as bs cs))
        ∘ _≅_.to (view≅ as bs cs)
        ≈⟨ σ-frame-app-to as bs cs ⟩∘⟨refl ⟩
      pvl (app-swap as bs cs) ∘ _≅_.to (view≅ as bs cs)
    ∎
    where
      -- (w ∘ x) ∘ (y ∘ z) ≈ (w ∘ x ∘ y) ∘ z   (pure reassociation)
      middle4
        : ∀ {A B C D E : ObjTerm}
            {w : HomTerm D E} {x : HomTerm C D} {y : HomTerm B C} {z : HomTerm A B}
        → (w ∘ x) ∘ (y ∘ z) ≈Term (w ∘ x ∘ y) ∘ z
      middle4 {w = w} {x} {y} {z} = begin
          (w ∘ x) ∘ (y ∘ z)   ≈⟨ assoc ⟩
          w ∘ (x ∘ (y ∘ z))   ≈⟨ refl⟩∘⟨ ≈-Term-sym assoc ⟩
          w ∘ ((x ∘ y) ∘ z)   ≈⟨ ≈-Term-sym assoc ⟩
          (w ∘ (x ∘ y)) ∘ z   ∎

  --------------------------------------------------------------------
  -- ## CONSUMER 1 — `vout-coh` (the OUTPUT-side `vout-coh-eq′` content).
  --
  -- The two swapped-order TO-frames are reconciled by the output locating
  -- permutes `vl₁`/`vl₂` and the reshuffle `rstk`, modulo `σ ⊗ id` on the
  -- two output factors.  Proven from the keystone `σ-frame-app-to′` plus a
  -- single `≅↭`-coherence of the located permutes (discharged by
  -- faithfulness `K`).
  --
  -- The residual hypothesis `coh-out` is the genuine SimLoc coherence: the
  -- two ways from the bracketed output `(as++bs)++cs` to the final stack
  -- `as++r₁'` — (LHS) locate-then-reshuffle `trans vl₁ rstk`, vs (RHS)
  -- block-swap-then-locate `trans (app-swap) vl₂` — agree as bijections.
  module _ (K : FaithfulnessResidual) where
    open FaithfulnessResidual K

    vout-coh
      : (as bs cs r₂ r₁' : List (Fin n))
        (vl₁  : (as ++ bs) ++ cs Perm.↭ bs ++ r₂)
        (vl₂  : (bs ++ as) ++ cs Perm.↭ as ++ r₁')
        (rstk : bs ++ r₂ Perm.↭ as ++ r₁')
        (coh-out : PermProp.map⁺ vlab (Perm.trans vl₁ rstk)
                   ≅↭ PermProp.map⁺ vlab (Perm.trans (app-swap as bs cs) vl₂))
      → pvl rstk ∘ (pvl vl₁ ∘ _≅_.to (view≅ as bs cs))
        ≈Term (pvl vl₂ ∘ _≅_.to (view≅ bs as cs)) ∘ (σ {Aof as} {Aof bs} ⊗₁ id {A = R-obj cs})
    vout-coh as bs cs r₂ r₁' vl₁ vl₂ rstk coh-out = begin
        pvl rstk ∘ (pvl vl₁ ∘ _≅_.to (view≅ as bs cs))
          ≈⟨ ≈-Term-sym assoc ⟩
        (pvl rstk ∘ pvl vl₁) ∘ _≅_.to (view≅ as bs cs)
          ≈⟨ (≈-Term-sym (pvl-trans vl₁ rstk)) ⟩∘⟨refl ⟩
        pvl (Perm.trans vl₁ rstk) ∘ _≅_.to (view≅ as bs cs)
          ≈⟨ permute-resp-≅↭ (PermProp.map⁺ vlab (Perm.trans vl₁ rstk))
                              (PermProp.map⁺ vlab (Perm.trans (app-swap as bs cs) vl₂))
                              coh-out ⟩∘⟨refl ⟩
        pvl (Perm.trans (app-swap as bs cs) vl₂) ∘ _≅_.to (view≅ as bs cs)
          ≈⟨ pvl-trans (app-swap as bs cs) vl₂ ⟩∘⟨refl ⟩
        (pvl vl₂ ∘ pvl (app-swap as bs cs)) ∘ _≅_.to (view≅ as bs cs)
          ≈⟨ assoc ⟩
        pvl vl₂ ∘ (pvl (app-swap as bs cs) ∘ _≅_.to (view≅ as bs cs))
          ≈⟨ refl⟩∘⟨ ≈-Term-sym (σ-frame-app-to′ as bs cs) ⟩
        pvl vl₂ ∘ (_≅_.to (view≅ bs as cs) ∘ (σ ⊗₁ id))
          ≈⟨ ≈-Term-sym assoc ⟩
        (pvl vl₂ ∘ _≅_.to (view≅ bs as cs)) ∘ (σ ⊗₁ id)
      ∎

  --------------------------------------------------------------------
  -- ## CONSUMER 2 — `vin-coh` (the INPUT-side `vin-coh-eq′` content).
  --
  -- The SAME block-braiding keystone in FROM-orientation.  The two
  -- swapped-order FROM-frames (input locating permutes `loc₁`/`loc₂`) are
  -- related by `σ ⊗ id` on the two input factors, modulo a single
  -- `≅↭`-coherence of the input permutes (discharged by `K`).
  module _ (K : FaithfulnessResidual) where
    open FaithfulnessResidual K

    vin-coh
      : (as bs cs sp : List (Fin n))
        (loc₁ : sp Perm.↭ (as ++ bs) ++ cs)
        (loc₂ : sp Perm.↭ (bs ++ as) ++ cs)
        (coh-in : PermProp.map⁺ vlab loc₁
                  ≅↭ PermProp.map⁺ vlab (Perm.trans loc₂ (app-swap bs as cs)))
      → _≅_.from (view≅ as bs cs) ∘ pvl loc₁
        ≈Term (σ {Aof bs} {Aof as} ⊗₁ id {A = R-obj cs})
              ∘ (_≅_.from (view≅ bs as cs) ∘ pvl loc₂)
    vin-coh as bs cs sp loc₁ loc₂ coh-in = begin
        _≅_.from (view≅ as bs cs) ∘ pvl loc₁
          ≈⟨ refl⟩∘⟨ permute-resp-≅↭ (PermProp.map⁺ vlab loc₁)
                                      (PermProp.map⁺ vlab (Perm.trans loc₂ (app-swap bs as cs)))
                                      coh-in ⟩
        _≅_.from (view≅ as bs cs) ∘ pvl (Perm.trans loc₂ (app-swap bs as cs))
          ≈⟨ refl⟩∘⟨ pvl-trans loc₂ (app-swap bs as cs) ⟩
        _≅_.from (view≅ as bs cs) ∘ (pvl (app-swap bs as cs) ∘ pvl loc₂)
          ≈⟨ ≈-Term-sym assoc ⟩
        (_≅_.from (view≅ as bs cs) ∘ pvl (app-swap bs as cs)) ∘ pvl loc₂
          ≈⟨ (≈-Term-sym (σ-frame-app-from as bs cs)) ⟩∘⟨refl ⟩
        ((σ ⊗₁ id) ∘ _≅_.from (view≅ bs as cs)) ∘ pvl loc₂
          ≈⟨ assoc ⟩
        (σ ⊗₁ id) ∘ (_≅_.from (view≅ bs as cs) ∘ pvl loc₂)
      ∎

