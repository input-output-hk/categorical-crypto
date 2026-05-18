{-# OPTIONS #-}

--------------------------------------------------------------------------------
-- Discharge module for `iso-decompose-⊗⊗` from
-- `Hypergraph.Completeness.DecodeRel.RespIso.TensorTensor`.
--
-- ## Goal
--
-- Given `f₁, f₂ : HomTerm A B`, `g₁, g₂ : HomTerm C D`, and a hypergraph
-- iso
--
--   ⟪ f₁ ⊗₁ g₁ ⟫  ≅ᴴ  ⟪ f₂ ⊗₁ g₂ ⟫,
--
-- extract sub-isos
--
--   ⟪ f₁ ⟫  ≅ᴴ  ⟪ f₂ ⟫       and       ⟪ g₁ ⟫  ≅ᴴ  ⟪ g₂ ⟫.
--
-- This is the inverse of `Hypergraph.Congruence.hTensor-resp-≅ᴴ`.
--
-- ## Why it's "just bookkeeping" but still subtle
--
-- Recall `⟪ f ⊗₁ g ⟫ = hTensor ⟪f⟫ ⟪g⟫`, where:
--   * `nV (hTensor G K)  = G.nV + K.nV`         (left/right halves)
--   * `nE (hTensor G K)  = G.nE + K.nE`         (left/right halves)
--   * `dom (hTensor G K) = map injL G.dom ++ map injR K.dom`
--   * `cod (hTensor G K) = map injL G.cod ++ map injR K.cod`
--   * `vlab` splits on `splitAt G.nV` to either G.vlab or K.vlab.
--   * `elab/ein/eout` likewise split on `splitAt G.nE`.
--
-- The iso provides a vertex bijection
--   φ : Fin (⟪f₁⟫.nV + ⟪g₁⟫.nV) → Fin (⟪f₂⟫.nV + ⟪g₂⟫.nV)
-- and an edge bijection
--   ψ : Fin (⟪f₁⟫.nE + ⟪g₁⟫.nE) → Fin (⟪f₂⟫.nE + ⟪g₂⟫.nE).
--
-- "Straight" extraction would restrict φ to the left half of the domain
-- (i.e. the image of `_↑ˡ_`) and verify its image lies in the left half
-- of the codomain.  Then the left restriction is the φ for `⟪f₁⟫ ≅ᴴ ⟪f₂⟫`,
-- and the right restriction is the φ for `⟪g₁⟫ ≅ᴴ ⟪g₂⟫`.
--
-- The truth: the iso φ on `f₁ ⊗₁ g₁` and `f₂ ⊗₁ g₂` is NOT forced to be
-- "straight" purely by the boundary equations.  When `length (flatten A)`
-- matches `length (flatten C)` and vertex labels align (and similarly
-- for B, D), the iso *may* swap halves.  In that crossed case we need a
-- σ-naturality argument akin to the one in `IdSigma.agda`: combine the
-- crossed sub-isos with a swap to obtain the "straight" form.
--
-- Either way, the sub-isos `⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫` and `⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫`
-- always exist — but in the crossed case the *left* sub-iso witnesses
-- `⟪ f₁ ⟫ ≅ᴴ ⟪ g₂ ⟫` (after a label-equality), which by the type
-- signature `f₁, f₂ : HomTerm A B` and `g₁, g₂ : HomTerm C D` cannot
-- happen unless `A ≡ C` and `B ≡ D` propositionally (heterogeneous).
-- For the lemma signature here, the straight case suffices in all uses
-- consumed by `decode-rel-resp-≅ᴴ-⊗⊗`.
--
-- ## Progress in this module
--
-- The following pieces of the discharge are now constructively proved
-- and exported:
--
--   * `dom-split-eq` / `cod-split-eq` — the position-ordered boundary
--     equations restricted to the two halves.  Concretely:
--
--       map injL₂ ⟪f₂⟫.dom ≡ map φ (map injL₁ ⟪f₁⟫.dom)
--       map injR₂ ⟪g₂⟫.dom ≡ map φ (map injR₁ ⟪g₁⟫.dom)
--
--     and analogously for cod.  Obtained from `φ-dom : T₂.dom ≡ map φ T₁.dom`
--     via `++-cancelˡ` after matching the prefix lengths
--     `length ⟪f₂⟫.dom ≡ length ⟪f₁⟫.dom` (both equal `length (flatten A)`).
--
-- The remaining content needed to finish the discharge is the
-- "no half-swap" coherence lemma — see the documentation header
-- block in `RespIso/TensorTensor.agda` for the full statement and the
-- soundness justification.  Concretely, what's missing is:
--
--   no-half-swap-φ
--     : ∀ (iG : Fin ⟪f₁⟫.nV)
--     → ∃[ iG' ∈ Fin ⟪f₂⟫.nV ]
--         (φ (iG ↑ˡ ⟪g₁⟫.nV) ≡ iG' ↑ˡ ⟪g₂⟫.nV)
--
-- (and analogously for ψ, cod, etc.).  On the boundary the existential
-- can be read off from `dom-split-eq`/`cod-split-eq`; on interior vertices
-- it requires either (a) a Linearity-based reachability argument, or
-- (b) the symmetric-monoidal σ-naturality coherence step that
-- characterises the crossed case.  Neither fits in a single focused
-- session, so the discharge of `iso-decompose-⊗⊗` is left as a postulate
-- here; this module is the engineering toolkit for the next attempt.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeTT
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL; hTensor)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.Fin using (_↑ˡ_; _↑ʳ_)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-map; map-++)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

--------------------------------------------------------------------------------
-- Position-ordered boundary slicing.
--
-- The shape of `(hTensor G K).dom` is `map injL G.dom ++ map injR K.dom`
-- (a concatenation of two list segments with known lengths).  Applied to
-- the iso's `φ-dom : T₂.dom ≡ map φ T₁.dom`, this becomes a position-by-
-- position equation between two list concatenations.  Because the
-- *prefixes* have equal lengths (both equal `length (flatten A)`), the
-- equation splits via `++-cancelˡ` into two half-equations.

private
  -- `length`-cancellation: if `xs ++ ys ≡ xs' ++ ys'` and `length xs ≡ length xs'`
  -- then `xs ≡ xs'` and `ys ≡ ys'`.  Proved by induction on `xs/xs'` with
  -- the length hypothesis dispatching the `[]/cons` cases.
  ++-split-eq
    : ∀ {A : Set} (xs xs' ys ys' : List A)
    → length xs ≡ length xs'
    → xs ++ ys ≡ xs' ++ ys'
    → (xs ≡ xs') × (ys ≡ ys')
  ++-split-eq []        []         ys ys' _   eq = refl , eq
  ++-split-eq []        (x' ∷ xs') _  _   ()  _
  ++-split-eq (x ∷ xs)  []         _  _   ()  _
  ++-split-eq (x ∷ xs)  (x' ∷ xs') ys ys' len eq =
    cong₂ _∷_ head-eq rec-l , rec-r
    where
      ∷-head : ∀ {A : Set} {x x' : A} {xs xs' : List A}
             → x ∷ xs ≡ x' ∷ xs' → x ≡ x'
      ∷-head refl = refl

      ∷-tail : ∀ {A : Set} {x x' : A} {xs xs' : List A}
             → x ∷ xs ≡ x' ∷ xs' → xs ≡ xs'
      ∷-tail refl = refl

      head-eq : x ≡ x'
      head-eq = ∷-head eq

      tail-eq : xs ++ ys ≡ xs' ++ ys'
      tail-eq = ∷-tail eq

      len' : length xs ≡ length xs'
      len' = suc-injective len

      rec-l : xs ≡ xs'
      rec-l = proj₁ (++-split-eq xs xs' ys ys' len' tail-eq)

      rec-r : ys ≡ ys'
      rec-r = proj₂ (++-split-eq xs xs' ys ys' len' tail-eq)

--------------------------------------------------------------------------------
-- Main slicing lemma.
--
-- Given a tensor iso, slice the boundary equations along the
-- "left half / right half" cut.  This is half the work of building
-- the sub-isos; the remaining half is the no-half-swap propagation
-- to interior vertices (see the header).

module _
  {A B C D}
  (f₁ : HomTerm A B) (g₁ : HomTerm C D)
  (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  (iso : ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫)
  where

  private
    open _≅ᴴ_ iso

    G₁  = ⟪ f₁ ⟫    ;  G₂  = ⟪ f₂ ⟫
    K₁  = ⟪ g₁ ⟫    ;  K₂  = ⟪ g₂ ⟫

    module G₁ = Hypergraph G₁
    module G₂ = Hypergraph G₂
    module K₁ = Hypergraph K₁
    module K₂ = Hypergraph K₂

    -- Length facts: both G₁.dom and G₂.dom have length `length (flatten A)`.
    -- Likewise G₁.cod, G₂.cod ≡ length (flatten B); K₁.dom, K₂.dom ≡ length (flatten C);
    -- K₁.cod, K₂.cod ≡ length (flatten D).
    length-G₁-dom : length G₁.dom ≡ length (flatten A)
    length-G₁-dom = trans (sym (length-map G₁.vlab G₁.dom)) (cong length (⟪⟫-domL f₁))

    length-G₂-dom : length G₂.dom ≡ length (flatten A)
    length-G₂-dom = trans (sym (length-map G₂.vlab G₂.dom)) (cong length (⟪⟫-domL f₂))

    length-G-dom-eq : length G₂.dom ≡ length G₁.dom
    length-G-dom-eq = trans length-G₂-dom (sym length-G₁-dom)

    length-G₁-cod : length G₁.cod ≡ length (flatten B)
    length-G₁-cod = trans (sym (length-map G₁.vlab G₁.cod)) (cong length (⟪⟫-codL f₁))

    length-G₂-cod : length G₂.cod ≡ length (flatten B)
    length-G₂-cod = trans (sym (length-map G₂.vlab G₂.cod)) (cong length (⟪⟫-codL f₂))

    length-G-cod-eq : length G₂.cod ≡ length G₁.cod
    length-G-cod-eq = trans length-G₂-cod (sym length-G₁-cod)

    -- Same trick after passing through `map injL` / `map (_↑ˡ _)`,
    -- which preserves list length.
    length-injL₁-G-dom : length (map (_↑ˡ K₁.nV) G₁.dom) ≡ length G₁.dom
    length-injL₁-G-dom = length-map (_↑ˡ K₁.nV) G₁.dom

    length-injL₂-G-dom : length (map (_↑ˡ K₂.nV) G₂.dom) ≡ length G₂.dom
    length-injL₂-G-dom = length-map (_↑ˡ K₂.nV) G₂.dom

    length-injL-dom-eq
      : length (map (_↑ˡ K₂.nV) G₂.dom) ≡ length (map φ (map (_↑ˡ K₁.nV) G₁.dom))
    length-injL-dom-eq =
      trans length-injL₂-G-dom
            (trans length-G-dom-eq
                   (trans (sym length-injL₁-G-dom)
                          (sym (length-map φ (map (_↑ˡ K₁.nV) G₁.dom)))))

    -- And on cod.
    length-injL₁-G-cod : length (map (_↑ˡ K₁.nV) G₁.cod) ≡ length G₁.cod
    length-injL₁-G-cod = length-map (_↑ˡ K₁.nV) G₁.cod

    length-injL₂-G-cod : length (map (_↑ˡ K₂.nV) G₂.cod) ≡ length G₂.cod
    length-injL₂-G-cod = length-map (_↑ˡ K₂.nV) G₂.cod

    length-injL-cod-eq
      : length (map (_↑ˡ K₂.nV) G₂.cod) ≡ length (map φ (map (_↑ˡ K₁.nV) G₁.cod))
    length-injL-cod-eq =
      trans length-injL₂-G-cod
            (trans length-G-cod-eq
                   (trans (sym length-injL₁-G-cod)
                          (sym (length-map φ (map (_↑ˡ K₁.nV) G₁.cod)))))

    -- Rewrite `φ-dom` so the right-hand `map φ` distributes over the `_++_`.
    map-φ-distrib-dom
      : map φ (map (_↑ˡ K₁.nV) G₁.dom ++ map (G₁.nV ↑ʳ_) K₁.dom)
      ≡ map φ (map (_↑ˡ K₁.nV) G₁.dom)
        ++ map φ (map (G₁.nV ↑ʳ_) K₁.dom)
    map-φ-distrib-dom =
      map-++ φ (map (_↑ˡ K₁.nV) G₁.dom) (map (G₁.nV ↑ʳ_) K₁.dom)

    -- Now the φ-dom equation `T₂.dom ≡ map φ T₁.dom` becomes
    --   map injL₂ G₂.dom ++ map injR₂ K₂.dom
    --     ≡ map φ (map injL₁ G₁.dom) ++ map φ (map injR₁ K₁.dom)
    φ-dom-split
      : map (_↑ˡ K₂.nV) G₂.dom ++ map (G₂.nV ↑ʳ_) K₂.dom
      ≡ map φ (map (_↑ˡ K₁.nV) G₁.dom) ++ map φ (map (G₁.nV ↑ʳ_) K₁.dom)
    φ-dom-split = trans φ-dom map-φ-distrib-dom

    map-φ-distrib-cod
      : map φ (map (_↑ˡ K₁.nV) G₁.cod ++ map (G₁.nV ↑ʳ_) K₁.cod)
      ≡ map φ (map (_↑ˡ K₁.nV) G₁.cod)
        ++ map φ (map (G₁.nV ↑ʳ_) K₁.cod)
    map-φ-distrib-cod =
      map-++ φ (map (_↑ˡ K₁.nV) G₁.cod) (map (G₁.nV ↑ʳ_) K₁.cod)

    φ-cod-split
      : map (_↑ˡ K₂.nV) G₂.cod ++ map (G₂.nV ↑ʳ_) K₂.cod
      ≡ map φ (map (_↑ˡ K₁.nV) G₁.cod) ++ map φ (map (G₁.nV ↑ʳ_) K₁.cod)
    φ-cod-split = trans φ-cod map-φ-distrib-cod

  -- Position-ordered boundary equations restricted to the left half.
  --
  --   map injL₂ G₂.dom ≡ map φ (map injL₁ G₁.dom)
  --
  -- and similarly for cod.  These are the immediate constraints on φ's
  -- behaviour at left-boundary vertices of T₁.
  dom-split-eq-L : map (_↑ˡ K₂.nV) G₂.dom ≡ map φ (map (_↑ˡ K₁.nV) G₁.dom)
  dom-split-eq-L = proj₁ (++-split-eq _ _ _ _ length-injL-dom-eq φ-dom-split)

  dom-split-eq-R : map (G₂.nV ↑ʳ_) K₂.dom ≡ map φ (map (G₁.nV ↑ʳ_) K₁.dom)
  dom-split-eq-R = proj₂ (++-split-eq _ _ _ _ length-injL-dom-eq φ-dom-split)

  cod-split-eq-L : map (_↑ˡ K₂.nV) G₂.cod ≡ map φ (map (_↑ˡ K₁.nV) G₁.cod)
  cod-split-eq-L = proj₁ (++-split-eq _ _ _ _ length-injL-cod-eq φ-cod-split)

  cod-split-eq-R : map (G₂.nV ↑ʳ_) K₂.cod ≡ map φ (map (G₁.nV ↑ʳ_) K₁.cod)
  cod-split-eq-R = proj₂ (++-split-eq _ _ _ _ length-injL-cod-eq φ-cod-split)

--------------------------------------------------------------------------------
-- Iso decomposition for ⊗⊗.
--
-- The constructive discharge of `iso-decompose-⊗⊗` (which lives in
-- `RespIso/TensorTensor.agda` and is consumed by
-- `DecodeRel/Inductive.agda`) would need the "no half-swap" content
-- described in the header.  The boundary slicing lemmas above
-- (`dom-split-eq-L`/`-R`, `cod-split-eq-L`/`-R`) handle the boundary
-- side; the propagation to interior vertices is the remaining
-- mathematical content.
--
-- The toolkit is left here for the next attempt, so that future work
-- can `open` the boundary slices directly rather than rederiving them.
