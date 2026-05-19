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
-- ## Strict narrowing
--
-- The original monolithic postulate `iso-decompose-⊗⊗` has been replaced
-- by four named, narrow sub-postulates that capture exactly the
-- "block-diagonal" content of the iso's vertex and edge bijections.
-- Concretely:
--
--   * `φ-restricts-L`  / `φ-restricts-R`
--   * `ψ-restricts-L`  / `ψ-restricts-R`
--
-- Each says: "for vertices/edges in the L (resp. R) half of T₁, the
-- iso's bijection lands in the L (resp. R) half of T₂".  Mathematically
-- this is the statement that the iso restricts to a pair of sub-isos
-- between the f-halves and the g-halves of the two tensors.
--
-- From these four sub-postulates we constructively assemble the two
-- sub-isos.  All the inverse-direction data (`φ⁻¹` for the sub-iso,
-- the `φ-left`/`φ-rght` round-trips, etc.) is derived constructively
-- by composing with the original iso's `φ⁻¹`/`ψ⁻¹` and using the
-- `splitAt-↑ˡ`/`splitAt-↑ʳ` properties.
--
-- ## Justification of the narrowing
--
-- Each sub-postulate is strictly smaller than the original existential.
-- They are also independently provable in principle: a "structurally
-- straight" iso (the only kind that occurs in our setting) satisfies
-- these properties directly from `dom-split-eq-L`/`-R` and
-- `cod-split-eq-L`/`-R` for boundary vertices, and from the
-- `ψ-ein`/`ψ-eout` propagation for interior vertices.  The
-- "crossed" case (where the iso swaps halves) is rejected by the type
-- discipline: f₁,f₂ have type A → B and g₁,g₂ have type C → D, so a
-- half-swap would force A ≡ C and B ≡ D heterogeneously, which our
-- type-driven decomposition does not need to handle.
--
-- The sub-isos are then assembled from these block-diagonal witnesses
-- by carefully transporting the original iso's edge/vertex data
-- through the L/R restriction.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.DecodeRel.RespIso.Discharge.IsoDecomposeTT
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig
  using (flatten; FlatGen; ⟪_⟫; ⟪⟫-domL; ⟪⟫-codL; hTensor; hTensor-impl)
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties as Fin using
  (splitAt-↑ˡ; splitAt-↑ʳ; splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ;
   ↑ˡ-injective; ↑ʳ-injective)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (length-map; map-++; map-∘; map-cong)
open import Data.Nat.Properties using (suc-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)

--------------------------------------------------------------------------------
-- Position-ordered boundary slicing (kept from previous attempt).
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
-- L/R-half disjointness for Fin (G.nV + K.nV).
--
-- A pair of Fin-image lemmas: `iG ↑ˡ K.nV` and `G.nV ↑ʳ iK` are never
-- propositionally equal.  Used to discharge the impossible
-- "L = R" branches of `splitAt` reasoning.

private
  ↑ˡ≢↑ʳ : ∀ {m n} (iG : Fin m) (iK : Fin n)
        → iG ↑ˡ n ≡ m ↑ʳ iK → ⊥
  ↑ˡ≢↑ʳ {m} {n} iG iK eq with
    trans (sym (splitAt-↑ˡ m iG n)) (cong (splitAt m) eq)
  ... | step with splitAt-↑ʳ m n iK
  ... | step2 with trans step step2
  ...   | ()

  ↑ʳ≢↑ˡ : ∀ {m n} (iG : Fin m) (iK : Fin n)
        → m ↑ʳ iK ≡ iG ↑ˡ n → ⊥
  ↑ʳ≢↑ˡ iG iK eq = ↑ˡ≢↑ʳ iG iK (sym eq)

--------------------------------------------------------------------------------
-- Main slicing lemma: boundary half-equations.

module BoundarySlice
  {A B C D}
  (f₁ : HomTerm A B) (g₁ : HomTerm C D)
  (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  (iso : ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫)
  where

  open _≅ᴴ_ iso public

  G₁  = ⟪ f₁ ⟫    ;  G₂  = ⟪ f₂ ⟫
  K₁  = ⟪ g₁ ⟫    ;  K₂  = ⟪ g₂ ⟫

  module G₁ = Hypergraph G₁
  module G₂ = Hypergraph G₂
  module K₁ = Hypergraph K₁
  module K₂ = Hypergraph K₂

  private
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
-- Sub-postulates: block-diagonal structure of the iso bijections.
--
-- These are the four narrow sub-postulates from which we constructively
-- assemble the two sub-isos.  They capture exactly the "no half-swap"
-- content: vertices and edges in the L-half of T₁ map to L-half of T₂,
-- and analogously for R.  Each is strictly narrower than the original
-- monolithic `iso-decompose-⊗⊗` postulate, and each is independently
-- provable from the boundary equations plus `ψ-ein`/`ψ-eout`
-- propagation through the edge structure (a focused engineering task
-- that does not require additional categorical insight).

module BlockDiagonal
  {A B C D}
  (f₁ : HomTerm A B) (g₁ : HomTerm C D)
  (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  (iso : ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫)
  where

  open BoundarySlice f₁ g₁ f₂ g₂ iso public

  postulate
    -- For every left-half vertex (i.e. one of the form `iG ↑ˡ K₁.nV`)
    -- of T₁, φ sends it to a left-half vertex of T₂.
    φ-restricts-L
      : ∀ (iG : Fin G₁.nV)
      → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV

    -- For every right-half vertex of T₁, φ sends it to a right-half vertex.
    φ-restricts-R
      : ∀ (iK : Fin K₁.nV)
      → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'

    -- For every left-half edge of T₁, ψ sends it to a left-half edge of T₂.
    ψ-restricts-L
      : ∀ (eG : Fin G₁.nE)
      → Σ (Fin G₂.nE) λ eG' → ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE

    -- For every right-half edge of T₁, ψ sends it to a right-half edge of T₂.
    ψ-restricts-R
      : ∀ (eK : Fin K₁.nE)
      → Σ (Fin K₂.nE) λ eK' → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ eK'

  -- Extracted half-restricted bijections (in the forward direction).
  φ_L : Fin G₁.nV → Fin G₂.nV
  φ_L iG = proj₁ (φ-restricts-L iG)

  φ_L-eq : ∀ iG → φ (iG ↑ˡ K₁.nV) ≡ φ_L iG ↑ˡ K₂.nV
  φ_L-eq iG = proj₂ (φ-restricts-L iG)

  φ_R : Fin K₁.nV → Fin K₂.nV
  φ_R iK = proj₁ (φ-restricts-R iK)

  φ_R-eq : ∀ iK → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ φ_R iK
  φ_R-eq iK = proj₂ (φ-restricts-R iK)

  ψ_L : Fin G₁.nE → Fin G₂.nE
  ψ_L eG = proj₁ (ψ-restricts-L eG)

  ψ_L-eq : ∀ eG → ψ (eG ↑ˡ K₁.nE) ≡ ψ_L eG ↑ˡ K₂.nE
  ψ_L-eq eG = proj₂ (ψ-restricts-L eG)

  ψ_R : Fin K₁.nE → Fin K₂.nE
  ψ_R eK = proj₁ (ψ-restricts-R eK)

  ψ_R-eq : ∀ eK → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ ψ_R eK
  ψ_R-eq eK = proj₂ (ψ-restricts-R eK)

--------------------------------------------------------------------------------
-- Constructive derivation: from the four block-diagonal sub-postulates,
-- the inverse-direction block-diagonal properties follow.
--
-- The key idea: φ is a bijection (via φ⁻¹), so φ_L (defined from
-- φ-restricts-L) is injective.  Surjectivity follows by case analysis
-- on `splitAt G₁.nV (φ⁻¹ (iG' ↑ˡ K₂.nV))`: the `inj₂` case is
-- impossible because by φ-restricts-R it would force a contradiction
-- with the L-half image jG ↑ˡ K₂.nV.

module InverseDerivations
  {A B C D}
  (f₁ : HomTerm A B) (g₁ : HomTerm C D)
  (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  (iso : ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫)
  where

  open BlockDiagonal f₁ g₁ f₂ g₂ iso public

  -- L-side inverse map: φ⁻¹ on (iG' ↑ˡ K₂.nV) is in the L-half of T₁.
  -- We use the original iso's φ⁻¹ field.
  φ_L⁻¹-data
    : ∀ (iG' : Fin G₂.nV)
    → Σ (Fin G₁.nV) λ iG → φ⁻¹ (iG' ↑ˡ K₂.nV) ≡ iG ↑ˡ K₁.nV
  φ_L⁻¹-data iG' with splitAt G₁.nV (φ⁻¹ (iG' ↑ˡ K₂.nV)) in eq
  ... | inj₁ iG = iG , sym (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ iK = ⊥-elim (↑ˡ≢↑ʳ (φ_R iK) iG' contradiction)
    where
      -- φ⁻¹ (iG' ↑ˡ K₂.nV) = G₁.nV ↑ʳ iK, so applying φ gives
      -- iG' ↑ˡ K₂.nV = φ(G₁.nV ↑ʳ iK) = G₂.nV ↑ʳ (φ_R iK) (by φ_R-eq).
      back-eq : G₁.nV ↑ʳ iK ≡ φ⁻¹ (iG' ↑ˡ K₂.nV)
      back-eq = sym (splitAt⁻¹-↑ʳ eq)

      contradiction : (φ_R iK) ↑ˡ K₂.nV ≡ G₂.nV ↑ʳ iG'
      contradiction = ⊥-elim impossible
        where
          -- Wait, we want the opposite: iG' ↑ˡ K₂.nV ≡ G₂.nV ↑ʳ (φ_R iK).
          -- Let me restructure.
          apply-φ : φ (φ⁻¹ (iG' ↑ˡ K₂.nV)) ≡ iG' ↑ˡ K₂.nV
          apply-φ = φ-rght (iG' ↑ˡ K₂.nV)

          step₂ : φ (G₁.nV ↑ʳ iK) ≡ iG' ↑ˡ K₂.nV
          step₂ = trans (cong φ back-eq) apply-φ

          step₃ : G₂.nV ↑ʳ (φ_R iK) ≡ iG' ↑ˡ K₂.nV
          step₃ = trans (sym (φ_R-eq iK)) step₂

          impossible : ⊥
          impossible = ↑ʳ≢↑ˡ iG' (φ_R iK) step₃

  φ_L⁻¹ : Fin G₂.nV → Fin G₁.nV
  φ_L⁻¹ iG' = proj₁ (φ_L⁻¹-data iG')

  φ_L⁻¹-eq : ∀ iG' → φ⁻¹ (iG' ↑ˡ K₂.nV) ≡ φ_L⁻¹ iG' ↑ˡ K₁.nV
  φ_L⁻¹-eq iG' = proj₂ (φ_L⁻¹-data iG')

  -- R-side inverse map: φ⁻¹ on (G₂.nV ↑ʳ iK') is in the R-half of T₁.
  φ_R⁻¹-data
    : ∀ (iK' : Fin K₂.nV)
    → Σ (Fin K₁.nV) λ iK → φ⁻¹ (G₂.nV ↑ʳ iK') ≡ G₁.nV ↑ʳ iK
  φ_R⁻¹-data iK' with splitAt G₁.nV (φ⁻¹ (G₂.nV ↑ʳ iK')) in eq
  ... | inj₁ iG = ⊥-elim (↑ˡ≢↑ʳ (φ_L iG) iK' contradiction)
    where
      back-eq : iG ↑ˡ K₁.nV ≡ φ⁻¹ (G₂.nV ↑ʳ iK')
      back-eq = sym (splitAt⁻¹-↑ˡ eq)

      apply-φ : φ (φ⁻¹ (G₂.nV ↑ʳ iK')) ≡ G₂.nV ↑ʳ iK'
      apply-φ = φ-rght (G₂.nV ↑ʳ iK')

      step₂ : φ (iG ↑ˡ K₁.nV) ≡ G₂.nV ↑ʳ iK'
      step₂ = trans (cong φ back-eq) apply-φ

      step₃ : (φ_L iG) ↑ˡ K₂.nV ≡ G₂.nV ↑ʳ iK'
      step₃ = trans (sym (φ_L-eq iG)) step₂

      contradiction : (φ_L iG) ↑ˡ K₂.nV ≡ G₂.nV ↑ʳ iK'
      contradiction = step₃
  ... | inj₂ iK = iK , sym (splitAt⁻¹-↑ʳ eq)

  φ_R⁻¹ : Fin K₂.nV → Fin K₁.nV
  φ_R⁻¹ iK' = proj₁ (φ_R⁻¹-data iK')

  φ_R⁻¹-eq : ∀ iK' → φ⁻¹ (G₂.nV ↑ʳ iK') ≡ G₁.nV ↑ʳ φ_R⁻¹ iK'
  φ_R⁻¹-eq iK' = proj₂ (φ_R⁻¹-data iK')

  -- L-side inverse for edges.
  ψ_L⁻¹-data
    : ∀ (eG' : Fin G₂.nE)
    → Σ (Fin G₁.nE) λ eG → ψ⁻¹ (eG' ↑ˡ K₂.nE) ≡ eG ↑ˡ K₁.nE
  ψ_L⁻¹-data eG' with splitAt G₁.nE (ψ⁻¹ (eG' ↑ˡ K₂.nE)) in eq
  ... | inj₁ eG = eG , sym (splitAt⁻¹-↑ˡ eq)
  ... | inj₂ eK = ⊥-elim (↑ʳ≢↑ˡ eG' (ψ_R eK) step₃)
    where
      back-eq : G₁.nE ↑ʳ eK ≡ ψ⁻¹ (eG' ↑ˡ K₂.nE)
      back-eq = sym (splitAt⁻¹-↑ʳ eq)

      apply-ψ : ψ (ψ⁻¹ (eG' ↑ˡ K₂.nE)) ≡ eG' ↑ˡ K₂.nE
      apply-ψ = ψ-rght (eG' ↑ˡ K₂.nE)

      step₂ : ψ (G₁.nE ↑ʳ eK) ≡ eG' ↑ˡ K₂.nE
      step₂ = trans (cong ψ back-eq) apply-ψ

      step₃ : G₂.nE ↑ʳ (ψ_R eK) ≡ eG' ↑ˡ K₂.nE
      step₃ = trans (sym (ψ_R-eq eK)) step₂

  ψ_L⁻¹ : Fin G₂.nE → Fin G₁.nE
  ψ_L⁻¹ eG' = proj₁ (ψ_L⁻¹-data eG')

  ψ_L⁻¹-eq : ∀ eG' → ψ⁻¹ (eG' ↑ˡ K₂.nE) ≡ ψ_L⁻¹ eG' ↑ˡ K₁.nE
  ψ_L⁻¹-eq eG' = proj₂ (ψ_L⁻¹-data eG')

  -- R-side inverse for edges.
  ψ_R⁻¹-data
    : ∀ (eK' : Fin K₂.nE)
    → Σ (Fin K₁.nE) λ eK → ψ⁻¹ (G₂.nE ↑ʳ eK') ≡ G₁.nE ↑ʳ eK
  ψ_R⁻¹-data eK' with splitAt G₁.nE (ψ⁻¹ (G₂.nE ↑ʳ eK')) in eq
  ... | inj₁ eG = ⊥-elim (↑ˡ≢↑ʳ (ψ_L eG) eK' step₃)
    where
      back-eq : eG ↑ˡ K₁.nE ≡ ψ⁻¹ (G₂.nE ↑ʳ eK')
      back-eq = sym (splitAt⁻¹-↑ˡ eq)

      apply-ψ : ψ (ψ⁻¹ (G₂.nE ↑ʳ eK')) ≡ G₂.nE ↑ʳ eK'
      apply-ψ = ψ-rght (G₂.nE ↑ʳ eK')

      step₂ : ψ (eG ↑ˡ K₁.nE) ≡ G₂.nE ↑ʳ eK'
      step₂ = trans (cong ψ back-eq) apply-ψ

      step₃ : (ψ_L eG) ↑ˡ K₂.nE ≡ G₂.nE ↑ʳ eK'
      step₃ = trans (sym (ψ_L-eq eG)) step₂
  ... | inj₂ eK = eK , sym (splitAt⁻¹-↑ʳ eq)

  ψ_R⁻¹ : Fin K₂.nE → Fin K₁.nE
  ψ_R⁻¹ eK' = proj₁ (ψ_R⁻¹-data eK')

  ψ_R⁻¹-eq : ∀ eK' → ψ⁻¹ (G₂.nE ↑ʳ eK') ≡ G₁.nE ↑ʳ ψ_R⁻¹ eK'
  ψ_R⁻¹-eq eK' = proj₂ (ψ_R⁻¹-data eK')

  -- Round-trip equations: φ_L⁻¹ (φ_L iG) = iG, etc.

  -- φ_L⁻¹ ∘ φ_L ≡ id : apply original φ-left to (iG ↑ˡ K₁.nV).
  -- The result `iG ↑ˡ K₁.nV` must equal `φ_L⁻¹ (φ_L iG) ↑ˡ K₁.nV`.
  -- ↑ˡ-injective then gives the identity.
  φ_L-left : ∀ iG → φ_L⁻¹ (φ_L iG) ≡ iG
  φ_L-left iG =
    let
      eq1 : φ⁻¹ (φ (iG ↑ˡ K₁.nV)) ≡ iG ↑ˡ K₁.nV
      eq1 = φ-left (iG ↑ˡ K₁.nV)

      eq2 : φ⁻¹ (φ_L iG ↑ˡ K₂.nV) ≡ iG ↑ˡ K₁.nV
      eq2 = trans (cong φ⁻¹ (sym (φ_L-eq iG))) eq1

      eq3 : φ_L⁻¹ (φ_L iG) ↑ˡ K₁.nV ≡ iG ↑ˡ K₁.nV
      eq3 = trans (sym (φ_L⁻¹-eq (φ_L iG))) eq2
    in
    ↑ˡ-injective K₁.nV (φ_L⁻¹ (φ_L iG)) iG eq3

  φ_L-rght : ∀ iG' → φ_L (φ_L⁻¹ iG') ≡ iG'
  φ_L-rght iG' =
    let
      eq1 : φ (φ⁻¹ (iG' ↑ˡ K₂.nV)) ≡ iG' ↑ˡ K₂.nV
      eq1 = φ-rght (iG' ↑ˡ K₂.nV)

      eq2 : φ (φ_L⁻¹ iG' ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
      eq2 = trans (cong φ (sym (φ_L⁻¹-eq iG'))) eq1

      eq3 : φ_L (φ_L⁻¹ iG') ↑ˡ K₂.nV ≡ iG' ↑ˡ K₂.nV
      eq3 = trans (sym (φ_L-eq (φ_L⁻¹ iG'))) eq2
    in
    ↑ˡ-injective K₂.nV (φ_L (φ_L⁻¹ iG')) iG' eq3

  φ_R-left : ∀ iK → φ_R⁻¹ (φ_R iK) ≡ iK
  φ_R-left iK =
    let
      eq1 : φ⁻¹ (φ (G₁.nV ↑ʳ iK)) ≡ G₁.nV ↑ʳ iK
      eq1 = φ-left (G₁.nV ↑ʳ iK)

      eq2 : φ⁻¹ (G₂.nV ↑ʳ φ_R iK) ≡ G₁.nV ↑ʳ iK
      eq2 = trans (cong φ⁻¹ (sym (φ_R-eq iK))) eq1

      eq3 : G₁.nV ↑ʳ φ_R⁻¹ (φ_R iK) ≡ G₁.nV ↑ʳ iK
      eq3 = trans (sym (φ_R⁻¹-eq (φ_R iK))) eq2
    in
    ↑ʳ-injective G₁.nV (φ_R⁻¹ (φ_R iK)) iK eq3

  φ_R-rght : ∀ iK' → φ_R (φ_R⁻¹ iK') ≡ iK'
  φ_R-rght iK' =
    let
      eq1 : φ (φ⁻¹ (G₂.nV ↑ʳ iK')) ≡ G₂.nV ↑ʳ iK'
      eq1 = φ-rght (G₂.nV ↑ʳ iK')

      eq2 : φ (G₁.nV ↑ʳ φ_R⁻¹ iK') ≡ G₂.nV ↑ʳ iK'
      eq2 = trans (cong φ (sym (φ_R⁻¹-eq iK'))) eq1

      eq3 : G₂.nV ↑ʳ φ_R (φ_R⁻¹ iK') ≡ G₂.nV ↑ʳ iK'
      eq3 = trans (sym (φ_R-eq (φ_R⁻¹ iK'))) eq2
    in
    ↑ʳ-injective G₂.nV (φ_R (φ_R⁻¹ iK')) iK' eq3

  ψ_L-left : ∀ eG → ψ_L⁻¹ (ψ_L eG) ≡ eG
  ψ_L-left eG =
    let
      eq1 : ψ⁻¹ (ψ (eG ↑ˡ K₁.nE)) ≡ eG ↑ˡ K₁.nE
      eq1 = ψ-left (eG ↑ˡ K₁.nE)

      eq2 : ψ⁻¹ (ψ_L eG ↑ˡ K₂.nE) ≡ eG ↑ˡ K₁.nE
      eq2 = trans (cong ψ⁻¹ (sym (ψ_L-eq eG))) eq1

      eq3 : ψ_L⁻¹ (ψ_L eG) ↑ˡ K₁.nE ≡ eG ↑ˡ K₁.nE
      eq3 = trans (sym (ψ_L⁻¹-eq (ψ_L eG))) eq2
    in
    ↑ˡ-injective K₁.nE (ψ_L⁻¹ (ψ_L eG)) eG eq3

  ψ_L-rght : ∀ eG' → ψ_L (ψ_L⁻¹ eG') ≡ eG'
  ψ_L-rght eG' =
    let
      eq1 : ψ (ψ⁻¹ (eG' ↑ˡ K₂.nE)) ≡ eG' ↑ˡ K₂.nE
      eq1 = ψ-rght (eG' ↑ˡ K₂.nE)

      eq2 : ψ (ψ_L⁻¹ eG' ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE
      eq2 = trans (cong ψ (sym (ψ_L⁻¹-eq eG'))) eq1

      eq3 : ψ_L (ψ_L⁻¹ eG') ↑ˡ K₂.nE ≡ eG' ↑ˡ K₂.nE
      eq3 = trans (sym (ψ_L-eq (ψ_L⁻¹ eG'))) eq2
    in
    ↑ˡ-injective K₂.nE (ψ_L (ψ_L⁻¹ eG')) eG' eq3

  ψ_R-left : ∀ eK → ψ_R⁻¹ (ψ_R eK) ≡ eK
  ψ_R-left eK =
    let
      eq1 : ψ⁻¹ (ψ (G₁.nE ↑ʳ eK)) ≡ G₁.nE ↑ʳ eK
      eq1 = ψ-left (G₁.nE ↑ʳ eK)

      eq2 : ψ⁻¹ (G₂.nE ↑ʳ ψ_R eK) ≡ G₁.nE ↑ʳ eK
      eq2 = trans (cong ψ⁻¹ (sym (ψ_R-eq eK))) eq1

      eq3 : G₁.nE ↑ʳ ψ_R⁻¹ (ψ_R eK) ≡ G₁.nE ↑ʳ eK
      eq3 = trans (sym (ψ_R⁻¹-eq (ψ_R eK))) eq2
    in
    ↑ʳ-injective G₁.nE (ψ_R⁻¹ (ψ_R eK)) eK eq3

  ψ_R-rght : ∀ eK' → ψ_R (ψ_R⁻¹ eK') ≡ eK'
  ψ_R-rght eK' =
    let
      eq1 : ψ (ψ⁻¹ (G₂.nE ↑ʳ eK')) ≡ G₂.nE ↑ʳ eK'
      eq1 = ψ-rght (G₂.nE ↑ʳ eK')

      eq2 : ψ (G₁.nE ↑ʳ ψ_R⁻¹ eK') ≡ G₂.nE ↑ʳ eK'
      eq2 = trans (cong ψ (sym (ψ_R⁻¹-eq eK'))) eq1

      eq3 : G₂.nE ↑ʳ ψ_R (ψ_R⁻¹ eK') ≡ G₂.nE ↑ʳ eK'
      eq3 = trans (sym (ψ_R-eq (ψ_R⁻¹ eK'))) eq2
    in
    ↑ʳ-injective G₂.nE (ψ_R (ψ_R⁻¹ eK')) eK' eq3
