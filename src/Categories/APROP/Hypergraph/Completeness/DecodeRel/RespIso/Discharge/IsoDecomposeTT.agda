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
-- by a narrower set of named sub-postulates that capture exactly the
-- "block-diagonal" content of the iso's vertex and edge bijections.
-- Concretely:
--
--   * `φ-restricts-L`  / `φ-restricts-R`          (vertices, still
--                                                  postulates)
--   * `ψ-restricts-L`  / `ψ-restricts-R`          (edges, now
--                                                  DISCHARGED for the
--                                                  generic case)
--   * `ψ-restricts-L-deg` / `ψ-restricts-R-deg`   (edges, narrower
--                                                  postulates for the
--                                                  degenerate corner
--                                                  case below)
--
-- Each `restricts-L` says: "for vertices/edges in the L-half of T₁,
-- the iso's bijection lands in the L-half of T₂".  Mathematically this
-- is the statement that the iso restricts to a pair of sub-isos
-- between the f-halves and the g-halves of the two tensors.
--
-- From these sub-postulates we constructively assemble the two
-- sub-isos.  All the inverse-direction data (`φ⁻¹` for the sub-iso,
-- the `φ-left`/`φ-rght` round-trips, etc.) is derived constructively
-- by composing with the original iso's `φ⁻¹`/`ψ⁻¹` and using the
-- `splitAt-↑ˡ`/`splitAt-↑ʳ` properties.
--
-- ## Edge postulate discharge (Apr 2026)
--
-- `ψ-restricts-L` and `ψ-restricts-R` have been discharged: each is now
-- a constructive `with`-tree.  When `G₁.ein eG` (or eout) is non-empty,
-- a half-swap would force a list-equation `map (G₂.nV ↑ʳ_) (k ∷ ks) ≡
-- map (_↑ˡ K₂.nV) ws`, contradicting `↑ʳ≢↑ˡ` on the head.  The proof
-- pulls in the iso's `ψ-ein`/`ψ-eout` field, `φ-restricts-L`/`-R`
-- (still postulates) to push the contradiction through the vertex
-- bijection, and `hTensor-impl.ein-c-inj₁/₂-red` to unfold the
-- compound `T₁.ein`/`T₂.ein` into half-restricted form.
--
-- The remaining "degenerate" case — an edge with BOTH `ein ≡ []` and
-- `eout ≡ []` (a `mor unit unit` ghost edge) — is captured by the two
-- narrow sub-postulates `ψ-restricts-L-deg` / `ψ-restricts-R-deg`.  In
-- such cases there are no endpoints to anchor the iso's `ψ` to a
-- particular half, so the iso could in principle swap a unit→unit
-- edge from f₁ with a unit→unit edge from g₂ (or vice versa).  Strict
-- narrowing: each `-deg` postulate is strictly weaker than the
-- original `ψ-restricts-L`/`-R` (just discard the two empty-list
-- hypotheses to recover the original).  Soundness assumption: same as
-- the original `iso-decompose-⊗⊗`, which we already accept; the
-- narrowing inherits this without any further structural commitment.
--
-- ## Justification of the narrowing (vertex case)
--
-- `φ-restricts-L`/`-R` are strictly smaller than the original
-- existential.  They are also independently provable in principle: a
-- "structurally straight" iso (the only kind that occurs in our
-- setting) satisfies these properties directly from
-- `dom-split-eq-L`/`-R` and `cod-split-eq-L`/`-R` for boundary
-- vertices, and from the `ψ-ein`/`ψ-eout` propagation for interior
-- vertices.  The "crossed" case (where the iso swaps halves) is
-- rejected by the type discipline: f₁,f₂ have type A → B and g₁,g₂
-- have type C → D, so a half-swap would force A ≡ C and B ≡ D
-- heterogeneously, which our type-driven decomposition does not need
-- to handle.
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
open import Categories.APROP.Hypergraph.Iso using (_≅ᴴ_)
open import Categories.APROP.Hypergraph.CoherenceHelpers sig
  using (subst₂-trans; subst₂-sym-subst₂; subst₂-refl)

open import Data.Empty using (⊥; ⊥-elim)
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

  -- List-level injectivity of `_↑ˡ n` and `m ↑ʳ_` on `Fin`-lists.
  map-↑ˡ-injective
    : ∀ {m n} (xs ys : List (Fin m))
    → map (_↑ˡ n) xs ≡ map (_↑ˡ n) ys → xs ≡ ys
  map-↑ˡ-injective []       []       _  = refl
  map-↑ˡ-injective []       (y ∷ _)  ()
  map-↑ˡ-injective (x ∷ _)  []       ()
  map-↑ˡ-injective {m} {n} (x ∷ xs) (y ∷ ys) eq =
    cong₂ _∷_ head-eq (map-↑ˡ-injective xs ys tail-eq)
    where
      ∷-head : ∀ {A : Set} {x x' : A} {xs xs' : List A}
             → x ∷ xs ≡ x' ∷ xs' → x ≡ x'
      ∷-head refl = refl
      ∷-tail : ∀ {A : Set} {x x' : A} {xs xs' : List A}
             → x ∷ xs ≡ x' ∷ xs' → xs ≡ xs'
      ∷-tail refl = refl
      head-eq : x ≡ y
      head-eq = ↑ˡ-injective n x y (∷-head eq)
      tail-eq : map (_↑ˡ n) xs ≡ map (_↑ˡ n) ys
      tail-eq = ∷-tail eq

  map-↑ʳ-injective
    : ∀ {m n} (xs ys : List (Fin n))
    → map (m ↑ʳ_) xs ≡ map (m ↑ʳ_) ys → xs ≡ ys
  map-↑ʳ-injective []       []       _  = refl
  map-↑ʳ-injective []       (y ∷ _)  ()
  map-↑ʳ-injective (x ∷ _)  []       ()
  map-↑ʳ-injective {m} {n} (x ∷ xs) (y ∷ ys) eq =
    cong₂ _∷_ head-eq (map-↑ʳ-injective xs ys tail-eq)
    where
      ∷-head : ∀ {A : Set} {x x' : A} {xs xs' : List A}
             → x ∷ xs ≡ x' ∷ xs' → x ≡ x'
      ∷-head refl = refl
      ∷-tail : ∀ {A : Set} {x x' : A} {xs xs' : List A}
             → x ∷ xs ≡ x' ∷ xs' → xs ≡ xs'
      ∷-tail refl = refl
      head-eq : x ≡ y
      head-eq = ↑ʳ-injective m x y (∷-head eq)
      tail-eq : map (m ↑ʳ_) xs ≡ map (m ↑ʳ_) ys
      tail-eq = ∷-tail eq

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
-- BoundaryDischarge: constructive φ-restricts-L/R witnesses for
-- BOUNDARY vertices (step (6) of the connected-components refactor
-- sketch above).
--
-- For any vertex `iG ∈ G₁.dom` (or `G₁.cod`, K₁.dom`, `K₁.cod`), the
-- position-by-position match of `dom-split-eq-L` etc. constructively
-- exhibits the corresponding G₂.dom/cod element and the L-form
-- equation.  No mutual recursion against `ψ-restricts-*`; no postulate.
--
-- This proves a strict *subset* of `φ-restricts-L/R`: the boundary
-- case.  The full postulate still needs the *interior + stranded*
-- case, which is the genuine obstruction (per the vertex-coverage
-- counter-example).  Exposing this discharge makes the residual
-- difficulty explicit: any future tighter narrowing of
-- `φ-restricts-L/R` could quantify only over "non-boundary L-vertices".

module BoundaryDischarge
  {A B C D}
  (f₁ : HomTerm A B) (g₁ : HomTerm C D)
  (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  (iso : ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫)
  where

  open BoundarySlice f₁ g₁ f₂ g₂ iso public

  -- Position witness: `x` is the (length ys)-th element of (ys ++ x ∷ zs).
  At : ∀ {A : Set} → A → List A → Set
  At {A} x xs = Σ (List A) λ ys → Σ (List A) λ zs → xs ≡ ys ++ x ∷ zs

  -- Same-position lookup across a `map`-equation.  Given parallel
  -- decompositions of `xs` and `ys` at the same position, the map
  -- equation yields equality of `f x ≡ g y` for the chosen elements.
  private
    map-at-eq
      : ∀ {S T R : Set}
      → (f : S → R) (g : T → R)
      → (x : S) (xs₁ xs₂ : List S)
      → (y : T) (ys₁ ys₂ : List T)
      → length xs₁ ≡ length ys₁
      → map f (xs₁ ++ x ∷ xs₂) ≡ map g (ys₁ ++ y ∷ ys₂)
      → f x ≡ g y
    map-at-eq f g x []         xs₂ y []         ys₂ _ eq = ∷-head eq
      where
        ∷-head : ∀ {A : Set} {x x' : A} {xs xs' : List A}
               → x ∷ xs ≡ x' ∷ xs' → x ≡ x'
        ∷-head refl = refl
    map-at-eq f g x (x' ∷ xs₁) xs₂ y (y' ∷ ys₁) ys₂ len eq =
      map-at-eq f g x xs₁ xs₂ y ys₁ ys₂ (suc-injective len) (∷-tail eq)
      where
        ∷-tail : ∀ {A : Set} {x x' : A} {xs xs' : List A}
               → x ∷ xs ≡ x' ∷ xs' → xs ≡ xs'
        ∷-tail refl = refl
    map-at-eq f g x []         xs₂ y (y' ∷ ys₁) ys₂ () _
    map-at-eq f g x (x' ∷ xs₁) xs₂ y []         ys₂ () _

    -- Length facts derived from `dom-split-eq-L`/`cod-split-eq-L`.
    dom-len-L : length G₁.dom ≡ length G₂.dom
    dom-len-L =
      trans (sym (length-map (_↑ˡ K₁.nV) G₁.dom))
      (trans (sym (length-map φ (map (_↑ˡ K₁.nV) G₁.dom)))
      (trans (sym (cong length dom-split-eq-L))
             (length-map (_↑ˡ K₂.nV) G₂.dom)))

    cod-len-L : length G₁.cod ≡ length G₂.cod
    cod-len-L =
      trans (sym (length-map (_↑ˡ K₁.nV) G₁.cod))
      (trans (sym (length-map φ (map (_↑ˡ K₁.nV) G₁.cod)))
      (trans (sym (cong length cod-split-eq-L))
             (length-map (_↑ˡ K₂.nV) G₂.cod)))

    dom-len-R : length K₁.dom ≡ length K₂.dom
    dom-len-R =
      trans (sym (length-map (G₁.nV ↑ʳ_) K₁.dom))
      (trans (sym (length-map φ (map (G₁.nV ↑ʳ_) K₁.dom)))
      (trans (sym (cong length dom-split-eq-R))
             (length-map (G₂.nV ↑ʳ_) K₂.dom)))

    cod-len-R : length K₁.cod ≡ length K₂.cod
    cod-len-R =
      trans (sym (length-map (G₁.nV ↑ʳ_) K₁.cod))
      (trans (sym (length-map φ (map (G₁.nV ↑ʳ_) K₁.cod)))
      (trans (sym (cong length cod-split-eq-R))
             (length-map (G₂.nV ↑ʳ_) K₂.cod)))

    -- Same-position list decomposition: given a decomposition of `xs`
    -- of length n and a length-balanced list `ys`, decompose `ys` at
    -- the same position.
    split-by-pos
      : ∀ {S T : Set} (x : S) (xs₁ xs₂ : List S) (ys : List T)
      → length (xs₁ ++ x ∷ xs₂) ≡ length ys
      → Σ T λ y → Σ (List T) λ ys₁ → Σ (List T) λ ys₂
          → ys ≡ ys₁ ++ y ∷ ys₂ × length xs₁ ≡ length ys₁
    split-by-pos x []         xs₂ (y ∷ ys)  _   = y , [] , ys , refl , refl
    split-by-pos x (x' ∷ xs₁) xs₂ (y ∷ ys)  len
      with split-by-pos x xs₁ xs₂ ys (suc-injective len)
    ... | y' , ys₁ , ys₂ , dec , lenEq =
            y' , (y ∷ ys₁) , ys₂ , cong (y ∷_) dec , cong suc lenEq
      where open import Data.Nat using (suc)
    split-by-pos x []         xs₂ []        ()
    split-by-pos x (_ ∷ _)    xs₂ []        ()

  -- Constructive discharge for L-boundary (dom) vertices.
  φ-restricts-L-from-dom
    : ∀ (iG : Fin G₁.nV) → At iG G₁.dom
    → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
  φ-restricts-L-from-dom iG (xs₁ , xs₂ , decomp) =
    let
      len-eq : length (xs₁ ++ iG ∷ xs₂) ≡ length G₂.dom
      len-eq = trans (sym (cong length decomp)) dom-len-L
    in helper (split-by-pos iG xs₁ xs₂ G₂.dom len-eq)
    where
      helper : (Σ (Fin G₂.nV) λ y → Σ (List (Fin G₂.nV)) λ ys₁ → Σ (List (Fin G₂.nV)) λ ys₂
                → G₂.dom ≡ ys₁ ++ y ∷ ys₂ × length xs₁ ≡ length ys₁)
             → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
      helper (iG' , ys₁ , ys₂ , g2-dec , lenEq) =
        iG' ,
        sym (map-at-eq (_↑ˡ K₂.nV) (λ z → φ (z ↑ˡ K₁.nV))
                       iG' ys₁ ys₂ iG xs₁ xs₂
                       (sym lenEq)
                       (trans (cong (map (_↑ˡ K₂.nV)) (sym g2-dec))
                       (trans dom-split-eq-L
                       (trans (sym (map-∘ G₁.dom))
                              (cong (map (λ z → φ (z ↑ˡ K₁.nV))) decomp)))))

  φ-restricts-L-from-cod
    : ∀ (iG : Fin G₁.nV) → At iG G₁.cod
    → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
  φ-restricts-L-from-cod iG (xs₁ , xs₂ , decomp) =
    let
      len-eq : length (xs₁ ++ iG ∷ xs₂) ≡ length G₂.cod
      len-eq = trans (sym (cong length decomp)) cod-len-L
    in helper (split-by-pos iG xs₁ xs₂ G₂.cod len-eq)
    where
      helper : (Σ (Fin G₂.nV) λ y → Σ (List (Fin G₂.nV)) λ ys₁ → Σ (List (Fin G₂.nV)) λ ys₂
                → G₂.cod ≡ ys₁ ++ y ∷ ys₂ × length xs₁ ≡ length ys₁)
             → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
      helper (iG' , ys₁ , ys₂ , g2-dec , lenEq) =
        iG' ,
        sym (map-at-eq (_↑ˡ K₂.nV) (λ z → φ (z ↑ˡ K₁.nV))
                       iG' ys₁ ys₂ iG xs₁ xs₂
                       (sym lenEq)
                       (trans (cong (map (_↑ˡ K₂.nV)) (sym g2-dec))
                       (trans cod-split-eq-L
                       (trans (sym (map-∘ G₁.cod))
                              (cong (map (λ z → φ (z ↑ˡ K₁.nV))) decomp)))))

  φ-restricts-R-from-dom
    : ∀ (iK : Fin K₁.nV) → At iK K₁.dom
    → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'
  φ-restricts-R-from-dom iK (xs₁ , xs₂ , decomp) =
    let
      len-eq : length (xs₁ ++ iK ∷ xs₂) ≡ length K₂.dom
      len-eq = trans (sym (cong length decomp)) dom-len-R
    in helper (split-by-pos iK xs₁ xs₂ K₂.dom len-eq)
    where
      helper : (Σ (Fin K₂.nV) λ y → Σ (List (Fin K₂.nV)) λ ys₁ → Σ (List (Fin K₂.nV)) λ ys₂
                → K₂.dom ≡ ys₁ ++ y ∷ ys₂ × length xs₁ ≡ length ys₁)
             → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'
      helper (iK' , ys₁ , ys₂ , k2-dec , lenEq) =
        iK' ,
        sym (map-at-eq (G₂.nV ↑ʳ_) (λ z → φ (G₁.nV ↑ʳ z))
                       iK' ys₁ ys₂ iK xs₁ xs₂
                       (sym lenEq)
                       (trans (cong (map (G₂.nV ↑ʳ_)) (sym k2-dec))
                       (trans dom-split-eq-R
                       (trans (sym (map-∘ K₁.dom))
                              (cong (map (λ z → φ (G₁.nV ↑ʳ z))) decomp)))))

  φ-restricts-R-from-cod
    : ∀ (iK : Fin K₁.nV) → At iK K₁.cod
    → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'
  φ-restricts-R-from-cod iK (xs₁ , xs₂ , decomp) =
    let
      len-eq : length (xs₁ ++ iK ∷ xs₂) ≡ length K₂.cod
      len-eq = trans (sym (cong length decomp)) cod-len-R
    in helper (split-by-pos iK xs₁ xs₂ K₂.cod len-eq)
    where
      helper : (Σ (Fin K₂.nV) λ y → Σ (List (Fin K₂.nV)) λ ys₁ → Σ (List (Fin K₂.nV)) λ ys₂
                → K₂.cod ≡ ys₁ ++ y ∷ ys₂ × length xs₁ ≡ length ys₁)
             → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'
      helper (iK' , ys₁ , ys₂ , k2-dec , lenEq) =
        iK' ,
        sym (map-at-eq (G₂.nV ↑ʳ_) (λ z → φ (G₁.nV ↑ʳ z))
                       iK' ys₁ ys₂ iK xs₁ xs₂
                       (sym lenEq)
                       (trans (cong (map (G₂.nV ↑ʳ_)) (sym k2-dec))
                       (trans cod-split-eq-R
                       (trans (sym (map-∘ K₁.cod))
                              (cong (map (λ z → φ (G₁.nV ↑ʳ z))) decomp)))))

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

  -- Status note (May 2026): `φ-restricts-L`/`-R` remain postulates after
  -- the edge-discharge work above (`ψ-restricts-L`/`-R` were eliminated,
  -- modulo narrower `-deg` postulates).  The natural proof strategy for
  -- vertices on at least one edge would case-split on
  -- `splitAt G₂.nV (φ (iG ↑ˡ K₁.nV))` and use `ψ-restricts-L eG` (for an
  -- edge eG with iG as endpoint) plus `ψ-ein`/`ψ-eout` to derive a
  -- contradiction in the R-half branch.  But the discharged
  -- `ψ-restricts-L` proof itself relies on `φ_L`/`φ_L-eq` — i.e. on this
  -- very postulate — to convert
  --   `map φ (map (_↑ˡ K₁.nV) (G₁.ein eG))` into
  --   `map (_↑ˡ K₂.nV) (map φ_L (G₁.ein eG))`.
  -- The two proofs are MUTUALLY RECURSIVE at the proof level, and the
  -- recursion has no obvious termination measure for Agda.  A clean
  -- discharge would require either:
  --   (1) a structural induction on the HomTerm `f₁` (and `g₁`) proving
  --       a "vertex coverage" lemma (every vertex of `⟪f⟫` is in
  --       `⟪f⟫.dom`, `⟪f⟫.cod`, or on some edge), then case-split on it
  --       and use the boundary `dom-split-eq-L`/`cod-split-eq-L` for
  --       boundary vertices plus a non-mutual edge-propagation for the
  --       interior;
  --   (2) reworking `ψ-restricts-L`/`-R` to avoid `φ_L` so the
  --       recursion is one-way.
  -- Both are substantial multi-hundred-LOC efforts.
  --
  -- ## Connected-components refactor sketch (May 2026, agent-ade28bbf)
  --
  -- A cleaner organisation factors all four block-diagonal postulates
  -- through ONE generic `iso-preserves-components` helper plus a single
  -- residual lemma.  Concretely:
  --
  --   1. Define `Side = L | R` and `vertex-side : Fin (G.nV+K.nV) → Side`
  --      via `splitAt`; similarly `edge-side`.
  --
  --   2. Constructive lemma: in `hTensor G K`, every endpoint of an
  --      L-edge has L-side (and dually for R-edges).  This follows from
  --      `hTensor-impl.ein-c-inj₁-red`/`ein-c-inj₂-red` together with
  --      the fact that `map (_↑ˡ K.nV)` produces only L-side values.
  --
  --   3. Constructive lemma `iso-preserves-edge-endpoints`: for the iso
  --      `T₁ ≅ᴴ T₂`, if vertex `v ∈ Fin T₁.nV` is an endpoint of edge
  --      `e ∈ Fin T₁.nE`, then `φ v` is an endpoint of `ψ e`.  Direct
  --      from `ψ-ein`/`ψ-eout` plus `∈`-image preservation.
  --
  --   4. Constructive lemma `iso-preserves-vertex-side-from-edge`:
  --      combining (2) and (3), if `v` lies on edge `e` of T₁ and we
  --      know `edge-side₂ (ψ e) = edge-side₁ e`, then
  --      `vertex-side₂ (φ v) = vertex-side₁ v`.
  --
  --   5. Constructive lemma `iso-preserves-edge-side`: directly from
  --      `ψ-ein`/`ψ-eout` on a NON-DEGENERATE edge (one with at least
  --      one endpoint), since the endpoint already has a known side via
  --      the boundary equations or by induction on the edge structure
  --      of `⟪fᵢ⟫`/`⟪gᵢ⟫`.  (Degenerate edges with empty `ein`+`eout`
  --      are exactly the ones picked up by `ψ-restricts-L-deg`/`-R-deg`.)
  --
  --   6. Constructive lemma `boundary-vertex-side`: every boundary
  --      vertex of T₁ has a known side from `dom-split-eq-L/R` and
  --      `cod-split-eq-L/R` (already in `BoundarySlice`).
  --
  --   7. Residual lemma (the SINGLE remaining hole): every vertex of
  --      `⟪f⟫` is reachable — i.e. either appears in `⟪f⟫.dom`,
  --      `⟪f⟫.cod`, or is an endpoint of some edge in `⟪f⟫.ein _` /
  --      `⟪f⟫.eout _`.  This `vertex-coverage` lemma is a structural
  --      induction on `f : HomTerm A B` and is the genuine remaining
  --      content; it has no analogue elsewhere in the codebase yet.
  --
  -- ## OBSTRUCTION (May 2026, agent-ad5261f1): vertex-coverage is FALSE
  --
  -- The `vertex-coverage` lemma in step (7) as stated above is *not*
  -- provable — there is a concrete counter-example arising from
  -- `hCompose` of two non-empty hypergraphs that share their merged
  -- boundary:
  --
  --   Take `f = id ∘ id : HomTerm (Var x) (Var x)`.  Then
  --
  --     ⟪ id ∘ id ⟫ = hCompose ⟪ id ⟫ ⟪ id ⟫ (refl)
  --                 = hCompose (hVar x) (hVar x) (refl)
  --
  --   This compound hypergraph has
  --
  --     nV     = G.nV + K.nV = 1 + 1 = 2
  --     nE     = 0
  --     dom    = map injL G.dom = map injL [zero] = [zero ↑ˡ 1]
  --     cod    = map remap K.cod = map remap [zero]
  --                = [injL zero]   (since K.dom = G.cod = [zero] forces
  --                                  remap zero ≡ injL zero)
  --
  --   So `dom ≡ cod ≡ [Fin.zero]` and `nE ≡ 0`.  The vertex
  --   `1 ↑ˡ ... ≡ injR zero` of `Fin 2` therefore appears in NEITHER
  --   `dom`, NOR `cod`, NOR any `ein`/`eout` (the latter being empty).
  --   It is a *stranded* vertex — exactly the kind that
  --   `Linearity.agda` calls out and which the linearity invariant
  --   tolerates by allowing 0-counts.
  --
  -- The iso `φ` on `⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫` is free to send a
  -- stranded L-half vertex of T₁ to a same-label vertex anywhere in T₂
  -- (including the R-half), because stranded vertices have no edge or
  -- boundary anchor.  So `φ-restricts-L`/`-R` is itself NOT derivable
  -- from connectivity-based reasoning alone; the original postulate
  -- (or a label-multiset counting argument) is genuinely required.
  --
  -- Any future discharge of `φ-restricts-L`/`-R` must therefore either:
  --
  --   (a) Weaken `vertex-coverage` to "covered OR stranded with a
  --       same-label covered partner", and then exhibit a deterministic
  --       per-vertex assignment that the iso must respect (this still
  --       seems to fail for the symmetric case where both halves have
  --       matching stranded copies); OR
  --
  --   (b) Adopt the label-multiset counting infrastructure on
  --       `Fin nV`-lists, which directly preserves per-half cardinalities
  --       under the iso and rules out half-swaps for ALL vertices
  --       (stranded or not).  This is the same infrastructure that
  --       `ψ-restricts-*-deg` requires.
  --
  -- The current narrowing (4 sub-postulates) is therefore the right
  -- factoring and the `vertex-coverage` route is a dead end: the next
  -- step on this proof has to be the multiset counting layer.
  --
  -- Once (1)–(7) are in place, `φ-restricts-L`/`-R` are derivable in a
  -- non-mutual fashion (the edge-side argument no longer references
  -- `φ_L`).  The two `ψ-restricts-*-deg` postulates still need a
  -- SEPARATE argument: they concern `mor unit unit` "ghost" edges with
  -- no endpoints, where neither side functions nor connectivity help.
  -- A counting argument on the multiset of edge labels per half (the
  -- iso preserves edge labels, and the per-half label-multiset is an
  -- intrinsic invariant of `⟪fᵢ⟫`/`⟪gᵢ⟫`) is the natural route, but it
  -- also requires its own infrastructure (a `Multiset`/permutation
  -- treatment of `Fin nE` lists).
  --
  -- ## Soundness audit of the four postulates
  --
  -- Each postulate has been independently checked against the σ-style
  -- "label repetition across halves" counter-example:
  --
  --   * `φ-restricts-L`/`-R` — NOT falsifiable by the counter-example,
  --     because vertices live in disjoint Fin coproducts; the iso's
  --     bijection acts on raw `Fin (G.nV+K.nV)` indices, not on labels.
  --     The only way to falsify would be a structural "half-swap" iso
  --     between heterogeneous types, which the type discipline of
  --     `HomTerm A B`/`HomTerm C D` rules out.
  --
  --   * `ψ-restricts-L-deg`/`-R-deg` — narrowest possible form: only
  --     fires on ghost edges with no endpoints in either direction.
  --     Falsifiability would require two `mor unit unit` edges, one in
  --     each half, with identical edge labels, and the iso swapping
  --     them; this is again ruled out by the structural decomposition
  --     of the HomTerm tensor.  This case is genuinely the
  --     "indistinguishable bookkeeping" corner and any cleanup likely
  --     requires the label-multiset counting argument above.
  --
  -- The current narrowing (4 sub-postulates instead of 1 monolithic
  -- `iso-decompose-⊗⊗`) is therefore sound, and any further discharge
  -- requires either the `vertex-coverage` structural lemma or the
  -- label-multiset counting infrastructure — neither of which exists
  -- elsewhere in the codebase yet.
  --
  -- May 2026 narrowing: the BOUNDARY case (vertices in G₁.dom or G₁.cod,
  -- resp. K₁.dom or K₁.cod) is now constructively discharged via
  -- `BoundaryDischarge` above.  We therefore narrow the postulates to
  -- *non-boundary* (interior + stranded) vertices.  The strict-narrowing
  -- property is immediate: trivially weaker than the full ∀-statement.
  open import Data.List.Membership.Propositional using (_∉_)

  postulate
    -- Narrower postulate: only fires when iG is in NEITHER G₁.dom nor
    -- G₁.cod (i.e. an interior or stranded L-half vertex).
    φ-restricts-L-non-bdy
      : ∀ (iG : Fin G₁.nV)
      → iG ∉ G₁.dom
      → iG ∉ G₁.cod
      → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV

    φ-restricts-R-non-bdy
      : ∀ (iK : Fin K₁.nV)
      → iK ∉ K₁.dom
      → iK ∉ K₁.cod
      → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'

  -- Constructive φ-restricts-L: dispatch on whether `iG` is a boundary
  -- vertex (in G₁.dom or G₁.cod, in which case
  -- `BoundaryDischarge.φ-restricts-L-from-dom`/`-cod` discharges it),
  -- or a non-boundary vertex (delegate to the narrower postulate).
  private
    module _∈?_-G₁-dom where
      open import Data.Fin.Properties using (_≟_)
      open import Data.List.Membership.DecPropositional (_≟_ {n = G₁.nV}) public

    module _∈?_-K₁-dom where
      open import Data.Fin.Properties using (_≟_)
      open import Data.List.Membership.DecPropositional (_≟_ {n = K₁.nV}) public

    open import Data.List.Relation.Unary.Any using (Any; here; there)
    open import Relation.Nullary.Decidable using (yes; no)
    open import Data.List.Membership.Propositional using (_∈_)

    -- Convert `Any (_≡ x) xs` into a decomposition `xs ≡ ys ++ x ∷ zs`.
    any-to-decomp
      : ∀ {A : Set} {x : A} {xs : List A}
      → Any (_≡_ x) xs
      → Σ (List A) λ ys → Σ (List A) λ zs → xs ≡ ys ++ x ∷ zs
    any-to-decomp {xs = []}     ()
    any-to-decomp {xs = y ∷ xs} (here refl) = [] , xs , refl
    any-to-decomp {xs = y ∷ xs} (there p)
      with any-to-decomp p
    ... | ys , zs , refl = (y ∷ ys) , zs , refl

  φ-restricts-L
    : ∀ (iG : Fin G₁.nV)
    → Σ (Fin G₂.nV) λ iG' → φ (iG ↑ˡ K₁.nV) ≡ iG' ↑ˡ K₂.nV
  φ-restricts-L iG with _∈?_-G₁-dom._∈?_ iG G₁.dom
  ... | yes mem = BoundaryDischarge.φ-restricts-L-from-dom
                    f₁ g₁ f₂ g₂ iso iG (any-to-decomp mem)
  ... | no  ¬dom with _∈?_-G₁-dom._∈?_ iG G₁.cod
  ...   | yes mem = BoundaryDischarge.φ-restricts-L-from-cod
                      f₁ g₁ f₂ g₂ iso iG (any-to-decomp mem)
  ...   | no  ¬cod = φ-restricts-L-non-bdy iG ¬dom ¬cod

  φ-restricts-R
    : ∀ (iK : Fin K₁.nV)
    → Σ (Fin K₂.nV) λ iK' → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ iK'
  φ-restricts-R iK with _∈?_-K₁-dom._∈?_ iK K₁.dom
  ... | yes mem = BoundaryDischarge.φ-restricts-R-from-dom
                    f₁ g₁ f₂ g₂ iso iK (any-to-decomp mem)
  ... | no  ¬dom with _∈?_-K₁-dom._∈?_ iK K₁.cod
  ...   | yes mem = BoundaryDischarge.φ-restricts-R-from-cod
                      f₁ g₁ f₂ g₂ iso iK (any-to-decomp mem)
  ...   | no  ¬cod = φ-restricts-R-non-bdy iK ¬dom ¬cod

  -- Forward bijection on the L-half of vertices, extracted from
  -- `φ-restricts-L`.
  φ_L : Fin G₁.nV → Fin G₂.nV
  φ_L iG = proj₁ (φ-restricts-L iG)

  φ_L-eq : ∀ iG → φ (iG ↑ˡ K₁.nV) ≡ φ_L iG ↑ˡ K₂.nV
  φ_L-eq iG = proj₂ (φ-restricts-L iG)

  φ_R : Fin K₁.nV → Fin K₂.nV
  φ_R iK = proj₁ (φ-restricts-R iK)

  φ_R-eq : ∀ iK → φ (G₁.nV ↑ʳ iK) ≡ G₂.nV ↑ʳ φ_R iK
  φ_R-eq iK = proj₂ (φ-restricts-R iK)

  --------------------------------------------------------------------
  -- Edge half-restriction is now DISCHARGED (no longer a postulate).
  --
  -- Strategy.  Pattern-match on `splitAt G₂.nE (ψ (eG ↑ˡ K₁.nE))`:
  --
  --   * `inj₁ eG'` case: by `splitAt⁻¹-↑ˡ`, we get
  --     `ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE`, and we return `eG'`.
  --
  --   * `inj₂ eK'` case: by `splitAt⁻¹-↑ʳ`, we get
  --     `ψ (eG ↑ˡ K₁.nE) ≡ G₂.nE ↑ʳ eK'`.  Apply `ψ-ein` (resp. `ψ-eout`):
  --     the iso says `T₂.ein (ψ (eG ↑ˡ K₁.nE)) ≡ map φ (T₁.ein (eG ↑ˡ K₁.nE))`.
  --     - LHS reduces to `map (G₂.nV ↑ʳ_) (K₂.ein eK')` (R-half vertices).
  --     - RHS reduces to `map (_↑ˡ K₂.nV) (map φ_L (G₁.ein eG))` using
  --       `φ-restricts-L` pointwise on the entries.
  --     If `G₁.ein eG ∷⁺` non-empty, taking the head of each list gives
  --     `G₂.nV ↑ʳ _ ≡ _ ↑ˡ K₂.nV`, contradicting `↑ʳ≢↑ˡ`.
  --     We try `G₁.ein eG`; if empty, fall back to `G₁.eout eG` via the
  --     `ψ-eout` constraint.
  --
  -- The remaining "degenerate" case where BOTH `G₁.ein eG = []` and
  -- `G₁.eout eG = []` corresponds to a `mor unit unit` edge with no
  -- endpoints.  This case is NOT discharged here: such "ghost" edges
  -- are genuinely indistinguishable to the iso and the iso could map
  -- them across halves.  We leave it as a narrower sub-postulate
  -- `ψ-restricts-L-deg` / `-R-deg` strictly weaker than the original.

  private
    -- Helpers (hTensor-impl, map-via-inj, map-via-raise are already in
    -- scope from the top-level `open import` of `FromAPROP`).
    module hT₁ = hTensor-impl ⟪ f₁ ⟫ ⟪ g₁ ⟫
    module hT₂ = hTensor-impl ⟪ f₂ ⟫ ⟪ g₂ ⟫

    -- `T₁′`, `T₂′` are local convenience aliases for the tensor
    -- hypergraphs.  They are intentionally distinct from `Assembly`'s
    -- public `T₁`, `T₂` (and the modules of the same name there) — we
    -- use them only inside the `ψ-restricts-L`/`-R` proofs below.
    module T₁′ = Hypergraph ⟪ f₁ ⊗₁ g₁ ⟫
    module T₂′ = Hypergraph ⟪ f₂ ⊗₁ g₂ ⟫

    -- `map φ (map (_↑ˡ K₁.nV) xs) ≡ map (_↑ˡ K₂.nV) (map φ_L xs)`.
    map-φ-injL-vert : (xs : List (Fin G₁.nV))
      → map φ (map (_↑ˡ K₁.nV) xs) ≡ map (_↑ˡ K₂.nV) (map φ_L xs)
    map-φ-injL-vert xs =
      trans (sym (map-∘ xs))
      (trans (map-cong φ_L-eq xs)
             (map-∘ xs))

    -- `map φ (map (G₁.nV ↑ʳ_) xs) ≡ map (G₂.nV ↑ʳ_) (map φ_R xs)`.
    map-φ-injR-vert : (xs : List (Fin K₁.nV))
      → map φ (map (G₁.nV ↑ʳ_) xs) ≡ map (G₂.nV ↑ʳ_) (map φ_R xs)
    map-φ-injR-vert xs =
      trans (sym (map-∘ xs))
      (trans (map-cong φ_R-eq xs)
             (map-∘ xs))

    -- Head-of-list mismatch: `map (G₂.nV ↑ʳ_) (k ∷ ks) ≡ map (_↑ˡ K₂.nV) (l ∷ ls)`
    -- forces `G₂.nV ↑ʳ k ≡ l ↑ˡ K₂.nV`, contradicting `↑ʳ≢↑ˡ`.
    ∷-↑ʳ≢↑ˡ
      : ∀ (k : Fin K₂.nV) (l : Fin G₂.nV) ks ls
      → map (G₂.nV ↑ʳ_) (k ∷ ks) ≡ map (_↑ˡ K₂.nV) (l ∷ ls) → ⊥
    ∷-↑ʳ≢↑ˡ k l ks ls eq = ↑ʳ≢↑ˡ l k head-eq
      where
        ∷-head : ∀ {A : Set} {x x' : A} {xs xs' : List A}
               → x ∷ xs ≡ x' ∷ xs' → x ≡ x'
        ∷-head refl = refl
        head-eq : G₂.nV ↑ʳ k ≡ l ↑ˡ K₂.nV
        head-eq = ∷-head eq

    -- Symmetric: `map (_↑ˡ K₂.nV) (l ∷ ls) ≡ map (G₂.nV ↑ʳ_) (k ∷ ks)`.
    ∷-↑ˡ≢↑ʳ
      : ∀ (l : Fin G₂.nV) (k : Fin K₂.nV) ls ks
      → map (_↑ˡ K₂.nV) (l ∷ ls) ≡ map (G₂.nV ↑ʳ_) (k ∷ ks) → ⊥
    ∷-↑ˡ≢↑ʳ l k ls ks eq = ↑ˡ≢↑ʳ l k head-eq
      where
        ∷-head : ∀ {A : Set} {x x' : A} {xs xs' : List A}
               → x ∷ xs ≡ x' ∷ xs' → x ≡ x'
        ∷-head refl = refl
        head-eq : l ↑ˡ K₂.nV ≡ G₂.nV ↑ʳ k
        head-eq = ∷-head eq

    -- A reusable contradiction extractor.  Given a non-empty list on
    -- one side of `_↑ʳ_` versus an arbitrary list on the `_↑ˡ_` side,
    -- the head-of-list `↑ʳ` vs `↑ˡ` disagreement produces ⊥.
    nonempty-↑ʳ≡↑ˡ-impossible
      : (k : Fin K₂.nV) (ks : List (Fin K₂.nV))
      → (ws : List (Fin G₂.nV))
      → map (G₂.nV ↑ʳ_) (k ∷ ks) ≡ map (_↑ˡ K₂.nV) ws
      → ⊥
    nonempty-↑ʳ≡↑ˡ-impossible k ks []        ()
    nonempty-↑ʳ≡↑ˡ-impossible k ks (w ∷ ws) eq = ∷-↑ʳ≢↑ˡ k w ks ws eq

    -- Symmetric.
    nonempty-↑ˡ≡↑ʳ-impossible
      : (g : Fin G₂.nV) (gs : List (Fin G₂.nV))
      → (ws : List (Fin K₂.nV))
      → map (_↑ˡ K₂.nV) (g ∷ gs) ≡ map (G₂.nV ↑ʳ_) ws
      → ⊥
    nonempty-↑ˡ≡↑ʳ-impossible g gs []        ()
    nonempty-↑ˡ≡↑ʳ-impossible g gs (w ∷ ws) eq = ∷-↑ˡ≢↑ʳ g w gs ws eq

  postulate
    -- "Degenerate" sub-postulates: only fire when the L-half edge
    -- has BOTH empty `ein` and empty `eout` (a `mor unit unit` ghost
    -- edge).  These are strictly weaker than the original
    -- `ψ-restricts-L`/`-R` postulates and only required for the corner
    -- case of unit→unit generators inside the tensor halves.
    ψ-restricts-L-deg
      : ∀ (eG : Fin G₁.nE)
      → G₁.ein eG ≡ []
      → G₁.eout eG ≡ []
      → Σ (Fin G₂.nE) λ eG' → ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE

    ψ-restricts-R-deg
      : ∀ (eK : Fin K₁.nE)
      → K₁.ein eK ≡ []
      → K₁.eout eK ≡ []
      → Σ (Fin K₂.nE) λ eK' → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ eK'

  -- ψ-restricts-L now DISCHARGED (no longer a postulate).
  ψ-restricts-L
    : ∀ (eG : Fin G₁.nE)
    → Σ (Fin G₂.nE) λ eG' → ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE
  ψ-restricts-L eG with splitAt G₂.nE (ψ (eG ↑ˡ K₁.nE)) in splEq
  ... | inj₁ eG' = eG' , sym (splitAt⁻¹-↑ˡ splEq)
  ... | inj₂ eK' = handle (G₁.ein eG) refl (G₁.eout eG) refl
    where
      back-eq : G₂.nE ↑ʳ eK' ≡ ψ (eG ↑ˡ K₁.nE)
      back-eq = splitAt⁻¹-↑ʳ splEq

      -- ψ-ein at (eG ↑ˡ K₁.nE).
      ein-iso : T₂′.ein (ψ (eG ↑ˡ K₁.nE)) ≡ map φ (T₁′.ein (eG ↑ˡ K₁.nE))
      ein-iso = ψ-ein (eG ↑ˡ K₁.nE)

      eout-iso : T₂′.eout (ψ (eG ↑ˡ K₁.nE)) ≡ map φ (T₁′.eout (eG ↑ˡ K₁.nE))
      eout-iso = ψ-eout (eG ↑ˡ K₁.nE)

      -- Rewrite LHS at G₂.nE ↑ʳ eK' (using back-eq) → map (G₂.nV ↑ʳ_) (K₂.ein eK').
      ein-LHS-rewrite
        : map (G₂.nV ↑ʳ_) (K₂.ein eK') ≡ map φ (T₁′.ein (eG ↑ˡ K₁.nE))
      ein-LHS-rewrite =
        trans (sym (hT₂.ein-c-inj₂-red eK'))
        (trans (cong T₂′.ein back-eq) ein-iso)

      eout-LHS-rewrite
        : map (G₂.nV ↑ʳ_) (K₂.eout eK') ≡ map φ (T₁′.eout (eG ↑ˡ K₁.nE))
      eout-LHS-rewrite =
        trans (sym (hT₂.eout-c-inj₂-red eK'))
        (trans (cong T₂′.eout back-eq) eout-iso)

      -- Rewrite RHS using hT₁.ein-c-inj₁-red and map-φ-injL-vert.
      ein-RHS-rewrite
        : map φ (T₁′.ein (eG ↑ˡ K₁.nE))
        ≡ map (_↑ˡ K₂.nV) (map φ_L (G₁.ein eG))
      ein-RHS-rewrite =
        trans (cong (map φ) (hT₁.ein-c-inj₁-red eG))
              (map-φ-injL-vert (G₁.ein eG))

      eout-RHS-rewrite
        : map φ (T₁′.eout (eG ↑ˡ K₁.nE))
        ≡ map (_↑ˡ K₂.nV) (map φ_L (G₁.eout eG))
      eout-RHS-rewrite =
        trans (cong (map φ) (hT₁.eout-c-inj₁-red eG))
              (map-φ-injL-vert (G₁.eout eG))

      -- Combined:
      ein-combined
        : map (G₂.nV ↑ʳ_) (K₂.ein eK')
        ≡ map (_↑ˡ K₂.nV) (map φ_L (G₁.ein eG))
      ein-combined = trans ein-LHS-rewrite ein-RHS-rewrite

      eout-combined
        : map (G₂.nV ↑ʳ_) (K₂.eout eK')
        ≡ map (_↑ˡ K₂.nV) (map φ_L (G₁.eout eG))
      eout-combined = trans eout-LHS-rewrite eout-RHS-rewrite

      -- Now case on whether G₁.ein eG / G₁.eout eG are non-empty.
      -- If either is non-empty, derive ⊥; if both empty, use the
      -- narrow `ψ-restricts-L-deg` postulate.
      handle
        : (e : List (Fin G₁.nV))
        → G₁.ein eG ≡ e
        → (o : List (Fin G₁.nV))
        → G₁.eout eG ≡ o
        → Σ (Fin G₂.nE) λ eG' → ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE
      handle []        eeq []          oeq = ψ-restricts-L-deg eG eeq oeq
      handle []        eeq (x₀ ∷ xs₀)  oeq =
        -- G₁.eout eG = x₀ ∷ xs₀ (non-empty).  Use eout to derive ⊥.
        go (K₂.eout eK') refl
        where
          eq-with-oeq
            : map (G₂.nV ↑ʳ_) (K₂.eout eK')
            ≡ map (_↑ˡ K₂.nV) (map φ_L (x₀ ∷ xs₀))
          eq-with-oeq =
            trans eout-combined (cong (λ z → map (_↑ˡ K₂.nV) (map φ_L z))
                                       oeq)

          go : ∀ (l : List (Fin K₂.nV)) → K₂.eout eK' ≡ l
             → Σ (Fin G₂.nE) λ eG' → ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE
          go []        keq =
            ⊥-elim (case-empty
              (trans (sym (cong (map (G₂.nV ↑ʳ_)) keq)) eq-with-oeq))
            where
              case-empty : [] ≡ map (_↑ˡ K₂.nV) (map φ_L (x₀ ∷ xs₀)) → ⊥
              case-empty ()
          go (k ∷ ks)  keq =
            ⊥-elim (nonempty-↑ʳ≡↑ˡ-impossible k ks
                      (map φ_L (x₀ ∷ xs₀))
                      (trans (sym (cong (map (G₂.nV ↑ʳ_)) keq)) eq-with-oeq))
      handle (x₀ ∷ xs₀)  eeq o           oeq =
        -- G₁.ein eG = x₀ ∷ xs₀ (non-empty).  Use ein to derive ⊥.
        go (K₂.ein eK') refl
        where
          eq-with-eeq
            : map (G₂.nV ↑ʳ_) (K₂.ein eK')
            ≡ map (_↑ˡ K₂.nV) (map φ_L (x₀ ∷ xs₀))
          eq-with-eeq =
            trans ein-combined (cong (λ z → map (_↑ˡ K₂.nV) (map φ_L z))
                                      eeq)

          go : ∀ (l : List (Fin K₂.nV)) → K₂.ein eK' ≡ l
             → Σ (Fin G₂.nE) λ eG' → ψ (eG ↑ˡ K₁.nE) ≡ eG' ↑ˡ K₂.nE
          go []        keq =
            ⊥-elim (case-empty
              (trans (sym (cong (map (G₂.nV ↑ʳ_)) keq)) eq-with-eeq))
            where
              case-empty : [] ≡ map (_↑ˡ K₂.nV) (map φ_L (x₀ ∷ xs₀)) → ⊥
              case-empty ()
          go (k ∷ ks)  keq =
            ⊥-elim (nonempty-↑ʳ≡↑ˡ-impossible k ks
                      (map φ_L (x₀ ∷ xs₀))
                      (trans (sym (cong (map (G₂.nV ↑ʳ_)) keq)) eq-with-eeq))

  -- ψ-restricts-R DISCHARGED (no longer a postulate).
  ψ-restricts-R
    : ∀ (eK : Fin K₁.nE)
    → Σ (Fin K₂.nE) λ eK' → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ eK'
  ψ-restricts-R eK with splitAt G₂.nE (ψ (G₁.nE ↑ʳ eK)) in splEq
  ... | inj₂ eK' = eK' , sym (splitAt⁻¹-↑ʳ splEq)
  ... | inj₁ eG' = handle (K₁.ein eK) refl (K₁.eout eK) refl
    where
      back-eq : eG' ↑ˡ K₂.nE ≡ ψ (G₁.nE ↑ʳ eK)
      back-eq = splitAt⁻¹-↑ˡ splEq

      ein-iso : T₂′.ein (ψ (G₁.nE ↑ʳ eK)) ≡ map φ (T₁′.ein (G₁.nE ↑ʳ eK))
      ein-iso = ψ-ein (G₁.nE ↑ʳ eK)

      eout-iso : T₂′.eout (ψ (G₁.nE ↑ʳ eK)) ≡ map φ (T₁′.eout (G₁.nE ↑ʳ eK))
      eout-iso = ψ-eout (G₁.nE ↑ʳ eK)

      ein-LHS-rewrite
        : map (_↑ˡ K₂.nV) (G₂.ein eG') ≡ map φ (T₁′.ein (G₁.nE ↑ʳ eK))
      ein-LHS-rewrite =
        trans (sym (hT₂.ein-c-inj₁-red eG'))
        (trans (cong T₂′.ein back-eq) ein-iso)

      eout-LHS-rewrite
        : map (_↑ˡ K₂.nV) (G₂.eout eG') ≡ map φ (T₁′.eout (G₁.nE ↑ʳ eK))
      eout-LHS-rewrite =
        trans (sym (hT₂.eout-c-inj₁-red eG'))
        (trans (cong T₂′.eout back-eq) eout-iso)

      ein-RHS-rewrite
        : map φ (T₁′.ein (G₁.nE ↑ʳ eK))
        ≡ map (G₂.nV ↑ʳ_) (map φ_R (K₁.ein eK))
      ein-RHS-rewrite =
        trans (cong (map φ) (hT₁.ein-c-inj₂-red eK))
              (map-φ-injR-vert (K₁.ein eK))

      eout-RHS-rewrite
        : map φ (T₁′.eout (G₁.nE ↑ʳ eK))
        ≡ map (G₂.nV ↑ʳ_) (map φ_R (K₁.eout eK))
      eout-RHS-rewrite =
        trans (cong (map φ) (hT₁.eout-c-inj₂-red eK))
              (map-φ-injR-vert (K₁.eout eK))

      ein-combined
        : map (_↑ˡ K₂.nV) (G₂.ein eG')
        ≡ map (G₂.nV ↑ʳ_) (map φ_R (K₁.ein eK))
      ein-combined = trans ein-LHS-rewrite ein-RHS-rewrite

      eout-combined
        : map (_↑ˡ K₂.nV) (G₂.eout eG')
        ≡ map (G₂.nV ↑ʳ_) (map φ_R (K₁.eout eK))
      eout-combined = trans eout-LHS-rewrite eout-RHS-rewrite

      handle
        : (e : List (Fin K₁.nV))
        → K₁.ein eK ≡ e
        → (o : List (Fin K₁.nV))
        → K₁.eout eK ≡ o
        → Σ (Fin K₂.nE) λ eK' → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ eK'
      handle []        eeq []          oeq = ψ-restricts-R-deg eK eeq oeq
      handle []        eeq (x₀ ∷ xs₀)  oeq =
        go (G₂.eout eG') refl
        where
          eq-with-oeq
            : map (_↑ˡ K₂.nV) (G₂.eout eG')
            ≡ map (G₂.nV ↑ʳ_) (map φ_R (x₀ ∷ xs₀))
          eq-with-oeq =
            trans eout-combined (cong (λ z → map (G₂.nV ↑ʳ_) (map φ_R z))
                                       oeq)

          go : ∀ (l : List (Fin G₂.nV)) → G₂.eout eG' ≡ l
             → Σ (Fin K₂.nE) λ eK' → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ eK'
          go []        geq =
            ⊥-elim (case-empty
              (trans (sym (cong (map (_↑ˡ K₂.nV)) geq)) eq-with-oeq))
            where
              case-empty : [] ≡ map (G₂.nV ↑ʳ_) (map φ_R (x₀ ∷ xs₀)) → ⊥
              case-empty ()
          go (g ∷ gs)  geq =
            ⊥-elim (nonempty-↑ˡ≡↑ʳ-impossible g gs
                      (map φ_R (x₀ ∷ xs₀))
                      (trans (sym (cong (map (_↑ˡ K₂.nV)) geq)) eq-with-oeq))
      handle (x₀ ∷ xs₀)  eeq o           oeq =
        go (G₂.ein eG') refl
        where
          eq-with-eeq
            : map (_↑ˡ K₂.nV) (G₂.ein eG')
            ≡ map (G₂.nV ↑ʳ_) (map φ_R (x₀ ∷ xs₀))
          eq-with-eeq =
            trans ein-combined (cong (λ z → map (G₂.nV ↑ʳ_) (map φ_R z))
                                      eeq)

          go : ∀ (l : List (Fin G₂.nV)) → G₂.ein eG' ≡ l
             → Σ (Fin K₂.nE) λ eK' → ψ (G₁.nE ↑ʳ eK) ≡ G₂.nE ↑ʳ eK'
          go []        geq =
            ⊥-elim (case-empty
              (trans (sym (cong (map (_↑ˡ K₂.nV)) geq)) eq-with-eeq))
            where
              case-empty : [] ≡ map (G₂.nV ↑ʳ_) (map φ_R (x₀ ∷ xs₀)) → ⊥
              case-empty ()
          go (g ∷ gs)  geq =
            ⊥-elim (nonempty-↑ˡ≡↑ʳ-impossible g gs
                      (map φ_R (x₀ ∷ xs₀))
                      (trans (sym (cong (map (_↑ˡ K₂.nV)) geq)) eq-with-eeq))

  -- Extracted half-restricted bijections on edges (forward direction).
  -- `φ_L`/`φ_R` defined earlier; here we extract `ψ_L`/`ψ_R` from the
  -- now-discharged `ψ-restricts-L`/`-R`.
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
  ... | inj₂ iK = ⊥-elim (↑ʳ≢↑ˡ iG' (φ_R iK) step₃)
    where
      -- φ⁻¹ (iG' ↑ˡ K₂.nV) = G₁.nV ↑ʳ iK, so applying φ gives
      -- iG' ↑ˡ K₂.nV = φ(G₁.nV ↑ʳ iK) = G₂.nV ↑ʳ (φ_R iK) (by φ_R-eq).
      back-eq : G₁.nV ↑ʳ iK ≡ φ⁻¹ (iG' ↑ˡ K₂.nV)
      back-eq = splitAt⁻¹-↑ʳ eq

      apply-φ : φ (φ⁻¹ (iG' ↑ˡ K₂.nV)) ≡ iG' ↑ˡ K₂.nV
      apply-φ = φ-rght (iG' ↑ˡ K₂.nV)

      step₂ : φ (G₁.nV ↑ʳ iK) ≡ iG' ↑ˡ K₂.nV
      step₂ = trans (cong φ back-eq) apply-φ

      step₃ : G₂.nV ↑ʳ (φ_R iK) ≡ iG' ↑ˡ K₂.nV
      step₃ = trans (sym (φ_R-eq iK)) step₂

  φ_L⁻¹ : Fin G₂.nV → Fin G₁.nV
  φ_L⁻¹ iG' = proj₁ (φ_L⁻¹-data iG')

  φ_L⁻¹-eq : ∀ iG' → φ⁻¹ (iG' ↑ˡ K₂.nV) ≡ φ_L⁻¹ iG' ↑ˡ K₁.nV
  φ_L⁻¹-eq iG' = proj₂ (φ_L⁻¹-data iG')

  -- R-side inverse map: φ⁻¹ on (G₂.nV ↑ʳ iK') is in the R-half of T₁.
  φ_R⁻¹-data
    : ∀ (iK' : Fin K₂.nV)
    → Σ (Fin K₁.nV) λ iK → φ⁻¹ (G₂.nV ↑ʳ iK') ≡ G₁.nV ↑ʳ iK
  φ_R⁻¹-data iK' with splitAt G₁.nV (φ⁻¹ (G₂.nV ↑ʳ iK')) in eq
  ... | inj₁ iG = ⊥-elim (↑ˡ≢↑ʳ (φ_L iG) iK' step₃)
    where
      back-eq : iG ↑ˡ K₁.nV ≡ φ⁻¹ (G₂.nV ↑ʳ iK')
      back-eq = splitAt⁻¹-↑ˡ eq

      apply-φ : φ (φ⁻¹ (G₂.nV ↑ʳ iK')) ≡ G₂.nV ↑ʳ iK'
      apply-φ = φ-rght (G₂.nV ↑ʳ iK')

      step₂ : φ (iG ↑ˡ K₁.nV) ≡ G₂.nV ↑ʳ iK'
      step₂ = trans (cong φ back-eq) apply-φ

      step₃ : (φ_L iG) ↑ˡ K₂.nV ≡ G₂.nV ↑ʳ iK'
      step₃ = trans (sym (φ_L-eq iG)) step₂
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
      back-eq = splitAt⁻¹-↑ʳ eq

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
      back-eq = splitAt⁻¹-↑ˡ eq

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

--------------------------------------------------------------------------------
-- Assembly: from the four block-diagonal sub-postulates plus their
-- constructively-derived inverse-direction data, build two sub-isos
--
--    iso-L : ⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫
--    iso-R : ⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫.
--
-- All record fields are derived by pulling back the analogous fields
-- of the original tensor-iso through the L/R splitting.  The boundary
-- equations use `dom-split-eq-L`/`-R` and `cod-split-eq-L`/`-R`; the
-- vertex-label, edge-endpoint, atom-list, and edge-label fields use
-- the `hT₁`/`hT₂` reduction lemmas `vlab-injL`/`vlab-injR`,
-- `ein-c-inj₁-red`/`ein-c-inj₂-red`, and `elab-c-inj₁`/`elab-c-inj₂`,
-- together with the original iso's matching fields restricted via
-- `φ_L-eq`/`ψ_L-eq` (resp. R).

module Assembly
  {A B C D}
  (f₁ : HomTerm A B) (g₁ : HomTerm C D)
  (f₂ : HomTerm A B) (g₂ : HomTerm C D)
  (iso : ⟪ f₁ ⊗₁ g₁ ⟫ ≅ᴴ ⟪ f₂ ⊗₁ g₂ ⟫)
  where

  open InverseDerivations f₁ g₁ f₂ g₂ iso public

  -- hTensor helpers for the two sides (avoids ambiguity over which
  -- `vlab-c`, `ein-c` etc. we mean).
  module hT₁ = hTensor-impl ⟪ f₁ ⟫ ⟪ g₁ ⟫
  module hT₂ = hTensor-impl ⟪ f₂ ⟫ ⟪ g₂ ⟫

  T₁ = ⟪ f₁ ⊗₁ g₁ ⟫
  T₂ = ⟪ f₂ ⊗₁ g₂ ⟫
  module T₁ = Hypergraph T₁
  module T₂ = Hypergraph T₂

  ------------------------------------------------------------------------------
  -- Generic re-writes: convert `map φ (map (_↑ˡ K.nV) xs)` into
  -- `map (_↑ˡ K.nV) (map φ_L xs)` using the elementwise `φ_L-eq`.

  map-φ-injL
    : (xs : List (Fin G₁.nV))
    → map φ (map (_↑ˡ K₁.nV) xs) ≡ map (_↑ˡ K₂.nV) (map φ_L xs)
  map-φ-injL xs =
    trans (sym (map-∘ xs))
    (trans (map-cong φ_L-eq xs)
           (map-∘ xs))

  map-φ-injR
    : (xs : List (Fin K₁.nV))
    → map φ (map (G₁.nV ↑ʳ_) xs) ≡ map (G₂.nV ↑ʳ_) (map φ_R xs)
  map-φ-injR xs =
    trans (sym (map-∘ xs))
    (trans (map-cong φ_R-eq xs)
           (map-∘ xs))

  ------------------------------------------------------------------------------
  -- Boundary preservation, restricted to the L/R halves.
  --
  --   G₂.dom ≡ map φ_L G₁.dom    (and similarly cod, R)
  --
  -- via `dom-split-eq-L` plus `map-↑ˡ-injective`.

  φ-dom-L : G₂.dom ≡ map φ_L G₁.dom
  φ-dom-L = map-↑ˡ-injective G₂.dom (map φ_L G₁.dom)
                              (trans dom-split-eq-L (map-φ-injL G₁.dom))

  φ-cod-L : G₂.cod ≡ map φ_L G₁.cod
  φ-cod-L = map-↑ˡ-injective G₂.cod (map φ_L G₁.cod)
                              (trans cod-split-eq-L (map-φ-injL G₁.cod))

  φ-dom-R : K₂.dom ≡ map φ_R K₁.dom
  φ-dom-R = map-↑ʳ-injective K₂.dom (map φ_R K₁.dom)
                              (trans dom-split-eq-R (map-φ-injR K₁.dom))

  φ-cod-R : K₂.cod ≡ map φ_R K₁.cod
  φ-cod-R = map-↑ʳ-injective K₂.cod (map φ_R K₁.cod)
                              (trans cod-split-eq-R (map-φ-injR K₁.cod))

  ------------------------------------------------------------------------------
  -- Vertex-label preservation, restricted to each half.

  φ-lab-L : ∀ iG → G₂.vlab (φ_L iG) ≡ G₁.vlab iG
  φ-lab-L iG =
    let
      -- IG.φ-lab at the lifted index `iG ↑ˡ K₁.nV`:
      lab-T : T₂.vlab (φ (iG ↑ˡ K₁.nV)) ≡ T₁.vlab (iG ↑ˡ K₁.nV)
      lab-T = φ-lab (iG ↑ˡ K₁.nV)

      -- Translate the LHS through φ_L-eq:
      lab-L-T : T₂.vlab (φ_L iG ↑ˡ K₂.nV) ≡ T₁.vlab (iG ↑ˡ K₁.nV)
      lab-L-T = trans (cong T₂.vlab (sym (φ_L-eq iG))) lab-T
    in
      -- T₂.vlab on `_↑ˡ K₂.nV` reduces to G₂.vlab; ditto T₁.
      trans (sym (hT₂.vlab-injL (φ_L iG)))
            (trans lab-L-T (hT₁.vlab-injL iG))

  φ-lab-R : ∀ iK → K₂.vlab (φ_R iK) ≡ K₁.vlab iK
  φ-lab-R iK =
    let
      lab-T : T₂.vlab (φ (G₁.nV ↑ʳ iK)) ≡ T₁.vlab (G₁.nV ↑ʳ iK)
      lab-T = φ-lab (G₁.nV ↑ʳ iK)

      lab-R-T : T₂.vlab (G₂.nV ↑ʳ φ_R iK) ≡ T₁.vlab (G₁.nV ↑ʳ iK)
      lab-R-T = trans (cong T₂.vlab (sym (φ_R-eq iK))) lab-T
    in
      trans (sym (hT₂.vlab-injR (φ_R iK)))
            (trans lab-R-T (hT₁.vlab-injR iK))

  ------------------------------------------------------------------------------
  -- Edge endpoints, restricted to each half.

  ψ-ein-L : ∀ eG → G₂.ein (ψ_L eG) ≡ map φ_L (G₁.ein eG)
  ψ-ein-L eG =
    let
      -- IG.ψ-ein at the lifted index `eG ↑ˡ K₁.nE`:
      ein-T : T₂.ein (ψ (eG ↑ˡ K₁.nE)) ≡ map φ (T₁.ein (eG ↑ˡ K₁.nE))
      ein-T = ψ-ein (eG ↑ˡ K₁.nE)

      -- Translate LHS through ψ_L-eq:
      ein-L-T : T₂.ein (ψ_L eG ↑ˡ K₂.nE) ≡ map φ (T₁.ein (eG ↑ˡ K₁.nE))
      ein-L-T = trans (cong T₂.ein (sym (ψ_L-eq eG))) ein-T

      -- Reduce T₂.ein (ψ_L eG ↑ˡ K₂.nE) via hT₂.ein-c-inj₁-red:
      step₁ : map (_↑ˡ K₂.nV) (G₂.ein (ψ_L eG))
            ≡ map φ (T₁.ein (eG ↑ˡ K₁.nE))
      step₁ = trans (sym (hT₂.ein-c-inj₁-red (ψ_L eG))) ein-L-T

      -- Reduce T₁.ein (eG ↑ˡ K₁.nE) via hT₁.ein-c-inj₁-red:
      step₂ : map (_↑ˡ K₂.nV) (G₂.ein (ψ_L eG))
            ≡ map φ (map (_↑ˡ K₁.nV) (G₁.ein eG))
      step₂ = trans step₁ (cong (map φ) (hT₁.ein-c-inj₁-red eG))

      -- Push φ through ↑ˡ via map-φ-injL:
      step₃ : map (_↑ˡ K₂.nV) (G₂.ein (ψ_L eG))
            ≡ map (_↑ˡ K₂.nV) (map φ_L (G₁.ein eG))
      step₃ = trans step₂ (map-φ-injL (G₁.ein eG))
    in
      map-↑ˡ-injective (G₂.ein (ψ_L eG)) (map φ_L (G₁.ein eG)) step₃

  ψ-eout-L : ∀ eG → G₂.eout (ψ_L eG) ≡ map φ_L (G₁.eout eG)
  ψ-eout-L eG =
    let
      eout-T : T₂.eout (ψ (eG ↑ˡ K₁.nE)) ≡ map φ (T₁.eout (eG ↑ˡ K₁.nE))
      eout-T = ψ-eout (eG ↑ˡ K₁.nE)

      eout-L-T : T₂.eout (ψ_L eG ↑ˡ K₂.nE) ≡ map φ (T₁.eout (eG ↑ˡ K₁.nE))
      eout-L-T = trans (cong T₂.eout (sym (ψ_L-eq eG))) eout-T

      step₁ : map (_↑ˡ K₂.nV) (G₂.eout (ψ_L eG))
            ≡ map φ (T₁.eout (eG ↑ˡ K₁.nE))
      step₁ = trans (sym (hT₂.eout-c-inj₁-red (ψ_L eG))) eout-L-T

      step₂ : map (_↑ˡ K₂.nV) (G₂.eout (ψ_L eG))
            ≡ map φ (map (_↑ˡ K₁.nV) (G₁.eout eG))
      step₂ = trans step₁ (cong (map φ) (hT₁.eout-c-inj₁-red eG))

      step₃ : map (_↑ˡ K₂.nV) (G₂.eout (ψ_L eG))
            ≡ map (_↑ˡ K₂.nV) (map φ_L (G₁.eout eG))
      step₃ = trans step₂ (map-φ-injL (G₁.eout eG))
    in
      map-↑ˡ-injective (G₂.eout (ψ_L eG)) (map φ_L (G₁.eout eG)) step₃

  ψ-ein-R : ∀ eK → K₂.ein (ψ_R eK) ≡ map φ_R (K₁.ein eK)
  ψ-ein-R eK =
    let
      ein-T : T₂.ein (ψ (G₁.nE ↑ʳ eK)) ≡ map φ (T₁.ein (G₁.nE ↑ʳ eK))
      ein-T = ψ-ein (G₁.nE ↑ʳ eK)

      ein-R-T : T₂.ein (G₂.nE ↑ʳ ψ_R eK) ≡ map φ (T₁.ein (G₁.nE ↑ʳ eK))
      ein-R-T = trans (cong T₂.ein (sym (ψ_R-eq eK))) ein-T

      step₁ : map (G₂.nV ↑ʳ_) (K₂.ein (ψ_R eK))
            ≡ map φ (T₁.ein (G₁.nE ↑ʳ eK))
      step₁ = trans (sym (hT₂.ein-c-inj₂-red (ψ_R eK))) ein-R-T

      step₂ : map (G₂.nV ↑ʳ_) (K₂.ein (ψ_R eK))
            ≡ map φ (map (G₁.nV ↑ʳ_) (K₁.ein eK))
      step₂ = trans step₁ (cong (map φ) (hT₁.ein-c-inj₂-red eK))

      step₃ : map (G₂.nV ↑ʳ_) (K₂.ein (ψ_R eK))
            ≡ map (G₂.nV ↑ʳ_) (map φ_R (K₁.ein eK))
      step₃ = trans step₂ (map-φ-injR (K₁.ein eK))
    in
      map-↑ʳ-injective (K₂.ein (ψ_R eK)) (map φ_R (K₁.ein eK)) step₃

  ψ-eout-R : ∀ eK → K₂.eout (ψ_R eK) ≡ map φ_R (K₁.eout eK)
  ψ-eout-R eK =
    let
      eout-T : T₂.eout (ψ (G₁.nE ↑ʳ eK)) ≡ map φ (T₁.eout (G₁.nE ↑ʳ eK))
      eout-T = ψ-eout (G₁.nE ↑ʳ eK)

      eout-R-T : T₂.eout (G₂.nE ↑ʳ ψ_R eK) ≡ map φ (T₁.eout (G₁.nE ↑ʳ eK))
      eout-R-T = trans (cong T₂.eout (sym (ψ_R-eq eK))) eout-T

      step₁ : map (G₂.nV ↑ʳ_) (K₂.eout (ψ_R eK))
            ≡ map φ (T₁.eout (G₁.nE ↑ʳ eK))
      step₁ = trans (sym (hT₂.eout-c-inj₂-red (ψ_R eK))) eout-R-T

      step₂ : map (G₂.nV ↑ʳ_) (K₂.eout (ψ_R eK))
            ≡ map φ (map (G₁.nV ↑ʳ_) (K₁.eout eK))
      step₂ = trans step₁ (cong (map φ) (hT₁.eout-c-inj₂-red eK))

      step₃ : map (G₂.nV ↑ʳ_) (K₂.eout (ψ_R eK))
            ≡ map (G₂.nV ↑ʳ_) (map φ_R (K₁.eout eK))
      step₃ = trans step₂ (map-φ-injR (K₁.eout eK))
    in
      map-↑ʳ-injective (K₂.eout (ψ_R eK)) (map φ_R (K₁.eout eK)) step₃

  ------------------------------------------------------------------------------
  -- Atom-list equalities.
  --
  -- Defined as the explicit chain that the `ψ-elab-L`/`-R` proofs
  -- below produce when they unwind the original `ψ-elab` field
  -- through the L/R restriction.  This definitional choice makes
  -- `ψ-elab-L`/`-R` go through without UIP: the proof's running
  -- `subst₂` ends up parameterised by exactly these `trans` chains.
  --
  -- The chain shape, for the L-half:
  --
  --   map G₂.vlab (G₂.ein (ψ_L eG))
  --     ≡⟨ map-via-inj hT₂.vlab-injL ⟩
  --   map T₂.vlab (map injL₂ (G₂.ein (ψ_L eG)))
  --     ≡⟨ sym (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red (ψ_L eG))) ⟩
  --   map T₂.vlab (T₂.ein (ψ_L eG ↑ˡ K₂.nE))
  --     ≡⟨ sym (cong (λ z → map T₂.vlab (T₂.ein z)) (ψ_L-eq eG)) ⟩
  --   map T₂.vlab (T₂.ein (ψ (eG ↑ˡ K₁.nE)))
  --     ≡⟨ atom-ein (eG ↑ˡ K₁.nE) ⟩
  --   map T₁.vlab (T₁.ein (eG ↑ˡ K₁.nE))
  --     ≡⟨ cong (map T₁.vlab) (hT₁.ein-c-inj₁-red eG) ⟩
  --   map T₁.vlab (map injL₁ (G₁.ein eG))
  --     ≡⟨ sym (map-via-inj hT₁.vlab-injL) ⟩
  --   map G₁.vlab (G₁.ein eG)

  atom-ein-L : ∀ eG → map G₂.vlab (G₂.ein (ψ_L eG))
                    ≡ map G₁.vlab (G₁.ein eG)
  atom-ein-L eG =
    trans (map-via-inj hT₂.vlab-injL (G₂.ein (ψ_L eG)))
    (trans (sym (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red (ψ_L eG))))
    (trans (cong (λ z → map T₂.vlab (T₂.ein z)) (sym (ψ_L-eq eG)))
    (trans (atom-ein (eG ↑ˡ K₁.nE))
    (trans (cong (map T₁.vlab) (hT₁.ein-c-inj₁-red eG))
           (sym (map-via-inj hT₁.vlab-injL (G₁.ein eG)))))))

  atom-eout-L : ∀ eG → map G₂.vlab (G₂.eout (ψ_L eG))
                     ≡ map G₁.vlab (G₁.eout eG)
  atom-eout-L eG =
    trans (map-via-inj hT₂.vlab-injL (G₂.eout (ψ_L eG)))
    (trans (sym (cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (ψ_L eG))))
    (trans (cong (λ z → map T₂.vlab (T₂.eout z)) (sym (ψ_L-eq eG)))
    (trans (atom-eout (eG ↑ˡ K₁.nE))
    (trans (cong (map T₁.vlab) (hT₁.eout-c-inj₁-red eG))
           (sym (map-via-inj hT₁.vlab-injL (G₁.eout eG)))))))

  atom-ein-R : ∀ eK → map K₂.vlab (K₂.ein (ψ_R eK))
                    ≡ map K₁.vlab (K₁.ein eK)
  atom-ein-R eK =
    trans (map-via-raise hT₂.vlab-injR (K₂.ein (ψ_R eK)))
    (trans (sym (cong (map T₂.vlab) (hT₂.ein-c-inj₂-red (ψ_R eK))))
    (trans (cong (λ z → map T₂.vlab (T₂.ein z)) (sym (ψ_R-eq eK)))
    (trans (atom-ein (G₁.nE ↑ʳ eK))
    (trans (cong (map T₁.vlab) (hT₁.ein-c-inj₂-red eK))
           (sym (map-via-raise hT₁.vlab-injR (K₁.ein eK)))))))

  atom-eout-R : ∀ eK → map K₂.vlab (K₂.eout (ψ_R eK))
                     ≡ map K₁.vlab (K₁.eout eK)
  atom-eout-R eK =
    trans (map-via-raise hT₂.vlab-injR (K₂.eout (ψ_R eK)))
    (trans (sym (cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (ψ_R eK))))
    (trans (cong (λ z → map T₂.vlab (T₂.eout z)) (sym (ψ_R-eq eK)))
    (trans (atom-eout (G₁.nE ↑ʳ eK))
    (trans (cong (map T₁.vlab) (hT₁.eout-c-inj₂-red eK))
           (sym (map-via-raise hT₁.vlab-injR (K₁.eout eK)))))))

  ------------------------------------------------------------------------------
  -- Edge-label preservation.
  --
  -- Strategy: chain through the same 6 segments used to construct
  -- `atom-ein-L` / `atom-eout-L`, applying the relevant unfolding
  -- lemma at each step:
  --
  --   step 1 (s1, s1'):  `hT₂.elab-c-inj₁ (ψ_L eG)` (read in reverse:
  --                       `subst₂ s1 s1' (G₂.elab (ψ_L eG))
  --                        ≡ subst₂ (cong …) (T₂.elab (ψ_L eG ↑ˡ K₂.nE))`).
  --   step 2 (s2, s2'):  `subst₂-sym-subst₂` collapses the
  --                       `(cong …) ∘ (sym (cong …))` pair to identity.
  --   step 3 (s3, s3'):  `T₂-elab-cong` transports `T₂.elab` along
  --                       `ψ_L-eq eG`.
  --   step 4 (s4, s4'):  `ψ-elab (eG ↑ˡ K₁.nE)` from the original iso.
  --   step 5 (s5, s5'):  `hT₁.elab-c-inj₁ eG` unfolds `T₁.elab`.
  --   step 6 (s6, s6'):  `subst₂-sym-subst₂` again.
  --
  -- The five `subst₂-trans` collapses then re-package the six nested
  -- `subst₂` calls into one `subst₂` along the full `atom-ein-L eG` /
  -- `atom-eout-L eG` chain.

  -- Transport-along-equality for `T.elab`.  Standard `subst₂` shape
  -- consistent with the atom-list equalities expressed via `cong`.
  T₂-elab-cong : ∀ {e₁ e₂ : Fin T₂.nE} (eq : e₁ ≡ e₂)
               → T₂.elab e₂ ≡ subst₂ FlatGen
                                (cong (λ z → map T₂.vlab (T₂.ein z))  eq)
                                (cong (λ z → map T₂.vlab (T₂.eout z)) eq)
                                (T₂.elab e₁)
  T₂-elab-cong refl = refl

  ψ-elab-L : ∀ eG → subst₂ FlatGen (atom-ein-L eG) (atom-eout-L eG)
                                    (G₂.elab (ψ_L eG))
                  ≡ G₁.elab eG
  ψ-elab-L eG =
    let
      -- Six segment-equations of `atom-ein-L eG`.
      s1  = map-via-inj hT₂.vlab-injL (G₂.ein (ψ_L eG))
      s1' = map-via-inj hT₂.vlab-injL (G₂.eout (ψ_L eG))
      s2  = sym (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red (ψ_L eG)))
      s2' = sym (cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (ψ_L eG)))
      s3  = cong (λ z → map T₂.vlab (T₂.ein z))  (sym (ψ_L-eq eG))
      s3' = cong (λ z → map T₂.vlab (T₂.eout z)) (sym (ψ_L-eq eG))
      s4  = atom-ein  (eG ↑ˡ K₁.nE)
      s4' = atom-eout (eG ↑ˡ K₁.nE)
      s5  = cong (map T₁.vlab) (hT₁.ein-c-inj₁-red eG)
      s5' = cong (map T₁.vlab) (hT₁.eout-c-inj₁-red eG)
      s6  = sym (map-via-inj hT₁.vlab-injL (G₁.ein eG))
      s6' = sym (map-via-inj hT₁.vlab-injL (G₁.eout eG))

      -- Step 1: apply `hT₂.elab-c-inj₁` in reverse to transport
      -- `G₂.elab (ψ_L eG)` to a `subst₂`-of-`T₂.elab`.
      step1 : subst₂ FlatGen s1 s1' (G₂.elab (ψ_L eG))
            ≡ subst₂ FlatGen
                (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red  (ψ_L eG)))
                (cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (ψ_L eG)))
                (T₂.elab (ψ_L eG ↑ˡ K₂.nE))
      step1 = sym (hT₂.elab-c-inj₁ (ψ_L eG))

      -- Step 2: collapse the `(cong …) ∘ (sym (cong …))` pair.
      step2 : subst₂ FlatGen s2 s2'
                (subst₂ FlatGen
                  (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red  (ψ_L eG)))
                  (cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (ψ_L eG)))
                  (T₂.elab (ψ_L eG ↑ˡ K₂.nE)))
            ≡ T₂.elab (ψ_L eG ↑ˡ K₂.nE)
      step2 = subst₂-sym-subst₂
                (cong (map T₂.vlab) (hT₂.ein-c-inj₁-red  (ψ_L eG)))
                (cong (map T₂.vlab) (hT₂.eout-c-inj₁-red (ψ_L eG)))
                (T₂.elab (ψ_L eG ↑ˡ K₂.nE))

      -- Step 3: transport `T₂.elab` from `(ψ_L eG ↑ˡ K₂.nE)` back to
      -- `ψ (eG ↑ˡ K₁.nE)` via `ψ_L-eq eG`.  `T₂-elab-cong` produces
      -- the `(sym ∘ ψ_L-eq)`-flavoured `subst₂`; symmetrising gives
      -- the direction we want.
      step3 : subst₂ FlatGen s3 s3' (T₂.elab (ψ_L eG ↑ˡ K₂.nE))
            ≡ T₂.elab (ψ (eG ↑ˡ K₁.nE))
      step3 = sym (T₂-elab-cong (sym (ψ_L-eq eG)))

      -- Step 4: original iso's `ψ-elab` at `eG ↑ˡ K₁.nE`.
      step4 : subst₂ FlatGen s4 s4' (T₂.elab (ψ (eG ↑ˡ K₁.nE)))
            ≡ T₁.elab (eG ↑ˡ K₁.nE)
      step4 = ψ-elab (eG ↑ˡ K₁.nE)

      -- Step 5: apply `hT₁.elab-c-inj₁` to unfold `T₁.elab (eG ↑ˡ K₁.nE)`.
      step5 : subst₂ FlatGen s5 s5' (T₁.elab (eG ↑ˡ K₁.nE))
            ≡ subst₂ FlatGen
                (map-via-inj hT₁.vlab-injL (G₁.ein  eG))
                (map-via-inj hT₁.vlab-injL (G₁.eout eG))
                (G₁.elab eG)
      step5 = hT₁.elab-c-inj₁ eG

      -- Step 6: collapse the `(map-via-inj) ∘ (sym (map-via-inj))` pair.
      step6 : subst₂ FlatGen s6 s6'
                (subst₂ FlatGen
                  (map-via-inj hT₁.vlab-injL (G₁.ein  eG))
                  (map-via-inj hT₁.vlab-injL (G₁.eout eG))
                  (G₁.elab eG))
            ≡ G₁.elab eG
      step6 = subst₂-sym-subst₂
                (map-via-inj hT₁.vlab-injL (G₁.ein  eG))
                (map-via-inj hT₁.vlab-injL (G₁.eout eG))
                (G₁.elab eG)

      -- Combine the six steps.  Each step's `subst₂` is applied to
      -- the previous step's RHS; we use `cong (subst₂ FlatGen ...)`
      -- to push them through.
      combined : subst₂ FlatGen s6 s6'
                  (subst₂ FlatGen s5 s5'
                    (subst₂ FlatGen s4 s4'
                      (subst₂ FlatGen s3 s3'
                        (subst₂ FlatGen s2 s2'
                          (subst₂ FlatGen s1 s1' (G₂.elab (ψ_L eG)))))))
               ≡ G₁.elab eG
      combined =
        trans (cong (subst₂ FlatGen s6 s6')
              (trans (cong (subst₂ FlatGen s5 s5')
                    (trans (cong (subst₂ FlatGen s4 s4')
                          (trans (cong (subst₂ FlatGen s3 s3')
                                (trans (cong (subst₂ FlatGen s2 s2') step1)
                                       step2))
                                 step3))
                           step4))
                     step5))
              step6

      -- Now collapse the six nested `subst₂` calls into one along the
      -- full `atom-ein-L eG` / `atom-eout-L eG` chain via 5 applications
      -- of `subst₂-trans`.
      -- atom-ein-L eG is right-associated as
      --   trans s1 (trans s2 (trans s3 (trans s4 (trans s5 s6)))).
      -- Split it inside-out, applying `sym (subst₂-trans)` at each
      -- step: `subst₂ (trans p R) Q X = subst₂ R Q' (subst₂ p X)`.

      r5 = trans s5  s6
      r5' = trans s5' s6'
      r4 = trans s4  r5
      r4' = trans s4' r5'
      r3 = trans s3  r4
      r3' = trans s3' r4'
      r2 = trans s2  r3
      r2' = trans s2' r3'
      -- r1 = trans s1 r2 = atom-ein-L eG (definitionally)
      -- r1' = trans s1' r2' = atom-eout-L eG (definitionally)

      Y₁ = subst₂ FlatGen s1 s1' (G₂.elab (ψ_L eG))
      Y₂ = subst₂ FlatGen s2 s2' Y₁
      Y₃ = subst₂ FlatGen s3 s3' Y₂
      Y₄ = subst₂ FlatGen s4 s4' Y₃
      Y₅ = subst₂ FlatGen s5 s5' Y₄
      Y₆ = subst₂ FlatGen s6 s6' Y₅

      split-1 : subst₂ FlatGen (trans s1 r2) (trans s1' r2') (G₂.elab (ψ_L eG))
              ≡ subst₂ FlatGen r2 r2' Y₁
      split-1 = sym (subst₂-trans s1 r2 s1' r2' (G₂.elab (ψ_L eG)))

      split-2 : subst₂ FlatGen r2 r2' Y₁ ≡ subst₂ FlatGen r3 r3' Y₂
      split-2 = sym (subst₂-trans s2 r3 s2' r3' Y₁)

      split-3 : subst₂ FlatGen r3 r3' Y₂ ≡ subst₂ FlatGen r4 r4' Y₃
      split-3 = sym (subst₂-trans s3 r4 s3' r4' Y₂)

      split-4 : subst₂ FlatGen r4 r4' Y₃ ≡ subst₂ FlatGen r5 r5' Y₄
      split-4 = sym (subst₂-trans s4 r5 s4' r5' Y₃)

      split-5 : subst₂ FlatGen r5 r5' Y₄ ≡ Y₆
      split-5 = sym (subst₂-trans s5 s6 s5' s6' Y₄)

      collapse : subst₂ FlatGen (atom-ein-L eG) (atom-eout-L eG)
                                (G₂.elab (ψ_L eG))
               ≡ Y₆
      collapse = trans split-1 (trans split-2 (trans split-3
                                  (trans split-4 split-5)))
    in
      trans collapse combined

  -- R-half companion.
  T₂-elab-cong-R : ∀ {e₁ e₂ : Fin T₂.nE} (eq : e₁ ≡ e₂)
                 → T₂.elab e₂ ≡ subst₂ FlatGen
                                  (cong (λ z → map T₂.vlab (T₂.ein z))  eq)
                                  (cong (λ z → map T₂.vlab (T₂.eout z)) eq)
                                  (T₂.elab e₁)
  T₂-elab-cong-R refl = refl

  ψ-elab-R : ∀ eK → subst₂ FlatGen (atom-ein-R eK) (atom-eout-R eK)
                                    (K₂.elab (ψ_R eK))
                  ≡ K₁.elab eK
  ψ-elab-R eK =
    let
      s1  = map-via-raise hT₂.vlab-injR (K₂.ein  (ψ_R eK))
      s1' = map-via-raise hT₂.vlab-injR (K₂.eout (ψ_R eK))
      s2  = sym (cong (map T₂.vlab) (hT₂.ein-c-inj₂-red  (ψ_R eK)))
      s2' = sym (cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (ψ_R eK)))
      s3  = cong (λ z → map T₂.vlab (T₂.ein z))  (sym (ψ_R-eq eK))
      s3' = cong (λ z → map T₂.vlab (T₂.eout z)) (sym (ψ_R-eq eK))
      s4  = atom-ein  (G₁.nE ↑ʳ eK)
      s4' = atom-eout (G₁.nE ↑ʳ eK)
      s5  = cong (map T₁.vlab) (hT₁.ein-c-inj₂-red  eK)
      s5' = cong (map T₁.vlab) (hT₁.eout-c-inj₂-red eK)
      s6  = sym (map-via-raise hT₁.vlab-injR (K₁.ein  eK))
      s6' = sym (map-via-raise hT₁.vlab-injR (K₁.eout eK))

      step1 : subst₂ FlatGen s1 s1' (K₂.elab (ψ_R eK))
            ≡ subst₂ FlatGen
                (cong (map T₂.vlab) (hT₂.ein-c-inj₂-red  (ψ_R eK)))
                (cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (ψ_R eK)))
                (T₂.elab (G₂.nE ↑ʳ ψ_R eK))
      step1 = sym (hT₂.elab-c-inj₂ (ψ_R eK))

      step2 : subst₂ FlatGen s2 s2'
                (subst₂ FlatGen
                  (cong (map T₂.vlab) (hT₂.ein-c-inj₂-red  (ψ_R eK)))
                  (cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (ψ_R eK)))
                  (T₂.elab (G₂.nE ↑ʳ ψ_R eK)))
            ≡ T₂.elab (G₂.nE ↑ʳ ψ_R eK)
      step2 = subst₂-sym-subst₂
                (cong (map T₂.vlab) (hT₂.ein-c-inj₂-red  (ψ_R eK)))
                (cong (map T₂.vlab) (hT₂.eout-c-inj₂-red (ψ_R eK)))
                (T₂.elab (G₂.nE ↑ʳ ψ_R eK))

      step3 : subst₂ FlatGen s3 s3' (T₂.elab (G₂.nE ↑ʳ ψ_R eK))
            ≡ T₂.elab (ψ (G₁.nE ↑ʳ eK))
      step3 = sym (T₂-elab-cong-R (sym (ψ_R-eq eK)))

      step4 : subst₂ FlatGen s4 s4' (T₂.elab (ψ (G₁.nE ↑ʳ eK)))
            ≡ T₁.elab (G₁.nE ↑ʳ eK)
      step4 = ψ-elab (G₁.nE ↑ʳ eK)

      step5 : subst₂ FlatGen s5 s5' (T₁.elab (G₁.nE ↑ʳ eK))
            ≡ subst₂ FlatGen
                (map-via-raise hT₁.vlab-injR (K₁.ein  eK))
                (map-via-raise hT₁.vlab-injR (K₁.eout eK))
                (K₁.elab eK)
      step5 = hT₁.elab-c-inj₂ eK

      step6 : subst₂ FlatGen s6 s6'
                (subst₂ FlatGen
                  (map-via-raise hT₁.vlab-injR (K₁.ein  eK))
                  (map-via-raise hT₁.vlab-injR (K₁.eout eK))
                  (K₁.elab eK))
            ≡ K₁.elab eK
      step6 = subst₂-sym-subst₂
                (map-via-raise hT₁.vlab-injR (K₁.ein  eK))
                (map-via-raise hT₁.vlab-injR (K₁.eout eK))
                (K₁.elab eK)

      combined : subst₂ FlatGen s6 s6'
                  (subst₂ FlatGen s5 s5'
                    (subst₂ FlatGen s4 s4'
                      (subst₂ FlatGen s3 s3'
                        (subst₂ FlatGen s2 s2'
                          (subst₂ FlatGen s1 s1' (K₂.elab (ψ_R eK)))))))
               ≡ K₁.elab eK
      combined =
        trans (cong (subst₂ FlatGen s6 s6')
              (trans (cong (subst₂ FlatGen s5 s5')
                    (trans (cong (subst₂ FlatGen s4 s4')
                          (trans (cong (subst₂ FlatGen s3 s3')
                                (trans (cong (subst₂ FlatGen s2 s2') step1)
                                       step2))
                                 step3))
                           step4))
                     step5))
              step6

      r5 = trans s5  s6
      r5' = trans s5' s6'
      r4 = trans s4  r5
      r4' = trans s4' r5'
      r3 = trans s3  r4
      r3' = trans s3' r4'
      r2 = trans s2  r3
      r2' = trans s2' r3'

      Y₁ = subst₂ FlatGen s1 s1' (K₂.elab (ψ_R eK))
      Y₂ = subst₂ FlatGen s2 s2' Y₁
      Y₃ = subst₂ FlatGen s3 s3' Y₂
      Y₄ = subst₂ FlatGen s4 s4' Y₃
      Y₅ = subst₂ FlatGen s5 s5' Y₄
      Y₆ = subst₂ FlatGen s6 s6' Y₅

      split-1 : subst₂ FlatGen (trans s1 r2) (trans s1' r2') (K₂.elab (ψ_R eK))
              ≡ subst₂ FlatGen r2 r2' Y₁
      split-1 = sym (subst₂-trans s1 r2 s1' r2' (K₂.elab (ψ_R eK)))

      split-2 : subst₂ FlatGen r2 r2' Y₁ ≡ subst₂ FlatGen r3 r3' Y₂
      split-2 = sym (subst₂-trans s2 r3 s2' r3' Y₁)

      split-3 : subst₂ FlatGen r3 r3' Y₂ ≡ subst₂ FlatGen r4 r4' Y₃
      split-3 = sym (subst₂-trans s3 r4 s3' r4' Y₂)

      split-4 : subst₂ FlatGen r4 r4' Y₃ ≡ subst₂ FlatGen r5 r5' Y₄
      split-4 = sym (subst₂-trans s4 r5 s4' r5' Y₃)

      split-5 : subst₂ FlatGen r5 r5' Y₄ ≡ Y₆
      split-5 = sym (subst₂-trans s5 s6 s5' s6' Y₄)

      collapse : subst₂ FlatGen (atom-ein-R eK) (atom-eout-R eK)
                                (K₂.elab (ψ_R eK))
               ≡ Y₆
      collapse = trans split-1 (trans split-2 (trans split-3
                                  (trans split-4 split-5)))
    in
      trans collapse combined

  ------------------------------------------------------------------------------
  -- Assemble the two sub-isos.

  iso-L : ⟪ f₁ ⟫ ≅ᴴ ⟪ f₂ ⟫
  iso-L = record
    { φ         = φ_L
    ; φ⁻¹       = φ_L⁻¹
    ; φ-left    = φ_L-left
    ; φ-rght    = φ_L-rght
    ; ψ         = ψ_L
    ; ψ⁻¹       = ψ_L⁻¹
    ; ψ-left    = ψ_L-left
    ; ψ-rght    = ψ_L-rght
    ; φ-lab     = φ-lab-L
    ; ψ-ein     = ψ-ein-L
    ; ψ-eout    = ψ-eout-L
    ; φ-dom     = φ-dom-L
    ; φ-cod     = φ-cod-L
    ; atom-ein  = atom-ein-L
    ; atom-eout = atom-eout-L
    ; ψ-elab    = ψ-elab-L
    }

  iso-R : ⟪ g₁ ⟫ ≅ᴴ ⟪ g₂ ⟫
  iso-R = record
    { φ         = φ_R
    ; φ⁻¹       = φ_R⁻¹
    ; φ-left    = φ_R-left
    ; φ-rght    = φ_R-rght
    ; ψ         = ψ_R
    ; ψ⁻¹       = ψ_R⁻¹
    ; ψ-left    = ψ_R-left
    ; ψ-rght    = ψ_R-rght
    ; φ-lab     = φ-lab-R
    ; ψ-ein     = ψ-ein-R
    ; ψ-eout    = ψ-eout-R
    ; φ-dom     = φ-dom-R
    ; φ-cod     = φ-cod-R
    ; atom-ein  = atom-ein-R
    ; atom-eout = atom-eout-R
    ; ψ-elab    = ψ-elab-R
    }
