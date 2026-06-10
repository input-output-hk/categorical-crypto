{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The σ-EXTENSION of the wire-level solver: block crossings as TRANSPARENT
-- generators.
--
-- The variant-/⟦box⟧-parametric engine (`UntypedI`/`ReflectI`/`NormalizeI`/
-- `SolverCompareI`) is instantiated at `v = Symm` over the extended generator
-- family
--
--     data MorS : List X → List X → Set where
--       box   : Mor a b → MorS a b
--       cross : (a b : List X) → MorS (a ++ b) (b ++ a)
--
-- with the crossing interpreted as the GENUINE block braiding of the free
-- symmetric monoidal category, conjugated to flat wire coordinates:
--
--     ⟦box⟧S (cross a b) = merge b {a} ∘ σ ∘ split a {b}
--
-- STAGE A (this module, complete):
--   * `σσ-block`  : the block involution  ⟦cross b a⟧ ∘ ⟦cross a b⟧ ≈ id
--                   (split∘merge cancellation + the σ∘σ≈id axiom — NO
--                   σ-naturality);
--   * `pad-∘`/`pad-id`/`pad-resp` : pad functoriality, lifting it to padded
--                   layers (`pad-σσ`);
--   * `Decide.normσ` : the fuel-driven normalizer interleaving the existing
--                   disjoint-interchange bubble sort (crosses are ordinary
--                   boxes for interchange) with the NEW σσ-CANCEL move that
--                   deletes an adjacent inverse cross-pair;
--   * `Decide.decideσ?` : the decision entry mirroring the front-end's
--                   `decide?W` (reflect → normσ → ≟DiagU → chain), with
--                   `DecidableEquality` on the extended generators derived
--                   from the caller's `_≟G_` (no-K style, via first-order
--                   projection functions — never a refl-match at a forced
--                   `++`-composite index).
--
-- RANK CONVENTION: the interchange tiebreak for ambiguous (scalar-like)
-- pairs needs a rank on the extended generators.  Crosses get rank 0 and
-- boxes get `suc ∘ rank` of the caller's rank — crossings sort below all
-- boxes among mutually-fitting pairs, and the caller's relative order on
-- boxes is preserved.
--
-- STAGE B (the naturality-slide CORE, see the bottom module):
--   * `slide-core` : the block-level slide — a box firing inside the
--     b-block AFTER the crossing equals the box firing BEFORE the crossing
--     at its pre-cross position.  ONE σ-naturality axiom instance; stated
--     for an ARBITRARY block update `h : wires b ⇒ wires b'`, fully
--     cast-free.
--   * `slide-pad` : the same under an arbitrary `pad pq sq` frame — still
--     cast-free (grouped coordinates).
--   * the re-cleaning of the two grouped box-layers into genuine clean
--     DiagU pads (`slide-clean`) — this is where the `++`-assoc castW tax
--     lives (`rpad-rpad`, `rpad-liftW`, `liftW-fuse`).
--
-- Hole-free, postulate-free, --safe --without-K.
--------------------------------------------------------------------------------

module Categories.SolverSigma where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _<ᵇ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped using (module WireSig; module UntypedI)
open import Categories.SolverReflect using (module ReflectI)
open import Categories.SolverNormalize using (module NormalizeI)
open import Categories.SolverCompare using (module SolverCompareI)

module Sigma {X : Set} (_≟X_ : DecidableEquality X)
             (Mor : List X → List X → Set) where

  -- `Symm ≤ Symm` for instance search, so σ needs no explicit ⦃ v≤v ⦄.
  private instance
    S≤S : Symm ≤ Symm
    S≤S = v≤v

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  ------------------------------------------------------------------------
  -- The extended generator family: boxes + transparent block crossings.
  ------------------------------------------------------------------------
  data MorS : List X → List X → Set where
    box   : ∀ {a b} → Mor a b → MorS a b
    cross : (a b : List X) → MorS (a ++ b) (b ++ a)

  -- the wire signature at MorS: `wires`, the wire-level generator datatype
  -- `mor` (whose `box` wraps a MorS), and the ⟦box⟧-independent merge/split.
  -- Qualified (`WS.`) here — `open UntypedI` below re-exports the same
  -- WireSig surface publicly, and a second anonymous open would be
  -- ambiguous (module application is name-generative).
  private module WS = WireSig Symm {X} MorS
  open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var)
  open FreeMonoidalHelper.Mor Symm X WS.mor

  ------------------------------------------------------------------------
  -- The interpretation: boxes stay opaque generators; a crossing is the
  -- block braiding conjugated to flat wire coordinates.
  ------------------------------------------------------------------------
  ⟦box⟧S : ∀ {a b} → MorS a b → HomTerm (WS.wires a) (WS.wires b)
  ⟦box⟧S (box f)     = var (WS.box (box f))
  ⟦box⟧S (cross a b) = WS.merge b {a} ∘ σ ∘ WS.split a {b}

  -- the full diagram engine at (Symm, MorS, ⟦box⟧S), re-exported.
  open UntypedI Symm {X} MorS ⟦box⟧S public
  open ≈R

  ------------------------------------------------------------------------
  -- STAGE A1: the block involution.  σ-naturality is NOT needed — only
  -- split∘merge cancellation, σ∘σ≈id, and assoc/id algebra.
  ------------------------------------------------------------------------
  σσ-block : ∀ (a b : List X)
           → ⟦box⟧S (cross b a) ∘ ⟦box⟧S (cross a b) ≈Term id
  σσ-block a b = begin
    (merge a ∘ σ ∘ split b) ∘ (merge b ∘ σ ∘ split a)
      ≈⟨ assoc ⟩
    merge a ∘ ((σ ∘ split b) ∘ (merge b ∘ σ ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge a ∘ (σ ∘ (split b ∘ (merge b ∘ σ ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    merge a ∘ (σ ∘ ((split b ∘ merge b) ∘ (σ ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge b) ≈-Term-refl)) ⟩
    merge a ∘ (σ ∘ (id ∘ (σ ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
    merge a ∘ (σ ∘ (σ ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge a ∘ ((σ ∘ σ) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ∘σ≈id ≈-Term-refl) ⟩
    merge a ∘ (id ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    merge a ∘ split a
      ≈⟨ merge∘split a ⟩
    id ∎

  ------------------------------------------------------------------------
  -- STAGE A2: pad functoriality (missing from the engine), and the lift
  -- of the involution to padded layers.
  ------------------------------------------------------------------------

  rpad-resp : ∀ {a b} (suf : List X) {g g' : HomTerm (wires a) (wires b)}
            → g ≈Term g' → rpad suf g ≈Term rpad suf g'
  rpad-resp suf eq =
    ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ eq ≈-Term-refl) ≈-Term-refl)

  pad-resp : ∀ {a b} (pre suf : List X) {g g' : HomTerm (wires a) (wires b)}
           → g ≈Term g' → pad pre suf g ≈Term pad pre suf g'
  pad-resp []      suf eq = rpad-resp suf eq
  pad-resp (x ∷ p) suf eq = ⊗-resp-≈ ≈-Term-refl (pad-resp p suf eq)

  rpad-id : ∀ {a} (suf : List X) → rpad suf (id {wires a}) ≈Term id
  rpad-id {a} suf = begin
    merge a ∘ (id ⊗₁ id) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
    merge a ∘ (id ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
    merge a ∘ split a
      ≈⟨ merge∘split a ⟩
    id ∎

  pad-id : ∀ {a} (pre suf : List X) → pad pre suf (id {wires a}) ≈Term id
  pad-id []      suf = rpad-id suf
  pad-id (x ∷ p) suf =
    ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (pad-id p suf)) id⊗id≈id

  rpad-∘ : ∀ {a b c} (suf : List X)
             (g : HomTerm (wires b) (wires c)) (f : HomTerm (wires a) (wires b))
         → rpad suf (g ∘ f) ≈Term rpad suf g ∘ rpad suf f
  rpad-∘ {a} {b} {c} suf g f = begin
    merge c ∘ ((g ∘ f) ⊗₁ id) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ≈-Term-refl) ⟩
    merge c ∘ ((g ∘ f) ⊗₁ (id ∘ id)) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ⊗-∘-dist ≈-Term-refl) ⟩
    merge c ∘ ((g ⊗₁ id) ∘ (f ⊗₁ id)) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ≈-Term-refl) ⟩
    merge c ∘ ((g ⊗₁ id) ∘ (id ∘ (f ⊗₁ id))) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl
           (∘-resp-≈ (≈-Term-sym (split∘merge b)) ≈-Term-refl)) ≈-Term-refl) ⟩
    merge c ∘ ((g ⊗₁ id) ∘ ((split b ∘ merge b) ∘ (f ⊗₁ id))) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (∘-resp-≈ ≈-Term-refl assoc) ≈-Term-refl) ⟩
    merge c ∘ ((g ⊗₁ id) ∘ (split b ∘ (merge b ∘ (f ⊗₁ id)))) ∘ split a
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge c ∘ ((g ⊗₁ id) ∘ ((split b ∘ (merge b ∘ (f ⊗₁ id))) ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
    merge c ∘ ((g ⊗₁ id) ∘ (split b ∘ ((merge b ∘ (f ⊗₁ id)) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge c ∘ (((g ⊗₁ id) ∘ split b) ∘ ((merge b ∘ (f ⊗₁ id)) ∘ split a))
      ≈⟨ ≈-Term-sym assoc ⟩
    (merge c ∘ ((g ⊗₁ id) ∘ split b)) ∘ ((merge b ∘ (f ⊗₁ id)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    (merge c ∘ (g ⊗₁ id) ∘ split b) ∘ (merge b ∘ (f ⊗₁ id) ∘ split a) ∎

  pad-∘ : ∀ {a b c} (pre suf : List X)
            (g : HomTerm (wires b) (wires c)) (f : HomTerm (wires a) (wires b))
        → pad pre suf (g ∘ f) ≈Term pad pre suf g ∘ pad pre suf f
  pad-∘ []      suf g f = rpad-∘ suf g f
  pad-∘ (x ∷ p) suf g f = begin
    id ⊗₁ pad p suf (g ∘ f)
      ≈⟨ ⊗-resp-≈ ≈-Term-refl (pad-∘ p suf g f) ⟩
    id ⊗₁ (pad p suf g ∘ pad p suf f)
      ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) ≈-Term-refl ⟩
    (id ∘ id) ⊗₁ (pad p suf g ∘ pad p suf f)
      ≈⟨ ⊗-∘-dist ⟩
    id ⊗₁ pad p suf g ∘ id ⊗₁ pad p suf f ∎

  -- the padded involution: an adjacent inverse cross-pair at the SAME
  -- offsets is the identity.
  pad-σσ : ∀ (pre suf a b : List X)
         → pad pre suf (⟦box⟧S (cross b a)) ∘ pad pre suf (⟦box⟧S (cross a b))
           ≈Term id
  pad-σσ pre suf a b = begin
    pad pre suf (⟦box⟧S (cross b a)) ∘ pad pre suf (⟦box⟧S (cross a b))
      ≈⟨ pad-∘ pre suf (⟦box⟧S (cross b a)) (⟦box⟧S (cross a b)) ⟨
    pad pre suf (⟦box⟧S (cross b a) ∘ ⟦box⟧S (cross a b))
      ≈⟨ pad-resp pre suf (σσ-block a b) ⟩
    pad pre suf id
      ≈⟨ pad-id pre suf ⟩
    id ∎

  ------------------------------------------------------------------------
  -- The reflect / normalize / compare stack at (Symm, MorS, ⟦box⟧S).
  ------------------------------------------------------------------------
  open ReflectI Symm {X} _≟X_ MorS ⟦box⟧S public
  open NormalizeI Symm {X} _≟X_ MorS ⟦box⟧S using
    ( castW; castW-∘; castW-irr
    ; substDiagU; substDiagU-out; ⟦substDiagU⟧
    ; LeftFit; leftFit
    ; dInput; dSwapped; dInput-out; dSwapped-out; diagU-swap-soundD; domeq
    ; assocW-castW; assocW⁻-castW; liftW-castW; castW-∷
    ; castW-sym-r; castW-sym-r-flip; castW-cancelʳ
    ; module SortD )
  open SortD using (leftFit?)

  private module SCmp = SolverCompareI Symm {X} _≟X_ MorS ⟦box⟧S

  -- the caller-facing generator triples (on the UNDERLYING `Mor`).
  GenM : Set
  GenM = Σ[ a ∈ List X ] Σ[ b ∈ List X ] Mor a b

  ------------------------------------------------------------------------
  -- The decision module.  Parameters mirror the front-end's `Decide`: a
  -- decidable equality on the underlying generator triples and a rank
  -- tiebreak for ambiguous (mutually-fitting, scalar-like) pairs.
  ------------------------------------------------------------------------
  module Decide
    (_≟G_ : DecidableEquality GenM)
    (rank : GenM → ℕ)
    where

    private
      _≟L_ : DecidableEquality (List X)
      _≟L_ = ≡-dec _≟X_

    ------------------------------------------------------------------------
    -- Decidable equality on the EXTENDED generator triples, no-K style:
    -- the negative cases go through first-order projection functions
    -- (`tagS`/`boxPay`/`crossPay`), never a refl-match at the forced
    -- `++`-composite indices of `cross`.
    ------------------------------------------------------------------------

    private
      tagS : SCmp.Gen → Bool
      tagS (_ , _ , box _)     = true
      tagS (_ , _ , cross _ _) = false

      boxPay : SCmp.Gen → Maybe GenM
      boxPay (a , b , box f)     = just (a , b , f)
      boxPay (_ , _ , cross _ _) = nothing

      crossPay : SCmp.Gen → Maybe (List X × List X)
      crossPay (_ , _ , box _)     = nothing
      crossPay (_ , _ , cross a b) = just (a , b)

      true≢false : true ≡ false → ⊥
      true≢false ()

    _≟GS_ : DecidableEquality SCmp.Gen
    (a , b , box f) ≟GS (a' , b' , box g) with (a , b , f) ≟G (a' , b' , g)
    ... | yes refl = yes refl
    ... | no ¬p    = no λ e → ¬p (just-injective (cong boxPay e))
    (a , b , box f)     ≟GS (_ , _ , cross c d) = no λ e → true≢false (cong tagS e)
    (_ , _ , cross a b) ≟GS (a' , b' , box g)   = no λ e → true≢false (sym (cong tagS e))
    (_ , _ , cross a b) ≟GS (_ , _ , cross c d) with a ≟L c | b ≟L d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        =
          no λ e → ¬p (cong proj₁ (just-injective (cong crossPay e)))
    ... | yes _    | no ¬q    =
          no λ e → ¬q (cong proj₂ (just-injective (cong crossPay e)))

    open SCmp.Decide _≟GS_ using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

    -- RANK: crosses sort below all boxes among ambiguous pairs; the
    -- caller's relative order on boxes is preserved.
    rankS : ∀ {a b} → MorS a b → ℕ
    rankS (box {a} {b} f) = suc (rank (a , b , f))
    rankS (cross _ _)     = zero

    ------------------------------------------------------------------------
    -- The one-step oracle: σσ-CANCEL first, then disjoint interchange.
    -- (Mirrors the front-end `Decide`'s `SwapRes`/`go`/`fire`/`step?`
    -- architecture: the inner index is GENERALIZED to a variable `m`
    -- carried with a propositional wiring equality `meq`, discharged by
    -- the Hedberg UIP on wire lists — never matched.)
    ------------------------------------------------------------------------

    SwapRes : ∀ {n} → DiagU n → Set
    SwapRes {n} d = Σ[ d' ∈ DiagU n ] Σ[ oeq ∈ out d ≡ out d' ]
                      (castW oeq ∘ ⟦ d ⟧ ≈Term ⟦ d' ⟧)

    private
      castW-cancel : ∀ {u v} (e : u ≡ v) → castW (sym e) ∘ castW e ≈Term id
      castW-cancel refl = idˡ

      unwrapCast : ∀ {u v} {A} (e : u ≡ v)
                   {x : HomTerm A (wires u)} {y : HomTerm A (wires v)}
                 → castW e ∘ x ≈Term y → x ≈Term castW (sym e) ∘ y
      unwrapCast refl eq =
        ≈-Term-trans (≈-Term-sym idˡ) (≈-Term-trans eq (≈-Term-sym idˡ))

      coeCod'-as-castW : ∀ {n p q} (e : p ≡ q) (h : HomTerm (wires n) (wires p))
                       → coeCod' e h ≈Term castW e ∘ h
      coeCod'-as-castW refl h = ≈-Term-sym idˡ

      ------------------------------------------------------------------
      -- THE σσ-CANCEL FIRE.  On a recognised adjacent inverse cross-pair
      -- (same pre/suf, blocks reversed) BOTH layers are removed; the tail
      -- lives at the SAME input index, so no diagram transport is needed
      -- and the soundness is `pad-σσ` + assoc/id algebra.
      ------------------------------------------------------------------
      fireσ : ∀ (px sx a b : List X)
              (rest' : DiagU (px ++ ((a ++ b) ++ sx)))
            → SwapRes (px ▸ sx ∷ cross a b ⟨ px ▸ sx ∷ cross b a ⟨ rest' ⟩ ⟩)
      fireσ px sx a b rest' = rest' , refl , (begin
        castW refl ∘ ((⟦ rest' ⟧ ∘ P₂) ∘ P₁)
          ≈⟨ idˡ ⟩
        (⟦ rest' ⟧ ∘ P₂) ∘ P₁
          ≈⟨ assoc ⟩
        ⟦ rest' ⟧ ∘ (P₂ ∘ P₁)
          ≈⟨ ∘-resp-≈ ≈-Term-refl (pad-σσ px sx a b) ⟩
        ⟦ rest' ⟧ ∘ id
          ≈⟨ idʳ ⟩
        ⟦ rest' ⟧ ∎)
        where
          P₁ = pad px sx (⟦box⟧S (cross a b))
          P₂ = pad px sx (⟦box⟧S (cross b a))

      -- the σσ recogniser at the generalized inner index: fires exactly
      -- when the head layer is `cross a b` at (px,sx) and the next layer
      -- is `cross b a` at the SAME (px,sx).
      goσ : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
            {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
          → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      goσ px sx (box f)     rest meq = nothing
      goσ px sx (cross a b) ([]_ m) meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ {ay} {by} py sy (box f) rest') meq = nothing
      goσ px sx (cross a b) (_▸_∷_⟨_⟩ py sy (cross c d) rest') meq
        with px ≟L py | sx ≟L sy | c ≟L b | d ≟L a
      ... | yes refl | yes refl | yes refl | yes refl
            rewrite ≡-irrelevantL meq refl = just (fireσ px sx a b rest')
      ... | no _  | _     | _     | _     = nothing
      ... | yes _ | no _  | _     | _     = nothing
      ... | yes _ | yes _ | no _  | _     = nothing
      ... | yes _ | yes _ | yes _ | no _  = nothing

      ------------------------------------------------------------------
      -- The interchange fire (verbatim from the front-end `Decide`, at
      -- MorS): one genuine swap on a recognised out-of-order head pair.
      ------------------------------------------------------------------
      fire : ∀ {ax bx ay by} {px sx py sy : List X}
             {fx : MorS ax bx} {fy : MorS ay by}
             (fit : LeftFit px sx py sy fx fy)
             (rest' : DiagU (py ++ (by ++ sy)))
             (meq : px ++ (bx ++ sx) ≡ py ++ (ay ++ sy))
           → SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) (py ▸ sy ∷ fy ⟨ rest' ⟩) ⟩)
      fire {ax} {bx} {ay} {by} {fx = fx} {fy = fy}
           (leftFit P mid s refl refl refl refl) rest' meq
        rewrite ≡-irrelevantL meq (domeq P ay mid bx s)
        = d' , oeq , snd
        where
          fit' : LeftFit (P ++ (ay ++ mid)) s P (mid ++ (bx ++ s)) fx fy
          fit' = leftFit P mid s refl refl refl refl
          eᵒ = domeq P ay mid ax s
          dBody : DiagU ((P ++ (ay ++ mid)) ++ (ax ++ s))
          dBody = (P ++ (ay ++ mid)) ▸ s ∷ fx
                    ⟨ substDiagU (sym (domeq P ay mid bx s))
                        (P ▸ (mid ++ (bx ++ s)) ∷ fy ⟨ rest' ⟩) ⟩
          dIn = dInput fit' rest'
          dSw = dSwapped fit' rest'
          d' : DiagU ((P ++ (ay ++ mid)) ++ (ax ++ s))
          d' = substDiagU (sym eᵒ) dSw
          e₁ = sym (substDiagU-out eᵒ dBody)
          q  = trans (dInput-out fit' rest') (sym (dSwapped-out fit' rest'))
          e₃ = sym (substDiagU-out (sym eᵒ) dSw)
          oeq = trans e₁ (trans q e₃)
          snd : castW oeq ∘ ⟦ dBody ⟧ ≈Term ⟦ d' ⟧
          snd = begin
            castW oeq ∘ ⟦ dBody ⟧
              ≈⟨ ∘-resp-≈ (castW-irr oeq (trans (trans e₁ q) e₃)) ≈-Term-refl ⟩
            castW (trans (trans e₁ q) e₃) ∘ ⟦ dBody ⟧
              ≈⟨ ∘-resp-≈ (castW-∘ (trans e₁ q) e₃) ≈-Term-refl ⟨
            (castW e₃ ∘ castW (trans e₁ q)) ∘ ⟦ dBody ⟧
              ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (castW-∘ e₁ q)) ≈-Term-refl ⟨
            (castW e₃ ∘ (castW q ∘ castW e₁)) ∘ ⟦ dBody ⟧
              ≈⟨ assoc ⟩
            castW e₃ ∘ ((castW q ∘ castW e₁) ∘ ⟦ dBody ⟧)
              ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
            castW e₃ ∘ (castW q ∘ (castW e₁ ∘ ⟦ dBody ⟧))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (⟦substDiagU⟧ eᵒ dBody)) ⟨
            castW e₃ ∘ (castW q ∘ (⟦ dIn ⟧ ∘ castW eᵒ))
              ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
            castW e₃ ∘ ((castW q ∘ ⟦ dIn ⟧) ∘ castW eᵒ)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (diagU-swap-soundD fit' rest') ≈-Term-refl) ⟩
            castW e₃ ∘ (⟦ dSw ⟧ ∘ castW eᵒ)
              ≈⟨ ≈-Term-sym assoc ⟩
            (castW e₃ ∘ ⟦ dSw ⟧) ∘ castW eᵒ
              ≈⟨ ∘-resp-≈ (⟦substDiagU⟧ (sym eᵒ) dSw) ≈-Term-refl ⟨
            (⟦ d' ⟧ ∘ castW (sym eᵒ)) ∘ castW eᵒ
              ≈⟨ assoc ⟩
            ⟦ d' ⟧ ∘ (castW (sym eᵒ) ∘ castW eᵒ)
              ≈⟨ ∘-resp-≈ ≈-Term-refl (castW-cancel eᵒ) ⟩
            ⟦ d' ⟧ ∘ id
              ≈⟨ idʳ ⟩
            ⟦ d' ⟧ ∎

      -- a fit is AMBIGUOUS when the reverse pair would also fit; such
      -- pairs are ordered by `rankS` instead.
      ambiguous? : List X → List X → List X → Bool
      ambiguous? [] [] [] = true
      ambiguous? _  _  _  = false

      -- the interchange recogniser at the generalized inner index.
      goSwap : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
               {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
             → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      goSwap px sx fx ([]_ m) meq = nothing
      goSwap {ax} {bx} px sx fx (_▸_∷_⟨_⟩ {ay} {by} py sy fy rest') meq
        with leftFit? px sx py sy fx fy
      ... | nothing  = nothing
      ... | just fit
        with ambiguous? ax by (LeftFit.mid fit) | rankS fy <ᵇ rankS fx
      ...   | false | _     = just (fire fit rest' meq)
      ...   | true  | true  = just (fire fit rest' meq)
      ...   | true  | false = nothing

      -- the combined per-position oracle: cancel first, then interchange.
      go : ∀ {ax bx} (px sx : List X) (fx : MorS ax bx)
           {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
         → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      go px sx fx rest meq with goσ px sx fx rest meq
      ... | just r  = just r
      ... | nothing = goSwap px sx fx rest meq

      -- lift a tail swap-result under a layer.
      lift∷ : ∀ {a b} (px sx : List X) (fx : MorS a b)
              {rest rest' : DiagU (px ++ (b ++ sx))}
              (oeq : out rest ≡ out rest')
            → castW oeq ∘ ⟦ rest ⟧ ≈Term ⟦ rest' ⟧
            → castW oeq ∘ ⟦ px ▸ sx ∷ fx ⟨ rest ⟩ ⟧
              ≈Term ⟦ px ▸ sx ∷ fx ⟨ rest' ⟩ ⟧
      lift∷ px sx fx oeq snd =
        ≈-Term-trans (≈-Term-sym assoc) (∘-resp-≈ snd ≈-Term-refl)

      -- compose two swap-results (cast functoriality).
      swapTrans : ∀ {n} {d d' d'' : DiagU n}
                  (oeq : out d ≡ out d') (oeq' : out d' ≡ out d'')
                → castW oeq  ∘ ⟦ d  ⟧ ≈Term ⟦ d'  ⟧
                → castW oeq' ∘ ⟦ d' ⟧ ≈Term ⟦ d'' ⟧
                → castW (trans oeq oeq') ∘ ⟦ d ⟧ ≈Term ⟦ d'' ⟧
      swapTrans {d = d} {d' = d'} {d'' = d''} oeq oeq' p q = begin
        castW (trans oeq oeq') ∘ ⟦ d ⟧
          ≈⟨ ∘-resp-≈ (castW-∘ oeq oeq') ≈-Term-refl ⟨
        (castW oeq' ∘ castW oeq) ∘ ⟦ d ⟧
          ≈⟨ assoc ⟩
        castW oeq' ∘ (castW oeq ∘ ⟦ d ⟧)
          ≈⟨ ∘-resp-≈ ≈-Term-refl p ⟩
        castW oeq' ∘ ⟦ d' ⟧
          ≈⟨ q ⟩
        ⟦ d'' ⟧ ∎

    -- one cancel-or-swap at the FIRST applicable position.
    stepσ? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    stepσ? ([]_ n) = nothing
    stepσ? (px ▸ sx ∷ fx ⟨ rest ⟩) with go px sx fx rest refl
    ... | just r  = just r
    ... | nothing with stepσ? rest
    ...   | nothing                  = nothing
    ...   | just (rest' , oeq , snd) =
            just (px ▸ sx ∷ fx ⟨ rest' ⟩ , oeq , lift∷ px sx fx oeq snd)

    -- fuel-bounded driver: fire the first applicable move, repeat.
    normσFuel : ∀ {n} → ℕ → (d : DiagU n) → SwapRes d
    normσFuel zero    d = d , refl , idˡ
    normσFuel (suc k) d with stepσ? d
    ... | nothing               = d , refl , idˡ
    ... | just (d' , oeq , snd) with normσFuel k d'
    ...   | (d'' , oeq' , snd') =
            d'' , trans oeq oeq' , swapTrans oeq oeq' snd snd'

    depth : ∀ {n} → DiagU n → ℕ
    depth ([]_ n)            = zero
    depth (_ ▸ _ ∷ _ ⟨ d ⟩) = suc (depth d)

    -- budget: a cancellation shrinks the diagram (so at most depth/2 of
    -- them), and each shrunken phase needs at most depth² bubble swaps —
    -- depth³ + depth² + depth + 1 over-approximates the total.
    normσ : ∀ {n} (d : DiagU n) → SwapRes d
    normσ d = normσFuel (suc (k * k * k + k * k + k)) d
      where k = depth d

    ------------------------------------------------------------------------
    -- The decision entry, mirroring the front-end's `decide?W`:
    -- reflect → normσ → ≟DiagU → chain the soundness witnesses.
    ------------------------------------------------------------------------
    decideσ? : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decideσ? {n} {m} f g with normσ (reflect f) | normσ (reflect g)
    ... | (df' , oeqf , sndf) | (dg' , oeqg , sndg) with df' ≟DiagU dg'
    ...   | no  _  = nothing
    ...   | yes eq = just (chain (≈NF⇒≡ eq))
      where
        half : ∀ (t : WTerm n m) (d' : DiagU n) (oeq : out (reflect t) ≡ out d')
             → castW oeq ∘ ⟦ reflect t ⟧ ≈Term ⟦ d' ⟧
             → embed t ≈Term castW (trans (sym oeq) (out-reflect t)) ∘ ⟦ d' ⟧
        half t d' oeq snd = begin
          embed t
            ≈⟨ reflect-sound boxSound t ⟨
          coeCod' (out-reflect t) ⟦ reflect t ⟧
            ≈⟨ coeCod'-as-castW (out-reflect t) ⟦ reflect t ⟧ ⟩
          castW (out-reflect t) ∘ ⟦ reflect t ⟧
            ≈⟨ ∘-resp-≈ ≈-Term-refl (unwrapCast oeq snd) ⟩
          castW (out-reflect t) ∘ (castW (sym oeq) ∘ ⟦ d' ⟧)
            ≈⟨ ≈-Term-sym assoc ⟩
          (castW (out-reflect t) ∘ castW (sym oeq)) ∘ ⟦ d' ⟧
            ≈⟨ ∘-resp-≈ (castW-∘ (sym oeq) (out-reflect t)) ≈-Term-refl ⟩
          castW (trans (sym oeq) (out-reflect t)) ∘ ⟦ d' ⟧ ∎

        chain : df' ≡ dg' → embed f ≈Term embed g
        chain deq = begin
          embed f
            ≈⟨ half f df' oeqf sndf ⟩
          castW (trans (sym oeqf) (out-reflect f)) ∘ ⟦ df' ⟧
            ≈⟨ step deq ⟩
          castW (trans (sym oeqg) (out-reflect g)) ∘ ⟦ dg' ⟧
            ≈⟨ half g dg' oeqg sndg ⟨
          embed g ∎
          where
            step : df' ≡ dg'
                 → castW (trans (sym oeqf) (out-reflect f)) ∘ ⟦ df' ⟧
                   ≈Term castW (trans (sym oeqg) (out-reflect g)) ∘ ⟦ dg' ⟧
            step refl = ∘-resp-≈ (castW-irr _ _) ≈-Term-refl

    -- the computing hit-witness (normalizes to ⊤ exactly on a hit).
    IsJust : ∀ {a} {A : Set a} → Maybe A → Set
    IsJust (just _) = ⊤
    IsJust nothing  = ⊥

    private
      extract : ∀ {a} {A : Set a} (x : Maybe A) → IsJust x → A
      extract (just a) _ = a

    -- reference-style entry point.
    solveσ! : ∀ {n m} (f g : WTerm n m)
              {hit : IsJust (decideσ? f g)} → embed f ≈Term embed g
    solveσ! f g {hit} = extract (decideσ? f g) hit

  ------------------------------------------------------------------------
  -- STAGE B: the naturality-slide CORE.
  --
  -- The slide configuration: a box fires AFTER a crossing, inside the
  -- b-block of its image; sliding it BEFORE the crossing moves it to its
  -- pre-cross position and updates the crossing's b-block (c ↦ d).  The
  -- categorical content is ONE instance of the braiding-naturality axiom
  -- σ∘[f⊗g]≈[g⊗f]∘σ at the pair (id_{wires a}, the-block-update); we
  -- state it for an ARBITRARY block update `h : wires b ⇒ wires b'` (the
  -- DiagU instance is `h = pad p₁ s₁ ⟦f⟧` with b = p₁ ++ (c ++ s₁)),
  -- which keeps the BLOCK-level statement and its `pad pq sq` lift fully
  -- CAST-FREE.  The `++`-assoc castW tax appears only in the final
  -- re-cleaning of the two grouped box-layers into genuine clean DiagU
  -- pads (`slide-clean` below).
  ------------------------------------------------------------------------

  -- THE BLOCK SLIDE: the box (update h, inside the b-block) fires after
  -- the crossing  ≈  it fires before the crossing at the pre-cross
  -- position.  ONE σ-naturality instance + split/merge cancellation.
  slide-core : ∀ (a : List X) {b b' : List X} (h : HomTerm (wires b) (wires b'))
             → ⟦box⟧S (cross a b') ∘ liftW a h
               ≈Term rpad a h ∘ ⟦box⟧S (cross a b)
  slide-core a {b} {b'} h = begin
    (merge b' ∘ σ ∘ split a) ∘ liftW a h
      ≈⟨ ∘-resp-≈ ≈-Term-refl (liftW-merge a h) ⟩
    (merge b' ∘ σ ∘ split a) ∘ (merge a ∘ (id ⊗₁ h) ∘ split a)
      ≈⟨ assoc ⟩
    merge b' ∘ ((σ ∘ split a) ∘ (merge a ∘ (id ⊗₁ h) ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge b' ∘ (σ ∘ (split a ∘ (merge a ∘ (id ⊗₁ h) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    merge b' ∘ (σ ∘ ((split a ∘ merge a) ∘ ((id ⊗₁ h) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge a) ≈-Term-refl)) ⟩
    merge b' ∘ (σ ∘ (id ∘ ((id ⊗₁ h) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
    merge b' ∘ (σ ∘ ((id ⊗₁ h) ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge b' ∘ ((σ ∘ (id ⊗₁ h)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ ≈-Term-refl) ⟩
    merge b' ∘ (((h ⊗₁ id) ∘ σ) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge b' ∘ ((h ⊗₁ id) ∘ (σ ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⟩
    merge b' ∘ ((h ⊗₁ id) ∘ (id ∘ (σ ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge b) ≈-Term-refl)) ⟨
    merge b' ∘ ((h ⊗₁ id) ∘ ((split b ∘ merge b) ∘ (σ ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
    merge b' ∘ ((h ⊗₁ id) ∘ (split b ∘ (merge b ∘ (σ ∘ split a))))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge b' ∘ (((h ⊗₁ id) ∘ split b) ∘ (merge b ∘ (σ ∘ split a)))
      ≈⟨ ≈-Term-sym assoc ⟩
    (merge b' ∘ (h ⊗₁ id) ∘ split b) ∘ (merge b ∘ σ ∘ split a) ∎

  -- the symmetric a-block case (update g : wires a ⇒ wires a').
  slide-core-a : ∀ (b : List X) {a a' : List X} (g : HomTerm (wires a) (wires a'))
               → ⟦box⟧S (cross a' b) ∘ rpad b g
                 ≈Term liftW b g ∘ ⟦box⟧S (cross a b)
  slide-core-a b {a} {a'} g = begin
    (merge b ∘ σ ∘ split a') ∘ (merge a' ∘ (g ⊗₁ id) ∘ split a)
      ≈⟨ assoc ⟩
    merge b ∘ ((σ ∘ split a') ∘ (merge a' ∘ (g ⊗₁ id) ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge b ∘ (σ ∘ (split a' ∘ (merge a' ∘ (g ⊗₁ id) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    merge b ∘ (σ ∘ ((split a' ∘ merge a') ∘ ((g ⊗₁ id) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge a') ≈-Term-refl)) ⟩
    merge b ∘ (σ ∘ (id ∘ ((g ⊗₁ id) ∘ split a)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
    merge b ∘ (σ ∘ ((g ⊗₁ id) ∘ split a))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
    merge b ∘ ((σ ∘ (g ⊗₁ id)) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ σ∘[f⊗g]≈[g⊗f]∘σ ≈-Term-refl) ⟩
    merge b ∘ (((id ⊗₁ g) ∘ σ) ∘ split a)
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    merge b ∘ ((id ⊗₁ g) ∘ (σ ∘ split a))
      ≈⟨ ≈-Term-sym assoc ⟩
    (merge b ∘ (id ⊗₁ g)) ∘ (σ ∘ split a)
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym idʳ)) ≈-Term-refl ⟩
    (merge b ∘ ((id ⊗₁ g) ∘ id)) ∘ (σ ∘ split a)
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym (split∘merge b)))) ≈-Term-refl ⟩
    (merge b ∘ ((id ⊗₁ g) ∘ (split b ∘ merge b))) ∘ (σ ∘ split a)
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ≈-Term-refl ⟩
    (merge b ∘ (((id ⊗₁ g) ∘ split b) ∘ merge b)) ∘ (σ ∘ split a)
      ≈⟨ ∘-resp-≈ (≈-Term-sym assoc) ≈-Term-refl ⟩
    ((merge b ∘ ((id ⊗₁ g) ∘ split b)) ∘ merge b) ∘ (σ ∘ split a)
      ≈⟨ assoc ⟩
    (merge b ∘ ((id ⊗₁ g) ∘ split b)) ∘ (merge b ∘ (σ ∘ split a))
      ≈⟨ ∘-resp-≈ (∘-resp-≈ ≈-Term-refl ≈-Term-refl) ≈-Term-refl ⟩
    (merge b ∘ (id ⊗₁ g) ∘ split b) ∘ (merge b ∘ σ ∘ split a)
      ≈⟨ ∘-resp-≈ (≈-Term-sym (liftW-merge b g)) ≈-Term-refl ⟩
    liftW b g ∘ (merge b ∘ σ ∘ split a) ∎

  -- THE PADDED SLIDE (grouped coordinates): the same equation under an
  -- arbitrary `pad pq sq` frame — still fully cast-free, via the Stage-A
  -- pad functoriality.
  slide-pad : ∀ (pq sq a : List X) {b b'} (h : HomTerm (wires b) (wires b'))
            → pad pq sq (⟦box⟧S (cross a b')) ∘ pad pq sq (liftW a h)
              ≈Term pad pq sq (rpad a h) ∘ pad pq sq (⟦box⟧S (cross a b))
  slide-pad pq sq a {b} {b'} h = begin
    pad pq sq (⟦box⟧S (cross a b')) ∘ pad pq sq (liftW a h)
      ≈⟨ pad-∘ pq sq (⟦box⟧S (cross a b')) (liftW a h) ⟨
    pad pq sq (⟦box⟧S (cross a b') ∘ liftW a h)
      ≈⟨ pad-resp pq sq (slide-core a h) ⟩
    pad pq sq (rpad a h ∘ ⟦box⟧S (cross a b))
      ≈⟨ pad-∘ pq sq (rpad a h) (⟦box⟧S (cross a b)) ⟩
    pad pq sq (rpad a h) ∘ pad pq sq (⟦box⟧S (cross a b)) ∎

  ------------------------------------------------------------------------
  -- STAGE B, re-cleaning: the two GROUPED box-layers of the slide
  -- (`pad pq sq (rpad a h)` / `pad pq sq (liftW a h)` with the concrete
  -- block update `h = pad p₁ s₁ G`) re-expressed as genuine clean DiagU
  -- pads at the composite offsets, conjugated by `++`-assoc index casts.
  -- This is where the castW tax lives.  The interface is the SANDWICH
  -- relation `Sand eC eD Y Z` (= Y ≈ castW eC ∘ Z ∘ castW eD), with the
  -- J-style combinators below; the two genuinely new coherence lemmas are
  -- `rpad-liftW` (suffix-pad past a prefix-lift, by induction on the
  -- prefix + α-naturality) and `rpad-rpad` (suffix-pad fusion, via
  -- `merge-assoc` and inverse algebra).
  ------------------------------------------------------------------------

  -- the conjugation-by-index-casts relation.
  Sand : ∀ {p q w t : List X} (eC : t ≡ q) (eD : p ≡ w)
       → HomTerm (wires p) (wires q) → HomTerm (wires w) (wires t) → Set
  Sand eC eD Y Z = Y ≈Term castW eC ∘ Z ∘ castW eD

  private
    sand-trans : ∀ {p q w t w' t'}
                 {Y : HomTerm (wires p) (wires q)}
                 {Z : HomTerm (wires w) (wires t)}
                 {V : HomTerm (wires w') (wires t')}
                 {eC : t ≡ q} {eD : p ≡ w} {fC : t' ≡ t} {fD : w ≡ w'}
               → Sand eC eD Y Z → Sand fC fD Z V
               → Sand (trans fC eC) (trans eD fD) Y V
    sand-trans {eC = refl} {refl} {refl} {refl} hy hz =
      ≈-Term-trans hy (≈-Term-trans idˡ (≈-Term-trans idʳ hz))

    sand-flip : ∀ {p q w t}
                {Y : HomTerm (wires p) (wires q)}
                {Z : HomTerm (wires w) (wires t)}
                {eC : t ≡ q} {eD : p ≡ w}
              → Sand eC eD Y Z → Sand (sym eC) (sym eD) Z Y
    sand-flip {eC = refl} {refl} hy =
      ≈-Term-trans (≈-Term-sym (≈-Term-trans hy (≈-Term-trans idˡ idʳ)))
                   (≈-Term-sym (≈-Term-trans idˡ idʳ))

    sand-irr : ∀ {p q w t}
               {Y : HomTerm (wires p) (wires q)}
               {Z : HomTerm (wires w) (wires t)}
               {eC eC' : t ≡ q} {eD eD' : p ≡ w}
             → Sand eC eD Y Z → Sand eC' eD' Y Z
    sand-irr {eC = eC} {eC'} {eD} {eD'} s =
      ≈-Term-trans s (∘-resp-≈ (castW-irr eC eC')
                                (∘-resp-≈ ≈-Term-refl (castW-irr eD eD')))

    sand-≈ˡ : ∀ {p q w t}
              {Y' Y : HomTerm (wires p) (wires q)}
              {Z : HomTerm (wires w) (wires t)}
              {eC : t ≡ q} {eD : p ≡ w}
            → Y' ≈Term Y → Sand eC eD Y Z → Sand eC eD Y' Z
    sand-≈ˡ e s = ≈-Term-trans e s

    sand-mid : ∀ {p q w t}
               {Y : HomTerm (wires p) (wires q)}
               {Z Z' : HomTerm (wires w) (wires t)}
               {eC : t ≡ q} {eD : p ≡ w}
             → Sand eC eD Y Z → Z ≈Term Z' → Sand eC eD Y Z'
    sand-mid s e =
      ≈-Term-trans s (∘-resp-≈ ≈-Term-refl (∘-resp-≈ e ≈-Term-refl))

    -- prefix-lift of a sandwich.
    liftW-sand : ∀ (p : List X) {pp q w t}
                 {Y : HomTerm (wires pp) (wires q)}
                 {Z : HomTerm (wires w) (wires t)}
                 {eC : t ≡ q} {eD : pp ≡ w}
               → Sand eC eD Y Z
               → Sand (cong (p ++_) eC) (cong (p ++_) eD) (liftW p Y) (liftW p Z)
    liftW-sand p {Y = Y} {Z = Z} {eC = eC} {eD = eD} s = begin
      liftW p Y
        ≈⟨ liftW-resp p s ⟩
      liftW p (castW eC ∘ Z ∘ castW eD)
        ≈⟨ liftW-∘ p (castW eC) (Z ∘ castW eD) ⟩
      liftW p (castW eC) ∘ liftW p (Z ∘ castW eD)
        ≈⟨ ∘-resp-≈ (liftW-castW p eC) (liftW-∘ p Z (castW eD)) ⟩
      castW (cong (p ++_) eC) ∘ (liftW p Z ∘ liftW p (castW eD))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (liftW-castW p eD)) ⟩
      castW (cong (p ++_) eC) ∘ (liftW p Z ∘ castW (cong (p ++_) eD)) ∎

    -- prefix-lift fusion, as a sandwich (assocW towers collapse to castW).
    liftW-fuse : ∀ (x m : List X) {u v} (W : HomTerm (wires u) (wires v))
               → Sand (++-assoc x m v) (sym (++-assoc x m u))
                      (liftW x (liftW m W)) (liftW (x ++ m) W)
    liftW-fuse x m {u} {v} W = begin
      liftW x (liftW m W)
        ≈⟨ liftW-assoc' x m W ⟩
      assocW⁻ x m v ∘ liftW (x ++ m) W ∘ assocW x m u
        ≈⟨ ∘-resp-≈ (assocW⁻-castW x m v)
                    (∘-resp-≈ ≈-Term-refl (assocW-castW x m u)) ⟩
      castW (++-assoc x m v) ∘ liftW (x ++ m) W ∘ castW (sym (++-assoc x m u)) ∎

    -- a suffix-pad slides under a single prefix wire (α-naturality).
    rpad-⊗-peel : ∀ (sq : List X) (x : X) {n n'} (V : HomTerm (wires n) (wires n'))
                → rpad sq (id {Var x} ⊗₁ V) ≈Term id {Var x} ⊗₁ rpad sq V
    rpad-⊗-peel sq x {n} {n'} V = begin
      (id ⊗₁ merge n' ∘ α⇒) ∘ ((id ⊗₁ V) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ split n)
        ≈⟨ assoc ⟩
      id ⊗₁ merge n' ∘ (α⇒ ∘ (((id ⊗₁ V) ⊗₁ id) ∘ (α⇐ ∘ id ⊗₁ split n)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      id ⊗₁ merge n' ∘ ((α⇒ ∘ ((id ⊗₁ V) ⊗₁ id)) ∘ (α⇐ ∘ id ⊗₁ split n))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ α-comm ≈-Term-refl) ⟩
      id ⊗₁ merge n' ∘ ((id ⊗₁ (V ⊗₁ id) ∘ α⇒) ∘ (α⇐ ∘ id ⊗₁ split n))
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      id ⊗₁ merge n' ∘ (id ⊗₁ (V ⊗₁ id) ∘ (α⇒ ∘ (α⇐ ∘ id ⊗₁ split n)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      id ⊗₁ merge n' ∘ (id ⊗₁ (V ⊗₁ id) ∘ ((α⇒ ∘ α⇐) ∘ id ⊗₁ split n))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl)) ⟩
      id ⊗₁ merge n' ∘ (id ⊗₁ (V ⊗₁ id) ∘ (id ∘ id ⊗₁ split n))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
      id ⊗₁ merge n' ∘ (id ⊗₁ (V ⊗₁ id) ∘ id ⊗₁ split n)
        ≈⟨ id⊗-∘3 (merge n') (V ⊗₁ id) (split n) ⟩
      id ⊗₁ (merge n' ∘ (V ⊗₁ id) ∘ split n) ∎

    -- NEW COHERENCE 1: a suffix-pad past a prefix-lift.
    rpad-liftW : ∀ (sq p : List X) {u v} (W : HomTerm (wires u) (wires v))
               → Sand (sym (++-assoc p v sq)) (++-assoc p u sq)
                      (rpad sq (liftW p W)) (liftW p (rpad sq W))
    rpad-liftW sq [] {u} {v} W = ≈-Term-sym (≈-Term-trans idˡ idʳ)
    rpad-liftW sq (x ∷ p) {u} {v} W = begin
      rpad sq (liftW (x ∷ p) W)
        ≈⟨ rpad-⊗-peel sq x (liftW p W) ⟩
      id ⊗₁ rpad sq (liftW p W)
        ≈⟨ ⊗-resp-≈ ≈-Term-refl (rpad-liftW sq p W) ⟩
      id ⊗₁ (castW (sym (++-assoc p v sq)) ∘ liftW p (rpad sq W) ∘ castW (++-assoc p u sq))
        ≈⟨ id⊗-∘3 _ _ _ ⟨
      id ⊗₁ castW (sym (++-assoc p v sq))
        ∘ id ⊗₁ liftW p (rpad sq W)
        ∘ id ⊗₁ castW (++-assoc p u sq)
        ≈⟨ ∘-resp-≈ (castW-∷ (sym (++-assoc p v sq)))
                    (∘-resp-≈ ≈-Term-refl (castW-∷ (++-assoc p u sq))) ⟩
      castW (cong (x ∷_) (sym (++-assoc p v sq)))
        ∘ liftW (x ∷ p) (rpad sq W)
        ∘ castW (cong (x ∷_) (++-assoc p u sq))
        ≈⟨ ∘-resp-≈ (castW-irr _ _) (∘-resp-≈ ≈-Term-refl (castW-irr _ _)) ⟩
      castW (sym (++-assoc (x ∷ p) v sq))
        ∘ liftW (x ∷ p) (rpad sq W)
        ∘ castW (++-assoc (x ∷ p) u sq) ∎

    -- coeCA (ReflectI's arbitrary-domain codomain coercion) is a castW.
    coeCA-as-castW : ∀ {A} {p q : List X} (e : p ≡ q) (h : HomTerm A (wires p))
                   → coeCA e h ≈Term castW e ∘ h
    coeCA-as-castW refl h = ≈-Term-sym idˡ

    -- merge-assoc, rearranged:  castW e ∘ A ≈ B  (grouped ↦ nested form).
    mmB : ∀ (w s sq : List X)
        → castW (++-assoc w s sq) ∘ (merge (w ++ s) {sq} ∘ (merge w {s} ⊗₁ id {wires sq}))
          ≈Term merge w {s ++ sq} ∘ (id ⊗₁ merge s {sq}) ∘ α⇒
    mmB w s sq =
      ≈-Term-trans (≈-Term-sym (coeCA-as-castW (++-assoc w s sq) _))
                   (≈-Term-sym (merge-assoc w s sq))

    -- the merge-merge fusion:  A ≈ castW (sym e) ∘ B.
    mm : ∀ (w s sq : List X)
       → merge (w ++ s) {sq} ∘ (merge w {s} ⊗₁ id {wires sq})
         ≈Term castW (sym (++-assoc w s sq))
             ∘ (merge w {s ++ sq} ∘ (id ⊗₁ merge s {sq}) ∘ α⇒)
    mm w s sq = begin
      merge (w ++ s) ∘ (merge w ⊗₁ id)
        ≈⟨ idˡ ⟨
      id ∘ (merge (w ++ s) ∘ (merge w ⊗₁ id))
        ≈⟨ ∘-resp-≈ (castW-sym-r (++-assoc w s sq)) ≈-Term-refl ⟨
      (castW (sym (++-assoc w s sq)) ∘ castW (++-assoc w s sq))
        ∘ (merge (w ++ s) ∘ (merge w ⊗₁ id))
        ≈⟨ assoc ⟩
      castW (sym (++-assoc w s sq))
        ∘ (castW (++-assoc w s sq) ∘ (merge (w ++ s) ∘ (merge w ⊗₁ id)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (mmB w s sq) ⟩
      castW (sym (++-assoc w s sq)) ∘ (merge w ∘ (id ⊗₁ merge s) ∘ α⇒) ∎

    -- the grouped merge pair is split-inverse...
    ms-iso : ∀ (w s sq : List X)
           → (merge (w ++ s) {sq} ∘ (merge w {s} ⊗₁ id {wires sq}))
             ∘ ((split w {s} ⊗₁ id {wires sq}) ∘ split (w ++ s) {sq}) ≈Term id
    ms-iso w s sq = begin
      (merge (w ++ s) ∘ (merge w ⊗₁ id)) ∘ ((split w ⊗₁ id) ∘ split (w ++ s))
        ≈⟨ assoc ⟩
      merge (w ++ s) ∘ ((merge w ⊗₁ id) ∘ ((split w ⊗₁ id) ∘ split (w ++ s)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      merge (w ++ s) ∘ (((merge w ⊗₁ id) ∘ (split w ⊗₁ id)) ∘ split (w ++ s))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
      merge (w ++ s) ∘ (((merge w ∘ split w) ⊗₁ (id ∘ id)) ∘ split (w ++ s))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ (merge∘split w) idˡ) ≈-Term-refl) ⟩
      merge (w ++ s) ∘ ((id ⊗₁ id) ∘ split (w ++ s))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
      merge (w ++ s) ∘ (id ∘ split (w ++ s))
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
      merge (w ++ s) ∘ split (w ++ s)
        ≈⟨ merge∘split (w ++ s) ⟩
      id ∎

    -- ...and so is the nested pair (the other inverse order).
    gb-iso : ∀ (w s sq : List X)
           → (α⇐ ∘ (id {wires w} ⊗₁ split s {sq}) ∘ split w {s ++ sq})
             ∘ (merge w {s ++ sq} ∘ (id ⊗₁ merge s {sq}) ∘ α⇒) ≈Term id
    gb-iso w s sq = begin
      (α⇐ ∘ (id ⊗₁ split s) ∘ split w) ∘ (merge w ∘ (id ⊗₁ merge s) ∘ α⇒)
        ≈⟨ assoc ⟩
      α⇐ ∘ (((id ⊗₁ split s) ∘ split w) ∘ (merge w ∘ (id ⊗₁ merge s) ∘ α⇒))
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      α⇐ ∘ ((id ⊗₁ split s) ∘ (split w ∘ (merge w ∘ (id ⊗₁ merge s) ∘ α⇒)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      α⇐ ∘ ((id ⊗₁ split s) ∘ ((split w ∘ merge w) ∘ ((id ⊗₁ merge s) ∘ α⇒)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (split∘merge w) ≈-Term-refl)) ⟩
      α⇐ ∘ ((id ⊗₁ split s) ∘ (id ∘ ((id ⊗₁ merge s) ∘ α⇒)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
      α⇐ ∘ ((id ⊗₁ split s) ∘ ((id ⊗₁ merge s) ∘ α⇒))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      α⇐ ∘ (((id ⊗₁ split s) ∘ (id ⊗₁ merge s)) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
      α⇐ ∘ (((id ∘ id) ⊗₁ (split s ∘ merge s)) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idˡ (split∘merge s)) ≈-Term-refl) ⟩
      α⇐ ∘ ((id ⊗₁ id) ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ id⊗id≈id ≈-Term-refl) ⟩
      α⇐ ∘ (id ∘ α⇒)
        ≈⟨ ∘-resp-≈ ≈-Term-refl idˡ ⟩
      α⇐ ∘ α⇒
        ≈⟨ α⇐∘α⇒≈id ⟩
      id ∎

    -- the split-split fusion (derived from `mm` by inverse algebra).
    ss : ∀ (w s sq : List X)
       → (split w {s} ⊗₁ id {wires sq}) ∘ split (w ++ s) {sq}
         ≈Term (α⇐ ∘ (id ⊗₁ split s {sq}) ∘ split w {s ++ sq})
             ∘ castW (++-assoc w s sq)
    ss w s sq = begin
      (split w ⊗₁ id) ∘ split (w ++ s)
        ≈⟨ idˡ ⟨
      id ∘ ((split w ⊗₁ id) ∘ split (w ++ s))
        ≈⟨ ∘-resp-≈ (gb-iso w s sq) ≈-Term-refl ⟨
      ((α⇐ ∘ (id ⊗₁ split s) ∘ split w) ∘ (merge w ∘ (id ⊗₁ merge s) ∘ α⇒))
        ∘ ((split w ⊗₁ id) ∘ split (w ++ s))
        ≈⟨ assoc ⟩
      (α⇐ ∘ (id ⊗₁ split s) ∘ split w)
        ∘ ((merge w ∘ (id ⊗₁ merge s) ∘ α⇒) ∘ ((split w ⊗₁ id) ∘ split (w ++ s)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (mmB w s sq) ≈-Term-refl) ⟨
      (α⇐ ∘ (id ⊗₁ split s) ∘ split w)
        ∘ ((castW (++-assoc w s sq) ∘ (merge (w ++ s) ∘ (merge w ⊗₁ id)))
           ∘ ((split w ⊗₁ id) ∘ split (w ++ s)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      (α⇐ ∘ (id ⊗₁ split s) ∘ split w)
        ∘ (castW (++-assoc w s sq)
           ∘ ((merge (w ++ s) ∘ (merge w ⊗₁ id)) ∘ ((split w ⊗₁ id) ∘ split (w ++ s))))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (ms-iso w s sq)) ⟩
      (α⇐ ∘ (id ⊗₁ split s) ∘ split w) ∘ (castW (++-assoc w s sq) ∘ id)
        ≈⟨ ∘-resp-≈ ≈-Term-refl idʳ ⟩
      (α⇐ ∘ (id ⊗₁ split s) ∘ split w) ∘ castW (++-assoc w s sq) ∎

    -- tensoring a composite with a single idle block.
    ⊗id-∘ : ∀ {A B C Z : ObjTerm} (P : HomTerm B C) (Q : HomTerm A B)
          → (P ∘ Q) ⊗₁ id {Z} ≈Term (P ⊗₁ id) ∘ (Q ⊗₁ id)
    ⊗id-∘ P Q = ≈-Term-trans (⊗-resp-≈ ≈-Term-refl (≈-Term-sym idˡ)) ⊗-∘-dist

    -- the nested middle collapses to the fused suffix-pad.
    midColl : ∀ (s sq : List X) {u v} (W : HomTerm (wires u) (wires v))
            → (merge v {s ++ sq} ∘ (id ⊗₁ merge s {sq}) ∘ α⇒)
              ∘ (((W ⊗₁ id {wires s}) ⊗₁ id {wires sq})
                 ∘ (α⇐ ∘ (id ⊗₁ split s {sq}) ∘ split u {s ++ sq}))
              ≈Term rpad (s ++ sq) W
    midColl s sq {u} {v} W = begin
      (merge v ∘ (id ⊗₁ merge s) ∘ α⇒)
        ∘ (((W ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u))
        ≈⟨ assoc ⟩
      merge v ∘ (((id ⊗₁ merge s) ∘ α⇒)
        ∘ (((W ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      merge v ∘ ((id ⊗₁ merge s)
        ∘ (α⇒ ∘ (((W ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u))))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      merge v ∘ ((id ⊗₁ merge s)
        ∘ ((α⇒ ∘ ((W ⊗₁ id) ⊗₁ id)) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α-comm ≈-Term-refl)) ⟩
      merge v ∘ ((id ⊗₁ merge s)
        ∘ ((W ⊗₁ id ⊗₁ id ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl assoc) ⟩
      merge v ∘ ((id ⊗₁ merge s)
        ∘ ((W ⊗₁ id ⊗₁ id) ∘ (α⇒ ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u))))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc))) ⟩
      merge v ∘ ((id ⊗₁ merge s)
        ∘ ((W ⊗₁ id ⊗₁ id) ∘ ((α⇒ ∘ α⇐) ∘ ((id ⊗₁ split s) ∘ split u))))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl
             (∘-resp-≈ ≈-Term-refl (∘-resp-≈ α⇒∘α⇐≈id ≈-Term-refl))) ⟩
      merge v ∘ ((id ⊗₁ merge s)
        ∘ ((W ⊗₁ id ⊗₁ id) ∘ (id ∘ ((id ⊗₁ split s) ∘ split u))))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ)) ⟩
      merge v ∘ ((id ⊗₁ merge s) ∘ ((W ⊗₁ id ⊗₁ id) ∘ ((id ⊗₁ split s) ∘ split u)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      merge v ∘ (((id ⊗₁ merge s) ∘ (W ⊗₁ id ⊗₁ id)) ∘ ((id ⊗₁ split s) ∘ split u))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
      merge v ∘ (((id ∘ W) ⊗₁ (merge s ∘ id ⊗₁ id)) ∘ ((id ⊗₁ split s) ∘ split u))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈
             (⊗-resp-≈ idˡ (≈-Term-trans (∘-resp-≈ ≈-Term-refl id⊗id≈id) idʳ))
             ≈-Term-refl) ⟩
      merge v ∘ ((W ⊗₁ merge s) ∘ ((id ⊗₁ split s) ∘ split u))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      merge v ∘ (((W ⊗₁ merge s) ∘ (id ⊗₁ split s)) ∘ split u)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (≈-Term-sym ⊗-∘-dist) ≈-Term-refl) ⟩
      merge v ∘ (((W ∘ id) ⊗₁ (merge s ∘ split s)) ∘ split u)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (⊗-resp-≈ idʳ (merge∘split s)) ≈-Term-refl) ⟩
      merge v ∘ ((W ⊗₁ id) ∘ split u) ∎

    -- NEW COHERENCE 2: suffix-pad fusion.
    rpad-rpad : ∀ (s sq : List X) {u v} (W : HomTerm (wires u) (wires v))
              → Sand (sym (++-assoc v s sq)) (++-assoc u s sq)
                     (rpad sq (rpad s W)) (rpad (s ++ sq) W)
    rpad-rpad s sq {u} {v} W = begin
      merge (v ++ s) ∘ (rpad s W ⊗₁ id) ∘ split (u ++ s)
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ expand ≈-Term-refl) ⟩
      merge (v ++ s)
        ∘ (((merge v ⊗₁ id) ∘ ((W ⊗₁ id) ⊗₁ id) ∘ (split u ⊗₁ id)) ∘ split (u ++ s))
        ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
      merge (v ++ s)
        ∘ ((merge v ⊗₁ id) ∘ ((((W ⊗₁ id) ⊗₁ id) ∘ (split u ⊗₁ id)) ∘ split (u ++ s)))
        ≈⟨ ≈-Term-sym assoc ⟩
      (merge (v ++ s) ∘ (merge v ⊗₁ id))
        ∘ ((((W ⊗₁ id) ⊗₁ id) ∘ (split u ⊗₁ id)) ∘ split (u ++ s))
        ≈⟨ ∘-resp-≈ (mm v s sq) assoc ⟩
      (castW (sym (++-assoc v s sq)) ∘ (merge v ∘ (id ⊗₁ merge s) ∘ α⇒))
        ∘ (((W ⊗₁ id) ⊗₁ id) ∘ ((split u ⊗₁ id) ∘ split (u ++ s)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (ss u s sq)) ⟩
      (castW (sym (++-assoc v s sq)) ∘ (merge v ∘ (id ⊗₁ merge s) ∘ α⇒))
        ∘ (((W ⊗₁ id) ⊗₁ id)
           ∘ ((α⇐ ∘ (id ⊗₁ split s) ∘ split u) ∘ castW (++-assoc u s sq)))
        ≈⟨ assoc ⟩
      castW (sym (++-assoc v s sq))
        ∘ ((merge v ∘ (id ⊗₁ merge s) ∘ α⇒)
           ∘ (((W ⊗₁ id) ⊗₁ id)
              ∘ ((α⇐ ∘ (id ⊗₁ split s) ∘ split u) ∘ castW (++-assoc u s sq))))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
      castW (sym (++-assoc v s sq))
        ∘ ((merge v ∘ (id ⊗₁ merge s) ∘ α⇒)
           ∘ ((((W ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u))
              ∘ castW (++-assoc u s sq)))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc) ⟩
      castW (sym (++-assoc v s sq))
        ∘ (((merge v ∘ (id ⊗₁ merge s) ∘ α⇒)
            ∘ (((W ⊗₁ id) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ split s) ∘ split u)))
           ∘ castW (++-assoc u s sq))
        ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ (midColl s sq W) ≈-Term-refl) ⟩
      castW (sym (++-assoc v s sq)) ∘ (rpad (s ++ sq) W ∘ castW (++-assoc u s sq)) ∎
      where
        expand : rpad s W ⊗₁ id {wires sq}
               ≈Term (merge v ⊗₁ id) ∘ ((W ⊗₁ id) ⊗₁ id) ∘ (split u ⊗₁ id)
        expand = begin
          (merge v ∘ (W ⊗₁ id) ∘ split u) ⊗₁ id
            ≈⟨ ⊗id-∘ (merge v) ((W ⊗₁ id) ∘ split u) ⟩
          (merge v ⊗₁ id) ∘ (((W ⊗₁ id) ∘ split u) ⊗₁ id)
            ≈⟨ ∘-resp-≈ ≈-Term-refl (⊗id-∘ (W ⊗₁ id) (split u)) ⟩
          (merge v ⊗₁ id) ∘ (((W ⊗₁ id) ⊗₁ id) ∘ (split u ⊗₁ id)) ∎

  ------------------------------------------------------------------------
  -- THE TWO RE-CLEANINGS.  With the concrete block update `h = pad p₁ s₁
  -- G` (G generic — the DiagU instance is `G = ⟦box⟧S (box f)`), the two
  -- grouped box-layers of the slide are genuine clean DiagU pads at the
  -- composite offsets, conjugated by `++`-assoc casts.  Stated with the
  -- index equalities ∀-quantified (any proofs work, by Hedberg UIP).
  ------------------------------------------------------------------------

  -- the SLID box layer (box before the crossing, at offset pq++(a++p₁)).
  padBoxSlid : ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
               (eC : (pq ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sq))
                   ≡ pq ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sq))
               (eD : pq ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sq)
                   ≡ (pq ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sq)))
             → pad pq sq (liftW a (pad p₁ s₁ G))
               ≈Term castW eC ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G ∘ castW eD
  padBoxSlid pq sq a p₁ s₁ {u} {v} G eC eD = sand-irr SF
    where
      R = rpad (s₁ ++ sq) G
      S4 = rpad-rpad s₁ sq G
      S3 = sand-≈ˡ (rpad-resp sq (pad≡liftW p₁ s₁ G)) (rpad-liftW sq p₁ (rpad s₁ G))
      S3' = sand-trans S3 (liftW-sand p₁ S4)
      S2 = rpad-liftW sq a (pad p₁ s₁ G)
      S2' = sand-trans S2 (liftW-sand a S3')
      S2'' = sand-trans S2' (liftW-fuse a p₁ R)
      S1 = sand-≈ˡ (pad≡liftW pq sq (liftW a (pad p₁ s₁ G))) (liftW-sand pq S2'')
      S0 = sand-trans S1 (liftW-fuse pq (a ++ p₁) R)
      SF = sand-mid S0 (≈-Term-sym (pad≡liftW (pq ++ (a ++ p₁)) (s₁ ++ sq) G))

  -- the INPUT-order box layer (box after the crossing, inside the b-image
  -- at offset pq++p₁).
  padBoxIn : ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
             (eC : (pq ++ p₁) ++ (v ++ (s₁ ++ (a ++ sq)))
                 ≡ pq ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sq))
             (eD : pq ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sq)
                 ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (a ++ sq))))
           → pad pq sq (rpad a (pad p₁ s₁ G))
             ≈Term castW eC ∘ pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G ∘ castW eD
  padBoxIn pq sq a p₁ s₁ {u} {v} G eC eD = sand-irr TF
    where
      R = rpad (s₁ ++ (a ++ sq)) G
      T4 = rpad-rpad s₁ (a ++ sq) G
      T3 = sand-≈ˡ (rpad-resp (a ++ sq) (pad≡liftW p₁ s₁ G))
                   (rpad-liftW (a ++ sq) p₁ (rpad s₁ G))
      T3' = sand-trans T3 (liftW-sand p₁ T4)
      T2 = rpad-rpad a sq (pad p₁ s₁ G)
      T2' = sand-trans T2 T3'
      T1 = sand-≈ˡ (pad≡liftW pq sq (rpad a (pad p₁ s₁ G))) (liftW-sand pq T2')
      T0 = sand-trans T1 (liftW-fuse pq p₁ R)
      TF = sand-mid T0 (≈-Term-sym (pad≡liftW (pq ++ p₁) (s₁ ++ (a ++ sq)) G))

  ------------------------------------------------------------------------
  -- THE ASSEMBLED CLEAN SLIDE.  Both box-layers are genuine clean DiagU
  -- pads; the four index casts are exactly the ones forced by the
  -- `++`-assoc gaps (any proofs of those equalities work).  The input
  -- order (crossing first, then the box inside its b-image) equals the
  -- slid order (box first at its pre-cross position, then the crossing
  -- with the updated b-block u ↦ v).
  ------------------------------------------------------------------------
  slide-clean :
    ∀ (pq sq a p₁ s₁ : List X) {u v} (G : HomTerm (wires u) (wires v))
      (e₁ : pq ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (u ++ (s₁ ++ (a ++ sq))))
      (e₂ : pq ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (v ++ (s₁ ++ (a ++ sq))))
      (e₃ : (pq ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sq))
          ≡ pq ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sq))
      (e₄ : pq ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sq)
          ≡ (pq ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sq)))
    → pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G
        ∘ castW e₁
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (u ++ s₁))))
      ≈Term castW e₂
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (v ++ s₁))))
        ∘ castW e₃
        ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G
        ∘ castW e₄
  slide-clean pq sq a p₁ s₁ {u} {v} G e₁ e₂ e₃ e₄ = begin
    padIn ∘ (castW e₁ ∘ Cab)
      ≈⟨ ∘-resp-≈ flipβ ≈-Term-refl ⟩
    (castW (sym (sym e₂)) ∘ (Gβ ∘ castW (sym e₁))) ∘ (castW e₁ ∘ Cab)
      ≈⟨ assoc ⟩
    castW (sym (sym e₂)) ∘ ((Gβ ∘ castW (sym e₁)) ∘ (castW e₁ ∘ Cab))
      ≈⟨ ∘-resp-≈ ≈-Term-refl assoc ⟩
    castW (sym (sym e₂)) ∘ (Gβ ∘ (castW (sym e₁) ∘ (castW e₁ ∘ Cab)))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (≈-Term-sym assoc)) ⟩
    castW (sym (sym e₂)) ∘ (Gβ ∘ ((castW (sym e₁) ∘ castW e₁) ∘ Cab))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl (∘-resp-≈ (castW-sym-r e₁) ≈-Term-refl)) ⟩
    castW (sym (sym e₂)) ∘ (Gβ ∘ (id ∘ Cab))
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl idˡ) ⟩
    castW (sym (sym e₂)) ∘ (Gβ ∘ Cab)
      ≈⟨ ∘-resp-≈ (castW-irr _ e₂) (≈-Term-sym (slide-pad pq sq a hᵇ)) ⟩
    castW e₂ ∘ (Cab' ∘ Gα)
      ≈⟨ ∘-resp-≈ ≈-Term-refl (∘-resp-≈ ≈-Term-refl
           (padBoxSlid pq sq a p₁ s₁ G e₃ e₄)) ⟩
    castW e₂ ∘ (Cab' ∘ (castW e₃ ∘ padSlid ∘ castW e₄)) ∎
    where
      hᵇ      = pad p₁ s₁ G
      Cab     = pad pq sq (⟦box⟧S (cross a (p₁ ++ (u ++ s₁))))
      Cab'    = pad pq sq (⟦box⟧S (cross a (p₁ ++ (v ++ s₁))))
      padIn   = pad (pq ++ p₁) (s₁ ++ (a ++ sq)) G
      padSlid = pad (pq ++ (a ++ p₁)) (s₁ ++ sq) G
      Gβ      = pad pq sq (rpad a hᵇ)
      Gα      = pad pq sq (liftW a hᵇ)
      flipβ : padIn ≈Term castW (sym (sym e₂)) ∘ Gβ ∘ castW (sym e₁)
      flipβ = sand-flip (padBoxIn pq sq a p₁ s₁ G (sym e₂) e₁)

  -- the DiagU instance: the block update is a genuine BOX `f : Mor c d`
  -- (`G = ⟦box⟧S (box f)`), i.e. the input order `cross a (p₁++(c++s₁))`
  -- then `box f` at offset pq++p₁ slides to `box f` at offset
  -- pq++(a++p₁) then `cross a (p₁++(d++s₁))`.
  slide-clean-box :
    ∀ (pq sq a p₁ s₁ : List X) {c d} (f : Mor c d)
      (e₁ : pq ++ (((p₁ ++ (c ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (c ++ (s₁ ++ (a ++ sq))))
      (e₂ : pq ++ (((p₁ ++ (d ++ s₁)) ++ a) ++ sq)
          ≡ (pq ++ p₁) ++ (d ++ (s₁ ++ (a ++ sq))))
      (e₃ : (pq ++ (a ++ p₁)) ++ (d ++ (s₁ ++ sq))
          ≡ pq ++ ((a ++ (p₁ ++ (d ++ s₁))) ++ sq))
      (e₄ : pq ++ ((a ++ (p₁ ++ (c ++ s₁))) ++ sq)
          ≡ (pq ++ (a ++ p₁)) ++ (c ++ (s₁ ++ sq)))
    → pad (pq ++ p₁) (s₁ ++ (a ++ sq)) (⟦box⟧S (box f))
        ∘ castW e₁
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (c ++ s₁))))
      ≈Term castW e₂
        ∘ pad pq sq (⟦box⟧S (cross a (p₁ ++ (d ++ s₁))))
        ∘ castW e₃
        ∘ pad (pq ++ (a ++ p₁)) (s₁ ++ sq) (⟦box⟧S (box f))
        ∘ castW e₄
  slide-clean-box pq sq a p₁ s₁ f = slide-clean pq sq a p₁ s₁ (⟦box⟧S (box f))

--------------------------------------------------------------------------------
-- TESTS: a concrete signature over ℕ-labelled wires.  Three 1-wire boxes
-- (two on wire colour 0 — distinguishable only by `_≟G2_`/rank — and one on
-- colour 2).  Machine-checked:
--   (i)   a σσ-cancellation hit (adjacent inverse cross-pair deletes), both
--         at the head and below a box layer;
--   (ii)  disjoint cross-box interchange (the crossing participates in the
--         bubble sort like an ordinary box);
--   (iii) negative cases (distinct boxes; a non-cancelling diagram).
--------------------------------------------------------------------------------
module SigmaTests where

  open import Data.Nat using (ℕ)
  open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_)

  data Gen2 : List ℕ → List ℕ → Set where
    kbox  : Gen2 (0 ∷ []) (0 ∷ [])
    k2box : Gen2 (0 ∷ []) (0 ∷ [])
    mbox  : Gen2 (2 ∷ []) (2 ∷ [])

  open Sigma _≟ℕ_ Gen2

  private
    _≟G2_ : DecidableEquality GenM
    (_ , _ , kbox)  ≟G2 (_ , _ , kbox)  = yes refl
    (_ , _ , kbox)  ≟G2 (_ , _ , k2box) = no λ ()
    (_ , _ , kbox)  ≟G2 (_ , _ , mbox)  = no λ ()
    (_ , _ , k2box) ≟G2 (_ , _ , kbox)  = no λ ()
    (_ , _ , k2box) ≟G2 (_ , _ , k2box) = yes refl
    (_ , _ , k2box) ≟G2 (_ , _ , mbox)  = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , kbox)  = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , k2box) = no λ ()
    (_ , _ , mbox)  ≟G2 (_ , _ , mbox)  = yes refl

    rank2 : GenM → ℕ
    rank2 (_ , _ , kbox)  = 0
    rank2 (_ , _ , k2box) = 1
    rank2 (_ , _ , mbox)  = 2

  open Decide _≟G2_ rank2

  ------------------------------------------------------------------------
  -- (i) σσ-cancellation.
  ------------------------------------------------------------------------
  w01 : List ℕ
  w01 = 0 ∷ 1 ∷ []

  -- cross then its inverse  ≈  id.
  tCancelL tCancelR : WTerm w01 w01
  tCancelL = boxʷ (cross (1 ∷ []) (0 ∷ [])) ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
  tCancelR = idʷ

  testCancel : IsJust (decideσ? tCancelL tCancelR)
  testCancel = tt

  -- the same pair fires below a leading box layer.
  tCancelDeepL tCancelDeepR : WTerm w01 w01
  tCancelDeepL = boxʷ (cross (1 ∷ []) (0 ∷ []))
              ∘ʷ boxʷ (cross (0 ∷ []) (1 ∷ []))
              ∘ʷ (boxʷ (box kbox) ⊗ʷ idʷ {1 ∷ []})
  tCancelDeepR = boxʷ (box kbox) ⊗ʷ idʷ {1 ∷ []}

  testCancelDeep : IsJust (decideσ? tCancelDeepL tCancelDeepR)
  testCancelDeep = tt

  ------------------------------------------------------------------------
  -- (ii) disjoint cross-box interchange: the crossing (wires 0-1) and the
  -- box (wire 2) commute — decided by the existing bubble sort, with the
  -- crossing as an ordinary layer.
  ------------------------------------------------------------------------
  w012 : List ℕ
  w012 = 0 ∷ 1 ∷ 2 ∷ []

  layerCross : WTerm w012 (1 ∷ 0 ∷ 2 ∷ [])
  layerCross = boxʷ (cross (0 ∷ []) (1 ∷ [])) ⊗ʷ idʷ {2 ∷ []}

  layerBoxPre : WTerm w012 w012
  layerBoxPre = idʷ {0 ∷ 1 ∷ []} ⊗ʷ boxʷ (box mbox)

  layerBoxPost : WTerm (1 ∷ 0 ∷ 2 ∷ []) (1 ∷ 0 ∷ 2 ∷ [])
  layerBoxPost = idʷ {1 ∷ 0 ∷ []} ⊗ʷ boxʷ (box mbox)

  tIntL tIntR : WTerm w012 (1 ∷ 0 ∷ 2 ∷ [])
  tIntL = layerCross ∘ʷ layerBoxPre     -- box (offset 2) first, then cross
  tIntR = layerBoxPost ∘ʷ layerCross    -- cross first, then box

  testInterchange : IsJust (decideσ? tIntL tIntR)
  testInterchange = tt

  ------------------------------------------------------------------------
  -- (iii) negative cases: every `just` is a real proof, and these are
  -- genuinely not decided (distinct generators / non-cancelling pair).
  ------------------------------------------------------------------------
  testNegBoxes : decideσ? (boxʷ (box kbox)) (boxʷ (box k2box)) ≡ nothing
  testNegBoxes = refl

  testNegCancel : decideσ? tCancelL tCancelDeepR ≡ nothing
  testNegCancel = refl

  ------------------------------------------------------------------------
  -- Stage-B litmus: the clean naturality slide instantiates at concrete
  -- offsets (kbox slides past `cross [1] [0]` from its post-cross to its
  -- pre-cross position), with all four `++`-assoc index casts `refl`.
  ------------------------------------------------------------------------
  litSlide : _
  litSlide = slide-clean-box [] [] (1 ∷ []) [] [] kbox refl refl refl refl
