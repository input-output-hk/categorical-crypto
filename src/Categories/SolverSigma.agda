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
