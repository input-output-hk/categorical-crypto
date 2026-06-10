{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The SYMMETRIC solver front-end: `solveMorσ!`.
--
-- The Mon front-end (`Categories.SolverFrontend`) decides clean monoidal
-- goals between ObjTerm-arity generators by reflecting through the
-- wire-level engine.  This module is its `Symm` mirror over the σ-EXTENDED
-- wire engine (`Categories.SolverSigma`): the front-end term language is
-- `FreeMonoidalHelper.Mor Symm X GenF`'s `HomTerm` — WITH the braiding σ —
-- and the wire level is `Sigma`'s `MorS` family (opaque boxes + transparent
-- block crossings), whose driver `decideσ?` normalizes by σσ-cancellation,
-- the two naturality SLIDES and disjoint interchange.
--
-- Structure (most of it copies the Mon front-end verbatim, `Mon → Symm`):
--
--   * `reflectF σ {A}{B} = boxʷ (cross (flatten A) (flatten B))` —
--     CAST-FREE, since `flatten (A ⊗₀ B) ≡ flatten A ++ flatten B` holds
--     definitionally;
--   * `inj` (wire-level free category → front-end free category) gains the
--     σ constructor (mapped to the front-end σ) and — for TOTALITY — a
--     `var (box (cross a b))` case mapped to the σ-composite
--     `mergeF b ∘ σ ∘ splitF a`.  That case is UNREACHABLE from
--     `embed ∘ reflectF` (`embed (boxʷ (cross a b))` unfolds to
--     `⟦box⟧S (cross a b)`, which is already structural material + σ, never
--     a `var`), so only its well-typedness matters;
--   * `inj-resp-≈` gains the three σ-axiom cases (σ∘σ≈id, σ-naturality,
--     hexagon — each maps to the same F-axiom);
--   * `bridgeF` gains ONE new case: for σ the goal reduces — after
--     `splitF ∘ mergeF` cancellation — to braiding naturality at the pair
--     (flat⇒ A , flat⇒ B), i.e. the σ∘[f⊗g]≈[g⊗f]∘σ axiom;
--   * `Decide` wraps the σ-engine's `decideσ?` (the slide-capable driver);
--     `Into` takes a target MONOIDAL category TOGETHER WITH a `Symmetric`
--     structure on it, and `WithGen.solveMorσ!` transports a decided
--     front-end equation along the free functor — definitionally, so the
--     equation's two sides read in the target's own vocabulary;
--   * `FinSetupσ` is the call-site convenience wrapper (the σ-analogue of
--     the Mon `FinSetup`).
--
-- WHAT DECIDES (verified in `Categories.SolverSigmaFrontendTests`): all
-- Mon front-end shapes, plus σ∘σ≈id (also deep in context), σ-naturality
-- through box generators (TWO machine-fired slides, one per image block),
-- and mixes of σ-cancellation with coherence/functoriality.
--
-- LIMITATIONS: the Mon front-end's L1/L2/L4/L5/L6 carry over verbatim.
-- The braiding-specific boundary (machine-checked in the tests):
--   Lσ1  HEXAGON-shaped goals do not decide: the normalizer never splits
--        or merges crossing BLOCKS (`cross a b` vs `cross a (b₁ ++ b₂)`
--        compositions are distinct normal forms).  Only cancellation of
--        exact inverse pairs and box-slides through a crossing fire.
--   Lσ2  A box STRADDLING the two image blocks of a crossing does not
--        slide (no sound move exists without splitting the box).
--
-- Hole-free, postulate-free, --safe --without-K.
--------------------------------------------------------------------------------

module Categories.SolverSigmaFrontend where

open import Level using (Level)

open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.FreeMonoidal
open import Categories.SolverSigma using (module Sigma)

module FrontendS
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Symm X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  -- `Symm ≤ Symm` for instance search, so σ needs no explicit ⦃ v≤v ⦄.
  private instance
    S≤S : Symm ≤ Symm
    S≤S = v≤v

  ------------------------------------------------------------------------
  -- Object flattening and the wire-level generator family.
  ------------------------------------------------------------------------

  flatten : ObjTerm → List X
  flatten unit      = []
  flatten (Y ⊗₀ Z) = flatten Y ++ flatten Z
  flatten (Var x)   = x ∷ []

  data MorW : List X → List X → Set where
    mk : ∀ {Y Z} → GenF Y Z → MorW (flatten Y) (flatten Z)

  -- THE σ-ENGINE at MorW: the extended generators `MorS MorW` (box|cross),
  -- the wire signature, ⟦box⟧S, reflect/embed, and the `Decide` driver
  -- (renamed `DecideW`, the front-end defines its own `Decide` below).
  open Sigma _≟X_ MorW renaming (module Decide to DecideW)
  open FreeMonoidalHelper.Mor Symm X mor    -- W-side HomTerm, _≈Term_, σ, …
  open ≈R

  -- Front-end free category: HomTerm over GenF, qualified `F`.
  private module F = FreeMonoidalHelper.Mor Symm X GenF

  -- F-side equational reasoning (mirror of ≈R).
  module F≈R where
    infix  3 _∎F
    infixr 2 stepF-≈ stepF-≈˘
    infix  1 beginF_
    beginF_ : ∀ {A B} {f g : F.HomTerm A B} → f F.≈Term g → f F.≈Term g
    beginF_ x = x
    stepF-≈ : ∀ {A B} (f : F.HomTerm A B) {g h} → g F.≈Term h → f F.≈Term g → f F.≈Term h
    stepF-≈ _ gh fg = F.≈-Term-trans fg gh
    stepF-≈˘ : ∀ {A B} (f : F.HomTerm A B) {g h} → g F.≈Term h → g F.≈Term f → f F.≈Term h
    stepF-≈˘ _ gh gf = F.≈-Term-trans (F.≈-Term-sym gf) gh
    _∎F : ∀ {A B} (f : F.HomTerm A B) → f F.≈Term f
    _ ∎F = F.≈-Term-refl
    syntax stepF-≈  f gh fg = f ≈F⟨ fg ⟩ gh
    syntax stepF-≈˘ f gh gf = f ≈F⟨ gf ⟨ gh
  open F≈R

  ------------------------------------------------------------------------
  -- F-side structural merge/split (same recursion as the wire-level ones).
  ------------------------------------------------------------------------

  mergeF : (a : List X) {suf : List X}
         → F.HomTerm (wires a ⊗₀ wires suf) (wires (a ++ suf))
  mergeF []      = F.λ⇒
  mergeF (x ∷ a) = F._∘_ (F._⊗₁_ F.id (mergeF a)) F.α⇒

  splitF : (a : List X) {suf : List X}
         → F.HomTerm (wires (a ++ suf)) (wires a ⊗₀ wires suf)
  splitF []      = F.λ⇐
  splitF (x ∷ a) = F._∘_ F.α⇐ (F._⊗₁_ F.id (splitF a))

  ------------------------------------------------------------------------
  -- The canonical structural iso  Y ≅ wires (flatten Y), in F.
  ------------------------------------------------------------------------

  flat⇒ : (Y : ObjTerm) → F.HomTerm Y (wires (flatten Y))
  flat⇒ unit      = F.id
  flat⇒ (Y ⊗₀ Z) = F._∘_ (mergeF (flatten Y)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z))
  flat⇒ (Var x)   = F.ρ⇐

  flat⇐ : (Y : ObjTerm) → F.HomTerm (wires (flatten Y)) Y
  flat⇐ unit      = F.id
  flat⇐ (Y ⊗₀ Z) = F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z)) (splitF (flatten Y))
  flat⇐ (Var x)   = F.ρ⇒

  ------------------------------------------------------------------------
  -- `inj`: the wire-level free category into the front-end free category.
  -- Homomorphic on all constructors (σ ↦ σ); a box generator gets
  -- conjugated by the canonical iso.  The `cross` generator case is
  -- UNREACHABLE from `embed ∘ reflectF` (embed unfolds a `boxʷ (cross …)`
  -- to ⟦box⟧S's σ-composite, never to a `var`); for totality it maps to
  -- the same σ-composite, F-side.
  ------------------------------------------------------------------------

  inj : ∀ {A B} → HomTerm A B → F.HomTerm A B
  inj (var (box (box (mk {Y} {Z} g)))) = F._∘_ (flat⇒ Z) (F._∘_ (F.var g) (flat⇐ Y))
  inj (var (box (cross a b))) = F._∘_ (mergeF b {a}) (F._∘_ F.σ (splitF a {b}))
  inj id         = F.id
  inj (g ∘ f)    = F._∘_ (inj g) (inj f)
  inj (f ⊗₁ g)   = F._⊗₁_ (inj f) (inj g)
  inj λ⇒         = F.λ⇒
  inj λ⇐         = F.λ⇐
  inj ρ⇒         = F.ρ⇒
  inj ρ⇐         = F.ρ⇐
  inj α⇒         = F.α⇒
  inj α⇐         = F.α⇐
  inj (σ ⦃ v≤v ⦄) = F.σ

  -- inj preserves the equational theory (each axiom maps to the same axiom).
  inj-resp-≈ : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → inj f F.≈Term inj g
  inj-resp-≈ idˡ                 = F.idˡ
  inj-resp-≈ idʳ                 = F.idʳ
  inj-resp-≈ assoc               = F.assoc
  inj-resp-≈ (∘-resp-≈ p q)      = F.∘-resp-≈ (inj-resp-≈ p) (inj-resp-≈ q)
  inj-resp-≈ ≈-Term-refl         = F.≈-Term-refl
  inj-resp-≈ (≈-Term-sym p)      = F.≈-Term-sym (inj-resp-≈ p)
  inj-resp-≈ (≈-Term-trans p q)  = F.≈-Term-trans (inj-resp-≈ p) (inj-resp-≈ q)
  inj-resp-≈ id⊗id≈id            = F.id⊗id≈id
  inj-resp-≈ (⊗-resp-≈ p q)      = F.⊗-resp-≈ (inj-resp-≈ p) (inj-resp-≈ q)
  inj-resp-≈ ⊗-∘-dist            = F.⊗-∘-dist
  inj-resp-≈ λ⇐∘λ⇒≈id            = F.λ⇐∘λ⇒≈id
  inj-resp-≈ λ⇒∘λ⇐≈id            = F.λ⇒∘λ⇐≈id
  inj-resp-≈ ρ⇐∘ρ⇒≈id            = F.ρ⇐∘ρ⇒≈id
  inj-resp-≈ ρ⇒∘ρ⇐≈id            = F.ρ⇒∘ρ⇐≈id
  inj-resp-≈ α⇐∘α⇒≈id            = F.α⇐∘α⇒≈id
  inj-resp-≈ α⇒∘α⇐≈id            = F.α⇒∘α⇐≈id
  inj-resp-≈ λ⇒∘id⊗f≈f∘λ⇒        = F.λ⇒∘id⊗f≈f∘λ⇒
  inj-resp-≈ ρ⇒∘f⊗id≈f∘ρ⇒        = F.ρ⇒∘f⊗id≈f∘ρ⇒
  inj-resp-≈ α-comm              = F.α-comm
  inj-resp-≈ triangle            = F.triangle
  inj-resp-≈ pentagon            = F.pentagon
  inj-resp-≈ (σ∘σ≈id ⦃ v≤v ⦄)          = F.σ∘σ≈id
  inj-resp-≈ (σ∘[f⊗g]≈[g⊗f]∘σ ⦃ v≤v ⦄) = F.σ∘[f⊗g]≈[g⊗f]∘σ
  inj-resp-≈ (hexagon ⦃ v≤v ⦄)         = F.hexagon

  -- inj maps the wire-level merge/split to the F-side ones, on the nose.
  inj-merge : ∀ (a : List X) {suf} → inj (merge a {suf}) ≡ mergeF a {suf}
  inj-merge []      = refl
  inj-merge (x ∷ a) = cong (λ h → F._∘_ (F._⊗₁_ F.id h) F.α⇒) (inj-merge a)

  inj-split : ∀ (a : List X) {suf} → inj (split a {suf}) ≡ splitF a {suf}
  inj-split []      = refl
  inj-split (x ∷ a) = cong (λ h → F._∘_ F.α⇐ (F._⊗₁_ F.id h)) (inj-split a)

  ------------------------------------------------------------------------
  -- F-side coercion along a wire-list equality, and the inj-commutations.
  ------------------------------------------------------------------------

  coeCF : ∀ {A} {p q : List X} → p ≡ q
        → F.HomTerm A (wires p) → F.HomTerm A (wires q)
  coeCF refl h = h

  coeCF-∘ˡ : ∀ {A R p q} (e : p ≡ q) (h : F.HomTerm R (wires p)) (j : F.HomTerm A R)
           → coeCF e (F._∘_ h j) F.≈Term F._∘_ (coeCF e h) j
  coeCF-∘ˡ refl h j = F.≈-Term-refl

  coeCF-resp : ∀ {A p q} (e : p ≡ q) {h h' : F.HomTerm A (wires p)}
             → h F.≈Term h' → coeCF e h F.≈Term coeCF e h'
  coeCF-resp refl eq = eq

  -- inj commutes with the wire-level coercions (all definitional on refl).
  inj-coeC : ∀ {A p q} (e : p ≡ q) (h : HomTerm A (wires p))
           → inj (coeC e h) ≡ coeCF e (inj h)
  inj-coeC refl h = refl

  inj-coeCA : ∀ {A p q} (e : p ≡ q) (h : HomTerm A (wires p))
            → inj (coeCA e h) ≡ coeCF e (inj h)
  inj-coeCA refl h = refl

  inj-coeCod' : ∀ {n p q} (e : p ≡ q) (h : HomTerm (wires n) (wires p))
              → inj (coeCod' e h) ≡ coeCF e (inj h)
  inj-coeCod' refl h = refl

  ------------------------------------------------------------------------
  -- Structural lemmas transferred from the wire level along inj.
  ------------------------------------------------------------------------

  mergeF∘splitF : ∀ (a : List X) {suf} → F._∘_ (mergeF a {suf}) (splitF a) F.≈Term F.id
  mergeF∘splitF a {suf} =
    F.≈-Term-trans
      (F.≡⇒≈Term (cong₂′ (sym (inj-merge a {suf})) (sym (inj-split a {suf}))))
      (inj-resp-≈ (merge∘split a))
    where
      cong₂′ : ∀ {A B C : ObjTerm} {h h' : F.HomTerm B C} {j j' : F.HomTerm A B}
             → h ≡ h' → j ≡ j' → F._∘_ h j ≡ F._∘_ h' j'
      cong₂′ refl refl = refl

  splitF∘mergeF : ∀ (a : List X) {suf} → F._∘_ (splitF a {suf}) (mergeF a) F.≈Term F.id
  splitF∘mergeF a {suf} =
    F.≈-Term-trans
      (F.≡⇒≈Term (cong₂′ (sym (inj-split a {suf})) (sym (inj-merge a {suf}))))
      (inj-resp-≈ (split∘merge a))
    where
      cong₂′ : ∀ {A B C : ObjTerm} {h h' : F.HomTerm B C} {j j' : F.HomTerm A B}
             → h ≡ h' → j ≡ j' → F._∘_ h j ≡ F._∘_ h' j'
      cong₂′ refl refl = refl

  -- right-unitor coherence on the F-side merge (transfer of merge-ρ).
  mergeF-ρ : ∀ (a : List X)
           → coeCF (++-identityʳ a) (mergeF a {[]}) F.≈Term F.ρ⇒
  mergeF-ρ a =
    F.≈-Term-trans
      (F.≡⇒≈Term (trans (cong (coeCF (++-identityʳ a)) (sym (inj-merge a)))
                        (sym (inj-coeC (++-identityʳ a) (merge a {[]})))))
      (inj-resp-≈ (merge-ρ a))

  -- merge associativity on the F side (transfer of merge-assoc).
  mergeF-assoc : ∀ (p q r : List X)
    → F._∘_ (mergeF p {q ++ r}) (F._∘_ (F._⊗₁_ (F.id {wires p}) (mergeF q {r})) F.α⇒)
      F.≈Term coeCF (++-assoc p q r)
                (F._∘_ (mergeF (p ++ q) {r}) (F._⊗₁_ (mergeF p {q}) (F.id {wires r})))
  mergeF-assoc p q r =
    F.≈-Term-trans
      (F.≡⇒≈Term (sym (lhs-eq)))
      (F.≈-Term-trans
        (inj-resp-≈ (merge-assoc p q r))
        (F.≡⇒≈Term rhs-eq))
    where
      lhs-eq : inj (merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒)
             ≡ F._∘_ (mergeF p {q ++ r})
                 (F._∘_ (F._⊗₁_ (F.id {wires p}) (mergeF q {r})) F.α⇒)
      lhs-eq rewrite inj-merge p {q ++ r} | inj-merge q {r} = refl
      rhs-eq : inj (coeCA (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
             ≡ coeCF (++-assoc p q r)
                 (F._∘_ (mergeF (p ++ q) {r}) (F._⊗₁_ (mergeF p {q}) (F.id {wires r})))
      rhs-eq rewrite inj-coeCA (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
                   | inj-merge (p ++ q) {r} | inj-merge p {q} = refl

  ------------------------------------------------------------------------
  -- The canonical iso laws (only the retraction is needed downstream).
  ------------------------------------------------------------------------

  flat⇐∘flat⇒ : ∀ (Y : ObjTerm) → F._∘_ (flat⇐ Y) (flat⇒ Y) F.≈Term F.id
  flat⇐∘flat⇒ unit = F.idˡ
  flat⇐∘flat⇒ (Y ⊗₀ Z) = beginF
    F._∘_ (F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z)) (splitF (flatten Y)))
          (F._∘_ (mergeF (flatten Y)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z)))
      ≈F⟨ F.assoc ⟩
    F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z))
          (F._∘_ (splitF (flatten Y))
                 (F._∘_ (mergeF (flatten Y)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z))))
      ≈F⟨ F.∘-resp-≈ F.≈-Term-refl (F.≈-Term-sym F.assoc) ⟩
    F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z))
          (F._∘_ (F._∘_ (splitF (flatten Y)) (mergeF (flatten Y)))
                 (F._⊗₁_ (flat⇒ Y) (flat⇒ Z)))
      ≈F⟨ F.∘-resp-≈ F.≈-Term-refl (F.∘-resp-≈ (splitF∘mergeF (flatten Y)) F.≈-Term-refl) ⟩
    F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z))
          (F._∘_ F.id (F._⊗₁_ (flat⇒ Y) (flat⇒ Z)))
      ≈F⟨ F.∘-resp-≈ F.≈-Term-refl F.idˡ ⟩
    F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z))
      ≈F⟨ F.⊗-∘-dist ⟨
    F._⊗₁_ (F._∘_ (flat⇐ Y) (flat⇒ Y)) (F._∘_ (flat⇐ Z) (flat⇒ Z))
      ≈F⟨ F.⊗-resp-≈ (flat⇐∘flat⇒ Y) (flat⇐∘flat⇒ Z) ⟩
    F._⊗₁_ F.id F.id
      ≈F⟨ F.id⊗id≈id ⟩
    F.id ∎F
  flat⇐∘flat⇒ (Var x) = F.ρ⇒∘ρ⇐≈id

  ------------------------------------------------------------------------
  -- Front-end reflection: structural constructors die into (casted) idʷ;
  -- the braiding σ becomes a transparent block CROSSING — cast-free, since
  -- `flatten (A ⊗₀ B) ≡ flatten A ++ flatten B` definitionally.
  ------------------------------------------------------------------------

  castʷ : ∀ {n n' m m'} → n ≡ n' → m ≡ m' → WTerm n m → WTerm n' m'
  castʷ refl refl t = t

  embed-castʷ : ∀ {n n' m m'} (p : n ≡ n') (q : m ≡ m') (t : WTerm n m)
              → embed (castʷ p q t) ≈Term coeDom p (coeCod' q (embed t))
  embed-castʷ refl refl t = ≈-Term-refl

  coeDF : ∀ {p q : List X} {B} → p ≡ q
        → F.HomTerm (wires p) B → F.HomTerm (wires q) B
  coeDF refl h = h

  inj-coeDom : ∀ {p q r} (e : p ≡ q) (h : HomTerm (wires p) (wires r))
             → inj (coeDom e h) ≡ coeDF e (inj h)
  inj-coeDom refl h = refl

  reflectF : ∀ {Y Z} → F.HomTerm Y Z → WTerm (flatten Y) (flatten Z)
  reflectF (F.var g)            = boxʷ (box (mk g))
  reflectF F.id                 = idʷ
  reflectF (F._∘_ g f)          = reflectF g ∘ʷ reflectF f
  reflectF (F._⊗₁_ f g)         = reflectF f ⊗ʷ reflectF g
  reflectF (F.λ⇒ {A})           = idʷ
  reflectF (F.λ⇐ {A})           = idʷ
  reflectF (F.ρ⇒ {A})           = castʷ refl (++-identityʳ (flatten A)) idʷ
  reflectF (F.ρ⇐ {A})           = castʷ refl (sym (++-identityʳ (flatten A))) idʷ
  reflectF (F.α⇒ {A} {B} {C})   = castʷ refl (++-assoc (flatten A) (flatten B) (flatten C)) idʷ
  reflectF (F.α⇐ {A} {B} {C})   = castʷ refl (sym (++-assoc (flatten A) (flatten B) (flatten C))) idʷ
  reflectF (F.σ {A} {B} ⦃ v≤v ⦄) = boxʷ (cross (flatten A) (flatten B))

  ------------------------------------------------------------------------
  -- The soundness bridge.  All stated in the front-end free category.
  ------------------------------------------------------------------------

  -- readability aliases (function aliases of the F constructors)
  private
    infixr 9 _∘F_
    infixr 10 _⊗F_
    _∘F_ : ∀ {A B C} → F.HomTerm B C → F.HomTerm A B → F.HomTerm A C
    _∘F_ = F._∘_
    _⊗F_ : ∀ {A B C D} → F.HomTerm A B → F.HomTerm C D → F.HomTerm (A ⊗₀ C) (B ⊗₀ D)
    _⊗F_ = F._⊗₁_
    idF : ∀ {A} → F.HomTerm A A
    idF = F.id
    reflF : ∀ {A B} {f : F.HomTerm A B} → f F.≈Term f
    reflF = F.≈-Term-refl

  -- a casted idʷ, embedded and injected, is the F-side coercion of whatever
  -- it is composed onto.
  cast-half : ∀ {P} {p q : List X} (e : p ≡ q) (h : F.HomTerm P (wires p))
            → inj (embed (castʷ refl e (idʷ {p}))) ∘F h F.≈Term coeCF e h
  cast-half {P} {p} {q} e h = beginF
    inj (embed (castʷ refl e (idʷ {p}))) ∘F h
      ≈F⟨ F.∘-resp-≈ (F.≈-Term-trans (inj-resp-≈ (embed-castʷ refl e idʷ))
                                     (F.≡⇒≈Term (inj-coeCod' e id))) reflF ⟩
    coeCF e idF ∘F h
      ≈F⟨ coeCF-∘ˡ e idF h ⟨
    coeCF e (idF ∘F h)
      ≈F⟨ coeCF-resp e F.idˡ ⟩
    coeCF e h ∎F

  -- the two opposite coercions cancel (UIP-free: by matching e).
  coe-coe : ∀ {A} {p q : List X} (e : p ≡ q) (h : F.HomTerm A (wires p))
          → coeCF (sym e) (coeCF e h) ≡ h
  coe-coe refl h = refl

  -- forward structural laws: flattening intertwines the unitors/associator.
  fwd-λ : ∀ (A : ObjTerm) → flat⇒ (unit ⊗₀ A) F.≈Term flat⇒ A ∘F F.λ⇒
  fwd-λ A = F.λ⇒∘id⊗f≈f∘λ⇒

  fwd-ρ : ∀ (A : ObjTerm)
        → coeCF (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit))
          F.≈Term flat⇒ A ∘F F.ρ⇒
  fwd-ρ A = beginF
    coeCF e (mergeF fA {[]} ∘F (flat⇒ A ⊗F idF))
      ≈F⟨ coeCF-∘ˡ e (mergeF fA {[]}) (flat⇒ A ⊗F idF) ⟩
    coeCF e (mergeF fA {[]}) ∘F (flat⇒ A ⊗F idF)
      ≈F⟨ F.∘-resp-≈ (mergeF-ρ fA) reflF ⟩
    F.ρ⇒ ∘F (flat⇒ A ⊗F idF)
      ≈F⟨ F.ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
    flat⇒ A ∘F F.ρ⇒ ∎F
    where
      fA = flatten A
      e  = ++-identityʳ fA

  fwd-α : ∀ (A B C : ObjTerm)
        → coeCF (++-assoc (flatten A) (flatten B) (flatten C))
                (flat⇒ ((A ⊗₀ B) ⊗₀ C))
          F.≈Term flat⇒ (A ⊗₀ (B ⊗₀ C)) ∘F F.α⇒
  fwd-α A B C = beginF
    coeCF e (mergeF (fA ++ fB) {fC} ∘F ((mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B)) ⊗F f⇒C))
      ≈F⟨ coeCF-resp e (F.∘-resp-≈ reflF
            (F.≈-Term-trans (F.⊗-resp-≈ reflF (F.≈-Term-sym F.idˡ)) F.⊗-∘-dist)) ⟩
    coeCF e (mergeF (fA ++ fB) {fC} ∘F ((mergeF fA {fB} ⊗F idF) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)))
      ≈F⟨ coeCF-resp e (F.≈-Term-sym F.assoc) ⟩
    coeCF e ((mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C))
      ≈F⟨ coeCF-∘ˡ e (mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ((f⇒A ⊗F f⇒B) ⊗F f⇒C) ⟩
    coeCF e (mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)
      ≈F⟨ F.∘-resp-≈ (mergeF-assoc fA fB fC) reflF ⟨
    (mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F F.α⇒)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)
      ≈F⟨ F.assoc ⟩
    mergeF fA {fB ++ fC} ∘F (((idF ⊗F mergeF fB {fC}) ∘F F.α⇒) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C))
      ≈F⟨ F.∘-resp-≈ reflF F.assoc ⟩
    mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F (F.α⇒ ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)))
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈ reflF F.α-comm) ⟩
    mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F ((f⇒A ⊗F (f⇒B ⊗F f⇒C)) ∘F F.α⇒))
      ≈F⟨ F.∘-resp-≈ reflF (F.≈-Term-sym F.assoc) ⟩
    mergeF fA {fB ++ fC} ∘F (((idF ⊗F mergeF fB {fC}) ∘F (f⇒A ⊗F (f⇒B ⊗F f⇒C))) ∘F F.α⇒)
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈
            (F.≈-Term-trans (F.≈-Term-sym F.⊗-∘-dist)
                            (F.⊗-resp-≈ F.idˡ reflF)) reflF) ⟩
    mergeF fA {fB ++ fC} ∘F ((f⇒A ⊗F (mergeF fB {fC} ∘F (f⇒B ⊗F f⇒C))) ∘F F.α⇒)
      ≈F⟨ F.≈-Term-sym F.assoc ⟩
    (mergeF fA {fB ++ fC} ∘F (f⇒A ⊗F (mergeF fB {fC} ∘F (f⇒B ⊗F f⇒C)))) ∘F F.α⇒ ∎F
    where
      fA = flatten A ; fB = flatten B ; fC = flatten C
      e  = ++-assoc fA fB fC
      f⇒A = flat⇒ A ; f⇒B = flat⇒ B ; f⇒C = flat⇒ C

  -- flip a forward law to its inverse structural morphism.
  flipF : ∀ {P Q} {p q : List X} (e : p ≡ q)
            (h⇒P : F.HomTerm P (wires p)) (h⇒Q : F.HomTerm Q (wires q))
            {c : F.HomTerm P Q} {c⁻¹ : F.HomTerm Q P}
        → c ∘F c⁻¹ F.≈Term idF
        → coeCF e h⇒P F.≈Term h⇒Q ∘F c
        → coeCF (sym e) h⇒Q F.≈Term h⇒P ∘F c⁻¹
  flipF e h⇒P h⇒Q {c} {c⁻¹} iso fwd = F.≈-Term-sym (beginF
    h⇒P ∘F c⁻¹
      ≈F⟨ F.∘-resp-≈ (F.≡⇒≈Term (coe-coe e h⇒P)) reflF ⟨
    coeCF (sym e) (coeCF e h⇒P) ∘F c⁻¹
      ≈F⟨ F.∘-resp-≈ (coeCF-resp (sym e) fwd) reflF ⟩
    coeCF (sym e) (h⇒Q ∘F c) ∘F c⁻¹
      ≈F⟨ F.∘-resp-≈ (coeCF-∘ˡ (sym e) h⇒Q c) reflF ⟩
    (coeCF (sym e) h⇒Q ∘F c) ∘F c⁻¹
      ≈F⟨ F.assoc ⟩
    coeCF (sym e) h⇒Q ∘F (c ∘F c⁻¹)
      ≈F⟨ F.∘-resp-≈ reflF iso ⟩
    coeCF (sym e) h⇒Q ∘F idF
      ≈F⟨ F.idʳ ⟩
    coeCF (sym e) h⇒Q ∎F)

  ------------------------------------------------------------------------
  -- bridgeF: the front-end reflection is sound, up to the canonical iso.
  -- The ONE genuinely new case is σ: `embed (boxʷ (cross fA fB))` unfolds
  -- to `merge fB ∘ σ ∘ split fA`; after `splitF ∘ mergeF` cancellation the
  -- goal is braiding naturality at the pair (flat⇒ A , flat⇒ B).
  ------------------------------------------------------------------------

  bridgeF : ∀ {Y Z} (t : F.HomTerm Y Z)
          → inj (embed (reflectF t)) ∘F flat⇒ Y F.≈Term flat⇒ Z ∘F t
  bridgeF {Y} {Z} (F.var g) = beginF
    (flat⇒ Z ∘F (F.var g ∘F flat⇐ Y)) ∘F flat⇒ Y
      ≈F⟨ F.assoc ⟩
    flat⇒ Z ∘F ((F.var g ∘F flat⇐ Y) ∘F flat⇒ Y)
      ≈F⟨ F.∘-resp-≈ reflF F.assoc ⟩
    flat⇒ Z ∘F (F.var g ∘F (flat⇐ Y ∘F flat⇒ Y))
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈ reflF (flat⇐∘flat⇒ Y)) ⟩
    flat⇒ Z ∘F (F.var g ∘F idF)
      ≈F⟨ F.∘-resp-≈ reflF F.idʳ ⟩
    flat⇒ Z ∘F F.var g ∎F
  bridgeF {Y} {.Y} F.id = F.≈-Term-trans F.idˡ (F.≈-Term-sym F.idʳ)
  bridgeF {Y} {Z} (F._∘_ {B = M} g f) = beginF
    (inj (embed (reflectF g)) ∘F inj (embed (reflectF f))) ∘F flat⇒ Y
      ≈F⟨ F.assoc ⟩
    inj (embed (reflectF g)) ∘F (inj (embed (reflectF f)) ∘F flat⇒ Y)
      ≈F⟨ F.∘-resp-≈ reflF (bridgeF f) ⟩
    inj (embed (reflectF g)) ∘F (flat⇒ M ∘F f)
      ≈F⟨ F.≈-Term-sym F.assoc ⟩
    (inj (embed (reflectF g)) ∘F flat⇒ M) ∘F f
      ≈F⟨ F.∘-resp-≈ (bridgeF g) reflF ⟩
    (flat⇒ Z ∘F g) ∘F f
      ≈F⟨ F.assoc ⟩
    flat⇒ Z ∘F (g ∘F f) ∎F
  bridgeF (F._⊗₁_ {A = Y} {B = Z} {C = Y'} {D = Z'} f g) = beginF
    inj (embed (reflectF f ⊗ʷ reflectF g)) ∘F (mergeF fY {fY'} ∘F (f⇒Y ⊗F f⇒Y'))
      ≈F⟨ F.∘-resp-≈ (F.≡⇒≈Term (cong₂ (λ m s → m ∘F ((IF ⊗F IG) ∘F s))
                                       (inj-merge fZ {fZ'}) (inj-split fY {fY'}))) reflF ⟩
    (mergeF fZ {fZ'} ∘F ((IF ⊗F IG) ∘F splitF fY {fY'})) ∘F (mergeF fY {fY'} ∘F (f⇒Y ⊗F f⇒Y'))
      ≈F⟨ F.assoc ⟩
    mergeF fZ {fZ'} ∘F (((IF ⊗F IG) ∘F splitF fY {fY'}) ∘F (mergeF fY {fY'} ∘F (f⇒Y ⊗F f⇒Y')))
      ≈F⟨ F.∘-resp-≈ reflF F.assoc ⟩
    mergeF fZ {fZ'} ∘F ((IF ⊗F IG) ∘F (splitF fY {fY'} ∘F (mergeF fY {fY'} ∘F (f⇒Y ⊗F f⇒Y'))))
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈ reflF (F.≈-Term-sym F.assoc)) ⟩
    mergeF fZ {fZ'} ∘F ((IF ⊗F IG) ∘F ((splitF fY {fY'} ∘F mergeF fY {fY'}) ∘F (f⇒Y ⊗F f⇒Y')))
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈ reflF
            (F.≈-Term-trans (F.∘-resp-≈ (splitF∘mergeF fY {fY'}) reflF) F.idˡ)) ⟩
    mergeF fZ {fZ'} ∘F ((IF ⊗F IG) ∘F (f⇒Y ⊗F f⇒Y'))
      ≈F⟨ F.∘-resp-≈ reflF F.⊗-∘-dist ⟨
    mergeF fZ {fZ'} ∘F ((IF ∘F f⇒Y) ⊗F (IG ∘F f⇒Y'))
      ≈F⟨ F.∘-resp-≈ reflF (F.⊗-resp-≈ (bridgeF f) (bridgeF g)) ⟩
    mergeF fZ {fZ'} ∘F ((f⇒Z ∘F f) ⊗F (f⇒Z' ∘F g))
      ≈F⟨ F.∘-resp-≈ reflF F.⊗-∘-dist ⟩
    mergeF fZ {fZ'} ∘F ((f⇒Z ⊗F f⇒Z') ∘F (f ⊗F g))
      ≈F⟨ F.≈-Term-sym F.assoc ⟩
    (mergeF fZ {fZ'} ∘F (f⇒Z ⊗F f⇒Z')) ∘F (f ⊗F g) ∎F
    where
      fY = flatten Y ; fY' = flatten Y' ; fZ = flatten Z ; fZ' = flatten Z'
      f⇒Y = flat⇒ Y ; f⇒Y' = flat⇒ Y' ; f⇒Z = flat⇒ Z ; f⇒Z' = flat⇒ Z'
      IF = inj (embed (reflectF f))
      IG = inj (embed (reflectF g))
  bridgeF (F.λ⇒ {A}) = F.≈-Term-trans F.idˡ (fwd-λ A)
  bridgeF (F.λ⇐ {A}) =
    F.≈-Term-trans F.idˡ
      (flipF refl (flat⇒ (unit ⊗₀ A)) (flat⇒ A) F.λ⇒∘λ⇐≈id (fwd-λ A))
  bridgeF (F.ρ⇒ {A}) =
    F.≈-Term-trans (cast-half (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit))) (fwd-ρ A)
  bridgeF (F.ρ⇐ {A}) =
    F.≈-Term-trans (cast-half (sym (++-identityʳ (flatten A))) (flat⇒ A))
      (flipF (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit)) (flat⇒ A)
             F.ρ⇒∘ρ⇐≈id (fwd-ρ A))
  bridgeF (F.α⇒ {A} {B} {C}) =
    F.≈-Term-trans
      (cast-half (++-assoc (flatten A) (flatten B) (flatten C)) (flat⇒ ((A ⊗₀ B) ⊗₀ C)))
      (fwd-α A B C)
  bridgeF (F.α⇐ {A} {B} {C}) =
    F.≈-Term-trans
      (cast-half (sym (++-assoc (flatten A) (flatten B) (flatten C))) (flat⇒ (A ⊗₀ (B ⊗₀ C))))
      (flipF (++-assoc (flatten A) (flatten B) (flatten C))
             (flat⇒ ((A ⊗₀ B) ⊗₀ C)) (flat⇒ (A ⊗₀ (B ⊗₀ C)))
             F.α⇒∘α⇐≈id (fwd-α A B C))
  bridgeF (F.σ {A} {B} ⦃ v≤v ⦄) = beginF
    inj (embed (reflectF (F.σ {A} {B}))) ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B))
      ≈F⟨ F.∘-resp-≈ (F.≡⇒≈Term (cong-σ (inj-merge fB {fA}) (inj-split fA {fB}))) reflF ⟩
    (mergeF fB {fA} ∘F (F.σ ∘F splitF fA {fB})) ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B))
      ≈F⟨ F.assoc ⟩
    mergeF fB {fA} ∘F ((F.σ ∘F splitF fA {fB}) ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B)))
      ≈F⟨ F.∘-resp-≈ reflF F.assoc ⟩
    mergeF fB {fA} ∘F (F.σ ∘F (splitF fA {fB} ∘F (mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B))))
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈ reflF (F.≈-Term-sym F.assoc)) ⟩
    mergeF fB {fA} ∘F (F.σ ∘F ((splitF fA {fB} ∘F mergeF fA {fB}) ∘F (f⇒A ⊗F f⇒B)))
      ≈F⟨ F.∘-resp-≈ reflF (F.∘-resp-≈ reflF
            (F.≈-Term-trans (F.∘-resp-≈ (splitF∘mergeF fA {fB}) reflF) F.idˡ)) ⟩
    mergeF fB {fA} ∘F (F.σ ∘F (f⇒A ⊗F f⇒B))
      ≈F⟨ F.∘-resp-≈ reflF F.σ∘[f⊗g]≈[g⊗f]∘σ ⟩
    mergeF fB {fA} ∘F ((f⇒B ⊗F f⇒A) ∘F F.σ)
      ≈F⟨ F.≈-Term-sym F.assoc ⟩
    (mergeF fB {fA} ∘F (f⇒B ⊗F f⇒A)) ∘F F.σ ∎F
    where
      fA = flatten A ; fB = flatten B
      f⇒A = flat⇒ A ; f⇒B = flat⇒ B
      σF : F.HomTerm (wires fA ⊗₀ wires fB) (wires fB ⊗₀ wires fA)
      σF = F.σ
      cong-σ : {h h' : F.HomTerm (wires fB ⊗₀ wires fA) (wires (fB ++ fA))}
               {j j' : F.HomTerm (wires (fA ++ fB)) (wires fA ⊗₀ wires fB)}
             → h ≡ h' → j ≡ j'
             → F._∘_ h (F._∘_ σF j) ≡ F._∘_ h' (F._∘_ σF j')
      cong-σ refl refl = refl

  ------------------------------------------------------------------------
  -- The cancellation: a wire-level equality of the two reflections is a
  -- front-end equality of the original terms.
  ------------------------------------------------------------------------

  solveF : ∀ {Y Z} {l r : F.HomTerm Y Z}
         → embed (reflectF l) ≈Term embed (reflectF r)
         → l F.≈Term r
  solveF {Y} {Z} {l} {r} eq = beginF
    l
      ≈F⟨ F.idˡ ⟨
    idF ∘F l
      ≈F⟨ F.∘-resp-≈ (flat⇐∘flat⇒ Z) reflF ⟨
    (flat⇐ Z ∘F flat⇒ Z) ∘F l
      ≈F⟨ F.assoc ⟩
    flat⇐ Z ∘F (flat⇒ Z ∘F l)
      ≈F⟨ F.∘-resp-≈ reflF main ⟩
    flat⇐ Z ∘F (flat⇒ Z ∘F r)
      ≈F⟨ F.≈-Term-sym F.assoc ⟩
    (flat⇐ Z ∘F flat⇒ Z) ∘F r
      ≈F⟨ F.∘-resp-≈ (flat⇐∘flat⇒ Z) reflF ⟩
    idF ∘F r
      ≈F⟨ F.idˡ ⟩
    r ∎F
    where
      main : flat⇒ Z ∘F l F.≈Term flat⇒ Z ∘F r
      main = beginF
        flat⇒ Z ∘F l
          ≈F⟨ bridgeF l ⟨
        inj (embed (reflectF l)) ∘F flat⇒ Y
          ≈F⟨ F.∘-resp-≈ (inj-resp-≈ eq) reflF ⟩
        inj (embed (reflectF r)) ∘F flat⇒ Y
          ≈F⟨ bridgeF r ⟩
        flat⇒ Z ∘F r ∎F

  ------------------------------------------------------------------------
  -- The decision procedure: reflect both sides, hand them to the σ-engine
  -- driver `decideσ?` (σσ-cancel + slides + interchange), cancel through
  -- the bridge.
  ------------------------------------------------------------------------

  GenΣ : Set
  GenΣ = Σ[ Y ∈ ObjTerm ] Σ[ Z ∈ ObjTerm ] GenF Y Z

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous (mutually-fitting) pairs;
                        -- for a Fin-indexed signature, `toℕ` of the index.
    where

    -- decidable equality and rank on the Σ-packaged wire-level generators,
    -- derived from the front-end ones (mk is injective on the triple).
    private
      _≟GM_ : DecidableEquality GenM
      (_ , _ , mk {Y} {Z} g) ≟GM (_ , _ , mk {Y'} {Z'} g')
        with (Y , Z , g) ≟G (Y' , Z' , g')
      ... | yes refl = yes refl
      ... | no ¬p    = no λ { refl → ¬p refl }

      rankM : GenM → ℕ
      rankM (_ , _ , mk {Y} {Z} g) = rank (Y , Z , g)

      module DW = DecideW _≟GM_ rankM

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- SYMMETRIC monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r with DW.decideσ? (reflectF l) (reflectF r)
    ... | nothing = nothing
    ... | just eq = just (solveF eq)

    -- the computing hit-witness: normalizes to ⊤ exactly on a solver hit, so
    -- the implicit is auto-discharged at concrete test sites.
    IsJust : ∀ {a} {A : Set a} → Maybe A → Set
    IsJust (just _) = ⊤
    IsJust nothing  = ⊥

    private
      extract : ∀ {a} {A : Set a} (x : Maybe A) → IsJust x → A
      extract (just a) _ = a

    -- reference-style entry point at the free level.
    solveTerm! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                 {hit : IsJust (decide?F l r)} → l F.≈Term r
    solveTerm! l r {hit} = extract (decide?F l r) hit

    ------------------------------------------------------------------------
    -- Transport into an arbitrary target SYMMETRIC monoidal category (a
    -- monoidal category bundled with a `Symmetric` structure), along the
    -- free functor at the ObjTerm-arity generators.  The interpretation is
    -- definitional on every term constructor — σ lands on the target's
    -- braiding — so `solveMorσ!`'s equation reads in the target's own
    -- vocabulary.
    ------------------------------------------------------------------------

    module Into
      {o ℓ e : Level}
      (C : MonoidalCategory o ℓ e)
      (Sym : Symmetric (C .MonoidalCategory.monoidal))
      (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
      where

      private
        dF : FreeMonoidalData
        dF = record { v = Symm ; X = X ; mor = GenF }

        ⟦v⟧F : ⟦ Symm ⟧ᵥ {o} {ℓ} {e}
        ⟦v⟧F = record
          { C = C .MonoidalCategory.U
          ; Monoidal-C = C .MonoidalCategory.monoidal
          ; Symmetric-C = λ ⦃ _ ⦄ → Sym
          }

      open FreeFunctorHelper dF ⟦v⟧F using (module Go)
      open Go ⟦_⟧ᵖ₀ using () renaming (⟦_⟧₀ to ⟦_⟧ₒ) public

      module WithGen
        (⟦gen⟧ : ∀ {Y Z} → GenF Y Z
               → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
        where

        private
          ffdF : FreeFunctorData dF {o} {ℓ} {e}
          ffdF = record { ⟦v⟧ = ⟦v⟧F ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦gen⟧ }

        open FreeFunctor {d = dF} ffdF public using (⟦_⟧₁; ⟦⟧-resp-≈)

        -- THE entry point: discharge a target-category equation whose two
        -- sides are interpretations of front-end terms (with σ).
        solveMorσ! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                     {hit : IsJust (decide?F l r)}
                   → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
        solveMorσ! l r {hit} = ⟦⟧-resp-≈ (solveTerm! l r {hit})

--------------------------------------------------------------------------------
-- `FinSetupσ`: the call-site convenience wrapper (the σ-analogue of the Mon
-- front-end's `FinSetup`).  From
--
--   * a target monoidal category `C` WITH a `Symmetric` structure,
--   * a `Vec` of object atoms, and
--   * a Fin-indexed `arity` table of generator arities,
--
-- it assembles the signature, decidable equalities and the rank tiebreak,
-- exposing the term language `S` (with σ), the generator embedding `gen`,
-- the object interpretation `⟦_⟧ₒ`, and — after `WithGen` supplies the
-- generator interpretations — the `solveMorσ!` entry point.
--------------------------------------------------------------------------------

module FinSetupσ
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  (Sym : Symmetric (C .MonoidalCategory.monoidal))
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper Symm (Fin nA) public
    using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    data GenS : ObjTerm → ObjTerm → Set where
      genS : (i : Fin nG) → GenS (proj₁ (arity i)) (proj₂ (arity i))

    -- the front-end term language over the assembled signature.
    module S = FreeMonoidalHelper.Mor Symm (Fin nA) GenS

    gen : (i : Fin nG) → S.HomTerm (proj₁ (arity i)) (proj₂ (arity i))
    gen i = S.var (genS i)

    open FrontendS {Fin nA} _≟Fin_ GenS using (GenΣ; module Decide)

    private
      _≟G_ : DecidableEquality GenΣ
      (_ , _ , genS i) ≟G (_ , _ , genS j) with i ≟Fin j
      ... | yes refl = yes refl
      ... | no ¬p    = no λ where refl → ¬p refl

      rankS : GenΣ → ℕ
      rankS (_ , _ , genS i) = toℕ i

    open Decide _≟G_ rankS public
      using (decide?F; IsJust; solveTerm!; module Into)
    open Into C Sym (lookup vars) public
