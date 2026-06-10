{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The solver FRONT-END: from wire-list diagrams to ObjTerm-arity generators.
--
-- The reflect/normalize/compare pipeline (SolverReflect / SolverNormalize /
-- SolverCompare) lives in the *wire-list* world: generators sit between
-- `wires a` / `wires b` and the tensor of flat terms needs a merge/split
-- conjugation (`embed (s ⊗ʷ t) = merge ∘ (… ⊗₁ …) ∘ split`).  That
-- conjugation leaks into every statement, so a clean target-category goal
-- like `(id ⊗₁ tᴹ) ∘ (sᴹ ⊗₁ id) ≈ sᴹ ⊗₁ tᴹ` cannot be discharged directly.
--
-- This module adds the missing front-end, mirroring the architecture of the
-- hypergraph solver's `Categories.Coherence.Symmetric.Setup`:
--
--   * generators `GenF : ObjTerm → ObjTerm → Set` live at ARBITRARY object
--     terms, and the front-end term language is `FreeMonoidalHelper.Mor`'s
--     `HomTerm` over `GenF`, whose interpretation into a target monoidal
--     category is DEFINITIONAL on every constructor (via `FreeFunctor`);
--
--   * `flatten : ObjTerm → List X` (with `flatten (Y ⊗₀ Z) ≡ flatten Y ++
--     flatten Z` definitionally) re-indexes the generators into a wire-level
--     family `MorW`, and `reflectF` maps front-end terms to wire terms
--     (structural morphisms die into casted `idʷ`s);
--
--   * the soundness bridge is proven ONCE, at the free level: `inj` maps the
--     wire-level free category into the front-end free category (boxes get
--     conjugated by the canonical structural iso `flat⇒`/`flat⇐`), and
--
--         bridgeF : inj (embed (reflectF t)) ∘ flat⇒ ≈ flat⇒ ∘ t
--
--     holds by induction, with the structural cases discharged by the
--     wire-level coherence lemmas (`merge-ρ`, `merge-assoc`, `merge∘split`)
--     transferred along `inj`;
--
--   * `Decide.solveTerm!` packages reflect → normalize → compare → bridge →
--     cancel into a decision procedure for the front-end `_≈Term_`, and
--     `Decide.Into.solveMor!` transports the result into an arbitrary target
--     monoidal category along the free functor — definitionally, so the
--     equation's two sides appear in the target's own vocabulary.
--
-- WHAT DECIDES (verified in `Categories.SolverFrontendTests`):
--   pure MacLane coherence (unitor/associator iso laws, triangle, pentagon,
--   λ≈ρ on unit); unitor/associator NATURALITY through box generators;
--   id/∘ laws and ⊗-functoriality; disjoint-box interchange in EITHER
--   firing order — the normalizer is a fuel-bounded bubble sort (`norm`,
--   budget (#layers)²+1) firing genuine interchange swaps at ANY position,
--   so multi-swap and non-head inversions decide — including multi-wire
--   boxes, empty-domain boxes and scalars (Eckmann-Hilton-style scalar
--   reordering decides via the `rank` tiebreak).
--
-- LIMITATIONS (precise; L2 machine-checked as `≡ nothing` in the tests):
--   L1  Sound, NOT complete: every `just` is a real `_≈Term_` proof, but
--       `nothing` does not refute the equation.
--   L2  Ambiguous pairs need an injective rank: scalar-like layers at the
--       same offset (`mid ≡ [] ∧ by ≡ [] ∧ ax ≡ []`) fit the swap
--       recogniser in BOTH orders and are ordered by the user-supplied
--       `rank` tiebreak; under a NON-INJECTIVE rank the sort cannot
--       separate them and `u ∘ v ≈ v ∘ u` stays undecided
--       (`Limitations.lim-equal-rank`).
--   L3  Monoidal only (`Variant` `Mon`): braided/symmetric goals are not
--       expressible (no σ in the term language).
--   L4  Decision-by-evaluation: requires a CONCRETE atom set (computing
--       `DecidableEquality`) and concrete arities; over abstract atoms the
--       `++-identityʳ`/`++-assoc` casts in `reflectF` do not reduce, so the
--       `IsJust` hit of `solveTerm!`/`solveMor!` cannot auto-discharge.
--       (For the same reason `step?` only iterates productively on concrete
--       diagrams: the `substDiagU` casts inside a swap result reduce only
--       at concrete indices.)
--   L5  Generator equality is the supplied syntactic `_≟G_`: no
--       generator-specific equations (naturality of a concrete box,
--       Frobenius laws, …) are known to the DECISION procedure.  The
--       rewriting layer (`rewriteMor!`/`rewriteMorₙ!`/`rewriteMorAuto!`)
--       carries such equations across as RULES: the rule fires inside a
--       two-sided frame `post ∘ (id ⊗ (– ⊗ id)) ∘ pre` (supplied, or
--       located by `focusAtₙ`), and the solver reconciles the endpoints.
--   L6  No canonicity/completeness theorem is claimed for `norm ∘ reflect`;
--       the test suite documents which equation shapes decide.
--
-- Hole-free, postulate-free, --safe.
--------------------------------------------------------------------------------

module Categories.SolverFrontend where

open import Level using (Level)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.Nat using (ℕ; _*_; _<ᵇ_) renaming (zero to nzero; suc to nsuc)
open import Data.Vec using (Vec; lookup)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ≡-dec)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Categories.Category using (Category; _[_,_]; _[_≈_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.FreeMonoidal
open import Categories.DiagramRewriteUntyped using (module Untyped)
open import Categories.SolverReflect using (module Reflect)
open import Categories.SolverNormalize using (module Normalize)
open import Categories.SolverCompare using (module SolverCompare)

module Frontend
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  -- UIP on the wire lists, via Hedberg (decidable equality), --without-K.
  private
    ≡-irrelevantL : ∀ {x y : List X} (e e' : x ≡ y) → e ≡ e'
    ≡-irrelevantL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  ------------------------------------------------------------------------
  -- Object flattening and the wire-level generator family.
  ------------------------------------------------------------------------

  flatten : ObjTerm → List X
  flatten unit      = []
  flatten (Y ⊗₀ Z) = flatten Y ++ flatten Z
  flatten (Var x)   = x ∷ []

  data MorW : List X → List X → Set where
    mk : ∀ {Y Z} → GenF Y Z → MorW (flatten Y) (flatten Z)

  -- Wire-level machinery at MorW.
  open Untyped Mon {X} MorW                -- wires, mor, box, ⟦box⟧, merge, split, …
  open FreeMonoidalHelper.Mor Mon X mor    -- W-side HomTerm, _≈Term_, …
  open Reflect Mon {X} _≟X_ MorW           -- WTerm, embed, reflect, coeC, merge-ρ, …
  open ≈R

  -- Front-end free category: HomTerm over GenF, qualified `F`.
  private module F = FreeMonoidalHelper.Mor Mon X GenF

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
  -- Homomorphic on all constructors; a box generator gets conjugated by
  -- the canonical iso.
  ------------------------------------------------------------------------

  inj : ∀ {A B} → HomTerm A B → F.HomTerm A B
  inj (var (box (mk {Y} {Z} g))) = F._∘_ (flat⇒ Z) (F._∘_ (F.var g) (flat⇐ Y))
  inj id         = F.id
  inj (g ∘ f)    = F._∘_ (inj g) (inj f)
  inj (f ⊗₁ g)   = F._⊗₁_ (inj f) (inj g)
  inj λ⇒         = F.λ⇒
  inj λ⇐         = F.λ⇐
  inj ρ⇒         = F.ρ⇒
  inj ρ⇐         = F.ρ⇐
  inj α⇒         = F.α⇒
  inj α⇐         = F.α⇐

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

  -- the two opposite coercions of identities cancel.
  coeCF-inv : ∀ {p q} (e : p ≡ q)
            → F._∘_ (coeCF (sym e) (F.id {wires q})) (coeCF e (F.id {wires p}))
              F.≈Term F.id
  coeCF-inv refl = F.idˡ

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
  -- Front-end reflection: structural constructors die into (casted) idʷ.
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
  reflectF (F.var g)            = boxʷ (mk g)
  reflectF F.id                 = idʷ
  reflectF (F._∘_ g f)          = reflectF g ∘ʷ reflectF f
  reflectF (F._⊗₁_ f g)         = reflectF f ⊗ʷ reflectF g
  reflectF (F.λ⇒ {A})           = idʷ
  reflectF (F.λ⇐ {A})           = idʷ
  reflectF (F.ρ⇒ {A})           = castʷ refl (++-identityʳ (flatten A)) idʷ
  reflectF (F.ρ⇐ {A})           = castʷ refl (sym (++-identityʳ (flatten A))) idʷ
  reflectF (F.α⇒ {A} {B} {C})   = castʷ refl (++-assoc (flatten A) (flatten B) (flatten C)) idʷ
  reflectF (F.α⇐ {A} {B} {C})   = castʷ refl (sym (++-assoc (flatten A) (flatten B) (flatten C))) idʷ

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
  -- The decision procedure: reflect both sides to DiagU, decide NF
  -- equality, chain the reflect-soundness witnesses, cancel through the
  -- bridge.  `Decide` needs decidable equality on labels and on the
  -- (Σ-packaged) front-end generators.
  ------------------------------------------------------------------------

  GenΣ : Set
  GenΣ = Σ[ Y ∈ ObjTerm ] Σ[ Z ∈ ObjTerm ] GenF Y Z

  module Decide
    (_≟G_ : DecidableEquality GenΣ)
    (rank : GenΣ → ℕ)   -- tiebreak key for ambiguous (mutually-fitting) pairs;
                        -- for a Fin-indexed signature, `toℕ` of the index.
    where

    private module SC = SolverCompare Mon _≟X_ MorW

    -- decidable equality on the Σ-packaged wire-level generators, derived
    -- from the front-end one (mk is injective on the ObjTerm triple).
    private
      _≟W_ : DecidableEquality SC.Gen
      (_ , _ , mk {Y} {Z} g) ≟W (_ , _ , mk {Y'} {Z'} g')
        with (Y , Z , g) ≟G (Y' , Z' , g')
      ... | yes refl = yes refl
      ... | no ¬p    = no λ { refl → ¬p refl }

    open SC.Decide _≟W_ using (_≈NF_; _≟DiagU_; ≈NF⇒≡)

    open Normalize Mon {X} _≟X_ MorW using
      ( castW; castW-∘; castW-irr
      ; substDiagU; substDiagU-out; ⟦substDiagU⟧
      ; LeftFit; leftFit
      ; dInput; dSwapped; dInput-out; dSwapped-out; diagU-swap-soundD; domeq
      ; module SortD )
    open SortD using (leftFit?)

    ------------------------------------------------------------------------
    -- A generic one-bubble interchange step on a clean DiagU.
    --
    -- The SortD engine (`dInput`/`dSwapped`/`diagU-swap-soundD`) consumes the
    -- head pair as explicit offsets/boxes because a two-layer head of an
    -- ABSTRACT `DiagU n` cannot be destructured (the inter-layer index
    -- `pre ++ (b ++ suf)` is `++`-rigid, so unification is stuck).  We dodge
    -- the obstruction by GENERALIZING the inner index to a fresh variable `m`
    -- carried with a propositional wiring equality `meq` — the inner cons
    -- then matches at a variable index, and `meq` is never matched, only
    -- discharged against `domeq` by the Hedberg UIP on wire lists.
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

      -- fire one genuine swap on a recognised out-of-order head pair.
      fire : ∀ {ax bx ay by} {px sx py sy : List X}
             {fx : MorW ax bx} {fy : MorW ay by}
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
          dIn = dInput fit' rest'          -- = substDiagU eᵒ dBody, definitionally
          dSw = dSwapped fit' rest'
          d' : DiagU ((P ++ (ay ++ mid)) ++ (ax ++ s))
          d' = substDiagU (sym eᵒ) dSw
          e₁ = sym (substDiagU-out eᵒ dBody)               -- out dBody ≡ out dIn
          q  = trans (dInput-out fit' rest') (sym (dSwapped-out fit' rest'))
          e₃ = sym (substDiagU-out (sym eᵒ) dSw)           -- out dSw ≡ out d'
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

      -- the wire-level generator's tiebreak key.
      rankW : ∀ {a b} → MorW a b → ℕ
      rankW (mk {Y} {Z} g) = rank (Y , Z , g)

      -- a fit is AMBIGUOUS when the reverse pair would also fit
      -- (mid ≡ [] ∧ by ≡ [] ∧ ax ≡ []): firing it unconditionally would
      -- oscillate, so such pairs are ordered by `rank` instead.
      ambiguous? : List X → List X → List X → Bool
      ambiguous? [] [] [] = true
      ambiguous? _  _  _  = false

      -- destructure the SECOND layer at a generalized (variable) index.
      go : ∀ {ax bx} (px sx : List X) (fx : MorW ax bx)
           {m : List X} (rest : DiagU m) (meq : px ++ (bx ++ sx) ≡ m)
         → Maybe (SwapRes (px ▸ sx ∷ fx ⟨ substDiagU (sym meq) rest ⟩))
      go px sx fx ([]_ m) meq = nothing
      go {ax} {bx} px sx fx (_▸_∷_⟨_⟩ {ay} {by} py sy fy rest') meq
        with leftFit? px sx py sy fx fy
      ... | nothing  = nothing
      ... | just fit
        with ambiguous? ax by (LeftFit.mid fit) | rankW fy <ᵇ rankW fx
      ...   | false | _     = just (fire fit rest' meq)
      ...   | true  | true  = just (fire fit rest' meq)
      ...   | true  | false = nothing

    -- one bubble step on the HEAD pair, or `nothing` when it is not an
    -- out-of-order independent pair (or fewer than two layers).
    swap2? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    swap2? ([]_ n)                = nothing
    swap2? (px ▸ sx ∷ fx ⟨ rest ⟩) = go px sx fx rest refl

    private
      -- lift a tail swap-result under a layer (same input index, so the
      -- rebuild is direct — no transport needed).
      lift∷ : ∀ {a b} (px sx : List X) (fx : MorW a b)
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

    -- one swap at the FIRST applicable position: try the head pair, else
    -- recurse into the tail.  (The recursion is unobstructed: only nested
    -- PATTERN-MATCHING of a two-layer head is index-stuck; rebuilding a
    -- layer over a normalized tail keeps the input index on the nose.)
    step? : ∀ {n} (d : DiagU n) → Maybe (SwapRes d)
    step? ([]_ n) = nothing
    step? (px ▸ sx ∷ fx ⟨ rest ⟩) with go px sx fx rest refl
    ... | just r  = just r
    ... | nothing with step? rest
    ...   | nothing                  = nothing
    ...   | just (rest' , oeq , snd) =
            just (px ▸ sx ∷ fx ⟨ rest' ⟩ , oeq , lift∷ px sx fx oeq snd)

    -- fuel-bounded bubble sort: fire the first applicable swap, repeat.
    -- On CONCRETE input the `substDiagU` casts inside each swap result
    -- compute away (their equalities reduce to refl), so successive steps
    -- keep firing; soundness is unconditional whatever the fuel.
    normFuel : ∀ {n} → ℕ → (d : DiagU n) → SwapRes d
    normFuel nzero    d = d , refl , idˡ
    normFuel (nsuc k) d with step? d
    ... | nothing               = d , refl , idˡ
    ... | just (d' , oeq , snd) with normFuel k d'
    ...   | (d'' , oeq' , snd') =
            d'' , trans oeq oeq' , swapTrans oeq oeq' snd snd'

    -- layer count, and the worst-case bubble budget (≥ #inversions).
    depth : ∀ {n} → DiagU n → ℕ
    depth ([]_ n)            = nzero
    depth (_ ▸ _ ∷ _ ⟨ d ⟩) = nsuc (depth d)

    norm : ∀ {n} (d : DiagU n) → SwapRes d
    norm d = normFuel (nsuc (depth d * depth d)) d

    ------------------------------------------------------------------------
    -- The wire-level decision: reflect both sides to DiagU, normalize,
    -- compare, chain the soundness witnesses.
    ------------------------------------------------------------------------

    decide?W : ∀ {n m} (f g : WTerm n m) → Maybe (embed f ≈Term embed g)
    decide?W {n} {m} f g with norm (reflect f) | norm (reflect g)
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

    -- front-end decision: a hit is a genuine `_≈Term_` of the free
    -- monoidal category over the ObjTerm-arity generators.
    decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r)
    decide?F l r with decide?W (reflectF l) (reflectF r)
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
    -- Term-level FOCUSING (the Mon analogue of the SMC solver's `Carve`):
    -- find a frame  `post ∘ (id {k} ⊗ (– ⊗ id {m})) ∘ pre`  exhibiting an
    -- occurrence of a redex `lᵗ` inside `s`.  The symmetric version routes
    -- a left-factor wire past the redex with σ; the Mon fragment has no
    -- braiding, so the frame is TWO-SIDED (pads on both sides of the hole).
    -- The search is unverified: a `focusAtₙ` hit is certified downstream by
    -- `decide?F s (plug foc lᵗ)`, so soundness rests solely on the solver.
    ------------------------------------------------------------------------

    -- decidable equality on front-end objects (no-K style: the negative
    -- cases go through injectivity lemmas, never a refl-match at a
    -- partially-forced index).
    private
      ⊗₀-inj₁ : ∀ {a b a' b'} → (a ⊗₀ b) ≡ (a' ⊗₀ b') → a ≡ a'
      ⊗₀-inj₁ refl = refl
      ⊗₀-inj₂ : ∀ {a b a' b'} → (a ⊗₀ b) ≡ (a' ⊗₀ b') → b ≡ b'
      ⊗₀-inj₂ refl = refl
      Var-inj : ∀ {x y} → Var x ≡ Var y → x ≡ y
      Var-inj refl = refl

    _≟O_ : DecidableEquality ObjTerm
    unit      ≟O unit       = yes refl
    unit      ≟O (_ ⊗₀ _)   = no λ ()
    unit      ≟O Var _      = no λ ()
    (_ ⊗₀ _)  ≟O unit       = no λ ()
    (a ⊗₀ b)  ≟O (a' ⊗₀ b') with a ≟O a' | b ≟O b'
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ eq → ¬p (⊗₀-inj₁ eq)
    ... | yes _    | no ¬q    = no λ eq → ¬q (⊗₀-inj₂ eq)
    (_ ⊗₀ _)  ≟O Var _      = no λ ()
    Var _     ≟O unit       = no λ ()
    Var _     ≟O (_ ⊗₀ _)   = no λ ()
    Var x     ≟O Var y      with x ≟X y
    ... | yes refl = yes refl
    ... | no ¬p    = no λ eq → ¬p (Var-inj eq)

    -- a focus: the two pad objects and the two context terms.
    Foc : (A B P Q : ObjTerm) → Set
    Foc A B P Q = Σ[ k ∈ ObjTerm ] Σ[ m ∈ ObjTerm ]
                    (F.HomTerm A (k ⊗₀ (P ⊗₀ m)) × F.HomTerm (k ⊗₀ (Q ⊗₀ m)) B)

    -- plug a morphism into the frame of a focus.
    plug : ∀ {A B P Q} → Foc A B P Q → F.HomTerm P Q → F.HomTerm A B
    plug (k , m , pre , post) mid =
      F._∘_ post (F._∘_ (F._⊗₁_ F.id (F._⊗₁_ mid F.id)) pre)

    private
      -- leaf: the whole of `s` is the redex (up to the solver).
      leaf-try : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → Maybe (Foc A B P Q)
      leaf-try {A} {B} {P} {Q} s lᵗ with A ≟O P | B ≟O Q
      ... | yes refl | yes refl with decide?F s lᵗ
      ...   | just _  = just (unit , unit , F._∘_ F.λ⇐ F.ρ⇐ , F._∘_ F.ρ⇒ F.λ⇒)
      ...   | nothing = nothing
      leaf-try _ _ | _ | _ = nothing

    -- enumerate all focus positions: whole-term first, then — for `∘` — the
    -- first-applied operand's positions before the second's, and — for `⊗` —
    -- the left factor's before the right's.
    focusAll : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → List (Foc A B P Q)

    private
      go-all : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → List (Foc A B P Q)
      go-all (F._∘_ g f) lᵗ =
           map (λ { (k , m , pre , post) → (k , m , pre , F._∘_ g post) })
               (focusAll f lᵗ)
        ++ map (λ { (k , m , pre , post) → (k , m , F._∘_ pre f , post) })
               (focusAll g lᵗ)
      go-all (F._⊗₁_ {A = A₁} {C = A₂} a b) lᵗ =
           map (λ { (k , m , pre , post) →                       -- redex in a
                  ( k , m ⊗₀ A₂
                  , F._∘_ (F._⊗₁_ F.id F.α⇒) (F._∘_ F.α⇒ (F._⊗₁_ pre F.id))
                  , F._∘_ (F._⊗₁_ post b) (F._∘_ F.α⇐ (F._⊗₁_ F.id F.α⇐)) ) })
               (focusAll a lᵗ)
        ++ map (λ { (k , m , pre , post) →                       -- redex in b
                  ( A₁ ⊗₀ k , m
                  , F._∘_ F.α⇐ (F._⊗₁_ F.id pre)
                  , F._∘_ (F._⊗₁_ a post) F.α⇒ ) })
               (focusAll b lᵗ)
      go-all _ _ = []

    focusAll s lᵗ with leaf-try s lᵗ
    ... | just r  = r ∷ go-all s lᵗ
    ... | nothing = go-all s lᵗ

    private
      lookupMaybe : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
      lookupMaybe []       _         = nothing
      lookupMaybe (x ∷ _)  nzero     = just x
      lookupMaybe (_ ∷ xs) (nsuc n)  = lookupMaybe xs n

    -- the n-th focus position (0-based, in the order above).
    focusAtₙ : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → ℕ → Maybe (Foc A B P Q)
    focusAtₙ s lᵗ n = lookupMaybe (focusAll s lᵗ) n

    -- extract a focus from a computed hit.
    fromHit : ∀ {a} {A : Set a} (x : Maybe A) → IsJust x → A
    fromHit (just a) _ = a

    ------------------------------------------------------------------------
    -- Transport into an arbitrary target monoidal category, along the free
    -- functor at the ObjTerm-arity generators.  The interpretation is
    -- definitional on every term constructor, so `solveMor!`'s equation
    -- reads in the target's own vocabulary.
    ------------------------------------------------------------------------

    module Into
      {o ℓ e : Level}
      (C : MonoidalCategory o ℓ e)
      (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
      where

      private
        dF : FreeMonoidalData
        dF = record { v = Mon ; X = X ; mor = GenF }

        ⟦v⟧F : ⟦ Mon ⟧ᵥ {o} {ℓ} {e}
        ⟦v⟧F = record
          { C = C .MonoidalCategory.U
          ; Monoidal-C = C .MonoidalCategory.monoidal
          ; Symmetric-C = λ where ⦃ () ⦄
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
        -- sides are interpretations of front-end terms.
        solveMor! : ∀ {Y Z} (l r : F.HomTerm Y Z)
                    {hit : IsJust (decide?F l r)}
                  → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
        solveMor! l r {hit} = ⟦⟧-resp-≈ (solveTerm! l r {hit})

        ------------------------------------------------------------------------
        -- Diagrammatic REWRITING in C (the Mon analogue of the SMC solver's
        -- `rewriteH!`/`rewriteAutoₙ!`).  A *rule* is any C-equation
        -- `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁` between interpretations of front-end terms —
        -- definitionally whatever raw C-equation the caller has (a generator
        -- law, an opaque-iso cancellation, an induction hypothesis, …).  The
        -- rule fires inside the two-sided frame
        --     post ∘ (id {k} ⊗ (– ⊗ id {m})) ∘ pre
        -- and the solver reconciles the caller's terms with the frames, so
        -- only the rule itself crosses the congruence.
        ------------------------------------------------------------------------

        private
          module MCc = MonoidalCategory C

          -- transport a rule across the frame of a focus, by congruence.
          plugCong : ∀ {A B P Q} (foc : Foc A B P Q) (l r : F.HomTerm P Q)
                   → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
                   → C .MonoidalCategory.U [ ⟦ plug foc l ⟧₁ ≈ ⟦ plug foc r ⟧₁ ]
          plugCong (k , m , pre , post) l r rule =
            MCc.∘-resp-≈ʳ (MCc.∘-resp-≈ˡ
              (MCc.⊗.F-resp-≈ (MCc.Equiv.refl , MCc.⊗.F-resp-≈ (rule , MCc.Equiv.refl))))

        -- manual position: the caller supplies the frame (`pre`/`post`).
        rewriteMor!
          : ∀ {A B P Q k m}
          → (s t : F.HomTerm A B)
          → (pre : F.HomTerm A (k ⊗₀ (P ⊗₀ m))) (post : F.HomTerm (k ⊗₀ (Q ⊗₀ m)) B)
          → (lᵗ rᵗ : F.HomTerm P Q)
          → C .MonoidalCategory.U [ ⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁ ]
          → {h₁ : IsJust (decide?F s (plug (k , m , pre , post) lᵗ))}
          → {h₂ : IsJust (decide?F t (plug (k , m , pre , post) rᵗ))}
          → C .MonoidalCategory.U [ ⟦ s ⟧₁ ≈ ⟦ t ⟧₁ ]
        rewriteMor! {k = k} {m = m} s t pre post lᵗ rᵗ rule {h₁} {h₂} =
          MCc.Equiv.trans (solveMor! s (plug foc lᵗ) {h₁})
            (MCc.Equiv.trans (plugCong foc lᵗ rᵗ rule)
              (MCc.Equiv.sym (solveMor! t (plug foc rᵗ) {h₂})))
          where foc = (k , m , pre , post)

        -- automatic position: the n-th occurrence of `lᵗ` in `s` is located
        -- by `focusAtₙ`; both endpoints are stated by the caller, so the
        -- located frame never appears in the exposed type.
        rewriteMorₙ!
          : ∀ {A B P Q}
          → (s t : F.HomTerm A B) (lᵗ rᵗ : F.HomTerm P Q) (n : ℕ)
          → C .MonoidalCategory.U [ ⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁ ]
          → {found : IsJust (focusAtₙ s lᵗ n)}
          → {h₁ : IsJust (decide?F s (plug (fromHit (focusAtₙ s lᵗ n) found) lᵗ))}
          → {h₂ : IsJust (decide?F t (plug (fromHit (focusAtₙ s lᵗ n) found) rᵗ))}
          → C .MonoidalCategory.U [ ⟦ s ⟧₁ ≈ ⟦ t ⟧₁ ]
        rewriteMorₙ! s t lᵗ rᵗ n rule {found} {h₁} {h₂} =
          MCc.Equiv.trans (solveMor! s (plug foc lᵗ) {h₁})
            (MCc.Equiv.trans (plugCong foc lᵗ rᵗ rule)
              (MCc.Equiv.sym (solveMor! t (plug foc rᵗ) {h₂})))
          where foc = fromHit (focusAtₙ s lᵗ n) found

        -- the first occurrence.
        rewriteMorAuto!
          : ∀ {A B P Q}
          → (s t : F.HomTerm A B) (lᵗ rᵗ : F.HomTerm P Q)
          → C .MonoidalCategory.U [ ⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁ ]
          → {found : IsJust (focusAtₙ s lᵗ 0)}
          → {h₁ : IsJust (decide?F s (plug (fromHit (focusAtₙ s lᵗ 0) found) lᵗ))}
          → {h₂ : IsJust (decide?F t (plug (fromHit (focusAtₙ s lᵗ 0) found) rᵗ))}
          → C .MonoidalCategory.U [ ⟦ s ⟧₁ ≈ ⟦ t ⟧₁ ]
        rewriteMorAuto! s t lᵗ rᵗ rule {found} {h₁} {h₂} =
          rewriteMorₙ! s t lᵗ rᵗ 0 rule {found} {h₁} {h₂}

--------------------------------------------------------------------------------
-- `FinSetup`: the call-site convenience wrapper (the analogue of the
-- hypergraph solver's `Coherence.Symmetric.Setup`).  From
--
--   * a target monoidal category `C`,
--   * a `Vec` of object atoms (the opaque objects of the goal), and
--   * a Fin-indexed `arity` table of generator arities (ObjTerms over the
--     atom indices),
--
-- it assembles the signature, decidable equalities and the rank tiebreak,
-- exposing the term language `S`, the generator embedding `gen`, the
-- object interpretation `⟦_⟧ₒ`, and — after `WithGen` supplies the
-- generator interpretations — the `solveMor!` entry point.
--
-- Typical use, discharging a C-equation between composites of opaque
-- morphisms and structural isos (cf. SolverFrontendTests.Target):
--
--   open FinSetup C (A ∷ B ∷ []) (λ { zero → Var zero , Var zero ; … })
--   open WithGen  (λ { (genS zero) → f ; … })
--   goal = solveMor! lhsᵗ rhsᵗ
--------------------------------------------------------------------------------

module FinSetup
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper Mon (Fin nA) public
    using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  module Sig {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

    data GenS : ObjTerm → ObjTerm → Set where
      genS : (i : Fin nG) → GenS (proj₁ (arity i)) (proj₂ (arity i))

    -- the front-end term language over the assembled signature.
    module S = FreeMonoidalHelper.Mor Mon (Fin nA) GenS

    gen : (i : Fin nG) → S.HomTerm (proj₁ (arity i)) (proj₂ (arity i))
    gen i = S.var (genS i)

    open Frontend {Fin nA} _≟Fin_ GenS using (GenΣ; module Decide)

    private
      _≟G_ : DecidableEquality GenΣ
      (_ , _ , genS i) ≟G (_ , _ , genS j) with i ≟Fin j
      ... | yes refl = yes refl
      ... | no ¬p    = no λ where refl → ¬p refl

      rankS : GenΣ → ℕ
      rankS (_ , _ , genS i) = toℕ i

    open Decide _≟G_ rankS public
      using (decide?F; IsJust; solveTerm!; module Into
            ; Foc; plug; focusAll; focusAtₙ; fromHit; _≟O_)
    open Into C (lookup vars) public
