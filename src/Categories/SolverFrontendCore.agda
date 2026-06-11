{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The shared CORE of the two solver front-ends.
--
-- `Categories.SolverFrontend` (Mon) and `Categories.SolverSigmaFrontend`
-- (Symm) are ~80% rename-identical: both flatten ObjTerm-arity generators
-- to a wire-level family, inject the wire-level free category back into the
-- front-end one, and cancel through the canonical structural iso
-- `flat⇒ / flat⇐`.  This module factors that shared material out, generic
-- in the `Variant`:
--
--   MaybeHit
--     `IsJust` / `fromHit` — the computing hit-witness used by both
--     `Decide` layers (must reduce on `just`/`nothing` at test sites).
--
--   FCore v GenF
--     Engine-free layer: `flatten`, the wire-level generator family `MorW`
--     (identical data in both front-ends), `GenΣ`, the F-side reasoning
--     module `F≈R`, and the Σ-packaged decidable-equality / rank helpers
--     consumed by the `Decide` layers.
--
--   FBridge v _≟X_ GenF MorEng ⟦box⟧
--     Engine-generic layer.  `MorEng` is the ENGINE's diagram-level
--     generator family (`MorW` for Mon, `MorS MorW` for Symm) and `⟦box⟧`
--     its interpretation; the module opens `WireSig` / `UntypedI` /
--     `ReflectI` at exactly these arguments, so `wires`, `mor`, `merge`,
--     `split`, `coeC`, `WTerm`, `embed`, … are THE SAME symbols as in the
--     front-ends' engine opens — every definitional unfolding available in
--     the front-ends is available here.  Body: `mergeF`/`splitF`,
--     `flat⇒`/`flat⇐`, `coeCF` + lemmas, `coe-coe`, `castʷ`/`embed-castʷ`,
--     `fwd-λ`, `flipF`.
--
--   FBridge.WithInj injBox reflectVar reflectσ
--     The variant-specific clauses of `inj` (the box case) and `reflectF`
--     (the var and σ cases) are parameters; everything else is generic —
--     the σ clauses of `inj`, `inj-resp-≈` and `reflectF` live HERE,
--     instance-gated on `⦃ Symm ≤ v ⦄` exactly like `HomTerm`'s σ
--     constructor (for Mon they are dead code: `Symm ≤ Mon` is empty).
--     Body: `inj`, `inj-resp-≈`, `inj-merge`/`inj-split`/`inj-coeC`,
--     `reflectF`, the transferred lemmas (`splitF∘mergeF`, `mergeF-ρ`,
--     `mergeF-assoc`), `flat⇐∘flat⇒`, `cast-half`, `fwd-ρ`/`fwd-α`.
--
--   FBridge.WithInj.Bridge inj-embed-var bridge-σ
--     The soundness bridge `bridgeF` and the cancellation `solveF`.  The
--     two parameters are the only non-generic ingredients: the var case's
--     unfolding equation (`refl` in both front-ends — `inj ∘ embed ∘
--     reflectVar` is definitionally the conjugated generator) and the σ
--     bridge law (a short braiding-naturality proof in Symm; absurd on the
--     empty `Symm ≤ Mon` in Mon).
--
--   IntoCore v GenF C SymC ⟦⟧₀
--     The shared free-functor transport plumbing wrapped by both front-ends'
--     `Into` layers: interpret the wire-level free category into a target
--     monoidal (Mon) or symmetric-monoidal (Symm, via the instance-gated
--     `SymC : ⦃ Symm ≤ v ⦄ → Symmetric …`) category along an object
--     assignment `⟦⟧₀`.
--
-- (`inj` is NOT an instance of `FreeMonoidal`'s `FreeFunctor`/`⟦_⟧₁`: that
-- functor's object action is the recursive `⟦_⟧₀`, never the literal identity
-- on `ObjTerm`, so the index-preserving `inj` and its on-the-nose
-- `inj-merge`/`inj-split`/`inj-coeC` `≡`-lemmas would drown in object
-- coercions.  Hence the dedicated, definitionally transparent `inj`.)
--
-- DEFINITIONAL-EQUALITY DISCIPLINE: everything computation-relevant
-- (`flatten`, `reflectF`, `castʷ`, `IsJust`, the `Decide`-layer equality
-- helpers) is defined by recursion HERE and parametrized only by neutral
-- data, so it reduces on constructors once the front-ends instantiate the
-- modules with concrete arguments — the test suites' `IsJust (decide? …)`
-- hits compute exactly as before.
--
-- Hole-free, postulate-free, --safe --without-K.
--------------------------------------------------------------------------------

module Categories.SolverFrontendCore where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Unit using (⊤)
open import Function using (case_of_)
open import Level using (Level)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Monoidal using (MonoidalCategory)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.DiagramRewriteUntyped using (module WireSig; module UntypedI)
open import Categories.FreeMonoidal
open import Categories.SolverReflect using (module ReflectI)

------------------------------------------------------------------------
-- The computing hit-witness (shared by both Decide layers).
------------------------------------------------------------------------

module MaybeHit where

  -- normalizes to ⊤ exactly on a solver hit, so the implicit is
  -- auto-discharged at concrete test sites.
  IsJust : ∀ {a} {A : Set a} → Maybe A → Set
  IsJust (just _) = ⊤
  IsJust nothing  = ⊥

  -- extract the value of a computed hit (a solver witness, a focus, …).
  fromHit : ∀ {a} {A : Set a} (x : Maybe A) → IsJust x → A
  fromHit (just a) _ = a

------------------------------------------------------------------------
-- FCore: the engine-free layer.
------------------------------------------------------------------------

module FCore
  (v : Variant)
  {X : Set}
  (let open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  private module F = FreeMonoidalHelper.Mor v X GenF

  ------------------------------------------------------------------------
  -- Object flattening and the wire-level generator family.
  ------------------------------------------------------------------------

  flatten : ObjTerm → List X
  flatten unit      = []
  flatten (Y ⊗₀ Z) = flatten Y ++ flatten Z
  flatten (Var x)   = x ∷ []

  data MorW : List X → List X → Set where
    mk : ∀ {Y Z} → GenF Y Z → MorW (flatten Y) (flatten Z)

  -- the Σ-packaged front-end generators (for caller-supplied DecEq/rank).
  GenΣ : Set
  GenΣ = Σ[ Y ∈ ObjTerm ] Σ[ Z ∈ ObjTerm ] GenF Y Z

  -- decidable equality on the Σ-packaged wire-level generators, derived
  -- from the front-end one (mk is injective on the ObjTerm triple).
  decMorW : DecidableEquality GenΣ
          → DecidableEquality (Σ[ a ∈ List X ] Σ[ b ∈ List X ] MorW a b)
  decMorW _≟G_ (_ , _ , mk {Y} {Z} g) (_ , _ , mk {Y'} {Z'} g') =
    case (Y , Z , g) ≟G (Y' , Z' , g') of λ where
      (yes refl) → yes refl
      (no ¬p)    → no λ { refl → ¬p refl }

  -- the wire-level generator's tiebreak key, from the front-end one.
  rankMorW : (GenΣ → ℕ) → ∀ {a b} → MorW a b → ℕ
  rankMorW rank (mk {Y} {Z} g) = rank (Y , Z , g)

  ------------------------------------------------------------------------
  -- F-side equational reasoning (mirror of the wire-level ≈R).
  ------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- FBridge: the engine-generic layer.
------------------------------------------------------------------------

module FBridge
  (v : Variant)
  {X : Set}
  (_≟X_ : DecidableEquality X)
  (let open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var))
  (GenF : ObjTerm → ObjTerm → Set)
  (MorEng : List X → List X → Set)
  (let open WireSig v {X} MorEng using () renaming (wires to wires↑; mor to mor↑))
  (let open FreeMonoidalHelper.Mor v X mor↑ using () renaming (HomTerm to HomTerm↑))
  (⟦box⟧ : ∀ {a b} → MorEng a b → HomTerm↑ (wires↑ a) (wires↑ b))
  where

  -- the engine surface, at EXACTLY the front-ends' instantiation — all
  -- names below are the same symbols the front-ends have in scope.
  open WireSig v {X} MorEng using (wires; mor; box; merge; split)
  open UntypedI v {X} MorEng ⟦box⟧ using (split∘merge)
  open ReflectI v {X} _≟X_ MorEng ⟦box⟧
    using (WTerm; boxʷ; idʷ; _∘ʷ_; _⊗ʷ_; embed; coeC; coeD; merge-ρ; merge-assoc)

  -- the wire-level free category (unqualified, as in the front-ends).
  open FreeMonoidalHelper.Mor v X mor

  -- the engine-free layer, at the same (v, GenF).
  open FCore v {X = X} GenF using (flatten; module F≈R)
  open F≈R

  -- front-end free category, qualified `F`.
  private module F = FreeMonoidalHelper.Mor v X GenF

  -- stock combinators at the F-side free category (proofs-only, plain
  -- opens: never re-exported).
  open MR F.FreeMonoidal
    using ()
    renaming (pullˡ to pullˡF; cancelˡ to cancelˡF; cancelʳ to cancelʳF;
              cancelInner to cancelInnerF; insertˡ to insertˡF;
              assoc²βε to assoc²βεF)
  open MonR F.Monoidal-FreeMonoidal
    using ()
    renaming (refl⟩∘⟨_ to infixr 4 reflF⟩∘⟨_; _⟩∘⟨refl to infixl 5 _⟩∘F⟨refl;
              ⟺ to ⟺F; _○_ to infixr 3 _○F_;
              _⟩⊗⟨_ to infixr 6 _⟩⊗F⟨_; split₁ˡ to split₁ˡF)

  -- readability aliases (function aliases of the F constructors).  Public:
  -- the front-ends pick them up from here instead of redefining them.
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
  -- F-side coercion along a wire-list equality.
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

  -- the two opposite coercions cancel (UIP-free: by matching e).
  coe-coe : ∀ {A} {p q : List X} (e : p ≡ q) (h : F.HomTerm A (wires p))
          → coeCF (sym e) (coeCF e h) ≡ h
  coe-coe refl h = refl

  ------------------------------------------------------------------------
  -- WTerm casts (the structural constructors of `reflectF` die into these).
  ------------------------------------------------------------------------

  castʷ : ∀ {n n' m m'} → n ≡ n' → m ≡ m' → WTerm n m → WTerm n' m'
  castʷ refl refl t = t

  embed-castʷ : ∀ {n n' m m'} (p : n ≡ n') (q : m ≡ m') (t : WTerm n m)
              → embed (castʷ p q t) ≈Term coeD p (coeC q (embed t))
  embed-castʷ refl refl t = ≈-Term-refl

  ------------------------------------------------------------------------
  -- Forward structural λ-law and the law flipper (engine-independent).
  ------------------------------------------------------------------------

  fwd-λ : ∀ (A : ObjTerm) → flat⇒ (unit ⊗₀ A) F.≈Term flat⇒ A ∘F F.λ⇒
  fwd-λ A = F.λ⇒∘id⊗f≈f∘λ⇒

  -- flip a forward law to its inverse structural morphism.
  flipF : ∀ {P Q} {p q : List X} (e : p ≡ q)
            (h⇒P : F.HomTerm P (wires p)) (h⇒Q : F.HomTerm Q (wires q))
            {c : F.HomTerm P Q} {c⁻¹ : F.HomTerm Q P}
        → c ∘F c⁻¹ F.≈Term idF
        → coeCF e h⇒P F.≈Term h⇒Q ∘F c
        → coeCF (sym e) h⇒Q F.≈Term h⇒P ∘F c⁻¹
  flipF e h⇒P h⇒Q {c} {c⁻¹} iso fwd = F.≈-Term-sym (beginF
    h⇒P ∘F c⁻¹
      ≈F⟨ F.≡⇒≈Term (coe-coe e h⇒P) ⟩∘F⟨refl ⟨
    coeCF (sym e) (coeCF e h⇒P) ∘F c⁻¹
      ≈F⟨ (coeCF-resp (sym e) fwd ○F coeCF-∘ˡ (sym e) h⇒Q c) ⟩∘F⟨refl ⟩
    (coeCF (sym e) h⇒Q ∘F c) ∘F c⁻¹
      ≈F⟨ cancelʳF iso ⟩
    coeCF (sym e) h⇒Q ∎F)

  ------------------------------------------------------------------------
  -- WithInj: the injection / reflection layer.  The box clause of `inj`
  -- and the var / σ clauses of `reflectF` are the parameters; the σ
  -- clauses of `inj` / `inj-resp-≈` are generic (instance-gated).
  ------------------------------------------------------------------------

  module WithInj
    (injBox : ∀ {a b} → MorEng a b → F.HomTerm (wires a) (wires b))
    (reflectVar : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z))
    (reflectσ : ∀ ⦃ s : Symm ≤ v ⦄ (A B : ObjTerm)
              → WTerm (flatten A ++ flatten B) (flatten B ++ flatten A))
    where

    ----------------------------------------------------------------------
    -- `inj`: the wire-level free category into the front-end free
    -- category.  Homomorphic on all constructors (σ ↦ σ); a box generator
    -- goes through the caller's `injBox`.
    ----------------------------------------------------------------------

    inj : ∀ {A B} → HomTerm A B → F.HomTerm A B
    inj (var (box w)) = injBox w
    inj id            = F.id
    inj (g ∘ f)       = F._∘_ (inj g) (inj f)
    inj (f ⊗₁ g)      = F._⊗₁_ (inj f) (inj g)
    inj λ⇒            = F.λ⇒
    inj λ⇐            = F.λ⇐
    inj ρ⇒            = F.ρ⇒
    inj ρ⇐            = F.ρ⇐
    inj α⇒            = F.α⇒
    inj α⇐            = F.α⇐
    inj (σ ⦃ s ⦄)     = F.σ ⦃ s ⦄

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
    inj-resp-≈ (σ∘σ≈id ⦃ s ⦄)          = F.σ∘σ≈id ⦃ s ⦄
    inj-resp-≈ (σ∘[f⊗g]≈[g⊗f]∘σ ⦃ s ⦄) = F.σ∘[f⊗g]≈[g⊗f]∘σ ⦃ s ⦄
    inj-resp-≈ (hexagon ⦃ s ⦄)         = F.hexagon ⦃ s ⦄

    -- inj maps the wire-level merge/split to the F-side ones, on the nose.
    inj-merge : ∀ (a : List X) {suf} → inj (merge a {suf}) ≡ mergeF a {suf}
    inj-merge []      = refl
    inj-merge (x ∷ a) = cong (λ h → F._∘_ (F._⊗₁_ F.id h) F.α⇒) (inj-merge a)

    inj-split : ∀ (a : List X) {suf} → inj (split a {suf}) ≡ splitF a {suf}
    inj-split []      = refl
    inj-split (x ∷ a) = cong (λ h → F._∘_ F.α⇐ (F._⊗₁_ F.id h)) (inj-split a)

    -- inj commutes with the wire-level coercion (definitional on refl).
    inj-coeC : ∀ {A p q} (e : p ≡ q) (h : HomTerm A (wires p))
             → inj (coeC e h) ≡ coeCF e (inj h)
    inj-coeC refl h = refl

    ----------------------------------------------------------------------
    -- Front-end reflection: structural constructors die into (casted)
    -- idʷ; the var and σ clauses are the caller's.
    ----------------------------------------------------------------------

    reflectF : ∀ {Y Z} → F.HomTerm Y Z → WTerm (flatten Y) (flatten Z)
    reflectF (F.var g)            = reflectVar g
    reflectF F.id                 = idʷ
    reflectF (F._∘_ g f)          = reflectF g ∘ʷ reflectF f
    reflectF (F._⊗₁_ f g)         = reflectF f ⊗ʷ reflectF g
    reflectF (F.λ⇒ {A})           = idʷ
    reflectF (F.λ⇐ {A})           = idʷ
    reflectF (F.ρ⇒ {A})           = castʷ refl (++-identityʳ (flatten A)) idʷ
    reflectF (F.ρ⇐ {A})           = castʷ refl (sym (++-identityʳ (flatten A))) idʷ
    reflectF (F.α⇒ {A} {B} {C})   = castʷ refl (++-assoc (flatten A) (flatten B) (flatten C)) idʷ
    reflectF (F.α⇐ {A} {B} {C})   = castʷ refl (sym (++-assoc (flatten A) (flatten B) (flatten C))) idʷ
    reflectF (F.σ {A} {B} ⦃ s ⦄)  = reflectσ ⦃ s ⦄ A B

    ----------------------------------------------------------------------
    -- Structural lemmas transferred from the wire level along inj.
    ----------------------------------------------------------------------

    splitF∘mergeF : ∀ (a : List X) {suf} → F._∘_ (splitF a {suf}) (mergeF a) F.≈Term F.id
    splitF∘mergeF a {suf} =
      F.≡⇒≈Term (cong₂ F._∘_ (sym (inj-split a {suf})) (sym (inj-merge a {suf})))
      ○F inj-resp-≈ (split∘merge a)

    -- right-unitor coherence on the F-side merge (transfer of merge-ρ).
    mergeF-ρ : ∀ (a : List X)
             → coeCF (++-identityʳ a) (mergeF a {[]}) F.≈Term F.ρ⇒
    mergeF-ρ a =
      F.≡⇒≈Term (trans (cong (coeCF (++-identityʳ a)) (sym (inj-merge a)))
                       (sym (inj-coeC (++-identityʳ a) (merge a {[]}))))
      ○F inj-resp-≈ (merge-ρ a)

    -- merge associativity on the F side (transfer of merge-assoc).
    mergeF-assoc : ∀ (p q r : List X)
      → F._∘_ (mergeF p {q ++ r}) (F._∘_ (F._⊗₁_ (F.id {wires p}) (mergeF q {r})) F.α⇒)
        F.≈Term coeCF (++-assoc p q r)
                  (F._∘_ (mergeF (p ++ q) {r}) (F._⊗₁_ (mergeF p {q}) (F.id {wires r})))
    mergeF-assoc p q r =
      F.≡⇒≈Term (sym lhs-eq) ○F inj-resp-≈ (merge-assoc p q r) ○F F.≡⇒≈Term rhs-eq
      where
        lhs-eq : inj (merge p {q ++ r} ∘ (id {wires p} ⊗₁ merge q {r}) ∘ α⇒)
               ≡ F._∘_ (mergeF p {q ++ r})
                   (F._∘_ (F._⊗₁_ (F.id {wires p}) (mergeF q {r})) F.α⇒)
        lhs-eq rewrite inj-merge p {q ++ r} | inj-merge q {r} = refl
        rhs-eq : inj (coeC (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r})))
               ≡ coeCF (++-assoc p q r)
                   (F._∘_ (mergeF (p ++ q) {r}) (F._⊗₁_ (mergeF p {q}) (F.id {wires r})))
        rhs-eq rewrite inj-coeC (++-assoc p q r) (merge (p ++ q) {r} ∘ (merge p {q} ⊗₁ id {wires r}))
                     | inj-merge (p ++ q) {r} | inj-merge p {q} = refl

    ----------------------------------------------------------------------
    -- The canonical iso laws (only the retraction is needed downstream).
    ----------------------------------------------------------------------

    flat⇐∘flat⇒ : ∀ (Y : ObjTerm) → F._∘_ (flat⇐ Y) (flat⇒ Y) F.≈Term F.id
    flat⇐∘flat⇒ unit = F.idˡ
    flat⇐∘flat⇒ (Y ⊗₀ Z) =
      cancelInnerF (splitF∘mergeF (flatten Y))
      ○F ⟺F F.⊗-∘-dist
      ○F (flat⇐∘flat⇒ Y ⟩⊗F⟨ flat⇐∘flat⇒ Z)
      ○F F.id⊗id≈id
    flat⇐∘flat⇒ (Var x) = F.ρ⇒∘ρ⇐≈id

    ----------------------------------------------------------------------
    -- cast-half: a casted idʷ, embedded and injected, is the F-side
    -- coercion of whatever it is composed onto.
    ----------------------------------------------------------------------

    cast-half : ∀ {P} {p q : List X} (e : p ≡ q) (h : F.HomTerm P (wires p))
              → inj (embed (castʷ refl e (idʷ {p}))) ∘F h F.≈Term coeCF e h
    cast-half {P} {p} {q} e h =
      ((inj-resp-≈ (embed-castʷ refl e idʷ) ○F F.≡⇒≈Term (inj-coeC e id)) ⟩∘F⟨refl)
      ○F ⟺F (coeCF-∘ˡ e idF h)
      ○F coeCF-resp e F.idˡ

    ----------------------------------------------------------------------
    -- Forward structural laws: flattening intertwines the unitors and the
    -- associator.
    ----------------------------------------------------------------------

    fwd-ρ : ∀ (A : ObjTerm)
          → coeCF (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit))
            F.≈Term flat⇒ A ∘F F.ρ⇒
    fwd-ρ A = beginF
      coeCF e (mergeF fA {[]} ∘F (flat⇒ A ⊗F idF))
        ≈F⟨ coeCF-∘ˡ e (mergeF fA {[]}) (flat⇒ A ⊗F idF) ⟩
      coeCF e (mergeF fA {[]}) ∘F (flat⇒ A ⊗F idF)
        ≈F⟨ mergeF-ρ fA ⟩∘F⟨refl ⟩
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
        ≈F⟨ coeCF-resp e ((reflF⟩∘⟨ split₁ˡF) ○F ⟺F F.assoc) ⟩
      coeCF e ((mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C))
        ≈F⟨ coeCF-∘ˡ e (mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ((f⇒A ⊗F f⇒B) ⊗F f⇒C) ⟩
      coeCF e (mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)
        ≈F⟨ mergeF-assoc fA fB fC ⟩∘F⟨refl ⟨
      (mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F F.α⇒)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)
        ≈F⟨ assoc²βεF ⟩
      mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F (F.α⇒ ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)))
        ≈F⟨ reflF⟩∘⟨ ((reflF⟩∘⟨ F.α-comm) ○F pullˡF (⟺F F.⊗-∘-dist ○F (F.idˡ ⟩⊗F⟨ reflF))) ⟩
      mergeF fA {fB ++ fC} ∘F ((f⇒A ⊗F (mergeF fB {fC} ∘F (f⇒B ⊗F f⇒C))) ∘F F.α⇒)
        ≈F⟨ ⟺F F.assoc ⟩
      (mergeF fA {fB ++ fC} ∘F (f⇒A ⊗F (mergeF fB {fC} ∘F (f⇒B ⊗F f⇒C)))) ∘F F.α⇒ ∎F
      where
        fA = flatten A ; fB = flatten B ; fC = flatten C
        e  = ++-assoc fA fB fC
        f⇒A = flat⇒ A ; f⇒B = flat⇒ B ; f⇒C = flat⇒ C

    ----------------------------------------------------------------------
    -- Bridge: the soundness bridge and the cancellation.  The var case's
    -- unfolding equation and the σ bridge law are the parameters (`refl`
    -- resp. a short braiding-naturality proof / absurd in the front-ends).
    ----------------------------------------------------------------------

    module Bridge
      (inj-embed-var : ∀ {Y Z} (g : GenF Y Z)
         → inj (embed (reflectVar g))
           ≡ F._∘_ (flat⇒ Z) (F._∘_ (F.var g) (flat⇐ Y)))
      (bridge-σ : ∀ {A B : ObjTerm} ⦃ s : Symm ≤ v ⦄
         → F._∘_ (inj (embed (reflectσ ⦃ s ⦄ A B))) (flat⇒ (A ⊗₀ B))
           F.≈Term F._∘_ (flat⇒ (B ⊗₀ A)) (F.σ ⦃ s ⦄))
      where

      --------------------------------------------------------------------
      -- bridgeF: the front-end reflection is sound, up to the canonical
      -- iso.
      --------------------------------------------------------------------

      bridgeF : ∀ {Y Z} (t : F.HomTerm Y Z)
              → inj (embed (reflectF t)) ∘F flat⇒ Y F.≈Term flat⇒ Z ∘F t
      bridgeF {Y} {Z} (F.var g) =
        (F.≡⇒≈Term (inj-embed-var g) ⟩∘F⟨refl)
        ○F F.assoc ○F (reflF⟩∘⟨ cancelʳF (flat⇐∘flat⇒ Y))
      bridgeF {Y} {.Y} F.id = F.idˡ ○F ⟺F F.idʳ
      bridgeF {Y} {Z} (F._∘_ {B = M} g f) =
        F.assoc ○F (reflF⟩∘⟨ bridgeF f) ○F pullˡF (bridgeF g) ○F F.assoc
      bridgeF (F._⊗₁_ {A = Y} {B = Z} {C = Y'} {D = Z'} f g) = beginF
        inj (embed (reflectF f ⊗ʷ reflectF g)) ∘F (mergeF fY {fY'} ∘F (f⇒Y ⊗F f⇒Y'))
          ≈F⟨ F.≡⇒≈Term (cong₂ (λ m s → m ∘F ((IF ⊗F IG) ∘F s))
                               (inj-merge fZ {fZ'}) (inj-split fY {fY'})) ⟩∘F⟨refl ⟩
        (mergeF fZ {fZ'} ∘F ((IF ⊗F IG) ∘F splitF fY {fY'})) ∘F (mergeF fY {fY'} ∘F (f⇒Y ⊗F f⇒Y'))
          ≈F⟨ assoc²βεF ○F (reflF⟩∘⟨ (reflF⟩∘⟨ cancelˡF (splitF∘mergeF fY {fY'}))) ⟩
        mergeF fZ {fZ'} ∘F ((IF ⊗F IG) ∘F (f⇒Y ⊗F f⇒Y'))
          ≈F⟨ reflF⟩∘⟨ (⟺F F.⊗-∘-dist ○F (bridgeF f ⟩⊗F⟨ bridgeF g) ○F F.⊗-∘-dist) ⟩
        mergeF fZ {fZ'} ∘F ((f⇒Z ⊗F f⇒Z') ∘F (f ⊗F g))
          ≈F⟨ ⟺F F.assoc ⟩
        (mergeF fZ {fZ'} ∘F (f⇒Z ⊗F f⇒Z')) ∘F (f ⊗F g) ∎F
        where
          fY = flatten Y ; fY' = flatten Y' ; fZ = flatten Z ; fZ' = flatten Z'
          f⇒Y = flat⇒ Y ; f⇒Y' = flat⇒ Y' ; f⇒Z = flat⇒ Z ; f⇒Z' = flat⇒ Z'
          IF = inj (embed (reflectF f))
          IG = inj (embed (reflectF g))
      bridgeF (F.λ⇒ {A}) = F.idˡ ○F fwd-λ A
      bridgeF (F.λ⇐ {A}) =
        F.idˡ ○F flipF refl (flat⇒ (unit ⊗₀ A)) (flat⇒ A) F.λ⇒∘λ⇐≈id (fwd-λ A)
      bridgeF (F.ρ⇒ {A}) =
        cast-half (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit)) ○F fwd-ρ A
      bridgeF (F.ρ⇐ {A}) =
        cast-half (sym (++-identityʳ (flatten A))) (flat⇒ A)
        ○F flipF (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit)) (flat⇒ A)
                 F.ρ⇒∘ρ⇐≈id (fwd-ρ A)
      bridgeF (F.α⇒ {A} {B} {C}) =
        cast-half (++-assoc (flatten A) (flatten B) (flatten C)) (flat⇒ ((A ⊗₀ B) ⊗₀ C))
        ○F fwd-α A B C
      bridgeF (F.α⇐ {A} {B} {C}) =
        cast-half (sym (++-assoc (flatten A) (flatten B) (flatten C))) (flat⇒ (A ⊗₀ (B ⊗₀ C)))
        ○F flipF (++-assoc (flatten A) (flatten B) (flatten C))
                 (flat⇒ ((A ⊗₀ B) ⊗₀ C)) (flat⇒ (A ⊗₀ (B ⊗₀ C)))
                 F.α⇒∘α⇐≈id (fwd-α A B C)
      bridgeF (F.σ {A} {B} ⦃ s ⦄) = bridge-σ {A} {B} ⦃ s ⦄

      --------------------------------------------------------------------
      -- The cancellation: a wire-level equality of the two reflections is
      -- a front-end equality of the original terms.
      --------------------------------------------------------------------

      solveF : ∀ {Y Z} {l r : F.HomTerm Y Z}
             → embed (reflectF l) ≈Term embed (reflectF r)
             → l F.≈Term r
      solveF {Y} {Z} {l} {r} eq =
        insertˡF (flat⇐∘flat⇒ Z) ○F (reflF⟩∘⟨ main) ○F cancelˡF (flat⇐∘flat⇒ Z)
        where
          main : flat⇒ Z ∘F l F.≈Term flat⇒ Z ∘F r
          main = ⟺F (bridgeF l) ○F (inj-resp-≈ eq ⟩∘F⟨refl) ○F bridgeF r

------------------------------------------------------------------------
-- IntoCore: the shared free-functor plumbing of the `Into` transport
-- layers.  Variant-generic via the instance-gated symmetric structure:
-- the Mon front-end passes the vacuous `λ ⦃ () ⦄`, the Symm front-end
-- wraps its caller's `Symmetric` witness.
------------------------------------------------------------------------

module IntoCore
  (v : Variant)
  {X : Set}
  (let open FreeMonoidalHelper v X using (ObjTerm))
  (GenF : ObjTerm → ObjTerm → Set)
  {o ℓ e : Level}
  (C : MonoidalCategory o ℓ e)
  (SymC : ⦃ Symm ≤ v ⦄ → Symmetric (C .MonoidalCategory.monoidal))
  (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
  where

  private
    dF : FreeMonoidalData
    dF = record { v = v ; X = X ; mor = GenF }

    ⟦v⟧F : ⟦ v ⟧ᵥ {o} {ℓ} {e}
    ⟦v⟧F = record
      { C = C .MonoidalCategory.U
      ; Monoidal-C = C .MonoidalCategory.monoidal
      ; Symmetric-C = SymC
      }

  open FreeFunctorHelper dF ⟦v⟧F using (module Go)
  open Go ⟦_⟧ᵖ₀ using () renaming (⟦_⟧₀ to ⟦_⟧ₒ) public

  module WithGenC
    (⟦gen⟧ : ∀ {Y Z} → GenF Y Z
           → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
    where

    private
      ffdF : FreeFunctorData dF {o} {ℓ} {e}
      ffdF = record { ⟦v⟧ = ⟦v⟧F ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦gen⟧ }

    open FreeFunctor {d = dF} ffdF public using (⟦_⟧₁; ⟦⟧-resp-≈)
