{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The shared core of the two solver front-ends.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend.Core where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; lookup; [_]; [_,_])

open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Data.List using (map)
open import Data.List.Properties
open import Data.Vec using (Vec; lookup)

open import Data.Maybe.Ext

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Symmetric

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.Coherence.Monoidal.Reflect
open import Categories.FreeMonoidal

------------------------------------------------------------------------
-- FreeSig: the ObjTerm-arity generator signature shared by the front-end
-- engine modules.
------------------------------------------------------------------------

module FReason
  (v : Variant) {X : Set}
  (let open FreeMonoidalHelper v X)
  (GenF : ObjTerm → ObjTerm → Set)
  where
  open FreeMonoidalHelper.Mor v X GenF public
  open MR FreeMonoidal public
  open MonR Monoidal-FreeMonoidal public using (refl⟩∘⟨_; _⟩∘⟨refl; ⟺; _○_; _⟩⊗⟨_; split₁ˡ)

record FreeSig (v : Variant) {X : Set} : Set₁ where
  open FreeMonoidalHelper v X public using (ObjTerm)
  field GenF : ObjTerm → ObjTerm → Set
  module F = FReason v GenF

------------------------------------------------------------------------
-- FCore: the engine-free layer.
------------------------------------------------------------------------

module FCore (v : Variant) {X : Set}
  (let open FreeMonoidalHelper v X)
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

  -- decidable equality on the Σ-packaged wire-level generators
  instance
    DecEq-MorΣ : ⦃ DecEq GenΣ ⦄ → DecEq (Σ[ a ∈ List X ] Σ[ b ∈ List X ] MorW a b)
    DecEq-MorΣ ._≟_ (_ , _ , mk {Y} {Z} g) (_ , _ , mk {Y'} {Z'} g') =
      case (Y , Z , g) ≟ (Y' , Z' , g') of λ where
        (yes refl) → yes refl
        (no ¬p)    → no λ where refl → ¬p refl

  -- the wire-level generator's tiebreak key, from the front-end one.
  rankMorW : (GenΣ → ℕ) → ∀ {a b} → MorW a b → ℕ
  rankMorW rank (mk {Y} {Z} g) = rank (Y , Z , g)

  ------------------------------------------------------------------------
  -- F-side equational reasoning (mirror of the wire-level ≈R).
  ------------------------------------------------------------------------

  module F≈R where
    open Category.HomReasoning F.FreeMonoidal public using () renaming (begin_ to beginF_; _∎ to _∎F)
    open Category.HomReasoning F.FreeMonoidal
      using () renaming (step-≈-⟩ to libStepF-≈; step-≈-⟨ to libStepF-≈˘)
    infixr 2 stepF-≈ stepF-≈˘
    stepF-≈  = libStepF-≈
    stepF-≈˘ = libStepF-≈˘
    syntax stepF-≈  f gh fg = f ≈F⟨ fg ⟩ gh
    syntax stepF-≈˘ f gh gf = f ≈F⟨ gf ⟨ gh

------------------------------------------------------------------------
-- FinSig: the shared Fin-indexed signature prelude for the call-site
-- wrappers (`FinSetup` / `FinSetupσ`).
--
-- The generator family `GenS` is a `Fin nG`-indexed data family at the
-- ObjTerm arities — crucially NOT parametrized by any target category, so a
-- single signature can be reused across targets.  The decidable equality and
-- rank come for free from `Fin`.
------------------------------------------------------------------------

module FinSig
  (v : Variant)
  {X : Set}
  (let open FreeMonoidalHelper v X)
  {nG : ℕ}
  (arity : Fin nG → ObjTerm × ObjTerm)
  where

  data GenS : ObjTerm → ObjTerm → Set where
    genS : (i : Fin nG) → GenS (proj₁ (arity i)) (proj₂ (arity i))

  -- the front-end term language over the assembled signature.
  module S = FreeMonoidalHelper.Mor v X GenS

  gen : (i : Fin nG) → S.HomTerm (proj₁ (arity i)) (proj₂ (arity i))
  gen i = S.var (genS i)

  open FCore v {X} GenS public using (GenΣ)

  instance
    DecEq-Gen : DecEq GenΣ
    DecEq-Gen ._≟_ (_ , _ , genS i) (_ , _ , genS j) = case i ≟ j of λ where
      (yes refl) → yes refl
      (no ¬p)    → no λ where refl → ¬p refl

  rankS : GenΣ → ℕ
  rankS (_ , _ , genS i) = toℕ i

------------------------------------------------------------------------
-- FBridge: the engine-generic layer.
------------------------------------------------------------------------

module FBridge
  {v : Variant} {X : Set} ⦃ _ : DecEq X ⦄
  (sig : FreeSig v {X})
  (let open FreeSig sig)
  (let open FreeMonoidalHelper v X using (unit; _⊗₀_; Var))
  (E : WireEngine v)
  where

  open WireEngine E renaming (Mor to MorEng)
  open WireSig v {X} MorEng
  open DiagramI E using (castW)
  open ReflectI E

  -- the wire-level free category (unqualified, as in the front-ends).
  open FreeMonoidalHelper.Mor v X mor

  open FCore v {X = X} GenF
  open F≈R

  ------------------------------------------------------------------------
  -- The canonical structural iso Y ≅ wires (flatten Y)
  ------------------------------------------------------------------------

  -- These are generator-independent structural isos (`Y ≅ wires (flatten Y)`),
  -- so mathematically they could sit beside `wires` in `FreeMonoidal`.  They
  -- stay here because they are stated over `flatten : ObjTerm → List X`, a
  -- solver-side notion defined in `FCore` and used only by the front-ends;
  -- `FreeMonoidal` provides just the reverse `wires`.  Relocating them would
  -- drag `flatten` into the widely-imported `FreeMonoidal` for no benefit to
  -- any consumer outside the solver.
  flat⇒ : (Y : ObjTerm) → F.HomTerm Y (wires (flatten Y))
  flat⇒ unit      = F.id
  flat⇒ (Y ⊗₀ Z) = F.merge (flatten Y) F.∘ (flat⇒ Y F.⊗₁ flat⇒ Z)
  flat⇒ (Var x)   = F.ρ⇐

  flat⇐ : (Y : ObjTerm) → F.HomTerm (wires (flatten Y)) Y
  flat⇐ unit      = F.id
  flat⇐ (Y ⊗₀ Z) = (flat⇐ Y F.⊗₁ flat⇐ Z) F.∘ F.split (flatten Y)
  flat⇐ (Var x)   = F.ρ⇒

  ------------------------------------------------------------------------
  -- F-side coercion along a wire-list equality.
  ------------------------------------------------------------------------

  private
    coeCF : ∀ {A} {p q : List X} → p ≡ q → F.HomTerm A (wires p) → F.HomTerm A (wires q)
    coeCF refl h = h

    coeCF-∘ˡ : ∀ {A R p q} (e : p ≡ q) (h : F.HomTerm R (wires p)) (j : F.HomTerm A R)
             → coeCF e (h F.∘ j) F.≈Term coeCF e h F.∘ j
    coeCF-∘ˡ refl h j = F.≈-Term-refl

    coeCF-resp : ∀ {A p q} (e : p ≡ q) {h h' : F.HomTerm A (wires p)}
               → h F.≈Term h' → coeCF e h F.≈Term coeCF e h'
    coeCF-resp refl eq = eq

    -- the two opposite coercions cancel (UIP-free: by matching e).
    coe-coe : ∀ {A} {p q : List X} (e : p ≡ q) (h : F.HomTerm A (wires p)) → coeCF (sym e) (coeCF e h) ≡ h
    coe-coe refl h = refl

    ------------------------------------------------------------------------
    -- WTerm casts (the structural constructors of `reflectF` die into these).
    ------------------------------------------------------------------------

    castʷ : ∀ {n m m'} → m ≡ m' → WTerm n m → WTerm n m'
    castʷ refl t = t

    embed-castʷ : ∀ {n m m'} (q : m ≡ m') (t : WTerm n m) → embed (castʷ q t) ≈Term castW q ∘ embed t
    embed-castʷ refl t = ≈-Term-sym idˡ

    ------------------------------------------------------------------------
    -- Forward structural λ-law and the law flipper (engine-independent).
    ------------------------------------------------------------------------

    fwd-λ : ∀ (A : ObjTerm) → flat⇒ (unit ⊗₀ A) F.≈Term flat⇒ A F.∘ F.λ⇒
    fwd-λ A = F.λ⇒∘id⊗f≈f∘λ⇒

    -- flip a forward law to its inverse structural morphism.
    flipF : ∀ {P Q} {p q : List X} (e : p ≡ q)
              (h⇒P : F.HomTerm P (wires p)) (h⇒Q : F.HomTerm Q (wires q))
              {c : F.HomTerm P Q} {c⁻¹ : F.HomTerm Q P}
          → c F.∘ c⁻¹ F.≈Term F.id
          → coeCF e h⇒P F.≈Term h⇒Q F.∘ c
          → coeCF (sym e) h⇒Q F.≈Term h⇒P F.∘ c⁻¹
    flipF e h⇒P h⇒Q {c} {c⁻¹} iso fwd = F.≈-Term-sym (beginF
      h⇒P F.∘ c⁻¹
        ≈F⟨ F.≡⇒≈Term (coe-coe e h⇒P) F.⟩∘⟨refl ⟨
      coeCF (sym e) (coeCF e h⇒P) F.∘ c⁻¹
        ≈F⟨ (coeCF-resp (sym e) fwd F.○ coeCF-∘ˡ (sym e) h⇒Q c) F.⟩∘⟨refl ⟩
      (coeCF (sym e) h⇒Q F.∘ c) F.∘ c⁻¹
        ≈F⟨ F.cancelʳ iso ⟩
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
    -- category.  It is an instance of the library-level generator bind
    -- (`FreeMonoidalHelper.Bind`, next to `FreeFunctor`): homomorphic on all
    -- constructors (σ ↦ σ), a box generator going through the caller's
    -- `injBox` via `injMor`.  The equational-respect table is `bind-resp-≈`.
    ----------------------------------------------------------------------

    injMor : ∀ {A B} → mor A B → F.HomTerm A B
    injMor (box w) = injBox w

    private module BindMor = FreeMonoidalHelper.Bind v X injMor

    inj : ∀ {A B} → HomTerm A B → F.HomTerm A B
    inj = BindMor.bind

    private
      -- inj preserves the equational theory (each axiom maps to the same axiom).
      inj-resp-≈ : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → inj f F.≈Term inj g
      inj-resp-≈ = BindMor.bind-resp-≈

    -- inj maps the wire-level merge/split to the F-side ones, on the nose.
    inj-merge : ∀ (a : List X) {suf} → inj (merge a) ≡ F.merge a {suf}
    inj-merge []      = refl
    inj-merge (x ∷ a) = cong (λ h → (F.id F.⊗₁ h) F.∘ F.α⇒) (inj-merge a)

    inj-split : ∀ (a : List X) {suf} → inj (split a) ≡ F.split a {suf}
    inj-split []      = refl
    inj-split (x ∷ a) = cong (λ h → F.α⇐ F.∘ (F.id F.⊗₁ h)) (inj-split a)

    -- a `mid` sandwiched between `split a {b}` and a re-merge collapses:
    -- the inner `merge a {b} ∘ split a {b}` cancels, regardless of `mid`.
    -- Shared by `bridgeF`'s ⊗-case and the σ bridge law (`bridge-σS`).
    merge-split-mid : ∀ (a : List X) {b} {O M P}
      (out : F.HomTerm M O)
      (mid : F.HomTerm (wires a ⊗₀ wires b) M)
      (rest : F.HomTerm P (wires a ⊗₀ wires b))
      → (out F.∘ (mid F.∘ F.split a)) F.∘ (F.merge a F.∘ rest) F.≈Term out F.∘ (mid F.∘ rest)
    merge-split-mid a out mid rest = F.assoc²βε F.○ (F.refl⟩∘⟨ (F.refl⟩∘⟨ F.cancelˡ (F.split∘merge a)))

    private
      inj-castW0 : ∀ {p q} (e : p ≡ q) → inj (castW e) ≡ coeCF e (F.id)
      inj-castW0 refl = refl

      coeCF-idˡ : ∀ {A p q} (e : p ≡ q) (j : F.HomTerm A (wires p)) → coeCF e (F.id) F.∘ j F.≈Term coeCF e j
      coeCF-idˡ refl j = F.idˡ

      inj-castW : ∀ {A p q} (e : p ≡ q) (h : HomTerm A (wires p)) → inj (castW e ∘ h) F.≈Term coeCF e (inj h)
      inj-castW e h = F.≡⇒≈Term (cong (λ z → z F.∘ inj h) (inj-castW0 e)) F.○ coeCF-idˡ e (inj h)

    ----------------------------------------------------------------------
    -- Front-end reflection: structural constructors die into (casted)
    -- idʷ; the var and σ clauses are the caller's.
    ----------------------------------------------------------------------

    reflectF : ∀ {Y Z} → F.HomTerm Y Z → WTerm (flatten Y) (flatten Z)
    reflectF (F.var g)            = reflectVar g
    reflectF F.id                 = idʷ
    reflectF (g F.∘ f)          = reflectF g ∘ʷ reflectF f
    reflectF (f F.⊗₁ g)         = reflectF f ⊗ʷ reflectF g
    reflectF (F.λ⇒ {A})           = idʷ
    reflectF (F.λ⇐ {A})           = idʷ
    reflectF (F.ρ⇒ {A})           = castʷ (++-identityʳ (flatten A)) idʷ
    reflectF (F.ρ⇐ {A})           = castʷ (sym (++-identityʳ (flatten A))) idʷ
    reflectF (F.α⇒ {A} {B} {C})   = castʷ (++-assoc (flatten A) (flatten B) (flatten C)) idʷ
    reflectF (F.α⇐ {A} {B} {C})   = castʷ (sym (++-assoc (flatten A) (flatten B) (flatten C))) idʷ
    reflectF (F.σ {A} {B} ⦃ s ⦄)  = reflectσ A B

    ----------------------------------------------------------------------
    -- Structural lemmas transferred from the wire level along inj.
    ----------------------------------------------------------------------

    private
      -- right-unitor coherence on the F-side merge (transfer of merge-ρ).
      mergeF-ρ : ∀ (a : List X) → coeCF (++-identityʳ a) (F.merge a) F.≈Term F.ρ⇒
      mergeF-ρ a =
        F.≡⇒≈Term (cong (coeCF (++-identityʳ a)) (sym (inj-merge a)))
        F.○ F.⟺ (inj-castW (++-identityʳ a) (merge a))
        F.○ inj-resp-≈ (merge-ρ a)

      -- merge associativity on the F side (transfer of merge-assoc).
      mergeF-assoc : ∀ (p q r : List X)
        → F.merge p F.∘ ((F.id F.⊗₁ F.merge q) F.∘ F.α⇒)
          F.≈Term coeCF (++-assoc p q r) (F.merge (p ++ q) F.∘ (F.merge p F.⊗₁ F.id))
      mergeF-assoc p q r =
        F.≡⇒≈Term (sym lhs-eq)
        F.○ inj-resp-≈ (merge-assoc p q r)
        F.○ inj-castW (++-assoc p q r) (merge (p ++ q) ∘ (merge p ⊗₁ id))
        F.○ coeCF-resp (++-assoc p q r) (F.≡⇒≈Term rhs-eq)
        where
          lhs-eq : inj (merge p ∘ (id ⊗₁ merge q) ∘ α⇒) ≡ F.merge p F.∘ ((F.id F.⊗₁ F.merge q {r}) F.∘ F.α⇒)
          lhs-eq rewrite inj-merge p {q ++ r} | inj-merge q {r} = refl
          rhs-eq : inj (merge (p ++ q) ∘ (merge p ⊗₁ id))
                 ≡ F.merge (p ++ q) F.∘ (F.merge p F.⊗₁ F.id {wires r})
          rhs-eq rewrite inj-merge (p ++ q) {r} | inj-merge p {q} = refl

      ----------------------------------------------------------------------
      -- The canonical iso laws (only the retraction is needed downstream).
      ----------------------------------------------------------------------

      -- Like `flat⇒`/`flat⇐` above, a generic structural fact that stays here
      -- rather than in `FreeMonoidal` because it is phrased over the solver-side
      -- `flatten`.
      flat⇐∘flat⇒ : ∀ (Y : ObjTerm) → flat⇐ Y F.∘ flat⇒ Y F.≈Term F.id
      flat⇐∘flat⇒ unit = F.idˡ
      flat⇐∘flat⇒ (Y ⊗₀ Z) =
        F.cancelInner (F.split∘merge (flatten Y))
        F.○ F.⟺ F.⊗-∘-dist
        F.○ (flat⇐∘flat⇒ Y F.⟩⊗⟨ flat⇐∘flat⇒ Z)
        F.○ F.id⊗id≈id
      flat⇐∘flat⇒ (Var x) = F.ρ⇒∘ρ⇐≈id

      ----------------------------------------------------------------------
      -- cast-half: a casted idʷ, embedded and injected, is the F-side
      -- coercion of whatever it is composed onto.
      ----------------------------------------------------------------------

      cast-half : ∀ {P} {p q : List X} (e : p ≡ q) (h : F.HomTerm P (wires p))
                → inj (embed (castʷ e (idʷ))) F.∘ h F.≈Term coeCF e h
      cast-half e h = ((inj-resp-≈ (embed-castʷ e idʷ) F.○ inj-castW e id) F.⟩∘⟨refl) F.○ coeCF-idˡ e h

      ----------------------------------------------------------------------
      -- Forward structural laws: flattening intertwines the unitors and the
      -- associator.
      ----------------------------------------------------------------------

      fwd-ρ : ∀ (A : ObjTerm) → coeCF (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit)) F.≈Term flat⇒ A F.∘ F.ρ⇒
      fwd-ρ A = beginF
        coeCF (++-identityʳ fA) (F.merge fA F.∘ (flat⇒ A F.⊗₁ F.id))
          ≈F⟨ coeCF-∘ˡ (++-identityʳ fA) (F.merge fA) (flat⇒ A F.⊗₁ F.id) ⟩
        coeCF (++-identityʳ fA) (F.merge fA) F.∘ (flat⇒ A F.⊗₁ F.id)
          ≈F⟨ mergeF-ρ fA F.⟩∘⟨refl ⟩
        F.ρ⇒ F.∘ (flat⇒ A F.⊗₁ F.id)
          ≈F⟨ F.ρ⇒∘f⊗id≈f∘ρ⇒ ⟩
        flat⇒ A F.∘ F.ρ⇒ ∎F
        where fA = flatten A

      fwd-α : ∀ (A B C : ObjTerm)
            → coeCF (++-assoc (flatten A) (flatten B) (flatten C)) (flat⇒ ((A ⊗₀ B) ⊗₀ C))
              F.≈Term flat⇒ (A ⊗₀ (B ⊗₀ C)) F.∘ F.α⇒
      fwd-α A B C = beginF
        coeCF e (F.merge (fA ++ fB) F.∘ ((F.merge fA F.∘ (f⇒A F.⊗₁ f⇒B)) F.⊗₁ f⇒C))
          ≈F⟨ coeCF-resp e ((F.refl⟩∘⟨ F.split₁ˡ) F.○ F.⟺ F.assoc) ⟩
        coeCF e ((F.merge (fA ++ fB) F.∘ (F.merge fA F.⊗₁ F.id)) F.∘ ((f⇒A F.⊗₁ f⇒B) F.⊗₁ f⇒C))
          ≈F⟨ coeCF-∘ˡ e (F.merge (fA ++ fB) F.∘ (F.merge fA F.⊗₁ F.id)) ((f⇒A F.⊗₁ f⇒B) F.⊗₁ f⇒C) ⟩
        coeCF e (F.merge (fA ++ fB) F.∘ (F.merge fA F.⊗₁ F.id)) F.∘ ((f⇒A F.⊗₁ f⇒B) F.⊗₁ f⇒C)
          ≈F⟨ mergeF-assoc fA fB fC F.⟩∘⟨refl ⟨
        (F.merge fA F.∘ ((F.id F.⊗₁ F.merge fB) F.∘ F.α⇒)) F.∘ ((f⇒A F.⊗₁ f⇒B) F.⊗₁ f⇒C)
          ≈F⟨ F.assoc²βε ⟩
        F.merge fA F.∘ ((F.id F.⊗₁ F.merge fB) F.∘ (F.α⇒ F.∘ ((f⇒A F.⊗₁ f⇒B) F.⊗₁ f⇒C)))
          ≈F⟨ F.refl⟩∘⟨ ((F.refl⟩∘⟨ F.α-comm) F.○ F.pullˡ (F.⟺ F.⊗-∘-dist F.○ (F.idˡ F.⟩⊗⟨ F.≈-Term-refl))) ⟩
        F.merge fA F.∘ ((f⇒A F.⊗₁ (F.merge fB F.∘ (f⇒B F.⊗₁ f⇒C))) F.∘ F.α⇒)
          ≈F⟨ F.⟺ F.assoc ⟩
        (F.merge fA F.∘ (f⇒A F.⊗₁ (F.merge fB F.∘ (f⇒B F.⊗₁ f⇒C)))) F.∘ F.α⇒ ∎F
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
         → inj (embed (reflectVar g)) ≡ flat⇒ Z F.∘ (F.var g F.∘ flat⇐ Y))
      (bridge-σ : ∀ {A B : ObjTerm} ⦃ s : Symm ≤ v ⦄
         → inj (embed (reflectσ A B)) F.∘ flat⇒ (A ⊗₀ B) F.≈Term flat⇒ (B ⊗₀ A) F.∘ F.σ)
      where

      private
        --------------------------------------------------------------------
        -- bridgeF: the front-end reflection is sound, up to the canonical
        -- iso.
        --------------------------------------------------------------------

        bridgeF : ∀ {Y Z} (t : F.HomTerm Y Z) → inj (embed (reflectF t)) F.∘ flat⇒ Y F.≈Term flat⇒ Z F.∘ t
        bridgeF {Y} {Z} (F.var g) =
          (F.≡⇒≈Term (inj-embed-var g) F.⟩∘⟨refl)
          F.○ F.assoc F.○ (F.refl⟩∘⟨ F.cancelʳ (flat⇐∘flat⇒ Y))
        bridgeF {Y} {.Y} F.id = F.idˡ F.○ F.⟺ F.idʳ
        bridgeF {Y} {Z} (g F.∘ f) = F.assoc F.○ (F.refl⟩∘⟨ bridgeF f) F.○ F.pullˡ (bridgeF g) F.○ F.assoc
        bridgeF (F._⊗₁_ {A = Y} {B = Z} {C = Y'} {D = Z'} f g) = beginF
          inj (embed (reflectF f ⊗ʷ reflectF g)) F.∘ (F.merge fY F.∘ (f⇒Y F.⊗₁ f⇒Y'))
            ≈F⟨ F.≡⇒≈Term (cong₂ (λ m s → m F.∘ ((IF F.⊗₁ IG) F.∘ s))
                                 (inj-merge fZ) (inj-split fY)) F.⟩∘⟨refl ⟩
          (F.merge fZ F.∘ ((IF F.⊗₁ IG) F.∘ F.split fY)) F.∘ (F.merge fY F.∘ (f⇒Y F.⊗₁ f⇒Y'))
            ≈F⟨ merge-split-mid fY (F.merge fZ) (IF F.⊗₁ IG) (f⇒Y F.⊗₁ f⇒Y') ⟩
          F.merge fZ F.∘ ((IF F.⊗₁ IG) F.∘ (f⇒Y F.⊗₁ f⇒Y'))
            ≈F⟨ F.refl⟩∘⟨ (F.⟺ F.⊗-∘-dist F.○ (bridgeF f F.⟩⊗⟨ bridgeF g) F.○ F.⊗-∘-dist) ⟩
          F.merge fZ F.∘ ((f⇒Z F.⊗₁ f⇒Z') F.∘ (f F.⊗₁ g))
            ≈F⟨ F.⟺ F.assoc ⟩
          (F.merge fZ F.∘ (f⇒Z F.⊗₁ f⇒Z')) F.∘ (f F.⊗₁ g) ∎F
          where
            fY = flatten Y ; fY' = flatten Y' ; fZ = flatten Z ; fZ' = flatten Z'
            f⇒Y = flat⇒ Y ; f⇒Y' = flat⇒ Y' ; f⇒Z = flat⇒ Z ; f⇒Z' = flat⇒ Z'
            IF = inj (embed (reflectF f))
            IG = inj (embed (reflectF g))
        bridgeF (F.λ⇒ {A}) = F.idˡ F.○ fwd-λ A
        bridgeF (F.λ⇐ {A}) = F.idˡ F.○ flipF refl (flat⇒ (unit ⊗₀ A)) (flat⇒ A) F.λ⇒∘λ⇐≈id (fwd-λ A)
        bridgeF (F.ρ⇒ {A}) = cast-half (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit)) F.○ fwd-ρ A
        bridgeF (F.ρ⇐ {A}) =
          cast-half (sym (++-identityʳ (flatten A))) (flat⇒ A)
          F.○ flipF (++-identityʳ (flatten A)) (flat⇒ (A ⊗₀ unit)) (flat⇒ A)
                   F.ρ⇒∘ρ⇐≈id (fwd-ρ A)
        bridgeF (F.α⇒ {A} {B} {C}) =
          cast-half (++-assoc (flatten A) (flatten B) (flatten C)) (flat⇒ ((A ⊗₀ B) ⊗₀ C))
          F.○ fwd-α A B C
        bridgeF (F.α⇐ {A} {B} {C}) =
          cast-half (sym (++-assoc (flatten A) (flatten B) (flatten C))) (flat⇒ (A ⊗₀ (B ⊗₀ C)))
          F.○ flipF (++-assoc (flatten A) (flatten B) (flatten C))
                   (flat⇒ ((A ⊗₀ B) ⊗₀ C)) (flat⇒ (A ⊗₀ (B ⊗₀ C)))
                   F.α⇒∘α⇐≈id (fwd-α A B C)
        bridgeF (F.σ {A} {B} ⦃ s ⦄) = bridge-σ

      -- the cancellation: a wire-level equality of the two reflections is
      -- a front-end equality of the original terms.
      solveF : ∀ {Y Z} {l r : F.HomTerm Y Z} → embed (reflectF l) ≈Term embed (reflectF r) → l F.≈Term r
      solveF {Y} {Z} {l} {r} eq =
        F.insertˡ (flat⇐∘flat⇒ Z) F.○ (F.refl⟩∘⟨ main) F.○ F.cancelˡ (flat⇐∘flat⇒ Z)
        where
          main : flat⇒ Z F.∘ l F.≈Term flat⇒ Z F.∘ r
          main = F.⟺ (bridgeF l) F.○ (inj-resp-≈ eq F.⟩∘⟨refl) F.○ bridgeF r

------------------------------------------------------------------------
-- FFocus: the variant-generic term-level FOCUSING and diagrammatic
-- REWRITING layer (the Mon analogue of the SMC solver's `Carve` +
-- `rewriteH!`).  Both are generic in the front-end free category and the
-- decision procedure — the only genuinely front-end-specific ingredient is
-- `decide?F`, which is passed as a parameter.  (The `DecEq ObjTerm`
-- instance depends only on `DecEq X`, so it belongs in this variant-generic
-- layer.)
--
-- The focusing search is unverified: a `focusAtₙ` hit is certified
-- downstream by `decide?F`, so soundness rests solely on the solver.
------------------------------------------------------------------------

module FFocus
  {v : Variant} {X : Set} ⦃ _ : DecEq X ⦄
  (sig : FreeSig v {X})
  (let open FreeSig sig)
  (decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r))
  where

  open FreeMonoidalHelper v X using (unit; _⊗₀_)

  -- reference-style entry point: discharge `l F.≈Term r` by reflection.
  solveTerm! : ∀ {Y Z} (l r : F.HomTerm Y Z) {hit : IsJust (decide?F l r)} → l F.≈Term r
  solveTerm! l r {hit} = to-witness-T (decide?F l r) hit

  private instance
    DecEq-ObjTerm : DecEq ObjTerm
    DecEq-ObjTerm ._≟_ = FreeMonoidalHelper.≟ObjTerm v X _≟_

  -- a focus: the two pad objects and the two context terms.
  Foc : (A B P Q : ObjTerm) → Set
  Foc A B P Q = Σ[ k ∈ ObjTerm ] Σ[ m ∈ ObjTerm ] (F.HomTerm A (k ⊗₀ (P ⊗₀ m)) × F.HomTerm (k ⊗₀ (Q ⊗₀ m)) B)

  -- plug a morphism into the frame of a focus.
  plug : ∀ {A B P Q} → Foc A B P Q → F.HomTerm P Q → F.HomTerm A B
  plug (k , m , pre , post) mid = post F.∘ ((F.id F.⊗₁ (mid F.⊗₁ F.id)) F.∘ pre)

  private
    -- leaf: the whole of `s` is the redex (up to the solver).
    leaf-try : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → Maybe (Foc A B P Q)
    leaf-try {A} {B} {P} {Q} s lᵗ = case A ≟ P of λ where
      (no _)     → nothing
      (yes refl) → case B ≟ Q of λ where
        (no _)     → nothing
        (yes refl) → case decide?F s lᵗ of λ where
          (just _) → just (unit , unit , F.λ⇐ F.∘ F.ρ⇐ , F.ρ⇒ F.∘ F.λ⇒)
          nothing  → nothing

  -- enumerate all focus positions: whole-term first, then — for `∘` — the
  -- first-applied operand's positions before the second's, and — for `⊗` —
  -- the left factor's before the right's.
  private
    focusAll : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → List (Foc A B P Q)

    go-all : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → List (Foc A B P Q)
    go-all (g F.∘ f) lᵗ =
         map (λ { (k , m , pre , post) → (k , m , pre , g F.∘ post) })
             (focusAll f lᵗ)
      ++ map (λ { (k , m , pre , post) → (k , m , pre F.∘ f , post) })
             (focusAll g lᵗ)
    go-all (F._⊗₁_ {A = A₁} {C = A₂} a b) lᵗ =
         map (λ { (k , m , pre , post) →                       -- redex in a
                ( k , m ⊗₀ A₂
                , (F.id F.⊗₁ F.α⇒) F.∘ (F.α⇒ F.∘ (pre F.⊗₁ F.id))
                , (post F.⊗₁ b) F.∘ (F.α⇐ F.∘ (F.id F.⊗₁ F.α⇐)) ) })
             (focusAll a lᵗ)
      ++ map (λ { (k , m , pre , post) →                       -- redex in b
                ( A₁ ⊗₀ k , m
                , F.α⇐ F.∘ (F.id F.⊗₁ pre)
                , (a F.⊗₁ post) F.∘ F.α⇒ ) })
             (focusAll b lᵗ)
    go-all _ _ = []

  focusAll s lᵗ = case leaf-try s lᵗ of λ where
    (just r) → r ∷ go-all s lᵗ
    nothing  → go-all s lᵗ

  private
    lookupMaybe : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
    lookupMaybe []       _        = nothing
    lookupMaybe (x ∷ _)  zero     = just x
    lookupMaybe (_ ∷ xs) (suc n)  = lookupMaybe xs n

  -- the n-th focus position (0-based, in the order above).
  focusAtₙ : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → ℕ → Maybe (Foc A B P Q)
  focusAtₙ s lᵗ n = lookupMaybe (focusAll s lᵗ) n

  ------------------------------------------------------------------------
  -- The diagrammatic rewriting wrappers in a target category.  A *rule* is
  -- any C-equation `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁`; it fires inside the two-sided frame
  -- `post ∘ (id {k} ⊗ (– ⊗ id {m})) ∘ pre` (supplied, or located by
  -- `focusAtₙ`), and the solver reconciles the caller's terms with the
  -- frames so only the rule itself crosses the congruence.
  ------------------------------------------------------------------------

  -- `Rewrite` packages the rewrite-wrapper boilerplate generically.  The two
  -- reduction-sensitive ingredients are passed as parameters: `solveMor!` and
  -- `plugCong`.
  module Rewrite
    {o ℓ e : Level}
    (C : MonoidalCategory o ℓ e)
    (⟦_⟧ₒ : ObjTerm → C .MonoidalCategory.U .Category.Obj)
    (⟦_⟧₁ : ∀ {Y Z} → F.HomTerm Y Z → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
    (solveMor! : ∀ {Y Z} (l r : F.HomTerm Y Z) {hit : IsJust (decide?F l r)}
               → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ])
    (plugCong : ∀ {A B P Q} (foc : Foc A B P Q) (l r : F.HomTerm P Q)
              → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
              → C .MonoidalCategory.U [ ⟦ plug foc l ⟧₁ ≈ ⟦ plug foc r ⟧₁ ])
    where

    private
      module MCc = MonoidalCategory C

      -- shared body: rewrite `s ≈ t` by firing a rule at a known focus.
      rewriteAt : ∀ {A B P Q}
                → (s t : F.HomTerm A B) (foc : Foc A B P Q) (lᵗ rᵗ : F.HomTerm P Q)
                → C .MonoidalCategory.U [ ⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁ ]
                → {h₁ : IsJust (decide?F s (plug foc lᵗ))}
                → {h₂ : IsJust (decide?F t (plug foc rᵗ))}
                → C .MonoidalCategory.U [ ⟦ s ⟧₁ ≈ ⟦ t ⟧₁ ]
      rewriteAt s t foc lᵗ rᵗ rule {h₁} {h₂} =
        MCc.Equiv.trans (solveMor! s (plug foc lᵗ) {h₁})
          (MCc.Equiv.trans (plugCong foc lᵗ rᵗ rule)
            (MCc.Equiv.sym (solveMor! t (plug foc rᵗ) {h₂})))

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
      rewriteAt s t (k , m , pre , post) lᵗ rᵗ rule {h₁} {h₂}

    -- automatic position: the n-th occurrence of `lᵗ` in `s` is located by
    -- `focusAtₙ`; both endpoints are stated by the caller.
    rewriteMorₙ!
      : ∀ {A B P Q}
      → (s t : F.HomTerm A B) (lᵗ rᵗ : F.HomTerm P Q) (n : ℕ)
      → C .MonoidalCategory.U [ ⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁ ]
      → {found : IsJust (focusAtₙ s lᵗ n)}
      → {h₁ : IsJust (decide?F s (plug (to-witness-T (focusAtₙ s lᵗ n) found) lᵗ))}
      → {h₂ : IsJust (decide?F t (plug (to-witness-T (focusAtₙ s lᵗ n) found) rᵗ))}
      → C .MonoidalCategory.U [ ⟦ s ⟧₁ ≈ ⟦ t ⟧₁ ]
    rewriteMorₙ! s t lᵗ rᵗ n rule {found} {h₁} {h₂} =
      rewriteAt s t (to-witness-T (focusAtₙ s lᵗ n) found) lᵗ rᵗ rule {h₁} {h₂}

    -- the first occurrence.
    rewriteMorAuto!
      : ∀ {A B P Q}
      → (s t : F.HomTerm A B) (lᵗ rᵗ : F.HomTerm P Q)
      → C .MonoidalCategory.U [ ⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁ ]
      → {found : IsJust (focusAtₙ s lᵗ 0)}
      → {h₁ : IsJust (decide?F s (plug (to-witness-T (focusAtₙ s lᵗ 0) found) lᵗ))}
      → {h₂ : IsJust (decide?F t (plug (to-witness-T (focusAtₙ s lᵗ 0) found) rᵗ))}
      → C .MonoidalCategory.U [ ⟦ s ⟧₁ ≈ ⟦ t ⟧₁ ]
    rewriteMorAuto! s t lᵗ rᵗ rule {found} {h₁} {h₂} = rewriteMorₙ! s t lᵗ rᵗ 0 rule {found} {h₁} {h₂}

------------------------------------------------------------------------
-- FSolve: the shared front-end — transport into a target monoidal
-- category along the free functor.  `Into` fixes the target, with the
-- variant's instance-gated symmetric structure (the Mon front-end passes
-- the vacuous `λ ⦃ () ⦄`, the Symm front-end wraps its caller's
-- `Symmetric` witness); `WithGen` then hosts the whole
-- focusing/rewriting epilogue (`solveMor!`/`plugCong`/`Rewrite`) at the
-- CONCRETE `FreeFunctor` interpretation, so the reduction-sensitive
-- `plugCong` (`⟦ plug foc l ⟧₁` only unfolds through the concrete
-- functor) lives in ONE place instead of being copied into each
-- front-end.
------------------------------------------------------------------------

module FSolve
  {v : Variant} {X : Set} ⦃ _ : DecEq X ⦄
  (sig : FreeSig v {X})
  (let open FreeSig sig)
  (decide?F : ∀ {Y Z} (l r : F.HomTerm Y Z) → Maybe (l F.≈Term r))
  where

  module Into
    {o ℓ e : Level}
    (C : MonoidalCategory o ℓ e)
    (sym : ⦃ Symm ≤ v ⦄ → Symmetric (C .MonoidalCategory.monoidal))
    (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
    where

    private
      module FF = FFocus sig decide?F
      module MCc = MonoidalCategory C

      -- the target repackaged as the variant-indexed interpretation the
      -- generator-independent object map and the free functor read in.
      ⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ}
      ⟦v⟧ = fromMC C sym

      dF : FreeMonoidalData
      dF = record { v = v ; X = X ; mor = GenF }

    -- the object map straight from the generator-independent `FreeObjInterp`, so
    -- `⟦_⟧ₒ` is definitionally one and the same across signatures over the same
    -- atoms (it does not project through the `GenF`-parametrised module).
    open FreeObjInterp v X ⟦v⟧ ⟦_⟧ᵖ₀ using () renaming (⟦_⟧₀ to ⟦_⟧ₒ) public

    module WithGen
      (⟦gen⟧ : ∀ {Y Z} → GenF Y Z → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
      where

      private
        ffdF : FreeFunctorData dF {o} {ℓ}
        ffdF = record { ⟦v⟧ = ⟦v⟧ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦gen⟧ }

      open FreeFunctor {d = dF} ffdF public using (⟦_⟧₁; ⟦⟧-resp-≈)

      -- the actual entry point
      solveMor! : ∀ {Y Z} (l r : F.HomTerm Y Z) {hit : IsJust (decide?F l r)}
                → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
      solveMor! l r {hit} = ⟦⟧-resp-≈ (FF.solveTerm! l r {hit})

      private
        -- transport a rule across the frame of a focus, by congruence.
        plugCong : ∀ {A B P Q} (foc : FF.Foc A B P Q) (l r : F.HomTerm P Q)
                 → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
                 → C .MonoidalCategory.U [ ⟦ FF.plug foc l ⟧₁ ≈ ⟦ FF.plug foc r ⟧₁ ]
        plugCong (k , m , pre , post) l r rule =
          MCc.∘-resp-≈ʳ (MCc.∘-resp-≈ˡ
            (MCc.⊗.F-resp-≈ (MCc.Equiv.refl , MCc.⊗.F-resp-≈ (rule , MCc.Equiv.refl))))

      open FF.Rewrite C ⟦_⟧ₒ ⟦_⟧₁ solveMor! plugCong public using (rewriteMor!; rewriteMorₙ!; rewriteMorAuto!)

------------------------------------------------------------------------
-- FinSetupCore: the shared body of the two call-site convenience wrappers
-- (`Frontend.FinSetup` / `Frontend.Sigma.FinSetupσ`).
--
-- From a target monoidal category `C` (with the variant's symmetric
-- structure `sym`) and a `Vec` of object atoms it exposes the object
-- language and the object interpretation `⟦_⟧ₒ`; the inner `Sig` then
-- assembles the Fin-indexed signature (`FinSig`) and runs the full
-- `FSolve`/`Into`/`WithGen` pipeline uniformly in the `Variant`.  The only
-- genuinely variant-specific input is the per-arity decision builder
-- `decide?F`, supplied by each wrapper's front-end (`Frontend`/`FrontendS`).
-- The crux that makes this sound: running `FinSig v arity` here yields the
-- SAME `GenS`/`S` as the wrapper's own `FinSig v arity` (module application
-- is non-generative), so the wrapper's `decide?F` matches the `S.HomTerm`
-- this `Sig` expects.
------------------------------------------------------------------------

module FinSetupCore
  {v : Variant}
  {o ℓ e : Level} (C : MonoidalCategory o ℓ e)
  (sym : ⦃ Symm ≤ v ⦄ → Symmetric (C .MonoidalCategory.monoidal))
  {nA : ℕ} (vars : Vec (C .MonoidalCategory.U .Category.Obj) nA)
  where

  -- the object language over the atom indices, with constructors renamed so
  -- they coexist with a caller's own free-category vocabulary.
  open FreeMonoidalHelper v (Fin nA) public using (ObjTerm) renaming (Var to V; unit to unitᵒ; _⊗₀_ to _⊗ᵒ_)

  -- the object interpretation `ObjTerm → C.Obj`.  Independent of any generator
  -- signature — definitionally the `⟦_⟧ₒ` each `Sig` exposes — so it can type a
  -- generator's interpretation BEFORE the signature is fixed.
  open FreeObjInterp v (Fin nA) (fromMC C sym) (lookup vars) public using () renaming (⟦_⟧₀ to ⟦_⟧ₒ)

  module Sig
    {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm)
    (decide?F : let open FinSig v arity in ∀ {Y Z} (l r : S.HomTerm Y Z) → Maybe (l S.≈Term r))
    where

    open FinSig v arity public using (GenS; genS; module S; gen; GenΣ; DecEq-Gen; rankS)

    private
      sig : FreeSig v {Fin nA}
      sig = record { GenF = GenS }

    open FFocus sig decide?F public using (solveTerm!)
    open FSolve sig decide?F public using (module Into)
    open Into C sym (lookup vars) public
