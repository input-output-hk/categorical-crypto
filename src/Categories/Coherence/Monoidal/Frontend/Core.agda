{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The generator-generic core of the solver front-end.
--------------------------------------------------------------------------------

module Categories.Coherence.Monoidal.Frontend.Core where

open import categorical-crypto.Prelude hiding (_∘_; id; map; merge; [_]; [_,_])

open import Data.Fin using (Fin; toℕ)
open import Data.List using (map)
open import Data.List.Properties
import Data.List.Properties.Ext as ListExt

open import Data.Maybe.Ext

open import Categories.Category
open import Categories.Category.Monoidal

import Categories.Category.Monoidal.Reasoning as MonR
import Categories.Morphism.Reasoning as MR

open import Categories.Coherence.Monoidal.Diagram
open import Categories.Coherence.Monoidal.Reflect
open import Categories.FreeMonoidal

------------------------------------------------------------------------
-- FReason: the front-end free monoidal category over an ObjTerm-arity
-- generator signature, plus the reasoning vocabulary its clients share.
------------------------------------------------------------------------

module FReason
  {X : Set}
  (let open FreeMonoidalHelper Mon X)
  (GenF : ObjTerm → ObjTerm → Set)
  where
  open FreeMonoidalHelper.Mor Mon X GenF public
  open MR FreeMonoidal public
  open MonR Monoidal-FreeMonoidal public using (refl⟩∘⟨_; _⟩∘⟨refl; ⟺; _○_; _⟩⊗⟨_; split₁ˡ)

------------------------------------------------------------------------
-- FCore: the wire-level image of the signature.
------------------------------------------------------------------------

module FCore {X : Set} (let open FreeMonoidalHelper Mon X) (GenF : ObjTerm → ObjTerm → Set) where

  private module F = FreeMonoidalHelper.Mor Mon X GenF

  ------------------------------------------------------------------------
  -- The wire-level generator family
  ------------------------------------------------------------------------

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
-- FinSig: the Fin-indexed signature prelude for the call-site wrapper
-- `FinSetup`.  `GenS` is not parametrized by any target category, so a single
-- signature can be reused across targets.
------------------------------------------------------------------------

module FinSig
  {X : Set} (let open FreeMonoidalHelper Mon X)
  {nG : ℕ} (arity : Fin nG → ObjTerm × ObjTerm) where

  data GenS : ObjTerm → ObjTerm → Set where
    genS : (i : Fin nG) → GenS (proj₁ (arity i)) (proj₂ (arity i))

  -- the front-end term language over the assembled signature.
  module S = FreeMonoidalHelper.Mor Mon X GenS

  gen : (i : Fin nG) → S.HomTerm (proj₁ (arity i)) (proj₂ (arity i))
  gen i = S.var (genS i)

  open FCore {X} GenS public using (GenΣ)

  instance
    DecEq-Gen : DecEq GenΣ
    DecEq-Gen ._≟_ (_ , _ , genS i) (_ , _ , genS j) = case i ≟ j of λ where
      (yes refl) → yes refl
      (no ¬p)    → no λ where refl → ¬p refl

  rankS : GenΣ → ℕ
  rankS (_ , _ , genS i) = toℕ i

------------------------------------------------------------------------
-- FBridge: reflection of front-end terms into the wire level, and the
-- soundness bridge `bridgeF` that carries a wire-level equality back.
------------------------------------------------------------------------

module FBridge
  {X : Set} ⦃ _ : DecEq X ⦄
  (let open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_; Var; flatten))
  (GenF : ObjTerm → ObjTerm → Set)
  where

  module F = FReason GenF

  open FCore {X} GenF
  open F≈R

  open WireSig {X} MorW
  open DiagramI MorW using (castW; module WireCohDec)
  open WireCohDec
  open ReflectI MorW

  open FreeMonoidalHelper.Mor Mon X mor hiding (flat⇒; flat⇐; flat⇐∘flat⇒)

  open F using (flat⇒; flat⇐; flat⇐∘flat⇒)

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
    -- Forward structural λ-law and the law flipper.
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
  -- `inj`: the wire-level free category into the front-end free category, an
  -- instance of the library-level generator bind `FreeMonoidalHelper.Bind`.
  -- A box is conjugated by the canonical iso `Y ≅ wires (flatten Y)`.
  ------------------------------------------------------------------------

  private
    injBox : ∀ {a b} → MorW a b → F.HomTerm (wires a) (wires b)
    injBox (mk {Y} {Z} g) = flat⇒ Z F.∘ (F.var g F.∘ flat⇐ Y)

    injMor : ∀ {A B} → mor A B → F.HomTerm A B
    injMor (box w) = injBox w

  private module BindMor = FreeMonoidalHelper.Bind Mon X injMor

  private
    inj : ∀ {A B} → HomTerm A B → F.HomTerm A B
    inj = BindMor.bind

    inj-resp-≈ : ∀ {A B} {f g : HomTerm A B} → f ≈Term g → inj f F.≈Term inj g
    inj-resp-≈ = BindMor.bind-resp-≈

    inj-merge : ∀ (a : List X) {suf} → inj (merge a) ≡ F.merge a {suf}
    inj-merge []      = refl
    inj-merge (x ∷ a) = cong (λ h → (F.id F.⊗₁ h) F.∘ F.α⇒) (inj-merge a)

    inj-split : ∀ (a : List X) {suf} → inj (split a) ≡ F.split a {suf}
    inj-split []      = refl
    inj-split (x ∷ a) = cong (λ h → F.α⇐ F.∘ (F.id F.⊗₁ h)) (inj-split a)

    merge-split-mid : ∀ (a : List X) {b} {O M P}
      (out : F.HomTerm M O)
      (mid : F.HomTerm (wires a ⊗₀ wires b) M)
      (rest : F.HomTerm P (wires a ⊗₀ wires b))
      → (out F.∘ (mid F.∘ F.split a)) F.∘ (F.merge a F.∘ rest) F.≈Term out F.∘ (mid F.∘ rest)
    merge-split-mid a out mid rest = F.assoc²βε F.○ (F.refl⟩∘⟨ (F.refl⟩∘⟨ F.cancelˡ (F.split∘merge a)))

    inj-castW0 : ∀ {p q} (e : p ≡ q) → inj (castW e) ≡ coeCF e (F.id)
    inj-castW0 refl = refl

    coeCF-idˡ : ∀ {A p q} (e : p ≡ q) (j : F.HomTerm A (wires p)) → coeCF e (F.id) F.∘ j F.≈Term coeCF e j
    coeCF-idˡ refl j = F.idˡ

    inj-castW : ∀ {A p q} (e : p ≡ q) (h : HomTerm A (wires p)) → inj (castW e ∘ h) F.≈Term coeCF e (inj h)
    inj-castW e h = F.≡⇒≈Term (cong (λ z → z F.∘ inj h) (inj-castW0 e)) F.○ coeCF-idˡ e (inj h)

  ------------------------------------------------------------------------
  -- Front-end reflection: structural constructors die into (casted) idʷ, a
  -- generator becomes its wire-level box.
  ------------------------------------------------------------------------

  reflectF : ∀ {Y Z} → F.HomTerm Y Z → WTerm (flatten Y) (flatten Z)
  reflectF (F.var g)            = boxʷ (mk g)
  reflectF F.id                 = idʷ
  reflectF (g F.∘ f)            = reflectF g ∘ʷ reflectF f
  reflectF (f F.⊗₁ g)           = reflectF f ⊗ʷ reflectF g
  reflectF (F.λ⇒ {A})           = idʷ
  reflectF (F.λ⇐ {A})           = idʷ
  reflectF (F.ρ⇒ {A})           = castʷ (++-identityʳ (flatten A)) idʷ
  reflectF (F.ρ⇐ {A})           = castʷ (sym (++-identityʳ (flatten A))) idʷ
  reflectF (F.α⇒ {A} {B} {C})   = castʷ (++-assoc (flatten A) (flatten B) (flatten C)) idʷ
  reflectF (F.α⇐ {A} {B} {C})   = castʷ (sym (++-assoc (flatten A) (flatten B) (flatten C))) idʷ
  reflectF (F.σ ⦃ () ⦄)

  ------------------------------------------------------------------------
  -- Structural lemmas transferred from the wire level along inj.
  ------------------------------------------------------------------------

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

    cast-half : ∀ {P} {p q : List X} (e : p ≡ q) (h : F.HomTerm P (wires p))
              → inj (embed (castʷ e (idʷ))) F.∘ h F.≈Term coeCF e h
    cast-half e h = ((inj-resp-≈ (embed-castʷ e idʷ) F.○ inj-castW e id) F.⟩∘⟨refl) F.○ coeCF-idˡ e h

    ------------------------------------------------------------------------
    -- Forward structural laws: flattening intertwines the unitors and the
    -- associator.
    ------------------------------------------------------------------------

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

    -- the front-end reflection is sound, up to the canonical iso.
    bridgeF : ∀ {Y Z} (t : F.HomTerm Y Z) → inj (embed (reflectF t)) F.∘ flat⇒ Y F.≈Term flat⇒ Z F.∘ t
    bridgeF {Y} {Z} (F.var g) = F.assoc F.○ (F.refl⟩∘⟨ F.cancelʳ (flat⇐∘flat⇒ Y))
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
    bridgeF (F.σ ⦃ () ⦄)

  solveF : ∀ {Y Z} {l r : F.HomTerm Y Z} → embed (reflectF l) ≈Term embed (reflectF r) → l F.≈Term r
  solveF {Y} {Z} {l} {r} eq =
    F.insertˡ (flat⇐∘flat⇒ Z) F.○ (F.refl⟩∘⟨ main) F.○ F.cancelˡ (flat⇐∘flat⇒ Z)
    where
      main : flat⇒ Z F.∘ l F.≈Term flat⇒ Z F.∘ r
      main = F.⟺ (bridgeF l) F.○ (inj-resp-≈ eq F.⟩∘⟨refl) F.○ bridgeF r

------------------------------------------------------------------------
-- FSolve: term-level focusing and the transport into a target monoidal
-- category along the free functor.  `Into` fixes the target; `WithGen` then
-- hosts the solve/rewrite epilogue at the concrete `FreeFunctor`
-- interpretation, which is what the reduction-sensitive `plugCong` needs.
--
-- The focusing search is unverified: a `focusAtₙ` hit is certified
-- downstream by `decide?F`, so soundness rests solely on the solver.
------------------------------------------------------------------------

module FSolve
  {X : Set} ⦃ _ : DecEq X ⦄
  (let open FreeMonoidalHelper Mon X using (ObjTerm; unit; _⊗₀_))
  (GenF : ObjTerm → ObjTerm → Set)
  (let open FreeMonoidalHelper.Mor Mon X GenF using (HomTerm; _≈Term_))
  (decide?F : ∀ {Y Z} (l r : HomTerm Y Z) → Maybe (l ≈Term r))
  where

  module F = FReason GenF

  -- reference-style entry point: discharge `l F.≈Term r` by reflection.
  solveTerm! : ∀ {Y Z} (l r : F.HomTerm Y Z) {hit : IsJust (decide?F l r)} → l F.≈Term r
  solveTerm! l r {hit} = to-witness-T (decide?F l r) hit

  private instance
    DecEq-ObjTerm : DecEq ObjTerm
    DecEq-ObjTerm ._≟_ = FreeMonoidalHelper.≟ObjTerm Mon X _≟_

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
         map (λ { (k , m , pre , post) → (k , m , pre , g F.∘ post) }) (focusAll f lᵗ)
      ++ map (λ { (k , m , pre , post) → (k , m , pre F.∘ f , post) }) (focusAll g lᵗ)
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

  -- the n-th focus position (0-based, in the order above).
  focusAtₙ : ∀ {A B P Q} → F.HomTerm A B → F.HomTerm P Q → ℕ → Maybe (Foc A B P Q)
  focusAtₙ s lᵗ n = ListExt.lookupMaybe (focusAll s lᵗ) n

  module Into
    {o ℓ e : Level}
    (C : MonoidalCategory o ℓ e)
    (⟦_⟧ᵖ₀ : X → C .MonoidalCategory.U .Category.Obj)
    where

    private
      module MCc = MonoidalCategory C

      ⟦v⟧ : ⟦ Mon ⟧ᵥ
      ⟦v⟧ = fromMC C noSymmetric

      dF : FreeMonoidalData
      dF = record { v = Mon ; X = X ; mor = GenF }

    -- the object map straight from the generator-independent `FreeObjInterp`,
    -- so `⟦_⟧ₒ` is definitionally one and the same across signatures over the
    -- same atoms.
    open FreeObjInterp Mon X ⟦v⟧ ⟦_⟧ᵖ₀ using () renaming (⟦_⟧₀ to ⟦_⟧ₒ) public

    module WithGen
      (⟦gen⟧ : ∀ {Y Z} → GenF Y Z → C .MonoidalCategory.U [ ⟦ Y ⟧ₒ , ⟦ Z ⟧ₒ ])
      where

      private
        ffdF : FreeFunctorData dF
        ffdF = record { ⟦v⟧ = ⟦v⟧ ; ⟦_⟧ᵖ₀ = ⟦_⟧ᵖ₀ ; ⟦_⟧ᵖ₁ = ⟦gen⟧ }

      open FreeFunctor {d = dF} ffdF public using (⟦_⟧₁; ⟦⟧-resp-≈)

      -- the actual entry point
      solveMor! : ∀ {Y Z} (l r : F.HomTerm Y Z) {hit : IsJust (decide?F l r)}
                → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
      solveMor! l r {hit} = ⟦⟧-resp-≈ (solveTerm! l r {hit})

      --------------------------------------------------------------------
      -- The diagrammatic rewriting wrappers.  A *rule* is any C-equation
      -- `⟦ lᵗ ⟧₁ ≈ ⟦ rᵗ ⟧₁`; it fires inside the two-sided frame
      -- `post ∘ (id {k} ⊗ (– ⊗ id {m})) ∘ pre`, supplied or located by
      -- `focusAtₙ`.
      --------------------------------------------------------------------

      private
        -- transport a rule across the frame of a focus, by congruence.
        plugCong : ∀ {A B P Q} (foc : Foc A B P Q) (l r : F.HomTerm P Q)
                 → C .MonoidalCategory.U [ ⟦ l ⟧₁ ≈ ⟦ r ⟧₁ ]
                 → C .MonoidalCategory.U [ ⟦ plug foc l ⟧₁ ≈ ⟦ plug foc r ⟧₁ ]
        plugCong (k , m , pre , post) l r rule =
          MCc.∘-resp-≈ʳ (MCc.∘-resp-≈ˡ
            (MCc.⊗.F-resp-≈ (MCc.Equiv.refl , MCc.⊗.F-resp-≈ (rule , MCc.Equiv.refl))))

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
