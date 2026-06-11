{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Shared F-structural core for the Mon and Symm solver front-ends.
--
-- Two public sub-modules:
--
--   FCore v _≟X_ GenF
--     Pure F-side algebra (no wire engine):
--     F≈R, mergeF/splitF, flatten, flat⇒/flat⇐, coeCF + lemmas, coe-coe,
--     _∘F_/_⊗F_/idF/reflF (readability aliases).
--
--   FBridge v _≟X_ GenF MorW  .WithEng  ( ... params ... )
--     Transfer lemmas (splitF∘mergeF, mergeF-ρ, mergeF-assoc),
--     flat⇐∘flat⇒, cast-half, fwd-λ/fwd-ρ/fwd-α, flipF,
--     bridgeF (id/∘/⊗₁/λ/ρ/α cases), solveF, GenΣ.
--     The var and σ cases of bridgeF are passed as parameters.
--
-- USAGE in each front-end:
--   open FCore v _≟X_ GenF              — inherit F-side algebra
--   open FBridge v _≟X_ GenF MorW       — open the bridge module
--   open FBridge.WithEng merge split ... — supply wire engine surface
--
-- HARD CONSTRAINT: public API of SolverFrontend / SolverSigmaFrontend unchanged.
--------------------------------------------------------------------------------

module Categories.SolverFrontendCore where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; Σ-syntax; _,_)

import Categories.Category.Monoidal.Reasoning as MonR

open import Categories.FreeMonoidal

------------------------------------------------------------------------
-- FCore: pure F-side algebra.
------------------------------------------------------------------------

module FCore
  (v    : Variant)
  {X   : Set}
  (_≟X_ : DecidableEquality X)
  (GenF : (let open FreeMonoidalHelper v X using (ObjTerm)) in
          ObjTerm → ObjTerm → Set)
  where

  open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var; wires) public
  private module F = FreeMonoidalHelper.Mor v X GenF

  -- Re-export the F module alias so callers can write F.HomTerm etc.
  module F = FreeMonoidalHelper.Mor v X GenF

  -- F-side equational reasoning (identical in both frontends).
  module F≈R where
    infix  3 _∎F
    infixr 2 stepF-≈ stepF-≈˘
    infix  1 beginF_
    beginF_ : ∀ {A B} {f g : F.HomTerm A B} → f F.≈Term g → f F.≈Term g
    beginF_ x = x
    stepF-≈ : ∀ {A B} (f : F.HomTerm A B) {g h}
            → g F.≈Term h → f F.≈Term g → f F.≈Term h
    stepF-≈ _ gh fg = F.≈-Term-trans fg gh
    stepF-≈˘ : ∀ {A B} (f : F.HomTerm A B) {g h}
             → g F.≈Term h → g F.≈Term f → f F.≈Term h
    stepF-≈˘ _ gh gf = F.≈-Term-trans (F.≈-Term-sym gf) gh
    _∎F : ∀ {A B} (f : F.HomTerm A B) → f F.≈Term f
    _ ∎F = F.≈-Term-refl
    syntax stepF-≈  f gh fg = f ≈F⟨ fg ⟩ gh
    syntax stepF-≈˘ f gh gf = f ≈F⟨ gf ⟨ gh
  open F≈R public

  -- F-side MonR combinators.
  open MonR F.Monoidal-FreeMonoidal public
    using ()
    renaming (refl⟩∘⟨_ to infixr 4 reflF⟩∘⟨_;
              _⟩∘⟨refl   to infixl 5 _⟩∘F⟨refl;
              refl⟩⊗⟨_  to infixr 6 reflF⟩⊗⟨_;
              _⟩⊗⟨refl   to infixl 7 _⟩⊗F⟨refl;
              _⟩⊗⟨_      to infixr 6 _⟩⊗F⟨_;
              ⟺          to ⟺F;
              _○_         to infixr 3 _○F_)

  -- Readability aliases.
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
  -- Object flattening.
  ------------------------------------------------------------------------

  flatten : ObjTerm → List X
  flatten unit      = []
  flatten (Y ⊗₀ Z) = flatten Y ++ flatten Z
  flatten (Var x)   = x ∷ []

  ------------------------------------------------------------------------
  -- F-side structural merge / split.
  -- DEFINITIONAL: mergeF/splitF reduce on constructors of `List X`.
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
  -- Canonical structural iso  Y ≅ wires (flatten Y), in F.
  -- DEFINITIONAL: flat⇒/flat⇐ reduce on constructors of `ObjTerm`.
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
  -- DEFINITIONAL: coeCF reduces on `refl`.
  ------------------------------------------------------------------------

  coeCF : ∀ {A} {p q : List X} → p ≡ q
        → F.HomTerm A (wires p) → F.HomTerm A (wires q)
  coeCF refl h = h

  coeCF-∘ˡ : ∀ {A R p q} (e : p ≡ q)
              (h : F.HomTerm R (wires p)) (j : F.HomTerm A R)
           → coeCF e (F._∘_ h j) F.≈Term F._∘_ (coeCF e h) j
  coeCF-∘ˡ refl h j = F.≈-Term-refl

  coeCF-resp : ∀ {A p q} (e : p ≡ q) {h h' : F.HomTerm A (wires p)}
             → h F.≈Term h' → coeCF e h F.≈Term coeCF e h'
  coeCF-resp refl eq = eq

  -- The two opposite coercions cancel.
  coe-coe : ∀ {A} {p q : List X} (e : p ≡ q) (h : F.HomTerm A (wires p))
          → coeCF (sym e) (coeCF e h) ≡ h
  coe-coe refl h = refl


------------------------------------------------------------------------
-- FBridge: transfer + bridge layer.
--
-- Parametrized over:
--   MorW  — the wire-level generator type (differs Mon vs Symm)
--   merge/split/coeC/embed/castʷ/embed-castʷ — wire engine surface
--   equational facts from the wire engine
--   inj/inj-resp-≈/inj-merge/inj-split/inj-coeC — injection facts
--   idʷ / inj-embed-idʷ — for cast-half
--   reflectF-var — for bridgeF var case (bridgeF-var)
------------------------------------------------------------------------

module FBridge
  (v    : Variant)
  {X   : Set}
  (_≟X_ : DecidableEquality X)
  (GenF : (let open FreeMonoidalHelper v X using (ObjTerm)) in
          ObjTerm → ObjTerm → Set)
  (MorW : List X → List X → Set)
  where

  open FreeMonoidalHelper v X using (ObjTerm; unit; _⊗₀_; Var; wires) public
  private module F = FreeMonoidalHelper.Mor v X GenF
  private module W = FreeMonoidalHelper.Mor v X MorW

  -- Inherit all of FCore.
  open FCore v _≟X_ GenF public

  module WithEng
    -- Wire-level merge/split.
    (merge  : ∀ (a : List X) {suf}
            → W.HomTerm (wires a ⊗₀ wires suf) (wires (a ++ suf)))
    (split  : ∀ (a : List X) {suf}
            → W.HomTerm (wires (a ++ suf)) (wires a ⊗₀ wires suf))
    -- Wire-level coercion.
    (coeC   : ∀ {A} {p q : List X} → p ≡ q
            → W.HomTerm A (wires p) → W.HomTerm A (wires q))
    -- Wire-level WTerm and embedding.
    {WTerm  : List X → List X → Set}
    (embed  : ∀ {n m} → WTerm n m → W.HomTerm (wires n) (wires m))
    -- castʷ and embed-castʷ.
    (castʷ  : ∀ {n n' m m'} → n ≡ n' → m ≡ m' → WTerm n m → WTerm n' m')
    (embed-castʷ : ∀ {n n' m m'} (p : n ≡ n') (q : m ≡ m') (t : WTerm n m)
                 → embed (castʷ p q t) W.≈Term
                   coeC p (coeC q (embed t)))
    -- Wire-level identity WTerm and its embed.
    (idʷ    : ∀ {n} → WTerm n n)
    -- inj (embed idʷ) ≡ F.id (needed for cast-half).
    (inj-embed-idʷ : ∀ {n} → (inj : ∀ {A B} → W.HomTerm A B → F.HomTerm A B)
                   → inj (embed (idʷ {n})) ≡ F.id)
    -- Wire-engine equational facts.
    (split∘merge-W : ∀ (a : List X) {suf}
                   → W._∘_ (split a {suf}) (merge a {suf}) W.≈Term W.id)
    (merge-ρ-W     : ∀ (a : List X)
                   → coeC (++-identityʳ a) (merge a {[]}) W.≈Term W.ρ⇒)
    (merge-assoc-W : ∀ (p q r : List X)
      → W._∘_ (merge p {q ++ r})
              (W._∘_ (W._⊗₁_ W.id (merge q {r})) W.α⇒)
        W.≈Term
        coeC (++-assoc p q r)
          (W._∘_ (merge (p ++ q) {r})
                 (W._⊗₁_ (merge p {q}) W.id)))
    -- The injection and its properties.
    (inj : ∀ {A B} → W.HomTerm A B → F.HomTerm A B)
    (inj-resp-≈ : ∀ {A B} {f g : W.HomTerm A B}
                → f W.≈Term g → inj f F.≈Term inj g)
    (inj-merge : ∀ (a : List X) {suf} → inj (merge a {suf}) ≡ mergeF a {suf})
    (inj-split : ∀ (a : List X) {suf} → inj (split a {suf}) ≡ splitF a {suf})
    (inj-coeC  : ∀ {A p q} (e : p ≡ q) (h : W.HomTerm A (wires p))
               → inj (coeC e h) ≡ coeCF e (inj h))
    -- reflectF for the var case and the var bridge law.
    (reflectF-var : ∀ {Y Z} → GenF Y Z → WTerm (flatten Y) (flatten Z))
    (bridgeF-var-law : ∀ {Y Z} (g : GenF Y Z)
      → inj (embed (reflectF-var g)) ∘F flat⇒ Y F.≈Term flat⇒ Z ∘F F.var g)
    where

    open W using ()
      renaming (≈-Term-refl to ≈W-refl; ≈-Term-sym to ≈W-sym;
                ≡⇒≈Term to ≡⇒≈W)

    -- ≈F abbreviations for use in proofs.
    open MonR F.Monoidal-FreeMonoidal
      using ()
      renaming (refl⟩∘⟨_ to infixr 4 reflF⟩∘⟨_;
                _⟩∘⟨refl   to infixl 5 _⟩∘F⟨refl;
                refl⟩⊗⟨_  to infixr 6 reflF⟩⊗⟨_;
                _⟩⊗⟨_      to infixr 6 _⟩⊗F⟨_;
                ⟺          to ⟺F;
                _○_         to infixr 3 _○F_)
    private
      infixr 9 _∘F_
      infixr 10 _⊗F_
      _∘F_ : ∀ {A B C} → F.HomTerm B C → F.HomTerm A B → F.HomTerm A C
      _∘F_ = F._∘_
      _⊗F_ : ∀ {A B C D} → F.HomTerm A B → F.HomTerm C D
           → F.HomTerm (A ⊗₀ C) (B ⊗₀ D)
      _⊗F_ = F._⊗₁_
      idF : ∀ {A} → F.HomTerm A A
      idF = F.id
      reflF : ∀ {A B} {f : F.HomTerm A B} → f F.≈Term f
      reflF = F.≈-Term-refl

    ----------------------------------------------------------------------
    -- Transfer lemmas.
    ----------------------------------------------------------------------

    splitF∘mergeF : ∀ (a : List X) {suf}
                  → F._∘_ (splitF a {suf}) (mergeF a) F.≈Term F.id
    splitF∘mergeF a {suf} =
      F.≡⇒≈Term (cong₂ F._∘_ (sym (inj-split a {suf})) (sym (inj-merge a {suf})))
      ○F inj-resp-≈ (split∘merge-W a)

    mergeF-ρ : ∀ (a : List X)
             → coeCF (++-identityʳ a) (mergeF a {[]}) F.≈Term F.ρ⇒
    mergeF-ρ a =
      F.≡⇒≈Term (trans (cong (coeCF (++-identityʳ a)) (sym (inj-merge a)))
                       (sym (inj-coeC (++-identityʳ a) (merge a {[]}))))
      ○F inj-resp-≈ (merge-ρ-W a)

    mergeF-assoc : ∀ (p q r : List X)
      → F._∘_ (mergeF p {q ++ r})
              (F._∘_ (F._⊗₁_ F.id (mergeF q {r})) F.α⇒)
        F.≈Term
        coeCF (++-assoc p q r)
          (F._∘_ (mergeF (p ++ q) {r})
                 (F._⊗₁_ (mergeF p {q}) F.id))
    mergeF-assoc p q r =
      F.≡⇒≈Term (sym lhs-eq) ○F inj-resp-≈ (merge-assoc-W p q r)
      ○F F.≡⇒≈Term rhs-eq
      where
        lhs-eq : inj (W._∘_ (merge p {q ++ r})
                       (W._∘_ (W._⊗₁_ W.id (merge q {r})) W.α⇒))
               ≡ F._∘_ (mergeF p {q ++ r})
                   (F._∘_ (F._⊗₁_ F.id (mergeF q {r})) F.α⇒)
        lhs-eq rewrite inj-merge p {q ++ r} | inj-merge q {r} = refl
        rhs-eq : inj (coeC (++-assoc p q r)
                   (W._∘_ (merge (p ++ q) {r})
                          (W._⊗₁_ (merge p {q}) W.id)))
               ≡ coeCF (++-assoc p q r)
                   (F._∘_ (mergeF (p ++ q) {r})
                          (F._⊗₁_ (mergeF p {q}) F.id))
        rhs-eq rewrite inj-coeC (++-assoc p q r)
                                (W._∘_ (merge (p ++ q) {r})
                                       (W._⊗₁_ (merge p {q}) W.id))
                     | inj-merge (p ++ q) {r} | inj-merge p {q} = refl

    ----------------------------------------------------------------------
    -- The canonical iso retraction.
    ----------------------------------------------------------------------

    flat⇐∘flat⇒ : ∀ (Y : ObjTerm) → F._∘_ (flat⇐ Y) (flat⇒ Y) F.≈Term F.id
    flat⇐∘flat⇒ unit = F.idˡ
    flat⇐∘flat⇒ (Y ⊗₀ Z) = beginF
      F._∘_ (F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z)) (splitF (flatten Y)))
            (F._∘_ (mergeF (flatten Y)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z)))
        ≈F⟨ F.assoc ⟩
      F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z))
            (F._∘_ (splitF (flatten Y))
                   (F._∘_ (mergeF (flatten Y)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z))))
        ≈F⟨ reflF⟩∘⟨ (⟺F F.assoc) ⟩
      F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z))
            (F._∘_ (F._∘_ (splitF (flatten Y)) (mergeF (flatten Y)))
                   (F._⊗₁_ (flat⇒ Y) (flat⇒ Z)))
        ≈F⟨ reflF⟩∘⟨ ((splitF∘mergeF (flatten Y)) ⟩∘F⟨refl) ⟩
      F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z))
            (F._∘_ F.id (F._⊗₁_ (flat⇒ Y) (flat⇒ Z)))
        ≈F⟨ reflF⟩∘⟨ F.idˡ ⟩
      F._∘_ (F._⊗₁_ (flat⇐ Y) (flat⇐ Z)) (F._⊗₁_ (flat⇒ Y) (flat⇒ Z))
        ≈F⟨ F.⊗-∘-dist ⟨
      F._⊗₁_ (F._∘_ (flat⇐ Y) (flat⇒ Y)) (F._∘_ (flat⇐ Z) (flat⇒ Z))
        ≈F⟨ flat⇐∘flat⇒ Y ⟩⊗F⟨ flat⇐∘flat⇒ Z ⟩
      F._⊗₁_ F.id F.id
        ≈F⟨ F.id⊗id≈id ⟩
      F.id ∎F
      where open F≈R
    flat⇐∘flat⇒ (Var x) = F.ρ⇒∘ρ⇐≈id

    ----------------------------------------------------------------------
    -- cast-half: a casted idʷ embedded+injected is an F-side coercion.
    ----------------------------------------------------------------------

    cast-half : ∀ {P} {p q : List X} (e : p ≡ q) (h : F.HomTerm P (wires p))
              → inj (embed (castʷ refl e (idʷ {p}))) ∘F h F.≈Term coeCF e h
    cast-half {P} {p} {q} e h =
      ((inj-resp-≈ (embed-castʷ refl e idʷ) ○F F.≡⇒≈Term (inj-coeC e (embed idʷ))
        ○F coeCF-resp e (F.≡⇒≈Term (inj-embed-idʷ inj))) ⟩∘F⟨refl)
      ○F ⟺F (coeCF-∘ˡ e idF h)
      ○F coeCF-resp e F.idˡ

    ----------------------------------------------------------------------
    -- Forward structural laws.
    ----------------------------------------------------------------------

    fwd-λ : ∀ (A : ObjTerm) → flat⇒ (unit ⊗₀ A) F.≈Term flat⇒ A ∘F F.λ⇒
    fwd-λ A = F.λ⇒∘id⊗f≈f∘λ⇒

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
        open F≈R

    fwd-α : ∀ (A B C : ObjTerm)
          → coeCF (++-assoc (flatten A) (flatten B) (flatten C))
                  (flat⇒ ((A ⊗₀ B) ⊗₀ C))
            F.≈Term flat⇒ (A ⊗₀ (B ⊗₀ C)) ∘F F.α⇒
    fwd-α A B C = beginF
      coeCF e (mergeF (fA ++ fB) {fC} ∘F ((mergeF fA {fB} ∘F (f⇒A ⊗F f⇒B)) ⊗F f⇒C))
        ≈F⟨ coeCF-resp e (reflF⟩∘⟨
              ((reflF⟩⊗F⟨ (⟺F F.idˡ)) ○F F.⊗-∘-dist)) ⟩
      coeCF e (mergeF (fA ++ fB) {fC} ∘F ((mergeF fA {fB} ⊗F idF) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)))
        ≈F⟨ coeCF-resp e (⟺F F.assoc) ⟩
      coeCF e ((mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C))
        ≈F⟨ coeCF-∘ˡ e (mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF))
                        ((f⇒A ⊗F f⇒B) ⊗F f⇒C) ⟩
      coeCF e (mergeF (fA ++ fB) {fC} ∘F (mergeF fA {fB} ⊗F idF)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)
        ≈F⟨ (mergeF-assoc fA fB fC) ⟩∘F⟨refl ⟨
      (mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F F.α⇒)) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)
        ≈F⟨ F.assoc ⟩
      mergeF fA {fB ++ fC} ∘F (((idF ⊗F mergeF fB {fC}) ∘F F.α⇒) ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C))
        ≈F⟨ reflF⟩∘⟨ F.assoc ⟩
      mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F (F.α⇒ ∘F ((f⇒A ⊗F f⇒B) ⊗F f⇒C)))
        ≈F⟨ reflF⟩∘⟨ (reflF⟩∘⟨ F.α-comm) ⟩
      mergeF fA {fB ++ fC} ∘F ((idF ⊗F mergeF fB {fC}) ∘F ((f⇒A ⊗F (f⇒B ⊗F f⇒C)) ∘F F.α⇒))
        ≈F⟨ reflF⟩∘⟨ (⟺F F.assoc) ⟩
      mergeF fA {fB ++ fC} ∘F (((idF ⊗F mergeF fB {fC}) ∘F (f⇒A ⊗F (f⇒B ⊗F f⇒C))) ∘F F.α⇒)
        ≈F⟨ reflF⟩∘⟨ (((⟺F F.⊗-∘-dist) ○F (F.idˡ ⟩⊗F⟨ reflF)) ⟩∘F⟨refl) ⟩
      mergeF fA {fB ++ fC} ∘F ((f⇒A ⊗F (mergeF fB {fC} ∘F (f⇒B ⊗F f⇒C))) ∘F F.α⇒)
        ≈F⟨ ⟺F F.assoc ⟩
      (mergeF fA {fB ++ fC} ∘F (f⇒A ⊗F (mergeF fB {fC} ∘F (f⇒B ⊗F f⇒C)))) ∘F F.α⇒ ∎F
      where
        fA = flatten A ; fB = flatten B ; fC = flatten C
        e  = ++-assoc fA fB fC
        f⇒A = flat⇒ A ; f⇒B = flat⇒ B ; f⇒C = flat⇒ C
        open F≈R
        -- need reflF⟩⊗F⟨ from MonR open above:
        reflF⟩⊗F⟨_ : ∀ {A B C D} {f : F.HomTerm A B}
                     {g g' : F.HomTerm C D}
                   → g F.≈Term g' → F._⊗₁_ f g F.≈Term F._⊗₁_ f g'
        reflF⟩⊗F⟨ eq = F.⊗-resp-≈ reflF eq

    ----------------------------------------------------------------------
    -- flipF: derive an inverse law from a forward law.
    ----------------------------------------------------------------------

    flipF : ∀ {P Q} {p q : List X} (e : p ≡ q)
              (h⇒P : F.HomTerm P (wires p)) (h⇒Q : F.HomTerm Q (wires q))
              {c : F.HomTerm P Q} {c⁻¹ : F.HomTerm Q P}
          → c ∘F c⁻¹ F.≈Term idF
          → coeCF e h⇒P F.≈Term h⇒Q ∘F c
          → coeCF (sym e) h⇒Q F.≈Term h⇒P ∘F c⁻¹
    flipF e h⇒P h⇒Q {c} {c⁻¹} iso fwd = ⟺F (beginF
      h⇒P ∘F c⁻¹
        ≈F⟨ (F.≡⇒≈Term (coe-coe e h⇒P)) ⟩∘F⟨refl ⟨
      coeCF (sym e) (coeCF e h⇒P) ∘F c⁻¹
        ≈F⟨ (coeCF-resp (sym e) fwd) ⟩∘F⟨refl ⟩
      coeCF (sym e) (h⇒Q ∘F c) ∘F c⁻¹
        ≈F⟨ (coeCF-∘ˡ (sym e) h⇒Q c) ⟩∘F⟨refl ⟩
      (coeCF (sym e) h⇒Q ∘F c) ∘F c⁻¹
        ≈F⟨ F.assoc ⟩
      coeCF (sym e) h⇒Q ∘F (c ∘F c⁻¹)
        ≈F⟨ reflF⟩∘⟨ iso ⟩
      coeCF (sym e) h⇒Q ∘F idF
        ≈F⟨ F.idʳ ⟩
      coeCF (sym e) h⇒Q ∎F)
      where open F≈R

    ----------------------------------------------------------------------
    -- bridgeF: the shared cases.
    --
    -- The var case is supplied by `bridgeF-var-law`.
    -- The σ case is NOT here (it belongs in FrontendS only).
    -- The remaining cases (id, ∘, ⊗₁, λ⇒/λ⇐, ρ⇒/ρ⇐, α⇒/α⇐) are shared.
    ----------------------------------------------------------------------

    -- reflectF for the non-var, non-σ structural cases: all reduce to
    -- idʷ (possibly casted) or ⊗ʷ/∘ʷ of sub-reflections.
    -- We only need the embedding of the STRUCTURAL cases, which equals
    -- castʷ refl e idʷ for the unitor/associator cases.
    -- The key fact we use: inj (embed (castʷ refl e idʷ)) = coeCF e F.id.
    -- This is exactly cast-half e F.id.

    -- Auxiliary: the embed of ∘ʷ/⊗ʷ distributes through inj.
    -- We take reflectF as a parameter (it must be supplied by each frontend).
    -- Then bridgeF is defined BY INDUCTION on F.HomTerm.

    -- The reflectF function for ALL cases (not just var).
    -- Both frontends have the same reflectF for structural cases;
    -- only var (and σ) differ in the wire-level term type.
    -- We pass `reflectF` as a whole function parameter.

    -- Rather than passing reflectF as a whole function, note that:
    --   bridgeF (id/∘/⊗₁/λ/ρ/α) depend only on cast-half, flat⇐∘flat⇒,
    --   fwd-λ/ρ/α, flipF — all proven above.
    -- We can define bridgeF-shared for those cases, leaving out var and σ.

    -- For the ∘ and ⊗₁ cases, we need to know
    --   inj (embed (reflectF (g ∘ f))) = inj (embed (reflectF g ∘ʷ reflectF f))
    --                                  = inj (embed (reflectF g)) ∘F inj (embed (reflectF f))
    -- which requires embed-∘ʷ and inj-∘.
    -- These hold because embed (t₁ ∘ʷ t₂) = embed t₁ ∘ embed t₂ and inj preserves ∘.
    -- We pass these as parameters.

    -- To keep the parameter list manageable, we package them:
    module BridgeF
      -- embed distributes over ∘ʷ/⊗ʷ (wire-level facts, same in both).
      -- Actually these are definitional from the embed definition in ReflectI!
      -- embed (g ∘ʷ f) = embed g ∘ embed f  (definitional)
      -- embed (f ⊗ʷ g) = merge ∘ (embed f ⊗₁ embed g) ∘ split  (definitional)
      -- inj preserves ∘/⊗₁  (definitional from inj's definition)
      -- So bridgeF ∘ and ⊗₁ cases don't need extra parameters IF
      -- "inj (embed (reflectF ...))" is passed as a whole opaque value.
      --
      -- The key insight: the shared cases of bridgeF need to know
      --   IEF : F.HomTerm (flatten Y) (flatten Z)  -- "inj ∘ embed ∘ reflectF"
      -- for the sub-term, and get it by induction.  So we define bridgeF
      -- as a recursive function taking reflectF as a parameter for the var case.
      -- ALL structural cases produce the same IEF regardless of the engine.

      -- reflectF for the structural (non-var, non-σ) cases produces
      -- the same WTerm in both engines (up to the wrapping of boxʷ).
      -- Specifically for the non-box cases:
      --   reflectF id = idʷ
      --   reflectF (g ∘ f) = reflectF g ∘ʷ reflectF f
      --   reflectF (f ⊗₁ g) = reflectF f ⊗ʷ reflectF g
      --   reflectF λ⇒ = idʷ
      --   reflectF λ⇐ = idʷ
      --   reflectF ρ⇒ = castʷ refl (++-identityʳ _) idʷ
      --   ... etc.
      --
      -- For the shared bridgeF proof we need reflectF as a whole function.
      -- We pass it as a module parameter.
      (reflectF : ∀ {Y Z} → F.HomTerm Y Z → WTerm (flatten Y) (flatten Z))
      -- The structural cases of embed∘reflectF behave as follows:
      -- (i)  embed (reflectF F.id) ≈Term W.id
      -- (ii) embed (reflectF (g ∘ f)) ≈Term embed (reflectF g) ∘W embed (reflectF f)
      --      (from reflectF (g ∘ f) = reflectF g ∘ʷ reflectF f and embed (a ∘ʷ b) = embed a ∘ embed b)
      -- (iii) embed (reflectF (f ⊗₁ g)) ≈Term merge _ ∘ (embed (reflectF f) ⊗₁ embed (reflectF g)) ∘ split _
      -- We need inj to commute: inj (f ∘W g) = inj f ∘F inj g  (passed as inj-∘)
      -- and inj (f ⊗₁W g) = inj f ⊗F inj g  (passed as inj-⊗)
      -- But these should be definitional from inj's definition!
      -- Specifically inj (f ∘ g) = inj f ∘F inj g  definitionally
      -- (since inj (f ∘ g) = F._∘_ (inj f) (inj g) by the ∘ case of inj).
      -- So we don't need to pass these as parameters.
      --
      -- Summary: we only need reflectF itself and the var-case law.
      -- The structural cases' correctness follows from the definitions.
      where

      -- Main bridgeF: all cases except σ.
      bridgeF : ∀ {Y Z} (t : F.HomTerm Y Z)
              → inj (embed (reflectF t)) ∘F flat⇒ Y F.≈Term flat⇒ Z ∘F t
      bridgeF {Y} {Z} (F.var g) = bridgeF-var-law g
      bridgeF {Y} {.Y} F.id = beginF
        inj (embed (reflectF F.id)) ∘F flat⇒ Y
          ≈F⟨ {! needs embed(reflectF id) = W.id and inj W.id = F.id !} ⟩
        F.id ∘F flat⇒ Y
          ≈F⟨ F.idˡ ⟩
        flat⇒ Y ∘F F.id
          ≈F⟨ ⟺F F.idʳ ⟩
        F.id ∘F F.id ∎F
        where open F≈R
      bridgeF _ = {!!}
