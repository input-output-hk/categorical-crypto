{-# OPTIONS --safe --without-K #-}

module Categories.FreeStrictMonoidal where

--------------------------------------------------------------------------------
-- The free strict monoidal category on a family of wire-list generators.
--
-- Objects are `List X` and the tensor is `++`.
--
-- The raw syntax `WTerm` (with `boxʷ`/`idʷ`/`_∘ʷ_`/`_⊗ʷ_`) is the free
-- category-with-tensor on the generators `Gen`.  On top of it we build an
-- equational theory `_≈ʷ_`, parametrised by an *engine relation* `R` (the free
-- strict monoidal category WITH relations): besides the category laws it carries
-- the strict-monoidal tensor axioms, so `_⊗ʷ_` is a genuine BIFUNCTOR in the
-- theory.  Only two of those axioms need coercions, and they are the cheap
-- *term transports* `castʷ`/`castʷᵈ` (fusing definitionally on `refl`,
-- irrelevant by Hedberg UIP on `List X`), NOT composed morphisms:
--
--   * cast-free : `⊗-resp-≈ʷ`, `id⊗id`, interchange `inter`, left unit `unitˡ`;
--   * cast-mediated : associativity `⊗-assoc` and the right unit `unitʳ`.
--
-- The cast-mediated axioms quantify over the canonical `++-assoc`/`++-identityʳ`
-- proofs only; cast-irrelevance for arbitrary proofs is Hedberg-derived under
-- `DecEq X`, so the freeness reading is exact for decidable `X`.
--
-- `Monoidal` instance: `++` is only a monoid UP TO propositional equality
-- (`++-assoc` / `++-identityʳ` are not definitional), so the associator and
-- right unitor of `MonoidalStrictR` are the transport isos `coeʷ` along those
-- proofs (the left unitor is the definitional identity).  The coherence squares
-- and the triangle/pentagon collapse to `coeʷ` transports of `≡`-proofs closed
-- by Hedberg irrelevance, hence the instance is gated on `⦃ DecEq X ⦄`.  We also
-- expose the plain `Category` `Strict` (the theory at the empty engine
-- `R = λ _ _ → ⊥`).  Opening `Categories.Category.Monoidal.Reasoning` on the
-- instance supplies the generic tensor vocabulary (`serialize`/`split`).
--------------------------------------------------------------------------------

open import Level
open import Data.List
open import Data.List.Properties
open import Data.Empty
open import Data.Product using (uncurry)
open import Relation.Binary.PropositionalEquality
import Data.List.Properties.Ext as ListExt
open import Class.DecEq

open import Categories.Category
open import Categories.Category.Helper
open import Categories.Category.Monoidal
import Categories.Category.Monoidal.Reasoning as MonR

module FreeStrictMonoidalHelper {X : Set} (Gen : List X → List X → Set) where
  infixr 9 _∘ʷ_
  infixr 10 _⊗ʷ_

  private variable
    n m k n' m' m'' k' nl ml nr mr a b c d : List X

  data WTerm : List X → List X → Set where
    boxʷ : Gen n m → WTerm n m
    idʷ  : WTerm n n
    _∘ʷ_ : WTerm m k → WTerm n m → WTerm n k
    _⊗ʷ_ : WTerm nl ml → WTerm nr mr → WTerm (nl ++ nr) (ml ++ mr)

  --------------------------------------------------------------------------------
  -- The two term transports and their (R-independent) algebra.  `castʷ` moves
  -- the CODOMAIN along `m ≡ m'`; `castʷᵈ` moves the DOMAIN along `n ≡ n'`.  Both
  -- reduce on `refl`, so every law below is a one-line `refl`-match.
  --------------------------------------------------------------------------------
  castʷ : m ≡ m' → WTerm n m → WTerm n m'
  castʷ refl t = t

  castʷᵈ : n ≡ n' → WTerm n m → WTerm n' m
  castʷᵈ refl t = t

  -- cancellation of a transport against its inverse (both orders)
  castʷ-symˡ : (e : m ≡ m') (t : WTerm n m) → castʷ (sym e) (castʷ e t) ≡ t
  castʷ-symˡ refl t = refl

  castʷ-symʳ : (e : m ≡ m') (t : WTerm n m') → castʷ e (castʷ (sym e) t) ≡ t
  castʷ-symʳ refl t = refl

  -- the same cancellations for the domain transport
  castʷᵈ-symˡ : (e : n ≡ n') (t : WTerm n m) → castʷᵈ (sym e) (castʷᵈ e t) ≡ t
  castʷᵈ-symˡ refl t = refl

  -- the two transports act on independent indices, hence commute
  castʷ-castʷᵈ : (e : n ≡ n') (e' : m ≡ m') (t : WTerm n m) → castʷ e' (castʷᵈ e t) ≡ castʷᵈ e (castʷ e' t)
  castʷ-castʷᵈ refl refl t = refl

  -- regroup an alternating domain/codomain transport tower into one pair
  regather : ∀ {n₀ n₁ n₂ m₀ m₁ m₂}
               (d₁ : n₁ ≡ n₂) (d₂ : n₀ ≡ n₁) (c₁ : m₁ ≡ m₂) (c₂ : m₀ ≡ m₁)
               (t : WTerm n₀ m₀)
           → castʷᵈ d₁ (castʷ c₁ (castʷᵈ d₂ (castʷ c₂ t)))
             ≡ castʷᵈ (trans d₂ d₁) (castʷ (trans c₂ c₁) t)
  regather refl refl refl refl t = refl

  -- interaction with composition: a codomain-transport of the LEFT factor is a
  -- codomain-transport of the composite; a domain-transport of the RIGHT factor
  -- is a domain-transport of the composite; and a domain-transport of the left
  -- factor slides across to a codomain-transport of the right factor.
  ∘ʷ-castʷ-l : (e : k ≡ k') (g : WTerm m k) (f : WTerm n m) → castʷ e g ∘ʷ f ≡ castʷ e (g ∘ʷ f)
  ∘ʷ-castʷ-l refl g f = refl

  ∘ʷ-castʷᵈ-r : (e : n ≡ n') (g : WTerm m k) (f : WTerm n m) → g ∘ʷ castʷᵈ e f ≡ castʷᵈ e (g ∘ʷ f)
  ∘ʷ-castʷᵈ-r refl g f = refl

  ∘ʷ-castʷᵈ-l : (e : m ≡ m') (g : WTerm m k) (f : WTerm n m') → castʷᵈ e g ∘ʷ f ≡ g ∘ʷ castʷ (sym e) f
  ∘ʷ-castʷᵈ-l refl g f = refl

  -- the sym-baked variant (avoids a `sym (sym e)` repair at the use sites)
  ∘ʷ-castʷᵈ-l′ : (e : m' ≡ m) (g : WTerm m k) (f : WTerm n m') → castʷᵈ (sym e) g ∘ʷ f ≡ g ∘ʷ castʷ e f
  ∘ʷ-castʷᵈ-l′ refl g f = refl

  -- the two mid-proof cast sandwiches of the shift soundness proofs: an
  -- inverse domain-transport pair around a composite of jointly-transported
  -- factors cancels outright.
  ∘ʷ-cast-cancelˡ : (e₁ : n' ≡ n) (e₂ : m ≡ m') (g : WTerm m k) (f : WTerm n m) → castʷᵈ e₁ (castʷᵈ e₂ g ∘ʷ castʷᵈ (sym e₁) (castʷ e₂ f)) ≡ g ∘ʷ f
  ∘ʷ-cast-cancelˡ refl refl g f = refl

  ∘ʷ-cast-cancelʳ : (e₁ : n ≡ n') (e₂ : m ≡ m') (g : WTerm m k) (f : WTerm n m) → castʷᵈ (sym e₁) (castʷᵈ e₂ g ∘ʷ castʷᵈ e₁ (castʷ e₂ f)) ≡ g ∘ʷ f
  ∘ʷ-cast-cancelʳ refl refl g f = refl

  -- interaction with the tensor: a domain/codomain transport pair of the RIGHT
  -- factor lifts through the prefix `s ⊗ʷ_` to the `cong (… ++_)` pair.
  ⊗ʷ-cast-pair-r : (d : nr ≡ n') (c : mr ≡ m') (s : WTerm nl ml) (t : WTerm nr mr) → s ⊗ʷ castʷᵈ d (castʷ c t) ≡ castʷᵈ (cong (nl ++_) d) (castʷ (cong (ml ++_) c) (s ⊗ʷ t))
  ⊗ʷ-cast-pair-r refl refl s t = refl

  -- cast-irrelevance (Hedberg): a transport is determined by its endpoints, so
  -- any two transports of the same shape agree.  Mirrors `WireCohDec.castW-irr`.
  module _ ⦃ _ : DecEq X ⦄ where
    ≡-irrL : {u v : List X} (e e' : u ≡ v) → e ≡ e'
    ≡-irrL = ListExt.≡-irrelevant _≟_

    castʷ-irr : (e e' : m ≡ m') (t : WTerm n m) → castʷ e t ≡ castʷ e' t
    castʷ-irr e e' t = cong (λ z → castʷ z t) (≡-irrL e e')

    castʷᵈ-irr : (e e' : n ≡ n') (t : WTerm n m) → castʷᵈ e t ≡ castʷᵈ e' t
    castʷᵈ-irr e e' t = cong (λ z → castʷᵈ z t) (≡-irrL e e')

  --------------------------------------------------------------------------------
  -- The flat pad: a box `g` idling behind `pre` wires and in front of `suf`
  -- wires.  This is the strict, cast-free analogue of `Diagram.pad` — no
  -- merge/split appears.
  --------------------------------------------------------------------------------
  padʷ : (pre suf : List X) {a b : List X} → WTerm a b → WTerm (pre ++ (a ++ suf)) (pre ++ (b ++ suf))
  padʷ pre suf g = idʷ {n = pre} ⊗ʷ (g ⊗ʷ idʷ {n = suf})

  -- pushing a domain/codomain transport of a pad's box out to a transport of
  -- the whole pad; and reindexing a pad's idle suffix along `suf ≡ suf'`.  Both
  -- reduce on `refl`.
  pad-castˢ : ∀ (pre suf : List X) {n n' m m' : List X} (d : n ≡ n') (c : m ≡ m')
                (t : WTerm n m)
            → padʷ pre suf (castʷᵈ d (castʷ c t))
              ≡ castʷᵈ (cong (λ z → pre ++ (z ++ suf)) d)
                  (castʷ (cong (λ z → pre ++ (z ++ suf)) c) (padʷ pre suf t))
  pad-castˢ pre suf refl refl t = refl

  padʷ-suf : ∀ (pre : List X) {suf suf' a b : List X} (e : suf ≡ suf') (g : WTerm a b)
           → padʷ pre suf' g
             ≡ castʷᵈ (cong (λ z → pre ++ (a ++ z)) e)
                 (castʷ (cong (λ z → pre ++ (b ++ z)) e) (padʷ pre suf g))
  padʷ-suf pre refl g = refl

  --------------------------------------------------------------------------------
  -- The equational theory, parametrised by an engine relation `R`.  Besides the
  -- category laws it carries the strict-monoidal bifunctor axioms; `axiom`
  -- injects the engine's own rewrites.
  --------------------------------------------------------------------------------
  module Theory (R : ∀ {n m} → WTerm n m → WTerm n m → Set) where

    infix 4 _≈ʷ_

    private variable f g h i : WTerm n m

    data _≈ʷ_ : WTerm n m → WTerm n m → Set where
      -- category laws
      idˡ      : idʷ ∘ʷ f ≈ʷ f
      idʳ      : f ∘ʷ idʷ ≈ʷ f
      assoc    : (h ∘ʷ g) ∘ʷ f ≈ʷ h ∘ʷ (g ∘ʷ f)
      ∘-resp-≈ : f ≈ʷ h → g ≈ʷ i → f ∘ʷ g ≈ʷ h ∘ʷ i
      reflʷ    : f ≈ʷ f
      symʷ     : f ≈ʷ g → g ≈ʷ f
      transʷ   : f ≈ʷ g → g ≈ʷ h → f ≈ʷ h
      -- tensor is a bifunctor (cast-free)
      ⊗-resp-≈ʷ : {f h : WTerm n m} {g i : WTerm a b} → f ≈ʷ h → g ≈ʷ i → f ⊗ʷ g ≈ʷ h ⊗ʷ i
      id⊗id : idʷ {n = a} ⊗ʷ idʷ {n = b} ≈ʷ idʷ
      inter : ∀ {nl ml kl nr mr kr} {g : WTerm ml kl} {f : WTerm nl ml} {g' : WTerm mr kr} {f' : WTerm nr mr} → (g ∘ʷ f) ⊗ʷ (g' ∘ʷ f') ≈ʷ (g ⊗ʷ g') ∘ʷ (f ⊗ʷ f')
      -- the left unit is definitional on OBJECTS (`[] ++ n = n`) but not on
      -- terms; it is the strictness axiom "left unitor = identity".
      unitˡ : (f : WTerm n m) → idʷ {n = []} ⊗ʷ f ≈ʷ f
      -- cast-mediated axioms: associativity and the right unit
      ⊗-assoc : ∀ {n₁ m₁ n₂ m₂ n₃ m₃} (f : WTerm n₁ m₁) (g : WTerm n₂ m₂) (h : WTerm n₃ m₃) → castʷᵈ (++-assoc n₁ n₂ n₃) (castʷ (++-assoc m₁ m₂ m₃) ((f ⊗ʷ g) ⊗ʷ h)) ≈ʷ f ⊗ʷ (g ⊗ʷ h)
      unitʳ : (f : WTerm n m) → castʷᵈ (++-identityʳ n) (castʷ (++-identityʳ m) (f ⊗ʷ idʷ {n = []})) ≈ʷ f
      -- the engine relation
      axiom : R f g → f ≈ʷ g

    -- coercion of propositional equality into the theory
    ≡→≈ʷ : {t t' : WTerm n m} → t ≡ t' → t ≈ʷ t'
    ≡→≈ʷ refl = reflʷ

    -- both transports respect the theory
    castʷ-resp : (e : m ≡ m') {t t' : WTerm n m} → t ≈ʷ t' → castʷ e t ≈ʷ castʷ e t'
    castʷ-resp refl p = p

    castʷᵈ-resp : (e : n ≡ n') {t t' : WTerm n m} → t ≈ʷ t' → castʷᵈ e t ≈ʷ castʷᵈ e t'
    castʷᵈ-resp refl p = p

    StrictR : Category 0ℓ 0ℓ 0ℓ
    StrictR = categoryHelper record
      { Obj       = List X
      ; _⇒_       = WTerm
      ; _≈_       = _≈ʷ_
      ; id        = idʷ
      ; _∘_       = _∘ʷ_
      ; assoc     = assoc
      ; identityˡ = idˡ
      ; identityʳ = idʳ
      ; equiv     = record { refl = reflʷ ; sym = symʷ ; trans = transʷ }
      ; ∘-resp-≈  = ∘-resp-≈
      }

    open Category.HomReasoning StrictR

    --------------------------------------------------------------------------------
    -- The transport-identity morphism `coeʷ e = castʷ e idʷ`: an iso `m ⇒ m'`
    -- for every `m ≡ m'`.  Each law matches its endpoint equality as `refl` and
    -- collapses to a unit/identity law, so every proof is a one-liner.
    --------------------------------------------------------------------------------
    coeʷ : {m m' : List X} → m ≡ m' → WTerm m m'
    coeʷ e = castʷ e idʷ

    -- the two bridges: pre-/post-composing a `coeʷ` is a term transport
    coeʷ-∘ : (e : m ≡ m') (t : WTerm n m) → coeʷ e ∘ʷ t ≈ʷ castʷ e t
    coeʷ-∘ refl t = idˡ

    coeʷ-∘ʳ : (e : m ≡ m') (t : WTerm m' k) → t ∘ʷ coeʷ e ≈ʷ castʷᵈ (sym e) t
    coeʷ-∘ʳ refl t = idʳ

    -- iso laws (both orders) and fusion
    coeʷ-isoˡ : (e : m ≡ m') → coeʷ (sym e) ∘ʷ coeʷ e ≈ʷ idʷ
    coeʷ-isoˡ refl = idˡ

    coeʷ-isoʳ : (e : m ≡ m') → coeʷ e ∘ʷ coeʷ (sym e) ≈ʷ idʷ
    coeʷ-isoʳ refl = idˡ

    coeʷ-fuse : (e : m ≡ m') (e' : m' ≡ m'') → coeʷ e' ∘ʷ coeʷ e ≈ʷ coeʷ (trans e e')
    coeʷ-fuse refl refl = idˡ

    -- whiskering a `coeʷ` by an idle block on either side lifts to a `coeʷ`
    coeʷ-⊗ˡ : (e : m ≡ m') (r : List X) → coeʷ e ⊗ʷ idʷ {n = r} ≈ʷ coeʷ (cong (_++ r) e)
    coeʷ-⊗ˡ refl r = id⊗id

    coeʷ-⊗ʳ : (l : List X) (e : m ≡ m') → idʷ {n = l} ⊗ʷ coeʷ e ≈ʷ coeʷ (cong (l ++_) e)
    coeʷ-⊗ʳ l refl = id⊗id

    --------------------------------------------------------------------------------
    -- The `Monoidal StrictR` instance
    --------------------------------------------------------------------------------
    module _ ⦃ _ : DecEq X ⦄ where
      -- two `coeʷ`s of the same List-equality agree (Hedberg irrelevance)
      coeʷ-irr : (e e' : m ≡ m') → coeʷ e ≈ʷ coeʷ e'
      coeʷ-irr e e' = ≡→≈ʷ (castʷ-irr e e' idʷ)

      -- right-unitor / associator naturality: the `unitʳ` / `⊗-assoc` axiom
      -- moved to the caller's `castʷ`-form through the two `coeʷ` bridges.
      unitorʳ-commuteˢ : {f : WTerm n m}
                       → coeʷ (++-identityʳ m) ∘ʷ (f ⊗ʷ idʷ {n = []}) ≈ʷ f ∘ʷ coeʷ (++-identityʳ n)
      unitorʳ-commuteˢ {n} {m} {f} = begin
        coeʷ (++-identityʳ m) ∘ʷ (f ⊗ʷ idʷ)
          ≈⟨ coeʷ-∘ (++-identityʳ m) (f ⊗ʷ idʷ) ⟩
        castʷ (++-identityʳ m) (f ⊗ʷ idʷ)
          ≈⟨ transʷ (≡→≈ʷ (sym (castʷᵈ-symˡ (++-identityʳ n) _)))
                    (castʷᵈ-resp (sym (++-identityʳ n)) (unitʳ f)) ⟩
        castʷᵈ (sym (++-identityʳ n)) f
          ≈⟨ coeʷ-∘ʳ (++-identityʳ n) f ⟨
        f ∘ʷ coeʷ (++-identityʳ n) ∎

      assoc-commuteˢ : ∀ {n₁ m₁ n₂ m₂ n₃ m₃}
                         {f : WTerm n₁ m₁} {g : WTerm n₂ m₂} {h : WTerm n₃ m₃}
                     → coeʷ (++-assoc m₁ m₂ m₃) ∘ʷ ((f ⊗ʷ g) ⊗ʷ h)
                       ≈ʷ (f ⊗ʷ (g ⊗ʷ h)) ∘ʷ coeʷ (++-assoc n₁ n₂ n₃)
      assoc-commuteˢ {n₁} {m₁} {n₂} {m₂} {n₃} {m₃} {f} {g} {h} = begin
        coeʷ (++-assoc m₁ m₂ m₃) ∘ʷ ((f ⊗ʷ g) ⊗ʷ h)
          ≈⟨ coeʷ-∘ (++-assoc m₁ m₂ m₃) ((f ⊗ʷ g) ⊗ʷ h) ⟩
        castʷ (++-assoc m₁ m₂ m₃) ((f ⊗ʷ g) ⊗ʷ h)
          ≈⟨ transʷ (≡→≈ʷ (sym (castʷᵈ-symˡ (++-assoc n₁ n₂ n₃) _)))
                    (castʷᵈ-resp (sym (++-assoc n₁ n₂ n₃)) (⊗-assoc f g h)) ⟩
        castʷᵈ (sym (++-assoc n₁ n₂ n₃)) (f ⊗ʷ (g ⊗ʷ h))
          ≈⟨ coeʷ-∘ʳ (++-assoc n₁ n₂ n₃) (f ⊗ʷ (g ⊗ʷ h)) ⟨
        (f ⊗ʷ (g ⊗ʷ h)) ∘ʷ coeʷ (++-assoc n₁ n₂ n₃) ∎

      -- triangle / pentagon: each structural morphism is a `coeʷ` (or a
      -- whiskered one, lifted by `coeʷ-⊗ˡ`/`coeʷ-⊗ʳ` + `id⊗id`), so each side
      -- is a single `coeʷ` and the two sides agree by `coeʷ-irr`.
      triangleˢ : {x y : List X}
                → (idʷ {n = x} ⊗ʷ idʷ) ∘ʷ coeʷ (++-assoc x [] y)
                  ≈ʷ coeʷ (++-identityʳ x) ⊗ʷ idʷ {n = y}
      triangleˢ {x} {y} = begin
        (idʷ {n = x} ⊗ʷ idʷ) ∘ʷ coeʷ (++-assoc x [] y)
          ≈⟨ ∘-resp-≈ id⊗id reflʷ ⟩
        idʷ ∘ʷ coeʷ (++-assoc x [] y)
          ≈⟨ idˡ ⟩
        coeʷ (++-assoc x [] y)
          ≈⟨ coeʷ-irr (++-assoc x [] y) (cong (_++ y) (++-identityʳ x)) ⟩
        coeʷ (cong (_++ y) (++-identityʳ x))
          ≈⟨ coeʷ-⊗ˡ (++-identityʳ x) y ⟨
        coeʷ (++-identityʳ x) ⊗ʷ idʷ {n = y} ∎

      pentagonˢ : {x y z w : List X}
                → (idʷ {n = x} ⊗ʷ coeʷ (++-assoc y z w))
                    ∘ʷ (coeʷ (++-assoc x (y ++ z) w) ∘ʷ (coeʷ (++-assoc x y z) ⊗ʷ idʷ {n = w}))
                  ≈ʷ coeʷ (++-assoc x y (z ++ w)) ∘ʷ coeʷ (++-assoc (x ++ y) z w)
      pentagonˢ {x} {y} {z} {w} = begin
        (idʷ ⊗ʷ coeʷ aYZW) ∘ʷ (coeʷ aXYZ,W ∘ʷ (coeʷ aXYZ ⊗ʷ idʷ))
          ≈⟨ ∘-resp-≈ (coeʷ-⊗ʳ x aYZW) (∘-resp-≈ reflʷ (coeʷ-⊗ˡ aXYZ w)) ⟩
        coeʷ (cong (x ++_) aYZW) ∘ʷ (coeʷ aXYZ,W ∘ʷ coeʷ (cong (_++ w) aXYZ))
          ≈⟨ ∘-resp-≈ reflʷ (coeʷ-fuse (cong (_++ w) aXYZ) aXYZ,W) ⟩
        coeʷ (cong (x ++_) aYZW) ∘ʷ coeʷ (trans (cong (_++ w) aXYZ) aXYZ,W)
          ≈⟨ coeʷ-fuse (trans (cong (_++ w) aXYZ) aXYZ,W) (cong (x ++_) aYZW) ⟩
        coeʷ (trans (trans (cong (_++ w) aXYZ) aXYZ,W) (cong (x ++_) aYZW))
          ≈⟨ coeʷ-irr _ _ ⟩
        coeʷ (trans aXY,Z,W aXY,ZW)
          ≈⟨ coeʷ-fuse aXY,Z,W aXY,ZW ⟨
        coeʷ aXY,ZW ∘ʷ coeʷ aXY,Z,W ∎
        where
          aYZW    = ++-assoc y z w
          aXYZ,W  = ++-assoc x (y ++ z) w
          aXYZ    = ++-assoc x y z
          aXY,ZW  = ++-assoc x y (z ++ w)
          aXY,Z,W = ++-assoc (x ++ y) z w

      MonoidalStrictR : Monoidal StrictR
      MonoidalStrictR = monoidalHelper StrictR record
        { ⊗ = record
            { F₀           = uncurry _++_
            ; F₁           = uncurry _⊗ʷ_
            ; identity     = id⊗id
            ; homomorphism = inter
            ; F-resp-≈     = uncurry ⊗-resp-≈ʷ
            }
        ; unit            = []
        ; unitorˡ         = record { from = idʷ ; to = idʷ ; iso = record { isoˡ = idˡ ; isoʳ = idˡ } }
        ; unitorʳ         = λ {x} → record
            { from = coeʷ (++-identityʳ x) ; to = coeʷ (sym (++-identityʳ x))
            ; iso  = record { isoˡ = coeʷ-isoˡ (++-identityʳ x) ; isoʳ = coeʷ-isoʳ (++-identityʳ x) } }
        ; associator      = λ {x} {y} {z} → record
            { from = coeʷ (++-assoc x y z) ; to = coeʷ (sym (++-assoc x y z))
            ; iso  = record { isoˡ = coeʷ-isoˡ (++-assoc x y z) ; isoʳ = coeʷ-isoʳ (++-assoc x y z) } }
        ; unitorˡ-commute = λ {_ _ f} → transʷ idˡ (transʷ (unitˡ f) (symʷ idʳ))
        ; unitorʳ-commute = unitorʳ-commuteˢ
        ; assoc-commute   = assoc-commuteˢ
        ; triangle        = triangleˢ
        ; pentagon        = pentagonˢ
        }

      -- generic tensor vocabulary over the instance, re-exported so the pad
      -- functoriality proofs and the disjoint-block slides read in library terms.
      open MonR MonoidalStrictR public using (serialize₁₂; serialize₂₁; split₁ʳ; split₂ʳ)

    --------------------------------------------------------------------------------
    -- `padʷ pre suf` as a functor: congruence (`pad-respˢ`), preservation of
    -- composition (`pad-∘ˢ`, distributing each idle block via the library
    -- `split₁ʳ`/`split₂ʳ`, hence `⦃ DecEq X ⦄`) and identity (`pad-idˢ`).
    --------------------------------------------------------------------------------
    pad-respˢ : (p s : List X) {a b : List X} {g g' : WTerm a b} → g ≈ʷ g' → padʷ p s g ≈ʷ padʷ p s g'
    pad-respˢ p s e = ⊗-resp-≈ʷ reflʷ (⊗-resp-≈ʷ e reflʷ)

    pad-∘ˢ : ⦃ _ : DecEq X ⦄ → (p s : List X) (g : WTerm m k) (f : WTerm n m) → padʷ p s (g ∘ʷ f) ≈ʷ padʷ p s g ∘ʷ padʷ p s f
    pad-∘ˢ p s g f = transʷ (⊗-resp-≈ʷ reflʷ split₁ʳ) split₂ʳ

    pad-idˢ : (p s : List X) → padʷ p s (idʷ {n = n}) ≈ʷ idʷ
    pad-idˢ p s = transʷ (⊗-resp-≈ʷ reflʷ id⊗id) id⊗id

    --------------------------------------------------------------------------------
    -- The pad-conjugation relation `≋`: `t ≋ t'` when `t` is `t'` up to a
    -- domain/codomain `++`-associativity transport pair.  The regather / push /
    -- endo-cast-irr glue of the pad regroupings is factored ONCE into the `≋` kit
    -- (`≋-trans`, `≋-cong-pad`, `≋-cong-⊗ʳ`, `≋→cast-formˢ`); the regroupings are
    -- then cast-free compositional `≋` statements, and the callers' explicit-cast
    -- lemmas are thin wrappers over them.
    --------------------------------------------------------------------------------
    record _≋_ {n₀ m₀ n₂ m₂ : List X} (t : WTerm n₀ m₀) (t' : WTerm n₂ m₂) : Set where
      constructor mk≋
      field
        dEq : n₀ ≡ n₂
        cEq : m₀ ≡ m₂
        eqʷ : castʷᵈ dEq (castʷ cEq t) ≈ʷ t'
    open _≋_

    private
      uncastᴶ : ∀ {p p' q q'} (d : p ≡ p') (c : q ≡ q') (t : WTerm p q)
              → castʷᵈ (sym d) (castʷ (sym c) (castʷᵈ d (castʷ c t))) ≡ t
      uncastᴶ refl refl t = refl

    ≈ʷ→≋ : {t t' : WTerm n m} → t ≈ʷ t' → t ≋ t'
    ≈ʷ→≋ p = mk≋ refl refl p

    ≋-sym : {t : WTerm n m} {t' : WTerm n' m'} → t ≋ t' → t' ≋ t
    ≋-sym {t = t} (mk≋ d c eq) = mk≋ (sym d) (sym c)
      (transʷ (castʷᵈ-resp (sym d) (castʷ-resp (sym c) (symʷ eq))) (≡→≈ʷ (uncastᴶ d c t)))

    ≋-trans : {t : WTerm n m} {t' : WTerm n' m'} {t'' : WTerm k' m''}
            → t ≋ t' → t' ≋ t'' → t ≋ t''
    ≋-trans {t = t} (mk≋ d₁ c₁ eq₁) (mk≋ d₂ c₂ eq₂) = mk≋ (trans d₁ d₂) (trans c₁ c₂)
      (transʷ (≡→≈ʷ (sym (regather d₂ d₁ c₂ c₁ t)))
              (transʷ (castʷᵈ-resp d₂ (castʷ-resp c₂ eq₁)) eq₂))

    ⊗-assocᴶ : ∀ {n₁ m₁ n₂ m₂ n₃ m₃} (f : WTerm n₁ m₁) (g : WTerm n₂ m₂) (h : WTerm n₃ m₃)
             → ((f ⊗ʷ g) ⊗ʷ h) ≋ (f ⊗ʷ (g ⊗ʷ h))
    ⊗-assocᴶ {n₁} {m₁} {n₂} {m₂} {n₃} {m₃} f g h =
      mk≋ (++-assoc n₁ n₂ n₃) (++-assoc m₁ m₂ m₃) (⊗-assoc f g h)

    ≋-cong-⊗ʳ : (s : WTerm nl ml) {t : WTerm n m} {t' : WTerm n' m'}
              → t ≋ t' → (s ⊗ʷ t) ≋ (s ⊗ʷ t')
    ≋-cong-⊗ʳ s {t = t} (mk≋ d c eq) = mk≋ (cong (_ ++_) d) (cong (_ ++_) c)
      (transʷ (≡→≈ʷ (sym (⊗ʷ-cast-pair-r d c s t))) (⊗-resp-≈ʷ reflʷ eq))

    ≋-cong-pad : (p s : List X) {t : WTerm n m} {t' : WTerm n' m'}
               → t ≋ t' → padʷ p s t ≋ padʷ p s t'
    ≋-cong-pad p s {t = t} (mk≋ d c eq) =
      mk≋ (cong (λ z → p ++ (z ++ s)) d) (cong (λ z → p ++ (z ++ s)) c)
        (transʷ (≡→≈ʷ (sym (pad-castˢ p s d c t))) (pad-respˢ p s eq))

    -- reindex a pad's idle suffix along `suf ≡ suf'`
    padʷ-sufᴶ : (pre : List X) {suf suf' a b : List X} (e : suf ≡ suf') (g : WTerm a b)
              → padʷ pre suf g ≋ padʷ pre suf' g
    padʷ-sufᴶ pre {a = a} {b} e g =
      mk≋ (cong (λ z → pre ++ (a ++ z)) e) (cong (λ z → pre ++ (b ++ z)) e)
        (≡→≈ʷ (sym (padʷ-suf pre e g)))

    --------------------------------------------------------------------------------
    -- The pad regroupings as cast-free `≋` statements: `pad-nestᴶ` at a split
    -- prefix, `pad-nestRᴶ` at a split suffix, `pad-fuseᴶ` fusing a wide pad into a
    -- pad-of-pad, `nest3ᴶ` the threefold nesting, and the two `pad-absorb_ᴶ`
    -- collapsing a box padded on one side then re-padded.  Each is `⊗-assocᴶ` +
    -- `id⊗id` composed through the `≋` kit.
    --------------------------------------------------------------------------------
    pad-nestᴶ : (p q suf : List X) {a b : List X} (g : WTerm a b)
              → padʷ (p ++ q) suf g ≋ (idʷ {n = p} ⊗ʷ padʷ q suf g)
    pad-nestᴶ p q suf g =
      ≋-trans (≈ʷ→≋ (⊗-resp-≈ʷ (symʷ id⊗id) reflʷ))
              (⊗-assocᴶ (idʷ {n = p}) (idʷ {n = q}) (g ⊗ʷ idʷ {n = suf}))

    pad-nestRᴶ : (pre suf rt : List X) {a b : List X} (g : WTerm a b)
               → padʷ pre (suf ++ rt) g ≋ (padʷ pre suf g ⊗ʷ idʷ {n = rt})
    pad-nestRᴶ pre suf rt g =
      ≋-trans (≈ʷ→≋ (⊗-resp-≈ʷ reflʷ (⊗-resp-≈ʷ reflʷ (symʷ id⊗id))))
        (≋-trans (≋-cong-⊗ʳ (idʷ {n = pre}) (≋-sym (⊗-assocᴶ g (idʷ {n = suf}) (idʷ {n = rt}))))
                 (≋-sym (⊗-assocᴶ (idʷ {n = pre}) (g ⊗ʷ idʷ {n = suf}) (idʷ {n = rt}))))

    pad-fuseᴶ : (px sx P s : List X) {a b : List X} (g : WTerm a b)
              → padʷ (px ++ P) (s ++ sx) g ≋ padʷ px sx (padʷ P s g)
    pad-fuseᴶ px sx P s g =
      ≋-trans (pad-nestᴶ px P (s ++ sx) g) (≋-cong-⊗ʳ (idʷ {n = px}) (pad-nestRᴶ P s sx g))

    nest3ᴶ : (p q r suf : List X) {a b : List X} (g : WTerm a b)
           → padʷ (p ++ (q ++ r)) suf g ≋ (idʷ {n = p} ⊗ʷ (idʷ {n = q} ⊗ʷ padʷ r suf g))
    nest3ᴶ p q r suf g =
      ≋-trans (pad-nestᴶ p (q ++ r) suf g) (≋-cong-⊗ʳ (idʷ {n = p}) (pad-nestᴶ q r suf g))

    pad-absorbLᴶ : (px sx a p₁ s₁ : List X) {u v : List X} (g : WTerm u v)
                 → padʷ px sx (idʷ {n = a} ⊗ʷ padʷ p₁ s₁ g) ≋ padʷ (px ++ (a ++ p₁)) (s₁ ++ sx) g
    pad-absorbLᴶ px sx a p₁ s₁ g =
      ≋-trans (≋-cong-pad px sx (≋-sym (pad-nestᴶ a p₁ s₁ g)))
              (≋-sym (pad-fuseᴶ px sx (a ++ p₁) s₁ g))

    pad-absorbRᴶ : (px sx a p₁ s₁ : List X) {u v : List X} (g : WTerm u v)
                 → padʷ px sx (padʷ p₁ s₁ g ⊗ʷ idʷ {n = a}) ≋ padʷ (px ++ p₁) (s₁ ++ (a ++ sx)) g
    pad-absorbRᴶ px sx a p₁ s₁ g =
      ≋-trans (≋-cong-pad px sx (≋-sym (pad-nestRᴶ p₁ s₁ a g)))
        (≋-trans (≋-sym (pad-fuseᴶ px sx p₁ (s₁ ++ a) g))
                 (padʷ-sufᴶ (px ++ p₁) (++-assoc s₁ a sx) g))

    -- the explicit-cast wrapper Diagram.shiftL-soundˢ consumes: canonical
    -- `++-assoc` endpoints, so no Hedberg reconciliation (instance-free).
    pad-nest : (p q suf : List X) {a b : List X} (g : WTerm a b)
             → padʷ (p ++ q) suf g
               ≈ʷ castʷᵈ (sym (++-assoc p q (a ++ suf)))
                    (castʷ (sym (++-assoc p q (b ++ suf))) (idʷ {n = p} ⊗ʷ padʷ q suf g))
    pad-nest p q suf g = symʷ (eqʷ (≋-sym (pad-nestᴶ p q suf g)))

    --------------------------------------------------------------------------------
    -- The explicit-cast wrappers whose caller supplies the transports; the caller
    -- pair is reconciled to the `≋`-record's canonical pair by Hedberg
    -- irrelevance (`≋→cast-formˢ`), so these carry the `⦃ DecEq X ⦄`.  `pad-nestR`
    -- feeds Diagram.shiftR-soundˢ, `nest3` feeds `swap-cleanˢ`, and the two
    -- `pad-absorb_ˢ` feed Sigma.slide-cleanˢ/-a.
    --------------------------------------------------------------------------------
    module _ ⦃ _ : DecEq X ⦄ where
      ≋→cast-formˢ : {t : WTerm n m} {t' : WTerm n' m'} → t ≋ t'
                   → (eD : n ≡ n') (eC : m ≡ m') → t' ≈ʷ castʷᵈ eD (castʷ eC t)
      ≋→cast-formˢ {t = t} (mk≋ d c eq) eD eC =
        transʷ (symʷ eq) (≡→≈ʷ (trans (cong (λ z → castʷᵈ z (castʷ c t)) (≡-irrL d eD))
                                      (cong (λ z → castʷᵈ eD (castʷ z t)) (≡-irrL c eC))))

      pad-nestR : (pre suf rt : List X) {a b : List X} (g : WTerm a b)
                  (dd : (pre ++ (a ++ suf)) ++ rt ≡ pre ++ (a ++ (suf ++ rt)))
                  (dc : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt)))
                → padʷ pre (suf ++ rt) g ≈ʷ castʷᵈ dd (castʷ dc (padʷ pre suf g ⊗ʷ idʷ {n = rt}))
      pad-nestR pre suf rt g dd dc = ≋→cast-formˢ (≋-sym (pad-nestRᴶ pre suf rt g)) dd dc

      nest3 : (p q r suf : List X) {a b : List X} (g : WTerm a b)
              (dd : p ++ (q ++ (r ++ (a ++ suf))) ≡ (p ++ (q ++ r)) ++ (a ++ suf))
              (dc : p ++ (q ++ (r ++ (b ++ suf))) ≡ (p ++ (q ++ r)) ++ (b ++ suf))
            → padʷ (p ++ (q ++ r)) suf g
              ≈ʷ castʷᵈ dd (castʷ dc (idʷ {n = p} ⊗ʷ (idʷ {n = q} ⊗ʷ padʷ r suf g)))
      nest3 p q r suf g dd dc = ≋→cast-formˢ (≋-sym (nest3ᴶ p q r suf g)) dd dc

      pad-absorbLˢ : (px sx a p₁ s₁ : List X) {u v : List X} (g : WTerm u v)
                     (eD : (px ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sx)) ≡ px ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sx))
                     (eC : (px ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sx)) ≡ px ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sx))
                   → padʷ px sx (idʷ {n = a} ⊗ʷ padʷ p₁ s₁ g)
                     ≈ʷ castʷᵈ eD (castʷ eC (padʷ (px ++ (a ++ p₁)) (s₁ ++ sx) g))
      pad-absorbLˢ px sx a p₁ s₁ g eD eC = ≋→cast-formˢ (≋-sym (pad-absorbLᴶ px sx a p₁ s₁ g)) eD eC

      pad-absorbRˢ : (px sx a p₁ s₁ : List X) {u v : List X} (g : WTerm u v)
                     (eD : (px ++ p₁) ++ (u ++ (s₁ ++ (a ++ sx))) ≡ px ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sx))
                     (eC : (px ++ p₁) ++ (v ++ (s₁ ++ (a ++ sx))) ≡ px ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sx))
                   → padʷ px sx (padʷ p₁ s₁ g ⊗ʷ idʷ {n = a})
                     ≈ʷ castʷᵈ eD (castʷ eC (padʷ (px ++ p₁) (s₁ ++ (a ++ sx)) g))
      pad-absorbRˢ px sx a p₁ s₁ g eD eC = ≋→cast-formˢ (≋-sym (pad-absorbRᴶ px sx a p₁ s₁ g)) eD eC
    -- The disjoint two-box interchange.  Two boxes `fy` (block `ay/by`, offset `P`) and `fx`
    -- (block `ax/bx`, offset `P ++ (·  ++ mid)`) sit in disjoint, non-crossing
    -- ranges of the flat wire word  P | y | mid | x | s , so the two firing
    -- orders agree.  The four `castʷ`/`castʷᵈ` reconcile the ONLY index gap —
    -- the `++`-associativity of that word — with NO merge/split conjugation.
    --
    -- Both orders reduce (via `nest3` + binary interchange) to the same canonical
    -- term `idʷ P ⊗ʷ (fy ⊗ʷ (idʷ mid ⊗ʷ (fx ⊗ʷ idʷ s)))`, transported by a single
    -- shared domain cast; the codomains already agree definitionally.
    swap-cleanˢ : ⦃ _ : DecEq X ⦄
                → ∀ (P mid s : List X) {ax bx ay by : List X}
                  (fx : Gen ax bx) (fy : Gen ay by)
                  {meq : (P ++ (ay ++ mid)) ++ (bx ++ s) ≡ P ++ (ay ++ (mid ++ (bx ++ s)))}
                  {E₂ : (P ++ (by ++ mid)) ++ (bx ++ s) ≡ P ++ (by ++ (mid ++ (bx ++ s)))}
                  {E₃ : P ++ (by ++ (mid ++ (ax ++ s))) ≡ (P ++ (by ++ mid)) ++ (ax ++ s)}
                  {E₄ : (P ++ (ay ++ mid)) ++ (ax ++ s) ≡ P ++ (ay ++ (mid ++ (ax ++ s)))}
                → padʷ P (mid ++ (bx ++ s)) (boxʷ fy)
                    ∘ʷ castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx))
                  ≈ʷ castʷ E₂ (padʷ (P ++ (by ++ mid)) s (boxʷ fx)
                       ∘ʷ castʷ E₃ (castʷᵈ (sym E₄)
                            (padʷ P (mid ++ (ax ++ s)) (boxʷ fy))))
    swap-cleanˢ P mid s {ax} {bx} {ay} {by} fx fy {meq} {E₂} {E₃} {E₄} =
      transʷ lhs-canon (symʷ rhs-canon)
      where
        Fx : WTerm (mid ++ (ax ++ s)) (mid ++ (bx ++ s))
        Fx = padʷ mid s (boxʷ fx)

        -- the shared canonical form (fy and Fx fired "simultaneously")
        CANON : WTerm (P ++ (ay ++ (mid ++ (ax ++ s)))) (P ++ (by ++ (mid ++ (bx ++ s))))
        CANON = idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ Fx)

        FY : WTerm (P ++ (ay ++ (mid ++ (bx ++ s)))) (P ++ (by ++ (mid ++ (bx ++ s))))
        FY = padʷ P (mid ++ (bx ++ s)) (boxʷ fy)

        FYi : WTerm (P ++ (ay ++ (mid ++ (ax ++ s)))) (P ++ (by ++ (mid ++ (ax ++ s))))
        FYi = padʷ P (mid ++ (ax ++ s)) (boxʷ fy)

        -- fy fired first-block, Fx second-block: the binary interchange
        fy-core : FY ∘ʷ (idʷ {n = P} ⊗ʷ (idʷ {n = ay} ⊗ʷ Fx)) ≈ʷ CANON
        fy-core = begin
          (idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ idʷ {n = mid ++ (bx ++ s)}))
            ∘ʷ (idʷ {n = P} ⊗ʷ (idʷ {n = ay} ⊗ʷ Fx))
            ≈⟨ inter ⟨
          (idʷ {n = P} ∘ʷ idʷ {n = P})
            ⊗ʷ ((boxʷ fy ⊗ʷ idʷ {n = mid ++ (bx ++ s)}) ∘ʷ (idʷ {n = ay} ⊗ʷ Fx))
            ≈⟨ ⊗-resp-≈ʷ idˡ (symʷ serialize₁₂) ⟩
          idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ Fx) ∎

        fy-core' : (idʷ {n = P} ⊗ʷ (idʷ {n = by} ⊗ʷ Fx)) ∘ʷ FYi ≈ʷ CANON
        fy-core' = begin
          (idʷ {n = P} ⊗ʷ (idʷ {n = by} ⊗ʷ Fx))
            ∘ʷ (idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ idʷ {n = mid ++ (ax ++ s)}))
            ≈⟨ inter ⟨
          (idʷ {n = P} ∘ʷ idʷ {n = P})
            ⊗ʷ ((idʷ {n = by} ⊗ʷ Fx) ∘ʷ (boxʷ fy ⊗ʷ idʷ {n = mid ++ (ax ++ s)}))
            ≈⟨ ⊗-resp-≈ʷ idˡ (symʷ serialize₂₁) ⟩
          idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ Fx) ∎

        -- LHS: reduce the (cast-mediated) fx-layer to the nested core, then fire.
        core-in : WTerm (P ++ (ay ++ (mid ++ (ax ++ s)))) (P ++ (ay ++ (mid ++ (bx ++ s))))
        core-in = idʷ {n = P} ⊗ʷ (idʷ {n = ay} ⊗ʷ Fx)

        reduce-fx : castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx)) ≈ʷ castʷᵈ (sym E₄) core-in
        reduce-fx = begin
          castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx))
            ≈⟨ castʷ-resp meq (nest3 P ay mid s (boxʷ fx) (sym E₄) (sym meq)) ⟩
          castʷ meq (castʷᵈ (sym E₄) (castʷ (sym meq) core-in))
            ≈⟨ ≡→≈ʷ (castʷ-castʷᵈ (sym E₄) meq (castʷ (sym meq) core-in)) ⟩
          castʷᵈ (sym E₄) (castʷ meq (castʷ (sym meq) core-in))
            ≈⟨ castʷᵈ-resp (sym E₄) (≡→≈ʷ (castʷ-symʳ meq core-in)) ⟩
          castʷᵈ (sym E₄) core-in ∎

        lhs-canon : padʷ P (mid ++ (bx ++ s)) (boxʷ fy) ∘ʷ castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx)) ≈ʷ castʷᵈ (sym E₄) CANON
        lhs-canon = begin
          FY ∘ʷ castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx))
            ≈⟨ ∘-resp-≈ reflʷ reduce-fx ⟩
          FY ∘ʷ castʷᵈ (sym E₄) core-in
            ≈⟨ ≡→≈ʷ (∘ʷ-castʷᵈ-r (sym E₄) FY core-in) ⟩
          castʷᵈ (sym E₄) (FY ∘ʷ core-in)
            ≈⟨ castʷᵈ-resp (sym E₄) fy-core ⟩
          castʷᵈ (sym E₄) CANON ∎

        -- RHS: peel the outer cast, reduce fx-out to the nested core, fire.
        core-out : WTerm (P ++ (by ++ (mid ++ (ax ++ s)))) (P ++ (by ++ (mid ++ (bx ++ s))))
        core-out = idʷ {n = P} ⊗ʷ (idʷ {n = by} ⊗ʷ Fx)

        T : WTerm ((P ++ (ay ++ mid)) ++ (ax ++ s)) ((P ++ (by ++ mid)) ++ (ax ++ s))
        T = castʷ E₃ (castʷᵈ (sym E₄) FYi)

        reduce-T : castʷ (sym E₃) T ≈ʷ castʷᵈ (sym E₄) FYi
        reduce-T = ≡→≈ʷ (castʷ-symˡ E₃ (castʷᵈ (sym E₄) FYi))

        inner2 : core-out ∘ʷ castʷ (sym E₃) T ≈ʷ castʷᵈ (sym E₄) CANON
        inner2 = begin
          core-out ∘ʷ castʷ (sym E₃) T
            ≈⟨ ∘-resp-≈ reflʷ reduce-T ⟩
          core-out ∘ʷ castʷᵈ (sym E₄) FYi
            ≈⟨ ≡→≈ʷ (∘ʷ-castʷᵈ-r (sym E₄) core-out FYi) ⟩
          castʷᵈ (sym E₄) (core-out ∘ʷ FYi)
            ≈⟨ castʷᵈ-resp (sym E₄) fy-core' ⟩
          castʷᵈ (sym E₄) CANON ∎

        inner : padʷ (P ++ (by ++ mid)) s (boxʷ fx) ∘ʷ T ≈ʷ castʷ (sym E₂) (castʷᵈ (sym E₄) CANON)
        inner = begin
          padʷ (P ++ (by ++ mid)) s (boxʷ fx) ∘ʷ T
            ≈⟨ ∘-resp-≈ (nest3 P by mid s (boxʷ fx) E₃ (sym E₂)) reflʷ ⟩
          castʷᵈ E₃ (castʷ (sym E₂) core-out) ∘ʷ T
            ≈⟨ ≡→≈ʷ (∘ʷ-castʷᵈ-l E₃ (castʷ (sym E₂) core-out) T) ⟩
          castʷ (sym E₂) core-out ∘ʷ castʷ (sym E₃) T
            ≈⟨ ≡→≈ʷ (∘ʷ-castʷ-l (sym E₂) core-out (castʷ (sym E₃) T)) ⟩
          castʷ (sym E₂) (core-out ∘ʷ castʷ (sym E₃) T)
            ≈⟨ castʷ-resp (sym E₂) inner2 ⟩
          castʷ (sym E₂) (castʷᵈ (sym E₄) CANON) ∎

        rhs-canon : castʷ E₂ (padʷ (P ++ (by ++ mid)) s (boxʷ fx) ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) (padʷ P (mid ++ (ax ++ s)) (boxʷ fy)))) ≈ʷ castʷᵈ (sym E₄) CANON
        rhs-canon = begin
          castʷ E₂ (padʷ (P ++ (by ++ mid)) s (boxʷ fx) ∘ʷ T)
            ≈⟨ castʷ-resp E₂ inner ⟩
          castʷ E₂ (castʷ (sym E₂) (castʷᵈ (sym E₄) CANON))
            ≈⟨ ≡→≈ʷ (castʷ-symʳ E₂ (castʷᵈ (sym E₄) CANON)) ⟩
          castʷᵈ (sym E₄) CANON ∎

  -- The plain free strict monoidal category: the theory with the empty engine.
  Strict : Category 0ℓ 0ℓ 0ℓ
  Strict = Theory.StrictR (λ _ _ → ⊥)
