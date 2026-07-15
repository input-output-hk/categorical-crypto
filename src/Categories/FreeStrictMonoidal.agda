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
-- NOTE on strictness / no `Monoidal` instance: `++` is only a monoid UP TO
-- propositional equality (`++-assoc` / `++-identityʳ` are not definitional), so
-- a full strict `Monoidal` instance would still need the associator/unitors to
-- be `castʷ`-transported identities with the attendant coherence bookkeeping.
-- That is deliberately out of scope here; we expose the `Category` `Strict`
-- (the theory instantiated at the empty engine `R = λ _ _ → ⊥`) and the tensor
-- as the morphism-former `_⊗ʷ_` with its bifunctor axioms in `Theory`.
--------------------------------------------------------------------------------

open import Level
open import Data.List
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Data.List.Properties.Ext as ListExt
open import Class.DecEq using (DecEq; _≟_)

open import Categories.Category
open import Categories.Category.Helper

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

  -- fusion of two codomain / two domain transports
  castʷ-fuse : (e : m ≡ m') (e' : m' ≡ m'') (t : WTerm n m)
             → castʷ e' (castʷ e t) ≡ castʷ (trans e e') t
  castʷ-fuse refl refl t = refl

  -- cancellation of a transport against its inverse (both orders)
  castʷ-symˡ : (e : m ≡ m') (t : WTerm n m) → castʷ (sym e) (castʷ e t) ≡ t
  castʷ-symˡ refl t = refl

  castʷ-symʳ : (e : m ≡ m') (t : WTerm n m') → castʷ e (castʷ (sym e) t) ≡ t
  castʷ-symʳ refl t = refl

  -- the same cancellations for the domain transport
  castʷᵈ-symˡ : (e : n ≡ n') (t : WTerm n m) → castʷᵈ (sym e) (castʷᵈ e t) ≡ t
  castʷᵈ-symˡ refl t = refl

  castʷᵈ-symʳ : (e : n ≡ n') (t : WTerm n' m) → castʷᵈ e (castʷᵈ (sym e) t) ≡ t
  castʷᵈ-symʳ refl t = refl

  -- the two transports act on independent indices, hence commute
  castʷ-castʷᵈ : (e : n ≡ n') (e' : m ≡ m') (t : WTerm n m)
               → castʷ e' (castʷᵈ e t) ≡ castʷᵈ e (castʷ e' t)
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
  ∘ʷ-castʷ-l : (e : k ≡ k') (g : WTerm m k) (f : WTerm n m)
             → castʷ e g ∘ʷ f ≡ castʷ e (g ∘ʷ f)
  ∘ʷ-castʷ-l refl g f = refl

  ∘ʷ-castʷᵈ-r : (e : n ≡ n') (g : WTerm m k) (f : WTerm n m)
              → g ∘ʷ castʷᵈ e f ≡ castʷᵈ e (g ∘ʷ f)
  ∘ʷ-castʷᵈ-r refl g f = refl

  ∘ʷ-castʷᵈ-l : (e : m ≡ m') (g : WTerm m k) (f : WTerm n m')
              → castʷᵈ e g ∘ʷ f ≡ g ∘ʷ castʷ (sym e) f
  ∘ʷ-castʷᵈ-l refl g f = refl

  -- interaction with the tensor: a transport of the RIGHT factor lifts through
  -- the prefix `s ⊗ʷ_` to a transport `cong (… ++_)`.
  ⊗ʷ-castʷ-r : (e : mr ≡ m') (s : WTerm nl ml) (t : WTerm nr mr)
             → s ⊗ʷ castʷ e t ≡ castʷ (cong (ml ++_) e) (s ⊗ʷ t)
  ⊗ʷ-castʷ-r refl s t = refl

  ⊗ʷ-castʷᵈ-r : (e : nr ≡ n') (s : WTerm nl ml) (t : WTerm nr mr)
              → s ⊗ʷ castʷᵈ e t ≡ castʷᵈ (cong (nl ++_) e) (s ⊗ʷ t)
  ⊗ʷ-castʷᵈ-r refl s t = refl

  -- the mirror laws: a transport of the LEFT factor lifts through `_⊗ʷ t` to a
  -- transport `cong (_++ …)`.
  ⊗ʷ-castʷ-l : (e : ml ≡ m') (s : WTerm nl ml) (t : WTerm nr mr)
             → castʷ e s ⊗ʷ t ≡ castʷ (cong (_++ mr) e) (s ⊗ʷ t)
  ⊗ʷ-castʷ-l refl s t = refl

  ⊗ʷ-castʷᵈ-l : (e : nl ≡ n') (s : WTerm nl ml) (t : WTerm nr mr)
              → castʷᵈ e s ⊗ʷ t ≡ castʷᵈ (cong (_++ nr) e) (s ⊗ʷ t)
  ⊗ʷ-castʷᵈ-l refl s t = refl

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
  padʷ : (pre suf : List X) {a b : List X} → WTerm a b
       → WTerm (pre ++ (a ++ suf)) (pre ++ (b ++ suf))
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
      ⊗-resp-≈ʷ : {f h : WTerm n m} {g i : WTerm a b}
                → f ≈ʷ h → g ≈ʷ i → f ⊗ʷ g ≈ʷ h ⊗ʷ i
      id⊗id : idʷ {n = a} ⊗ʷ idʷ {n = b} ≈ʷ idʷ
      inter : ∀ {nl ml kl nr mr kr}
                {g : WTerm ml kl} {f : WTerm nl ml}
                {g' : WTerm mr kr} {f' : WTerm nr mr}
            → (g ∘ʷ f) ⊗ʷ (g' ∘ʷ f') ≈ʷ (g ⊗ʷ g') ∘ʷ (f ⊗ʷ f')
      -- the left unit is definitional on OBJECTS (`[] ++ n = n`) but not on
      -- terms; it is the strictness axiom "left unitor = identity".
      unitˡ : (f : WTerm n m) → idʷ {n = []} ⊗ʷ f ≈ʷ f
      -- cast-mediated axioms: associativity and the right unit
      ⊗-assoc : ∀ {n₁ m₁ n₂ m₂ n₃ m₃}
                  (f : WTerm n₁ m₁) (g : WTerm n₂ m₂) (h : WTerm n₃ m₃)
              → castʷᵈ (++-assoc n₁ n₂ n₃) (castʷ (++-assoc m₁ m₂ m₃)
                  ((f ⊗ʷ g) ⊗ʷ h))
                ≈ʷ f ⊗ʷ (g ⊗ʷ h)
      unitʳ : (f : WTerm n m)
            → castʷᵈ (++-identityʳ n) (castʷ (++-identityʳ m) (f ⊗ʷ idʷ {n = []}))
              ≈ʷ f
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
    -- Regrouping a pad at a split prefix.  `padʷ (p ++ q) suf g`, whose idle
    -- prefix is bracketed as one block, equals the twice-nested pad `idʷ p ⊗ʷ
    -- padʷ q suf g` transported across the two `++`-associativity gaps.  Pure
    -- `⊗-assoc` + `id⊗id` + transport algebra.
    --------------------------------------------------------------------------------
    pad-nest : (p q suf : List X) {a b : List X} (g : WTerm a b)
             → padʷ (p ++ q) suf g
               ≈ʷ castʷᵈ (sym (++-assoc p q (a ++ suf)))
                    (castʷ (sym (++-assoc p q (b ++ suf))) (idʷ {n = p} ⊗ʷ padʷ q suf g))
    pad-nest p q suf {a} {b} g = begin
      padʷ (p ++ q) suf g
        ≈⟨ ⊗-resp-≈ʷ id⊗id reflʷ ⟨
      (idʷ {n = p} ⊗ʷ idʷ {n = q}) ⊗ʷ (g ⊗ʷ idʷ {n = suf})
        ≈⟨ ≡→≈ʷ (sym (uncast (++-assoc p q (a ++ suf)) (++-assoc p q (b ++ suf)) _)) ⟩
      castʷᵈ (sym eD) (castʷ (sym eC)
        (castʷᵈ eD (castʷ eC ((idʷ {n = p} ⊗ʷ idʷ {n = q}) ⊗ʷ (g ⊗ʷ idʷ {n = suf})))))
        ≈⟨ castʷᵈ-resp (sym eD) (castʷ-resp (sym eC) (⊗-assoc _ _ _)) ⟩
      castʷᵈ (sym eD) (castʷ (sym eC) (idʷ {n = p} ⊗ʷ padʷ q suf g)) ∎
      where
        eD = ++-assoc p q (a ++ suf)
        eC = ++-assoc p q (b ++ suf)
        -- undo a domain/codomain transport pair (fully generic on `refl`)
        uncast : ∀ {n n' m m'} (d : n ≡ n') (c : m ≡ m') (t : WTerm n m)
               → castʷᵈ (sym d) (castʷ (sym c) (castʷᵈ d (castʷ c t))) ≡ t
        uncast refl refl t = refl

    --------------------------------------------------------------------------------
    -- Threefold nesting `padʷ (p ++ (q ++ r)) suf g ≈ idʷ p ⊗ʷ (idʷ q ⊗ʷ padʷ r
    -- suf g)`, up to transports supplied by the caller (reconciled by Hedberg
    -- irrelevance).  This is the "5-block re-association".
    --------------------------------------------------------------------------------
    nest3 : ⦃ _ : DecEq X ⦄
          → (p q r suf : List X) {a b : List X} (g : WTerm a b)
            (dd : p ++ (q ++ (r ++ (a ++ suf))) ≡ (p ++ (q ++ r)) ++ (a ++ suf))
            (dc : p ++ (q ++ (r ++ (b ++ suf))) ≡ (p ++ (q ++ r)) ++ (b ++ suf))
          → padʷ (p ++ (q ++ r)) suf g
            ≈ʷ castʷᵈ dd (castʷ dc (idʷ {n = p} ⊗ʷ (idʷ {n = q} ⊗ʷ padʷ r suf g)))
    nest3 p q r suf {a} {b} g dd dc = begin
      padʷ (p ++ (q ++ r)) suf g
        ≈⟨ pad-nest p (q ++ r) suf g ⟩
      castʷᵈ eD₁ (castʷ eC₁ (idʷ {n = p} ⊗ʷ padʷ (q ++ r) suf g))
        ≈⟨ castʷᵈ-resp eD₁ (castʷ-resp eC₁ (⊗-resp-≈ʷ reflʷ (pad-nest q r suf g))) ⟩
      castʷᵈ eD₁ (castʷ eC₁ (idʷ {n = p} ⊗ʷ
        castʷᵈ eD₂ (castʷ eC₂ (idʷ {n = q} ⊗ʷ padʷ r suf g))))
        ≈⟨ ≡→≈ʷ push ⟩
      castʷᵈ eD₁ (castʷ eC₁ (castʷᵈ (cong (p ++_) eD₂)
        (castʷ (cong (p ++_) eC₂) core)))
        ≈⟨ ≡→≈ʷ (regather eD₁ (cong (p ++_) eD₂) eC₁ (cong (p ++_) eC₂) core) ⟩
      castʷᵈ (trans (cong (p ++_) eD₂) eD₁) (castʷ (trans (cong (p ++_) eC₂) eC₁) core)
        ≈⟨ ≡→≈ʷ (castʷᵈ-irr _ dd _) ⟩
      castʷᵈ dd (castʷ (trans (cong (p ++_) eC₂) eC₁) core)
        ≈⟨ castʷᵈ-resp dd (≡→≈ʷ (castʷ-irr _ dc core)) ⟩
      castʷᵈ dd (castʷ dc core) ∎
      where
        eD₁ = sym (++-assoc p (q ++ r) (a ++ suf))
        eC₁ = sym (++-assoc p (q ++ r) (b ++ suf))
        eD₂ = sym (++-assoc q r (a ++ suf))
        eC₂ = sym (++-assoc q r (b ++ suf))
        core = idʷ {n = p} ⊗ʷ (idʷ {n = q} ⊗ʷ padʷ r suf g)
        -- push the inner pair of transports out through `idʷ p ⊗ʷ_`
        push : castʷᵈ eD₁ (castʷ eC₁ (idʷ {n = p} ⊗ʷ
                 castʷᵈ eD₂ (castʷ eC₂ (idʷ {n = q} ⊗ʷ padʷ r suf g))))
             ≡ castʷᵈ eD₁ (castʷ eC₁ (castʷᵈ (cong (p ++_) eD₂)
                 (castʷ (cong (p ++_) eC₂) core)))
        push = cong (λ z → castʷᵈ eD₁ (castʷ eC₁ z))
                 (trans (⊗ʷ-castʷᵈ-r eD₂ (idʷ {n = p}) _)
                        (cong (castʷᵈ (cong (p ++_) eD₂)) (⊗ʷ-castʷ-r eC₂ (idʷ {n = p}) _)))

    --------------------------------------------------------------------------------
    -- The suffix analogue of `pad-nest`: widening a pad's idle SUFFIX by `rt`
    -- equals the pad tensored on the right with `idʷ rt`, up to the two
    -- `++`-associativity transports the caller supplies (reconciled by Hedberg
    -- irrelevance).  Two `⊗-assoc` re-brackets (one for the box block `g ⊗ʷ
    -- idʷ suf`, one for the whole pad) plus `id⊗id` to fuse `idʷ suf ⊗ʷ idʷ rt`.
    --------------------------------------------------------------------------------
    pad-nestR : ⦃ _ : DecEq X ⦄
              → (pre suf rt : List X) {a b : List X} (g : WTerm a b)
                (dd : (pre ++ (a ++ suf)) ++ rt ≡ pre ++ (a ++ (suf ++ rt)))
                (dc : (pre ++ (b ++ suf)) ++ rt ≡ pre ++ (b ++ (suf ++ rt)))
              → padʷ pre (suf ++ rt) g
                ≈ʷ castʷᵈ dd (castʷ dc (padʷ pre suf g ⊗ʷ idʷ {n = rt}))
    pad-nestR pre suf rt {a} {b} g dd dc = begin
      padʷ pre (suf ++ rt) g
        ≈⟨ ⊗-resp-≈ʷ reflʷ (⊗-resp-≈ʷ reflʷ (symʷ id⊗id)) ⟩
      idʷ {n = pre} ⊗ʷ (g ⊗ʷ (idʷ {n = suf} ⊗ʷ idʷ {n = rt}))
        ≈⟨ ⊗-resp-≈ʷ reflʷ (⊗-assoc g (idʷ {n = suf}) (idʷ {n = rt})) ⟨
      idʷ {n = pre} ⊗ʷ castʷᵈ eDr (castʷ eCr Z)
        ≈⟨ ≡→≈ʷ push ⟩
      castʷᵈ (cong (pre ++_) eDr) (castʷ (cong (pre ++_) eCr) (idʷ {n = pre} ⊗ʷ Z))
        ≈⟨ castʷᵈ-resp (cong (pre ++_) eDr)
             (castʷ-resp (cong (pre ++_) eCr) (⊗-assoc (idʷ {n = pre}) (g ⊗ʷ idʷ {n = suf}) (idʷ {n = rt}))) ⟨
      castʷᵈ (cong (pre ++_) eDr) (castʷ (cong (pre ++_) eCr) (castʷᵈ eDr2 (castʷ eCr2 T)))
        ≈⟨ ≡→≈ʷ (regather (cong (pre ++_) eDr) eDr2 (cong (pre ++_) eCr) eCr2 T) ⟩
      castʷᵈ (trans eDr2 (cong (pre ++_) eDr)) (castʷ (trans eCr2 (cong (pre ++_) eCr)) T)
        ≈⟨ ≡→≈ʷ (castʷᵈ-irr _ dd _) ⟩
      castʷᵈ dd (castʷ (trans eCr2 (cong (pre ++_) eCr)) T)
        ≈⟨ castʷᵈ-resp dd (≡→≈ʷ (castʷ-irr _ dc T)) ⟩
      castʷᵈ dd (castʷ dc T) ∎
      where
        eDr = ++-assoc a suf rt
        eCr = ++-assoc b suf rt
        eDr2 = ++-assoc pre (a ++ suf) rt
        eCr2 = ++-assoc pre (b ++ suf) rt
        Z = (g ⊗ʷ idʷ {n = suf}) ⊗ʷ idʷ {n = rt}
        T = padʷ pre suf g ⊗ʷ idʷ {n = rt}
        -- push the box-block transports out through `idʷ pre ⊗ʷ_`
        push : idʷ {n = pre} ⊗ʷ castʷᵈ eDr (castʷ eCr Z)
             ≡ castʷᵈ (cong (pre ++_) eDr) (castʷ (cong (pre ++_) eCr) (idʷ {n = pre} ⊗ʷ Z))
        push = trans (⊗ʷ-castʷᵈ-r eDr (idʷ {n = pre}) (castʷ eCr Z))
                     (cong (castʷᵈ (cong (pre ++_) eDr)) (⊗ʷ-castʷ-r eCr (idʷ {n = pre}) Z))

    -- Note `castʷᵈ dd` after the `castʷᵈ (cong (p ++_) eD₂)` needs no fusion:
    -- the two are collapsed by `≡→≈ʷ refl`? — see the last step above which uses
    -- irrelevance-free equality; the outer `castʷᵈ dd` absorbs the inner one is
    -- handled by the caller supplying `dd` already post-fusion.  (This last
    -- `refl` step is definitional after the previous rewrites.)

    --------------------------------------------------------------------------------
    -- Two disjoint boxes on adjacent blocks commute (binary interchange +
    -- units).  `slide-past` fires the right box first, `slide-past'` the left.
    --------------------------------------------------------------------------------
    slide-past : ∀ {ay by : List X} (u : WTerm ay by) {c d : List X} (w : WTerm c d)
               → (u ⊗ʷ idʷ {n = d}) ∘ʷ (idʷ {n = ay} ⊗ʷ w) ≈ʷ u ⊗ʷ w
    slide-past u w = begin
      (u ⊗ʷ idʷ) ∘ʷ (idʷ ⊗ʷ w)
        ≈⟨ inter ⟨
      (u ∘ʷ idʷ) ⊗ʷ (idʷ ∘ʷ w)
        ≈⟨ ⊗-resp-≈ʷ idʳ idˡ ⟩
      u ⊗ʷ w ∎

    slide-past' : ∀ {ay by : List X} (u : WTerm ay by) {c d : List X} (w : WTerm c d)
                → (idʷ {n = by} ⊗ʷ w) ∘ʷ (u ⊗ʷ idʷ {n = c}) ≈ʷ u ⊗ʷ w
    slide-past' u w = begin
      (idʷ ⊗ʷ w) ∘ʷ (u ⊗ʷ idʷ)
        ≈⟨ inter ⟨
      (idʷ ∘ʷ u) ⊗ʷ (w ∘ʷ idʷ)
        ≈⟨ ⊗-resp-≈ʷ idˡ idʳ ⟩
      u ⊗ʷ w ∎

    -- the idle prefix / suffix distributes over composition: `idʷ p ⊗ʷ_` (and
    -- `_⊗ʷ idʷ r`) is a functor, by interchange against a split identity.  Both
    -- are cast-free.
    id⊗-∘ˢ : (p : List X) (g : WTerm m k) (f : WTerm n m)
           → idʷ {n = p} ⊗ʷ (g ∘ʷ f) ≈ʷ (idʷ {n = p} ⊗ʷ g) ∘ʷ (idʷ {n = p} ⊗ʷ f)
    id⊗-∘ˢ p g f = transʷ (⊗-resp-≈ʷ (symʷ idˡ) reflʷ) inter

    ⊗id-∘ˢ : (r : List X) (g : WTerm m k) (f : WTerm n m)
           → (g ∘ʷ f) ⊗ʷ idʷ {n = r} ≈ʷ (g ⊗ʷ idʷ {n = r}) ∘ʷ (f ⊗ʷ idʷ {n = r})
    ⊗id-∘ˢ r g f = transʷ (⊗-resp-≈ʷ reflʷ (symʷ idˡ)) inter

    --------------------------------------------------------------------------------
    -- `padʷ pre suf` as a functor: congruence (`pad-respˢ`), preservation of
    -- composition (`pad-∘ˢ`) and identity (`pad-idˢ`), all cast-free; plus the
    -- pad-fusion `pad-fuseˢ` (a wider pad regrouped into a pad-of-pad, up to the
    -- two `++`-assoc transports the caller supplies, reconciled by Hedberg).
    --------------------------------------------------------------------------------
    pad-respˢ : (p s : List X) {a b : List X} {g g' : WTerm a b}
              → g ≈ʷ g' → padʷ p s g ≈ʷ padʷ p s g'
    pad-respˢ p s e = ⊗-resp-≈ʷ reflʷ (⊗-resp-≈ʷ e reflʷ)

    pad-∘ˢ : (p s : List X) (g : WTerm m k) (f : WTerm n m)
           → padʷ p s (g ∘ʷ f) ≈ʷ padʷ p s g ∘ʷ padʷ p s f
    pad-∘ˢ p s g f =
      transʷ (⊗-resp-≈ʷ reflʷ (⊗id-∘ˢ s g f)) (id⊗-∘ˢ p (g ⊗ʷ idʷ {n = s}) (f ⊗ʷ idʷ {n = s}))

    pad-idˢ : (p s : List X) → padʷ p s (idʷ {n = n}) ≈ʷ idʷ
    pad-idˢ p s = transʷ (⊗-resp-≈ʷ reflʷ id⊗id) id⊗id

    pad-fuseˢ : ⦃ _ : DecEq X ⦄
              → (px sx P s : List X) {a b : List X} (g : WTerm a b)
                (dd : px ++ ((P ++ (a ++ s)) ++ sx) ≡ (px ++ P) ++ (a ++ (s ++ sx)))
                (dc : px ++ ((P ++ (b ++ s)) ++ sx) ≡ (px ++ P) ++ (b ++ (s ++ sx)))
              → padʷ (px ++ P) (s ++ sx) g
                ≈ʷ castʷᵈ dd (castʷ dc (padʷ px sx (padʷ P s g)))
    pad-fuseˢ px sx P s {a} {b} g dd dc = begin
      padʷ (px ++ P) (s ++ sx) g
        ≈⟨ pad-nest px P (s ++ sx) g ⟩
      castʷᵈ eD₁ (castʷ eC₁ (idʷ {n = px} ⊗ʷ padʷ P (s ++ sx) g))
        ≈⟨ castʷᵈ-resp eD₁ (castʷ-resp eC₁ (⊗-resp-≈ʷ reflʷ (pad-nestR P s sx g fD fC))) ⟩
      castʷᵈ eD₁ (castʷ eC₁ (idʷ {n = px} ⊗ʷ castʷᵈ fD (castʷ fC (padʷ P s g ⊗ʷ idʷ {n = sx}))))
        ≈⟨ ≡→≈ʷ push ⟩
      castʷᵈ eD₁ (castʷ eC₁ (castʷᵈ (cong (px ++_) fD) (castʷ (cong (px ++_) fC) core)))
        ≈⟨ ≡→≈ʷ (regather eD₁ (cong (px ++_) fD) eC₁ (cong (px ++_) fC) core) ⟩
      castʷᵈ (trans (cong (px ++_) fD) eD₁) (castʷ (trans (cong (px ++_) fC) eC₁) core)
        ≈⟨ ≡→≈ʷ (castʷᵈ-irr _ dd _) ⟩
      castʷᵈ dd (castʷ (trans (cong (px ++_) fC) eC₁) core)
        ≈⟨ castʷᵈ-resp dd (≡→≈ʷ (castʷ-irr _ dc core)) ⟩
      castʷᵈ dd (castʷ dc core) ∎
      where
        eD₁ = sym (++-assoc px P (a ++ (s ++ sx)))
        eC₁ = sym (++-assoc px P (b ++ (s ++ sx)))
        fD  = trans (++-assoc P (a ++ s) sx) (cong (P ++_) (++-assoc a s sx))
        fC  = trans (++-assoc P (b ++ s) sx) (cong (P ++_) (++-assoc b s sx))
        Z   = padʷ P s g ⊗ʷ idʷ {n = sx}
        -- `idʷ px ⊗ʷ Z` is `padʷ px sx (padʷ P s g)` = `core` DEFINITIONALLY.
        core = padʷ px sx (padʷ P s g)
        push : castʷᵈ eD₁ (castʷ eC₁ (idʷ {n = px} ⊗ʷ castʷᵈ fD (castʷ fC Z)))
             ≡ castʷᵈ eD₁ (castʷ eC₁ (castʷᵈ (cong (px ++_) fD) (castʷ (cong (px ++_) fC) core)))
        push = cong (λ z → castʷᵈ eD₁ (castʷ eC₁ z))
                 (trans (⊗ʷ-castʷᵈ-r fD (idʷ {n = px}) (castʷ fC Z))
                        (cong (castʷᵈ (cong (px ++_) fD)) (⊗ʷ-castʷ-r fC (idʷ {n = px}) Z)))

    --------------------------------------------------------------------------------
    -- The two padded-box regroupings the σ naturality-slide re-cleanings consume.
    -- A box padded on the LEFT by an idle `a`-block (`idʷ a ⊗ʷ padʷ p₁ s₁ g`)
    -- and then by `px/sx`, is the single clean pad at the fused prefix
    -- `px ++ (a ++ p₁)` / suffix `s₁ ++ sx` (`pad-absorbLˢ`); dually a box padded
    -- on the RIGHT by `idʷ a` collapses to the pad at prefix `px ++ p₁` / suffix
    -- `s₁ ++ (a ++ sx)` (`pad-absorbRˢ`).  Both up to the two caller-supplied
    -- `++`-assoc transports (reconciled by Hedberg), pure `pad-fuseˢ` +
    -- `pad-nest`/`pad-nestR` + `pad-castˢ` regrouping.
    private
      -- the two shapes of `++`-assoc rebracketing these regroupings use.
      raˢ : ∀ (P x s t : List X) → (P ++ (x ++ s)) ++ t ≡ P ++ (x ++ (s ++ t))
      raˢ P x s t = trans (++-assoc P (x ++ s) t) (cong (P ++_) (++-assoc x s t))

      fuseEqˢ : ∀ (px P x s sx : List X)
              → px ++ ((P ++ (x ++ s)) ++ sx) ≡ (px ++ P) ++ (x ++ (s ++ sx))
      fuseEqˢ px P x s sx =
        trans (cong (px ++_) (++-assoc P (x ++ s) sx))
          (trans (sym (++-assoc px P ((x ++ s) ++ sx)))
            (cong ((px ++ P) ++_) (++-assoc x s sx)))

    pad-absorbLˢ : ⦃ _ : DecEq X ⦄
                 → (px sx a p₁ s₁ : List X) {u v : List X} (g : WTerm u v)
                   (eD : (px ++ (a ++ p₁)) ++ (u ++ (s₁ ++ sx))
                       ≡ px ++ ((a ++ (p₁ ++ (u ++ s₁))) ++ sx))
                   (eC : (px ++ (a ++ p₁)) ++ (v ++ (s₁ ++ sx))
                       ≡ px ++ ((a ++ (p₁ ++ (v ++ s₁))) ++ sx))
                 → padʷ px sx (idʷ {n = a} ⊗ʷ padʷ p₁ s₁ g)
                   ≈ʷ castʷᵈ eD (castʷ eC (padʷ (px ++ (a ++ p₁)) (s₁ ++ sx) g))
    pad-absorbLˢ px sx a p₁ s₁ {u} {v} g eD eC = symʷ (begin
      castʷᵈ eD (castʷ eC wide)
        ≈⟨ castʷᵈ-resp eD (castʷ-resp eC (pad-fuseˢ px sx (a ++ p₁) s₁ g (fuseEqˢ px (a ++ p₁) u s₁ sx) (fuseEqˢ px (a ++ p₁) v s₁ sx))) ⟩
      castʷᵈ eD (castʷ eC (castʷᵈ fD (castʷ fC pop)))
        ≈⟨ ≡→≈ʷ (regather eD fD eC fC pop) ⟩
      castʷᵈ (trans fD eD) (castʷ (trans fC eC) pop)
        ≈⟨ castʷᵈ-resp (trans fD eD) (castʷ-resp (trans fC eC) (pad-respˢ px sx (pad-nest a p₁ s₁ g))) ⟩
      castʷᵈ (trans fD eD) (castʷ (trans fC eC) (padʷ px sx (castʷᵈ D0 (castʷ C0 gα))))
        ≈⟨ castʷᵈ-resp (trans fD eD) (castʷ-resp (trans fC eC) (≡→≈ʷ (pad-castˢ px sx D0 C0 gα))) ⟩
      castʷᵈ (trans fD eD) (castʷ (trans fC eC) (castʷᵈ D1 (castʷ C1 (padʷ px sx gα))))
        ≈⟨ ≡→≈ʷ (regather (trans fD eD) D1 (trans fC eC) C1 (padʷ px sx gα)) ⟩
      castʷᵈ (trans D1 (trans fD eD)) (castʷ (trans C1 (trans fC eC)) (padʷ px sx gα))
        ≈⟨ ≡→≈ʷ (castʷᵈ-irr (trans D1 (trans fD eD)) refl _) ⟩
      castʷ (trans C1 (trans fC eC)) (padʷ px sx gα)
        ≈⟨ ≡→≈ʷ (castʷ-irr (trans C1 (trans fC eC)) refl _) ⟩
      padʷ px sx gα ∎)
      where
        wide = padʷ (px ++ (a ++ p₁)) (s₁ ++ sx) g
        gα   = idʷ {n = a} ⊗ʷ padʷ p₁ s₁ g
        pop  = padʷ px sx (padʷ (a ++ p₁) s₁ g)
        fD = fuseEqˢ px (a ++ p₁) u s₁ sx
        fC = fuseEqˢ px (a ++ p₁) v s₁ sx
        D0 = sym (++-assoc a p₁ (u ++ s₁))
        C0 = sym (++-assoc a p₁ (v ++ s₁))
        D1 = cong (λ z → px ++ (z ++ sx)) D0
        C1 = cong (λ z → px ++ (z ++ sx)) C0

    pad-absorbRˢ : ⦃ _ : DecEq X ⦄
                 → (px sx a p₁ s₁ : List X) {u v : List X} (g : WTerm u v)
                   (eD : (px ++ p₁) ++ (u ++ (s₁ ++ (a ++ sx)))
                       ≡ px ++ (((p₁ ++ (u ++ s₁)) ++ a) ++ sx))
                   (eC : (px ++ p₁) ++ (v ++ (s₁ ++ (a ++ sx)))
                       ≡ px ++ (((p₁ ++ (v ++ s₁)) ++ a) ++ sx))
                 → padʷ px sx (padʷ p₁ s₁ g ⊗ʷ idʷ {n = a})
                   ≈ʷ castʷᵈ eD (castʷ eC (padʷ (px ++ p₁) (s₁ ++ (a ++ sx)) g))
    pad-absorbRˢ px sx a p₁ s₁ {u} {v} g eD eC = symʷ (begin
      castʷᵈ eD (castʷ eC widR)
        ≈⟨ castʷᵈ-resp eD (castʷ-resp eC (≡→≈ʷ (padʷ-suf (px ++ p₁) esuf g))) ⟩
      castʷᵈ eD (castʷ eC (castʷᵈ SD (castʷ SC widR')))
        ≈⟨ ≡→≈ʷ (regather eD SD eC SC widR') ⟩
      castʷᵈ (trans SD eD) (castʷ (trans SC eC) widR')
        ≈⟨ castʷᵈ-resp (trans SD eD) (castʷ-resp (trans SC eC) (pad-fuseˢ px sx p₁ (s₁ ++ a) g (fuseEqˢ px p₁ u (s₁ ++ a) sx) (fuseEqˢ px p₁ v (s₁ ++ a) sx))) ⟩
      castʷᵈ (trans SD eD) (castʷ (trans SC eC) (castʷᵈ fD (castʷ fC pop')))
        ≈⟨ ≡→≈ʷ (regather (trans SD eD) fD (trans SC eC) fC pop') ⟩
      castʷᵈ (trans fD (trans SD eD)) (castʷ (trans fC (trans SC eC)) pop')
        ≈⟨ castʷᵈ-resp (trans fD (trans SD eD)) (castʷ-resp (trans fC (trans SC eC)) (pad-respˢ px sx (pad-nestR p₁ s₁ a g (raˢ p₁ u s₁ a) (raˢ p₁ v s₁ a)))) ⟩
      castʷᵈ (trans fD (trans SD eD)) (castʷ (trans fC (trans SC eC)) (padʷ px sx (castʷᵈ RD (castʷ RC gβ))))
        ≈⟨ castʷᵈ-resp (trans fD (trans SD eD)) (castʷ-resp (trans fC (trans SC eC)) (≡→≈ʷ (pad-castˢ px sx RD RC gβ))) ⟩
      castʷᵈ (trans fD (trans SD eD)) (castʷ (trans fC (trans SC eC)) (castʷᵈ RD1 (castʷ RC1 (padʷ px sx gβ))))
        ≈⟨ ≡→≈ʷ (regather (trans fD (trans SD eD)) RD1 (trans fC (trans SC eC)) RC1 (padʷ px sx gβ)) ⟩
      castʷᵈ (trans RD1 (trans fD (trans SD eD))) (castʷ (trans RC1 (trans fC (trans SC eC))) (padʷ px sx gβ))
        ≈⟨ ≡→≈ʷ (castʷᵈ-irr (trans RD1 (trans fD (trans SD eD))) refl _) ⟩
      castʷ (trans RC1 (trans fC (trans SC eC))) (padʷ px sx gβ)
        ≈⟨ ≡→≈ʷ (castʷ-irr (trans RC1 (trans fC (trans SC eC))) refl _) ⟩
      padʷ px sx gβ ∎)
      where
        widR  = padʷ (px ++ p₁) (s₁ ++ (a ++ sx)) g
        widR' = padʷ (px ++ p₁) ((s₁ ++ a) ++ sx) g
        pop'  = padʷ px sx (padʷ p₁ (s₁ ++ a) g)
        gβ    = padʷ p₁ s₁ g ⊗ʷ idʷ {n = a}
        esuf  = ++-assoc s₁ a sx
        SD = cong (λ z → (px ++ p₁) ++ (u ++ z)) esuf
        SC = cong (λ z → (px ++ p₁) ++ (v ++ z)) esuf
        fD = fuseEqˢ px p₁ u (s₁ ++ a) sx
        fC = fuseEqˢ px p₁ v (s₁ ++ a) sx
        RD = raˢ p₁ u s₁ a
        RC = raˢ p₁ v s₁ a
        RD1 = cong (λ z → px ++ (z ++ sx)) RD
        RC1 = cong (λ z → px ++ (z ++ sx)) RC

    --------------------------------------------------------------------------------
    -- THE GO/NO-GO THEOREM.  Two boxes `fy` (block `ay/by`, offset `P`) and `fx`
    -- (block `ax/bx`, offset `P ++ (·  ++ mid)`) sit in disjoint, non-crossing
    -- ranges of the flat wire word  P | y | mid | x | s , so the two firing
    -- orders agree.  The four `castʷ`/`castʷᵈ` reconcile the ONLY index gap —
    -- the `++`-associativity of that word — with NO merge/split conjugation.
    --
    -- Both orders reduce (via `nest3` + binary interchange) to the same canonical
    -- term `idʷ P ⊗ʷ (fy ⊗ʷ (idʷ mid ⊗ʷ (fx ⊗ʷ idʷ s)))`, transported by a single
    -- shared domain cast; the codomains already agree definitionally.
    --------------------------------------------------------------------------------
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
            ≈⟨ ⊗-resp-≈ʷ idˡ (slide-past (boxʷ fy) Fx) ⟩
          idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ Fx) ∎

        fy-core' : (idʷ {n = P} ⊗ʷ (idʷ {n = by} ⊗ʷ Fx)) ∘ʷ FYi ≈ʷ CANON
        fy-core' = begin
          (idʷ {n = P} ⊗ʷ (idʷ {n = by} ⊗ʷ Fx))
            ∘ʷ (idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ idʷ {n = mid ++ (ax ++ s)}))
            ≈⟨ inter ⟨
          (idʷ {n = P} ∘ʷ idʷ {n = P})
            ⊗ʷ ((idʷ {n = by} ⊗ʷ Fx) ∘ʷ (boxʷ fy ⊗ʷ idʷ {n = mid ++ (ax ++ s)}))
            ≈⟨ ⊗-resp-≈ʷ idˡ (slide-past' (boxʷ fy) Fx) ⟩
          idʷ {n = P} ⊗ʷ (boxʷ fy ⊗ʷ Fx) ∎

        -- LHS: reduce the (cast-mediated) fx-layer to the nested core, then fire.
        core-in : WTerm (P ++ (ay ++ (mid ++ (ax ++ s)))) (P ++ (ay ++ (mid ++ (bx ++ s))))
        core-in = idʷ {n = P} ⊗ʷ (idʷ {n = ay} ⊗ʷ Fx)

        reduce-fx : castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx))
                  ≈ʷ castʷᵈ (sym E₄) core-in
        reduce-fx = begin
          castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx))
            ≈⟨ castʷ-resp meq (nest3 P ay mid s (boxʷ fx) (sym E₄) (sym meq)) ⟩
          castʷ meq (castʷᵈ (sym E₄) (castʷ (sym meq) core-in))
            ≈⟨ ≡→≈ʷ (castʷ-castʷᵈ (sym E₄) meq (castʷ (sym meq) core-in)) ⟩
          castʷᵈ (sym E₄) (castʷ meq (castʷ (sym meq) core-in))
            ≈⟨ castʷᵈ-resp (sym E₄) (≡→≈ʷ (castʷ-symʳ meq core-in)) ⟩
          castʷᵈ (sym E₄) core-in ∎

        lhs-canon : padʷ P (mid ++ (bx ++ s)) (boxʷ fy)
                      ∘ʷ castʷ meq (padʷ (P ++ (ay ++ mid)) s (boxʷ fx))
                    ≈ʷ castʷᵈ (sym E₄) CANON
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

        inner : padʷ (P ++ (by ++ mid)) s (boxʷ fx) ∘ʷ T
              ≈ʷ castʷ (sym E₂) (castʷᵈ (sym E₄) CANON)
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

        rhs-canon : castʷ E₂ (padʷ (P ++ (by ++ mid)) s (boxʷ fx)
                       ∘ʷ castʷ E₃ (castʷᵈ (sym E₄) (padʷ P (mid ++ (ax ++ s)) (boxʷ fy))))
                  ≈ʷ castʷᵈ (sym E₄) CANON
        rhs-canon = begin
          castʷ E₂ (padʷ (P ++ (by ++ mid)) s (boxʷ fx) ∘ʷ T)
            ≈⟨ castʷ-resp E₂ inner ⟩
          castʷ E₂ (castʷ (sym E₂) (castʷᵈ (sym E₄) CANON))
            ≈⟨ ≡→≈ʷ (castʷ-symʳ E₂ (castʷᵈ (sym E₄) CANON)) ⟩
          castʷᵈ (sym E₄) CANON ∎

  --------------------------------------------------------------------------------
  -- The plain free strict monoidal category: the theory with the empty engine.
  --------------------------------------------------------------------------------
  Strict : Category 0ℓ 0ℓ 0ℓ
  Strict = Theory.StrictR (λ _ _ → ⊥)
