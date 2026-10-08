{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Presented free strict symmetric monoidal category on `List X`, with `⊗ = ++`.
--
-- Associativity and right units of `++` require equality casts, not
-- coherence isomorphisms.  Decidable equality supplies UIP for their proofs.
-- Cons/singleton associators and `map-++` reduce at the decoder's frames,
-- so those casts vanish definitionally.  No cast-related axiom is needed.
--------------------------------------------------------------------------------

module Categories.FreeStrictSMC where

open import Axiom.UniquenessOfIdentityProofs
open import Data.List
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++⁺ʳ; ++⁺ˡ; ↭-sym-involutive)
open import Data.Product using (Σ-syntax; _,_)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Categories.Category using (Category)
open import Categories.Category.Helper

module Build
  (X : Set) (_≟X_ : DecidableEquality X)
  (mor : List X → List X → Set)
  where
  private
    variable
      A : Set
      xs xs' xs'' ys ys' ys'' zs ws us vs ps qs R : List A
      as as' as'' bs bs' bs'' cs cs' ds es fs us' vs' : List A

  uipL : UIP (List X)
  uipL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  ------------------------------------------------------------------------
  -- Presentation
  ------------------------------------------------------------------------

  infixr 9 _∘ˢ_
  infixr 10 _⊗ˢ_

  -- Some constructor telescopes stay explicit to preserve positional argument order.
  data HomS : List X → List X → Set where
    idˢ  : HomS xs xs
    _∘ˢ_ : ∀ {xs ys zs} → HomS ys zs → HomS xs ys → HomS xs zs
    _⊗ˢ_ : HomS xs ys → HomS us vs → HomS (xs ++ us) (ys ++ vs)
    genˢ : mor as bs → HomS as bs
    σˢ   : ∀ xs ys → HomS (xs ++ ys) (ys ++ xs)

  castˢ : xs ≡ xs' → ys ≡ ys' → HomS xs ys → HomS xs' ys'
  castˢ = subst₂ HomS

  infix 4 _≈ˢ_

  data _≈ˢ_ : ∀ {xs ys} → HomS xs ys → HomS xs ys → Set where
    ≈-refl  : {f : HomS xs ys} → f ≈ˢ f
    ≈-sym   : {f g : HomS xs ys} → f ≈ˢ g → g ≈ˢ f
    ≈-trans : {f g h : HomS xs ys} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
    ∘-resp  : ∀ {xs ys zs} {g g' : HomS ys zs} {f f' : HomS xs ys}
            → g ≈ˢ g' → f ≈ˢ f' → g ∘ˢ f ≈ˢ g' ∘ˢ f'
    ⊗-resp  : {f f' : HomS xs ys} {g g' : HomS us vs}
            → f ≈ˢ f' → g ≈ˢ g' → f ⊗ˢ g ≈ˢ f' ⊗ˢ g'
    idˡ    : {f : HomS xs ys} → idˢ ∘ˢ f ≈ˢ f
    idʳ    : {f : HomS xs ys} → f ∘ˢ idˢ ≈ˢ f
    assocˢ : ∀ {ws xs ys zs} {h : HomS ys zs} {g : HomS xs ys} {f : HomS ws xs}
           → (h ∘ˢ g) ∘ˢ f ≈ˢ h ∘ˢ (g ∘ˢ f)
    ⊗-id   : idˢ {xs} ⊗ˢ idˢ {us} ≈ˢ idˢ {xs ++ us}
    interchangeˢ
      : ∀ {xs ys zs us vs ws}
          {a : HomS ys zs} {b : HomS vs ws} {c : HomS xs ys} {d : HomS us vs}
      → (a ⊗ˢ b) ∘ˢ (c ⊗ˢ d) ≈ˢ (a ∘ˢ c) ⊗ˢ (b ∘ˢ d)
    ⊗-assocˢ
      : (f : HomS xs ys) (g : HomS us vs) (h : HomS ps qs)
      → castˢ (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h)
        ≈ˢ f ⊗ˢ (g ⊗ˢ h)
    ⊗-unitʳˢ
      : (f : HomS xs ys)
      → castˢ (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]}) ≈ˢ f
    σ-natˢ : {f : HomS xs ys} {g : HomS us vs}
           → σˢ ys vs ∘ˢ (f ⊗ˢ g) ≈ˢ (g ⊗ˢ f) ∘ˢ σˢ xs us
    σ-σˢ   : ∀ {xs ys} → σˢ ys xs ∘ˢ σˢ xs ys ≈ˢ idˢ
    σ-hexˢ : ∀ xs ys zs
           → σˢ (xs ++ ys) zs
             ≈ˢ castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                  ((σˢ xs zs ⊗ˢ idˢ {ys})
                    ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                         (idˢ {xs} ⊗ˢ σˢ ys zs))
    -- The unit-braiding axiom yields the left unit laws without a cast,
    -- since `[] ++ xs` reduces.
    σ-unitˢ : ∀ xs
            → σˢ [] xs ≈ˢ castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})

  SCat : Category 0ℓ 0ℓ 0ℓ
  SCat = categoryHelper record
    { Obj       = List X
    ; _⇒_       = HomS
    ; _≈_       = _≈ˢ_
    ; id        = idˢ
    ; _∘_       = _∘ˢ_
    ; assoc     = assocˢ
    ; identityˡ = idˡ
    ; identityʳ = idʳ
    ; equiv     = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }
    ; ∘-resp-≈  = ∘-resp
    }

  ------------------------------------------------------------------------
  -- Cast calculus
  ------------------------------------------------------------------------

  ≡⇒≈ˢ : {f g : HomS xs ys} → f ≡ g → f ≈ˢ g
  ≡⇒≈ˢ refl = ≈-refl

  cast-resp
    : (p : xs ≡ xs') (q : ys ≡ ys') {f g : HomS xs ys}
    → f ≈ˢ g → castˢ p q f ≈ˢ castˢ p q g
  cast-resp refl refl f≈g = f≈g

  cast-fuse
    : (p : xs ≡ xs') (p' : xs' ≡ xs'') (q : ys ≡ ys') (q' : ys' ≡ ys'')
      (f : HomS xs ys)
    → castˢ p' q' (castˢ p q f) ≡ castˢ (trans p p') (trans q q') f
  cast-fuse refl refl refl refl f = refl

  cast-irrel
    : (p p' : xs ≡ xs') (q q' : ys ≡ ys') (f : HomS xs ys)
    → castˢ p q f ≡ castˢ p' q' f
  cast-irrel p p' q q' f rewrite uipL p p' | uipL q q' = refl

  cast-id : (p q : xs ≡ xs') → castˢ p q (idˢ {xs}) ≈ˢ idˢ {xs'}
  cast-id refl q rewrite uipL q refl = ≈-refl

  ∘-cast-split
    : (P : as ≡ as') (M : bs ≡ bs') (Q : cs ≡ cs')
      (g : HomS bs cs) (f : HomS as bs)
    → castˢ P Q (g ∘ˢ f) ≈ˢ castˢ M Q g ∘ˢ castˢ P M f
  ∘-cast-split refl refl refl g f = ≈-refl

  cast-flip
    : (p : xs ≡ xs') (q : ys ≡ ys') {f : HomS xs ys} {g : HomS xs' ys'}
    → castˢ p q f ≈ˢ g → f ≈ˢ castˢ (sym p) (sym q) g
  cast-flip refl refl e = e

  ------------------------------------------------------------------------
  -- Heterogeneous strict equality
  ------------------------------------------------------------------------

  -- `_≈̂_` packages endpoint equalities so `++`/`map` bookkeeping is paid
  -- once inside congruence and transitivity, not at every decoder step.
  -- `List X` has UIP (`uipL`), so the endpoint proofs introduce no coherence.

  infix 4 _≈̂_
  _≈̂_ : HomS as bs → HomS as' bs' → Set
  _≈̂_ {as} {bs} {as'} {bs'} f g =
    Σ[ p ∈ as ≡ as' ] Σ[ q ∈ bs ≡ bs' ] (castˢ p q f ≈ˢ g)

  ≈ˢ⇒≈̂ : {f g : HomS as bs} → f ≈ˢ g → f ≈̂ g
  ≈ˢ⇒≈̂ e = refl , refl , e

  ≈̂-refl : {f : HomS as bs} → f ≈̂ f
  ≈̂-refl = refl , refl , ≈-refl

  cast-≈̂ : {p : as ≡ as'} {q : bs ≡ bs'} {f : HomS as bs}
         → castˢ p q f ≈̂ f
  cast-≈̂ {p = p} {q} {f} =
    sym p , sym q ,
    ≈-trans (≡⇒≈ˢ (cast-fuse p (sym p) q (sym q) f))
            (≡⇒≈ˢ (cast-irrel (trans p (sym p)) refl (trans q (sym q)) refl f))

  ≈̂-sym : {f : HomS as bs} {g : HomS as' bs'}
        → f ≈̂ g → g ≈̂ f
  ≈̂-sym (p , q , e) = sym p , sym q , ≈-sym (cast-flip p q e)

  ≈̂-trans : {f : HomS as bs} {g : HomS as' bs'} {h : HomS as'' bs''}
          → f ≈̂ g → g ≈̂ h → f ≈̂ h
  ≈̂-trans {f = f} (p₁ , q₁ , e₁) (p₂ , q₂ , e₂) =
    trans p₁ p₂ , trans q₁ q₂ ,
    ≈-trans (≡⇒≈ˢ (sym (cast-fuse p₁ p₂ q₁ q₂ f)))
            (≈-trans (cast-resp p₂ q₂ e₁) e₂)

  ∘-resp-≈̂ : {g : HomS bs cs} {g' : HomS bs' cs'}
              {f : HomS as bs} {f' : HomS as' bs'}
           → g ≈̂ g' → f ≈̂ f' → (g ∘ˢ f) ≈̂ (g' ∘ˢ f')
  ∘-resp-≈̂ {g = g} {f = f} (gd , gc , eg) (fd , fc , ef) =
    fd , gc ,
    ≈-trans (∘-cast-split fd gd gc g f)
            (∘-resp eg (≈-trans (≡⇒≈ˢ (cast-irrel fd fd gd fc f)) ef))

  cast-⊗-both
    : (p : as ≡ as') (q : bs ≡ bs') (r : us ≡ us') (s : vs ≡ vs')
      (f : HomS as bs) (g : HomS us vs)
    → castˢ (cong₂ _++_ p r) (cong₂ _++_ q s) (f ⊗ˢ g)
      ≡ castˢ p q f ⊗ˢ castˢ r s g
  cast-⊗-both refl refl refl refl f g = refl

  -- Projecting an `≈̂` chain to homogeneous endpoints can leave factor
  -- metas free; explicit `cast-⊗-both` arguments pin them.
  ⊗-resp-≈̂ : {f : HomS as bs} {f' : HomS as' bs'}
              {g : HomS us vs} {g' : HomS us' vs'}
           → f ≈̂ f' → g ≈̂ g' → (f ⊗ˢ g) ≈̂ (f' ⊗ˢ g')
  ⊗-resp-≈̂ {f = f} {g = g} (fp , fq , ef) (gp , gq , eg) =
    cong₂ _++_ fp gp , cong₂ _++_ fq gq ,
    ≈-trans (≡⇒≈ˢ (cast-⊗-both fp fq gp gq f g)) (⊗-resp ef eg)

  ≈̂⇒≈ˢ : {f g : HomS as bs} → f ≈̂ g → f ≈ˢ g
  ≈̂⇒≈ˢ {f = f} (p , q , e) =
    ≈-trans (≈-sym (≡⇒≈ˢ (cast-irrel p refl q refl f))) e

  idˢ-≈̂ : (p : as ≡ bs) → idˢ {as} ≈̂ idˢ {bs}
  idˢ-≈̂ p = p , p , cast-id p p

  σ-≈̂ : (p : as ≡ as') (q : bs ≡ bs')
      → σˢ as bs ≈̂ σˢ as' bs'
  σ-≈̂ refl refl = ≈̂-refl

  ≈̂⇒castˢ
    : {f : HomS as bs} {g : HomS as' bs'}
    → f ≈̂ g → (P : as ≡ as') (Q : bs ≡ bs') → castˢ P Q f ≈ˢ g
  ≈̂⇒castˢ {f = f} (p , q , e) P Q = ≈-trans (≡⇒≈ˢ (cast-irrel P p Q q f)) e

  castˢ⇒≈̂
    : (p : as ≡ as') (q : bs ≡ bs') {f : HomS as bs} {g : HomS as' bs'}
    → castˢ p q f ≈ˢ g → f ≈̂ g
  castˢ⇒≈̂ p q e = p , q , e

  ∘-cast-resp
    : (P : as ≡ as') (M : bs ≡ bs') (Q : cs ≡ cs')
        {g : HomS bs cs} {g' : HomS bs' cs'} {f : HomS as bs} {f' : HomS as' bs'}
    → castˢ M Q g ≈ˢ g' → castˢ P M f ≈ˢ f'
    → castˢ P Q (g ∘ˢ f) ≈ˢ g' ∘ˢ f'
  ∘-cast-resp P M Q eg ef = ≈-trans (∘-cast-split P M Q _ _) (∘-resp eg ef)

  -- The two middle morphisms have independent boundaries, allowing
  -- heterogeneous re-spellings on both sides of the sandwich.
  viâ : {u v : HomS as bs} {u' : HomS cs ds} {v' : HomS es fs}
      → u ≈̂ u' → u' ≈̂ v' → v ≈̂ v' → u ≈ˢ v
  viâ l e r = ≈̂⇒≈ˢ (≈̂-trans l (≈̂-trans e (≈̂-sym r)))

  viaˢ : {u v : HomS as bs} {u' v' : HomS as' bs'}
       → u ≈̂ u' → u' ≈ˢ v' → v ≈̂ v' → u ≈ˢ v
  viaˢ l e r = viâ l (≈ˢ⇒≈̂ e) r

  ------------------------------------------------------------------------
  -- Unit laws
  ------------------------------------------------------------------------

  σ-unitʳˢ : ∀ xs → σˢ xs [] ≈ˢ castˢ (sym (++-identityʳ xs)) refl (idˢ {xs})
  σ-unitʳˢ xs =
    ≈-trans (≈-sym idˡ)
    (≈-trans (∘-resp (≈-sym c⁻¹∘c) ≈-refl)
    (≈-trans assocˢ
    (≈-trans (∘-resp ≈-refl (∘-resp (≈-sym (σ-unitˢ xs)) ≈-refl))
    (≈-trans (∘-resp ≈-refl σ-σˢ)
      idʳ))))
    where
      I = ++-identityʳ xs
      c⁻¹∘c : castˢ (sym I) refl (idˢ {xs}) ∘ˢ castˢ refl (sym I) (idˢ {xs})
              ≈ˢ idˢ {xs}
      c⁻¹∘c = ≈-trans (≈-sym (∘-cast-split refl (sym I) refl idˢ idˢ)) idˡ

  ⊗-unitˡˢ : (f : HomS xs ys) → idˢ {[]} ⊗ˢ f ≈ˢ f
  ⊗-unitˡˢ {xs} {ys} f =
    ≈-trans (≈-sym idʳ)
    (≈-trans (∘-resp ≈-refl (≈-sym σ-σˢ))
    (≈-trans (≈-sym assocˢ)
    (≈-trans (∘-resp (≈-sym σ-natˢ) ≈-refl)
    (≈-trans (∘-resp (∘-resp (σ-unitʳˢ ys)
                             (cast-flip Ix Iy (⊗-unitʳˢ f)))
                     (σ-unitˢ xs))
    (≈-trans (∘-resp (≈-trans (≈-sym (∘-cast-split (sym Ix) (sym Iy) refl idˢ f))
                              (cast-resp (sym Ix) refl idˡ))
                     ≈-refl)
    (≈-trans (≈-sym (∘-cast-split refl (sym Ix) refl f idˢ))
      idʳ))))))
    where
      Ix = ++-identityʳ xs
      Iy = ++-identityʳ ys

  box-suffix-ˢ
    : (b : HomS as bs) (rest R : List X)
    → castˢ (++-assoc as rest R) (++-assoc bs rest R)
        ((b ⊗ˢ idˢ {rest}) ⊗ˢ idˢ {R})
      ≈ˢ b ⊗ˢ idˢ {rest ++ R}
  box-suffix-ˢ b rest R =
    ≈-trans (⊗-assocˢ b idˢ idˢ) (⊗-resp ≈-refl ⊗-id)

  ------------------------------------------------------------------------
  -- Vertex permutations
  ------------------------------------------------------------------------

  module Perm′ (V : Set) (vlab : V → X) where

    permuteˢ : xs ↭ ys → HomS (map vlab xs) (map vlab ys)
    permuteˢ Perm.refl         = idˢ
    permuteˢ (Perm.prep x p)   = idˢ {vlab x ∷ []} ⊗ˢ permuteˢ p
    permuteˢ (Perm.swap x y p) = σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ permuteˢ p
    permuteˢ (Perm.trans p q)  = permuteˢ q ∘ˢ permuteˢ p

    permuteˢ-subst
      : (e : ys ≡ ys') (p : xs ↭ ys)
      → permuteˢ (subst (λ z → xs ↭ z) e p)
        ≡ castˢ refl (cong (map vlab) e) (permuteˢ p)
    permuteˢ-subst refl p = refl

    permuteˢ-frame
      : (R : List V) (p : xs ↭ ys)
      → permuteˢ (++⁺ʳ R p) ≈̂ permuteˢ p ⊗ˢ idˢ {map vlab R}
    permuteˢ-frame {xs} R Perm.refl =
      ≈̂-trans (idˢ-≈̂ (map-++ vlab xs R)) (≈ˢ⇒≈̂ (≈-sym ⊗-id))
    permuteˢ-frame R (Perm.prep x p) =
      ≈̂-trans (⊗-resp-≈̂ ≈̂-refl (permuteˢ-frame R p))
              (≈̂-sym (castˢ⇒≈̂ _ _ (⊗-assocˢ _ _ _)))
    permuteˢ-frame R (Perm.swap x y p) =
      ≈̂-trans (⊗-resp-≈̂ ≈̂-refl (permuteˢ-frame R p))
              (≈̂-sym (castˢ⇒≈̂ _ _ (⊗-assocˢ _ _ _)))
    permuteˢ-frame R (Perm.trans p q) =
      ≈̂-trans (∘-resp-≈̂ (permuteˢ-frame R q) (permuteˢ-frame R p))
              (≈ˢ⇒≈̂ (≈-trans interchangeˢ (⊗-resp ≈-refl idˡ)))

    permuteˢ-frameˡ
      : (L : List V) (p : xs ↭ ys)
      → permuteˢ (++⁺ˡ L p) ≈̂ idˢ {map vlab L} ⊗ˢ permuteˢ p
    permuteˢ-frameˡ []      p = ≈ˢ⇒≈̂ (≈-sym (⊗-unitˡˢ (permuteˢ p)))
    permuteˢ-frameˡ (l ∷ L) p =
      ≈̂-trans (⊗-resp-≈̂ ≈̂-refl (permuteˢ-frameˡ L p))
        (≈̂-trans (≈̂-sym (castˢ⇒≈̂ _ _ (⊗-assocˢ _ _ _)))
                 (⊗-resp-≈̂ (≈ˢ⇒≈̂ ⊗-id) ≈̂-refl))

    -- Structural inversion avoids any label-injectivity hypothesis.
    permuteˢ-inv-left
      : (p : xs ↭ ys)
      → permuteˢ (Perm.↭-sym p) ∘ˢ permuteˢ p ≈ˢ idˢ {map vlab xs}
    permuteˢ-inv-left Perm.refl         = idˡ
    permuteˢ-inv-left (Perm.prep x p)   =
      ≈-trans interchangeˢ
        (≈-trans (⊗-resp idˡ (permuteˢ-inv-left p)) ⊗-id)
    permuteˢ-inv-left (Perm.swap x y p) =
      ≈-trans interchangeˢ
        (≈-trans (⊗-resp σ-σˢ (permuteˢ-inv-left p)) ⊗-id)
    permuteˢ-inv-left (Perm.trans p q)  =
      ≈-trans assocˢ
        (≈-trans (∘-resp ≈-refl (≈-sym assocˢ))
          (≈-trans (∘-resp ≈-refl (∘-resp (permuteˢ-inv-left q) ≈-refl))
            (≈-trans (∘-resp ≈-refl idˡ) (permuteˢ-inv-left p))))

    -- Use stdlib `↭-sym-involutive` rather than a second induction.
    permuteˢ-inv-right
      : (p : xs ↭ ys)
      → permuteˢ p ∘ˢ permuteˢ (Perm.↭-sym p) ≈ˢ idˢ {map vlab ys}
    permuteˢ-inv-right p =
      ≈-trans
        (∘-resp (≈-sym (≡⇒≈ˢ (cong permuteˢ (↭-sym-involutive p)))) ≈-refl)
        (permuteˢ-inv-left (Perm.↭-sym p))

  ------------------------------------------------------------------------
  -- Restriction along vertex labels
  ------------------------------------------------------------------------

  -- `map vlab` does not commute definitionally with `++`; `_⊗ᵛ_` and `σᵛ`
  -- absorb `map-++` transports once for the decoder.  Vertex associators
  -- reduce at singleton/cons frames.  `HomV` and `_≈ᵛ_` are definitionally
  -- their label-level counterparts, so crossing that boundary needs no functor.

  module Restrict (V : Set) (vlab : V → X) where

    open Perm′ V vlab

    private
      m : List V → List X
      m = map vlab

    HomV : List V → List V → Set
    HomV as bs = HomS (m as) (m bs)

    infixr 9 _∘ᵛ_
    infixr 10 _⊗ᵛ_
    infix 4 _≈ᵛ_

    idᵛ : HomV as as
    idᵛ = idˢ

    _∘ᵛ_ : HomV bs cs → HomV as bs → HomV as cs
    _∘ᵛ_ = _∘ˢ_

    _⊗ᵛ_ : HomV as bs → HomV us vs → HomV (as ++ us) (bs ++ vs)
    _⊗ᵛ_ {as} {bs} {us} {vs} f g =
      castˢ (sym (map-++ vlab as us)) (sym (map-++ vlab bs vs)) (f ⊗ˢ g)

    σᵛ : ∀ as bs → HomV (as ++ bs) (bs ++ as)
    σᵛ as bs =
      castˢ (sym (map-++ vlab as bs)) (sym (map-++ vlab bs as))
        (σˢ (m as) (m bs))

    castᵛ : as ≡ as' → bs ≡ bs' → HomV as bs → HomV as' bs'
    castᵛ = subst₂ HomV

    _≈ᵛ_ : HomV as bs → HomV as bs → Set
    _≈ᵛ_ = _≈ˢ_

    permuteᵛ : as ↭ bs → HomV as bs
    permuteᵛ = permuteˢ

    ------------------------------------------------------------------------
    -- Vertex transport calculus
    ------------------------------------------------------------------------

    castᵛ-cast
      : (p : as ≡ as') (q : bs ≡ bs') (t : HomV as bs)
      → castᵛ p q t ≡ castˢ (cong m p) (cong m q) t
    castᵛ-cast refl refl t = refl

    subst-codᵛ
      : (q : bs ≡ bs') (t : HomV as bs)
      → subst (HomV as) q t ≡ castᵛ refl q t
    subst-codᵛ refl t = refl

    cast-respᵛ
      : (p : as ≡ as') (q : bs ≡ bs') {f g : HomV as bs}
      → f ≈ᵛ g → castᵛ p q f ≈ᵛ castᵛ p q g
    cast-respᵛ refl refl e = e

    cast-idᵛ : (p q : as ≡ as') → castᵛ p q (idᵛ {as}) ≈ᵛ idᵛ {as'}
    cast-idᵛ p q =
      ≈-trans (≡⇒≈ˢ (castᵛ-cast p q idᵛ)) (cast-id (cong m p) (cong m q))

    cast-flipᵛ
      : (p : as ≡ as') (q : bs ≡ bs') {f : HomV as bs} {g : HomV as' bs'}
      → castᵛ p q f ≈ᵛ g → f ≈ᵛ castᵛ (sym p) (sym q) g
    cast-flipᵛ refl refl e = e

    cast-fuseᵛ
      : (p : as ≡ as') (p' : as' ≡ as'') (q : bs ≡ bs') (q' : bs' ≡ bs'')
        (t : HomV as bs)
      → castᵛ p' q' (castᵛ p q t) ≡ castᵛ (trans p p') (trans q q') t
    cast-fuseᵛ refl refl refl refl t = refl

    ∘-castᵛ
      : (p : as ≡ as') (q : bs ≡ bs') (r : cs ≡ cs')
        (g : HomV bs cs) (f : HomV as bs)
      → castᵛ q r g ∘ᵛ castᵛ p q f ≈ᵛ castᵛ p r (g ∘ᵛ f)
    ∘-castᵛ refl refl refl g f = ≈-refl

    -- Explicit factors pin the endpoint information hidden by projection.
    ⊗ᵛ-≈̂ : (f : HomV as bs) (g : HomV us vs)
         → (f ⊗ᵛ g) ≈̂ (f ⊗ˢ g)
    ⊗ᵛ-≈̂ {as} {bs} {us} {vs} f g =
      cast-≈̂ {p = sym (map-++ vlab as us)} {q = sym (map-++ vlab bs vs)}

    σᵛ-≈̂ : ∀ as bs → σᵛ as bs ≈̂ σˢ (m as) (m bs)
    σᵛ-≈̂ as bs =
      cast-≈̂ {p = sym (map-++ vlab as bs)} {q = sym (map-++ vlab bs as)}

    ⊗-resp-≈̂ᵛ
      : {f : HomV as bs} {f' : HomV as' bs'}
        {g : HomV us vs} {g' : HomV us' vs'}
      → f ≈̂ f' → g ≈̂ g' → (f ⊗ᵛ g) ≈̂ (f' ⊗ᵛ g')
    ⊗-resp-≈̂ᵛ {f = f} {f'} {g} {g'} ef eg =
      ≈̂-trans (⊗ᵛ-≈̂ f g) (≈̂-trans (⊗-resp-≈̂ ef eg) (≈̂-sym (⊗ᵛ-≈̂ f' g')))

    castᵛ-≈̂
      : (p : as ≡ as') (q : bs ≡ bs') (t : HomV as bs)
      → castᵛ p q t ≈̂ t
    castᵛ-≈̂ p q t =
      ≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (castᵛ-cast p q t)))
              (cast-≈̂ {p = cong m p} {q = cong m q})

    castᵛ⇒≈̂
      : (p : as ≡ as') (q : bs ≡ bs') (t : HomV as bs) {v : HomV as' bs'}
      → castᵛ p q t ≈ᵛ v → t ≈̂ v
    castᵛ⇒≈̂ p q t e =
      castˢ⇒≈̂ (cong m p) (cong m q)
              (≈-trans (≡⇒≈ˢ (sym (castᵛ-cast p q t))) e)

    ------------------------------------------------------------------------
    -- Vertex presentation
    ------------------------------------------------------------------------

    ⊗-respᵛ
      : {f f' : HomV as bs} {g g' : HomV us vs}
      → f ≈ᵛ f' → g ≈ᵛ g' → f ⊗ᵛ g ≈ᵛ f' ⊗ᵛ g'
    ⊗-respᵛ e e' = cast-resp _ _ (⊗-resp e e')

    ⊗-idᵛ : idᵛ {as} ⊗ᵛ idᵛ {us} ≈ᵛ idᵛ {as ++ us}
    ⊗-idᵛ = ≈-trans (cast-resp _ _ ⊗-id) (cast-id _ _)

    interchangeᵛ
      : {f : HomV bs cs} {g : HomV vs ws} {f' : HomV as bs} {g' : HomV us vs}
      → (f ⊗ᵛ g) ∘ᵛ (f' ⊗ᵛ g') ≈ᵛ (f ∘ᵛ f') ⊗ᵛ (g ∘ᵛ g')
    interchangeᵛ {f = f} {g} {f'} {g'} =
      viaˢ (∘-resp-≈̂ (⊗ᵛ-≈̂ f g) (⊗ᵛ-≈̂ f' g')) interchangeˢ
           (⊗ᵛ-≈̂ (f ∘ᵛ f') (g ∘ᵛ g'))

    private
      ⊗-assocᵛ
        : (f : HomV as bs) (g : HomV us vs) (h : HomV ps qs)
        → castᵛ (++-assoc as us ps) (++-assoc bs vs qs) ((f ⊗ᵛ g) ⊗ᵛ h)
          ≈ᵛ f ⊗ᵛ (g ⊗ᵛ h)
      ⊗-assocᵛ {as} {bs} {us} {vs} {ps} {qs} f g h =
        viaˢ lhs≈ (⊗-assocˢ f g h) rhs≈
        where
          lhs≈ : castᵛ (++-assoc as us ps) (++-assoc bs vs qs) ((f ⊗ᵛ g) ⊗ᵛ h)
                 ≈̂ castˢ (++-assoc (m as) (m us) (m ps))
                         (++-assoc (m bs) (m vs) (m qs)) ((f ⊗ˢ g) ⊗ˢ h)
          lhs≈ =
            ≈̂-trans (castᵛ-≈̂ (++-assoc as us ps) (++-assoc bs vs qs)
                      ((f ⊗ᵛ g) ⊗ᵛ h))
            (≈̂-trans (⊗ᵛ-≈̂ (f ⊗ᵛ g) h)
            (≈̂-trans (⊗-resp-≈̂ (⊗ᵛ-≈̂ f g) ≈̂-refl)
                     (≈̂-sym (cast-≈̂ {p = ++-assoc (m as) (m us) (m ps)}
                                    {q = ++-assoc (m bs) (m vs) (m qs)}))))

          rhs≈ : f ⊗ᵛ (g ⊗ᵛ h) ≈̂ (f ⊗ˢ (g ⊗ˢ h))
          rhs≈ =
            ≈̂-trans (⊗ᵛ-≈̂ f (g ⊗ᵛ h))
                    (⊗-resp-≈̂ ≈̂-refl (⊗ᵛ-≈̂ g h))

    ⊗-unitʳᵛ
      : (f : HomV as bs)
      → castᵛ (++-identityʳ as) (++-identityʳ bs) (f ⊗ᵛ idᵛ {[]}) ≈ᵛ f
    ⊗-unitʳᵛ {as} {bs} f =
      viaˢ (≈̂-trans (castᵛ-≈̂ (++-identityʳ as) (++-identityʳ bs) (f ⊗ᵛ idᵛ {[]}))
           (≈̂-trans (⊗ᵛ-≈̂ f (idᵛ {[]}))
                    (≈̂-sym (cast-≈̂ {p = ++-identityʳ (m as)}
                                   {q = ++-identityʳ (m bs)}))))
           (⊗-unitʳˢ f) ≈̂-refl

    σ-natᵛ
      : {f : HomV as bs} {g : HomV us vs}
      → σᵛ bs vs ∘ᵛ (f ⊗ᵛ g) ≈ᵛ (g ⊗ᵛ f) ∘ᵛ σᵛ as us
    σ-natᵛ {as} {bs} {us} {vs} {f} {g} =
      viaˢ (∘-resp-≈̂ (σᵛ-≈̂ bs vs) (⊗ᵛ-≈̂ f g)) σ-natˢ
           (∘-resp-≈̂ (⊗ᵛ-≈̂ g f) (σᵛ-≈̂ as us))

    σ-σᵛ : σᵛ bs as ∘ᵛ σᵛ as bs ≈ᵛ idᵛ {as ++ bs}
    σ-σᵛ {bs = bs} {as = as} =
      viaˢ (∘-resp-≈̂ (σᵛ-≈̂ bs as) (σᵛ-≈̂ as bs)) σ-σˢ
           (idˢ-≈̂ (map-++ vlab as bs))

    σ-hexᵛ
      : ∀ as bs cs
      → σᵛ (as ++ bs) cs
        ≈ᵛ castᵛ (sym (++-assoc as bs cs)) (++-assoc cs as bs)
             ((σᵛ as cs ⊗ᵛ idᵛ {bs})
               ∘ᵛ castᵛ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs))
    σ-hexᵛ as bs cs =
      viaˢ (≈̂-trans (σᵛ-≈̂ (as ++ bs) cs) (σ-≈̂ (map-++ vlab as bs) refl))
           (σ-hexˢ a b c) rhs≈
      where
        a = m as ; b = m bs ; c = m cs

        Cinner = castˢ refl (sym (++-assoc a c b)) (idˢ {a} ⊗ˢ σˢ b c)

        leftC : (σᵛ as cs ⊗ᵛ idᵛ {bs}) ≈̂ (σˢ a c ⊗ˢ idˢ {b})
        leftC =
          ≈̂-trans (⊗ᵛ-≈̂ (σᵛ as cs) (idᵛ {bs}))
                  (⊗-resp-≈̂ (σᵛ-≈̂ as cs) ≈̂-refl)

        rightC : castᵛ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs)
                 ≈̂ Cinner
        rightC =
          ≈̂-trans
            (≈̂-trans (castᵛ-≈̂ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs))
            (≈̂-trans (⊗ᵛ-≈̂ (idᵛ {as}) (σᵛ bs cs))
                     (⊗-resp-≈̂ ≈̂-refl (σᵛ-≈̂ bs cs))))
            (≈̂-sym (cast-≈̂ {p = refl} {q = sym (++-assoc a c b)}))

        rhs≈ : castᵛ (sym (++-assoc as bs cs)) (++-assoc cs as bs)
                 ((σᵛ as cs ⊗ᵛ idᵛ {bs})
                   ∘ᵛ castᵛ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs))
               ≈̂ castˢ (sym (++-assoc a b c)) (++-assoc c a b) ((σˢ a c ⊗ˢ idˢ {b}) ∘ˢ Cinner)
        rhs≈ =
          ≈̂-trans (castᵛ-≈̂ (sym (++-assoc as bs cs)) (++-assoc cs as bs) _)
          (≈̂-trans (∘-resp-≈̂ leftC rightC)
                   (≈̂-sym (cast-≈̂ {p = sym (++-assoc a b c)}
                                  {q = ++-assoc c a b})))

    σ-unitᵛ
      : ∀ as → σᵛ [] as ≈ᵛ castᵛ refl (sym (++-identityʳ as)) (idᵛ {as})
    σ-unitᵛ as =
      ≈-trans stepA (≡⇒≈ˢ (sym (castᵛ-cast refl (sym (++-identityʳ as)) idᵛ)))
      where
        stepA : σᵛ [] as
                ≈ᵛ castˢ refl (cong m (sym (++-identityʳ as))) (idˢ {m as})
        stepA =
          ≈-trans (cast-resp refl (sym (map-++ vlab as [])) (σ-unitˢ (m as)))
            (≡⇒≈ˢ
              (trans (cast-fuse refl refl (sym (++-identityʳ (m as)))
                        (sym (map-++ vlab as [])) (idˢ {m as}))
                     (cast-irrel refl refl _
                        (cong m (sym (++-identityʳ as))) (idˢ {m as}))))

    ------------------------------------------------------------------------
    -- Derived vertex laws
    ------------------------------------------------------------------------

    ⊗id-distᵛ
      : (f : HomV bs cs) (g : HomV as bs)
      → (f ∘ᵛ g) ⊗ᵛ idᵛ {R} ≈ᵛ (f ⊗ᵛ idᵛ {R}) ∘ᵛ (g ⊗ᵛ idᵛ {R})
    ⊗id-distᵛ f g = ≈-trans (⊗-respᵛ ≈-refl (≈-sym idˡ)) (≈-sym interchangeᵛ)

    box-conjᵛ
      : (g : HomV as bs) (cs : List V)
      → g ⊗ᵛ idᵛ {cs} ≈ᵛ σᵛ cs bs ∘ᵛ ((idᵛ {cs} ⊗ᵛ g) ∘ᵛ σᵛ as cs)
    box-conjᵛ g cs =
      ≈-sym
        (≈-trans (≈-sym assocˢ)
          (≈-trans (∘-resp σ-natᵛ ≈-refl)
            (≈-trans assocˢ (≈-trans (∘-resp ≈-refl σ-σᵛ) idʳ))))

    box-suffix-ᵛ
      : (b : HomV as bs) (rest R : List V)
      → castᵛ (++-assoc as rest R) (++-assoc bs rest R)
          ((b ⊗ᵛ idᵛ {rest}) ⊗ᵛ idᵛ {R})
        ≈ᵛ b ⊗ᵛ idᵛ {rest ++ R}
    box-suffix-ᵛ b rest R =
      ≈-trans (⊗-assocᵛ b idᵛ idᵛ) (⊗-respᵛ ≈-refl ⊗-idᵛ)

    ⊗-assoc-≈̂ᵛ
      : (f : HomV as bs) (g : HomV us vs) (h : HomV ps qs)
      → ((f ⊗ᵛ g) ⊗ᵛ h) ≈̂ (f ⊗ᵛ (g ⊗ᵛ h))
    ⊗-assoc-≈̂ᵛ {as} {bs} {us} {vs} {ps} {qs} f g h =
      ≈̂-trans (≈̂-sym (castᵛ-≈̂ (++-assoc as us ps) (++-assoc bs vs qs)
                        ((f ⊗ᵛ g) ⊗ᵛ h)))
              (≈ˢ⇒≈̂ (⊗-assocᵛ f g h))

    box-suffix-≈̂ᵛ
      : (b : HomV as bs) (rest R : List V)
      → ((b ⊗ᵛ idᵛ {rest}) ⊗ᵛ idᵛ {R}) ≈̂ (b ⊗ᵛ idᵛ {rest ++ R})
    box-suffix-≈̂ᵛ {as} {bs} b rest R =
      ≈̂-trans (≈̂-sym (castᵛ-≈̂ (++-assoc as rest R) (++-assoc bs rest R)
                        ((b ⊗ᵛ idᵛ {rest}) ⊗ᵛ idᵛ {R})))
              (≈ˢ⇒≈̂ (box-suffix-ᵛ b rest R))

    permuteᵛ-frame
      : (R : List V) (p : as ↭ bs)
      → permuteᵛ (++⁺ʳ R p) ≈ᵛ permuteᵛ p ⊗ᵛ idᵛ {R}
    permuteᵛ-frame R p = ≈̂⇒≈ˢ (≈̂-trans (permuteˢ-frame R p) (≈̂-sym cast-≈̂))

    permuteᵛ-frameˡ
      : (L : List V) (p : as ↭ bs)
      → permuteᵛ (++⁺ˡ L p) ≈ᵛ idᵛ {L} ⊗ᵛ permuteᵛ p
    permuteᵛ-frameˡ L p = ≈̂⇒≈ˢ (≈̂-trans (permuteˢ-frameˡ L p) (≈̂-sym cast-≈̂))

--------------------------------------------------------------------------------
-- Generator translation
--------------------------------------------------------------------------------

module Map
  (X : Set) (_≟X_ : DecidableEquality X)
  (mor₁ mor₂ : List X → List X → Set)
  (J : ∀ {as bs} → mor₁ as bs → mor₂ as bs)
  where

  private
    variable
      xs xs' ys ys' : List X
    module S₁ = Build X _≟X_ mor₁
    module S₂ = Build X _≟X_ mor₂

  mapS : S₁.HomS xs ys → S₂.HomS xs ys
  mapS S₁.idˢ          = S₂.idˢ
  mapS (g S₁.∘ˢ f)     = mapS g S₂.∘ˢ mapS f
  mapS (f S₁.⊗ˢ g)     = mapS f S₂.⊗ˢ mapS g
  mapS (S₁.genˢ t)     = S₂.genˢ (J t)
  mapS (S₁.σˢ xs ys)   = S₂.σˢ xs ys

  private
    mapS-cast
      : (p : xs ≡ xs') (q : ys ≡ ys') (t : S₁.HomS xs ys)
      → mapS (S₁.castˢ p q t) ≡ S₂.castˢ p q (mapS t)
    mapS-cast refl refl t = refl

  mapS-resp
    : {f g : S₁.HomS xs ys} → f S₁.≈ˢ g → mapS f S₂.≈ˢ mapS g
  mapS-resp S₁.≈-refl          = S₂.≈-refl
  mapS-resp (S₁.≈-sym e)       = S₂.≈-sym (mapS-resp e)
  mapS-resp (S₁.≈-trans e e')  = S₂.≈-trans (mapS-resp e) (mapS-resp e')
  mapS-resp (S₁.∘-resp e e')   = S₂.∘-resp (mapS-resp e) (mapS-resp e')
  mapS-resp (S₁.⊗-resp e e')   = S₂.⊗-resp (mapS-resp e) (mapS-resp e')
  mapS-resp S₁.idˡ             = S₂.idˡ
  mapS-resp S₁.idʳ             = S₂.idʳ
  mapS-resp S₁.assocˢ          = S₂.assocˢ
  mapS-resp S₁.⊗-id            = S₂.⊗-id
  mapS-resp S₁.interchangeˢ    = S₂.interchangeˢ
  mapS-resp (S₁.⊗-assocˢ {xs} {ys} {us} {vs} {ps} {qs} f g h) =
    S₂.≈-trans
      (S₂.≡⇒≈ˢ (mapS-cast (++-assoc xs us ps) (++-assoc ys vs qs)
                  ((f S₁.⊗ˢ g) S₁.⊗ˢ h)))
      (S₂.⊗-assocˢ (mapS f) (mapS g) (mapS h))
  mapS-resp (S₁.⊗-unitʳˢ {xs} {ys} f) =
    S₂.≈-trans
      (S₂.≡⇒≈ˢ (mapS-cast (++-identityʳ xs) (++-identityʳ ys)
                  (f S₁.⊗ˢ S₁.idˢ)))
      (S₂.⊗-unitʳˢ (mapS f))
  mapS-resp S₁.σ-natˢ          = S₂.σ-natˢ
  mapS-resp S₁.σ-σˢ            = S₂.σ-σˢ
  mapS-resp (S₁.σ-hexˢ xs ys zs) =
    S₂.≈-trans (S₂.σ-hexˢ xs ys zs)
      (S₂.≈-sym (S₂.≡⇒≈ˢ (trans
        (mapS-cast (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
           ((S₁.σˢ xs zs S₁.⊗ˢ S₁.idˢ {ys})
             S₁.∘ˢ S₁.castˢ refl (sym (++-assoc xs zs ys))
                     (S₁.idˢ {xs} S₁.⊗ˢ S₁.σˢ ys zs)))
        (cong (λ z → S₂.castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                       ((S₂.σˢ xs zs S₂.⊗ˢ S₂.idˢ {ys}) S₂.∘ˢ z))
              (mapS-cast refl (sym (++-assoc xs zs ys))
                 (S₁.idˢ {xs} S₁.⊗ˢ S₁.σˢ ys zs))))))
  mapS-resp (S₁.σ-unitˢ xs) =
    S₂.≈-trans (S₂.σ-unitˢ xs)
      (S₂.≈-sym (S₂.≡⇒≈ˢ
        (mapS-cast refl (sym (++-identityʳ xs)) (S₁.idˢ {xs}))))
