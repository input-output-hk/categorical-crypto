{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- A presented free STRICT SMC with objects `List X` and `⊗ = ++`: the
-- middle category of the strictified soundness pipeline.
--
-- `++` is NOT definitionally associative/right-unital on variables, so
-- object-index mismatches still need transports — but they are EQUALITY
-- casts (UIP-trivial: `List X` has decidable equality), not coherence
-- isomorphisms carrying naturality obligations.  Design invariants:
--   * `++-assoc (a ∷ b ∷ []) us vs` and `map-++ vlab (x ∷ xs) R` REDUCE
--     (their cons clauses fire), so casts at cons/singleton frames vanish
--     definitionally — exactly the shapes the decoder produces;
--   * every cast lemma is derived by refl-matching + UIP; `_≈ˢ_` needs NO
--     cast-related axiom.
--
-- `Build` constructs the category over a generator family `mor`; `Map`
-- is the evident homomorphism along a generator translation (used to move
-- from the `FlatGen`-generated instance into the `HomTerm`-generated one
-- that `Strict.Embed` embeds back into the free SMC).
--
-- `box-suffix-ˢ`/`box-commute-ˢ`/`permuteˢ-frame` at the bottom are the
-- strict forms of the decoder's separability/commutation/frame lemmas.
--------------------------------------------------------------------------------

module Categories.FreeStrictSMC where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ≡-dec; map-++)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Axiom.UniquenessOfIdentityProofs using (UIP; module Decidable⇒UIP)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)

module Build
  (X : Set) (_≟X_ : DecidableEquality X)
  (mor : List X → List X → Set)
  where

  uipL : UIP (List X)
  uipL = Decidable⇒UIP.≡-irrelevant (≡-dec _≟X_)

  ------------------------------------------------------------------------
  -- The presented strict SMC.

  infixr 9 _∘ˢ_
  infixr 10 _⊗ˢ_

  data HomS : List X → List X → Set where
    idˢ  : ∀ {xs} → HomS xs xs
    _∘ˢ_ : ∀ {xs ys zs} → HomS ys zs → HomS xs ys → HomS xs zs
    _⊗ˢ_ : ∀ {xs ys us vs} → HomS xs ys → HomS us vs → HomS (xs ++ us) (ys ++ vs)
    genˢ : ∀ {as bs} → mor as bs → HomS as bs
    σˢ   : ∀ xs ys → HomS (xs ++ ys) (ys ++ xs)

  castˢ : ∀ {xs xs' ys ys'} → xs ≡ xs' → ys ≡ ys' → HomS xs ys → HomS xs' ys'
  castˢ = subst₂ HomS

  infix 4 _≈ˢ_

  data _≈ˢ_ : ∀ {xs ys} → HomS xs ys → HomS xs ys → Set where
    -- equivalence + congruence
    ≈-refl  : ∀ {xs ys} {f : HomS xs ys} → f ≈ˢ f
    ≈-sym   : ∀ {xs ys} {f g : HomS xs ys} → f ≈ˢ g → g ≈ˢ f
    ≈-trans : ∀ {xs ys} {f g h : HomS xs ys} → f ≈ˢ g → g ≈ˢ h → f ≈ˢ h
    ∘-resp  : ∀ {xs ys zs} {g g' : HomS ys zs} {f f' : HomS xs ys}
            → g ≈ˢ g' → f ≈ˢ f' → g ∘ˢ f ≈ˢ g' ∘ˢ f'
    ⊗-resp  : ∀ {xs ys us vs} {f f' : HomS xs ys} {g g' : HomS us vs}
            → f ≈ˢ f' → g ≈ˢ g' → f ⊗ˢ g ≈ˢ f' ⊗ˢ g'
    -- category
    idˡ    : ∀ {xs ys} {f : HomS xs ys} → idˢ ∘ˢ f ≈ˢ f
    idʳ    : ∀ {xs ys} {f : HomS xs ys} → f ∘ˢ idˢ ≈ˢ f
    assocˢ : ∀ {ws xs ys zs} {h : HomS ys zs} {g : HomS xs ys} {f : HomS ws xs}
           → (h ∘ˢ g) ∘ˢ f ≈ˢ h ∘ˢ (g ∘ˢ f)
    -- strict monoidal
    ⊗-id   : ∀ {xs us} → idˢ {xs} ⊗ˢ idˢ {us} ≈ˢ idˢ {xs ++ us}
    interchangeˢ
      : ∀ {xs ys zs us vs ws}
          {a : HomS ys zs} {b : HomS vs ws} {c : HomS xs ys} {d : HomS us vs}
      → (a ⊗ˢ b) ∘ˢ (c ⊗ˢ d) ≈ˢ (a ∘ˢ c) ⊗ˢ (b ∘ˢ d)
    ⊗-assocˢ
      : ∀ {xs ys us vs ps qs}
          (f : HomS xs ys) (g : HomS us vs) (h : HomS ps qs)
      → castˢ (++-assoc xs us ps) (++-assoc ys vs qs) ((f ⊗ˢ g) ⊗ˢ h)
        ≈ˢ f ⊗ˢ (g ⊗ˢ h)
    ⊗-unitʳˢ
      : ∀ {xs ys} (f : HomS xs ys)
      → castˢ (++-identityʳ xs) (++-identityʳ ys) (f ⊗ˢ idˢ {[]}) ≈ˢ f
    -- symmetry
    σ-natˢ : ∀ {xs ys us vs} {f : HomS xs ys} {g : HomS us vs}
           → σˢ ys vs ∘ˢ (f ⊗ˢ g) ≈ˢ (g ⊗ˢ f) ∘ˢ σˢ xs us
    σ-σˢ   : ∀ {xs ys} → σˢ ys xs ∘ˢ σˢ xs ys ≈ˢ idˢ
    σ-hexˢ : ∀ xs ys zs
           → σˢ (xs ++ ys) zs
             ≈ˢ castˢ (sym (++-assoc xs ys zs)) (++-assoc zs xs ys)
                  ((σˢ xs zs ⊗ˢ idˢ {ys})
                    ∘ˢ castˢ refl (sym (++-assoc xs zs ys))
                         (idˢ {xs} ⊗ˢ σˢ ys zs))
    -- unit braiding coherence (true in every braided category; an axiom of
    -- the presentation so the strict side can derive the LEFT unit laws,
    -- which have no cast: `[] ++ xs` reduces)
    σ-unitˢ : ∀ xs
            → σˢ [] xs ≈ˢ castˢ refl (sym (++-identityʳ xs)) (idˢ {xs})

  ------------------------------------------------------------------------
  -- The cast kit.  Everything DERIVED (refl-matching + UIP); `_≈ˢ_` has
  -- no cast-related axiom.

  ≡⇒≈ˢ : ∀ {xs ys} {f g : HomS xs ys} → f ≡ g → f ≈ˢ g
  ≡⇒≈ˢ refl = ≈-refl

  cast-resp
    : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') {f g : HomS xs ys}
    → f ≈ˢ g → castˢ p q f ≈ˢ castˢ p q g
  cast-resp refl refl f≈g = f≈g

  cast-fuse
    : ∀ {xs xs' xs'' ys ys' ys''}
        (p : xs ≡ xs') (p' : xs' ≡ xs'') (q : ys ≡ ys') (q' : ys' ≡ ys'')
        (f : HomS xs ys)
    → castˢ p' q' (castˢ p q f) ≡ castˢ (trans p p') (trans q q') f
  cast-fuse refl refl refl refl f = refl

  cast-irrel
    : ∀ {xs xs' ys ys'} (p p' : xs ≡ xs') (q q' : ys ≡ ys') (f : HomS xs ys)
    → castˢ p q f ≡ castˢ p' q' f
  cast-irrel p p' q q' f rewrite uipL p p' | uipL q q' = refl

  cast-id
    : ∀ {xs xs'} (p q : xs ≡ xs') → castˢ p q (idˢ {xs}) ≈ˢ idˢ {xs'}
  cast-id refl q rewrite uipL q refl = ≈-refl

  -- a cast that only moves the RIGHT ⊗-factor's endpoints commutes with a
  -- fixed left frame (arbitrary proofs P, Q absorbed by UIP)
  cast-⊗-frame
    : ∀ {ls ls'} (h : HomS ls ls')
        {us us' vs vs'} (p' : us ≡ us') (q' : vs ≡ vs') (f : HomS us vs)
        (P : ls ++ us ≡ ls ++ us') (Q : ls' ++ vs ≡ ls' ++ vs')
    → castˢ P Q (h ⊗ˢ f) ≈ˢ h ⊗ˢ castˢ p' q' f
  cast-⊗-frame h refl refl f P Q
    rewrite uipL P refl | uipL Q refl = ≈-refl

  -- a cast pulled out of the left factor of a ⊗ with a fixed right id-frame
  cast-⊗ˡ
    : ∀ {us us' vs vs' ls} (p' : us ≡ us') (q' : vs ≡ vs') (f : HomS us vs)
    → castˢ p' q' f ⊗ˢ idˢ {ls}
      ≡ castˢ (cong (_++ ls) p') (cong (_++ ls) q') (f ⊗ˢ idˢ {ls})
  cast-⊗ˡ refl refl f = refl

  -- split a cast over a composition through a chosen middle proof
  ∘-cast-split
    : ∀ {as as' bs bs' cs cs'}
        (P : as ≡ as') (M : bs ≡ bs') (Q : cs ≡ cs')
        (g : HomS bs cs) (f : HomS as bs)
    → castˢ P Q (g ∘ˢ f) ≈ˢ castˢ M Q g ∘ˢ castˢ P M f
  ∘-cast-split refl refl refl g f = ≈-refl

  -- flip a cast to the other side of `_≈ˢ_`
  cast-flip
    : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys')
        {f : HomS xs ys} {g : HomS xs' ys'}
    → castˢ p q f ≈ˢ g → f ≈ˢ castˢ (sym p) (sym q) g
  cast-flip refl refl e = e

  ------------------------------------------------------------------------
  -- Unit-side laws, DERIVED from `σ-unitˢ` (the left forms are cast-free
  -- because `[] ++ xs` reduces).

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

  ⊗-unitˡˢ : ∀ {xs ys} (f : HomS xs ys) → idˢ {[]} ⊗ˢ f ≈ˢ f
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

  ------------------------------------------------------------------------
  -- MEASUREMENT 1: the fired-edge separability step (`box-suffix`).
  -- Non-strict version: ~281 LOC + the BoxAssoc bracket machinery.

  box-suffix-ˢ
    : ∀ {as bs} (b : HomS as bs) (rest R : List X)
    → castˢ (++-assoc as rest R) (++-assoc bs rest R)
        ((b ⊗ˢ idˢ {rest}) ⊗ˢ idˢ {R})
      ≈ˢ b ⊗ˢ idˢ {rest ++ R}
  box-suffix-ˢ b rest R =
    ≈-trans (⊗-assocˢ b idˢ idˢ) (⊗-resp ≈-refl ⊗-id)

  ------------------------------------------------------------------------
  -- MEASUREMENT 2: the per-swap disjoint-block box commutation
  -- (the "independent firings commute" core of part (II)).

  box-commute-ˢ
    : ∀ {as bs cs ds} (b : HomS as bs) (b' : HomS cs ds)
    → (b ⊗ˢ idˢ {ds}) ∘ˢ (idˢ {as} ⊗ˢ b')
      ≈ˢ (idˢ {bs} ⊗ˢ b') ∘ˢ (b ⊗ˢ idˢ {cs})
  box-commute-ˢ b b' =
    ≈-trans interchangeˢ
      (≈-trans (⊗-resp idʳ idˡ)
        (≈-sym (≈-trans interchangeˢ (⊗-resp idˡ idʳ))))

  ------------------------------------------------------------------------
  -- MEASUREMENT 3: `permuteˢ` and the residual-frame lemmas
  -- (the `frame-ext` analogue).  Note prep/swap need NO cast in the
  -- DEFINITION: singleton/cons left frames make `++` reduce.
  -- Parameterised by the vertex set, so `HomS` itself stays independent
  -- of any particular hypergraph.

  module Perm′ (V : Set) (vlab : V → X) where

    open import Data.List.Relation.Binary.Permutation.Propositional.Properties
      using (++⁺ʳ)

    permuteˢ : ∀ {xs ys : List V} → xs ↭ ys → HomS (map vlab xs) (map vlab ys)
    permuteˢ Perm.refl         = idˢ
    permuteˢ (Perm.prep x p)   = idˢ {vlab x ∷ []} ⊗ˢ permuteˢ p
    permuteˢ (Perm.swap x y p) = σˢ (vlab x ∷ []) (vlab y ∷ []) ⊗ˢ permuteˢ p
    permuteˢ (Perm.trans p q)  = permuteˢ q ∘ˢ permuteˢ p

    -- permuteˢ of a subst-ed derivation is a cast of permuteˢ
    permuteˢ-subst
      : ∀ {xs ys ys' : List V} (e : ys ≡ ys') (p : xs ↭ ys)
      → permuteˢ (subst (λ z → xs ↭ z) e p)
        ≡ castˢ refl (cong (map vlab) e) (permuteˢ p)
    permuteˢ-subst refl p = refl

    -- the stdlib residual frame `++⁺ʳ R` factors through `⊗ˢ idˢ`
    permuteˢ-frame
      : ∀ {xs ys : List V} (R : List V) (p : xs ↭ ys)
      → castˢ (map-++ vlab xs R) (map-++ vlab ys R) (permuteˢ (++⁺ʳ R p))
        ≈ˢ permuteˢ p ⊗ˢ idˢ {map vlab R}
    permuteˢ-frame {xs} R Perm.refl =
      ≈-trans (cast-id (map-++ vlab xs R) (map-++ vlab xs R)) (≈-sym ⊗-id)
    permuteˢ-frame R (Perm.prep x p) =
      ≈-trans
        (cast-⊗-frame (idˢ {vlab x ∷ []})
          (map-++ vlab _ R) (map-++ vlab _ R) (permuteˢ (++⁺ʳ R p)) _ _)
        (≈-trans (⊗-resp ≈-refl (permuteˢ-frame R p))
                 (≈-sym (⊗-assocˢ (idˢ {vlab x ∷ []}) (permuteˢ p) idˢ)))
    permuteˢ-frame R (Perm.swap x y p) =
      ≈-trans
        (cast-⊗-frame (σˢ (vlab x ∷ []) (vlab y ∷ []))
          (map-++ vlab _ R) (map-++ vlab _ R) (permuteˢ (++⁺ʳ R p)) _ _)
        (≈-trans (⊗-resp ≈-refl (permuteˢ-frame R p))
                 (≈-sym (⊗-assocˢ (σˢ (vlab x ∷ []) (vlab y ∷ []))
                                  (permuteˢ p) idˢ)))
    permuteˢ-frame R (Perm.trans p q) =
      ≈-trans
        (∘-cast-split (map-++ vlab _ R) (map-++ vlab _ R) (map-++ vlab _ R)
          (permuteˢ (++⁺ʳ R q)) (permuteˢ (++⁺ʳ R p)))
        (≈-trans (∘-resp (permuteˢ-frame R q) (permuteˢ-frame R p))
                 (≈-trans interchangeˢ (⊗-resp ≈-refl idˡ)))

--------------------------------------------------------------------------------
-- The homomorphism along a generator translation `J : mor₁ ⇒ mor₂`
-- (identity on objects).  `castˢ` commutes with it on the nose, so every
-- `_≈ˢ_` axiom maps to its counterpart.

module Map
  (X : Set) (_≟X_ : DecidableEquality X)
  (mor₁ mor₂ : List X → List X → Set)
  (J : ∀ {as bs} → mor₁ as bs → mor₂ as bs)
  where

  private
    module S₁ = Build X _≟X_ mor₁
    module S₂ = Build X _≟X_ mor₂

  mapS : ∀ {xs ys} → S₁.HomS xs ys → S₂.HomS xs ys
  mapS S₁.idˢ          = S₂.idˢ
  mapS (g S₁.∘ˢ f)     = mapS g S₂.∘ˢ mapS f
  mapS (f S₁.⊗ˢ g)     = mapS f S₂.⊗ˢ mapS g
  mapS (S₁.genˢ t)     = S₂.genˢ (J t)
  mapS (S₁.σˢ xs ys)   = S₂.σˢ xs ys

  mapS-cast
    : ∀ {xs xs' ys ys'} (p : xs ≡ xs') (q : ys ≡ ys') (t : S₁.HomS xs ys)
    → mapS (S₁.castˢ p q t) ≡ S₂.castˢ p q (mapS t)
  mapS-cast refl refl t = refl

  mapS-resp
    : ∀ {xs ys} {f g : S₁.HomS xs ys} → f S₁.≈ˢ g → mapS f S₂.≈ˢ mapS g
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
