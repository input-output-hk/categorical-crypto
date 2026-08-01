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
open import Data.Product using (Σ-syntax; _,_)
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
  -- Heterogeneous strict equality `_≈̂_` (F1).
  --
  -- `_≈ˢ_` only relates morphisms at IDENTICAL endpoints, so every step of a
  -- decoder proof that moves a morphism across a `++`/`map` boundary must
  -- name the endpoint mismatch and glue it with `cast-fuse`/`cast-irrel`/
  -- `∘-cast-split`.  `_≈̂_` packages the two endpoint equalities into the
  -- relation (the SAME device as `_≅↭ᴴ_` in `FaithfulnessInductive`), so a
  -- chain of `≈̂`-steps pays the endpoint bookkeeping ONCE, inside the
  -- congruence/transitivity combinators, instead of at every step.  The
  -- endpoints are `List X`, a set (UIP via `uipL`), so no coherence leaks.

  infix 4 _≈̂_
  _≈̂_ : ∀ {as bs as' bs'} → HomS as bs → HomS as' bs' → Set
  _≈̂_ {as} {bs} {as'} {bs'} f g =
    Σ[ p ∈ as ≡ as' ] Σ[ q ∈ bs ≡ bs' ] (castˢ p q f ≈ˢ g)

  -- embed the homogeneous equivalence (`castˢ refl refl` reduces)
  ≈ˢ⇒≈̂ : ∀ {as bs} {f g : HomS as bs} → f ≈ˢ g → f ≈̂ g
  ≈ˢ⇒≈̂ e = refl , refl , e

  ≈̂-refl : ∀ {as bs} {f : HomS as bs} → f ≈̂ f
  ≈̂-refl = refl , refl , ≈-refl

  -- the ONE lemma that retires `cast-fuse`/`cast-irrel`/`cast-flip`: a cast is
  -- heterogeneously equal to its content.
  cast-≈̂ : ∀ {as bs as' bs'} {p : as ≡ as'} {q : bs ≡ bs'} {f : HomS as bs}
         → castˢ p q f ≈̂ f
  cast-≈̂ {p = p} {q} {f} =
    sym p , sym q ,
    ≈-trans (≡⇒≈ˢ (cast-fuse p (sym p) q (sym q) f))
            (≡⇒≈ˢ (cast-irrel (trans p (sym p)) refl (trans q (sym q)) refl f))

  ≈̂-sym : ∀ {as bs as' bs'} {f : HomS as bs} {g : HomS as' bs'}
        → f ≈̂ g → g ≈̂ f
  ≈̂-sym (p , q , e) = sym p , sym q , ≈-sym (cast-flip p q e)

  ≈̂-trans : ∀ {as bs as' bs' as'' bs''}
              {f : HomS as bs} {g : HomS as' bs'} {h : HomS as'' bs''}
          → f ≈̂ g → g ≈̂ h → f ≈̂ h
  ≈̂-trans {f = f} (p₁ , q₁ , e₁) (p₂ , q₂ , e₂) =
    trans p₁ p₂ , trans q₁ q₂ ,
    ≈-trans (≡⇒≈ˢ (sym (cast-fuse p₁ p₂ q₁ q₂ f)))
            (≈-trans (cast-resp p₂ q₂ e₁) e₂)

  -- composition congruence: threads the middle endpoint through `∘-cast-split`
  -- (choosing `g`'s domain proof as the middle) — no refl-matching needed.
  ∘-resp-≈̂ : ∀ {as bs cs as' bs' cs'}
               {g : HomS bs cs} {g' : HomS bs' cs'}
               {f : HomS as bs} {f' : HomS as' bs'}
           → g ≈̂ g' → f ≈̂ f' → (g ∘ˢ f) ≈̂ (g' ∘ˢ f')
  ∘-resp-≈̂ {g = g} {f = f} (gd , gc , eg) (fd , fc , ef) =
    fd , gc ,
    ≈-trans (∘-cast-split fd gd gc g f)
            (∘-resp eg (≈-trans (≡⇒≈ˢ (cast-irrel fd fd gd fc f)) ef))

  -- a cast over a ⊗ splits into a cast on each factor, through the two
  -- `cong₂ _++_` endpoint proofs (all four component proofs refl-match: then
  -- both `cong₂` reduce to refl and every `castˢ … refl refl` vanishes).
  -- This is the ⊗-analogue of `∘-cast-split`; it dissolves the ⊗-frame
  -- entanglement that blocked TensorBraid / Decoder / DecodeSigma.
  cast-⊗-both
    : ∀ {as as' bs bs' us us' vs vs'}
        (p : as ≡ as') (q : bs ≡ bs') (r : us ≡ us') (s : vs ≡ vs')
        (f : HomS as bs) (g : HomS us vs)
    → castˢ (cong₂ _++_ p r) (cong₂ _++_ q s) (f ⊗ˢ g)
      ≡ castˢ p q f ⊗ˢ castˢ r s g
  cast-⊗-both refl refl refl refl f g = refl

  -- tensor congruence at GENERAL endpoints: the tensor's own endpoint proofs
  -- are the `cong₂ _++_` of the two factors' proofs; `cast-⊗-both` splits the
  -- combined cast into the two factor casts, which `⊗-resp` then relates.
  -- (Endpoint proofs are NOT refl here, so pin `cast-⊗-both`'s arguments when a
  -- projected `≈̂⇒≈ˢ` chain leaves the factor metas free — same discipline as
  -- `cast-≈̂` in a homogeneous-projected chain.)
  ⊗-resp-≈̂ : ∀ {as bs us vs as' bs' us' vs'}
               {f : HomS as bs} {f' : HomS as' bs'}
               {g : HomS us vs} {g' : HomS us' vs'}
           → f ≈̂ f' → g ≈̂ g' → (f ⊗ˢ g) ≈̂ (f' ⊗ˢ g')
  ⊗-resp-≈̂ {f = f} {g = g} (fp , fq , ef) (gp , gq , eg) =
    cong₂ _++_ fp gp , cong₂ _++_ fq gq ,
    ≈-trans (≡⇒≈ˢ (cast-⊗-both fp fq gp gq f g)) (⊗-resp ef eg)

  -- project back to `≈ˢ` once the endpoints coincide (UIP collapses the proofs)
  ≈̂⇒≈ˢ : ∀ {as bs} {f g : HomS as bs} → f ≈̂ g → f ≈ˢ g
  ≈̂⇒≈ˢ {f = f} (p , q , e) =
    ≈-trans (≈-sym (≡⇒≈ˢ (cast-irrel p refl q refl f))) e

  -- the two object-level bridges: an identity and a braiding transported
  -- across propositional endpoint equalities
  idˢ-≈̂ : ∀ {as bs : List X} (p : as ≡ bs) → idˢ {as} ≈̂ idˢ {bs}
  idˢ-≈̂ p = p , p , cast-id p p

  σ-≈̂ : ∀ {as as' bs bs' : List X} (p : as ≡ as') (q : bs ≡ bs')
      → σˢ as bs ≈̂ σˢ as' bs'
  σ-≈̂ refl refl = ≈̂-refl

  -- …or discharge the cast form at ANY externally pinned pair of endpoint
  -- proofs (UIP again): the projection consumers with a fixed signature need
  ≈̂⇒castˢ
    : ∀ {as bs as' bs'} {f : HomS as bs} {g : HomS as' bs'}
    → f ≈̂ g → (P : as ≡ as') (Q : bs ≡ bs') → castˢ P Q f ≈ˢ g
  ≈̂⇒castˢ {f = f} (p , q , e) P Q = ≈-trans (≡⇒≈ˢ (cast-irrel P p Q q f)) e

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

  -- `(f ∘ g) ⊗ id{R} ≈ (f ⊗ id{R}) ∘ (g ⊗ id{R})` — composition
  -- distributes over an identity frame on the right (interchange with
  -- `id ∘ id` collapsed).  Shared by the strict decoder/interchange/
  -- tensor modules.
  ⊗id-distˢ
    : ∀ {as bs cs R : List X} (f : HomS bs cs) (g : HomS as bs)
    → (f ∘ˢ g) ⊗ˢ idˢ {R} ≈ˢ (f ⊗ˢ idˢ {R}) ∘ˢ (g ⊗ˢ idˢ {R})
  ⊗id-distˢ f g = ≈-trans (⊗-resp ≈-refl (≈-sym idˡ)) (≈-sym interchangeˢ)

  ------------------------------------------------------------------------
  -- MEASUREMENT 3: `permuteˢ` and the residual-frame lemmas
  -- (the `frame-ext` analogue).  Note prep/swap need NO cast in the
  -- DEFINITION: singleton/cons left frames make `++` reduce.
  -- Parameterised by the vertex set, so `HomS` itself stays independent
  -- of any particular hypergraph.

  module Perm′ (V : Set) (vlab : V → X) where

    open import Data.List.Relation.Binary.Permutation.Propositional.Properties
      using (++⁺ʳ; ++⁺ˡ; ↭-sym-involutive)

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

    -- the stdlib LEFT residual frame `++⁺ˡ L` factors through `idˢ ⊗ˢ_`
    -- (`permuteˢ-frame`'s mirror; cons clauses of `map-++`/`++-assoc` reduce,
    -- so only the `map-++ vlab L _` boundary cast is paid)
    permuteˢ-frameˡ
      : ∀ (L : List V) {xs ys : List V} (p : xs ↭ ys)
      → castˢ (map-++ vlab L xs) (map-++ vlab L ys) (permuteˢ (++⁺ˡ L p))
        ≈ˢ idˢ {map vlab L} ⊗ˢ permuteˢ p
    permuteˢ-frameˡ []       {xs} {ys} p =
      ≈-trans (≡⇒≈ˢ (cast-irrel (map-++ vlab [] xs) refl
                                (map-++ vlab [] ys) refl (permuteˢ p)))
              (≈-sym (⊗-unitˡˢ (permuteˢ p)))
    permuteˢ-frameˡ (l ∷ L) {xs} {ys} p =
      ≈-trans
        (cast-⊗-frame (idˢ {vlab l ∷ []})
          (map-++ vlab L xs) (map-++ vlab L ys) (permuteˢ (++⁺ˡ L p))
          (map-++ vlab (l ∷ L) xs) (map-++ vlab (l ∷ L) ys))
        (≈-trans (⊗-resp (≈-refl {f = idˢ {vlab l ∷ []}}) (permuteˢ-frameˡ L p))
          (≈-trans (≈-sym (⊗-assocˢ (idˢ {vlab l ∷ []}) (idˢ {map vlab L})
                                    (permuteˢ p)))
            (cast-resp (++-assoc (vlab l ∷ []) (map vlab L) _)
                       (++-assoc (vlab l ∷ []) (map vlab L) _)
                       (⊗-resp ⊗-id ≈-refl))))

    -- `permuteˢ` of an inverse derivation is the categorical inverse.
    -- K-FREE: structural on the derivation, so the `Support.PermK` residual is
    -- NOT involved (contrast the `eval-↭`/`FinBij` self-loop route).
    permuteˢ-inv-left
      : ∀ {xs ys : List V} (p : xs ↭ ys)
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

    -- the mirror, via stdlib `↭-sym-involutive` rather than a second induction
    permuteˢ-inv-right
      : ∀ {xs ys : List V} (p : xs ↭ ys)
      → permuteˢ p ∘ˢ permuteˢ (Perm.↭-sym p) ≈ˢ idˢ {map vlab ys}
    permuteˢ-inv-right p =
      ≈-trans
        (∘-resp (≈-sym (≡⇒≈ˢ (cong permuteˢ (↭-sym-involutive p)))) ≈-refl)
        (permuteˢ-inv-left (Perm.↭-sym p))

  ------------------------------------------------------------------------
  -- RESTRICTION along `map vlab` (F7).
  --
  -- Every decoder endpoint is `map vlab s` for a VERTEX stack `s : List V`,
  -- and `map` does not commute with `++` definitionally, so each `++` in a
  -- statement forces a `map-++` transport.  `HomV as bs = HomS (map vlab as)
  -- (map vlab bs)` is the SAME morphism type re-indexed by vertex stacks; its
  -- `_⊗ᵛ_`/`σᵛ` absorb that transport once, and then the whole presentation
  -- holds again with `List V` associators — whose singleton/cons instances
  -- REDUCE, so the decoder's own shapes become cast-free.
  --
  -- `HomV` is literally `HomS` precomposed with `map vlab`, and `_≈ᵛ_` IS
  -- `_≈ˢ_`, so the boundary back to the label level is the IDENTITY: no
  -- functor and no coherence lemmas are needed, and V-level and label-level
  -- statements interoperate definitionally.

  module Restrict (V : Set) (vlab : V → X) where

    open Perm′ V vlab using (permuteˢ; permuteˢ-frame; permuteˢ-frameˡ)

    open import Data.List.Relation.Binary.Permutation.Propositional.Properties
      using (++⁺ʳ; ++⁺ˡ)

    private
      m : List V → List X
      m = map vlab

    HomV : List V → List V → Set
    HomV as bs = HomS (m as) (m bs)

    infixr 9 _∘ᵛ_
    infixr 10 _⊗ᵛ_
    infix 4 _≈ᵛ_

    idᵛ : ∀ {as} → HomV as as
    idᵛ = idˢ

    _∘ᵛ_ : ∀ {as bs cs} → HomV bs cs → HomV as bs → HomV as cs
    g ∘ᵛ f = g ∘ˢ f

    _⊗ᵛ_ : ∀ {as bs us vs} → HomV as bs → HomV us vs → HomV (as ++ us) (bs ++ vs)
    _⊗ᵛ_ {as} {bs} {us} {vs} f g =
      castˢ (sym (map-++ vlab as us)) (sym (map-++ vlab bs vs)) (f ⊗ˢ g)

    σᵛ : ∀ as bs → HomV (as ++ bs) (bs ++ as)
    σᵛ as bs =
      castˢ (sym (map-++ vlab as bs)) (sym (map-++ vlab bs as))
        (σˢ (m as) (m bs))

    castᵛ : ∀ {as as' bs bs'} → as ≡ as' → bs ≡ bs' → HomV as bs → HomV as' bs'
    castᵛ = subst₂ HomV

    _≈ᵛ_ : ∀ {as bs} → HomV as bs → HomV as bs → Set
    f ≈ᵛ g = f ≈ˢ g

    -- the V-level permute already lands in `HomV` on the nose
    permuteᵛ : ∀ {as bs : List V} → as ↭ bs → HomV as bs
    permuteᵛ = permuteˢ

    ------------------------------------------------------------------------
    -- The cast/heterogeneous kit at V level.  `castᵛ` is the `List V`-indexed
    -- transport; it is a `castˢ` along `cong m`.

    castᵛ-cast
      : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') (t : HomV as bs)
      → castᵛ p q t ≡ castˢ (cong m p) (cong m q) t
    castᵛ-cast refl refl t = refl

    cast-respᵛ
      : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') {f g : HomV as bs}
      → f ≈ᵛ g → castᵛ p q f ≈ᵛ castᵛ p q g
    cast-respᵛ refl refl e = e

    cast-idᵛ : ∀ {as as'} (p q : as ≡ as') → castᵛ p q (idᵛ {as}) ≈ᵛ idᵛ {as'}
    cast-idᵛ p q =
      ≈-trans (≡⇒≈ˢ (castᵛ-cast p q idᵛ)) (cast-id (cong m p) (cong m q))

    cast-irrelᵛ
      : ∀ {as as' bs bs'} (p p' : as ≡ as') (q q' : bs ≡ bs') (t : HomV as bs)
      → castᵛ p q t ≡ castᵛ p' q' t
    cast-irrelᵛ p p' q q' t =
      trans (castᵛ-cast p q t)
        (trans (cast-irrel (cong m p) (cong m p') (cong m q) (cong m q') t)
               (sym (castᵛ-cast p' q' t)))

    cast-flipᵛ
      : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs')
          {f : HomV as bs} {g : HomV as' bs'}
      → castᵛ p q f ≈ᵛ g → f ≈ᵛ castᵛ (sym p) (sym q) g
    cast-flipᵛ refl refl e = e

    idᵛ-≈̂ : ∀ {as bs : List V} (p : as ≡ bs) → idᵛ {as} ≈̂ idᵛ {bs}
    idᵛ-≈̂ p = idˢ-≈̂ (cong m p)

    σᵛ-≈̂ : ∀ {as as' bs bs' : List V} (p : as ≡ as') (q : bs ≡ bs')
         → σᵛ as bs ≈̂ σᵛ as' bs'
    σᵛ-≈̂ refl refl = ≈̂-refl

    -- `_⊗ᵛ_`/`castᵛ` congruences for `≈̂` chains (the `⊗ᵛ`/`castᵛ` casts peel)
    ⊗-resp-≈̂ᵛ
      : ∀ {as bs us vs as' bs' us' vs'}
          {f : HomV as bs} {f' : HomV as' bs'}
          {g : HomV us vs} {g' : HomV us' vs'}
      → f ≈̂ f' → g ≈̂ g' → (f ⊗ᵛ g) ≈̂ (f' ⊗ᵛ g')
    ⊗-resp-≈̂ᵛ {as} {bs} {us} {vs} {as'} {bs'} {us'} {vs'} ef eg =
      ≈̂-trans (cast-≈̂ {p = sym (map-++ vlab as us)} {q = sym (map-++ vlab bs vs)})
      (≈̂-trans (⊗-resp-≈̂ ef eg)
               (≈̂-sym (cast-≈̂ {p = sym (map-++ vlab as' us')}
                              {q = sym (map-++ vlab bs' vs')})))

    castᵛ-≈̂
      : ∀ {as as' bs bs'} (p : as ≡ as') (q : bs ≡ bs') (t : HomV as bs)
      → castᵛ p q t ≈̂ t
    castᵛ-≈̂ p q t =
      ≈̂-trans (≈ˢ⇒≈̂ (≡⇒≈ˢ (castᵛ-cast p q t)))
              (cast-≈̂ {p = cong m p} {q = cong m q})

    ------------------------------------------------------------------------
    -- The presentation, re-proved at V level.  Category and `_≈ᵛ_` structure
    -- are INHERITED (`idᵛ`/`_∘ᵛ_`/`_≈ᵛ_` are the strict ones); only the
    -- monoidal/symmetry axioms pay the `map-++` bookkeeping, and they pay it
    -- here ONCE for the whole decoder cone.

    ⊗-respᵛ
      : ∀ {as bs us vs} {f f' : HomV as bs} {g g' : HomV us vs}
      → f ≈ᵛ f' → g ≈ᵛ g' → f ⊗ᵛ g ≈ᵛ f' ⊗ᵛ g'
    ⊗-respᵛ e e' = cast-resp _ _ (⊗-resp e e')

    ⊗-idᵛ : ∀ {as us} → idᵛ {as} ⊗ᵛ idᵛ {us} ≈ᵛ idᵛ {as ++ us}
    ⊗-idᵛ = ≈-trans (cast-resp _ _ ⊗-id) (cast-id _ _)

    interchangeᵛ
      : ∀ {as bs cs us vs ws}
          {f : HomV bs cs} {g : HomV vs ws} {f' : HomV as bs} {g' : HomV us vs}
      → (f ⊗ᵛ g) ∘ᵛ (f' ⊗ᵛ g') ≈ᵛ (f ∘ᵛ f') ⊗ᵛ (g ∘ᵛ g')
    interchangeᵛ {as} {bs} {cs} {us} {vs} {ws} =
      ≈̂⇒≈ˢ (≈̂-trans (∘-resp-≈̂ (cast-≈̂ {p = sym (map-++ vlab bs vs)}
                                       {q = sym (map-++ vlab cs ws)})
                               (cast-≈̂ {p = sym (map-++ vlab as us)}
                                       {q = sym (map-++ vlab bs vs)}))
            (≈̂-trans (≈ˢ⇒≈̂ interchangeˢ)
                     (≈̂-sym (cast-≈̂ {p = sym (map-++ vlab as us)}
                                    {q = sym (map-++ vlab cs ws)}))))

    ⊗-assocᵛ
      : ∀ {as bs us vs ps qs}
          (f : HomV as bs) (g : HomV us vs) (h : HomV ps qs)
      → castᵛ (++-assoc as us ps) (++-assoc bs vs qs) ((f ⊗ᵛ g) ⊗ᵛ h)
        ≈ᵛ f ⊗ᵛ (g ⊗ᵛ h)
    ⊗-assocᵛ {as} {bs} {us} {vs} {ps} {qs} f g h =
      ≈̂⇒≈ˢ
        (≈̂-trans lhs≈
        (≈̂-trans (≈̂-trans (≈̂-sym (cast-≈̂ {p = ++-assoc (m as) (m us) (m ps)}
                                          {q = ++-assoc (m bs) (m vs) (m qs)}))
                          (≈ˢ⇒≈̂ (⊗-assocˢ f g h)))
                 (≈̂-sym rhs≈)))
      where
        lhs≈ : castᵛ (++-assoc as us ps) (++-assoc bs vs qs) ((f ⊗ᵛ g) ⊗ᵛ h)
               ≈̂ ((f ⊗ˢ g) ⊗ˢ h)
        lhs≈ =
          ≈̂-trans (castᵛ-≈̂ (++-assoc as us ps) (++-assoc bs vs qs)
                    ((f ⊗ᵛ g) ⊗ᵛ h))
          (≈̂-trans (cast-≈̂ {p = sym (map-++ vlab (as ++ us) ps)}
                           {q = sym (map-++ vlab (bs ++ vs) qs)})
                   (⊗-resp-≈̂ (cast-≈̂ {p = sym (map-++ vlab as us)}
                                     {q = sym (map-++ vlab bs vs)}) ≈̂-refl))

        rhs≈ : f ⊗ᵛ (g ⊗ᵛ h) ≈̂ (f ⊗ˢ (g ⊗ˢ h))
        rhs≈ =
          ≈̂-trans (cast-≈̂ {p = sym (map-++ vlab as (us ++ ps))}
                          {q = sym (map-++ vlab bs (vs ++ qs))})
                  (⊗-resp-≈̂ ≈̂-refl
                     (cast-≈̂ {p = sym (map-++ vlab us ps)}
                             {q = sym (map-++ vlab vs qs)}))

    ⊗-unitʳᵛ
      : ∀ {as bs} (f : HomV as bs)
      → castᵛ (++-identityʳ as) (++-identityʳ bs) (f ⊗ᵛ idᵛ {[]}) ≈ᵛ f
    ⊗-unitʳᵛ {as} {bs} f =
      ≈̂⇒≈ˢ
        (≈̂-trans (castᵛ-≈̂ (++-identityʳ as) (++-identityʳ bs) (f ⊗ᵛ idᵛ {[]}))
        (≈̂-trans (cast-≈̂ {p = sym (map-++ vlab as [])}
                         {q = sym (map-++ vlab bs [])})
                 (≈̂-trans (≈̂-sym (cast-≈̂ {p = ++-identityʳ (m as)}
                                          {q = ++-identityʳ (m bs)}))
                          (≈ˢ⇒≈̂ (⊗-unitʳˢ f)))))

    σ-natᵛ
      : ∀ {as bs us vs} {f : HomV as bs} {g : HomV us vs}
      → σᵛ bs vs ∘ᵛ (f ⊗ᵛ g) ≈ᵛ (g ⊗ᵛ f) ∘ᵛ σᵛ as us
    σ-natᵛ {as} {bs} {us} {vs} =
      ≈̂⇒≈ˢ (≈̂-trans (∘-resp-≈̂ (cast-≈̂ {p = sym (map-++ vlab bs vs)}
                                       {q = sym (map-++ vlab vs bs)})
                               (cast-≈̂ {p = sym (map-++ vlab as us)}
                                       {q = sym (map-++ vlab bs vs)}))
            (≈̂-trans (≈ˢ⇒≈̂ σ-natˢ)
                     (≈̂-sym (∘-resp-≈̂ (cast-≈̂ {p = sym (map-++ vlab us as)}
                                              {q = sym (map-++ vlab vs bs)})
                                      (cast-≈̂ {p = sym (map-++ vlab as us)}
                                              {q = sym (map-++ vlab us as)})))))

    σ-σᵛ : ∀ {as bs} → σᵛ bs as ∘ᵛ σᵛ as bs ≈ᵛ idᵛ {as ++ bs}
    σ-σᵛ {as} {bs} =
      ≈̂⇒≈ˢ (≈̂-trans (∘-resp-≈̂ (cast-≈̂ {p = sym (map-++ vlab bs as)}
                                       {q = sym (map-++ vlab as bs)})
                               (cast-≈̂ {p = sym (map-++ vlab as bs)}
                                       {q = sym (map-++ vlab bs as)}))
            (≈̂-trans (≈ˢ⇒≈̂ σ-σˢ)
                     (≈̂-sym (idˢ-≈̂ (map-++ vlab as bs)))))

    σ-hexᵛ
      : ∀ as bs cs
      → σᵛ (as ++ bs) cs
        ≈ᵛ castᵛ (sym (++-assoc as bs cs)) (++-assoc cs as bs)
             ((σᵛ as cs ⊗ᵛ idᵛ {bs})
               ∘ᵛ castᵛ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs))
    σ-hexᵛ as bs cs =
      ≈̂⇒≈ˢ (≈̂-trans lhs≈ (≈̂-trans (σ-≈̂ (map-++ vlab as bs) refl)
                          (≈̂-trans hexC (≈̂-sym rhs≈))))
      where
        a = m as ; b = m bs ; c = m cs

        Cinner = castˢ refl (sym (++-assoc a c b)) (idˢ {a} ⊗ˢ σˢ b c)
        C = (σˢ a c ⊗ˢ idˢ {b}) ∘ˢ Cinner

        lhs≈ : σᵛ (as ++ bs) cs ≈̂ σˢ (m (as ++ bs)) c
        lhs≈ = cast-≈̂ {p = sym (map-++ vlab (as ++ bs) cs)}
                      {q = sym (map-++ vlab cs (as ++ bs))}

        hexC : σˢ (a ++ b) c ≈̂ C
        hexC = ≈̂-trans (≈ˢ⇒≈̂ (σ-hexˢ a b c))
                       (cast-≈̂ {p = sym (++-assoc a b c)} {q = ++-assoc c a b})

        leftC : (σᵛ as cs ⊗ᵛ idᵛ {bs}) ≈̂ (σˢ a c ⊗ˢ idˢ {b})
        leftC =
          ≈̂-trans (cast-≈̂ {p = sym (map-++ vlab (as ++ cs) bs)}
                          {q = sym (map-++ vlab (cs ++ as) bs)})
                  (⊗-resp-≈̂ (cast-≈̂ {p = sym (map-++ vlab as cs)}
                                    {q = sym (map-++ vlab cs as)}) ≈̂-refl)

        rightC : castᵛ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs)
                 ≈̂ Cinner
        rightC =
          ≈̂-trans
            (≈̂-trans (castᵛ-≈̂ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs))
            (≈̂-trans (cast-≈̂ {p = sym (map-++ vlab as (bs ++ cs))}
                             {q = sym (map-++ vlab as (cs ++ bs))})
                     (⊗-resp-≈̂ ≈̂-refl
                        (cast-≈̂ {p = sym (map-++ vlab bs cs)}
                                {q = sym (map-++ vlab cs bs)}))))
            (≈̂-sym (cast-≈̂ {p = refl} {q = sym (++-assoc a c b)}))

        rhs≈ : castᵛ (sym (++-assoc as bs cs)) (++-assoc cs as bs)
                 ((σᵛ as cs ⊗ᵛ idᵛ {bs})
                   ∘ᵛ castᵛ refl (sym (++-assoc as cs bs)) (idᵛ {as} ⊗ᵛ σᵛ bs cs))
               ≈̂ C
        rhs≈ =
          ≈̂-trans (castᵛ-≈̂ (sym (++-assoc as bs cs)) (++-assoc cs as bs) _)
                  (∘-resp-≈̂ leftC rightC)

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
    -- The derived V-level kit the decoder cone actually consumes.  Note that
    -- `++-assoc (a ∷ []) us vs` and `map-++ vlab (a ∷ as) R` REDUCE, so at the
    -- singleton/cons frames the decoder produces these are cast-FREE.

    ⊗id-distᵛ
      : ∀ {as bs cs R : List V} (f : HomV bs cs) (g : HomV as bs)
      → (f ∘ᵛ g) ⊗ᵛ idᵛ {R} ≈ᵛ (f ⊗ᵛ idᵛ {R}) ∘ᵛ (g ⊗ᵛ idᵛ {R})
    ⊗id-distᵛ f g = ≈-trans (⊗-respᵛ ≈-refl (≈-sym idˡ)) (≈-sym interchangeᵛ)

    -- left-frame mirror of `⊗id-distᵛ`
    id⊗-distᵛ
      : ∀ {as bs cs L : List V} (g : HomV bs cs) (f : HomV as bs)
      → idᵛ {L} ⊗ᵛ (g ∘ᵛ f) ≈ᵛ (idᵛ {L} ⊗ᵛ g) ∘ᵛ (idᵛ {L} ⊗ᵛ f)
    id⊗-distᵛ g f = ≈-trans (⊗-respᵛ (≈-sym idˡ) ≈-refl) (≈-sym interchangeᵛ)

    box-suffix-ᵛ
      : ∀ {as bs} (b : HomV as bs) (rest R : List V)
      → castᵛ (++-assoc as rest R) (++-assoc bs rest R)
          ((b ⊗ᵛ idᵛ {rest}) ⊗ᵛ idᵛ {R})
        ≈ᵛ b ⊗ᵛ idᵛ {rest ++ R}
    box-suffix-ᵛ b rest R =
      ≈-trans (⊗-assocᵛ b idᵛ idᵛ) (⊗-respᵛ ≈-refl ⊗-idᵛ)

    -- heterogeneous forms of the two re-bracketings every consumer needs
    -- (the `castᵛ` is peeled, so no endpoint path is ever named)
    ⊗-assoc-≈̂ᵛ
      : ∀ {as bs us vs ps qs}
          (f : HomV as bs) (g : HomV us vs) (h : HomV ps qs)
      → ((f ⊗ᵛ g) ⊗ᵛ h) ≈̂ (f ⊗ᵛ (g ⊗ᵛ h))
    ⊗-assoc-≈̂ᵛ {as} {bs} {us} {vs} {ps} {qs} f g h =
      ≈̂-trans (≈̂-sym (castᵛ-≈̂ (++-assoc as us ps) (++-assoc bs vs qs)
                        ((f ⊗ᵛ g) ⊗ᵛ h)))
              (≈ˢ⇒≈̂ (⊗-assocᵛ f g h))

    box-suffix-≈̂ᵛ
      : ∀ {as bs} (b : HomV as bs) (rest R : List V)
      → ((b ⊗ᵛ idᵛ {rest}) ⊗ᵛ idᵛ {R}) ≈̂ (b ⊗ᵛ idᵛ {rest ++ R})
    box-suffix-≈̂ᵛ {as} {bs} b rest R =
      ≈̂-trans (≈̂-sym (castᵛ-≈̂ (++-assoc as rest R) (++-assoc bs rest R)
                        ((b ⊗ᵛ idᵛ {rest}) ⊗ᵛ idᵛ {R})))
              (≈ˢ⇒≈̂ (box-suffix-ᵛ b rest R))

    box-commute-ᵛ
      : ∀ {as bs cs ds} (b : HomV as bs) (b' : HomV cs ds)
      → (b ⊗ᵛ idᵛ {ds}) ∘ᵛ (idᵛ {as} ⊗ᵛ b')
        ≈ᵛ (idᵛ {bs} ⊗ᵛ b') ∘ᵛ (b ⊗ᵛ idᵛ {cs})
    box-commute-ᵛ b b' =
      ≈-trans interchangeᵛ
        (≈-trans (⊗-respᵛ idʳ idˡ)
          (≈-sym (≈-trans interchangeᵛ (⊗-respᵛ idˡ idʳ))))

    -- the residual frame, CAST-FREE at V level (contrast `permuteˢ-frame`)
    permuteᵛ-frame
      : ∀ {as bs : List V} (R : List V) (p : as ↭ bs)
      → permuteᵛ (++⁺ʳ R p) ≈ᵛ permuteᵛ p ⊗ᵛ idᵛ {R}
    permuteᵛ-frame {as} {bs} R p =
      cast-flip (map-++ vlab as R) (map-++ vlab bs R) (permuteˢ-frame R p)

    -- its LEFT mirror
    permuteᵛ-frameˡ
      : ∀ (L : List V) {as bs : List V} (p : as ↭ bs)
      → permuteᵛ (++⁺ˡ L p) ≈ᵛ idᵛ {L} ⊗ᵛ permuteᵛ p
    permuteᵛ-frameˡ L {as} {bs} p =
      cast-flip (map-++ vlab L as) (map-++ vlab L bs) (permuteˢ-frameˡ L p)

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

  private
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
