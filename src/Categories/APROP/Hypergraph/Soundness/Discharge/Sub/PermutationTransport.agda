{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic permutation-transport plumbing, shared by `Sub/BlockNFBraid.agda`,
-- `Sub/FireMidEquivariant.agda` and `Sub/StackEquivariance.agda`.
--
-- Two layers:
--
--   * Top level — fully generic (`Set`-polymorphic) `subst₂ _↭_` /
--     `map⁺`-commutation algebra: pushing the permutation constructors
--     (`prep`/`swap`/`trans`) through endpoint `subst₂`s, and commuting
--     `map⁺ f` with the smart combinators (`↭-trans`, `↭-sym`, `↭-reflexive`,
--     `shift`, `++⁺ʳ`, `++-comm`) modulo the `map-++` endpoint rewrites.
--     The two lemmas that need proof-irrelevant endpoint paths
--     (`subst₂-↭-irr`, `map⁺-++-comm`) take the UIP witness as an argument
--     (derivable via Hedberg from decidable equality, `--without-K`-safe).
--
--   * `module Monoidal (d : FreeMonoidalData)` — the `HomTerm`/iso transport
--     combinators (`to-subst₂-≅`/`from-subst₂-≅`, `subst₂-resp-≈`,
--     `subst₂-∘-split`) and the shared `frame-transport` body of the
--     `frame-ext`/`σ-block-comm`-style framing lemmas.  Re-exported `public`
--     by `BlockNFBraid`, so consumers keep their `BNB.*` spellings.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Soundness.Discharge.Sub.PermutationTransport
  where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst₂)
open import Relation.Binary.PropositionalEquality.Properties using (sym-cong)

--------------------------------------------------------------------------------
-- Generic `subst₂ _↭_` plumbing: push a permutation constructor through the
-- two endpoint substs.

prep-subst₂
  : ∀ {B : Set} (b : B) {us us' vs vs' : List B} (p : us ≡ us') (q : vs ≡ vs')
      (r : us Perm.↭ vs)
  → Perm.prep b (subst₂ Perm._↭_ p q r)
    ≡ subst₂ Perm._↭_ (cong (b ∷_) p) (cong (b ∷_) q) (Perm.prep b r)
prep-subst₂ b refl refl r = refl

swap-subst₂
  : ∀ {B : Set} (a b : B) {us us' vs vs' : List B} (p : us ≡ us') (q : vs ≡ vs')
      (r : us Perm.↭ vs)
  → Perm.swap a b (subst₂ Perm._↭_ p q r)
    ≡ subst₂ Perm._↭_ (cong (a ∷_) (cong (b ∷_) p)) (cong (b ∷_) (cong (a ∷_) q))
        (Perm.swap a b r)
swap-subst₂ a b refl refl r = refl

trans-subst₂
  : ∀ {B : Set} {us us' vs vs' ws ws' : List B}
      (p : us ≡ us') (q : vs ≡ vs') (r : ws ≡ ws')
      (s₁ : us Perm.↭ vs) (s₂ : vs Perm.↭ ws)
  → Perm.trans (subst₂ Perm._↭_ p q s₁) (subst₂ Perm._↭_ q r s₂)
    ≡ subst₂ Perm._↭_ p r (Perm.trans s₁ s₂)
trans-subst₂ refl refl refl s₁ s₂ = refl

sym-cons₂
  : ∀ {B : Set} (a b : B) {us vs : List B} (p : us ≡ vs)
  → cong (a ∷_) (cong (b ∷_) (sym p))
    ≡ sym (cong (a ∷_) (cong (b ∷_) p))
sym-cons₂ a b refl = refl

subst₂-↭-refl
  : ∀ {B : Set} {us vs : List B} (p : us ≡ vs)
  → subst₂ Perm._↭_ p p (Perm.refl {xs = us}) ≡ Perm.refl {xs = vs}
subst₂-↭-refl refl = refl

-- Any two proofs of the same endpoint equalities are interchangeable,
-- given a UIP witness on `List B` (Hedberg from `DecidableEquality B`
-- at the call sites, `--without-K`-safe).
subst₂-↭-irr
  : ∀ {B : Set} (uipB : ∀ {us vs : List B} (p q : us ≡ vs) → p ≡ q)
      {us us' vs vs' : List B}
      (p p' : us ≡ us') (q q' : vs ≡ vs') (r : us Perm.↭ vs)
  → subst₂ Perm._↭_ p q r ≡ subst₂ Perm._↭_ p' q' r
subst₂-↭-irr uipB p p' q q' r =
  cong₂ (λ a b → subst₂ Perm._↭_ a b r) (uipB p p') (uipB q q')

↭-sym-subst₂
  : ∀ {B : Set} {us us' vs vs' : List B}
      (p : us ≡ us') (q : vs ≡ vs') (r : us Perm.↭ vs)
  → Perm.↭-sym (subst₂ Perm._↭_ p q r) ≡ subst₂ Perm._↭_ q p (Perm.↭-sym r)
↭-sym-subst₂ refl refl r = refl

subst₂-↭-reflexive
  : ∀ {B : Set} {us us' vs vs' : List B} (p : us ≡ us') (q : vs ≡ vs') (e : us ≡ vs)
  → subst₂ Perm._↭_ p q (Perm.↭-reflexive e)
    ≡ Perm.↭-reflexive (trans (sym p) (trans e q))
subst₂-↭-reflexive refl refl refl = refl

map⁺-↭-trans
  : ∀ {A B : Set} (f : A → B) {xs ys zs : List A}
      (a : xs Perm.↭ ys) (b : ys Perm.↭ zs)
  → PermProp.map⁺ f (Perm.↭-trans a b)
    ≡ Perm.↭-trans (PermProp.map⁺ f a) (PermProp.map⁺ f b)
map⁺-↭-trans f Perm.refl          b              = refl
map⁺-↭-trans f (Perm.prep x a)    Perm.refl       = refl
map⁺-↭-trans f (Perm.swap x y a)  Perm.refl       = refl
map⁺-↭-trans f (Perm.trans a a')  Perm.refl       = refl
map⁺-↭-trans f (Perm.prep x a)    (Perm.prep y b) = refl
map⁺-↭-trans f (Perm.prep x a)    (Perm.swap y z b) = refl
map⁺-↭-trans f (Perm.prep x a)    (Perm.trans b b') = refl
map⁺-↭-trans f (Perm.swap x y a)  (Perm.prep z b) = refl
map⁺-↭-trans f (Perm.swap x y a)  (Perm.swap z w b) = refl
map⁺-↭-trans f (Perm.swap x y a)  (Perm.trans b b') = refl
map⁺-↭-trans f (Perm.trans a a')  (Perm.prep z b) = refl
map⁺-↭-trans f (Perm.trans a a')  (Perm.swap z w b) = refl
map⁺-↭-trans f (Perm.trans a a')  (Perm.trans b b') = refl

↭-trans-subst₂
  : ∀ {B : Set} {us us' vs vs' ws ws' : List B}
      (p : us ≡ us') (q : vs ≡ vs') (r : ws ≡ ws')
      (s₁ : us Perm.↭ vs) (s₂ : vs Perm.↭ ws)
  → Perm.↭-trans (subst₂ Perm._↭_ p q s₁) (subst₂ Perm._↭_ q r s₂)
    ≡ subst₂ Perm._↭_ p r (Perm.↭-trans s₁ s₂)
↭-trans-subst₂ refl refl refl s₁ s₂ = refl

map⁺-↭-sym
  : ∀ {A B : Set} (f : A → B) {xs ys : List A} (ρ : xs Perm.↭ ys)
  → PermProp.map⁺ f (Perm.↭-sym ρ) ≡ Perm.↭-sym (PermProp.map⁺ f ρ)
map⁺-↭-sym f Perm.refl          = refl
map⁺-↭-sym f (Perm.prep x ρ)    = cong (Perm.prep _) (map⁺-↭-sym f ρ)
map⁺-↭-sym f (Perm.swap x y ρ)  = cong (Perm.swap _ _) (map⁺-↭-sym f ρ)
map⁺-↭-sym f (Perm.trans p q)   =
  cong₂ Perm.trans (map⁺-↭-sym f q) (map⁺-↭-sym f p)

map⁺-↭-reflexive
  : ∀ {A B : Set} (f : A → B) {xs ys : List A} (eq : xs ≡ ys)
  → PermProp.map⁺ f (Perm.↭-reflexive eq) ≡ Perm.↭-reflexive (cong (map f) eq)
map⁺-↭-reflexive f refl = refl

map⁺-shift
  : ∀ {A B : Set} (f : A → B) (v : A) (xs ys : List A)
  → PermProp.map⁺ f (PermProp.shift v xs ys)
    ≡ subst₂ Perm._↭_
        (sym (map-++ f xs (v ∷ ys)))
        (cong (f v ∷_) (sym (map-++ f xs ys)))
        (PermProp.shift (f v) (map f xs) (map f ys))
map⁺-shift f v []        ys = refl
map⁺-shift f v (w ∷ xs') ys =
  -- LHS = trans (prep (f w) (map⁺ f (shift v xs' ys))) (swap (f w) (f v) refl)
  trans
    (cong (λ r → Perm.trans r (Perm.swap (f w) (f v) Perm.refl))
      (trans (cong (Perm.prep (f w)) (map⁺-shift f v xs' ys))
             (prep-subst₂ (f w)
                (sym (map-++ f xs' (v ∷ ys)))
                (cong (f v ∷_) (sym (map-++ f xs' ys)))
                (PermProp.shift (f v) (map f xs') (map f ys)))))
    (trans
      (trans
        (cong (Perm.trans
                (subst₂ Perm._↭_ p-dom mid
                   (Perm.prep (f w) (PermProp.shift (f v) (map f xs') (map f ys)))))
          swap-as-subst₂)
        (trans-subst₂ p-dom mid r-cod
          (Perm.prep (f w) (PermProp.shift (f v) (map f xs') (map f ys)))
          (Perm.swap (f w) (f v) Perm.refl)))
      (cong₂ (λ p q → subst₂ Perm._↭_ p q
                (PermProp.shift (f v) (f w ∷ map f xs') (map f ys)))
        (sym (sym-cong (map-++ f xs' (v ∷ ys))))
        (cong (cong (f v ∷_)) (sym (sym-cong (map-++ f xs' ys))))))
  where
    p₀ = sym (map-++ f xs' ys)
    p-dom = cong (f w ∷_) (sym (map-++ f xs' (v ∷ ys)))
    mid   = cong (f w ∷_) (cong (f v ∷_) p₀)
    r-cod = cong (f v ∷_) (cong (f w ∷_) p₀)

    swap-as-subst₂
      : Perm.swap (f w) (f v) Perm.refl
        ≡ subst₂ Perm._↭_ mid r-cod (Perm.swap (f w) (f v) Perm.refl)
    swap-as-subst₂ =
      trans (cong (Perm.swap (f w) (f v)) (sym (subst₂-↭-refl p₀)))
            (swap-subst₂ (f w) (f v) p₀ p₀ Perm.refl)

--------------------------------------------------------------------------------
-- `map⁺ f` commutes with `++⁺ʳ` / `++-comm` (modulo the `map-++` substs).

module _ {S T : Set} (f : S → T) where

  map⁺-++⁺ʳ
    : ∀ (cs : List S) {es fs : List S} (P : es Perm.↭ fs)
    → PermProp.map⁺ f (PermProp.++⁺ʳ cs P)
      ≡ subst₂ Perm._↭_ (sym (map-++ f es cs)) (sym (map-++ f fs cs))
          (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f P))
  map⁺-++⁺ʳ cs {es} Perm.refl =
    sym (subst₂-↭-refl (sym (map-++ f es cs)))
  map⁺-++⁺ʳ cs {x ∷ es} {x ∷ fs} (Perm.prep .x P) =
    trans (cong (Perm.prep _) (map⁺-++⁺ʳ cs P))
    (trans (prep-subst₂ (f x) (sym (map-++ f es cs)) (sym (map-++ f fs cs))
             (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f P)))
           (cong₂ (λ p q → subst₂ Perm._↭_ p q
                     (Perm.prep (f x)
                       (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f P))))
                  (sym (sym-cong (map-++ f es cs)))
                  (sym (sym-cong (map-++ f fs cs)))))
  map⁺-++⁺ʳ cs {x ∷ y ∷ es} {y ∷ x ∷ fs} (Perm.swap .x .y P) =
    trans (cong (Perm.swap _ _) (map⁺-++⁺ʳ cs P))
    (trans (swap-subst₂ (f x) (f y)
             (sym (map-++ f es cs)) (sym (map-++ f fs cs))
             (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f P)))
           (cong₂ (λ p q → subst₂ Perm._↭_ p q
                     (Perm.swap (f x) (f y)
                       (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f P))))
                  (sym-cons₂ (f x) (f y) (map-++ f es cs))
                  (sym-cons₂ (f y) (f x) (map-++ f fs cs))))
  map⁺-++⁺ʳ cs {es} {fs} (Perm.trans {ys = gs} P Q) =
    trans (cong₂ Perm.trans (map⁺-++⁺ʳ cs P) (map⁺-++⁺ʳ cs Q))
          (trans-subst₂ (sym (map-++ f es cs)) (sym (map-++ f gs cs))
             (sym (map-++ f fs cs))
             (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f P))
             (PermProp.++⁺ʳ (map f cs) (PermProp.map⁺ f Q)))

module _ {S T : Set} (f : S → T)
         (uipT : ∀ {us vs : List T} (p q : us ≡ vs) → p ≡ q) where

  map⁺-++-comm
    : ∀ (es fs : List S)
    → PermProp.map⁺ f (PermProp.++-comm es fs)
      ≡ subst₂ Perm._↭_ (sym (map-++ f es fs)) (sym (map-++ f fs es))
          (PermProp.++-comm (map f es) (map f fs))
  map⁺-++-comm [] fs =
    -- ++-comm [] fs = ↭-sym (++-identityʳ fs)  (definitionally)
    trans (map⁺-↭-sym f (PermProp.++-identityʳ fs))
    (trans (cong Perm.↭-sym (map⁺-↭-reflexive f (++-id fs)))
    (trans (cong (λ z → Perm.↭-sym (Perm.↭-reflexive z))
              (uipT (cong (map f) (++-id fs))
                   (trans (sym (sym (map-++ f fs [])))
                          (trans (++-id (map f fs)) (sym (map-++ f [] fs))))))
    (trans (cong Perm.↭-sym
              (sym (subst₂-↭-reflexive (sym (map-++ f fs []))
                      (sym (map-++ f [] fs)) (++-id (map f fs)))))
           (↭-sym-subst₂ (sym (map-++ f fs [])) (sym (map-++ f [] fs))
                   (Perm.↭-reflexive (++-id (map f fs)))))))
    where
      open import Data.List.Properties using () renaming (++-identityʳ to ++-id)
  map⁺-++-comm (x ∷ es') fs =
    -- ++-comm (x∷es') fs = ↭-trans A (↭-trans B refl)  (definitionally)
    trans (map⁺-↭-trans f A (Perm.↭-trans B Perm.refl))
    (trans (cong (Perm.↭-trans (PermProp.map⁺ f A))
              (map⁺-↭-trans f B Perm.refl))
    (trans (cong₂ (λ a b → Perm.↭-trans a (Perm.↭-trans b (PermProp.map⁺ f Perm.refl)))
             -- prep part (IH pushed through prep)
             (trans (cong (Perm.prep (f x)) (map⁺-++-comm es' fs))
                    (prep-subst₂ (f x) pA-dom qMid
                       (PermProp.++-comm (map f es') (map f fs))))
             -- shift part
             shift-part)
    (trans (cong (λ z → Perm.↭-trans (subst₂ Perm._↭_ pA pMid A')
                          (Perm.↭-trans (subst₂ Perm._↭_ pMid qB B') z))
             (sym (subst₂-↭-refl qB)))
    (trans (cong (Perm.↭-trans (subst₂ Perm._↭_ pA pMid A'))
              (↭-trans-subst₂ pMid qB qB B' Perm.refl))
    (trans (↭-trans-subst₂ pA pMid qB A' (Perm.↭-trans B' Perm.refl))
           (subst₂-↭-irr uipT pA (sym (map-++ f (x ∷ es') fs)) qB qB
             (PermProp.++-comm (f x ∷ map f es') (map f fs))))))))
    where
      A = Perm.prep x (PermProp.++-comm es' fs)
      B = Perm.↭-sym (PermProp.shift x fs es')
      pA-dom = sym (map-++ f es' fs)
      qMid   = sym (map-++ f fs es')
      pA   = cong (f x ∷_) pA-dom
      pMid = cong (f x ∷_) qMid
      qB   = sym (map-++ f fs (x ∷ es'))
      A'   = Perm.prep (f x) (PermProp.++-comm (map f es') (map f fs))
      B'   = Perm.↭-sym (PermProp.shift (f x) (map f fs) (map f es'))
      shift-part
        : PermProp.map⁺ f (Perm.↭-sym (PermProp.shift x fs es'))
          ≡ subst₂ Perm._↭_
              (cong (f x ∷_) (sym (map-++ f fs es')))
              (sym (map-++ f fs (x ∷ es')))
              (Perm.↭-sym (PermProp.shift (f x) (map f fs) (map f es')))
      shift-part =
        trans (map⁺-↭-sym f (PermProp.shift x fs es'))
        (trans (cong Perm.↭-sym (map⁺-shift f x fs es'))
        (trans (↭-sym-subst₂ (sym (map-++ f fs (x ∷ es')))
                  (cong (f x ∷_) (sym (map-++ f fs es')))
                  (PermProp.shift (f x) (map f fs) (map f es')))
               refl))

--------------------------------------------------------------------------------
-- `HomTerm`/iso transport over a free monoidal signature.

open import Categories.FreeMonoidal
open import Categories.Category using (Category)

module Monoidal (d : FreeMonoidalData) where

  open FreeMonoidal d
  open import Categories.Morphism FreeMonoidal using (_≅_)

  private
    module FM = Category FreeMonoidal

  open FM.HomReasoning

  to-subst₂-≅
    : ∀ {A A' B : ObjTerm} (p : A ≡ A') (i : A ≅ B)
    → _≅_.to (subst₂ _≅_ p refl i) ≡ subst₂ HomTerm refl p (_≅_.to i)
  to-subst₂-≅ refl i = refl

  from-subst₂-≅
    : ∀ {A A' B : ObjTerm} (p : A ≡ A') (i : A ≅ B)
    → _≅_.from (subst₂ _≅_ p refl i) ≡ subst₂ HomTerm p refl (_≅_.from i)
  from-subst₂-≅ refl i = refl

  subst₂-resp-≈
    : ∀ {A A' B B' : ObjTerm} (p : A ≡ A') (q : B ≡ B') {u v : HomTerm A B}
    → u ≈Term v
    → subst₂ HomTerm p q u ≈Term subst₂ HomTerm p q v
  subst₂-resp-≈ refl refl h = h

  subst₂-∘-split
    : ∀ {A A' B C C' : ObjTerm} (p : A ≡ A') (r : C ≡ C')
        (f : HomTerm B C) (g : HomTerm A B)
    → subst₂ HomTerm p r (f ∘ g)
      ≡ subst₂ HomTerm refl r f ∘ subst₂ HomTerm p refl g
  subst₂-∘-split refl refl f g = refl

  -- Generic "transport a raw `to ∘ (mid ∘ from)` framing through the two
  -- endpoint `subst₂`s".  This is the shared body of `frame-ext`/
  -- `σ-block-comm` (and the `pvv-++⁺ˡ-slide` left slide): both split the
  -- boundary `subst₂` over the two interior objects, turn the outer raw isos
  -- into framed `to`/`from`, and leave the middle morphism (re)framed.
  -- Parameterised by the raw MID and the three reframing equalities
  -- (`to-eq`, `mid-eq`, `from-eq`).
  frame-transport
    : ∀ {A A' B B' M N : ObjTerm}
        (pDom : A ≡ A') (pCod : B ≡ B')
        (rawTO : HomTerm M B) (rawMID : HomTerm N M) (rawFROM : HomTerm A N)
        {TO : HomTerm M B'} {FRAMED : HomTerm N M} {FROM : HomTerm A' N}
    → subst₂ HomTerm refl pCod rawTO ≡ TO
    → rawMID ≡ FRAMED
    → subst₂ HomTerm pDom refl rawFROM ≡ FROM
    → subst₂ HomTerm pDom pCod (rawTO ∘ (rawMID ∘ rawFROM))
      ≈Term TO ∘ (FRAMED ∘ FROM)
  frame-transport pDom pCod rawTO rawMID rawFROM to-eq mid-eq from-eq = begin
      subst₂ HomTerm pDom pCod (rawTO ∘ (rawMID ∘ rawFROM))
        ≈⟨ ≡⇒≈Term (subst₂-∘-split pDom pCod rawTO (rawMID ∘ rawFROM)) ⟩
      subst₂ HomTerm refl pCod rawTO ∘ subst₂ HomTerm pDom refl (rawMID ∘ rawFROM)
        ≈⟨ ∘-resp-≈ (≡⇒≈Term to-eq)
             (≈-Term-trans (≡⇒≈Term (subst₂-∘-split pDom refl rawMID rawFROM))
               (∘-resp-≈ (≡⇒≈Term mid-eq) (≡⇒≈Term from-eq))) ⟩
      _ ∘ (_ ∘ _) ∎
