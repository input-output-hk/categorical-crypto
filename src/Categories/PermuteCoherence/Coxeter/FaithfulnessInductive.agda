{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- An INDUCTIVE variant of `≅↭`, and the combinatorial completeness of it.
--
-- `≅↭` (Canonical.agda) is the *semantic* relation "equal evaluated
-- bijection" (`eval-↭ p ≈-fb eval-↭ q`).  This module introduces an
-- INDUCTIVELY GENERATED congruence `_≅↭ⁱ_` on `↭`-derivations whose
-- generators are exactly the relations of the free symmetric-monoidal
-- structure (groupoid laws, bifunctoriality, σ-naturality, σ²=id,
-- and the braid).
--
-- Architecture:
--
--   * `complete : eval-↭ p ≈-fb eval-↭ q → p ≅↭ⁱ q`
--       a purely COMBINATORIAL statement about `↭`-derivations (no terms,
--       no `subst`): the Coxeter / word-problem core.
--
-- Minimised constructor set: `swap`-congruence is derivable from `swap-nat`
-- + `prep`-congruence; far-commutativity is derived (`far-nat`) rather than
-- taken as a generator.
------------------------------------------------------------------------

open import Relation.Binary using (DecidableEquality)

module Categories.PermuteCoherence.Coxeter.FaithfulnessInductive
  (X : Set)
  (_≟X_ : DecidableEquality X) where

open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.Nat.Base using (ℕ; suc; pred)
open import Data.Nat.Properties using (suc-injective)
open import Data.Nat.Properties using () renaming (≡-irrelevant to ℕ-≡-irrelevant)
open import Data.Fin.Base using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns using (0F)
import Data.Fin.Permutation as P
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Binary.PropositionalEquality using (subst₂)
open import Data.List.Properties using () renaming (≡-dec to List-≡-dec)
import Axiom.UniquenessOfIdentityProofs as UIPmod
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (↭-length)
open import Data.Product using (_,_; proj₁; proj₂; Σ-syntax)

open import Categories.PermuteCoherence.FinBij
  using (FinBij; _≈-fb_; cons-fb; swap-fb; id-fb; _∘-fb_)
open import Categories.PermuteCoherence.Eval using (eval-↭)
open import Categories.PermuteCoherence.Coxeter.EvalSoundness
  using ( cons-fb-functor-id; cons²-fb-id; cons-fb-functor-comp
        ; swap-fb-involutive; swap-fb-natural; yang-baxter )
-- The Word model (position level) and its list-level interpretation.
open import Categories.PermuteCoherence.Coxeter.Word
  using ( Word; liftW; _~ʷ_; ~refl; ~sym; ~trans; ∷c; c1; c2; c3
        ; Far; far0ˡ; far0ʳ; farS; Adj; adj0; adjS
        ; evalW; canonW-resp-≈
        ; cons-fb-cong )
open import Categories.PermuteCoherence.Coxeter.InsertProof using (straightenW)
open import Categories.PermuteCoherence.Coxeter.WordInterp {X = X}
  using ( swapAt; swapAt-↭; applyW; applyW-length; ⟦_⟧↭
        ; cast-push; eval-respect)
private
  variable
    x y z a b c e : X
    xs ys zs ws : List X
    xs′ ys′ zs′ : List X

-- Hedberg UIP on `List X`, from decidable equality on the atom type `X`.
-- Used to discharge constrained `List X` endpoint equalities in the
-- heterogeneous wrapper without `--with-K`.
uipX : ∀ {us vs : List X} (p q : us ≡ vs) → p ≡ q
uipX = UIPmod.Decidable⇒UIP.≡-irrelevant (List-≡-dec _≟X_)

------------------------------------------------------------------------
-- 1. The inductive congruence `_≅↭ⁱ_`.

infix 4 _≅↭ⁱ_

data _≅↭ⁱ_ : {xs ys : List X} → xs ↭ ys → xs ↭ ys → Set where

  -- equivalence
  iref : {p : xs ↭ ys} → p ≅↭ⁱ p
  isym : {p q : xs ↭ ys} → p ≅↭ⁱ q → q ≅↭ⁱ p
  itrn : {p q r : xs ↭ ys} → p ≅↭ⁱ q → q ≅↭ⁱ r → p ≅↭ⁱ r

  -- congruence (prep + trans; swap-congruence is derivable)
  prepc : {p q : xs ↭ ys} → p ≅↭ⁱ q → Perm.prep x p ≅↭ⁱ Perm.prep x q
  trc   : {p p′ : xs ↭ ys} {q q′ : ys ↭ zs}
        → p ≅↭ⁱ p′ → q ≅↭ⁱ q′ → Perm.trans p q ≅↭ⁱ Perm.trans p′ q′

  -- groupoid (trans) laws
  tr-unitˡ : {p : xs ↭ ys} → Perm.trans (Perm.refl {xs = xs}) p ≅↭ⁱ p
  tr-unitʳ : {p : xs ↭ ys} → Perm.trans p (Perm.refl {xs = ys}) ≅↭ⁱ p
  tr-assoc : {p : xs ↭ ys} {q : ys ↭ zs} {r : zs ↭ ws}
           → Perm.trans (Perm.trans p q) r ≅↭ⁱ Perm.trans p (Perm.trans q r)

  -- bifunctoriality of `prep`
  prep-id : Perm.prep x (Perm.refl {xs = xs}) ≅↭ⁱ Perm.refl {xs = x ∷ xs}
  prep-tr : {p : xs ↭ ys} {q : ys ↭ zs}
          → Perm.prep x (Perm.trans p q) ≅↭ⁱ Perm.trans (Perm.prep x p) (Perm.prep x q)

  -- σ-naturality: a swap with inner `p` factors as (prep-tower) ∘ (bare swap)
  swap-nat : {p : xs ↭ ys}
           → Perm.swap x y p
             ≅↭ⁱ
             Perm.trans (Perm.prep x (Perm.prep y p)) (Perm.swap x y (Perm.refl {xs = ys}))

  -- σ-naturality, LEFT form: the OTHER naturality square of σ.  Needed to
  -- derive far-commutativity (`far-nat`).
  swap-nat-left : {p : xs ↭ ys}
                → Perm.swap x y p
                  ≅↭ⁱ
                  Perm.trans (Perm.swap x y (Perm.refl {xs = xs})) (Perm.prep y (Perm.prep x p))

  -- σ² = id: a bare swap followed by its reverse is the identity
  swap-invol : Perm.trans (Perm.swap x y (Perm.refl {xs = xs}))
                          (Perm.swap y x (Perm.refl {xs = xs}))
               ≅↭ⁱ Perm.refl {xs = x ∷ y ∷ xs}

  -- the braid (Yang-Baxter): reversing three front elements, two ways
  swap-braid : Perm.trans (Perm.swap x y (Perm.refl {xs = z ∷ xs}))
                          (Perm.trans (Perm.prep y (Perm.swap x z (Perm.refl {xs = xs})))
                                      (Perm.swap y z (Perm.refl {xs = x ∷ xs})))
               ≅↭ⁱ
               Perm.trans (Perm.prep x (Perm.swap y z (Perm.refl {xs = xs})))
                          (Perm.trans (Perm.swap x z (Perm.refl {xs = y ∷ xs}))
                                      (Perm.prep z (Perm.swap x y (Perm.refl {xs = xs}))))

------------------------------------------------------------------------
-- 2. `_≅↭ⁱ_` vs the semantic `≅↭` (= equal evaluated bijection).
--
-- `sound` is the EASY direction (each generator preserves `eval-↭`), by
-- induction with one `FinBij`-level coherence per generator.  `complete`
-- (below) is the COMBINATORIAL core.  Together they give `_≅↭ⁱ_ ⟺ _≅↭_`.

private
  sw∘c≈sw : ∀ {n} → swap-fb n ∘-fb cons-fb (cons-fb (id-fb {n})) ≈-fb swap-fb n
  sw∘c≈sw {n} i = cong (swap-fb n P.⟨$⟩ʳ_) (cons²-fb-id {n} i)

sound : {p q : xs ↭ ys} → p ≅↭ⁱ q → eval-↭ p ≈-fb eval-↭ q
sound iref          = λ i → refl
sound (isym h)      = λ i → sym (sound h i)
sound (itrn h₁ h₂)  = λ i → trans (sound h₁ i) (sound h₂ i)
sound (prepc h)     = cons-fb-cong (sound h)
sound (trc {p = p} {p′ = p′} {q = q} {q′ = q′} h₁ h₂) =
  λ i → trans (cong (eval-↭ q P.⟨$⟩ʳ_) (sound h₁ i))
              (sound h₂ (eval-↭ p′ P.⟨$⟩ʳ i))
sound tr-unitˡ      = λ i → refl
sound tr-unitʳ      = λ i → refl
sound tr-assoc      = λ i → refl
sound prep-id       = cons-fb-functor-id
sound (prep-tr {p = p} {q = q}) =
  cons-fb-functor-comp (eval-↭ q) (eval-↭ p)
sound (swap-nat {p = p}) =
  λ i → cong (swap-fb _ P.⟨$⟩ʳ_)
             (sym (cons²-fb-id (cons-fb (cons-fb (eval-↭ p)) P.⟨$⟩ʳ i)))
sound (swap-nat-left {p = p}) =
  λ i → trans (swap-fb-natural (eval-↭ p) i)
              (cong (cons-fb (cons-fb (eval-↭ p)) P.⟨$⟩ʳ_)
                    (cong (swap-fb _ P.⟨$⟩ʳ_) (sym (cons²-fb-id i))))
sound (swap-invol {xs = xs}) i =
  trans (cong (swap-fb (length xs) P.⟨$⟩ʳ_)
              (trans (cons²-fb-id (swap-fb (length xs)
                        P.⟨$⟩ʳ (cons-fb (cons-fb (id-fb {length xs})) P.⟨$⟩ʳ i)))
                     (cong (swap-fb (length xs) P.⟨$⟩ʳ_) (cons²-fb-id i))))
        (swap-fb-involutive {length xs} i)
-- `swap-braid` is proved POINTWISE (at a fixed index `i`): `≈-fb` only
-- constrains the FORWARD map, so a combinator-style proof would leave
-- `.from`/`.to-cong`/`.inverse` fields of intermediate records as unsolvable
-- metas.  Applying at `i` reduces to `_⟨$⟩ʳ_` and avoids that.
sound (swap-braid {xs = xs}) i =
  trans lhsCollapse (trans (yang-baxter {L} i) (sym rhsCollapse))
  where
  L  = length xs
  Sx = swap-fb (suc L)                              -- the two outer transpositions
  cs = cons-fb (swap-fb L)                          -- the lifted inner transposition
  c2s = cons-fb (cons-fb (id-fb {suc L}))           -- collapsible `cons²(id)`
  D  = cons-fb (swap-fb L ∘-fb cons-fb (cons-fb (id-fb {L})))
  ccx : ∀ k → c2s P.⟨$⟩ʳ k ≡ k
  ccx = cons²-fb-id {suc L}
  collM : ∀ k → D P.⟨$⟩ʳ k ≡ cs P.⟨$⟩ʳ k            -- inner lift collapses
  collM = cons-fb-cong (sw∘c≈sw {L})
  -- LHS at `i` reduces to YB-LHS.
  lhsCollapse : Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ (D P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ i))))
                ≡ Sx P.⟨$⟩ʳ (cs P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ i))
  lhsCollapse =
    cong (Sx P.⟨$⟩ʳ_)
      (trans (ccx (D P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ i))))
      (trans (collM (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ i)))
             (cong (cs P.⟨$⟩ʳ_) (cong (Sx P.⟨$⟩ʳ_) (ccx i)))))
  -- RHS at `i` reduces to YB-RHS.
  rhsCollapse : D P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ (D P.⟨$⟩ʳ i)))
                ≡ cs P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (cs P.⟨$⟩ʳ i))
  rhsCollapse =
    trans (collM (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ (D P.⟨$⟩ʳ i))))
      (cong (cs P.⟨$⟩ʳ_)
        (trans (cong (Sx P.⟨$⟩ʳ_) (ccx (D P.⟨$⟩ʳ i)))
               (cong (Sx P.⟨$⟩ʳ_) (collM i))))

------------------------------------------------------------------------
-- 3. The heterogeneous wrapper `_≅↭ᴴ_`.
--
-- `_≅↭ⁱ_` is endpoint-homogeneous, but a `~ʷ`-move rewrites the
-- intermediate list, so relating `⟦w⟧↭ xs` and `⟦w′⟧↭ xs` needs a `subst`.
-- `_≅↭ᴴ_` cages that subst by packaging the endpoint equalities; matching
-- them to `refl` makes `subst₂ refl refl` vanish, so no `subst` algebra
-- leaks into `bridge-sound`/`complete`.
------------------------------------------------------------------------

infix 4 _≅↭ᴴ_

_≅↭ᴴ_ : {xs ys xs′ zs : List X} → xs ↭ ys → xs′ ↭ zs → Set
_≅↭ᴴ_ {xs} {ys} {xs′} {zs} p q =
  Σ[ el ∈ xs ≡ xs′ ] Σ[ er ∈ ys ≡ zs ] (subst₂ Perm._↭_ el er p ≅↭ⁱ q)

-- equivalence
hrefl : {p : xs ↭ ys} → p ≅↭ᴴ p
hrefl = refl , refl , iref

hsym : {p : xs ↭ ys} {q : xs′ ↭ zs} → p ≅↭ᴴ q → q ≅↭ᴴ p
hsym (refl , refl , h) = refl , refl , isym h

htrn : {xs″ ws′ : List X} {p : xs ↭ ys} {q : xs′ ↭ zs} {r : xs″ ↭ ws′}
     → p ≅↭ᴴ q → q ≅↭ᴴ r → p ≅↭ᴴ r
htrn (refl , refl , h₁) (refl , refl , h₂) = refl , refl , itrn h₁ h₂

-- congruences
prepᴴ : {p : xs ↭ ys} {q : xs′ ↭ zs} → p ≅↭ᴴ q → Perm.prep x p ≅↭ᴴ Perm.prep x q
prepᴴ (refl , refl , h) = refl , refl , prepc h

trcᴴ : {p : xs ↭ ys} {q : ys ↭ zs} {p′ : xs′ ↭ ys′} {q′ : ys′ ↭ zs′}
     → p ≅↭ᴴ p′ → q ≅↭ᴴ q′ → Perm.trans p q ≅↭ᴴ Perm.trans p′ q′
-- After matching the first wrapper to `(refl , refl , …)` the shared middle
-- list `ys′` is unified with `ys`, so the second wrapper's domain equality
-- `el₂ : ys ≡ ys` is constrained — it cannot be matched against `refl`
-- under `--without-K`.  We bind it and collapse it via Hedberg UIP (`uipX`).
trcᴴ {q = q} (refl , refl , h₁) (el₂ , refl , h₂) =
  refl , refl , trc h₁ (subst (λ e → subst₂ Perm._↭_ e refl q ≅↭ⁱ _) (uipX el₂ refl) h₂)

-- A single-generator piece is heterogeneously equal to another when its
-- (index, list) inputs match (so the `∷c`/index-rewrite case is clean).
swapAt-↭-≅↭ᴴ : {n : ℕ} {i j : Fin n} → i ≡ j → (e : xs ≡ ys)
             → swapAt-↭ i xs ≅↭ᴴ swapAt-↭ j ys
swapAt-↭-≅↭ᴴ refl refl = hrefl

-- …and appending one to a `≅↭ᴴ` needs no new list equality: the one the
-- wrapper already carries IS `swapAt-↭-≅↭ᴴ`'s argument (4 sites).
∷ᴴ : {n : ℕ} {i j : Fin n} {p : xs ↭ ys} {q : xs′ ↭ ys′} → i ≡ j → (h : p ≅↭ᴴ q)
   → Perm.trans p (swapAt-↭ i ys) ≅↭ᴴ Perm.trans q (swapAt-↭ j ys′)
∷ᴴ eq h = trcᴴ h (swapAt-↭-≅↭ᴴ eq (proj₁ (proj₂ h)))

-- Convert back to the homogeneous relation, once the endpoints coincide
-- (e.g. at `complete`, where `p q : xs ↭ ys`).  The endpoint equalities
-- `el : xs ≡ xs`, `er : ys ≡ ys` are reflexive but not free, so we collapse
-- them to `refl` via Hedberg UIP (`uipX`) instead of matching `--with-K`.
toⁱ : {p q : xs ↭ ys} → p ≅↭ᴴ q → p ≅↭ⁱ q
toⁱ {p = p} {q = q} (el , er , h) =
  subst (λ e₂ → subst₂ Perm._↭_ refl e₂ p ≅↭ⁱ q) (uipX er refl)
    (subst (λ e₁ → subst₂ Perm._↭_ e₁ er p ≅↭ⁱ q) (uipX el refl) h)

-- Inject a homogeneous `≅↭ⁱ` into the wrapper.
liftⁱ : {p q : xs ↭ ys} → p ≅↭ⁱ q → p ≅↭ᴴ q
liftⁱ h = refl , refl , h

-- The C1 generator lemma: applying the position-`i` swap twice is the
-- identity, in `≅↭ᴴ`.  Depth-lifting pattern (shared by C2/C3): base = a
-- front `≅↭ⁱ` relation (`swap-invol`), `fsuc` = lift one level with `prepᴴ`,
-- gluing with `prep-tr`/`prep-id`.
swap²ᴴ : {n : ℕ} (i : Fin n) (ys : List X)
       → Perm.trans (swapAt-↭ i ys) (swapAt-↭ i (swapAt i ys)) ≅↭ᴴ Perm.refl {xs = ys}
swap²ᴴ i        []             = liftⁱ tr-unitˡ
swap²ᴴ 0F       (a ∷ [])       = liftⁱ tr-unitˡ
swap²ᴴ 0F       (a ∷ b ∷ rest) = liftⁱ swap-invol
swap²ᴴ (fsuc i) (a ∷ xs)       =
  htrn (liftⁱ (isym prep-tr))
       (htrn (prepᴴ (swap²ᴴ i xs)) (liftⁱ prep-id))

-- The general σ-naturality square: `swap-nat` says `swap = (prep-tower) ∘
-- bare`, `swap-nat-left` says `swap = bare ∘ (prep-tower)`, so the two
-- prep-towers commute past the bare swap.
far-nat : {p : xs ↭ ys}
        → Perm.trans (Perm.prep x (Perm.prep y p)) (Perm.swap x y (Perm.refl {xs = ys}))
          ≅↭ⁱ Perm.trans (Perm.swap x y (Perm.refl {xs = xs})) (Perm.prep y (Perm.prep x p))
far-nat = itrn (isym swap-nat) swap-nat-left

-- The C2 generator lemma (far-commutativity).  `farS` lifts via `prepᴴ`;
-- the `far0ˡ`/`far0ʳ` bases are the naturality square `far-nat`, with short
-- junk lists settled by the unit laws.
swapFarᴴ : {n : ℕ} {i j : Fin n} → Far i j → (ys : List X)
  → Perm.trans (swapAt-↭ j ys) (swapAt-↭ i (swapAt j ys))
    ≅↭ᴴ Perm.trans (swapAt-↭ i ys) (swapAt-↭ j (swapAt i ys))
swapFarᴴ far0ˡ    []             = hrefl
swapFarᴴ far0ˡ    (a ∷ [])       = liftⁱ (itrn tr-unitʳ (isym tr-unitˡ))
swapFarᴴ far0ˡ    (a ∷ b ∷ rest) = liftⁱ far-nat
swapFarᴴ far0ʳ    []             = hrefl
swapFarᴴ far0ʳ    (a ∷ [])       = liftⁱ (itrn tr-unitˡ (isym tr-unitʳ))
swapFarᴴ far0ʳ    (a ∷ b ∷ rest) = liftⁱ (isym far-nat)
swapFarᴴ (farS f) []             = hrefl
swapFarᴴ (farS f) (a ∷ ys′)      =
  htrn (liftⁱ (isym prep-tr)) (htrn (prepᴴ (swapFarᴴ f ys′)) (liftⁱ prep-tr))

-- `prep` distributes over a 3-fold composite (used to lift the braid).
distr3 : {as bs cs ds : List X} {p : as ↭ bs} {q : bs ↭ cs} {r : cs ↭ ds}
       → Perm.prep x (Perm.trans p (Perm.trans q r))
         ≅↭ⁱ Perm.trans (Perm.prep x p) (Perm.trans (Perm.prep x q) (Perm.prep x r))
distr3 = itrn prep-tr (trc iref prep-tr)

-- The C3 generator lemma (braid).  `adjS` lifts via `prepᴴ`; the `adj0`
-- base — on a length-≥3 list — is the `swap-braid` constructor; shorter
-- lists are ruled out by the length hypothesis.
swapBraidᴴ : {n : ℕ} {i k : Fin n} → Adj i k → (ys : List X) → length ys ≡ suc n
  → Perm.trans (swapAt-↭ i ys)
      (Perm.trans (swapAt-↭ k (swapAt i ys)) (swapAt-↭ i (swapAt k (swapAt i ys))))
    ≅↭ᴴ Perm.trans (swapAt-↭ k ys)
      (Perm.trans (swapAt-↭ i (swapAt k ys)) (swapAt-↭ k (swapAt i (swapAt k ys))))
swapBraidᴴ adj0       (a ∷ b ∷ c ∷ rest) _   = liftⁱ swap-braid
swapBraidᴴ adj0       []                 ()
swapBraidᴴ adj0       (a ∷ [])           ()
swapBraidᴴ adj0       (a ∷ b ∷ [])       ()
swapBraidᴴ (adjS adj) []                 ()
swapBraidᴴ (adjS adj) (a ∷ ys′)          len =
  htrn (liftⁱ (isym distr3))
       (htrn (prepᴴ (swapBraidᴴ adj ys′ (suc-injective len))) (liftⁱ distr3))

-- Soundness of the bridge: `~ʷ`-equal words give `≅↭ᴴ`-equal
-- interpretations.  `c1/c2/c3` ↦ re-associate, replace the inner block by
-- its generator lemma (`swap²ᴴ`/`swapFarᴴ`/`swapBraidᴴ`), re-associate back.
bridge-sound : {n : ℕ} {w w′ : Word n} → w ~ʷ w′ → (xs : List X) → length xs ≡ suc n
             → ⟦ w ⟧↭ xs ≅↭ᴴ ⟦ w′ ⟧↭ xs
bridge-sound ~refl          xs len = hrefl
bridge-sound (~sym r)       xs len = hsym (bridge-sound r xs len)
bridge-sound (~trans r₁ r₂) xs len = htrn (bridge-sound r₁ xs len) (bridge-sound r₂ xs len)
bridge-sound (∷c {i = i} {j = j} eq r) xs len = ∷ᴴ eq (bridge-sound r xs len)
bridge-sound (c1 i {w = w}) xs len =
  htrn (liftⁱ tr-assoc)
       (htrn (trcᴴ hrefl (swap²ᴴ i (applyW w xs))) (liftⁱ tr-unitʳ))
bridge-sound (c2 {i = i} {j = j} {w = w} f) xs len =
  htrn (liftⁱ tr-assoc)
       (htrn (trcᴴ hrefl (swapFarᴴ f (applyW w xs))) (liftⁱ (isym tr-assoc)))
bridge-sound (c3 {i = i} {k = k} {w = w} adj) xs len =
  htrn (liftⁱ (itrn tr-assoc tr-assoc))
       (htrn (trcᴴ hrefl (swapBraidᴴ adj (applyW w xs) (trans (applyW-length w xs) len)))
             (liftⁱ (isym (itrn tr-assoc tr-assoc))))

------------------------------------------------------------------------
-- 4. Structure of the interpretation `⟦_⟧↭`, for the straightening.
--
-- These relate `⟦_⟧↭` to the word operations `liftW`/`_++_`.  They are
-- `≅↭ᴴ` (not `≅↭ⁱ`): the endpoint only reduces for a *concrete* word, so
-- the endpoint equality is carried.

interp-cong : {n : ℕ} {w : Word n} {as bs : List X}
            → as ≡ bs → ⟦ w ⟧↭ as ≅↭ᴴ ⟦ w ⟧↭ bs
interp-cong refl = hrefl

-- A lifted word interprets as the original under `prep`.
interp-liftW : {n : ℕ} (w : Word n) {x : X} {xs : List X}
             → ⟦ liftW w ⟧↭ (x ∷ xs) ≅↭ᴴ Perm.prep x (⟦ w ⟧↭ xs)
interp-liftW []        = liftⁱ (isym prep-id)
interp-liftW (i ∷ w′) =
  htrn (∷ᴴ refl (interp-liftW w′)) (liftⁱ (isym prep-tr))

-- A concatenated word interprets as the composite of the two pieces.
interp-++ : {n : ℕ} (v w : Word n) {xs : List X}
          → ⟦ v ++ w ⟧↭ xs ≅↭ᴴ Perm.trans (⟦ w ⟧↭ xs) (⟦ v ⟧↭ (applyW w xs))
interp-++ []       w = liftⁱ (isym tr-unitʳ)
interp-++ (i ∷ v′) w =
  htrn (∷ᴴ refl (interp-++ v′ w)) (liftⁱ tr-assoc)

------------------------------------------------------------------------
-- 5. `flatten`: every `↭`-derivation `p` is `≅↭ᴴ`-equal to the
--    interpretation `⟦ w ⟧↭ xs` of some `Word (length xs)`.
--
-- By induction on `p`, using the `⟦_⟧↭` structure lemmas of §4:
--   * `refl`  ↦ `[]`.
--   * `prep x p′` ↦ `liftW w′`, glued by `interp-liftW`.
--   * `trans p′ q′` ↦ `w_q′ ++ w_p`, glued by `interp-++` (`w_q`
--       `subst`-transported from `length ys` to `length xs`).
--   * `swap x y p′` ↦ `0F ∷ liftW (liftW w′)`: factor by `swap-nat`, send
--       the prep-tower through `interp-liftW` twice, recognise the front
--       `swapAt-↭ 0F` as the bare swap.

⟦⟧↭-subst : {n m : ℕ} (eq : n ≡ m) (w : Word n) {as : List X}
          → ⟦ subst Word eq w ⟧↭ as ≅↭ᴴ ⟦ w ⟧↭ as
⟦⟧↭-subst refl w = hrefl

swap-refl-cong : {ys ys′ : List X}
               → ys′ ≡ ys
               → Perm.swap x y (Perm.refl {xs = ys′}) ≅↭ᴴ Perm.swap x y (Perm.refl {xs = ys})
swap-refl-cong refl = hrefl

flatten : (p : xs ↭ ys) → Σ[ w ∈ Word (pred (length xs)) ] (p ≅↭ᴴ ⟦ w ⟧↭ xs)
flatten Perm.refl = [] , hrefl
flatten (Perm.prep {xs = []} x p′) with flatten p′
... | [] , rel′ = [] , htrn (prepᴴ rel′) (liftⁱ prep-id)
flatten (Perm.prep {xs = z ∷ zs} x p′) with flatten p′
... | w′ , rel′ = liftW w′ , htrn (prepᴴ rel′) (hsym (interp-liftW w′))
flatten (Perm.trans {xs = xs} {ys = ys} {zs = zs} p′ q′)
  with flatten p′ | flatten q′
... | w_p , rel_p | w_q , rel_q =
  w_q′ ++ w_p ,
  htrn (trcᴴ rel_p (htrn rel_q (interp-cong er_p)))
       (hsym (htrn (interp-++ w_q′ w_p)
                   (trcᴴ hrefl (⟦⟧↭-subst (sym eq′) w_q))))
  where
  eq′ : pred (length xs) ≡ pred (length ys)
  eq′ = cong pred (↭-length p′)
  w_q′ : Word (pred (length xs))
  w_q′ = subst Word (sym eq′) w_q
  er_p : ys ≡ applyW w_p xs
  er_p = proj₁ (proj₂ rel_p)
flatten (Perm.swap {xs = z ∷ zs} {ys = ys′} x y p′) with flatten p′
... | w′ , rel′ =
  0F ∷ liftW (liftW w′) ,
  htrn (liftⁱ swap-nat) (∷ᴴ (refl {x = 0F}) piece1)
  where
  piece1 : Perm.prep x (Perm.prep y p′)
           ≅↭ᴴ ⟦ liftW (liftW w′) ⟧↭ (x ∷ y ∷ z ∷ zs)
  piece1 = htrn (prepᴴ (prepᴴ rel′))
                (hsym (htrn (interp-liftW (liftW w′)) (prepᴴ (interp-liftW w′))))
flatten (Perm.swap {xs = []} {ys = ys′} x y p′) with flatten p′
... | [] , rel′ =
  0F ∷ [] ,
  htrn (liftⁱ swap-nat)
       (trcᴴ collapse (swap-refl-cong er′))
  where
  er′ : ys′ ≡ []
  er′ = proj₁ (proj₂ rel′)
  collapse : Perm.prep x (Perm.prep y p′) ≅↭ᴴ Perm.refl {xs = x ∷ y ∷ []}
  collapse =
    htrn (prepᴴ (prepᴴ rel′))
         (htrn (prepᴴ (liftⁱ prep-id)) (liftⁱ prep-id))

------------------------------------------------------------------------
-- 6. `complete`, the combinatorial core.
--
-- `flatten` (§5) sends every derivation `p : (z∷zs) ↭ ys` to a `Word`
-- whose `evalW` agrees with `eval-↭ p` (`flatten-eval`).  So equal
-- `eval-↭`s give equal `evalW`s, hence (`canonW-resp-≈`, `straightenW`)
-- `~ʷ`-equal flattened words, which `bridge-sound` turns into a `≅↭ᴴ`;
-- sandwiched between the two `flatten`-relations it yields `p ≅↭ⁱ q`.

private
  -- UIP on `Fin`-transports: independent of the length proof.  The two
  -- `ℕ`-equalities are interchangeable by Hedberg UIP on `ℕ` (`--without-K`).
  subst-Fin-uip : {m m′ : ℕ} (e e′ : m ≡ m′) (k : Fin m)
                → subst Fin e k ≡ subst Fin e′ k
  subst-Fin-uip e e′ k = cong (λ z → subst Fin z k) (ℕ-≡-irrelevant e e′)

  -- The `flatten`ed word's `evalW` agrees with `eval-↭ p`, transported along
  -- the length proof.  Pointwise.  The wrapper's codomain equality has a free
  -- left endpoint, so it is matched to `refl` here (only the domain one is
  -- constrained and needs `uipX`); `subst₂ refl refl` then vanishes and all
  -- that is left of the transport algebra is one choice of length proof.
  flatten-eval
    : {z : X} {zs ys : List X} (p : (z ∷ zs) ↭ ys) (w : Word (length zs))
    → p ≅↭ᴴ ⟦ w ⟧↭ (z ∷ zs)
    → (k : Fin (suc (length zs)))
    → evalW w P.⟨$⟩ʳ k
      ≡ subst Fin (sym (↭-length p)) (eval-↭ p P.⟨$⟩ʳ k)
  flatten-eval {z = z} {zs} p w (el , refl , h) k
    rewrite uipX el refl =
    trans (sym (eval-respect w (z ∷ zs) refl k))
    (trans (cast-push refl L (eval-↭ (⟦ w ⟧↭ (z ∷ zs))) k)
    (trans (cong (subst Fin L) (sym (sound h k)))
           (subst-Fin-uip L (sym (↭-length p)) (eval-↭ p P.⟨$⟩ʳ k))))
    where
    L : length (applyW w (z ∷ zs)) ≡ suc (length zs)
    L = trans (applyW-length w (z ∷ zs)) refl

complete : {p q : xs ↭ ys} → eval-↭ p ≈-fb eval-↭ q → p ≅↭ⁱ q
complete {xs = []} {ys = ys} {p = p} {q = q} _
  with flatten p | flatten q
... | [] , rel_p | [] , rel_q = toⁱ (htrn rel_p (hsym rel_q))
complete {xs = z ∷ zs} {ys = ys} {p = p} {q = q} h
  with flatten p | flatten q
... | w_p , rel_p | w_q , rel_q = toⁱ (htrn rel_p (htrn bridge (hsym rel_q)))
  where
  -- `evalW w_p ≈-fb evalW w_q`, via `flatten-eval` + the hypothesis.
  eval≈ : evalW w_p ≈-fb evalW w_q
  eval≈ k =
    trans (flatten-eval p w_p rel_p k)
    (trans (cong (subst Fin (sym (↭-length p))) (h k))
    (trans (subst-Fin-uip (sym (↭-length p)) (sym (↭-length q)) (eval-↭ q P.⟨$⟩ʳ k))
           (sym (flatten-eval q w_q rel_q k))))
  -- lift to `~ʷ` (canonical normal forms) and back via `bridge-sound`.
  word~ : w_p ~ʷ w_q
  word~ = ~trans (straightenW w_p)
                 (~trans (canonW-resp-≈ eval≈) (~sym (straightenW w_q)))
  bridge : ⟦ w_p ⟧↭ (z ∷ zs) ≅↭ᴴ ⟦ w_q ⟧↭ (z ∷ zs)
  bridge = bridge-sound word~ (z ∷ zs) refl
