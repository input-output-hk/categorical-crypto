{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- The `∘` case of the decoder, end to end, for the pruning translation `⟪_⟫ₚ`
-- (whose `∘` is `hComposeP`).  Two halves of one story about the same cospan
-- composite, sharing one parameter block `(G K bdy-eq lin-G lin-K)`:
--
--   * linearity is PRESERVED (`Linear-hComposeP`), via injectivity of the
--     K-side vertex remap `remapP = remap K.dom lookup-cod`
--     (`remapP-injective`).  The routing baked into `remapP`:
--       - members of K.dom go to `lookup-cod i ↑ˡ count-non K.dom` (G-side),
--       - non-members go to `G.nV ↑ʳ j`                    (pruned slot);
--   * the decoder is TOTAL on `⟪_⟫ₚ`: `decode-attempt-hComposeP` (the `∘`
--     lift), `⟪⟫-LinearP` (the invariant), `decode-attempt-LinearP`.
--
-- Pruning removes only vertices, never edges (same `nE`, same Fin order), so
-- every atomic (non-`∘`) decode lemma from `DecodeAttempt` is reused verbatim;
-- only the `∘` machinery is proven here.  No postulates.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.DecodeAttemptLinearP
  (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.FromAPROP sig

open import Categories.APROP.Hypergraph.Model.PrunedCompose sig

open import Categories.APROP.Hypergraph.Util.Prune

open import Categories.APROP.Hypergraph.Model.Translation sig
  using () renaming (⟪_⟫ to ⟪_⟫ₚ; ⟪⟫-domL to ⟪⟫ₚ-domL; ⟪⟫-codL to ⟪⟫ₚ-codL)
open import Categories.APROP.Hypergraph.Soundness.Base.Unflatten sig

open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig

open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties sig

import Categories.APROP.Hypergraph.Model.Invariant sig as Inv
import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig as Lin
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using ( count; count-++; count-map-↑ˡ; count-map-inj
        ; count-map-↑ˡ-mismatch; count-swap
        ; producedList; consumedList; Linear; concat-tabulate-blocks)

-- Reused-as-is generic decode lemmas (arbitrary `H`).
open import Categories.APROP.Hypergraph.Soundness.Decode.DecodeAttempt sig


open import Data.Nat
open import Data.List
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_; cast; toℕ)
-- `Data.List`, opened wholesale for the decode half, also exports `splitAt`.
open import Data.Fin using () renaming (splitAt to splitAtF)
open import Data.Fin.Properties using
  ( splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ
  ; toℕ-cast; toℕ-injective)
  -- `Data.Nat`, opened wholesale for the decode half, also exports `_≟_`.
  renaming (_≟_ to _≟F_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Nat as Nat using ()
import Data.Nat.Properties as Nat
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary.Decidable using (yes; no)

--------------------------------------------------------------------------------
-- Count / permutation helpers.

open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using ( count≤1⇒Unique; ∉→count-zero; count-++-bndˡ; count-++-bndʳ
        ; count-map-resp; ++-bnd→disjoint)

private

  -- `cast eq` is injective (preserves `toℕ`).  Stdlib 2.3 lacks
  -- `cast-injective`; derived from `toℕ-cast` + `toℕ-injective`.
  cast-injective : ∀ {m n} (eq : m ≡ n) {i j : Fin m} → cast eq i ≡ cast eq j → i ≡ j
  cast-injective eq {i} {j} ci≡cj =
    toℕ-injective
      (trans (sym (toℕ-cast eq i))
             (trans (cong toℕ ci≡cj) (toℕ-cast eq j)))

  -- `count` over `X ++ C`, where `C` is given as a two-block split `A ++ B`.
  count-split3 : ∀ {n} (v : Fin n) (X : List (Fin n)) {C} (A B : List (Fin n))
               → C ≡ A ++ B → count v (X ++ C) ≡ count v X + count v A + count v B
  count-split3 v X A B refl = trans (count-++ v X (A ++ B))
    (trans (cong (count v X +_) (count-++ v A B)) (sym (Nat.+-assoc (count v X) _ _)))

--------------------------------------------------------------------------------
-- The shared parameter block: a cospan-composable pair of LINEAR hypergraphs.
-- Everything about one composite lives here — the linearity half, the per-edge
-- liftings (G-side `injL = _↑ˡ cn`, K-side `remapP`, whose lift needs
-- `remapP-injective` from the linearity half), and the `∘` decode lemma.

module _
  (G K : Hypergraph FlatGen) (bdy-eq : codL G ≡ domL K)
  (lin-G : Linear G) (lin-K : Linear K)
  where

  open hComposeP-impl G K bdy-eq

  private
    module G = Hypergraph G
    module K = Hypergraph K

    G-bal = proj₁ lin-G
    G-bnd = proj₂ lin-G
    K-bal = proj₁ lin-K
    K-bnd = proj₂ lin-K

    G-eb    = concat (tabulate G.eout)
    G-ein-b = concat (tabulate G.ein)
    K-eb    = concat (tabulate K.eout)
    K-ein-b = concat (tabulate K.ein)

    cn = count-non K.dom
  ------------------------------------------------------------------------
  -- Bounds carried over from the linearity invariant.

  K-dom-bnd : ∀ k → count k K.dom Nat.≤ 1
  K-dom-bnd k = count-++-bndˡ k K.dom K-eb (K-bnd k)

  G-cod-bnd : ∀ v → count v G.cod Nat.≤ 1
  G-cod-bnd v =
    count-++-bndˡ v G.cod G-ein-b
      (Nat.≤-trans (Nat.≤-reflexive (sym (G-bal v))) (G-bnd v))

  ------------------------------------------------------------------------
  -- `remapP-injective`.

  K-dom-Unique : Unique K.dom
  K-dom-Unique = count≤1⇒Unique K-dom-bnd

  G-cod-Unique : Unique G.cod
  G-cod-Unique = count≤1⇒Unique G-cod-bnd

  -- `lookup-cod` is injective: `lookup G.cod` (injective on a Unique
  -- list) precomposed with the injective `cast`.
  lookup-cod-injective : ∀ {i j : Fin (length K.dom)} → lookup-cod i ≡ lookup-cod j → i ≡ j
  lookup-cod-injective {i} {j} eq =
    cast-injective dom-cod-len
      (lookup-injective-unique G-cod-Unique
        (cast dom-cod-len i) (cast dom-cod-len j) eq)

  -- Injectivity of the pruned K-side vertex remap.
  remapP-injective : ∀ {v v'} → remapP v ≡ remapP v' → v ≡ v'
  remapP-injective = remap-injective K.dom lookup-cod K-dom-Unique lookup-cod-injective

  ------------------------------------------------------------------------
  -- `map remapP K.dom ≡ map (_↑ˡ cn) G.cod`.  Each member of K.dom is
  -- routed to `lookup-cod idx ↑ˡ cn`, and `lookup-cod` walks G.cod in
  -- lockstep with K.dom, so the two mapped lists agree.

  private
    -- Pointwise: `remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn`.
    remapP-on-dom : ∀ (idx : Fin (length K.dom)) → remapP (lookup K.dom idx) ≡ lookup-cod idx ↑ˡ cn
    remapP-on-dom idx =
      remap-inj₁ K.dom lookup-cod (lookup K.dom idx) idx
        (classify-lookup-Unique K.dom K-dom-Unique idx)

    -- List-extensionality: two `map`s agree when their lengths agree and
    -- they agree pointwise (up to `cast` on the index).
    map-ext-cast
      : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          (f : A → B) (g : C → B)
          (xs : List A) (ys : List C) (len : length xs ≡ length ys)
      → (∀ i → f (lookup xs i) ≡ g (lookup ys (cast len i)))
      → map f xs ≡ map g ys
    map-ext-cast f g []       []       _   _  = refl
    map-ext-cast f g []       (y ∷ ys) ()  _
    map-ext-cast f g (x ∷ xs) []       ()  _
    map-ext-cast f g (x ∷ xs) (y ∷ ys) len pt =
      cong₂ _∷_ (pt zero)
        (map-ext-cast f g xs ys (Nat.suc-injective len) (λ i → pt (suc i)))

  map-remapP-K-dom : map remapP K.dom ≡ map (_↑ˡ cn) G.cod
  map-remapP-K-dom = map-ext-cast remapP (_↑ˡ cn) K.dom G.cod dom-cod-len remapP-on-dom

  -- count facts about `map remapP K.dom` consumed by the balance proof.
  count-map-remapP-K-dom-injL : ∀ (i : Fin G.nV) → count (i ↑ˡ cn) (map remapP K.dom) ≡ count i G.cod
  count-map-remapP-K-dom-injL i = trans (cong (count (i ↑ˡ cn)) map-remapP-K-dom) (count-map-↑ˡ cn i G.cod)

  count-map-remapP-K-dom-raise : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (map remapP K.dom) ≡ 0
  count-map-remapP-K-dom-raise j =
    trans (cong (count (G.nV ↑ʳ j)) map-remapP-K-dom)
          (count-map-↑ˡ-mismatch G.nV j G.cod)

  ------------------------------------------------------------------------
  -- For BALANCE we only push K-balance through `remapP` via
  -- `count-map-resp` (treating `remapP` opaquely); for BOUND we need to
  -- bound `count v (map remapP K-eb)`, obtained from K-bound by
  -- `count-map-inj` at the `remapP`-fiber of the counted vertex.

  ------------------------------------------------------------------------
  -- Structural decompositions of `concat (tabulate eout-c / ein-c)`.


  eout-comp-eq : concat (tabulate eout-c) ≡ map injL G-eb ++ map remapP K-eb
  eout-comp-eq = concat-tabulate-blocks eout-c G.eout K.eout injL remapP
                   eout-c-inj₁-red eout-c-inj₂-red

  ein-comp-eq : concat (tabulate ein-c) ≡ map injL G-ein-b ++ map remapP K-ein-b
  ein-comp-eq = concat-tabulate-blocks ein-c G.ein K.ein injL remapP
                  ein-c-inj₁-red ein-c-inj₂-red

  ------------------------------------------------------------------------
  -- The dom/cod of the composite (from `hComposeP`'s record):
  --   dom = map injL G.dom ,  cod = map remapP K.cod.

  count-prod
    : ∀ v
    → count v (producedList (hComposeP G K bdy-eq))
    ≡ count v (map injL G.dom)
    + count v (map injL G-eb)
    + count v (map remapP K-eb)
  count-prod v =
    count-split3 v (map injL G.dom) (map injL G-eb) (map remapP K-eb) eout-comp-eq

  count-cons
    : ∀ v
    → count v (consumedList (hComposeP G K bdy-eq))
    ≡ count v (map remapP K.cod)
    + count v (map injL G-ein-b)
    + count v (map remapP K-ein-b)
  count-cons v =
    count-split3 v (map remapP K.cod) (map injL G-ein-b) (map remapP K-ein-b) ein-comp-eq

  ------------------------------------------------------------------------
  -- K-balance pushed through `remapP` (treating remapP opaquely).

  K-bal-via-remapP : ∀ v → count v (map remapP (K.dom ++ K-eb)) ≡ count v (map remapP (K.cod ++ K-ein-b))
  K-bal-via-remapP v = count-map-resp remapP (K.dom ++ K-eb) (K.cod ++ K-ein-b) K-bal v

  ------------------------------------------------------------------------
  -- The "L-side balance" identity.  For v = injL i it combines G-bal with
  -- `map-remapP-K-dom`; for v = raise j both sides are 0.

  αβ≡εη
    : ∀ v
    → count v (map injL G.dom) + count v (map injL G-eb)
    ≡ count v (map injL G-ein-b) + count v (map remapP K.dom)
  αβ≡εη v with splitAtF G.nV v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = cn} eq
  ...           | refl =
                  trans (cong₂ Nat._+_
                          (count-map-↑ˡ cn i G.dom)
                          (count-map-↑ˡ cn i G-eb))
                  (trans (sym (count-++ i G.dom G-eb))
                  (trans (G-bal i)
                  (trans (count-swap i G.cod G-ein-b)
                  (trans (count-++ i G-ein-b G.cod)
                         (cong₂ Nat._+_
                           (sym (count-map-↑ˡ cn i G-ein-b))
                           (sym (count-map-remapP-K-dom-injL i)))))))
  αβ≡εη v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
  ...                | refl =
                       trans (cong₂ Nat._+_
                               (count-map-↑ˡ-mismatch G.nV j G.dom)
                               (count-map-↑ˡ-mismatch G.nV j G-eb))
                       (sym (cong₂ Nat._+_
                               (count-map-↑ˡ-mismatch G.nV j G-ein-b)
                               (count-map-remapP-K-dom-raise j)))

  ------------------------------------------------------------------------
  -- Balance: combining all the pieces.

  balance : ∀ v → count v (producedList (hComposeP G K bdy-eq)) ≡ count v (consumedList (hComposeP G K bdy-eq))
  balance v =
    trans (count-prod v)
    (trans (cong (Nat._+ γ) (αβ≡εη v))
    (trans (Nat.+-assoc ε η γ)
    (trans (cong (ε Nat.+_)
                 (trans (sym (count-++ v (map remapP K.dom) (map remapP K-eb)))
                 (trans (sym (cong (count v) (map-++ remapP K.dom K-eb)))
                 (trans (K-bal-via-remapP v)
                 (trans (cong (count v) (map-++ remapP K.cod K-ein-b))
                        (count-++ v (map remapP K.cod) (map remapP K-ein-b)))))))
    (trans (sym (Nat.+-assoc ε δ ζ))
    (trans (cong (Nat._+ ζ) (Nat.+-comm ε δ))
           (sym (count-cons v)))))))
    where
      γ = count v (map remapP K-eb)
      δ = count v (map remapP K.cod)
      ε = count v (map injL G-ein-b)
      ζ = count v (map remapP K-ein-b)
      η = count v (map remapP K.dom)

  ------------------------------------------------------------------------
  -- Bound: case-split on `v`.  The produced count decomposes (count-prod)
  -- into the G.dom, G-eb and (map remapP K-eb) contributions.
  --
  --   * For v = raise j: the G-side terms are 0 and the K-eb term is ≤ 1
  --     (it equals `count k K-eb` for the unique remapP-preimage, by
  --     injectivity, bounded by K-bound).
  --   * For v = injL i: the G-side terms sum to ≤ 1 (G-bound), and the
  --     K-eb term is *exactly 0* — any `k ∈ K-eb` with `remapP k ≡ injL i`
  --     would have `k ∈ K.dom` (only K.dom members route to injL slots),
  --     giving count ≥ 2 in `K.dom ++ K-eb`, contradicting K-bound.

  private
    K-eb-bnd : ∀ k → count k K-eb Nat.≤ 1
    K-eb-bnd k = count-++-bndʳ k K.dom K-eb (K-bnd k)

    -- count (any v) in (map remapP K-eb) ≤ 1, via injectivity of remapP.
    -- Decide membership of v in the mapped list: a member has a preimage
    -- `k` (`∈-map⁻`) whose count bounds the v-count; a non-member's count
    -- is 0.
    count-remapP-K-eb-≤1 : ∀ v → count v (map remapP K-eb) Nat.≤ 1
    count-remapP-K-eb-≤1 v with any? (v ≟F_) (map remapP K-eb)
    ... | no  v∉ = Nat.≤-trans (Nat.≤-reflexive (∉→count-zero v∉)) z≤n
    ... | yes v∈ with ∈-map⁻ remapP v∈
    ...   | k , _ , v≡rk =
            Nat.≤-trans
              (Nat.≤-reflexive
                (subst (λ w → count w (map remapP K-eb) ≡ count k K-eb) (sym v≡rk)
                       (count-map-inj remapP remapP-injective k K-eb)))
              (K-eb-bnd k)

    -- Only K.dom members route to `↑ˡ`-slots (injL).  `Prune.classify-view`
    -- gives both halves in one split: `is-mem` carries the membership witness
    -- directly; `is-non` reduces `remapP k` to a `G.nV ↑ʳ_` slot, absurd
    -- against `injL i` by `Invariant.↑ˡ≢↑ʳ`.
    remapP-injL→dom : ∀ (k : Fin K.nV) (i : Fin G.nV) → remapP k ≡ injL i → k ∈ K.dom
    remapP-injL→dom k i rpk with classify K.dom k | classify-view K.dom k
    ... | _ | is-mem k∈ = k∈
    ... | _ | is-non _  = ⊥-elim (Inv.↑ˡ≢↑ʳ i _ (sym rpk))

    -- The K-eb contribution at an injL-slot vanishes: a preimage `k`
    -- (`∈-map⁻`) of `injL i` is in K.dom, and K.dom is disjoint from K-eb.
    count-injL-remapP-K-eb-zero : ∀ (i : Fin G.nV) → count (injL i) (map remapP K-eb) ≡ 0
    count-injL-remapP-K-eb-zero i with any? (injL i ≟F_) (map remapP K-eb)
    ... | no  i∉ = ∉→count-zero i∉
    ... | yes i∈ with ∈-map⁻ remapP i∈
    ...   | k , k∈ , i≡rk =
            ⊥-elim (++-bnd→disjoint K.dom K-eb (K-bnd k)
                      (remapP-injL→dom k i (sym i≡rk)) k∈)

    bound-injL : ∀ (i : Fin G.nV) → count (injL i) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
    bound-injL i =
      subst (Nat._≤ 1)
        (sym (trans (count-prod (i ↑ˡ cn))
              (trans (cong (Nat._+ count (injL i) (map remapP K-eb))
                           (cong₂ Nat._+_
                             (count-map-↑ˡ cn i G.dom)
                             (count-map-↑ˡ cn i G-eb)))
                     (trans (cong (count i G.dom + count i G-eb Nat.+_)
                                  (count-injL-remapP-K-eb-zero i))
                            (trans (Nat.+-identityʳ _)
                                   (sym (count-++ i G.dom G-eb)))))))
        (G-bnd i)

    bound-raise : ∀ (j : Fin cn) → count (G.nV ↑ʳ j) (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
    bound-raise j =
      subst (Nat._≤ 1)
        (sym (trans (count-prod (G.nV ↑ʳ j))
              (trans (cong (Nat._+ count (G.nV ↑ʳ j) (map remapP K-eb))
                           (cong₂ Nat._+_
                             (count-map-↑ˡ-mismatch G.nV j G.dom)
                             (count-map-↑ˡ-mismatch G.nV j G-eb)))
                     refl)))
        (count-remapP-K-eb-≤1 (G.nV ↑ʳ j))

  bound : ∀ v → count v (producedList (hComposeP G K bdy-eq)) Nat.≤ 1
  bound v with splitAtF G.nV v in eq
  ... | inj₁ i with splitAt⁻¹-↑ˡ {n = cn} eq
  ...           | refl = bound-injL i
  bound v | inj₂ j with splitAt⁻¹-↑ʳ {m = G.nV} eq
  ...                | refl = bound-raise j

  ------------------------------------------------------------------------
  -- The pruned composition preserves linearity.

  Linear-hComposeP : Linear (hComposeP G K bdy-eq)
  Linear-hComposeP = balance , bound

  ------------------------------------------------------------------------
  -- G-side: the frame-free instance of `DecodeAttempt.StackLift` — the stack
  -- former is `map injL` and `fold` is one `map-++`.

  private
    module PureL where
      out : List (Fin G.nV) → List (Fin nV-P)
      out = map injL

      hit : ∀ (e : Fin G.nE) (xs rest : List (Fin G.nV))
              (p : xs Perm.↭ G.ein e ++ rest)
          → extract-prefix (G.ein e) xs ≡ just (rest , p)
          → ∃[ q ] extract-prefix
                     (Hypergraph.ein (hComposeP G K bdy-eq) (e ↑ˡ K.nE)) (out xs)
                   ≡ just (out rest , q)
      hit e xs rest p eq =
        subst (λ ks → ∃[ q ] extract-prefix ks (out xs) ≡ just (out rest , q))
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-just injL (Inv.inject+-inj cn)
                                                  (G.ein e) xs rest p eq)

      miss : ∀ (e : Fin G.nE) (xs : List (Fin G.nV))
           → extract-prefix (G.ein e) xs ≡ nothing
           → extract-prefix
               (Hypergraph.ein (hComposeP G K bdy-eq) (e ↑ˡ K.nE)) (out xs)
             ≡ nothing
      miss e xs eq =
        subst (λ ks → extract-prefix ks (out xs) ≡ nothing)
              (sym (ein-c-inj₁-red e))
              (extract-prefix-via-injective-nothing injL (Inv.inject+-inj cn)
                                                     (G.ein e) xs eq)

      fold : ∀ (e : Fin G.nE) (rest : List (Fin G.nV))
           → Hypergraph.eout (hComposeP G K bdy-eq) (e ↑ˡ K.nE) ++ out rest
             ≡ out (G.eout e ++ rest)
      fold e rest =
        trans (cong (_++ out rest) (eout-c-inj₁-red e))
              (sym (map-++ injL (G.eout e) rest))

      open StackLift (hComposeP G K bdy-eq) G (_↑ˡ K.nE) out hit miss fold public

  process-edges-↑ˡ-pure-L
    : ∀ (es : List (Fin G.nE)) (xs : List (Fin G.nV))
    → process-edges (hComposeP G K bdy-eq) (map (_↑ˡ K.nE) es) (map injL xs)
      ≡ map injL (process-edges G es xs)
  process-edges-↑ˡ-pure-L = PureL.process-edges-lift

  --------------------------------------------------------------------
  -- K-side: the frame-free instance of `DecodeAttempt.PermLift` — with no
  -- L-block to commute past, `front` and `fold` are one `map-++` each.

  private
    module ViaRemapP where
      out : List (Fin K.nV) → List (Fin nV-P)
      out = map remapP

      front : ∀ (e : Fin K.nE) (ys rest : List (Fin K.nV))
            → ys Perm.↭ K.ein e ++ rest
            → out ys Perm.↭ map remapP (K.ein e) ++ out rest
      front e ys rest p =
        Perm.↭-trans (PermProp.map⁺ remapP p)
                     (Perm.↭-reflexive (map-++ remapP (K.ein e) rest))

      fold : ∀ (e : Fin K.nE) (rest : List (Fin K.nV))
           → map remapP (K.eout e) ++ out rest Perm.↭ out (K.eout e ++ rest)
      fold e rest = Perm.↭-reflexive (sym (map-++ remapP (K.eout e) rest))

      miss : ∀ (e : Fin K.nE) (ys : List (Fin K.nV))
           → extract-prefix (K.ein e) ys ≡ nothing
           → extract-prefix (map remapP (K.ein e)) (out ys) ≡ nothing
      miss e ys eq =
        extract-prefix-via-injective-nothing remapP remapP-injective
                                              (K.ein e) ys eq

      open PermLift (hComposeP G K bdy-eq) K (G.nE ↑ʳ_) remapP out
             ein-c-inj₂-red eout-c-inj₂-red front fold miss public

  ------------------------------------------------------------------------
  -- `decode-attempt-hComposeP`: run the G-block, then the K-block.

  decode-attempt-hComposeP
    : process-all-edges G (Hypergraph.dom G) Perm.↭ Hypergraph.cod G
    → process-all-edges K (Hypergraph.dom K) Perm.↭ Hypergraph.cod K
    → process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))
        Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
  decode-attempt-hComposeP perm-G perm-K =
      perm-final
    where
      open Perm.PermutationReasoning

      s_G_final = process-all-edges G G.dom
      s_K_final = process-all-edges K K.dom

      proc = process-all-edges (hComposeP G K bdy-eq) (Hypergraph.dom (hComposeP G K bdy-eq))

      after-G-stack = process-edges (hComposeP G K bdy-eq)
                        (map (_↑ˡ K.nE) (range G.nE))
                        (Hypergraph.dom (hComposeP G K bdy-eq))

      after-G-≡ : after-G-stack ≡ map injL s_G_final
      after-G-≡ = PureL.process-edges-lift (range G.nE) G.dom

      after-G-↭-remap-Kdom : after-G-stack Perm.↭ map remapP K.dom
      after-G-↭-remap-Kdom = begin
        after-G-stack
          ≡⟨ after-G-≡ ⟩
        map injL s_G_final
          ↭⟨ PermProp.map⁺ injL perm-G ⟩
        map injL G.cod
          ≡⟨ sym map-remapP-K-dom ⟩
        map remapP K.dom
          ∎

      K-lift : process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
                 Perm.↭ map remapP s_K_final
      K-lift = ViaRemapP.process-edges-lift
                 (range K.nE) after-G-stack K.dom after-G-↭-remap-Kdom

      proc-≡ : proc
               ≡ process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
      proc-≡ =
        trans (cong (λ es → process-edges (hComposeP G K bdy-eq) es
                              (Hypergraph.dom (hComposeP G K bdy-eq)))
                    (Inv.range-++ G.nE K.nE))
              (process-edges-++-stack (hComposeP G K bdy-eq)
                (map (_↑ˡ K.nE) (range G.nE))
                (map (G.nE ↑ʳ_) (range K.nE))
                (Hypergraph.dom (hComposeP G K bdy-eq)))

      perm-final : proc Perm.↭ Hypergraph.cod (hComposeP G K bdy-eq)
      perm-final = begin
        proc
          ≡⟨ proc-≡ ⟩
        process-edges (hComposeP G K bdy-eq) (map (G.nE ↑ʳ_) (range K.nE)) after-G-stack
          ↭⟨ K-lift ⟩
        map remapP s_K_final
          ↭⟨ PermProp.map⁺ remapP perm-K ⟩
        map remapP K.cod
          ∎

--------------------------------------------------------------------------------
-- `⟪⟫-LinearP`.

⟪⟫-LinearP : ∀ {A B} (f : HomTerm A B) → Lin.Linear ⟪ f ⟫ₚ
⟪⟫-LinearP (Agen g)        = Lin.Linear-hGen g
⟪⟫-LinearP (id {A})        = Lin.Linear-hId A
⟪⟫-LinearP (g ∘ f)         =
  Linear-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
⟪⟫-LinearP (f ⊗₁ g)        = Lin.Linear-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ (⟪⟫-LinearP f) (⟪⟫-LinearP g)
⟪⟫-LinearP (λ⇒ {A})        = Lin.Linear-hId A
⟪⟫-LinearP (λ⇐ {A})        = Lin.Linear-hId A
⟪⟫-LinearP (ρ⇒ {A})        = Lin.Linear-hId (A ⊗₀ unit)
⟪⟫-LinearP (ρ⇐ {A})        = Lin.Linear-hId (A ⊗₀ unit)
⟪⟫-LinearP (α⇒ {A}{B}{C})  = Lin.Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-LinearP (α⇐ {A}{B}{C})  = Lin.Linear-hId ((A ⊗₀ B) ⊗₀ C)
⟪⟫-LinearP (σ {A}{B})      = Lin.Linear-hSwap A B

--------------------------------------------------------------------------------
-- `decode-attempt-LinearP`.

decode-attempt-LinearP
  : ∀ {A B} (f : HomTerm A B)
  → process-all-edges ⟪ f ⟫ₚ (Hypergraph.dom ⟪ f ⟫ₚ) Perm.↭ Hypergraph.cod ⟪ f ⟫ₚ
decode-attempt-LinearP (Agen g)        = decode-attempt-hGen g
decode-attempt-LinearP (id {A})        = decode-attempt-hId A
decode-attempt-LinearP (g ∘ f)         =
  decode-attempt-hComposeP ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (trans (⟪⟫ₚ-codL f) (sym (⟪⟫ₚ-domL g)))
    (⟪⟫-LinearP f) (⟪⟫-LinearP g)
    (decode-attempt-LinearP f) (decode-attempt-LinearP g)
decode-attempt-LinearP (f ⊗₁ g)        =
  decode-attempt-hTensor ⟪ f ⟫ₚ ⟪ g ⟫ₚ
    (decode-attempt-LinearP f) (decode-attempt-LinearP g)
decode-attempt-LinearP (λ⇒ {A})        = decode-attempt-hId A
decode-attempt-LinearP (λ⇐ {A})        = decode-attempt-hId A
decode-attempt-LinearP (ρ⇒ {A})        = decode-attempt-hId (A ⊗₀ unit)
decode-attempt-LinearP (ρ⇐ {A})        = decode-attempt-hId (A ⊗₀ unit)
decode-attempt-LinearP (α⇒ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
decode-attempt-LinearP (α⇐ {A}{B}{C})  = decode-attempt-hId ((A ⊗₀ B) ⊗₀ C)
decode-attempt-LinearP (σ {A}{B})      = decode-attempt-hSwap A B

-- NOTE (weak-decoder demotion, Review-2 F2): the non-strict total decoder
-- `decodeP` (which packaged `proj₁ (decode-attempt-LinearP f)` as a boundary
-- `subst₂ HomTerm`) had zero live consumers — the live pipeline runs entirely
-- through the strict `decodePˢ`.  It has been deleted along with the weak
-- morphism apparatus; only the totality witness `decode-attempt-LinearP`
-- survives (consumed by `Strict/Decode/Decode` — the witness IS the bare
-- permutation `process-all-edges ⟪f⟫ dom ↭ cod`, so no `Maybe`/`≡ just`
-- unwrapping is needed).
