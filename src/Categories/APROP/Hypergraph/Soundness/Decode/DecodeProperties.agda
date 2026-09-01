{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Foundation lemmas for `extract-elem` and `extract-prefix` (defined in
-- `Combinatorics.ExtractPrefix`, re-exported by `Decode.agda`).  These reduce the per-case
-- `decode-attempt-h*` obligations to facts about disjoint Fin injections
-- and `Unique` lists.  Three families: single-list searches, membership /
-- permutation lemmas, and mixed-injection liftings (for hTensor/hComposeP).
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Decode.DecodeProperties (sig : APROPSignature) where

open APROP sig
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-elem; extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Stack.SeparableStack sig
  using ( extract-prefix-++ˡ; extract-prefix-++ˡ-nothing
        ; extract-prefix-++ʳ-nothing )
open import Categories.APROP.Hypergraph.Model.Invariant sig using (inject+-inj; raise-inj; ↑ˡ≢↑ʳ)
-- The derivation-level `map⁺`-naturality of the same `extract-elem`/
-- `extract-prefix` (`Decode` re-exports them from `Combinatorics.ExtractPrefix`,
-- so the statements coincide definitionally); the ∃-forms below just forget
-- which derivation is produced.
open import Categories.Combinatorics.ExtractPrefixEvalPhi
  using (extract-elem-map⁺; extract-prefix-map⁺)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (_≟_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬_)

--------------------------------------------------------------------------------
-- `extract-elem` on a head match returns `just (xs , p)` for SOME `p`.
-- `p` is not pinned to `Perm.refl`: `extract-elem`'s body uses
-- `subst (… ≡ …) p Perm.refl`, which doesn't simplify under `--without-K`.

extract-elem-self
  : ∀ {n} (k : Fin n) (xs : List (Fin n))
  → Σ[ p ∈ ((k ∷ xs) Perm.↭ k ∷ xs) ]
      extract-elem k (k ∷ xs) ≡ just (xs , p)
extract-elem-self k xs with k ≟ k
... | yes a = _ , refl
... | no  q = ⊥-elim (q refl)

--------------------------------------------------------------------------------
-- `extract-elem` skips a non-matching head `x ≢ k`, prepending `x` onto
-- the residual.  Two halves matching the `Maybe` output shape.

extract-elem-skip-nothing
  : ∀ {n} (k x : Fin n) (xs : List (Fin n))
  → ¬ (x ≡ k)
  → extract-elem k xs ≡ nothing
  → extract-elem k (x ∷ xs) ≡ nothing
extract-elem-skip-nothing k x xs x≢k eq with x ≟ k
... | yes p = ⊥-elim (x≢k p)
... | no  _ rewrite eq = refl

--------------------------------------------------------------------------------
-- `extract-elem` on a disjoint-injection mismatch returns `nothing` for
-- any list whose elements are all on the wrong side.

private
  ↑ʳ≢↑ˡ : ∀ {nA nB} (i : Fin nA) (j : Fin nB) → ¬ (nA ↑ʳ j ≡ i ↑ˡ nB)
  ↑ʳ≢↑ˡ i j p = ↑ˡ≢↑ʳ i j (sym p)

extract-elem-↑ˡ-on-↑ʳ-list
  : ∀ {nA nB} (i : Fin nA) (xs : List (Fin nB))
  → extract-elem (i ↑ˡ nB) (map (nA ↑ʳ_) xs) ≡ nothing
extract-elem-↑ˡ-on-↑ʳ-list i []       = refl
extract-elem-↑ˡ-on-↑ʳ-list {nA} {nB} i (x ∷ xs) =
  extract-elem-skip-nothing (i ↑ˡ nB) (nA ↑ʳ x) (map (nA ↑ʳ_) xs)
    (↑ʳ≢↑ˡ i x)
    (extract-elem-↑ˡ-on-↑ʳ-list i xs)

-- R-side key on an L-side list: mirror of `extract-elem-↑ˡ-on-↑ʳ-list`,
-- feeding the LEFT-frame disjointness side conditions below.
extract-elem-↑ʳ-on-↑ˡ-list
  : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA))
  → extract-elem (nA ↑ʳ j) (map (_↑ˡ nB) xs) ≡ nothing
extract-elem-↑ʳ-on-↑ˡ-list nA j []            = refl
extract-elem-↑ʳ-on-↑ˡ-list nA {nB} j (x ∷ xs) =
  extract-elem-skip-nothing (nA ↑ʳ j) (x ↑ˡ nB) (map (_↑ˡ nB) xs)
    (↑ˡ≢↑ʳ x j)
    (extract-elem-↑ʳ-on-↑ˡ-list nA j xs)

--------------------------------------------------------------------------------
-- `extract-prefix-self`: searching for `xs` in `xs` always succeeds with
-- empty residual.  No uniqueness needed — even with duplicates, each head
-- `extract-elem k (k ∷ ks)` matches.

extract-prefix-self
  : ∀ {n} (xs : List (Fin n))
  → Σ[ p ∈ (xs Perm.↭ xs ++ []) ] extract-prefix xs xs ≡ just ([] , p)
extract-prefix-self []       = Perm.refl , refl
extract-prefix-self (x ∷ xs) with extract-elem-self x xs
... | p1 , eq1 with extract-prefix-self xs
...               | p2 , eq2 rewrite eq1 | eq2 = _ , refl

--------------------------------------------------------------------------------
-- `extract-elem`/`extract-prefix` lifting through an injective
-- `f : Fin n → Fin m`.  The disjoint-injection liftings below are special
-- cases; the K-side `remapP` of `hComposeP` is another (injective when both
-- G and K are `Linear`).

extract-elem-via-injective-nothing
  : ∀ {n m} (f : Fin n → Fin m)
  → (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ∀ (k : Fin n) (xs : List (Fin n))
  → extract-elem k xs ≡ nothing
  → extract-elem (f k) (map f xs) ≡ nothing
extract-elem-via-injective-nothing f f-inj k []       _  = refl
extract-elem-via-injective-nothing f f-inj k (x ∷ xs) eq with x ≟ k
extract-elem-via-injective-nothing f f-inj k (x ∷ xs) eq | yes _ with eq
... | ()
extract-elem-via-injective-nothing f f-inj k (x ∷ xs) eq | no  q
    with extract-elem k xs in eq-inner
... | nothing =
      extract-elem-skip-nothing
        (f k) (f x) (map f xs)
        (λ p₁ → q (f-inj p₁))
        (extract-elem-via-injective-nothing f f-inj k xs eq-inner)
... | just _ with eq
... | ()

extract-elem-via-injective-just
  : ∀ {n m} (f : Fin n → Fin m)
  → (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ∀ (k : Fin n) (xs rest : List (Fin n)) (p : xs Perm.↭ k ∷ rest)
  → extract-elem k xs ≡ just (rest , p)
  → ∃[ q ] extract-elem (f k) (map f xs) ≡ just (map f rest , q)
extract-elem-via-injective-just f f-inj k xs rest p eq =
  _ , extract-elem-map⁺ f f-inj k xs rest p eq

extract-prefix-via-injective-nothing
  : ∀ {n m} (f : Fin n → Fin m)
  → (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ∀ (ks xs : List (Fin n))
  → extract-prefix ks xs ≡ nothing
  → extract-prefix (map f ks) (map f xs) ≡ nothing
extract-prefix-via-injective-nothing f f-inj []       xs ()
extract-prefix-via-injective-nothing f f-inj (k ∷ ks) xs eq with extract-elem k xs in eq-elem
... | nothing rewrite extract-elem-via-injective-nothing f f-inj k xs eq-elem = refl
extract-prefix-via-injective-nothing f f-inj (k ∷ ks) xs eq
    | just (xs' , p-elem)
    with extract-prefix ks xs' in eq-prefix
... | nothing with extract-elem-via-injective-just f f-inj k xs xs' p-elem eq-elem
... | _ , eq-elem-f
    rewrite eq-elem-f
          | extract-prefix-via-injective-nothing f f-inj ks xs' eq-prefix
    = refl
extract-prefix-via-injective-nothing f f-inj (k ∷ ks) xs eq
    | just (xs' , p-elem) | just (rest , p-prefix)
    with eq
... | ()

extract-prefix-via-injective-just
  : ∀ {n m} (f : Fin n → Fin m)
  → (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ∀ (ks xs rest : List (Fin n)) (p : xs Perm.↭ ks ++ rest)
  → extract-prefix ks xs ≡ just (rest , p)
  → ∃[ q ] extract-prefix (map f ks) (map f xs) ≡ just (map f rest , q)
extract-prefix-via-injective-just f f-inj ks xs rest p eq =
  _ , extract-prefix-map⁺ f f-inj ks xs rest p eq

--------------------------------------------------------------------------------
-- Lifting `extract-elem` / `extract-prefix` through disjoint injections
-- (for `decode-attempt-hTensor`).  These relate a search on a pure-side
-- list to one on a "mixed" list `map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys` when
-- the key lives entirely on one side.
--
-- Each lemma is a COMPOSITION of the two orthogonal general principles above,
-- so the bespoke `with x ≟ k` cascades are gone (F18):
--   * equivariance under an injection — `extract-*-via-injective-*`;
--   * frame insensitivity — the `++ˡ` (right-frame) / `++ʳ` (left-frame)
--     families in `Stack.SeparableStack`.
-- L-side keys (`↑ˡ`) put the `↑ʳ`-block on the RIGHT ⇒ right frame; R-side
-- keys (`↑ʳ`) put the `↑ˡ`-block on the LEFT ⇒ left frame (whose disjointness
-- side condition is discharged by `extract-elem-↑ʳ-on-↑ˡ-list`).

--------------------------------------------------------------------------------
-- `extract-prefix` lifting: success direction (same two-principle composition).

extract-prefix-↑ˡ-on-mixed-just
  : ∀ {nA} nB (ks xs : List (Fin nA)) (ys : List (Fin nB))
      (rest : List (Fin nA)) (p : xs Perm.↭ ks ++ rest)
  → extract-prefix ks xs ≡ just (rest , p)
  → ∃[ q ] extract-prefix (map (_↑ˡ nB) ks)
                          (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
              ≡ just (map (_↑ˡ nB) rest ++ map (nA ↑ʳ_) ys , q)
extract-prefix-↑ˡ-on-mixed-just {nA} nB ks xs ys rest p eq
    with extract-prefix-via-injective-just (_↑ˡ nB) (inject+-inj nB) ks xs rest p eq
... | _ , e =
      _ , extract-prefix-++ˡ (map (_↑ˡ nB) ks) (map (_↑ˡ nB) xs)
            (map (nA ↑ʳ_) ys) e

--------------------------------------------------------------------------------
-- `extract-prefix` lifting: failure direction (per-edge "edge cannot
-- fire" case in `DecodeAttempt`).

extract-prefix-↑ˡ-on-mixed-nothing
  : ∀ {nA} nB (ks xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-prefix ks xs ≡ nothing
  → extract-prefix (map (_↑ˡ nB) ks)
                   (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
       ≡ nothing
extract-prefix-↑ˡ-on-mixed-nothing {nA} nB ks xs ys eq =
  extract-prefix-++ˡ-nothing (map (_↑ˡ nB) ks) (map (_↑ˡ nB) xs) (map (nA ↑ʳ_) ys)
    (map⁺ (universal (λ k → extract-elem-↑ˡ-on-↑ʳ-list k ys) ks))
    (extract-prefix-via-injective-nothing (_↑ˡ nB) (inject+-inj nB) ks xs eq)

extract-prefix-↑ʳ-on-mixed-nothing
  : ∀ nA {nB} (ks : List (Fin nB)) (xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-prefix ks ys ≡ nothing
  → extract-prefix (map (nA ↑ʳ_) ks)
                   (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
       ≡ nothing
extract-prefix-↑ʳ-on-mixed-nothing nA {nB} ks xs ys eq =
  extract-prefix-++ʳ-nothing (map (nA ↑ʳ_) ks) (map (_↑ˡ nB) xs) (map (nA ↑ʳ_) ys)
    (map⁺ (universal (λ k → extract-elem-↑ʳ-on-↑ˡ-list nA k xs) ks))
    (extract-prefix-via-injective-nothing (nA ↑ʳ_) (raise-inj nA) ks ys eq)

--------------------------------------------------------------------------------
-- `extract-elem-found`: `y ∈ xs` constructively produces a successful
-- `extract-elem y xs ≡ just (rest, p)`.

extract-elem-found
  : ∀ {n} (y : Fin n) (xs : List (Fin n))
  → y ∈ xs
  → ∃[ rest ] ∃[ p ] extract-elem y xs ≡ just (rest , p)
extract-elem-found y (x ∷ xs) (here refl) with y ≟ y
... | yes _ = _ , _ , refl
... | no  q = ⊥-elim (q refl)
extract-elem-found y (x ∷ xs) (there mem) with x ≟ y
... | yes _   = _ , _ , refl
... | no  q   with extract-elem-found y xs mem
...              | _ , _ , eq rewrite eq = _ , _ , refl

--------------------------------------------------------------------------------
-- `extract-prefix-↭-residual`: when `xs ↭ ks ++ rest`, `extract-prefix ks xs`
-- succeeds with a residual `rest'` permuting to `rest`.

extract-prefix-↭-residual
  : ∀ {n} (ks xs rest : List (Fin n))
  → xs Perm.↭ ks ++ rest
  → ∃[ rest' ] ∃[ p ] extract-prefix ks xs ≡ just (rest' , p)
                     × rest Perm.↭ rest'
extract-prefix-↭-residual []       xs rest perm-in = xs , Perm.refl , refl , Perm.↭-sym perm-in
extract-prefix-↭-residual (k ∷ ks) xs rest perm-in
    with extract-elem-found k xs
           (PermProp.∈-resp-↭ (Perm.↭-sym perm-in) (here refl))
... | xs' , q , eq-extract
    with extract-prefix-↭-residual ks xs' rest
           (PermProp.drop-∷ (Perm.↭-trans (Perm.↭-sym q) perm-in))
... | rest' , p-prefix , eq-prefix , rest-perm
    rewrite eq-extract | eq-prefix = rest' , _ , refl , rest-perm

--------------------------------------------------------------------------------
-- `extract-prefix-↭-nothing`: contrapositive of the residual lemma.
-- `extract-prefix ks xs ≡ nothing` and `xs ↭ xs'` ⇒ `extract-prefix ks
-- xs' ≡ nothing`.  Lifts the "edge doesn't fire" case to ↭-stacks.

extract-prefix-↭-nothing
  : ∀ {n} (ks xs xs' : List (Fin n))
  → xs Perm.↭ xs'
  → extract-prefix ks xs ≡ nothing
  → extract-prefix ks xs' ≡ nothing
extract-prefix-↭-nothing ks xs xs' xs↭xs' eq with extract-prefix ks xs' in eq-xs'
... | nothing             = refl
... | just (rest' , p-xs') with extract-prefix-↭-residual ks xs rest' (Perm.↭-trans xs↭xs' p-xs')
... | _ , _ , eq-xs , _ rewrite eq-xs with eq
... | ()
