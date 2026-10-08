{-# OPTIONS --safe --without-K #-}

-- Search transparency needs absent keys in a left frame.
module Categories.Combinatorics.ExtractPrefix.Properties where

open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.ExtractPrefixEvalPhi

open import Data.Empty
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using (_≟_; ↑ˡ-injective; ↑ʳ-injective)
open import Data.Fin.Properties.Ext
open import Data.List.Base
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.List.Relation.Unary.All using (All; []; _∷_; universal)
open import Data.List.Relation.Unary.All.Properties using (map⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation

private variable n m nA nB : ℕ

--------------------------------------------------------------------------------
-- Right frames
--------------------------------------------------------------------------------

-- Search stops at the first occurrence, so a successful prefix search never
-- inspects the right frame. Its proof tree carries that frame unchanged.
extract-elem-++ˡ
  : (k : Fin n) (xs R : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ k ∷ rest}
  → extract-elem k xs ≡ just (rest , p)
  → extract-elem k (xs ++ R) ≡ just (rest ++ R , PermProp.++⁺ʳ R p)
extract-elem-++ˡ k []       R ()
extract-elem-++ˡ k (x ∷ xs) R eq with x ≟ k
extract-elem-++ˡ k (x ∷ xs) R {rest} {p} eq | yes refl with eq
... | refl = refl
extract-elem-++ˡ k (x ∷ xs) R eq | no ¬q with extract-elem k xs in eqxs
extract-elem-++ˡ k (x ∷ xs) R eq | no ¬q | just (rest' , q') with eq
... | refl rewrite extract-elem-++ˡ k xs R eqxs = refl

prefix-++ˡ-perm
  : (ks : List (Fin n)) {xs R rest : List (Fin n)}
  → (xs ++ R) Perm.↭ (ks ++ rest) ++ R
  → (xs ++ R) Perm.↭ ks ++ (rest ++ R)
prefix-++ˡ-perm ks {xs} {R} {rest} q =
  subst (λ z → (xs ++ R) Perm.↭ z) (++-assoc ks rest R) q

extract-prefix-++ˡ
  : (ks xs R : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ ks ++ rest}
  → extract-prefix ks xs ≡ just (rest , p)
  → extract-prefix ks (xs ++ R)
    ≡ just (rest ++ R , prefix-++ˡ-perm ks (PermProp.++⁺ʳ R p))
extract-prefix-++ˡ []       xs R {rest} {p} eq with eq
... | refl = refl
extract-prefix-++ˡ (k ∷ ks) xs R eq with extract-elem k xs in eqe
extract-prefix-++ˡ (k ∷ ks) xs R eq | just (xs' , pe) with extract-prefix ks xs' in eqp
extract-prefix-++ˡ (k ∷ ks) xs R {rest} {p} eq | just (xs' , pe)
  | just (rest' , pp) with eq
... | refl
      rewrite extract-elem-++ˡ k xs R eqe
            | extract-prefix-++ˡ ks xs' R eqp =
      cong (λ z → just (rest' ++ R , z)) perm-eq
  where
    -- The codomain associativity transport slides through prep k.
    perm-eq
      : Perm.trans (PermProp.++⁺ʳ R pe)
          (Perm.prep k (prefix-++ˡ-perm ks {xs'} {R} {rest'} (PermProp.++⁺ʳ R pp)))
        ≡ prefix-++ˡ-perm (k ∷ ks) {xs} {R} {rest'}
            (PermProp.++⁺ʳ R (Perm.trans pe (Perm.prep k pp)))
    perm-eq = gen (++-assoc ks rest' R) (PermProp.++⁺ʳ R pp)
      where
        -- Generalise the equality before eliminating it.
        gen
          : ∀ {a b : List (Fin _)} (e : a ≡ b)
              (Q : (xs' ++ R) Perm.↭ a)
          → Perm.trans (PermProp.++⁺ʳ R pe)
              (Perm.prep k (subst (λ z → (xs' ++ R) Perm.↭ z) e Q))
            ≡ subst (λ z → (xs ++ R) Perm.↭ z) (cong (k ∷_) e)
                (Perm.trans (PermProp.++⁺ʳ R pe) (Perm.prep k Q))
        gen refl Q = refl

-- A failed search may succeed in the right frame unless its key is absent there.
extract-elem-++ˡ-nothing
  : (k : Fin n) (xs R : List (Fin n))
  → extract-elem k xs ≡ nothing
  → extract-elem k R  ≡ nothing
  → extract-elem k (xs ++ R) ≡ nothing
extract-elem-++ˡ-nothing k []       R eqx eqR = eqR
extract-elem-++ˡ-nothing k (x ∷ xs) R eqx eqR with x ≟ k
... | yes refl with eqx
...   | ()
extract-elem-++ˡ-nothing k (x ∷ xs) R eqx eqR | no ¬q with extract-elem k xs in eqxs
... | nothing rewrite extract-elem-++ˡ-nothing k xs R eqxs eqR = refl

extract-prefix-++ˡ-nothing
  : (ks xs R : List (Fin n))
  → All (λ j → extract-elem j R ≡ nothing) ks
  → extract-prefix ks xs ≡ nothing
  → extract-prefix ks (xs ++ R) ≡ nothing
extract-prefix-++ˡ-nothing []       xs R _          ()
extract-prefix-++ˡ-nothing (k ∷ ks) xs R (dk ∷ dks) eqn with extract-elem k xs in eqe
... | nothing rewrite extract-elem-++ˡ-nothing k xs R eqe dk = refl
... | just (xs' , pe) with extract-prefix ks xs' in eqp
...     | nothing
          rewrite extract-elem-++ˡ k xs R eqe
                | extract-prefix-++ˡ-nothing ks xs' R dks eqp = refl
...     | just (_ , _) with eqn
...       | ()

--------------------------------------------------------------------------------
-- Left frames
--------------------------------------------------------------------------------

-- A left frame survives extraction, but prepending fresh outputs afterward
-- moves those outputs before the frame; term-level framing then needs a braid.

extract-elem-++ʳ
  : (k : Fin n) (F xs : List (Fin n))
      {rest : List (Fin n)} {p : xs Perm.↭ k ∷ rest}
  → extract-elem k F ≡ nothing
  → extract-elem k xs ≡ just (rest , p)
  → ∃[ q ] extract-elem k (F ++ xs) ≡ just (F ++ rest , q)
extract-elem-++ʳ k []      xs {rest} {p} eqF eqx = p , eqx
extract-elem-++ʳ k (f ∷ F) xs eqF eqx with f ≟ k
extract-elem-++ʳ k (f ∷ F) xs eqF eqx | yes refl with eqF
... | ()
extract-elem-++ʳ k (f ∷ F) xs eqF eqx | no ¬q with extract-elem k F in eqFi
... | nothing with extract-elem-++ʳ k F xs eqFi eqx
...              | _ , e rewrite e = _ , refl
extract-elem-++ʳ k (f ∷ F) xs eqF eqx | no ¬q | just _ with eqF
... | ()

extract-prefix-++ʳ-nothing
  : (ks F ys : List (Fin n))
  → All (λ k → extract-elem k F ≡ nothing) ks
  → extract-prefix ks ys ≡ nothing
  → extract-prefix ks (F ++ ys) ≡ nothing
extract-prefix-++ʳ-nothing []       F ys _          ()
extract-prefix-++ʳ-nothing (k ∷ ks) F ys (ak ∷ aks) eq with extract-elem k ys in eqe
... | nothing rewrite extract-elem-++ˡ-nothing k F ys ak eqe = refl
... | just (ys' , pe) with extract-prefix ks ys' in eqp
...     | nothing with extract-elem-++ʳ k F ys ak eqe
...        | _ , e-elem
             rewrite e-elem
                   | extract-prefix-++ʳ-nothing ks F ys' aks eqp = refl
extract-prefix-++ʳ-nothing (k ∷ ks) F ys (ak ∷ aks) eq | just (ys' , pe)
    | just (_ , _) with eq
...    | ()
-- The witness is not pinned to Perm.refl: extract-elem uses a subst
-- that does not simplify under --without-K.

extract-elem-self
  : (k : Fin n) (xs : List (Fin n))
  → Σ[ p ∈ ((k ∷ xs) Perm.↭ k ∷ xs) ]
      extract-elem k (k ∷ xs) ≡ just (xs , p)
extract-elem-self k xs with k ≟ k
... | yes a = _ , refl
... | no  q = ⊥-elim (q refl)

extract-elem-skip-nothing
  : (k x : Fin n) (xs : List (Fin n))
  → ¬ (x ≡ k)
  → extract-elem k xs ≡ nothing
  → extract-elem k (x ∷ xs) ≡ nothing
extract-elem-skip-nothing k x xs x≢k eq with x ≟ k
... | yes p = ⊥-elim (x≢k p)
... | no  _ rewrite eq = refl

extract-elem-↑ˡ-on-↑ʳ-list
  : (i : Fin nA) (xs : List (Fin nB))
  → extract-elem (i ↑ˡ nB) (map (nA ↑ʳ_) xs) ≡ nothing
extract-elem-↑ˡ-on-↑ʳ-list i []       = refl
extract-elem-↑ˡ-on-↑ʳ-list {nA} {nB} i (x ∷ xs) =
  extract-elem-skip-nothing (i ↑ˡ nB) (nA ↑ʳ x) (map (nA ↑ʳ_) xs)
    (λ p → ↑ˡ≢↑ʳ i x (sym p))
    (extract-elem-↑ˡ-on-↑ʳ-list i xs)

extract-elem-↑ʳ-on-↑ˡ-list
  : ∀ nA {nB} (j : Fin nB) (xs : List (Fin nA))
  → extract-elem (nA ↑ʳ j) (map (_↑ˡ nB) xs) ≡ nothing
extract-elem-↑ʳ-on-↑ˡ-list nA j []            = refl
extract-elem-↑ʳ-on-↑ˡ-list nA {nB} j (x ∷ xs) =
  extract-elem-skip-nothing (nA ↑ʳ j) (x ↑ˡ nB) (map (_↑ˡ nB) xs)
    (↑ˡ≢↑ʳ x j)
    (extract-elem-↑ʳ-on-↑ˡ-list nA j xs)

-- Duplicates need no uniqueness hypothesis: each head matches itself.
extract-prefix-self
  : (xs : List (Fin n))
  → Σ[ p ∈ (xs Perm.↭ xs ++ []) ] extract-prefix xs xs ≡ just ([] , p)
extract-prefix-self []       = Perm.refl , refl
extract-prefix-self (x ∷ xs) with extract-elem-self x xs
... | p1 , eq1 with extract-prefix-self xs
...               | p2 , eq2 rewrite eq1 | eq2 = _ , refl

--------------------------------------------------------------------------------
-- Injective search liftings
--------------------------------------------------------------------------------

extract-elem-via-injective-nothing
  : (f : Fin n → Fin m)
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
  : (f : Fin n → Fin m)
  → (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ∀ (k : Fin n) (xs rest : List (Fin n)) (p : xs Perm.↭ k ∷ rest)
  → extract-elem k xs ≡ just (rest , p)
  → ∃[ q ] extract-elem (f k) (map f xs) ≡ just (map f rest , q)
extract-elem-via-injective-just f f-inj k xs rest p eq =
  _ , extract-elem-map⁺ f f-inj k xs rest p eq

extract-prefix-via-injective-nothing
  : (f : Fin n → Fin m)
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
  : (f : Fin n → Fin m)
  → (f-inj : ∀ {x y} → f x ≡ f y → x ≡ y)
  → ∀ (ks xs rest : List (Fin n)) (p : xs Perm.↭ ks ++ rest)
  → extract-prefix ks xs ≡ just (rest , p)
  → ∃[ q ] extract-prefix (map f ks) (map f xs) ≡ just (map f rest , q)
extract-prefix-via-injective-just f f-inj ks xs rest p eq =
  _ , extract-prefix-map⁺ f f-inj ks xs rest p eq

--------------------------------------------------------------------------------
-- Disjoint-injection liftings
--------------------------------------------------------------------------------

-- Right frames need no disjointness on success; left frames do.
-- The mixed-list injections discharge the latter side condition.

extract-prefix-↑ˡ-on-mixed-just
  : ∀ nB (ks xs : List (Fin nA)) (ys : List (Fin nB))
      (rest : List (Fin nA)) (p : xs Perm.↭ ks ++ rest)
  → extract-prefix ks xs ≡ just (rest , p)
  → ∃[ q ] extract-prefix (map (_↑ˡ nB) ks)
                          (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
              ≡ just (map (_↑ˡ nB) rest ++ map (nA ↑ʳ_) ys , q)
extract-prefix-↑ˡ-on-mixed-just {nA} nB ks xs ys rest p eq
    with extract-prefix-via-injective-just (_↑ˡ nB) (↑ˡ-injective nB _ _) ks xs rest p eq
... | _ , e =
      _ , extract-prefix-++ˡ (map (_↑ˡ nB) ks) (map (_↑ˡ nB) xs)
            (map (nA ↑ʳ_) ys) e

extract-prefix-↑ˡ-on-mixed-nothing
  : ∀ nB (ks xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-prefix ks xs ≡ nothing
  → extract-prefix (map (_↑ˡ nB) ks)
                   (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
       ≡ nothing
extract-prefix-↑ˡ-on-mixed-nothing {nA} nB ks xs ys eq =
  extract-prefix-++ˡ-nothing (map (_↑ˡ nB) ks) (map (_↑ˡ nB) xs) (map (nA ↑ʳ_) ys)
    (map⁺ (universal (λ k → extract-elem-↑ˡ-on-↑ʳ-list k ys) ks))
    (extract-prefix-via-injective-nothing (_↑ˡ nB) (↑ˡ-injective nB _ _) ks xs eq)

extract-prefix-↑ʳ-on-mixed-nothing
  : ∀ nA {nB} (ks : List (Fin nB)) (xs : List (Fin nA)) (ys : List (Fin nB))
  → extract-prefix ks ys ≡ nothing
  → extract-prefix (map (nA ↑ʳ_) ks)
                   (map (_↑ˡ nB) xs ++ map (nA ↑ʳ_) ys)
       ≡ nothing
extract-prefix-↑ʳ-on-mixed-nothing nA {nB} ks xs ys eq =
  extract-prefix-++ʳ-nothing (map (nA ↑ʳ_) ks) (map (_↑ˡ nB) xs) (map (nA ↑ʳ_) ys)
    (map⁺ (universal (λ k → extract-elem-↑ʳ-on-↑ˡ-list nA k xs) ks))
    (extract-prefix-via-injective-nothing (nA ↑ʳ_) (↑ʳ-injective nA _ _) ks ys eq)

extract-elem-found
  : (y : Fin n) (xs : List (Fin n))
  → y ∈ xs
  → ∃[ rest ] ∃[ p ] extract-elem y xs ≡ just (rest , p)
extract-elem-found y (x ∷ xs) (here refl) with y ≟ y
... | yes _ = _ , _ , refl
... | no  q = ⊥-elim (q refl)
extract-elem-found y (x ∷ xs) (there mem) with x ≟ y
... | yes _   = _ , _ , refl
... | no  q   with extract-elem-found y xs mem
...              | _ , _ , eq rewrite eq = _ , _ , refl

extract-prefix-↭-residual
  : (ks xs rest : List (Fin n))
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

extract-prefix-↭-nothing
  : (ks xs xs' : List (Fin n))
  → xs Perm.↭ xs'
  → extract-prefix ks xs ≡ nothing
  → extract-prefix ks xs' ≡ nothing
extract-prefix-↭-nothing ks xs xs' xs↭xs' eq with extract-prefix ks xs' in eq-xs'
... | nothing             = refl
... | just (rest' , p-xs') with extract-prefix-↭-residual ks xs rest' (Perm.↭-trans xs↭xs' p-xs')
... | _ , _ , eq-xs , _ rewrite eq-xs with eq
... | ()
