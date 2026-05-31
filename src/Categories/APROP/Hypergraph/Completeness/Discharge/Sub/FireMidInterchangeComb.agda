{-# OPTIONS --without-K #-}

--------------------------------------------------------------------------------
-- Combinatorial scaffolding for `Sub/FireMidInterchange.block-nf`.
--
-- The SIMULTANEOUS-LOCATION combinatorics of the both-fire two-edge
-- interchange: from the four locating permutes (and the disjointness given
-- by `Incomp` + `Linear`), we locate BOTH input blocks at once, producing a
-- common residual list `Rlist` and the two "block" locating permutes
--
--   loc₁ : sp ↭ (ein e ++ ein e') ++ Rlist
--   loc₂ : sp ↭ (ein e' ++ ein e) ++ Rlist
--
-- (note: a SINGLE shared `Rlist`, with the two orders differing only by the
-- swap of the two `ein` blocks).  Plus the output reshuffle
--
--   r-stk : eout e' ++ r₂ ↭ eout e ++ r₁'
--
-- (= `AllFireEdgeSwap.post-swap-stack-↭`, re-derived here over the
-- `--without-K`/non-`sig-dec` API).
--
-- All of this is pure `_↭_` / `count` combinatorics; it is FULLY
-- CONSTRUCTIVE and postulate-free.  It is the "located" half of the
-- block-normal-form chase: it tells us WHERE the two boxes' input/output
-- blocks live inside the stack, leaving only the categorical bracketing
-- (`block-nf`'s frame morphisms + `nf₁`/`nf₂`) to the consumer.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Completeness.Discharge.Sub.FireMidInterchangeComb
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Completeness.Decode sig
  using (extract-prefix; extract-elem)
open import Categories.APROP.Hypergraph.Completeness.Linearity sig
  using (Linear; count; count-++; consumedList)

open import Categories.APROP.Hypergraph.Completeness.Discharge.EdgeDependency
  using (Dep)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; map; concat)
open import Data.List.Base using (tabulate)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)

--------------------------------------------------------------------------------
-- ## Generic `count` / `extract-prefix` combinatorics (H-agnostic), copied
-- VERBATIM from `RunInterchangeEmptyTail.agda` (which itself copied them from
-- `SwapValidity.agda`'s inaccessible `private` block).  All `--without-K`-clean.

private
  variable
    n : ℕ

  nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
  nothing≢just ()

  count-cons-yes : (v : Fin n) (xs : List (Fin n))
                 → count v (v ∷ xs) ≡ suc (count v xs)
  count-cons-yes v xs with v ≟ v
  ... | yes _ = refl
  ... | no  q = ⊥-elim (q refl)

  count-cons-no : (v x : Fin n) (xs : List (Fin n)) → ¬ (v ≡ x)
                → count v (x ∷ xs) ≡ count v xs
  count-cons-no v x xs v≢x with v ≟ x
  ... | yes p = ⊥-elim (v≢x p)
  ... | no  _ = refl

  ∈→count-pos : ∀ {v : Fin n} {xs} → v ∈ xs → 0 <ⁿ count v xs
  ∈→count-pos {v = v} {x ∷ xs} (here refl)  rewrite count-cons-yes v xs = s≤sⁿ z≤nⁿ
  ∈→count-pos {v = v} {x ∷ xs} (there v∈xs) with v ≟ x
  ... | yes _ = s≤sⁿ z≤nⁿ
  ... | no  _ = ∈→count-pos v∈xs

  count-pos→∈ : ∀ {v : Fin n} {xs} → 0 <ⁿ count v xs → v ∈ xs
  count-pos→∈ {v = v} {[]}     ()
  count-pos→∈ {v = v} {x ∷ xs} c with v ≟ x
  ... | yes refl = here refl
  ... | no  _    = there (count-pos→∈ c)

  ↭⇒count : {xs ys : List (Fin n)} → xs Perm.↭ ys → ∀ v → count v xs ≡ count v ys
  ↭⇒count Perm.refl                       v = refl
  ↭⇒count (Perm.prep x p)                 v with v ≟ x
  ... | yes _ = cong suc (↭⇒count p v)
  ... | no  _ = ↭⇒count p v
  ↭⇒count (Perm.swap {xs = xs} {ys = ys} x y p) v = swap-case (v ≟ x) (v ≟ y)
    where
      swap-case : _ → _ → count v (x ∷ y ∷ xs) ≡ count v (y ∷ x ∷ ys)
      swap-case (yes refl) (yes refl) =
        trans (count-cons-yes v (v ∷ xs))
        (trans (cong suc (count-cons-yes v xs))
        (trans (cong suc (cong suc (↭⇒count p v)))
        (trans (cong suc (sym (count-cons-yes v ys)))
               (sym (count-cons-yes v (v ∷ ys))))))
      swap-case (yes refl) (no  q) =
        trans (count-cons-yes v (y ∷ xs))
        (trans (cong suc (count-cons-no v y xs q))
        (trans (cong suc (↭⇒count p v))
        (trans (sym (count-cons-yes v ys))
               (sym (count-cons-no v y (v ∷ ys) q)))))
      swap-case (no  q) (yes refl) =
        trans (count-cons-no v x (v ∷ xs) q)
        (trans (count-cons-yes v xs)
        (trans (cong suc (↭⇒count p v))
        (trans (cong suc (sym (count-cons-no v x ys q)))
               (sym (count-cons-yes v (x ∷ ys))))))
      swap-case (no  q₁) (no  q₂) =
        trans (count-cons-no v x (y ∷ xs) q₁)
        (trans (count-cons-no v y xs q₂)
        (trans (↭⇒count p v)
        (trans (sym (count-cons-no v x ys q₁))
               (sym (count-cons-no v y (x ∷ ys) q₂)))))
  ↭⇒count (Perm.trans p₁ p₂)              v = trans (↭⇒count p₁ v) (↭⇒count p₂ v)

  count-pos→extract-elem
    : (k : Fin n) (xs : List (Fin n)) → 0 <ⁿ count k xs
    → Σ[ rest ∈ List (Fin n) ] Σ[ p ∈ xs Perm.↭ k ∷ rest ]
        extract-elem k xs ≡ just (rest , p)
  count-pos→extract-elem k []       ()
  count-pos→extract-elem k (x ∷ xs) c with x ≟ k
  ... | yes refl = xs , _ , refl
  ... | no  x≢k  with count-pos→extract-elem k xs
                      (subst (0 <ⁿ_) (count-cons-no k x xs (λ e → x≢k (sym e))) c)
  ...   | rest , p , eq rewrite eq = x ∷ rest , _ , refl

  count-≤→extract-prefix
    : (ks xs : List (Fin n)) → (∀ v → count v ks ≤ⁿ count v xs)
    → Σ[ rest ∈ List (Fin n) ] Σ[ p ∈ xs Perm.↭ ks ++ rest ]
        extract-prefix ks xs ≡ just (rest , p)
  count-≤→extract-prefix []       xs h = xs , Perm.refl , refl
  count-≤→extract-prefix (k ∷ ks) xs h
    with count-pos→extract-elem k xs
           (Nat.<-≤-trans (s≤sⁿ z≤nⁿ)
             (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks))) (h k)))
  ... | xs' , p , eq-elem
      with count-≤→extract-prefix ks xs' h-rest
    where
      h-rest : ∀ v → count v ks ≤ⁿ count v xs'
      h-rest v with v ≟ k
      ... | yes refl =
            s≤s⁻¹
              (Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-yes k ks)))
              (Nat.≤-trans (h k)
                           (Nat.≤-reflexive
                             (trans (↭⇒count p k) (count-cons-yes k xs')))))
      ... | no  v≢k =
            Nat.≤-trans (Nat.≤-reflexive (sym (count-cons-no v k ks v≢k)))
            (Nat.≤-trans (h v)
                         (Nat.≤-reflexive
                           (trans (↭⇒count p v) (count-cons-no v k xs' v≢k))))
  ...   | rest , q , eq-rest rewrite eq-elem | eq-rest =
          rest , _ , refl

  count-concat-tabulate-≤
    : ∀ {nE} (f : Fin nE → List (Fin n)) (e : Fin nE) (v : Fin n)
    → count v (f e) ≤ⁿ count v (concat (tabulate f))
  count-concat-tabulate-≤ f zero    v =
    Nat.≤-trans (Nat.m≤m+n _ _)
                (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
  count-concat-tabulate-≤ f (suc e) v =
    Nat.≤-trans (count-concat-tabulate-≤ (λ i → f (suc i)) e v)
                (Nat.≤-trans (Nat.m≤n+m _ _)
                             (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

  count-concat-tabulate-pair-≤
    : ∀ {nE} (f : Fin nE → List (Fin n)) (e e' : Fin nE) → ¬ (e ≡ e')
    → (v : Fin n)
    → count v (f e) + count v (f e') ≤ⁿ count v (concat (tabulate f))
  count-concat-tabulate-pair-≤ f zero    zero     e≢e' v = ⊥-elim (e≢e' refl)
  count-concat-tabulate-pair-≤ f zero    (suc e') e≢e' v =
    Nat.≤-trans
      (Nat.+-monoʳ-≤ (count v (f zero))
                     (count-concat-tabulate-≤ (λ i → f (suc i)) e' v))
      (Nat.≤-reflexive (sym (count-++ v (f zero) _)))
  count-concat-tabulate-pair-≤ f (suc e) zero     e≢e' v =
    Nat.≤-trans
      (Nat.≤-reflexive (Nat.+-comm (count v (f (suc e))) (count v (f zero))))
      (Nat.≤-trans
        (Nat.+-monoʳ-≤ (count v (f zero))
                       (count-concat-tabulate-≤ (λ i → f (suc i)) e v))
        (Nat.≤-reflexive (sym (count-++ v (f zero) _))))
  count-concat-tabulate-pair-≤ f (suc e) (suc e')  e≢e' v =
    Nat.≤-trans
      (count-concat-tabulate-pair-≤ (λ i → f (suc i)) e e'
        (λ eq → e≢e' (cong suc eq)) v)
      (Nat.≤-trans (Nat.m≤n+m _ _)
                   (Nat.≤-reflexive (sym (count-++ v (f zero) _))))

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (dih : ∀ {e} → ¬ (Dep H e e))
         (lin : Linear H)
         where
  private module H = Hypergraph H

  ----------------------------------------------------------------------
  -- ## Disjointness from `Linear` + `Incomp`, copied from
  -- `RunInterchangeEmptyTail.agda`'s `private` block.
  ----------------------------------------------------------------------

  private
    consume-bnd : ∀ (v : Fin H.nV) → count v (consumedList H) ≤ⁿ 1
    consume-bnd v = subst (_≤ⁿ 1) (proj₁ lin v) (proj₂ lin v)

    ein-concat-bnd : ∀ (v : Fin H.nV)
                   → count v (concat (tabulate H.ein)) ≤ⁿ 1
    ein-concat-bnd v =
      Nat.≤-trans
        (Nat.≤-trans (Nat.m≤n+m _ (count v H.cod))
                     (Nat.≤-reflexive (sym (count-++ v H.cod _))))
        (consume-bnd v)

  -- `ein e ⊥ ein e'` (Linear): no vertex is consumed by two distinct edges.
  ein-ein-disjoint
    : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → (v : Fin H.nV)
    → 0 <ⁿ count v (H.ein e) → count v (H.ein e') ≡ 0
  ein-ein-disjoint {e} {e'} e≢e' v v∈ein-e =
    Nat.n≤0⇒n≡0
      (s≤s⁻¹
        (Nat.≤-trans
          (Nat.+-monoˡ-≤ (count v (H.ein e')) v∈ein-e)
          (Nat.≤-trans (count-concat-tabulate-pair-≤ H.ein e e' e≢e' v)
                       (ein-concat-bnd v))))

  -- `eout e ⊥ ein e'` (Incomp / ¬Dep): `e` does not produce a wire `e'`
  -- consumes.
  eout-ein-disjoint
    : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e') → (v : Fin H.nV)
    → 0 <ⁿ count v (H.ein e') → count v (H.eout e) ≡ 0
  eout-ein-disjoint {e} {e'} ¬dep v v∈ein-e' =
    Nat.n≤0⇒n≡0
      (Nat.≮⇒≥ λ v∈eout-e →
        ¬dep (v , count-pos→∈ v∈eout-e , count-pos→∈ v∈ein-e'))

  ----------------------------------------------------------------------
  -- ## Extracting `ein e'` from the residual `r₁`.
  --
  -- From `p₂ : eout e ++ r₁ ↭ ein e' ++ r₂` plus `eout e ⊥ ein e'`, every
  -- vertex of `ein e'` lives in `r₁` (not in `eout e`).  Hence `ein e'`
  -- is a count-prefix of `r₁`, so we can extract a residual `Rlist` with
  -- `r₁ ↭ ein e' ++ Rlist`.
  ----------------------------------------------------------------------

  -- `count v (ein e') ≤ count v r₁` for all `v`, using disjointness of
  -- `eout e` with `ein e'`.
  ein'-≤-r₁
    : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e')
    → (r₁ r₂ : List (Fin H.nV)) → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → ∀ v → count v (H.ein e') ≤ⁿ count v r₁
  ein'-≤-r₁ {e} {e'} ¬dep r₁ r₂ p₂ v with count-pos-or-zero v
    where
      count-pos-or-zero : (v : Fin H.nV)
                        → (0 <ⁿ count v (H.ein e')) ⊎ (count v (H.ein e') ≡ 0)
      count-pos-or-zero v with count v (H.ein e')
      ... | zero  = inj₂ refl
      ... | suc _ = inj₁ (s≤sⁿ z≤nⁿ)
  ... | inj₂ z   = subst (_≤ⁿ count v r₁) (sym z) z≤nⁿ
  ... | inj₁ pos =
        -- count v (eout e) + count v r₁ = count v (ein e') + count v r₂,
        -- and count v (eout e) ≡ 0, so count v (ein e') ≤ count v r₁.
        Nat.≤-trans (Nat.m≤m+n (count v (H.ein e')) (count v r₂))
        (Nat.≤-reflexive
          (trans (sym (count-++ v (H.ein e') r₂))
          (trans (sym (↭⇒count p₂ v))
          (trans (count-++ v (H.eout e) r₁)
                 (trans (cong (_+ count v r₁) (eout-ein-disjoint ¬dep v pos))
                        refl)))))

  -- Extract `ein e'` from `r₁`.
  extract-ein'
    : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e')
    → (r₁ r₂ : List (Fin H.nV)) → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → Σ[ Rlist ∈ List (Fin H.nV) ] (r₁ Perm.↭ H.ein e' ++ Rlist)
  extract-ein' {e} {e'} ¬dep r₁ r₂ p₂ =
    let rest , q , _ = count-≤→extract-prefix (H.ein e') r₁ (ein'-≤-r₁ ¬dep r₁ r₂ p₂)
    in rest , q

  ----------------------------------------------------------------------
  -- ## Simultaneous location.
  --
  -- For the BOTH-FIRE order `e ∷ e'`, with the residual `Rlist` extracted
  -- above, the input stack `sp` locates BOTH input blocks at once:
  --
  --   loc₁ : sp ↭ (ein e ++ ein e') ++ Rlist.
  ----------------------------------------------------------------------

  -- The block-located permute for the `e ∷ e'` order, with residual
  -- `Rlist`: `sp ↭ (ein e ++ ein e') ++ Rlist`.
  block-loc-e
    : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e')
    → (sp r₁ r₂ : List (Fin H.nV))
    → sp Perm.↭ H.ein e ++ r₁
    → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → (Rlist : List (Fin H.nV))
    → r₁ Perm.↭ H.ein e' ++ Rlist
    → sp Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
  block-loc-e {e} {e'} ¬dep sp r₁ r₂ p₁ p₂ Rlist q₁ = loc
    where
      open Perm.PermutationReasoning
      loc : sp Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
      loc = begin
        sp                                   ↭⟨ p₁ ⟩
        H.ein e ++ r₁                        ↭⟨ PermProp.++⁺ˡ (H.ein e) q₁ ⟩
        H.ein e ++ H.ein e' ++ Rlist         ≡⟨ sym (++-assoc (H.ein e) (H.ein e') Rlist) ⟩
        (H.ein e ++ H.ein e') ++ Rlist       ∎

  ----------------------------------------------------------------------
  -- ## The output reshuffle (= `AllFireEdgeSwap.post-swap-stack-↭`,
  -- re-derived here over the `--without-K` API).
  ----------------------------------------------------------------------

  private
    ++-cancelˡ
      : ∀ (xs : List (Fin H.nV)) {ys zs : List (Fin H.nV)}
      → xs ++ ys Perm.↭ xs ++ zs
      → ys Perm.↭ zs
    ++-cancelˡ []       p = p
    ++-cancelˡ (x ∷ xs) p = ++-cancelˡ xs (PermProp.drop-∷ p)

  -- The output reshuffle between the two final stacks.
  post-swap-stack-↭
    : ∀ (e₁ e₂ : Fin H.nE)
        (sp r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : sp Perm.↭ H.ein e₁ ++ r₁)
        (p₂  : H.eout e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂)
        (p₂' : sp Perm.↭ H.ein e₂ ++ r₂')
        (p₁' : H.eout e₂ ++ r₂' Perm.↭ H.ein e₁ ++ r₁')
    → H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
  post-swap-stack-↭ e₁ e₂ sp r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁' = cancelled
    where
      open Perm.PermutationReasoning

      r₁-r₂' : H.ein e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂'
      r₁-r₂' = Perm.↭-trans (Perm.↭-sym p₁) p₂'

      step-A : H.eout e₂ ++ H.eout e₁ ++ r₁ Perm.↭ H.eout e₂ ++ H.ein e₂ ++ r₂
      step-A = PermProp.++⁺ˡ (H.eout e₂) p₂

      step-B : H.eout e₂ ++ H.ein e₂ ++ r₂ Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂
      step-B = begin
        H.eout e₂ ++ H.ein e₂ ++ r₂
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₂) r₂) ⟩
        (H.eout e₂ ++ H.ein e₂) ++ r₂
          ↭⟨ PermProp.++⁺ʳ r₂ (PermProp.++-comm (H.eout e₂) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₂) ++ r₂
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₂) r₂ ⟩
        H.ein e₂ ++ H.eout e₂ ++ r₂ ∎

      step-C : H.eout e₂ ++ H.eout e₁ ++ r₁ Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂
      step-C = Perm.↭-trans step-A step-B

      step-A' : H.eout e₁ ++ H.eout e₂ ++ r₂' Perm.↭ H.eout e₁ ++ H.ein e₁ ++ r₁'
      step-A' = PermProp.++⁺ˡ (H.eout e₁) p₁'

      step-B' : H.eout e₁ ++ H.ein e₁ ++ r₁' Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      step-B' = begin
        H.eout e₁ ++ H.ein e₁ ++ r₁'
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₁) r₁') ⟩
        (H.eout e₁ ++ H.ein e₁) ++ r₁'
          ↭⟨ PermProp.++⁺ʳ r₁' (PermProp.++-comm (H.eout e₁) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₁) ++ r₁'
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₁) r₁' ⟩
        H.ein e₁ ++ H.eout e₁ ++ r₁' ∎

      step-C' : H.eout e₁ ++ H.eout e₂ ++ r₂' Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      step-C' = Perm.↭-trans step-A' step-B'

      mult-r₁-r₂'
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
        Perm.↭ H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
      mult-r₁-r₂' =
        PermProp.++⁺ˡ (H.eout e₁) (PermProp.++⁺ˡ (H.eout e₂) r₁-r₂')

      inner-lhs : H.eout e₁ ++ H.ein e₁ ++ r₁ Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁
      inner-lhs = begin
        H.eout e₁ ++ H.ein e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₁) r₁) ⟩
        (H.eout e₁ ++ H.ein e₁) ++ r₁
          ↭⟨ PermProp.++⁺ʳ r₁ (PermProp.++-comm (H.eout e₁) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₁) ++ r₁
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₁) r₁ ⟩
        H.ein e₁ ++ H.eout e₁ ++ r₁ ∎

      inner-lhs-2
        : H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
      inner-lhs-2 = begin
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₁) (H.eout e₁ ++ r₁)) ⟩
        (H.eout e₂ ++ H.ein e₁) ++ H.eout e₁ ++ r₁
          ↭⟨ PermProp.++⁺ʳ (H.eout e₁ ++ r₁)
                            (PermProp.++-comm (H.eout e₂) (H.ein e₁)) ⟩
        (H.ein e₁ ++ H.eout e₂) ++ H.eout e₁ ++ r₁
          ≡⟨ ++-assoc (H.ein e₁) (H.eout e₂) (H.eout e₁ ++ r₁) ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁ ∎

      lhs-rearrange
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
        Perm.↭ H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
      lhs-rearrange = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₁ ++ r₁
          ≡⟨ sym (++-assoc (H.eout e₁) (H.eout e₂) (H.ein e₁ ++ r₁)) ⟩
        (H.eout e₁ ++ H.eout e₂) ++ H.ein e₁ ++ r₁
          ↭⟨ PermProp.++⁺ʳ (H.ein e₁ ++ r₁)
                            (PermProp.++-comm (H.eout e₁) (H.eout e₂)) ⟩
        (H.eout e₂ ++ H.eout e₁) ++ H.ein e₁ ++ r₁
          ≡⟨ ++-assoc (H.eout e₂) (H.eout e₁) (H.ein e₁ ++ r₁) ⟩
        H.eout e₂ ++ H.eout e₁ ++ H.ein e₁ ++ r₁
          ↭⟨ PermProp.++⁺ˡ (H.eout e₂) inner-lhs ⟩
        H.eout e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁
          ↭⟨ inner-lhs-2 ⟩
        H.ein e₁ ++ H.eout e₂ ++ H.eout e₁ ++ r₁
          ↭⟨ PermProp.++⁺ˡ (H.ein e₁) step-C ⟩
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂ ∎

      inner-rhs-inner : H.eout e₂ ++ H.ein e₂ ++ r₂' Perm.↭ H.ein e₂ ++ H.eout e₂ ++ r₂'
      inner-rhs-inner = begin
        H.eout e₂ ++ H.ein e₂ ++ r₂'
          ≡⟨ sym (++-assoc (H.eout e₂) (H.ein e₂) r₂') ⟩
        (H.eout e₂ ++ H.ein e₂) ++ r₂'
          ↭⟨ PermProp.++⁺ʳ r₂' (PermProp.++-comm (H.eout e₂) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₂) ++ r₂'
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₂) r₂' ⟩
        H.ein e₂ ++ H.eout e₂ ++ r₂' ∎

      inner-rhs-1
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
      inner-rhs-1 = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ˡ (H.eout e₁) inner-rhs-inner ⟩
        H.eout e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂'
          ≡⟨ sym (++-assoc (H.eout e₁) (H.ein e₂) (H.eout e₂ ++ r₂')) ⟩
        (H.eout e₁ ++ H.ein e₂) ++ H.eout e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ʳ (H.eout e₂ ++ r₂')
                            (PermProp.++-comm (H.eout e₁) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.eout e₁) ++ H.eout e₂ ++ r₂'
          ≡⟨ ++-assoc (H.ein e₂) (H.eout e₁) (H.eout e₂ ++ r₂') ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂' ∎

      rhs-rearrange
        : H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      rhs-rearrange = begin
        H.eout e₁ ++ H.eout e₂ ++ H.ein e₂ ++ r₂'
          ↭⟨ inner-rhs-1 ⟩
        H.ein e₂ ++ H.eout e₁ ++ H.eout e₂ ++ r₂'
          ↭⟨ PermProp.++⁺ˡ (H.ein e₂) step-C' ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁' ∎

      ein-aligned
        : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      ein-aligned =
        Perm.↭-trans (Perm.↭-sym lhs-rearrange)
        (Perm.↭-trans mult-r₁-r₂' rhs-rearrange)

      ein-comm
        : H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
      ein-comm = begin
        H.ein e₁ ++ H.ein e₂ ++ H.eout e₂ ++ r₂
          ≡⟨ sym (++-assoc (H.ein e₁) (H.ein e₂) (H.eout e₂ ++ r₂)) ⟩
        (H.ein e₁ ++ H.ein e₂) ++ H.eout e₂ ++ r₂
          ↭⟨ PermProp.++⁺ʳ (H.eout e₂ ++ r₂) (PermProp.++-comm (H.ein e₁) (H.ein e₂)) ⟩
        (H.ein e₂ ++ H.ein e₁) ++ H.eout e₂ ++ r₂
          ≡⟨ ++-assoc (H.ein e₂) (H.ein e₁) (H.eout e₂ ++ r₂) ⟩
        H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂ ∎

      common
        : H.ein e₂ ++ H.ein e₁ ++ H.eout e₂ ++ r₂
        Perm.↭ H.ein e₂ ++ H.ein e₁ ++ H.eout e₁ ++ r₁'
      common = Perm.↭-trans (Perm.↭-sym ein-comm) ein-aligned

      cancelled-1
        : H.ein e₁ ++ H.eout e₂ ++ r₂ Perm.↭ H.ein e₁ ++ H.eout e₁ ++ r₁'
      cancelled-1 = ++-cancelˡ (H.ein e₂) common

      cancelled : H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
      cancelled = ++-cancelˡ (H.ein e₁) cancelled-1

  ----------------------------------------------------------------------
  -- ## The packaged simultaneous-location data for the both-fire pair.
  --
  -- A single `Rlist` (shared by both orders), the two block-located
  -- input permutes (differing only by the `ein` block swap), and the
  -- output reshuffle.
  ----------------------------------------------------------------------

  -- From `p₂ : eout e ++ r₁ ↭ ein e' ++ r₂` and `q₁ : r₁ ↭ ein e' ++ Rlist`,
  -- the e-output residual is `r₂ ↭ eout e ++ Rlist`.
  eout-residual
    : ∀ {e e' : Fin H.nE}
    → (r₁ r₂ Rlist : List (Fin H.nV))
    → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → r₁ Perm.↭ H.ein e' ++ Rlist
    → r₂ Perm.↭ H.eout e ++ Rlist
  eout-residual {e} {e'} r₁ r₂ Rlist p₂ q₁ =
    Perm.↭-sym (++-cancelˡ (H.ein e') (Perm.↭-trans shifted p₂))
    where
      open Perm.PermutationReasoning
      -- ein e' ++ eout e ++ Rlist ↭ eout e ++ ein e' ++ Rlist ↭ eout e ++ r₁
      shifted : H.ein e' ++ H.eout e ++ Rlist Perm.↭ H.eout e ++ r₁
      shifted = begin
        H.ein e' ++ H.eout e ++ Rlist
          ↭⟨ PermProp.shifts (H.ein e') (H.eout e) ⟩
        H.eout e ++ H.ein e' ++ Rlist
          ↭⟨ PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym q₁) ⟩
        H.eout e ++ r₁ ∎

  -- The output-located permute for the e-first order's final stack:
  -- `(eout e ++ eout e') ++ Rlist ↭ eout e' ++ r₂`.
  vout-loc-e
    : ∀ {e e' : Fin H.nE}
    → (r₁ r₂ Rlist : List (Fin H.nV))
    → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → r₁ Perm.↭ H.ein e' ++ Rlist
    → (H.eout e ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
  vout-loc-e {e} {e'} r₁ r₂ Rlist p₂ q₁ = goal
    where
      open Perm.PermutationReasoning
      r₂-eq : r₂ Perm.↭ H.eout e ++ Rlist
      r₂-eq = eout-residual {e} {e'} r₁ r₂ Rlist p₂ q₁
      goal : (H.eout e ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
      goal = begin
        (H.eout e ++ H.eout e') ++ Rlist
          ≡⟨ ++-assoc (H.eout e) (H.eout e') Rlist ⟩
        H.eout e ++ H.eout e' ++ Rlist
          ↭⟨ PermProp.shifts (H.eout e) (H.eout e') ⟩
        H.eout e' ++ H.eout e ++ Rlist
          ↭⟨ PermProp.++⁺ˡ (H.eout e') (Perm.↭-sym r₂-eq) ⟩
        H.eout e' ++ r₂ ∎

  record SimLoc
    {e e' : Fin H.nE} (¬dep-ee' : ¬ (Dep H e e')) (¬dep-e'e : ¬ (Dep H e' e))
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    : Set where
    field
      Rlist     : List (Fin H.nV)
      loc₁      : sp Perm.↭ (H.ein e  ++ H.ein e') ++ Rlist
      loc₂      : sp Perm.↭ (H.ein e' ++ H.ein e ) ++ Rlist
      vout-loc₁ : (H.eout e  ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
      vout-loc₂ : (H.eout e' ++ H.eout e ) ++ Rlist Perm.↭ H.eout e  ++ r₁'
      r-stk     : H.eout e' ++ r₂ Perm.↭ H.eout e ++ r₁'

  sim-loc
    : ∀ {e e' : Fin H.nE} (¬dep-ee' : ¬ (Dep H e e')) (¬dep-e'e : ¬ (Dep H e' e))
        (sp : List (Fin H.nV))
        (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
        (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
        (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
        (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    → SimLoc ¬dep-ee' ¬dep-e'e sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁'
  sim-loc {e} {e'} ¬dep-ee' ¬dep-e'e sp r₁ p₁ r₂ p₂ r₂' p₂' r₁' p₁' =
    record
      { Rlist = Rlist ; loc₁ = loc₁ ; loc₂ = loc₂'-bridged
      ; vout-loc₁ = vout-loc₁ ; vout-loc₂ = vout-loc₂-bridged
      ; r-stk = r-stk }
    where
      open Perm.PermutationReasoning

      -- Residual for the e-first order.
      Rlist : List (Fin H.nV)
      Rlist = proj₁ (extract-ein' ¬dep-ee' r₁ r₂ p₂)
      q₁ : r₁ Perm.↭ H.ein e' ++ Rlist
      q₁ = proj₂ (extract-ein' ¬dep-ee' r₁ r₂ p₂)

      loc₁ : sp Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
      loc₁ = block-loc-e ¬dep-ee' sp r₁ r₂ p₁ p₂ Rlist q₁

      vout-loc₁ : (H.eout e ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
      vout-loc₁ = vout-loc-e {e} {e'} r₁ r₂ Rlist p₂ q₁

      -- Residual for the e'-first order.
      Rlist' : List (Fin H.nV)
      Rlist' = proj₁ (extract-ein' ¬dep-e'e r₂' r₁' p₁')
      q₂' : r₂' Perm.↭ H.ein e ++ Rlist'
      q₂' = proj₂ (extract-ein' ¬dep-e'e r₂' r₁' p₁')

      loc₂' : sp Perm.↭ (H.ein e' ++ H.ein e) ++ Rlist'
      loc₂' = block-loc-e ¬dep-e'e sp r₂' r₁' p₂' p₁' Rlist' q₂'

      vout-loc₂' : (H.eout e' ++ H.eout e) ++ Rlist' Perm.↭ H.eout e ++ r₁'
      vout-loc₂' = vout-loc-e {e'} {e} r₂' r₁' Rlist' p₁' q₂'

      -- The two residuals are perm-equal: align the `ein` prefixes via
      -- `++-comm`, then cancel.
      prefix-comm
        : (H.ein e' ++ H.ein e) ++ Rlist' Perm.↭ (H.ein e ++ H.ein e') ++ Rlist'
      prefix-comm = PermProp.++⁺ʳ Rlist' (PermProp.++-comm (H.ein e') (H.ein e))

      Rlist'-Rlist : Rlist' Perm.↭ Rlist
      Rlist'-Rlist =
        ++-cancelˡ (H.ein e ++ H.ein e')
          (Perm.↭-trans (Perm.↭-sym prefix-comm)
            (Perm.↭-trans (Perm.↭-sym loc₂') loc₁))

      loc₂'-bridged : sp Perm.↭ (H.ein e' ++ H.ein e) ++ Rlist
      loc₂'-bridged =
        Perm.↭-trans loc₂' (PermProp.++⁺ˡ (H.ein e' ++ H.ein e) Rlist'-Rlist)

      vout-loc₂-bridged : (H.eout e' ++ H.eout e) ++ Rlist Perm.↭ H.eout e ++ r₁'
      vout-loc₂-bridged =
        Perm.↭-trans (PermProp.++⁺ˡ (H.eout e' ++ H.eout e) (Perm.↭-sym Rlist'-Rlist))
                     vout-loc₂'

      r-stk : H.eout e' ++ r₂ Perm.↭ H.eout e ++ r₁'
      r-stk = post-swap-stack-↭ e e' sp r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'
