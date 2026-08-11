{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- The simultaneous-location combinatorics of the both-fire two-edge
-- interchange.
-- From the four locating permutes (plus disjointness from `Incomp` + `Linear`)
-- it locates BOTH input blocks at once, producing a single shared residual
-- `Rlist` with
--
--   loc₁ : sp ↭ (ein e ++ ein e') ++ Rlist
--   loc₂ : sp ↭ (ein e' ++ ein e) ++ Rlist
--
-- (the two orders differing only by the `ein` block swap) plus the output
-- reshuffle `r-stk : eout e' ++ r₂ ↭ eout e ++ r₁'`.  Pure `_↭_` / `count`
-- combinatorics; the categorical bracketing is left to the consumer.
--------------------------------------------------------------------------------

open import Categories.APROP

module Categories.APROP.Hypergraph.Soundness.Discharge.FireMidInterchangeComb
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.APROP.Hypergraph.Soundness.Decode.Decode sig
  using (extract-prefix)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear; count; count-++; consumedList)

open import Categories.APROP.Hypergraph.Soundness.Discharge.EdgeDependency using (Dep)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; _++_; concat)
open import Data.List.Base using (tabulate)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Ext using (nothing≢just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Categories.APROP.Hypergraph.Soundness.Discharge.CountCombinatorics sig
  using ( ↭⇒count; count-≡⇒↭; count-pos→∈; count-≤→extract-prefix; ++-cancelˡ
        ; count-++-bndʳ
        ; extract-prefix-just→count-≤
        ; count-concat-tabulate-pair-≤)

private
  variable
    n : ℕ

  -- A four-summand ℕ rearrangement (used to reshuffle the count identity
  -- below): `(a + b) + (c + d) ≡ (a + d) + (c + b)`.
  mid4 : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + d) + (c + b)
  mid4 a b c d =
    trans (Nat.+-assoc a b (c + d))
    (trans (cong (a +_) (Nat.+-comm b (c + d)))
    (trans (cong (λ z → a + (z + b)) (Nat.+-comm c d))
    (trans (cong (a +_) (Nat.+-assoc d c b))
           (sym (Nat.+-assoc a d (c + b))))))

  -- The scalar (per-vertex) core of `post-swap-stack-↭`: the three count
  -- identities coming from the four locating permutes force `q + y ≡ p + y'`
  -- by right-cancelling the common `b + x'`.
  scalar
    : ∀ (a b p q x y x' y' : ℕ)
    → a + x ≡ b + x'          -- from p₁ , p₂'
    → p + x ≡ b + y           -- from p₂
    → q + x' ≡ a + y'         -- from p₁'
    → q + y ≡ p + y'
  scalar a b p q x y x' y' I II III =
    Nat.+-cancelʳ-≡ (b + x') (q + y) (p + y')
      (trans (mid4 q y b x')
      (trans (cong₂ _+_ III (sym II))
      (trans (mid4 a y' p x)
      (trans (Nat.+-comm (a + x) (p + y'))
             (cong (p + y' +_) I)))))

--------------------------------------------------------------------------------

module _ (H : Hypergraph FlatGen)
         (lin : Linear H)
         where
  private module H = Hypergraph H

  ----------------------------------------------------------------------
  -- Disjointness from `Linear` + `Incomp`.
  ----------------------------------------------------------------------

  private
    consume-bnd : ∀ (v : Fin H.nV) → count v (consumedList H) ≤ⁿ 1
    consume-bnd v = subst (_≤ⁿ 1) (proj₁ lin v) (proj₂ lin v)

    ein-concat-bnd : ∀ (v : Fin H.nV) → count v (concat (tabulate H.ein)) ≤ⁿ 1
    ein-concat-bnd v = count-++-bndʳ v H.cod _ (consume-bnd v)

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
  -- FIRING STABILITY (Linear + Incomp): `e'`'s firing decision is the
  -- same on `s` and on the post-`e` stack `eout e ++ r₁`, since for every
  -- vertex consumed by `e'` the count is unchanged across the `e`-step
  -- (`count v (ein e) ≡ 0` by Linearity, `count v (eout e) ≡ 0` by Incomp).
  ----------------------------------------------------------------------

  private
    count-ein'-pres
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → (v : Fin H.nV) → 0 <ⁿ count v (H.ein e')
      → count v s ≡ count v (H.eout e ++ r₁)
    count-ein'-pres {e} {e'} e≢e' ¬dep r₁ s p v v∈ein-e' =
      trans (↭⇒count p v)
      (trans (count-++ v (H.ein e) r₁)
      (trans (cong (_+ count v r₁)
                   (ein-ein-disjoint (λ eq → e≢e' (sym eq)) v v∈ein-e'))
      (sym (trans (count-++ v (H.eout e) r₁)
                  (cong (_+ count v r₁) (eout-ein-disjoint ¬dep v v∈ein-e'))))))

    count-zero-or-pos : (e' : Fin H.nE) (v : Fin H.nV)
                      → (count v (H.ein e') ≡ 0) ⊎ (0 <ⁿ count v (H.ein e'))
    count-zero-or-pos e' v with count v (H.ein e')
    ... | zero  = inj₁ refl
    ... | suc _ = inj₂ (s≤sⁿ z≤nⁿ)

    -- Transport an `ein e'`-count bound between two stacks whose `ein e'`
    -- counts agree on every vertex `e'` actually consumes.  Both firing-
    -- stability directions (`s` ⇆ `eout e ++ r₁`) are this one lemma; the
    -- zero-count vertices are bounded by `z≤n` on either side.
    ein'-≤-transport
      : ∀ {e' : Fin H.nE} (v : Fin H.nV) (T U : List (Fin H.nV))
      → (0 <ⁿ count v (H.ein e') → count v T ≡ count v U)
      → count v (H.ein e') ≤ⁿ count v T → count v (H.ein e') ≤ⁿ count v U
    ein'-≤-transport {e'} v T U eq h with count-zero-or-pos e' v
    ... | inj₁ z   = subst (_≤ⁿ count v U) (sym z) z≤nⁿ
    ... | inj₂ pos = subst (count v (H.ein e') ≤ⁿ_) (eq pos) h

    ein'-≤-fwd
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → (∀ v → count v (H.ein e') ≤ⁿ count v s)
      → (∀ v → count v (H.ein e') ≤ⁿ count v (H.eout e ++ r₁))
    ein'-≤-fwd {e} {e'} e≢e' ¬dep r₁ s p h v =
      ein'-≤-transport v s (H.eout e ++ r₁)
        (count-ein'-pres e≢e' ¬dep r₁ s p v) (h v)

    ein'-≤-bwd
      : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → (∀ v → count v (H.ein e') ≤ⁿ count v (H.eout e ++ r₁))
      → (∀ v → count v (H.ein e') ≤ⁿ count v s)
    ein'-≤-bwd {e} {e'} e≢e' ¬dep r₁ s p h v =
      ein'-≤-transport v (H.eout e ++ r₁) s
        (λ pos → sym (count-ein'-pres e≢e' ¬dep r₁ s p v pos)) (h v)

  e'-fires-stable
    : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
    → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
    → ∀ {r₂' p₂'} → extract-prefix (H.ein e') s ≡ just (r₂' , p₂')
    → Σ[ r ∈ List (Fin H.nV) ] Σ[ q ∈ _ ]
        extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ just (r , q)
  e'-fires-stable {e} {e'} e≢e' ¬dep r₁ s p {r₂'} {p₂'} eqe' =
    count-≤→extract-prefix (H.ein e') (H.eout e ++ r₁)
      (ein'-≤-fwd e≢e' ¬dep r₁ s p
        (extract-prefix-just→count-≤ (H.ein e') s r₂' p₂'))

  -- A `just` outcome on `eout e ++ r₁` would (via the backward count
  -- transport) force success on `s`.
  e'-skips-stable
    : ∀ {e e' : Fin H.nE} → ¬ (e ≡ e') → ¬ (Dep H e e')
    → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
    → extract-prefix (H.ein e') s ≡ nothing
    → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ nothing
  e'-skips-stable {e} {e'} e≢e' ¬dep r₁ s p eqe'
    with extract-prefix (H.ein e') (H.eout e ++ r₁)
  ... | nothing      = refl
  ... | just (r , q) =
        ⊥-elim (nothing≢just (trans (sym eqe')
          (proj₂ (proj₂ (count-≤→extract-prefix (H.ein e') s
            (ein'-≤-bwd e≢e' ¬dep r₁ s p
              (extract-prefix-just→count-≤ (H.ein e') (H.eout e ++ r₁) r q)))))))

  ----------------------------------------------------------------------
  -- Extracting `ein e'` from the residual `r₁`.  From `p₂` + `eout e ⊥
  -- ein e'`, every vertex of `ein e'` lives in `r₁`, so `ein e'` is a
  -- count-prefix of `r₁`, giving `r₁ ↭ ein e' ++ Rlist`.
  ----------------------------------------------------------------------

  ein'-≤-r₁
    : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e')
    → (r₁ r₂ : List (Fin H.nV)) → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → ∀ v → count v (H.ein e') ≤ⁿ count v r₁
  ein'-≤-r₁ {e} {e'} ¬dep r₁ r₂ p₂ v with count-zero-or-pos e' v
  ... | inj₁ z   = subst (_≤ⁿ count v r₁) (sym z) z≤nⁿ
  ... | inj₂ pos =
        Nat.≤-trans (Nat.m≤m+n (count v (H.ein e')) (count v r₂))
        (Nat.≤-reflexive
          (trans (sym (count-++ v (H.ein e') r₂))
          (trans (sym (↭⇒count p₂ v))
          (trans (count-++ v (H.eout e) r₁)
                 (trans (cong (_+ count v r₁) (eout-ein-disjoint ¬dep v pos))
                        refl)))))

  extract-ein'
    : ∀ {e e' : Fin H.nE} → ¬ (Dep H e e')
    → (r₁ r₂ : List (Fin H.nV)) → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → Σ[ Rlist ∈ List (Fin H.nV) ] (r₁ Perm.↭ H.ein e' ++ Rlist)
  extract-ein' {e} {e'} ¬dep r₁ r₂ p₂ =
    let rest , q , _ = count-≤→extract-prefix (H.ein e') r₁ (ein'-≤-r₁ ¬dep r₁ r₂ p₂)
    in rest , q

  ----------------------------------------------------------------------
  -- Simultaneous location: for the `e ∷ e'` order with residual `Rlist`,
  -- the input stack `sp` locates both input blocks at once:
  --   loc₁ : sp ↭ (ein e ++ ein e') ++ Rlist.
  ----------------------------------------------------------------------

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
  -- The output reshuffle between the two final stacks.
  ----------------------------------------------------------------------

  post-swap-stack-↭
    : ∀ (e₁ e₂ : Fin H.nE)
        (sp r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : sp Perm.↭ H.ein e₁ ++ r₁)
        (p₂  : H.eout e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂)
        (p₂' : sp Perm.↭ H.ein e₂ ++ r₂')
        (p₁' : H.eout e₂ ++ r₂' Perm.↭ H.ein e₁ ++ r₁')
    → H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
  --
  -- This is an equation in the free commutative monoid on `Fin H.nV`, so it
  -- is decided by vertex counts (`count-≡⇒↭`).  For a fixed vertex `v` the
  -- four locating permutes give three `count` identities (via `↭⇒count` +
  -- `count-++`), from which the goal's count identity is pure ℕ arithmetic
  -- (`scalar`).
  post-swap-stack-↭ e₁ e₂ sp r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁' =
    count-≡⇒↭ (H.eout e₂ ++ r₂) (H.eout e₁ ++ r₁') per-v
    where
      -- a + x ≡ b + x'   (`p₁` , `p₂'` share the domain `sp`)
      eqI : ∀ v → count v (H.ein e₁) + count v r₁ ≡ count v (H.ein e₂) + count v r₂'
      eqI v = trans (sym (trans (↭⇒count p₁ v) (count-++ v (H.ein e₁) r₁)))
                    (trans (↭⇒count p₂' v) (count-++ v (H.ein e₂) r₂'))

      -- p + x ≡ b + y    (`p₂`)
      eqII : ∀ v → count v (H.eout e₁) + count v r₁ ≡ count v (H.ein e₂) + count v r₂
      eqII v = trans (sym (count-++ v (H.eout e₁) r₁))
                     (trans (↭⇒count p₂ v) (count-++ v (H.ein e₂) r₂))

      -- q + x' ≡ a + y'  (`p₁'`)
      eqIII : ∀ v → count v (H.eout e₂) + count v r₂' ≡ count v (H.ein e₁) + count v r₁'
      eqIII v = trans (sym (count-++ v (H.eout e₂) r₂'))
                      (trans (↭⇒count p₁' v) (count-++ v (H.ein e₁) r₁'))

      per-v : ∀ v → count v (H.eout e₂ ++ r₂) ≡ count v (H.eout e₁ ++ r₁')
      per-v v =
        trans (count-++ v (H.eout e₂) r₂)
        (trans (scalar (count v (H.ein e₁)) (count v (H.ein e₂))
                       (count v (H.eout e₁)) (count v (H.eout e₂))
                       (count v r₁) (count v r₂) (count v r₂') (count v r₁')
                       (eqI v) (eqII v) (eqIII v))
               (sym (count-++ v (H.eout e₁) r₁')))

  ----------------------------------------------------------------------
  -- The packaged simultaneous-location data for the both-fire pair: a
  -- shared `Rlist`, the two block-located input permutes, the output
  -- reshuffle.
  ----------------------------------------------------------------------

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
      shifted : H.ein e' ++ H.eout e ++ Rlist Perm.↭ H.eout e ++ r₁
      shifted = begin
        H.ein e' ++ H.eout e ++ Rlist
          ↭⟨ PermProp.shifts (H.ein e') (H.eout e) ⟩
        H.eout e ++ H.ein e' ++ Rlist
          ↭⟨ PermProp.++⁺ˡ (H.eout e) (Perm.↭-sym q₁) ⟩
        H.eout e ++ r₁ ∎

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

  module _
    {e e' : Fin H.nE} (¬dep-ee' : ¬ (Dep H e e')) (¬dep-e'e : ¬ (Dep H e' e))
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    where

    record SimLoc : Set where
      field
        Rlist     : List (Fin H.nV)
        loc₁      : sp Perm.↭ (H.ein e  ++ H.ein e') ++ Rlist
        loc₂      : sp Perm.↭ (H.ein e' ++ H.ein e ) ++ Rlist
        vout-loc₁ : (H.eout e  ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
        vout-loc₂ : (H.eout e' ++ H.eout e ) ++ Rlist Perm.↭ H.eout e  ++ r₁'
        r-stk     : H.eout e' ++ r₂ Perm.↭ H.eout e ++ r₁'

    sim-loc : SimLoc
    sim-loc =
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
        prefix-comm : (H.ein e' ++ H.ein e) ++ Rlist' Perm.↭ (H.ein e ++ H.ein e') ++ Rlist'
        prefix-comm = PermProp.++⁺ʳ Rlist' (PermProp.++-comm (H.ein e') (H.ein e))

        Rlist'-Rlist : Rlist' Perm.↭ Rlist
        Rlist'-Rlist =
          ++-cancelˡ (H.ein e ++ H.ein e')
            (Perm.↭-trans (Perm.↭-sym prefix-comm)
              (Perm.↭-trans (Perm.↭-sym loc₂') loc₁))

        loc₂'-bridged : sp Perm.↭ (H.ein e' ++ H.ein e) ++ Rlist
        loc₂'-bridged = Perm.↭-trans loc₂' (PermProp.++⁺ˡ (H.ein e' ++ H.ein e) Rlist'-Rlist)

        vout-loc₂-bridged : (H.eout e' ++ H.eout e) ++ Rlist Perm.↭ H.eout e ++ r₁'
        vout-loc₂-bridged =
          Perm.↭-trans (PermProp.++⁺ˡ (H.eout e' ++ H.eout e) (Perm.↭-sym Rlist'-Rlist))
                       vout-loc₂'

        r-stk : H.eout e' ++ r₂ Perm.↭ H.eout e ++ r₁'
        r-stk = post-swap-stack-↭ e e' sp r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁'
