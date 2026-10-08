{-# OPTIONS --safe --without-K #-}

-- Two-edge interchange reduces to counts in the free commutative monoid
-- on Fin H.nV; categorical bracketing belongs to Strict.Interchange.FireMid.

open import Categories.APROP.Internal.Prelude

module Categories.APROP.Hypergraph.Soundness.Discharge.FireMidInterchangeComb
  (sig : APROPSignature) where

open APROP sig

open import Categories.APROP.Hypergraph.Model.Core using (Hypergraph)
open import Categories.APROP.Hypergraph.Model.FromAPROP sig using (FlatGen)
open import Categories.Combinatorics.ExtractPrefix
open import Categories.Combinatorics.FinCount
  using ( count; count-++; ↭⇒count; count-≡⇒↭; count-pos→∈
        ; count-≤→extract-prefix; ++-cancelˡ; count-++-bndʳ
        ; extract-prefix-just→count-≤
        ; count-concat-tabulate-pair-≤)
open import Categories.APROP.Hypergraph.Model.Dependency using (Dep)
open import Categories.APROP.Hypergraph.Soundness.Linearity.Linearity sig
  using (Linear; consumedList)


open import Data.Empty
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Ext
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat using (s≤s⁻¹) renaming (_≤_ to _≤ⁿ_; _<_ to _<ⁿ_; s≤s to s≤sⁿ; z≤n to z≤nⁿ)
import Data.Nat.Properties as Nat
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary


private
  mid4 : ∀ (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + d) + (c + b)
  mid4 a b c d =
    trans (Nat.+-assoc a b (c + d))
    (trans (cong (a +_) (Nat.+-comm b (c + d)))
    (trans (cong (λ z → a + (z + b)) (Nat.+-comm c d))
    (trans (cong (a +_) (Nat.+-assoc d c b))
           (sym (Nat.+-assoc a d (c + b))))))

  scalar
    : ∀ (a b p q x y x' y' : ℕ)
    → a + x ≡ b + x'
    → p + x ≡ b + y
    → q + x' ≡ a + y'
    → q + y ≡ p + y'
  scalar a b p q x y x' y' I II III =
    Nat.+-cancelʳ-≡ (b + x') (q + y) (p + y')
      (trans (mid4 q y b x')
      (trans (cong₂ _+_ III (sym II))
      (trans (mid4 a y' p x)
      (trans (Nat.+-comm (a + x) (p + y'))
             (cong (p + y' +_) I)))))

module _ (H : Hypergraph FlatGen) where
  private module H = Hypergraph H
  private variable e e' : Fin H.nE

  eout-ein-disjoint
    : ¬ (Dep H e e') → (v : Fin H.nV)
    → 0 <ⁿ count v (H.ein e') → count v (H.eout e) ≡ 0
  eout-ein-disjoint {e} {e'} ¬dep v v∈ein-e' =
    Nat.n≤0⇒n≡0
      (Nat.≮⇒≥ λ v∈eout-e →
        ¬dep (v , count-pos→∈ v∈eout-e , count-pos→∈ v∈ein-e'))

  private
    count-zero-or-pos : (e' : Fin H.nE) (v : Fin H.nV)
                      → (count v (H.ein e') ≡ 0) ⊎ (0 <ⁿ count v (H.ein e'))
    count-zero-or-pos e' v with count v (H.ein e')
    ... | zero  = inj₁ refl
    ... | suc _ = inj₂ (s≤sⁿ z≤nⁿ)

    -- Zero-count vertices are bounded on either stack without transport.
    ein'-≤-transport
      : (v : Fin H.nV) (T U : List (Fin H.nV))
      → (0 <ⁿ count v (H.ein e') → count v T ≡ count v U)
      → count v (H.ein e') ≤ⁿ count v T → count v (H.ein e') ≤ⁿ count v U
    ein'-≤-transport {e'} v T U eq h with count-zero-or-pos e' v
    ... | inj₁ z   = subst (_≤ⁿ count v U) (sym z) z≤nⁿ
    ... | inj₂ pos = subst (count v (H.ein e') ≤ⁿ_) (eq pos) h

  ----------------------------------------------------------------------
  -- Firing stability
  ----------------------------------------------------------------------

  module _ (lin : Linear H) where

    private
      consume-bnd : ∀ (v : Fin H.nV) → count v (consumedList H) ≤ⁿ 1
      consume-bnd v = subst (_≤ⁿ 1) (proj₁ lin v) (proj₂ lin v)

      ein-concat-bnd : ∀ (v : Fin H.nV) → count v (concat (tabulate H.ein)) ≤ⁿ 1
      ein-concat-bnd v = count-++-bndʳ v H.cod _ (consume-bnd v)

    ein-ein-disjoint
      : ¬ (e ≡ e') → (v : Fin H.nV)
      → 0 <ⁿ count v (H.ein e) → count v (H.ein e') ≡ 0
    ein-ein-disjoint {e} {e'} e≢e' v v∈ein-e =
      Nat.n≤0⇒n≡0
        (s≤s⁻¹
          (Nat.≤-trans
            (Nat.+-monoˡ-≤ (count v (H.ein e')) v∈ein-e)
            (Nat.≤-trans (count-concat-tabulate-pair-≤ H.ein e e' e≢e' v)
                         (ein-concat-bnd v))))

    private
      count-ein'-pres
        : ¬ (e ≡ e') → ¬ (Dep H e e')
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

    e'-fires-stable
      : ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → ∀ {r₂' p₂'} → extract-prefix (H.ein e') s ≡ just (r₂' , p₂')
      → Σ[ r ∈ List (Fin H.nV) ] Σ[ q ∈ _ ]
          extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ just (r , q)
    e'-fires-stable {e} {e'} e≢e' ¬dep r₁ s p {r₂'} {p₂'} eqe' =
      count-≤→extract-prefix (H.ein e') (H.eout e ++ r₁)
        (λ v → ein'-≤-transport v s (H.eout e ++ r₁)
                 (count-ein'-pres e≢e' ¬dep r₁ s p v)
                 (extract-prefix-just→count-≤ (H.ein e') s r₂' p₂' v))

    e'-skips-stable
      : ¬ (e ≡ e') → ¬ (Dep H e e')
      → (r₁ s : List (Fin H.nV)) → s Perm.↭ H.ein e ++ r₁
      → extract-prefix (H.ein e') s ≡ nothing
      → extract-prefix (H.ein e') (H.eout e ++ r₁) ≡ nothing
    e'-skips-stable {e} {e'} e≢e' ¬dep r₁ s p eqe'
      with extract-prefix (H.ein e') (H.eout e ++ r₁)
    ... | nothing      = refl
    ... | just (r , q) =
          ⊥-elim (nothing≢just (trans (sym eqe')
            (proj₂ (proj₂ (count-≤→extract-prefix (H.ein e') s
              (λ v → ein'-≤-transport v (H.eout e ++ r₁) s
                       (λ pos → sym (count-ein'-pres e≢e' ¬dep r₁ s p v pos))
                       (extract-prefix-just→count-≤
                          (H.ein e') (H.eout e ++ r₁) r q v)))))))

  ----------------------------------------------------------------------
  -- Simultaneous location
  ----------------------------------------------------------------------

  ein'-≤-r₁
    : ¬ (Dep H e e')
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
    : ¬ (Dep H e e')
    → (r₁ r₂ : List (Fin H.nV)) → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → Σ[ Rlist ∈ List (Fin H.nV) ] (r₁ Perm.↭ H.ein e' ++ Rlist)
  extract-ein' {e} {e'} ¬dep r₁ r₂ p₂ =
    let rest , q , _ = count-≤→extract-prefix (H.ein e') r₁ (ein'-≤-r₁ ¬dep r₁ r₂ p₂)
    in rest , q

  block-loc-e
    : (sp r₁ : List (Fin H.nV))
    → sp Perm.↭ H.ein e ++ r₁
    → (Rlist : List (Fin H.nV))
    → r₁ Perm.↭ H.ein e' ++ Rlist
    → sp Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
  block-loc-e {e} {e'} sp r₁ p₁ Rlist q₁ = begin
    sp                                   ↭⟨ p₁ ⟩
    H.ein e ++ r₁                        ↭⟨ PermProp.++⁺ˡ (H.ein e) q₁ ⟩
    H.ein e ++ H.ein e' ++ Rlist         ≡⟨ sym (++-assoc (H.ein e) (H.ein e') Rlist) ⟩
    (H.ein e ++ H.ein e') ++ Rlist       ∎
    where
      open Perm.PermutationReasoning

  post-swap-stack-↭
    : ∀ (e₁ e₂ : Fin H.nE)
        (sp r₁ r₂ r₁' r₂' : List (Fin H.nV))
        (p₁  : sp Perm.↭ H.ein e₁ ++ r₁)
        (p₂  : H.eout e₁ ++ r₁ Perm.↭ H.ein e₂ ++ r₂)
        (p₂' : sp Perm.↭ H.ein e₂ ++ r₂')
        (p₁' : H.eout e₂ ++ r₂' Perm.↭ H.ein e₁ ++ r₁')
    → H.eout e₂ ++ r₂ Perm.↭ H.eout e₁ ++ r₁'
  -- Vertex counts decide this free commutative-monoid equation.
  post-swap-stack-↭ e₁ e₂ sp r₁ r₂ r₁' r₂' p₁ p₂ p₂' p₁' =
    count-≡⇒↭ (H.eout e₂ ++ r₂) (H.eout e₁ ++ r₁') per-v
    where
      eqI : ∀ v → count v (H.ein e₁) + count v r₁ ≡ count v (H.ein e₂) + count v r₂'
      eqI v = trans (sym (trans (↭⇒count p₁ v) (count-++ v (H.ein e₁) r₁)))
                    (trans (↭⇒count p₂' v) (count-++ v (H.ein e₂) r₂'))

      eqII : ∀ v → count v (H.eout e₁) + count v r₁ ≡ count v (H.ein e₂) + count v r₂
      eqII v = trans (sym (count-++ v (H.eout e₁) r₁))
                     (trans (↭⇒count p₂ v) (count-++ v (H.ein e₂) r₂))

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

  eout-residual
    : (r₁ r₂ Rlist : List (Fin H.nV))
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
    : (r₁ r₂ Rlist : List (Fin H.nV))
    → H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂
    → r₁ Perm.↭ H.ein e' ++ Rlist
    → (H.eout e ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
  vout-loc-e {e} {e'} r₁ r₂ Rlist p₂ q₁ = begin
    (H.eout e ++ H.eout e') ++ Rlist
      ≡⟨ ++-assoc (H.eout e) (H.eout e') Rlist ⟩
    H.eout e ++ H.eout e' ++ Rlist
      ↭⟨ PermProp.shifts (H.eout e) (H.eout e') ⟩
    H.eout e' ++ H.eout e ++ Rlist
      ↭⟨ PermProp.++⁺ˡ (H.eout e') (Perm.↭-sym r₂-eq) ⟩
    H.eout e' ++ r₂ ∎
    where
      open Perm.PermutationReasoning
      r₂-eq : r₂ Perm.↭ H.eout e ++ Rlist
      r₂-eq = eout-residual r₁ r₂ Rlist p₂ q₁

  module _
    {e e' : Fin H.nE} (¬dep-ee' : ¬ (Dep H e e')) (¬dep-e'e : ¬ (Dep H e' e))
    (sp : List (Fin H.nV))
    (r₁  : List (Fin H.nV)) (p₁  : sp Perm.↭ H.ein e ++ r₁)
    (r₂  : List (Fin H.nV)) (p₂  : H.eout e ++ r₁ Perm.↭ H.ein e' ++ r₂)
    (r₂' : List (Fin H.nV)) (p₂' : sp Perm.↭ H.ein e' ++ r₂')
    (r₁' : List (Fin H.nV)) (p₁' : H.eout e' ++ r₂' Perm.↭ H.ein e ++ r₁')
    where

    record SimLoc : Set where
      field Rlist     : List (Fin H.nV)
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

        Rlist : List (Fin H.nV)
        Rlist = proj₁ (extract-ein' ¬dep-ee' r₁ r₂ p₂)
        q₁ : r₁ Perm.↭ H.ein e' ++ Rlist
        q₁ = proj₂ (extract-ein' ¬dep-ee' r₁ r₂ p₂)

        loc₁ : sp Perm.↭ (H.ein e ++ H.ein e') ++ Rlist
        loc₁ = block-loc-e sp r₁ p₁ Rlist q₁

        vout-loc₁ : (H.eout e ++ H.eout e') ++ Rlist Perm.↭ H.eout e' ++ r₂
        vout-loc₁ = vout-loc-e {e} {e'} r₁ r₂ Rlist p₂ q₁

        Rlist' : List (Fin H.nV)
        Rlist' = proj₁ (extract-ein' ¬dep-e'e r₂' r₁' p₁')
        q₂' : r₂' Perm.↭ H.ein e ++ Rlist'
        q₂' = proj₂ (extract-ein' ¬dep-e'e r₂' r₁' p₁')

        loc₂' : sp Perm.↭ (H.ein e' ++ H.ein e) ++ Rlist'
        loc₂' = block-loc-e sp r₂' p₂' Rlist' q₂'

        vout-loc₂' : (H.eout e' ++ H.eout e) ++ Rlist' Perm.↭ H.eout e ++ r₁'
        vout-loc₂' = vout-loc-e {e'} {e} r₂' r₁' Rlist' p₁' q₂'

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
