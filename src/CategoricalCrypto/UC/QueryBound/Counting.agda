{-# OPTIONS --safe --without-K --guardedness #-}

-- What the potential in `QBᵢ` means on a run: `UC.QueryBound.Counting`
-- inhabited.
--
-- On every activation word the certificate produces a run whose output word
-- carries at most `c` downward outputs per activation from above, and which
-- erases to the machine's own behaviour.  The bound travels INSIDE `Dₚ` — a
-- distribution admits no inspection of an output — so it lives in the type of a
-- refined run rather than as a predicate on an observed list.
--
-- The recursion carries the amortised invariant with the FINAL potential
-- RETAINED (`#inj₁ outs + Φ final ≤ Φ s + c * #inj₂ w`): that is the form that
-- recurses, since a step pays for its own downward output out of what the
-- account holds, and the form with `Φ final` dropped does not.  The design is
-- the reference arc's (`CategoricalCrypto.SFunMSetoid.QueryBound.Counting`),
-- with two changes forced by this layer — each cons step of `traceᵍ` is a
-- `>>=ₚ` rather than a functorial action, and the initial slack is zeroed by
-- `pointᵍ`/`coh₀` rather than by a `subst` along `Φ (init M) ≡ 0`.
--
-- `CountedRun` is a record, not a Σ, for the same reason `CountBound` is: `#inj₂`
-- is not injective, so a transparent pair strands `w` on a `#inj₂ ? ≟ #inj₂ w`
-- constraint at every use.
--
-- Separate from `UC.QueryBound` because that module is at its measured
-- typechecking budget; nothing here mentions `Proc`.

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; _≤_; s≤s)
open import Data.Nat.Properties
  using (*-suc; +-assoc; +-monoˡ-≤; m+n≤o⇒m≤o; m≤m+n; ≤-reflexive; ≤-trans)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.QueryBound.Counting where

private
  variable X Y Z : Set

  infixr 5 _⟨≈⟩_

  _⟨≈⟩_ : {d e h : Dₚ X} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
  _⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

  bindᶠ : {d : Dₚ X} {k l : X → Dₚ Y}
        → ((x : X) → k x ≈ₚ l x) → (d >>=ₚ k) ≈ₚ (d >>=ₚ l)
  bindᶠ {d = d} {k} {l} h = >>=ₚ-cong d d k l (≈ₚ-refl d) h

  return-≡ : {x y : X} → x ≡ y → returnₚ x ≈ₚ returnₚ y
  return-≡ refl = ≈ₚ-refl _

  map-map : (d : Dₚ X) (h : X → Y) (k : Y → Z) → mapₚ k (mapₚ h d) ≈ₚ mapₚ (k ∘′ h) d
  map-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) (returnₚ ∘′ k)
            ⟨≈⟩ bindᶠ (λ x → >>=ₚ-identityˡ (h x) (returnₚ ∘′ k))

  map-cong : (d : Dₚ X) {h k : X → Y} → ((x : X) → h x ≡ k x) → mapₚ h d ≈ₚ mapₚ k d
  map-cong d eq = bindᶠ (λ x → return-≡ (eq x))

  map-arg : {d e : Dₚ X} (h : X → Y) → d ≈ₚ e → mapₚ h d ≈ₚ mapₚ h e
  map-arg {d = d} {e} h de = >>=ₚ-cong d e (returnₚ ∘′ h) (returnₚ ∘′ h) de λ _ → ≈ₚ-refl _

  map->>= : (d : Dₚ X) (h : X → Y) (k : Y → Dₚ Z) → (mapₚ h d >>=ₚ k) ≈ₚ (d >>=ₚ (k ∘′ h))
  map->>= d h k = >>=ₚ-assoc d (returnₚ ∘′ h) k ⟨≈⟩ bindᶠ (λ x → >>=ₚ-identityˡ (h x) k)

  -- Push a continuation across an erasure: if `d` erases to `dᵉ` along `h` and
  -- `k` factors through `h`, the two binds agree.  Every use below takes `h` at
  -- `forget`, which is what lets a proof-carrying answer under a continuation be
  -- replaced by the erased one.
  pushᵉ : (h : X → Y) (d : Dₚ X) (dᵉ : Dₚ Y) (k : X → Dₚ Z) (kᵉ : Y → Dₚ Z)
        → mapₚ h d ≈ₚ dᵉ → ((x : X) → k x ≈ₚ kᵉ (h x)) → (d >>=ₚ k) ≈ₚ (dᵉ >>=ₚ kᵉ)
  pushᵉ h d dᵉ k kᵉ erase factor =
    bindᶠ factor ⟨≈⟩ ≈ₚ-sym _ _ (map->>= d h kᵉ)
      ⟨≈⟩ >>=ₚ-cong (mapₚ h d) dᵉ kᵉ kᵉ erase (λ _ → ≈ₚ-refl _)

------------------------------------------------------------------------
-- The refined run

module Refined {A B : Iface} (S : Set) (point : Dₚ S)
               (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B)))
               (c : ℕ) (q : QBᵢ S point step c) where

  open QBᵢ q

  -- A run of `w` from `s`: where it ends, what it emitted, and the amortised
  -- invariant relating the two.
  record CountedRun (s : S) (w : List (Pos A ⊎ Neg B)) : Set where
    constructor counted
    field
      final : S
      outs  : List (Neg A ⊎ Pos B)
      bound : #inj₁ outs + Φ final ≤ Φ s + c * #inj₂ w

  open CountedRun

  private
    -- One activation from above deposits `c`, cashed against the extra `c` its
    -- own entry contributes to the word's count.
    deposit : (x n : ℕ) → x + c + c * n ≡ x + c * suc n
    deposit x n = trans (+-assoc x c (c * n)) (cong (x +_) (sym (*-suc c n)))

    afterR : (s : S) (u n : ℕ) → u ≤ Φ s + c → u + c * n ≤ Φ s + c * suc n
    afterR s u n le = ≤-trans (+-monoˡ-≤ (c * n) le) (≤-reflexive (deposit (Φ s) n))

    -- Prepending a downward output costs one unit of potential, which the step's
    -- own withdrawal supplies — that is why `le`'s left side is a `suc`.
    -- Prepending an upward one is free.  Every index is explicit: a
    -- `#inj₂`-valued bound determines none of them.
    consᴰ : (s : S) (w : List (Pos A ⊎ Neg B)) (s′ : S) (w′ : List (Pos A ⊎ Neg B))
            (a : Neg A) → suc (Φ s′) + c * #inj₂ w′ ≤ Φ s + c * #inj₂ w
          → CountedRun s′ w′ → CountedRun s w
    consᴰ _ _ _ _ a le r = counted (final r) (inj₁ a ∷ outs r) (≤-trans (s≤s (bound r)) le)

    consᶜ : (s : S) (w : List (Pos A ⊎ Neg B)) (s′ : S) (w′ : List (Pos A ⊎ Neg B))
            (b : Pos B) → Φ s′ + c * #inj₂ w′ ≤ Φ s + c * #inj₂ w
          → CountedRun s′ w′ → CountedRun s w
    consᶜ _ _ _ _ b le r = counted (final r) (inj₂ b ∷ outs r) (≤-trans (bound r) le)

    -- The tail of one `traceᵍ` step: run the rest of the word, prepend this
    -- activation's output.
    contᵉ : (w : List (Pos A ⊎ Neg B)) → S × (Neg A ⊎ Pos B) → Dₚ (List (Neg A ⊎ Pos B))
    contᵉ w p = mapₚ (proj₂ p ∷_) (traceᵍ S point step (proj₁ p) w)

  -- The refined run, driven by the certificate's own activations.  The account
  -- is empty at the end of the word, so the base case is pure slack.
  countᵍ : (s : S) (w : List (Pos A ⊎ Neg B)) → Dₚ (CountedRun s w)
  atL : (s : S) (w : List (Pos A ⊎ Neg B)) (a : Pos A)
      → Ans Φ (Neg A) (Pos B) (Φ s) → Dₚ (CountedRun s (inj₁ a ∷ w))
  atR : (s : S) (w : List (Pos A ⊎ Neg B)) (b : Neg B)
      → Ans Φ (Neg A) (Pos B) (Φ s + c) → Dₚ (CountedRun s (inj₂ b ∷ w))

  countᵍ s []           = returnₚ (counted s [] (m≤m+n (Φ s) (c * 0)))
  countᵍ s (inj₁ a ∷ w) = onLᵍ s a >>=ₚ atL s w a
  countᵍ s (inj₂ b ∷ w) = onRᵍ s b >>=ₚ atR s w b

  atL s w a (inj₁ ((s′ , lt) , a′)) =
    mapₚ (consᴰ s (inj₁ a ∷ w) s′ w a′ (+-monoˡ-≤ (c * #inj₂ w) lt)) (countᵍ s′ w)
  atL s w a (inj₂ ((s′ , le) , b′)) =
    mapₚ (consᶜ s (inj₁ a ∷ w) s′ w b′ (+-monoˡ-≤ (c * #inj₂ w) le)) (countᵍ s′ w)

  atR s w b (inj₁ ((s′ , lt) , a′)) =
    mapₚ (consᴰ s (inj₂ b ∷ w) s′ w a′ (afterR s (suc (Φ s′)) (#inj₂ w) lt)) (countᵍ s′ w)
  atR s w b (inj₂ ((s′ , le) , b′)) =
    mapₚ (consᶜ s (inj₂ b ∷ w) s′ w b′ (afterR s (Φ s′) (#inj₂ w) le)) (countᵍ s′ w)

  private
    -- Erasing the bound off a consing step.  The recursive instance is the
    -- hypothesis `rec` rather than a call, so `countᵍ-erase`'s own recursion is
    -- the only one in the walk.
    eraseCons : (o : Neg A ⊎ Pos B) (d : Dₚ X) (g : X → List (Neg A ⊎ Pos B))
                (h : X → Y) (e : Y → List (Neg A ⊎ Pos B))
              → ((x : X) → e (h x) ≡ o ∷ g x)
              → (t : Dₚ (List (Neg A ⊎ Pos B))) → mapₚ g d ≈ₚ t
              → mapₚ e (mapₚ h d) ≈ₚ mapₚ (o ∷_) t
    eraseCons o d g h e agree t rec = map-map d h e ⟨≈⟩ map-cong d agree
                                ⟨≈⟩ ≈ₚ-sym _ _ (map-map d g (o ∷_)) ⟨≈⟩ map-arg (o ∷_) rec

  -- The refined run really is the machine's: forgetting the bound leaves the
  -- behaviour `behᵍ` is read off.
  countᵍ-erase : (s : S) (w : List (Pos A ⊎ Neg B))
               → mapₚ outs (countᵍ s w) ≈ₚ traceᵍ S point step s w
  countᵍ-erase s [] = >>=ₚ-identityˡ (counted s [] (m≤m+n (Φ s) (c * 0))) (returnₚ ∘′ outs)
  countᵍ-erase s (inj₁ a ∷ w) =
    >>=ₚ-assoc (onLᵍ s a) (atL s w a) (returnₚ ∘′ outs)
      ⟨≈⟩ pushᵉ forget (onLᵍ s a) (step (s , inj₁ a)) kᵍ (contᵉ w) (cohL s a) factor
    where
    kᵍ : Ans Φ (Neg A) (Pos B) (Φ s) → Dₚ (List (Neg A ⊎ Pos B))
    kᵍ y = mapₚ outs (atL s w a y)

    factor : (y : Ans Φ (Neg A) (Pos B) (Φ s)) → kᵍ y ≈ₚ contᵉ w (forget y)
    factor (inj₁ ((s′ , lt) , a′)) =
      eraseCons (inj₁ a′) (countᵍ s′ w) outs
                (consᴰ s (inj₁ a ∷ w) s′ w a′ (+-monoˡ-≤ (c * #inj₂ w) lt)) outs
                (λ _ → refl) (traceᵍ S point step s′ w) (countᵍ-erase s′ w)
    factor (inj₂ ((s′ , le) , b′)) =
      eraseCons (inj₂ b′) (countᵍ s′ w) outs
                (consᶜ s (inj₁ a ∷ w) s′ w b′ (+-monoˡ-≤ (c * #inj₂ w) le)) outs
                (λ _ → refl) (traceᵍ S point step s′ w) (countᵍ-erase s′ w)
  countᵍ-erase s (inj₂ b ∷ w) =
    >>=ₚ-assoc (onRᵍ s b) (atR s w b) (returnₚ ∘′ outs)
      ⟨≈⟩ pushᵉ forget (onRᵍ s b) (step (s , inj₂ b)) kᵍ (contᵉ w) (cohR s b) factor
    where
    kᵍ : Ans Φ (Neg A) (Pos B) (Φ s + c) → Dₚ (List (Neg A ⊎ Pos B))
    kᵍ y = mapₚ outs (atR s w b y)

    factor : (y : Ans Φ (Neg A) (Pos B) (Φ s + c)) → kᵍ y ≈ₚ contᵉ w (forget y)
    factor (inj₁ ((s′ , lt) , a′)) =
      eraseCons (inj₁ a′) (countᵍ s′ w) outs
                (consᴰ s (inj₂ b ∷ w) s′ w a′ (afterR s (suc (Φ s′)) (#inj₂ w) lt)) outs
                (λ _ → refl) (traceᵍ S point step s′ w) (countᵍ-erase s′ w)
    factor (inj₂ ((s′ , le) , b′)) =
      eraseCons (inj₂ b′) (countᵍ s′ w) outs
                (consᶜ s (inj₂ b ∷ w) s′ w b′ (afterR s (Φ s′) (#inj₂ w) le)) outs
                (λ _ → refl) (traceᵍ S point step s′ w) (countᵍ-erase s′ w)

------------------------------------------------------------------------
-- The counting theorem

-- The account starts empty — `pointᵍ` is a distribution over zero-potential
-- states — so the initial slack vanishes and the potential left at the end can
-- be dropped; `coh₀` then identifies the refined start with the machine's own.
qbᵢ⇒count : {A B : Iface} (S : Set) (point : Dₚ S)
            (step : S × (Pos A ⊎ Neg B) → Dₚ (S × (Neg A ⊎ Pos B))) (c : ℕ)
          → QBᵢ S point step c → CountBound S point step c
qbᵢ⇒count {A} {B} S point step c q = record { runs = runs ; erases = erases }
  where
  open QBᵢ q
  open Refined S point step c q
  open CountedRun

  drop : (w : List (Pos A ⊎ Neg B)) (z : AtMost Φ 0) → CountedRun (proj₁ z) w
       → Σ[ os ∈ List (Neg A ⊎ Pos B) ] #inj₁ os ≤ c * #inj₂ w
  drop w (s₀ , le₀) r = outs r
                      , m+n≤o⇒m≤o (#inj₁ (outs r))
                          (≤-trans (bound r) (+-monoˡ-≤ (c * #inj₂ w) le₀))

  runs : (w : List (Pos A ⊎ Neg B))
       → Dₚ (Σ[ os ∈ List (Neg A ⊎ Pos B) ] #inj₁ os ≤ c * #inj₂ w)
  runs w = pointᵍ >>=ₚ λ z → mapₚ (drop w z) (countᵍ (proj₁ z) w)

  erases : (w : List (Pos A ⊎ Neg B)) → mapₚ proj₁ (runs w) ≈ₚ behᵍ S point step w
  erases w =
    >>=ₚ-assoc pointᵍ (λ z → mapₚ (drop w z) (countᵍ (proj₁ z) w)) (returnₚ ∘′ proj₁)
      ⟨≈⟩ bindᶠ (λ z → map-map (countᵍ (proj₁ z) w) (drop w z) proj₁
                   ⟨≈⟩ map-cong (countᵍ (proj₁ z) w) (λ _ → refl)
                   ⟨≈⟩ countᵍ-erase (proj₁ z) w)
      ⟨≈⟩ ≈ₚ-sym _ _ (map->>= pointᵍ proj₁ (λ s → traceᵍ S point step s w))
      ⟨≈⟩ >>=ₚ-cong (mapₚ proj₁ pointᵍ) point _ _ coh₀ (λ _ → ≈ₚ-refl _)

counting : Counting
counting = qbᵢ⇒count
