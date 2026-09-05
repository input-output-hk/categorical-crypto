{-# OPTIONS --safe --without-K --guardedness #-}

-- The query bound multiplies along composition: the two-position token walk.
--
-- The potential of a composite is `Φᵍ · c′ + Φᶠ`: one unit of the outer
-- process's potential is worth a whole activation of the inner one, i.e. `c′`
-- downward events, so the outer's deposit of `c` buys `c · c′` of the
-- composite's.  The walk then moves between two positions with one invariant
-- each — at `g` the composite's potential is within the reference, at `f` it is
-- within it with `c′` to spare, the token having reached `f` by spending one of
-- `g`'s units — and every downward output of the composite pays for itself out
-- of `f`'s deposit.  The recursion is measured by `Φᵍ`: the `g`-to-`f`
-- transition is `g`'s own downward output, hence strictly decreasing, and the
-- return leg leaves `Φᵍ` alone, so one cycle charges one unit.
--
-- `Unfolding` is the whole interface to the composite's step.  A `𝒢ₚ`-composite
-- is a ⊕-trace whose loop wire is the intermediate interface in both
-- directions, so its step solves that loop within one external step; the six
-- equations say what the solved loop does in each of its positions, and nothing
-- below unfolds a trace or an iteration.  Everything is stated over
-- state/point/step PARAMETERS for the reason `UC.QueryBound`'s header records.

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties
  using (*-distribʳ-+; *-monoˡ-≤; +-assoc; +-comm; +-monoˡ-≤; +-monoʳ-<; +-monoʳ-≤;
         n≤0⇒n≡0; n≮0; ≤-pred; ≤-refl; ≤-reflexive; ≤-trans)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘′_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; sym; trans)

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.UC.QueryBound

module CategoricalCrypto.UC.QueryBound.Compose where

------------------------------------------------------------------------
-- `Dₚ` shorthands: the library's lemmas take their subjects explicitly, and a
-- transparent chain would strand them as metas (as in `UC.Machine.Run`).

private
  variable A′ B′ C′ : Set

  infixr 5 _⟨≈⟩_

  _⟨≈⟩_ : {d e h : Dₚ A′} → d ≈ₚ e → e ≈ₚ h → d ≈ₚ h
  _⟨≈⟩_ {d = d} {e} {h} = ≈ₚ-trans d e h

  ≈refl : {d : Dₚ A′} → d ≈ₚ d
  ≈refl {d = d} = ≈ₚ-refl d

  ≈sym : {d e : Dₚ A′} → d ≈ₚ e → e ≈ₚ d
  ≈sym {d = d} {e} = ≈ₚ-sym d e

  bindᶠ : {d : Dₚ A′} {k l : A′ → Dₚ B′}
        → ((a : A′) → k a ≈ₚ l a) → (d >>=ₚ k) ≈ₚ (d >>=ₚ l)
  bindᶠ {d = d} {k} {l} h = >>=ₚ-cong d d k l ≈refl h

  bindˣ : {d e : Dₚ A′} {k : A′ → Dₚ B′} → d ≈ₚ e → (d >>=ₚ k) ≈ₚ (e >>=ₚ k)
  bindˣ {d = d} {e} {k} h = >>=ₚ-cong d e k k h λ _ → ≈refl

  bind-map : (d : Dₚ A′) (h : A′ → B′) (k : B′ → Dₚ C′)
           → (mapₚ h d >>=ₚ k) ≈ₚ (d >>=ₚ (k ∘′ h))
  bind-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) k
             ⟨≈⟩ bindᶠ (λ a → >>=ₚ-identityˡ (h a) k)

  map-bind : (d : Dₚ A′) (h : A′ → Dₚ B′) (k : B′ → C′)
           → mapₚ k (d >>=ₚ h) ≈ₚ (d >>=ₚ λ a → mapₚ k (h a))
  map-bind d h k = >>=ₚ-assoc d h (returnₚ ∘′ k)

  map-map : (d : Dₚ A′) (h : A′ → B′) (k : B′ → C′)
          → mapₚ k (mapₚ h d) ≈ₚ mapₚ (k ∘′ h) d
  map-map d h k = >>=ₚ-assoc d (returnₚ ∘′ h) (returnₚ ∘′ k)
            ⟨≈⟩ bindᶠ (λ a → >>=ₚ-identityˡ (h a) (returnₚ ∘′ k))

  map-arg : {d e : Dₚ A′} (h : A′ → B′) → d ≈ₚ e → mapₚ h d ≈ₚ mapₚ h e
  map-arg h de = bindˣ de

------------------------------------------------------------------------
-- The composite's step, as the walk sees it

module Compose {A B C : Iface} (Sg Sf : Set)
               (pointg : Dₚ Sg) (pointf : Dₚ Sf) (pointᶜ : Dₚ (Sg × Sf))
               (stepg : Sg × (Pos B ⊎ Neg C) → Dₚ (Sg × (Neg B ⊎ Pos C)))
               (stepf : Sf × (Pos A ⊎ Neg B) → Dₚ (Sf × (Neg A ⊎ Pos B)))
               (stepᶜ : (Sg × Sf) × (Pos A ⊎ Neg C) → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C)))
               (solveᶜ : (Sg × Sf) × ((Neg A ⊎ Pos C) ⊎ (Neg B ⊎ Pos B))
                       → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C)))
               where

  -- The token has just left `f`: a downward message exits the composite, an
  -- upward one climbs the loop wire to `g`.
  resumeF : Sg → Sf × (Neg A ⊎ Pos B) → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C))
  resumeF sg (sf , inj₁ a) = solveᶜ ((sg , sf) , inj₁ (inj₁ a))
  resumeF sg (sf , inj₂ b) = solveᶜ ((sg , sf) , inj₂ (inj₂ b))

  -- …and symmetrically out of `g`: an upward message exits, a downward one
  -- descends the loop wire to `f`.
  resumeG : Sf → Sg × (Neg B ⊎ Pos C) → Dₚ ((Sg × Sf) × (Neg A ⊎ Pos C))
  resumeG sf (sg , inj₁ b) = solveᶜ ((sg , sf) , inj₂ (inj₁ b))
  resumeG sf (sg , inj₂ p) = solveᶜ ((sg , sf) , inj₁ (inj₂ p))

  record Unfolding : Set where
    field
      point-eq  : pointᶜ ≈ₚ (pointg >>=ₚ λ sg → mapₚ (sg ,_) pointf)
      step-L    : (sg : Sg) (sf : Sf) (a : Pos A)
                → stepᶜ ((sg , sf) , inj₁ a) ≈ₚ (stepf (sf , inj₁ a) >>=ₚ resumeF sg)
      step-R    : (sg : Sg) (sf : Sf) (n : Neg C)
                → stepᶜ ((sg , sf) , inj₂ n) ≈ₚ (stepg (sg , inj₂ n) >>=ₚ resumeG sf)
      solve-out : (s : Sg × Sf) (o : Neg A ⊎ Pos C)
                → solveᶜ (s , inj₁ o) ≈ₚ returnₚ (s , o)
      solve-B⁻  : (sg : Sg) (sf : Sf) (b : Neg B)
                → solveᶜ ((sg , sf) , inj₂ (inj₁ b))
                ≈ₚ (stepf (sf , inj₂ b) >>=ₚ resumeF sg)
      solve-B⁺  : (sg : Sg) (sf : Sf) (b : Pos B)
                → solveᶜ ((sg , sf) , inj₂ (inj₂ b))
                ≈ₚ (stepg (sg , inj₁ b) >>=ₚ resumeG sf)

  module _ {c c′ : ℕ} (u : Unfolding)
           (qg : QBᵢ {B} {C} Sg pointg stepg c)
           (qf : QBᵢ {A} {B} Sf pointf stepf c′) where

    private
      module qg = QBᵢ qg
      module qf = QBᵢ qf
      open Unfolding u

      Φᶜ : Sg × Sf → ℕ
      Φᶜ (sg , sf) = qg.Φ sg ℕ.* c′ ℕ.+ qf.Φ sf

      Aᶜ : ℕ → Set
      Aᶜ = Ans Φᶜ (Neg A) (Pos C)

      --------------------------------------------------------------------
      -- The potential arithmetic

      -- A `g`-unit is worth an activation of `f`…
      unit : {x y : ℕ} → x ℕ.< y → x ℕ.* c′ ℕ.+ c′ ℕ.≤ y ℕ.* c′
      unit {x} le = ≤-trans (≤-reflexive (+-comm (x ℕ.* c′) c′)) (*-monoˡ-≤ c′ le)

      -- …so `g`'s deposit of `c` is the composite's deposit of `c · c′`.
      grant : {x y : ℕ} → x ℕ.≤ y ℕ.+ c → x ℕ.* c′ ℕ.≤ y ℕ.* c′ ℕ.+ c ℕ.* c′
      grant {y = y} le = ≤-trans (*-monoˡ-≤ c′ le) (≤-reflexive (*-distribʳ-+ c′ y c))

      grant< : {x y : ℕ} → x ℕ.< y ℕ.+ c → x ℕ.* c′ ℕ.+ c′ ℕ.≤ y ℕ.* c′ ℕ.+ c ℕ.* c′
      grant< {y = y} le = ≤-trans (unit le) (≤-reflexive (*-distribʳ-+ c′ y c))

      -- `f`'s slack and the composite's deposit, moved past `g`'s potential.
      slack : (a y k : ℕ) → a ℕ.+ (y ℕ.+ k) ≡ (a ℕ.+ k) ℕ.+ y
      slack a y k = trans (cong (a ℕ.+_) (+-comm y k)) (sym (+-assoc a k y))

      reassoc : (a y k : ℕ) → (a ℕ.+ k) ℕ.+ y ≡ (a ℕ.+ y) ℕ.+ k
      reassoc a y k = trans (+-assoc a k y)
                            (trans (cong (a ℕ.+_) (+-comm k y)) (sym (+-assoc a y k)))

      --------------------------------------------------------------------
      -- The walk
      --
      -- `r` is the reference potential the composite's answer must respect and
      -- `k` the fuel, read off `g`'s potential.

      loopGᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) → qg.Φ sg ℕ.≤ k → Φᶜ (sg , sf) ℕ.≤ r
             → Pos B → Dₚ (Aᶜ r)
      atGᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) → qg.Φ sg ℕ.≤ k → Φᶜ (sg , sf) ℕ.≤ r
           → Ans qg.Φ (Neg B) (Pos C) (qg.Φ sg) → Dₚ (Aᶜ r)
      loopFᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) → qg.Φ sg ℕ.≤ k
             → qg.Φ sg ℕ.* c′ ℕ.+ (qf.Φ sf ℕ.+ c′) ℕ.≤ r → Neg B → Dₚ (Aᶜ r)
      atFᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) → qg.Φ sg ℕ.≤ k
           → qg.Φ sg ℕ.* c′ ℕ.+ (qf.Φ sf ℕ.+ c′) ℕ.≤ r
           → Ans qf.Φ (Neg A) (Pos B) (qf.Φ sf ℕ.+ c′) → Dₚ (Aᶜ r)

      loopGᵍ k r sg sf fk inv b = qg.onLᵍ sg b >>=ₚ atGᵍ k r sg sf fk inv

      atGᵍ k r sg sf fk inv (inj₂ ((sg′ , l) , p)) =
        returnₚ (inj₂ (((sg′ , sf)
                       , ≤-trans (+-monoˡ-≤ (qf.Φ sf) (*-monoˡ-≤ c′ l)) inv) , p))
      atGᵍ zero r sg sf fk inv (inj₁ ((sg′ , lt) , b)) = ⊥-elim (n≮0 (≤-trans lt fk))
      atGᵍ (suc k) r sg sf fk inv (inj₁ ((sg′ , lt) , b)) =
        loopFᵍ k r sg′ sf (≤-pred (≤-trans lt fk))
          (≤-trans (≤-reflexive (slack (qg.Φ sg′ ℕ.* c′) (qf.Φ sf) c′))
                   (≤-trans (+-monoˡ-≤ (qf.Φ sf) (unit lt)) inv))
          b

      loopFᵍ k r sg sf fk inv b = qf.onRᵍ sf b >>=ₚ atFᵍ k r sg sf fk inv

      atFᵍ k r sg sf fk inv (inj₁ ((sf′ , lt) , a)) =
        returnₚ (inj₁ (((sg , sf′)
                       , ≤-trans (+-monoʳ-< (qg.Φ sg ℕ.* c′) lt) inv) , a))
      atFᵍ k r sg sf fk inv (inj₂ ((sf′ , l) , b)) =
        loopGᵍ k r sg sf′ fk (≤-trans (+-monoʳ-≤ (qg.Φ sg ℕ.* c′) l) inv) b

      --------------------------------------------------------------------
      -- …and it erases to the composite's own solved loop

      cohGᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) (fk : qg.Φ sg ℕ.≤ k)
              (inv : Φᶜ (sg , sf) ℕ.≤ r) (b : Pos B)
            → mapₚ forget (loopGᵍ k r sg sf fk inv b)
            ≈ₚ (stepg (sg , inj₁ b) >>=ₚ resumeG sf)
      dispGᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) (fk : qg.Φ sg ℕ.≤ k)
               (inv : Φᶜ (sg , sf) ℕ.≤ r) (y : Ans qg.Φ (Neg B) (Pos C) (qg.Φ sg))
             → mapₚ forget (atGᵍ k r sg sf fk inv y) ≈ₚ resumeG sf (forget y)
      cohFᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) (fk : qg.Φ sg ℕ.≤ k)
              (inv : qg.Φ sg ℕ.* c′ ℕ.+ (qf.Φ sf ℕ.+ c′) ℕ.≤ r) (b : Neg B)
            → mapₚ forget (loopFᵍ k r sg sf fk inv b)
            ≈ₚ (stepf (sf , inj₂ b) >>=ₚ resumeF sg)
      dispFᵍ : (k r : ℕ) (sg : Sg) (sf : Sf) (fk : qg.Φ sg ℕ.≤ k)
               (inv : qg.Φ sg ℕ.* c′ ℕ.+ (qf.Φ sf ℕ.+ c′) ℕ.≤ r)
               (y : Ans qf.Φ (Neg A) (Pos B) (qf.Φ sf ℕ.+ c′))
             → mapₚ forget (atFᵍ k r sg sf fk inv y) ≈ₚ resumeF sg (forget y)

      cohGᵍ k r sg sf fk inv b =
            map-bind (qg.onLᵍ sg b) (atGᵍ k r sg sf fk inv) forget
        ⟨≈⟩ bindᶠ (dispGᵍ k r sg sf fk inv)
        ⟨≈⟩ ≈sym (bind-map (qg.onLᵍ sg b) forget (resumeG sf))
        ⟨≈⟩ bindˣ (qg.cohL sg b)

      dispGᵍ k r sg sf fk inv (inj₂ ((sg′ , l) , p)) =
            >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
        ⟨≈⟩ ≈sym (solve-out (sg′ , sf) (inj₂ p))
      dispGᵍ zero r sg sf fk inv (inj₁ ((sg′ , lt) , b)) = ⊥-elim (n≮0 (≤-trans lt fk))
      dispGᵍ (suc k) r sg sf fk inv (inj₁ ((sg′ , lt) , b)) =
        cohFᵍ k r sg′ sf _ _ b ⟨≈⟩ ≈sym (solve-B⁻ sg′ sf b)

      cohFᵍ k r sg sf fk inv b =
            map-bind (qf.onRᵍ sf b) (atFᵍ k r sg sf fk inv) forget
        ⟨≈⟩ bindᶠ (dispFᵍ k r sg sf fk inv)
        ⟨≈⟩ ≈sym (bind-map (qf.onRᵍ sf b) forget (resumeF sg))
        ⟨≈⟩ bindˣ (qf.cohR sf b)

      dispFᵍ k r sg sf fk inv (inj₁ ((sf′ , lt) , a)) =
            >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
        ⟨≈⟩ ≈sym (solve-out (sg , sf′) (inj₁ a))
      dispFᵍ k r sg sf fk inv (inj₂ ((sf′ , l) , b)) =
        cohGᵍ k r sg sf′ fk _ b ⟨≈⟩ ≈sym (solve-B⁺ sg sf′ b)

      --------------------------------------------------------------------
      -- The two entries
      --
      -- An external activation deposits nothing on the left and `c · c′` on the
      -- right, matching where the composite's own step feeds it in.

      enterLᵍ : (sg : Sg) (sf : Sf) → Ans qf.Φ (Neg A) (Pos B) (qf.Φ sf)
              → Dₚ (Aᶜ (Φᶜ (sg , sf)))
      enterLᵍ sg sf (inj₁ ((sf′ , lt) , a)) =
        returnₚ (inj₁ (((sg , sf′) , +-monoʳ-< (qg.Φ sg ℕ.* c′) lt) , a))
      enterLᵍ sg sf (inj₂ ((sf′ , l) , b)) =
        loopGᵍ (qg.Φ sg) _ sg sf′ ≤-refl (+-monoʳ-≤ (qg.Φ sg ℕ.* c′) l) b

      enterRᵍ : (sg : Sg) (sf : Sf) → Ans qg.Φ (Neg B) (Pos C) (qg.Φ sg ℕ.+ c)
              → Dₚ (Aᶜ (Φᶜ (sg , sf) ℕ.+ c ℕ.* c′))
      enterRᵍ sg sf (inj₂ ((sg′ , l) , p)) =
        returnₚ (inj₂ (((sg′ , sf)
                       , ≤-trans (+-monoˡ-≤ (qf.Φ sf) (grant l))
                                 (≤-reflexive (reassoc (qg.Φ sg ℕ.* c′) (qf.Φ sf)
                                                       (c ℕ.* c′)))) , p))
      enterRᵍ sg sf (inj₁ ((sg′ , lt) , b)) =
        loopFᵍ (qg.Φ sg′) _ sg′ sf ≤-refl
          (≤-trans (≤-reflexive (slack (qg.Φ sg′ ℕ.* c′) (qf.Φ sf) c′))
            (≤-trans (+-monoˡ-≤ (qf.Φ sf) (grant< lt))
                     (≤-reflexive (reassoc (qg.Φ sg ℕ.* c′) (qf.Φ sf) (c ℕ.* c′)))))
          b

      onLᶜᵍ : (s : Sg × Sf) (a : Pos A) → Dₚ (Aᶜ (Φᶜ s))
      onLᶜᵍ (sg , sf) a = qf.onLᵍ sf a >>=ₚ enterLᵍ sg sf

      onRᶜᵍ : (s : Sg × Sf) (n : Neg C) → Dₚ (Aᶜ (Φᶜ s ℕ.+ c ℕ.* c′))
      onRᶜᵍ (sg , sf) n = qg.onRᵍ sg n >>=ₚ enterRᵍ sg sf

      entryL : (sg : Sg) (sf : Sf) (y : Ans qf.Φ (Neg A) (Pos B) (qf.Φ sf))
             → mapₚ forget (enterLᵍ sg sf y) ≈ₚ resumeF sg (forget y)
      entryL sg sf (inj₁ ((sf′ , lt) , a)) =
            >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
        ⟨≈⟩ ≈sym (solve-out (sg , sf′) (inj₁ a))
      entryL sg sf (inj₂ ((sf′ , l) , b)) =
        cohGᵍ (qg.Φ sg) _ sg sf′ ≤-refl _ b ⟨≈⟩ ≈sym (solve-B⁺ sg sf′ b)

      entryR : (sg : Sg) (sf : Sf) (y : Ans qg.Φ (Neg B) (Pos C) (qg.Φ sg ℕ.+ c))
             → mapₚ forget (enterRᵍ sg sf y) ≈ₚ resumeG sf (forget y)
      entryR sg sf (inj₂ ((sg′ , l) , p)) =
            >>=ₚ-identityˡ _ (returnₚ ∘′ forget)
        ⟨≈⟩ ≈sym (solve-out (sg′ , sf) (inj₂ p))
      entryR sg sf (inj₁ ((sg′ , lt) , b)) =
        cohFᵍ (qg.Φ sg′) _ sg′ sf ≤-refl _ b ⟨≈⟩ ≈sym (solve-B⁻ sg′ sf b)

      cohLᶜ : (s : Sg × Sf) (a : Pos A)
            → mapₚ forget (onLᶜᵍ s a) ≈ₚ stepᶜ (s , inj₁ a)
      cohLᶜ (sg , sf) a =
            map-bind (qf.onLᵍ sf a) (enterLᵍ sg sf) forget
        ⟨≈⟩ bindᶠ (entryL sg sf)
        ⟨≈⟩ ≈sym (bind-map (qf.onLᵍ sf a) forget (resumeF sg))
        ⟨≈⟩ bindˣ (qf.cohL sf a)
        ⟨≈⟩ ≈sym (step-L sg sf a)

      cohRᶜ : (s : Sg × Sf) (n : Neg C)
            → mapₚ forget (onRᶜᵍ s n) ≈ₚ stepᶜ (s , inj₂ n)
      cohRᶜ (sg , sf) n =
            map-bind (qg.onRᵍ sg n) (enterRᵍ sg sf) forget
        ⟨≈⟩ bindᶠ (entryR sg sf)
        ⟨≈⟩ ≈sym (bind-map (qg.onRᵍ sg n) forget (resumeG sf))
        ⟨≈⟩ bindˣ (qg.cohR sg n)
        ⟨≈⟩ ≈sym (step-R sg sf n)

      --------------------------------------------------------------------
      -- The zero-potential point

      zeroᶜ : AtMost qg.Φ 0 → AtMost qf.Φ 0 → AtMost Φᶜ 0
      zeroᶜ zg zf = (proj₁ zg , proj₁ zf)
                  , ≤-reflexive (cong₂ (λ x y → x ℕ.* c′ ℕ.+ y)
                                       (n≤0⇒n≡0 (proj₂ zg)) (n≤0⇒n≡0 (proj₂ zf)))

      pointᵍᶜ : Dₚ (AtMost Φᶜ 0)
      pointᵍᶜ = qg.pointᵍ >>=ₚ λ zg → mapₚ (zeroᶜ zg) qf.pointᵍ

      coh₀ᶜ : mapₚ proj₁ pointᵍᶜ ≈ₚ pointᶜ
      coh₀ᶜ =
            map-bind qg.pointᵍ (λ zg → mapₚ (zeroᶜ zg) qf.pointᵍ) proj₁
        ⟨≈⟩ bindᶠ (λ zg → map-map qf.pointᵍ (zeroᶜ zg) proj₁
                     ⟨≈⟩ ≈sym (map-map qf.pointᵍ proj₁ (proj₁ zg ,_))
                     ⟨≈⟩ map-arg (proj₁ zg ,_) qf.coh₀)
        ⟨≈⟩ ≈sym (bind-map qg.pointᵍ proj₁ (λ sg → mapₚ (sg ,_) pointf))
        ⟨≈⟩ bindˣ qg.coh₀
        ⟨≈⟩ ≈sym point-eq

    qbᵢ-∘ᵍ : QBᵢ {A} {C} (Sg × Sf) pointᶜ stepᶜ (c ℕ.* c′)
    qbᵢ-∘ᵍ = record
      { Φ = Φᶜ ; pointᵍ = pointᵍᶜ ; coh₀ = coh₀ᶜ ; onLᵍ = onLᶜᵍ ; onRᵍ = onRᶜᵍ
      ; cohL = cohLᶜ ; cohR = cohRᶜ
      }
