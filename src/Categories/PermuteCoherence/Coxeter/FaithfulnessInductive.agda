{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Inductive permutation congruence and its equivalence to evaluated equality.
-- The constructor set omits swap-congruence and far-commutativity:
-- both follow from naturality.
------------------------------------------------------------------------

open import Relation.Binary using (DecidableEquality)

module Categories.PermuteCoherence.Coxeter.FaithfulnessInductive
  (X : Set)
  (_≟X_ : DecidableEquality X) where

open import Categories.PermuteCoherence.Coxeter.InsertProof
open import Categories.PermuteCoherence.Coxeter.Word
open import Categories.PermuteCoherence.Coxeter.WordInterp {X = X}
open import Categories.PermuteCoherence.Eval
open import Categories.PermuteCoherence.FinBij
open import Categories.PermuteCoherence.FinBij.Properties

open import Data.Fin.Base using (Fin) renaming (suc to fsuc)
open import Data.Fin.Patterns
import Data.Fin.Permutation as P
open import Data.List.Base
import Data.List.Properties.Ext as ListExt
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open Perm using (_↭_)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
open import Data.Nat.Base
open import Data.Nat.Properties renaming (≡-irrelevant to ℕ-≡-irrelevant)
open import Data.Product
open import Relation.Binary.PropositionalEquality

private
  variable
    x y z : X
    xs ys zs ws xs′ ys′ zs′ xs″ ws′ as bs cs ds : List X
    n m m′ : ℕ

uipX : (p q : xs ≡ ys) → p ≡ q
uipX = ListExt.≡-irrelevant _≟X_

infix 4 _≅↭ⁱ_

data _≅↭ⁱ_ : xs ↭ ys → xs ↭ ys → Set where

  iref : {p : xs ↭ ys} → p ≅↭ⁱ p
  isym : {p q : xs ↭ ys} → p ≅↭ⁱ q → q ≅↭ⁱ p
  itrn : {p q r : xs ↭ ys} → p ≅↭ⁱ q → q ≅↭ⁱ r → p ≅↭ⁱ r

  prepc : {p q : xs ↭ ys} → p ≅↭ⁱ q → Perm.prep x p ≅↭ⁱ Perm.prep x q
  trc   : {p p′ : xs ↭ ys} {q q′ : ys ↭ zs}
        → p ≅↭ⁱ p′ → q ≅↭ⁱ q′ → Perm.trans p q ≅↭ⁱ Perm.trans p′ q′

  tr-unitˡ : {p : xs ↭ ys} → Perm.trans (Perm.refl {xs = xs}) p ≅↭ⁱ p
  tr-unitʳ : {p : xs ↭ ys} → Perm.trans p (Perm.refl {xs = ys}) ≅↭ⁱ p
  tr-assoc : {p : xs ↭ ys} {q : ys ↭ zs} {r : zs ↭ ws}
           → Perm.trans (Perm.trans p q) r ≅↭ⁱ Perm.trans p (Perm.trans q r)

  prep-id : Perm.prep x (Perm.refl {xs = xs}) ≅↭ⁱ Perm.refl {xs = x ∷ xs}
  prep-tr : {p : xs ↭ ys} {q : ys ↭ zs}
          → Perm.prep x (Perm.trans p q) ≅↭ⁱ Perm.trans (Perm.prep x p) (Perm.prep x q)

  swap-nat : {p : xs ↭ ys}
           → Perm.swap x y p
             ≅↭ⁱ
             Perm.trans (Perm.prep x (Perm.prep y p)) (Perm.swap x y (Perm.refl {xs = ys}))

  swap-nat-left : {p : xs ↭ ys}
                → Perm.swap x y p
                  ≅↭ⁱ
                  Perm.trans (Perm.swap x y (Perm.refl {xs = xs})) (Perm.prep y (Perm.prep x p))

  swap-invol : Perm.trans (Perm.swap x y (Perm.refl {xs = xs}))
                          (Perm.swap y x (Perm.refl {xs = xs}))
               ≅↭ⁱ Perm.refl {xs = x ∷ y ∷ xs}

  swap-braid : Perm.trans (Perm.swap x y (Perm.refl {xs = z ∷ xs}))
                          (Perm.trans (Perm.prep y (Perm.swap x z (Perm.refl {xs = xs})))
                                      (Perm.swap y z (Perm.refl {xs = x ∷ xs})))
               ≅↭ⁱ
               Perm.trans (Perm.prep x (Perm.swap y z (Perm.refl {xs = xs})))
                          (Perm.trans (Perm.swap x z (Perm.refl {xs = y ∷ xs}))
                                      (Perm.prep z (Perm.swap x y (Perm.refl {xs = xs}))))

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
-- Pointwise braid reasoning avoids intermediate-record metas: `_≈-fb_`
-- sees only the forward map, not the remaining fields (see `Word`).
sound (swap-braid {xs = xs}) i =
  trans lhsCollapse (trans (yang-baxter {L} i) (sym rhsCollapse))
  where
  L  = length xs
  Sx = swap-fb (suc L)
  liftedSwap = cons-fb (swap-fb L)
  c2s = cons-fb (cons-fb (id-fb {suc L}))
  D  = cons-fb (swap-fb L ∘-fb cons-fb (cons-fb (id-fb {L})))
  ccx : ∀ k → c2s P.⟨$⟩ʳ k ≡ k
  ccx = cons²-fb-id {suc L}
  collM : ∀ k → D P.⟨$⟩ʳ k ≡ liftedSwap P.⟨$⟩ʳ k
  collM = cons-fb-cong (λ k → cong (swap-fb L P.⟨$⟩ʳ_) (cons²-fb-id {L} k))
  lhsCollapse : Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ (D P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ i))))
                ≡ Sx P.⟨$⟩ʳ (liftedSwap P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ i))
  lhsCollapse =
    cong (Sx P.⟨$⟩ʳ_)
      (trans (ccx (D P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ i))))
      (trans (collM (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ i)))
             (cong (liftedSwap P.⟨$⟩ʳ_) (cong (Sx P.⟨$⟩ʳ_) (ccx i)))))
  rhsCollapse : D P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ (D P.⟨$⟩ʳ i)))
                ≡ liftedSwap P.⟨$⟩ʳ (Sx P.⟨$⟩ʳ (liftedSwap P.⟨$⟩ʳ i))
  rhsCollapse =
    trans (collM (Sx P.⟨$⟩ʳ (c2s P.⟨$⟩ʳ (D P.⟨$⟩ʳ i))))
      (cong (liftedSwap P.⟨$⟩ʳ_)
        (trans (cong (Sx P.⟨$⟩ʳ_) (ccx (D P.⟨$⟩ʳ i)))
               (cong (Sx P.⟨$⟩ʳ_) (collM i))))

------------------------------------------------------------------------
-- Heterogeneous congruence
------------------------------------------------------------------------

-- A `~ʷ` move changes the intermediate list.  Package its endpoint
-- equality as in `FreeStrictSMC.Build._≈̂_`.

infix 4 _≅↭ᴴ_

_≅↭ᴴ_ : xs ↭ ys → xs′ ↭ zs → Set
_≅↭ᴴ_ {xs} {ys} {xs′} {zs} p q =
  Σ[ el ∈ xs ≡ xs′ ] Σ[ er ∈ ys ≡ zs ] (subst₂ Perm._↭_ el er p ≅↭ⁱ q)

hrefl : {p : xs ↭ ys} → p ≅↭ᴴ p
hrefl = refl , refl , iref

hsym : {p : xs ↭ ys} {q : xs′ ↭ zs} → p ≅↭ᴴ q → q ≅↭ᴴ p
hsym (refl , refl , h) = refl , refl , isym h

htrn : {p : xs ↭ ys} {q : xs′ ↭ zs} {r : xs″ ↭ ws′}
     → p ≅↭ᴴ q → q ≅↭ᴴ r → p ≅↭ᴴ r
htrn (refl , refl , h₁) (refl , refl , h₂) = refl , refl , itrn h₁ h₂

prepᴴ : {p : xs ↭ ys} {q : xs′ ↭ zs} → p ≅↭ᴴ q → Perm.prep x p ≅↭ᴴ Perm.prep x q
prepᴴ (refl , refl , h) = refl , refl , prepc h

trcᴴ : {p : xs ↭ ys} {q : ys ↭ zs} {p′ : xs′ ↭ ys′} {q′ : ys′ ↭ zs′}
     → p ≅↭ᴴ p′ → q ≅↭ᴴ q′ → Perm.trans p q ≅↭ᴴ Perm.trans p′ q′
-- After the first match, the shared middle equality is constrained.
-- UIP collapses it without a reflexive pattern match.
trcᴴ {q = q} (refl , refl , h₁) (el₂ , refl , h₂) =
  refl , refl , trc h₁ (subst (λ e → subst₂ Perm._↭_ e refl q ≅↭ⁱ _) (uipX el₂ refl) h₂)

∷ᴴ : {i : Fin n} {p : xs ↭ ys} {q : xs′ ↭ ys′} → (h : p ≅↭ᴴ q)
   → Perm.trans p (swapAt-↭ i ys) ≅↭ᴴ Perm.trans q (swapAt-↭ i ys′)
∷ᴴ h@(_ , refl , _) = trcᴴ h hrefl

-- Coincident endpoints constrain both equalities; collapse them with UIP.
toⁱ : {p q : xs ↭ ys} → p ≅↭ᴴ q → p ≅↭ⁱ q
toⁱ {p = p} {q = q} (el , er , h) =
  subst (λ e₂ → subst₂ Perm._↭_ refl e₂ p ≅↭ⁱ q) (uipX er refl)
    (subst (λ e₁ → subst₂ Perm._↭_ e₁ er p ≅↭ⁱ q) (uipX el refl) h)

liftⁱ : {p q : xs ↭ ys} → p ≅↭ⁱ q → p ≅↭ᴴ q
liftⁱ h = refl , refl , h

swap²ᴴ : (i : Fin n) (ys : List X)
       → Perm.trans (swapAt-↭ i ys) (swapAt-↭ i (swapAt i ys)) ≅↭ᴴ Perm.refl {xs = ys}
swap²ᴴ i        []             = liftⁱ tr-unitˡ
swap²ᴴ 0F       (a ∷ [])       = liftⁱ tr-unitˡ
swap²ᴴ 0F       (a ∷ b ∷ rest) = liftⁱ swap-invol
swap²ᴴ (fsuc i) (a ∷ xs)       =
  htrn (liftⁱ (isym prep-tr))
       (htrn (prepᴴ (swap²ᴴ i xs)) (liftⁱ prep-id))

far-nat : {p : xs ↭ ys}
        → Perm.trans (Perm.prep x (Perm.prep y p)) (Perm.swap x y (Perm.refl {xs = ys}))
          ≅↭ⁱ Perm.trans (Perm.swap x y (Perm.refl {xs = xs})) (Perm.prep y (Perm.prep x p))
far-nat = itrn (isym swap-nat) swap-nat-left

swapFarᴴ : {i j : Fin n} → Far i j → (ys : List X)
  → Perm.trans (swapAt-↭ j ys) (swapAt-↭ i (swapAt j ys))
    ≅↭ᴴ Perm.trans (swapAt-↭ i ys) (swapAt-↭ j (swapAt i ys))
swapFarᴴ far0ˡ    []             = hrefl
swapFarᴴ far0ˡ    (a ∷ [])       = liftⁱ (itrn tr-unitʳ (isym tr-unitˡ))
swapFarᴴ far0ˡ    (a ∷ b ∷ rest) = liftⁱ far-nat
swapFarᴴ (farS f) []             = hrefl
swapFarᴴ (farS f) (a ∷ ys′)      =
  htrn (liftⁱ (isym prep-tr)) (htrn (prepᴴ (swapFarᴴ f ys′)) (liftⁱ prep-tr))

distr3 : {p : as ↭ bs} {q : bs ↭ cs} {r : cs ↭ ds}
       → Perm.prep x (Perm.trans p (Perm.trans q r))
         ≅↭ⁱ Perm.trans (Perm.prep x p) (Perm.trans (Perm.prep x q) (Perm.prep x r))
distr3 = itrn prep-tr (trc iref prep-tr)

swapBraidᴴ : {i k : Fin n} → Adj i k → (ys : List X) → length ys ≡ suc n
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

bridge-sound : {w w′ : Word (length zs)} → w ~ʷ w′
             → ⟦ w ⟧↭ (z ∷ zs) ≅↭ᴴ ⟦ w′ ⟧↭ (z ∷ zs)
bridge-sound ~refl          = hrefl
bridge-sound (~sym r)       = hsym (bridge-sound r)
bridge-sound (~trans r₁ r₂) = htrn (bridge-sound r₁) (bridge-sound r₂)
bridge-sound (∷c r)         = ∷ᴴ (bridge-sound r)
bridge-sound {zs = zs} {z = z} (c1 i {w = w}) =
  htrn (liftⁱ tr-assoc)
       (htrn (trcᴴ hrefl (swap²ᴴ i (applyW w (z ∷ zs)))) (liftⁱ tr-unitʳ))
bridge-sound {zs = zs} {z = z} (c2 {w = w} f) =
  htrn (liftⁱ tr-assoc)
       (htrn (trcᴴ hrefl (swapFarᴴ f (applyW w (z ∷ zs)))) (liftⁱ (isym tr-assoc)))
bridge-sound {zs = zs} {z = z} (c3 {w = w} adj) =
  htrn (liftⁱ (itrn tr-assoc tr-assoc))
       (htrn (trcᴴ hrefl (swapBraidᴴ adj (applyW w (z ∷ zs)) (applyW-length w (z ∷ zs))))
             (liftⁱ (isym (itrn tr-assoc tr-assoc))))

------------------------------------------------------------------------
-- Interpretation structure
------------------------------------------------------------------------

-- Endpoints reduce only for concrete words, so the relations are heterogeneous.
interp-liftW : (w : Word n)
             → ⟦ liftW w ⟧↭ (x ∷ xs) ≅↭ᴴ Perm.prep x (⟦ w ⟧↭ xs)
interp-liftW []        = liftⁱ (isym prep-id)
interp-liftW (i ∷ w′) =
  htrn (∷ᴴ (interp-liftW w′)) (liftⁱ (isym prep-tr))

interp-++ : (v w : Word n)
          → ⟦ v ++ w ⟧↭ xs ≅↭ᴴ Perm.trans (⟦ w ⟧↭ xs) (⟦ v ⟧↭ (applyW w xs))
interp-++ []       w = liftⁱ (isym tr-unitʳ)
interp-++ (i ∷ v′) w =
  htrn (∷ᴴ (interp-++ v′ w)) (liftⁱ tr-assoc)

------------------------------------------------------------------------
-- Flattening and completeness
------------------------------------------------------------------------

⟦⟧↭-subst : (eq : n ≡ m) (w : Word n)
          → ⟦ subst Word eq w ⟧↭ as ≅↭ᴴ ⟦ w ⟧↭ as
⟦⟧↭-subst refl w = hrefl

flatten : (p : xs ↭ ys) → Σ[ w ∈ Word (pred (length xs)) ] (p ≅↭ᴴ ⟦ w ⟧↭ xs)
flatten Perm.refl = [] , hrefl
flatten (Perm.prep {xs = []} x p′) with flatten p′
... | [] , rel′ = [] , htrn (prepᴴ rel′) (liftⁱ prep-id)
flatten (Perm.prep {xs = z ∷ zs} x p′) with flatten p′
... | w′ , rel′ = liftW w′ , htrn (prepᴴ rel′) (hsym (interp-liftW w′))
-- The free middle endpoint can be matched to the interpreted list.
flatten (Perm.trans {xs = xs} p′ q′)
  with flatten p′ | flatten q′
... | w_p , rel_p@(_ , refl , _) | w_q , rel_q =
  w_q′ ++ w_p ,
  htrn (trcᴴ rel_p rel_q)
       (hsym (htrn (interp-++ w_q′ w_p)
                   (trcᴴ hrefl (⟦⟧↭-subst (sym eq′) w_q))))
  where
  eq′ : pred (length xs) ≡ pred (length (applyW w_p xs))
  eq′ = cong pred (↭-length p′)
  w_q′ : Word (pred (length xs))
  w_q′ = subst Word (sym eq′) w_q
flatten (Perm.swap {xs = z ∷ zs} {ys = ys′} x y p′) with flatten p′
... | w′ , rel′ =
  0F ∷ liftW (liftW w′) ,
  htrn (liftⁱ swap-nat) (∷ᴴ piece1)
  where
  piece1 : Perm.prep x (Perm.prep y p′)
           ≅↭ᴴ ⟦ liftW (liftW w′) ⟧↭ (x ∷ y ∷ z ∷ zs)
  piece1 = htrn (prepᴴ (prepᴴ rel′))
                (hsym (htrn (interp-liftW (liftW w′)) (prepᴴ (interp-liftW w′))))
-- Matching the free codomain forces the empty endpoint.
flatten (Perm.swap {xs = []} {ys = ys′} x y p′) with flatten p′
... | [] , rel′@(_ , refl , _) =
  0F ∷ [] ,
  htrn (liftⁱ swap-nat) (trcᴴ collapse hrefl)
  where
  collapse : Perm.prep x (Perm.prep y p′) ≅↭ᴴ Perm.refl {xs = x ∷ y ∷ []}
  collapse =
    htrn (prepᴴ (prepᴴ rel′))
         (htrn (prepᴴ (liftⁱ prep-id)) (liftⁱ prep-id))

private
  subst-Fin-uip : (e e′ : m ≡ m′) (k : Fin m)
                → subst Fin e k ≡ subst Fin e′ k
  subst-Fin-uip e e′ k = cong (λ z → subst Fin z k) (ℕ-≡-irrelevant e e′)

  -- The codomain equality is free; only the domain needs UIP.
  flatten-eval
    : (p : (z ∷ zs) ↭ ys) (w : Word (length zs))
    → p ≅↭ᴴ ⟦ w ⟧↭ (z ∷ zs)
    → (k : Fin (suc (length zs)))
    → evalW w P.⟨$⟩ʳ k
      ≡ subst Fin (sym (↭-length p)) (eval-↭ p P.⟨$⟩ʳ k)
  flatten-eval {z = z} {zs} p w (el , refl , h) k
    rewrite uipX el refl =
    trans (sym (eval-respect z zs w k))
    (trans (cast-push refl L (eval-↭ (⟦ w ⟧↭ (z ∷ zs))) k)
    (trans (cong (subst Fin L) (sym (sound h k)))
           (subst-Fin-uip L (sym (↭-length p)) (eval-↭ p P.⟨$⟩ʳ k))))
    where
    L : length (applyW w (z ∷ zs)) ≡ suc (length zs)
    L = applyW-length w (z ∷ zs)

complete : {p q : xs ↭ ys} → eval-↭ p ≈-fb eval-↭ q → p ≅↭ⁱ q
complete {xs = []} {ys = ys} {p = p} {q = q} _
  with flatten p | flatten q
... | [] , rel_p | [] , rel_q = toⁱ (htrn rel_p (hsym rel_q))
complete {xs = z ∷ zs} {ys = ys} {p = p} {q = q} h
  with flatten p | flatten q
... | w_p , rel_p | w_q , rel_q = toⁱ (htrn rel_p (htrn bridge (hsym rel_q)))
  where
  eval≈ : evalW w_p ≈-fb evalW w_q
  eval≈ k =
    trans (flatten-eval p w_p rel_p k)
    (trans (cong (subst Fin (sym (↭-length p))) (h k))
    (trans (subst-Fin-uip (sym (↭-length p)) (sym (↭-length q)) (eval-↭ q P.⟨$⟩ʳ k))
           (sym (flatten-eval q w_q rel_q k))))
  word~ : w_p ~ʷ w_q
  word~ = ~trans (straightenW w_p)
                 (~trans (canonW-resp-≈ eval≈) (~sym (straightenW w_q)))
  bridge : ⟦ w_p ⟧↭ (z ∷ zs) ≅↭ᴴ ⟦ w_q ⟧↭ (z ∷ zs)
  bridge = bridge-sound word~
