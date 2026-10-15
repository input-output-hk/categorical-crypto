{-# OPTIONS --safe --without-K #-}

-- Finite-support cylinders suffice even when the reply type is infinite.
-- The induction carries rationally weighted initial states: conditioning on
-- a reply need not preserve total mass, and must not renormalize failure.
module CategoricalCrypto.SSP.Dist.FiniteTesting where

open import Algebra using (CommutativeRing)
open import Class.DecEq
open import Data.Empty using (⊥-elim)
open import Data.List.Base as List hiding (sum)
open import Data.List.Membership.Propositional
import Data.List.Membership.Propositional.Properties as Mem
import Data.List.NonEmpty as NE
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Relation.Unary.Unique.DecPropositional.Properties as Uniq
open import Data.List.Relation.Unary.Unique.Propositional
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Rational.Base
open import Data.Rational.Properties
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)

open import CategoricalCrypto.SSP.Dist.Kernel using
  (Oracle; ⟦_⟧; _·_; none; evalC-⟦⟧; ⟦mapᶜ⟧; ⟦graft⟧; regraft)
open import CategoricalCrypto.SSP.Iface using (Iface; unitᴵ; Ωᴵ)
open import CategoricalCrypto.SSP.Observation using (runᵖ)
import CategoricalCrypto.SSP.Protocol as P
import ProbabilisticLogic.Distribution.Linearity as Linearity
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation using (E; E-bind)
open import ProbabilisticLogic.Distribution.RationalDist.Partial

module Lin = Linearity (CommutativeRing.commutativeSemiring +-*-commutativeRing)

private variable
  A B Q R T X : Set

Weighted : Set → Set
Weighted A = List (ℚ × A)

bindW : Weighted A → (A → Weighted B) → Weighted B
bindW xs k = concatMap (λ (w , a) → Lin.scaleL w (k a)) xs

mapW : (A → B) → Weighted A → Weighted B
mapW f = List.map (map₂ f)

weightW : (A → ℚ) → Weighted A → Weighted A
weightW h = List.map (λ (w , a) → w * h a , a)

mapW-law : (f : A → B) (xs : Weighted A) (g : B → ℚ)
  → Lin.lookup-L (mapW f xs) g ≡ Lin.lookup-L xs (g ∘ f)
mapW-law f [] g = refl
mapW-law f ((w , a) ∷ xs) g = cong (w * g (f a) +_) (mapW-law f xs g)

weightW-law : (h : A → ℚ) (xs : Weighted A) (g : A → ℚ)
  → Lin.lookup-L (weightW h xs) g ≡ Lin.lookup-L xs (λ a → h a * g a)
weightW-law h [] g = refl
weightW-law h ((w , a) ∷ xs) g = cong₂ _+_ (*-assoc w (h a) (g a)) (weightW-law h xs g)

lookup-on : (xs : Weighted A) {f g : A → ℚ}
  → (∀ {w a} → (w , a) ∈ xs → f a ≡ g a) → Lin.lookup-L xs f ≡ Lin.lookup-L xs g
lookup-on [] e = refl
lookup-on ((w , a) ∷ xs) e = cong₂ _+_ (cong (w *_) (e (here refl)))
  (lookup-on xs (λ p → e (there p)))

module Replies (_≟_ : DecidableEquality R) where
  δ : R → R → ℚ
  δ a b with a ≟ b
  ... | yes _ = 1ℚ
  ... | no _ = 0ℚ

  δ-self : ∀ a → δ a a ≡ 1ℚ
  δ-self a with a ≟ a
  ... | yes _ = refl
  ... | no p = ⊥-elim (p refl)

  δ-other : ∀ {a b} → a ≢ b → δ a b ≡ 0ℚ
  δ-other {a} {b} p with a ≟ b
  ... | yes e = ⊥-elim (p e)
  ... | no _ = refl

  module Reg = Lin.Regroup δ δ-self δ-other

  sum : List R → (R → ℚ) → ℚ
  sum sup f = Lin.lookup-L (List.map (1ℚ ,_) sup) f

  sum-cong : (sup : List R) {f g : R → ℚ} → (∀ o → f o ≡ g o) → sum sup f ≡ sum sup g
  sum-cong sup = Lin.lookup-L-cong-P (List.map (1ℚ ,_) sup)

  singleton-wt : ∀ a b → Reg.wt ((1ℚ , a) ∷ []) b ≡ δ a b
  singleton-wt a b = trans (+-identityʳ _) (*-identityˡ _)

  sum-weights : (sup : List R) (h f : R → ℚ)
    → Lin.lookup-L (List.map (λ o → h o , o) sup) f
      ≡ sum sup (λ o → h o * f o)
  sum-weights [] h f = refl
  sum-weights (o ∷ sup) h f = cong₂ _+_ (sym (*-identityˡ (h o * f o))) (sum-weights sup h f)

  collapse : (sup : List R) → Unique sup → (a : R) → a ∈ sup → (f : R → ℚ)
    → sum sup (λ o → δ a o * f o) ≡ f a
  collapse sup unique a member f = sym (trans (sym (singleton-law′ (f a)))
    (trans (Reg.lookup-L-regroup ((1ℚ , a) ∷ []) unique (λ { (here refl) → member }) f)
      (trans (Reg.lookup-L-map-cong _ _ (singleton-wt a) sup f)
        (sum-weights sup (δ a) f))))
    where
    singleton-law′ : ∀ x → 1ℚ * x + 0ℚ ≡ x
    singleton-law′ x = trans (+-identityʳ (1ℚ * x)) (*-identityˡ x)

  split : (xs : Weighted (R × Q)) (sup : List R) → Unique sup
    → (∀ {w a q} → (w , (a , q)) ∈ xs → a ∈ sup) → (f : R × Q → ℚ)
    → Lin.lookup-L xs f ≡ sum sup (λ o → Lin.lookup-L xs (λ (a , q) → δ a o * f (o , q)))
  split xs sup unique cover f = trans
    (lookup-on xs (λ { {a = (a , q)} p →
      sym (collapse sup unique a (cover p) (λ o → f (o , q))) }))
    (Lin.lookup-L-swap xs (List.map (1ℚ ,_) sup) (λ (a , q) o → δ a o * f (o , q)))

Uniform : (T R : Set) → DecEq T → Iface
Uniform T R dec = record { Ch = T ; Q = λ _ → ⊤ ; R = λ _ → R ; Ch-dec = dec }

TotalKernel : Set → Set → Set → Set
TotalKernel T R Q = T → Q → Dist-ℚ (R × Q)

word : TotalKernel T R Q → List T → Q → Dist-ℚ (List R)
word K [] q = return-ℚ []
word K (t ∷ ts) q = K t q >>=ᴹ λ (o , q′) → Dmap (o ∷_) (word K ts q′)

oracle : TotalKernel T R Q → Q → T → ⊤ → Dist⊥ (Q × R)
oracle K q t _ = K t q >>=ᴹ λ (o , q′) → return⊥ (q′ , o)

value : ∀ {dec} → TotalKernel T R Q → P.Calls (Uniform T R dec) X → Q → (Maybe X → ℚ) → ℚ
value K (P.ret x) q ξ = ξ (just x)
value K (P.call t _ k) q ξ = E (K t q) (λ (o , q′) → value K (k o) q′ ξ)
value K (P.coin μ k) q ξ = E μ (λ b → value K (k b) q ξ)
value K P.dead q ξ = ξ nothing

lift : (Maybe X → ℚ) → Maybe (X × Q) → ℚ
lift ξ = ξ ∘ Data.Maybe.Base.map proj₁

native-value : ∀ {dec} (K : TotalKernel T R Q) (c : P.Calls (Uniform T R dec) X) q ξ
  → E (⟦ c ⟧ (oracle K) q) (lift ξ) ≡ value K c q ξ
native-value K (P.ret x) q ξ = lookupᴰℚ-return (just (x , q)) (lift ξ)
native-value K (P.call t tt k) q ξ = trans
  (>>=ᴹ-assoc (K t q) (λ (o , q′) → return⊥ (q′ , o))
    (kmaybe (λ (q′ , o) → ⟦ k o ⟧ (oracle K) q′)) (lift ξ))
  (trans (E-bind (K t q) (λ (o , q′) → return⊥ (q′ , o) >>=⊥ λ (s , a) → ⟦ k a ⟧ (oracle K) s) (lift ξ))
    (lookupᴰℚ-cong-P (entries (K t q)) (λ { (o , q′) →
      trans (>>=⊥-identityˡ (q′ , o) (λ (s , a) → ⟦ k a ⟧ (oracle K) s) (lift ξ))
        (native-value K (k o) q′ ξ) })))
native-value K (P.coin μ k) q ξ = trans (E-bind μ (λ b → ⟦ k b ⟧ (oracle K) q) (lift ξ))
  (lookupᴰℚ-cong-P (entries μ) (λ b → native-value K (k b) q ξ))
native-value {Q = Q} K P.dead q ξ = lookupᴰℚ-return nothing (lift {Q = Q} ξ)

observe : ∀ {dec} → TotalKernel T R Q → P.Calls (Uniform T R dec) X → Q → Dist⊥ X
observe K c q = Dmap (Data.Maybe.Base.map proj₁) (⟦ c ⟧ (oracle K) q)

observe-value : ∀ {dec} (K : TotalKernel T R Q) (c : P.Calls (Uniform T R dec) X) q ξ
  → E (observe K c q) ξ ≡ value K c q ξ
observe-value K c q ξ = trans
  (lookupᴰℚ-Dmap (Data.Maybe.Base.map proj₁) (⟦ c ⟧ (oracle K) q) ξ)
  (native-value K c q ξ)

wordTest : ∀ {dec} → List T → (List R → X) → P.Calls (Uniform T R dec) X
wordTest [] f = P.ret (f [])
wordTest (t ∷ ts) f = P.call t tt λ o → wordTest ts (λ os → f (o ∷ os))

wordTest-value : ∀ {dec} (K : TotalKernel T R Q) ts (f : List R → X) q ξ
  → value {dec = dec} K (wordTest ts f) q ξ ≡ E (word K ts q) (ξ ∘ just ∘ f)
wordTest-value K [] f q ξ = sym (lookupᴰℚ-return [] (ξ ∘ just ∘ f))
wordTest-value K (t ∷ ts) f q ξ = trans
  (lookupᴰℚ-cong-P (entries (K t q)) (λ { (o , q′) → wordTest-value K ts (λ os → f (o ∷ os)) q′ ξ }))
  (sym (trans (E-bind (K t q) (λ (o , q′) → Dmap (o ∷_) (word K ts q′)) (ξ ∘ just ∘ f))
    (lookupᴰℚ-cong-P (entries (K t q)) (λ { (o , q′) →
      lookupᴰℚ-Dmap (o ∷_) (word K ts q′) (ξ ∘ just ∘ f) }))))

singleton-law : (q : Q) (f : Q → ℚ) → Lin.lookup-L ((1ℚ , q) ∷ []) f ≡ f q
singleton-law q f = trans (+-identityʳ _) (*-identityˡ _)

module Cylinders {T R : Set} (_≟_ : DecidableEquality R) where
  open Replies _≟_

  rows : TotalKernel T R Q → Weighted Q → T → Weighted (R × Q)
  rows K xs t = bindW xs (λ q → NE.toList (entries (K t q)))

  after : TotalKernel T R Q → Weighted Q → T → R → Weighted Q
  after K xs t o = mapW proj₂ (weightW (λ p → δ (proj₁ p) o) (rows K xs t))

  after-rows : ∀ (K : TotalKernel T R Q) (xs : Weighted Q) t o (f : Q → ℚ)
    → Lin.lookup-L (after K xs t o) f
      ≡ Lin.lookup-L (rows K xs t) (λ (a , q′) → δ a o * f q′)
  after-rows K xs t o f = trans
    (mapW-law proj₂ (weightW (λ p → δ (proj₁ p) o) (rows K xs t)) f)
    (weightW-law (λ p → δ (proj₁ p) o) (rows K xs t) (f ∘ proj₂))

  after-law : ∀ (K : TotalKernel T R Q) (xs : Weighted Q) t o (f : Q → ℚ)
    → Lin.lookup-L (after K xs t o) f
      ≡ Lin.lookup-L xs (λ q → E (K t q) (λ (a , q′) → δ a o * f q′))
  after-law K xs t o f = trans (after-rows K xs t o f)
    (Lin.lookup-L-concatMap-scaleL (λ q → NE.toList (entries (K t q))) (λ (a , q′) → δ a o * f q′) xs)

  cylinder : R → (List R → ℚ) → List R → ℚ
  cylinder o f [] = 0ℚ
  cylinder o f (a ∷ as) = δ a o * f as

  cylinder-law : ∀ (K : TotalKernel T R Q) (xs : Weighted Q) t o ts f
    → Lin.lookup-L (after K xs t o) (λ q → E (word K ts q) f)
      ≡ Lin.lookup-L xs (λ q → E (word K (t ∷ ts) q) (cylinder o f))
  cylinder-law K xs t o ts f = trans (after-law K xs t o _)
    (Lin.lookup-L-cong-P xs (λ q → sym (trans
      (E-bind (K t q) (λ (a , q′) → Dmap (a ∷_) (word K ts q′)) (cylinder o f))
      (lookupᴰℚ-cong-P (entries (K t q)) (λ { (a , q′) →
        trans (lookupᴰℚ-Dmap (a ∷_) (word K ts q′) (cylinder o f))
          (lookupᴰℚ-*ₗ (δ a o) (entries (word K ts q′)) f) })))))

  Fixed : TotalKernel T R Q → Weighted Q → TotalKernel T R A → Weighted A → Set
  Fixed K xs H ys = ∀ ts f → Lin.lookup-L xs (λ q → E (word K ts q) f)
    ≡ Lin.lookup-L ys (λ q → E (word H ts q) f)

  fixed-after : ∀ (K : TotalKernel T R Q) xs (H : TotalKernel T R A) ys
    → Fixed K xs H ys → ∀ t o → Fixed K (after K xs t o) H (after H ys t o)
  fixed-after K xs H ys eq t o ts f = trans (cylinder-law K xs t o ts f)
    (trans (eq (t ∷ ts) (cylinder o f)) (sym (cylinder-law H ys t o ts f)))

  fixed-constant : ∀ (K : TotalKernel T R Q) xs (H : TotalKernel T R A) ys
    → Fixed K xs H ys → ∀ c → Lin.lookup-L xs (λ _ → c) ≡ Lin.lookup-L ys (λ _ → c)
  fixed-constant K xs H ys eq c = trans
    (Lin.lookup-L-cong-P xs (λ q → sym (lookupᴰℚ-return [] f)))
    (trans (eq [] f) (Lin.lookup-L-cong-P ys (λ q → lookupᴰℚ-return [] f)))
    where
    f : List R → ℚ
    f _ = c

  call-split : ∀ {dec} (K : TotalKernel T R Q) xs t
    (k : R → P.Calls (Uniform T R dec) X) ξ sup → Unique sup
    → (∀ {w a q} → (w , (a , q)) ∈ rows K xs t → a ∈ sup)
    → Lin.lookup-L xs (λ q → value K (P.call t tt k) q ξ)
      ≡ sum sup (λ o → Lin.lookup-L (after K xs t o) (λ q → value K (k o) q ξ))
  call-split K xs t k ξ sup unique cover = trans
    (sym (Lin.lookup-L-concatMap-scaleL (λ q → NE.toList (entries (K t q)))
      (λ (o , q) → value K (k o) q ξ) xs))
    (trans (split (rows K xs t) sup unique cover (λ (o , q) → value K (k o) q ξ))
      (sum-cong sup (λ o → sym (after-rows K xs t o (λ q → value K (k o) q ξ)))))

  adaptive-weighted : ∀ {dec} (c : P.Calls (Uniform T R dec) X)
    (K : TotalKernel T R Q) xs (H : TotalKernel T R A) ys → Fixed K xs H ys
    → ∀ ξ → Lin.lookup-L xs (λ q → value K c q ξ) ≡ Lin.lookup-L ys (λ q → value H c q ξ)
  adaptive-weighted (P.ret x) K xs H ys eq ξ = fixed-constant K xs H ys eq (ξ (just x))
  adaptive-weighted (P.call t tt k) K xs H ys eq ξ = trans
    (call-split K xs t k ξ sup unique coverK)
    (trans (sum-cong sup (λ o → adaptive-weighted (k o) K (after K xs t o)
      H (after H ys t o) (fixed-after K xs H ys eq t o) ξ))
      (sym (call-split H ys t k ξ sup unique coverH)))
    where
    left = List.map (proj₁ ∘ proj₂) (rows K xs t)
    right = List.map (proj₁ ∘ proj₂) (rows H ys t)
    sup = deduplicate _≟_ (left ++ right)
    unique = Uniq.deduplicate-! _≟_ (left ++ right)
    coverK : ∀ {w a q} → (w , (a , q)) ∈ rows K xs t → a ∈ sup
    coverK p = Mem.∈-deduplicate⁺ _≟_ (Mem.∈-++⁺ˡ (Mem.∈-map⁺ (proj₁ ∘ proj₂) p))
    coverH : ∀ {w a q} → (w , (a , q)) ∈ rows H ys t → a ∈ sup
    coverH p = Mem.∈-deduplicate⁺ _≟_ (Mem.∈-++⁺ʳ left (Mem.∈-map⁺ (proj₁ ∘ proj₂) p))
  adaptive-weighted (P.coin μ k) K xs H ys eq ξ = trans
    (Lin.lookup-L-swap xs (NE.toList (entries μ)) (λ q b → value K (k b) q ξ))
    (trans (lookupᴰℚ-cong-P (entries μ) (λ b → adaptive-weighted (k b) K xs H ys eq ξ))
      (sym (Lin.lookup-L-swap ys (NE.toList (entries μ)) (λ q b → value H (k b) q ξ))))
  adaptive-weighted P.dead K xs H ys eq ξ = fixed-constant K xs H ys eq (ξ nothing)

  fixed-to-calls : ∀ {dec} (K : TotalKernel T R Q) q (H : TotalKernel T R A) r
    → (∀ ts → word K ts q ≈Mℚ word H ts r)
    → (c : P.Calls (Uniform T R dec) X) → observe K c q ≈Mℚ observe H c r
  fixed-to-calls K q H r eq c ξ = trans (observe-value K c q ξ)
    (trans (sym (singleton-law q (λ s → value K c s ξ)))
      (trans (adaptive-weighted c K ((1ℚ , q) ∷ []) H ((1ℚ , r) ∷ []) fixed ξ)
        (trans (singleton-law r (λ s → value H c s ξ)) (sym (observe-value H c r ξ)))))
    where
    fixed : Fixed K ((1ℚ , q) ∷ []) H ((1ℚ , r) ∷ [])
    fixed ts f = trans (singleton-law q (λ s → E (word K ts s) f))
      (trans (eq ts f) (sym (singleton-law r (λ s → E (word H ts s) f))))

calls-to-fixed : ∀ {dec} (K : TotalKernel T R Q) q (H : TotalKernel T R A) r
  → (∀ {X} (c : P.Calls (Uniform T R dec) X) → observe K c q ≈Mℚ observe H c r)
  → ∀ ts → word K ts q ≈Mℚ word H ts r
calls-to-fixed K q H r eq ts f = trans
  (sym (wordTest-value K ts (λ os → os) q reward))
  (trans (sym (observe-value K test q reward))
    (trans (eq test reward)
      (trans (observe-value H test r reward) (wordTest-value H ts (λ os → os) r reward))))
  where
  reward : Maybe (List _) → ℚ
  reward nothing = 0ℚ
  reward (just os) = f os
  test = wordTest ts (λ os → os)

partial-map-reward : (f : A → B) (μ : Dist⊥ A) (ξ : Maybe B → ℚ)
  → E (Dmap⊥ f μ) ξ ≡ E μ (ξ ∘ Data.Maybe.Base.map f)
partial-map-reward f μ ξ = trans (E-bind μ (kmaybe (return⊥ ∘ f)) ξ)
  (lookupᴰℚ-cong-P (entries μ) (λ where
    nothing → lookupᴰℚ-return nothing ξ
    (just a) → lookupᴰℚ-return (just (f a)) ξ))

closed-compose-result : ∀ {I} (D : P.Protocol I Ωᴵ) (R : P.Protocol unitᴵ I)
  → runᵖ (D P.∘ᵖ R) ≈Mℚ Dmap (Data.Maybe.Base.map (proj₂ ∘ proj₁))
    (⟦ P.step D (P.init D) tt tt ⟧ (R · none) (P.init R , tt))
closed-compose-result D R ξ = trans (evalC-⟦⟧ (P.mapᶜ proj₂ u) none tt ξ)
  (trans (partial-map-reward proj₁ mapped ξ)
    (trans (⟦mapᶜ⟧ proj₂ u none tt (lift ξ))
      (trans (partial-map-reward (map₁ proj₂) grafted (lift ξ))
        (trans (⟦graft⟧ D R none t (P.init R) tt reward)
          (trans (partial-map-reward regraft original reward)
            (trans (lookupᴰℚ-cong-P (entries original) (λ where nothing → refl ; (just _) → refl))
              (sym (lookupᴰℚ-Dmap (Data.Maybe.Base.map (proj₂ ∘ proj₁)) original ξ))))))))
  where
  t = P.step D (P.init D) tt tt
  u = P.graft D R t (P.init R)
  mapped = ⟦ P.mapᶜ proj₂ u ⟧ none tt
  grafted = ⟦ u ⟧ none tt
  original = ⟦ t ⟧ (R · none) (P.init R , tt)
  reward = lift ξ ∘ Data.Maybe.Base.map (map₁ proj₂)
