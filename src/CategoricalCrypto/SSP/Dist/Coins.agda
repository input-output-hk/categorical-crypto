{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.SSP.Dist.Coins where

open import Data.Maybe.Base using (just)
open import Data.Product.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using (Coins; done; toss; sample; coins)
open import CategoricalCrypto.SSP.Dist.Kernel using (_>>=ᶜ_)
open import CategoricalCrypto.SSP.Iface using (Iface)
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.SSP.Observation using (evalC)
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Product
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

private variable X Y Z : Set
private variable A : Iface

infixl 1 _>>=ᶜᵒ_
_>>=ᶜᵒ_ : Coins X → (X → Coins Y) → Coins Y
done x >>=ᶜᵒ f = f x
toss μ k >>=ᶜᵒ f = toss μ (λ b → k b >>=ᶜᵒ f)

mapCoins : (X → Y) → Coins X → Coins Y
mapCoins f κ = κ >>=ᶜᵒ done ∘ f

pairCoins : Coins X → Coins Y → Coins (X × Y)
pairCoins κ λκ = κ >>=ᶜᵒ λ x → mapCoins (x ,_) λκ

sample-bind : (κ : Coins X) (f : X → Coins Y)
  → sample (κ >>=ᶜᵒ f) ≈Mℚ (sample κ >>=ᴹ sample ∘ f)
sample-bind (done x) f P = sym (>>=ᴹ-identityˡ x (sample ∘ f) P)
sample-bind (toss μ k) f P = trans
  (>>=ᴹ-congˡ μ (λ b → sample (k b >>=ᶜᵒ f))
    (λ b → sample (k b) >>=ᴹ sample ∘ f) (λ b → sample-bind (k b) f) P)
  (sym (>>=ᴹ-assoc μ (sample ∘ k) (sample ∘ f) P))

sample-map : (f : X → Y) (κ : Coins X) → sample (mapCoins f κ) ≈Mℚ Dmap f (sample κ)
sample-map f κ = sample-bind κ (done ∘ f)

sample-pair : (κ : Coins X) (λκ : Coins Y)
  → sample (pairCoins κ λκ) ≈Mℚ independent (sample κ) (sample λκ)
sample-pair κ λκ P = trans (sample-bind κ (λ x → mapCoins (x ,_) λκ) P)
  (>>=ᴹ-congˡ (sample κ) (λ x → sample (mapCoins (x ,_) λκ))
    (λ x → Dmap (x ,_) (sample λκ)) (λ x → sample-map (x ,_) λκ) P)

eval-coins : (κ : Coins X) → evalC (coins κ) ≈Mℚ Dmap just (sample κ)
eval-coins (done x) P = sym (map-return just x P)
eval-coins (toss μ k) P = trans
  (>>=ᴹ-congˡ μ (λ b → evalC (coins (k b))) (λ b → Dmap just (sample (k b)))
    (λ b → eval-coins (k b)) P)
  (sym (>>=ᴹ-assoc μ (sample ∘ k) (return-ℚ ∘ just) P))

coins-map-id : (κ : Coins X) → coins {A = A} (mapCoins (λ x → x) κ) P.≈ᶜ coins κ
coins-map-id (done x) = P.ret refl
coins-map-id (toss μ k) = P.coin λ b → coins-map-id (k b)

coins-map-compose : (f : X → Y) (g : Y → Z) (κ : Coins X)
  → coins {A = A} (mapCoins g (mapCoins f κ)) P.≈ᶜ coins (mapCoins (g ∘ f) κ)
coins-map-compose f g (done x) = P.ret refl
coins-map-compose f g (toss μ k) = P.coin λ b → coins-map-compose f g (k b)

map-coins : (f : X → Y) (κ : Coins X)
  → P.mapᶜ f (coins {A = A} κ) P.≈ᶜ coins (mapCoins f κ)
map-coins f (done x) = P.ret refl
map-coins f (toss μ k) = P.coin λ b → map-coins f (k b)

bind-call-cong : {t u : P.Calls A X} {f g : X → P.Calls A Y}
  → t P.≈ᶜ u → (∀ x → f x P.≈ᶜ g x) → (t >>=ᶜ f) P.≈ᶜ (u >>=ᶜ g)
bind-call-cong (P.ret refl) h = h _
bind-call-cong (P.call h) k = P.call λ r → bind-call-cong (h r) k
bind-call-cong (P.coin h) k = P.coin λ b → bind-call-cong (h b) k
bind-call-cong P.dead h = P.dead

coins-bind-through : (κ : Coins X) (f : X → Coins Y) (k : X → P.Calls A Y)
  → (∀ x → coins (f x) P.≈ᶜ k x) → coins (κ >>=ᶜᵒ f) P.≈ᶜ (coins κ >>=ᶜ k)
coins-bind-through (done x) f k h = h x
coins-bind-through (toss μ g) f k h = P.coin λ b → coins-bind-through (g b) f k h

coins-map-bind : (f : X → Y) (κ : Coins X) (k : Y → P.Calls A Z)
  → (coins (mapCoins f κ) >>=ᶜ k) P.≈ᶜ (coins κ >>=ᶜ (k ∘ f))
coins-map-bind f (done x) k = P.≈ᶜ-refl
coins-map-bind f (toss μ g) k = P.coin λ b → coins-map-bind f (g b) k

pair-calls : (κ : Coins X) (λκ : Coins Y) (f : X → Y → Z)
  → coins {A = A} (mapCoins (uncurry f) (pairCoins κ λκ))
    P.≈ᶜ (coins κ >>=ᶜ λ x → P.mapᶜ (f x) (coins λκ))
pair-calls (done x) (done y) f = P.ret refl
pair-calls (done x) (toss μ k) f = P.coin λ b → pair-calls (done x) (k b) f
pair-calls (toss μ k) λκ f = P.coin λ b → pair-calls (k b) λκ f
