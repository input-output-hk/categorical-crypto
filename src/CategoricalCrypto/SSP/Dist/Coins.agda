{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.SSP.Dist.Coins where

open import Data.Maybe.Base using (just)
open import Data.Product.Base
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.SSP.Dist.Kernel using
  (Coins; done; toss; sample; coins; _>>=ᶜ_; _≈ᵏ_; ≈ᶜ⇒≈ᵏ; ≈ᵏ-trans; ≈ᵏ->>=ᶜ; ≈ᵏ-refl
  ; >>=ᶜ-ret; evalC-⟦⟧; ⟦_⟧; none; run≈ᵏ)
open import CategoricalCrypto.SSP.Iface
import CategoricalCrypto.SSP.Protocol as P
open import CategoricalCrypto.SSP.Observation using (evalC)
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial using (return⊥; >>=⊥-congʳ)
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

reindex-coins : ∀ {I K} (m : I ⇒ᴵ K) (κ : Coins X)
  → P.reindex m (coins κ) P.≈ᶜ coins κ
reindex-coins m (done x) = P.ret refl
reindex-coins m (toss μ k) = P.coin λ b → reindex-coins m (k b)

graft-cong : ∀ {I K L} (U : P.Protocol K L) (V : P.Protocol I K)
  {t u : P.Calls K (P.St U × X)} → t P.≈ᶜ u → ∀ q → P.graft U V t q P.≈ᶜ P.graft U V u q
serve-cong : ∀ {I K L} (U : P.Protocol K L) (V : P.Protocol I K)
  {c : Ch K} {k l : R K c → P.Calls K (P.St U × X)}
  → (∀ r → k r P.≈ᶜ l r) → (t : P.Calls I (P.St V × R K c))
  → P.serve U V k t P.≈ᶜ P.serve U V l t

graft-cong U V (P.ret refl) q = P.ret refl
graft-cong U V (P.call {c = c} {q = a} h) q = serve-cong U V h (P.step V q c a)
graft-cong U V (P.coin h) q = P.coin λ b → graft-cong U V (h b) q
graft-cong U V P.dead q = P.dead
serve-cong U V h (P.ret (q , r)) = graft-cong U V (h r) q
serve-cong U V h (P.call c a k) = P.call λ r → serve-cong U V h (k r)
serve-cong U V h (P.coin μ k) = P.coin λ b → serve-cong U V h (k b)
serve-cong U V h P.dead = P.dead

serve-tree-cong : ∀ {I K L} (U : P.Protocol K L) (V : P.Protocol I K)
  {c : Ch K} (k : R K c → P.Calls K (P.St U × X))
  {t u : P.Calls I (P.St V × R K c)} → t P.≈ᶜ u
  → P.serve U V k t P.≈ᶜ P.serve U V k u
serve-tree-cong U V k (P.ret refl) = P.≈ᶜ-refl
serve-tree-cong U V k (P.call h) = P.call λ r → serve-tree-cong U V k (h r)
serve-tree-cong U V k (P.coin h) = P.coin λ b → serve-tree-cong U V k (h b)
serve-tree-cong U V k P.dead = P.dead

serve-coins : ∀ {I K L} (U : P.Protocol K L) (V : P.Protocol I K)
  {c : Ch K} (k : R K c → P.Calls K (P.St U × X)) (κ : Coins (P.St V × R K c))
  → P.serve U V k (coins κ) P.≈ᶜ
    (coins κ >>=ᶜ λ (q , r) → P.graft U V (k r) q)
serve-coins U V k (done x) = P.≈ᶜ-refl
serve-coins U V k (toss μ h) = P.coin λ b → serve-coins U V k (h b)

close-coins : ∀ {K} (U : P.Protocol (unitᴵ ⊗ᴵ unitᴵ) K)
  (κ : Coins (P.St U × X))
  → P.graft U P.⌜ λᴵ ⌝ (coins κ) tt P.≈ᶜ
    coins (mapCoins (λ (s , x) → ((s , tt) , x)) κ)
close-coins U (done x) = P.ret refl
close-coins U (toss μ h) = P.coin λ b → close-coins U (h b)

map-result : ∀ {I} (f : X → Y) (κ : Coins X)
  → coins {A = I} (mapCoins f κ) P.≈ᶜ (coins κ >>=ᶜ P.ret ∘ f)
map-result f (done x) = P.ret refl
map-result f (toss μ h) = P.coin λ b → map-result f (h b)

mapped-bind-calls : ∀ {I} (f : Y → Z) (κ : Coins X) (g : X → Coins Y)
  → coins {A = I} (mapCoins f (κ >>=ᶜᵒ g)) P.≈ᶜ
    (coins κ >>=ᶜ λ x → coins (mapCoins f (g x)))
mapped-bind-calls f (done x) g = P.≈ᶜ-refl
mapped-bind-calls f (toss μ h) g = P.coin λ b → mapped-bind-calls f (h b) g

pair-result : ∀ {I} (κ : Coins X) (ν : Coins Y) (f : X → Y → Z)
  → coins {A = I} (mapCoins (uncurry f) (pairCoins κ ν)) P.≈ᶜ
    (coins κ >>=ᶜ λ x → coins ν >>=ᶜ λ y → P.ret (f x y))
pair-result (done x) (done y) f = P.ret refl
pair-result (done x) (toss μ k) f = P.coin λ b → pair-result (done x) (k b) f
pair-result (toss μ k) ν f = P.coin λ b → pair-result (k b) ν f

selected-result : ∀ {I W} (f : W → X) (κ : Coins Y) (h : Y → Z) (k : Z → Coins W)
  → coins {A = I} (mapCoins f (mapCoins h κ >>=ᶜᵒ k)) P.≈ᶜ
    (coins κ >>=ᶜ λ y → coins (mapCoins f (k (h y))))
selected-result f κ h k = P.≈ᶜ-trans (mapped-bind-calls f (mapCoins h κ) k)
  (coins-map-bind h κ (λ z → coins (mapCoins f (k z))))

native-result : ∀ {I W} (f : (X × Y) × Z → W) (o : Z) (κ : Coins X) (ν : Coins Y)
  → coins {A = I} (mapCoins f (mapCoins swap (mapCoins (o ,_) (pairCoins κ ν)))) P.≈ᶜ
    (coins κ >>=ᶜ λ x → coins ν >>=ᶜ λ y → P.ret (f ((x , y) , o)))
native-result f o κ ν = P.≈ᶜ-trans
  (coins-map-compose swap f (mapCoins (o ,_) (pairCoins κ ν)))
  (P.≈ᶜ-trans (coins-map-compose (o ,_) (f ∘ swap) (pairCoins κ ν))
    (pair-result κ ν (λ x y → f ((x , y) , o))))

bind-map : ∀ {I} (f : X → Y) (t : P.Calls I X) (k : Y → P.Calls I Z)
  → (P.mapᶜ f t >>=ᶜ k) P.≈ᶜ (t >>=ᶜ k ∘ f)
bind-map f (P.ret x) k = P.≈ᶜ-refl
bind-map f (P.call c a h) k = P.call λ r → bind-map f (h r) k
bind-map f (P.coin μ h) k = P.coin λ b → bind-map f (h b) k
bind-map f P.dead k = P.dead

map-kernel : ∀ {I} (f : X → Y) {t u : P.Calls I X} → t ≈ᵏ u → P.mapᶜ f t ≈ᵏ P.mapᶜ f u
map-kernel f {t} {u} e = ≈ᵏ-trans (≈ᶜ⇒≈ᵏ (P.≈ᶜ-sym (>>=ᶜ-ret f t)))
  (≈ᵏ-trans (≈ᵏ->>=ᶜ e (λ _ → ≈ᵏ-refl)) (≈ᶜ⇒≈ᵏ (>>=ᶜ-ret f u)))

kernel-eval : {t u : P.Calls unitᴵ X} → t ≈ᵏ u → evalC t ≈Mℚ evalC u
kernel-eval {t = t} {u = u} e R = trans (evalC-⟦⟧ t none tt R)
  (trans (>>=⊥-congʳ (return⊥ ∘ proj₁) (⟦ t ⟧ none tt) (⟦ u ⟧ none tt)
    (run≈ᵏ e none tt) R) (sym (evalC-⟦⟧ u none tt R)))
