{-# OPTIONS --safe --without-K #-}

-- Call trees read as stochastic maps (`docs/uc-setup-ssp-dist.md` §2).  An
-- oracle is any strategy answering an interface from a state of its own; read
-- against one, a call tree is a sub-distribution over its result and the
-- oracle's next state (`⟦_⟧`), and trees agreeing against every oracle are
-- kernel-equal (`_≈ᵏ_`).  A protocol serves its export from an oracle for its
-- import (`_·_`), and grafting is serving (`⟦graft⟧`).
--
-- A sampling simulation `P ⊑ P′` sends each state of `P` to a distribution of
-- states of `P′` that commutes with every activation against every oracle:
-- SSProve's stable invariant (ssprove2023 Thm. 2.4) made stochastic, which is
-- what lazy against eager sampling needs; `sampling` builds one from
-- per-activation squares of call trees.  It survives tensoring with any
-- protocol (`⊑-⊗ˡ`, `⊑-⊗ʳ`) and leaves the readout of every closed composite
-- unchanged (`⊑-run`).

module CategoricalCrypto.SSP.Dist.Kernel where

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures

open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Partial
open import ProbabilisticLogic.Distribution.RationalDist.Setoid

open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Observation
open import CategoricalCrypto.SSP.Protocol

private variable
  A B C D : Iface
  S T U X Y Z : Set

------------------------------------------------------------------------
-- Oracles and the reading of a call tree

Oracle : Iface → Set → Set
Oracle A S = S → (c : Ch A) → Q A c → Dist⊥ (S × R A c)

⟦_⟧ : Calls A X → Oracle A S → S → Dist⊥ (X × S)
⟦ ret x ⟧      O s = return⊥ (x , s)
⟦ call c q k ⟧ O s = O s c q >>=⊥ λ p → ⟦ k (proj₂ p) ⟧ O (proj₁ p)
⟦ coin μ k ⟧   O s = μ >>=ᴹ λ b → ⟦ k b ⟧ O s
⟦ dead ⟧       O s = return-ℚ nothing

-- The interface without channels needs no answers.
none : Oracle unitᴵ ⊤
none _ ()

_∘ᴼ_ : Oracle B S → A ⇒ᴵ B → Oracle A S
(O ∘ᴼ m) s c q = Dmap⊥ (map₂ (re m)) (O s (ch m c) (qu m q))

infixl 1 _>>=ᶜ_
_>>=ᶜ_ : Calls A X → (X → Calls A Y) → Calls A Y
ret x      >>=ᶜ f = f x
call c q k >>=ᶜ f = call c q λ r → k r >>=ᶜ f
coin μ k   >>=ᶜ f = coin μ λ b → k b >>=ᶜ f
dead       >>=ᶜ f = dead

>>=ᶜ-ret : (f : X → Y) (t : Calls A X) → (t >>=ᶜ ret ∘ f) ≈ᶜ mapᶜ f t
>>=ᶜ-ret f (ret x)      = ret refl
>>=ᶜ-ret f (call c q k) = call λ r → >>=ᶜ-ret f (k r)
>>=ᶜ-ret f (coin μ k)   = coin λ b → >>=ᶜ-ret f (k b)
>>=ᶜ-ret f dead         = dead

infix 4 _≈ᵏ_
record _≈ᵏ_ (t t′ : Calls A X) : Set₁ where
  constructor mk≈ᵏ
  field run≈ᵏ : ∀ {S} (O : Oracle A S) s → ⟦ t ⟧ O s ≈Mℚ ⟦ t′ ⟧ O s
open _≈ᵏ_ public

≈ᵏ-refl : {t : Calls A X} → t ≈ᵏ t
≈ᵏ-refl = mk≈ᵏ λ _ _ _ → refl

≈ᵏ-sym : {t t′ : Calls A X} → t ≈ᵏ t′ → t′ ≈ᵏ t
≈ᵏ-sym e = mk≈ᵏ λ O s ξ → sym (run≈ᵏ e O s ξ)

≈ᵏ-trans : {t t′ t″ : Calls A X} → t ≈ᵏ t′ → t′ ≈ᵏ t″ → t ≈ᵏ t″
≈ᵏ-trans e e′ = mk≈ᵏ λ O s ξ → trans (run≈ᵏ e O s ξ) (run≈ᵏ e′ O s ξ)

≈ᵏ-isEquivalence : IsEquivalence (_≈ᵏ_ {A} {X})
≈ᵏ-isEquivalence = record { refl = ≈ᵏ-refl ; sym = ≈ᵏ-sym ; trans = ≈ᵏ-trans }

≈ᶜ⇒≈ᵏ : {t t′ : Calls A X} → t ≈ᶜ t′ → t ≈ᵏ t′
≈ᶜ⇒≈ᵏ e = mk≈ᵏ (go e)
  where
  go : {t t′ : Calls A X} → t ≈ᶜ t′ → ∀ {S} (O : Oracle A S) s → ⟦ t ⟧ O s ≈Mℚ ⟦ t′ ⟧ O s
  go (ret refl) O s = λ _ → refl
  go (call {c = c} {q} {k} {k′} h) O s =
    >>=⊥-congˡ (O s c q) (λ p → ⟦ k (proj₂ p) ⟧ O (proj₁ p)) (λ p → ⟦ k′ (proj₂ p) ⟧ O (proj₁ p))
               λ p → go (h (proj₂ p)) O (proj₁ p)
  go (coin {μ} {k} {k′} h) O s = >>=ᴹ-congˡ μ (λ b → ⟦ k b ⟧ O s) (λ b → ⟦ k′ b ⟧ O s) λ b → go (h b) O s
  go dead O s = λ _ → refl

⟦>>=ᶜ⟧ : (t : Calls A X) (f : X → Calls A Y) (O : Oracle A S) (s : S)
       → ⟦ t >>=ᶜ f ⟧ O s ≈Mℚ (⟦ t ⟧ O s >>=⊥ λ p → ⟦ f (proj₁ p) ⟧ O (proj₂ p))
⟦>>=ᶜ⟧ (ret x) f O s ξ = sym (>>=⊥-identityˡ (x , s) (λ p → ⟦ f (proj₁ p) ⟧ O (proj₂ p)) ξ)
⟦>>=ᶜ⟧ (call c q k) f O s ξ = trans
  (>>=⊥-congˡ (O s c q) (λ p → ⟦ k (proj₂ p) >>=ᶜ f ⟧ O (proj₁ p))
              (λ p → ⟦ k (proj₂ p) ⟧ O (proj₁ p) >>=⊥ λ p′ → ⟦ f (proj₁ p′) ⟧ O (proj₂ p′))
              (λ p → ⟦>>=ᶜ⟧ (k (proj₂ p)) f O (proj₁ p)) ξ)
  (sym (>>=⊥-assoc (O s c q) (λ p → ⟦ k (proj₂ p) ⟧ O (proj₁ p)) (λ p′ → ⟦ f (proj₁ p′) ⟧ O (proj₂ p′)) ξ))
⟦>>=ᶜ⟧ (coin μ k) f O s ξ = trans
  (>>=ᴹ-congˡ μ (λ b → ⟦ k b >>=ᶜ f ⟧ O s) (λ b → ⟦ k b ⟧ O s >>=⊥ λ p → ⟦ f (proj₁ p) ⟧ O (proj₂ p))
              (λ b → ⟦>>=ᶜ⟧ (k b) f O s) ξ)
  (sym (>>=ᴹ-assoc μ (λ b → ⟦ k b ⟧ O s) (kmaybe λ p → ⟦ f (proj₁ p) ⟧ O (proj₂ p)) ξ))
⟦>>=ᶜ⟧ dead f O s ξ = sym (>>=ᴹ-identityˡ nothing (kmaybe λ p → ⟦ f (proj₁ p) ⟧ O (proj₂ p)) ξ)

≈ᵏ->>=ᶜ : {t t′ : Calls A X} {f f′ : X → Calls A Y} → t ≈ᵏ t′ → (∀ x → f x ≈ᵏ f′ x) → (t >>=ᶜ f) ≈ᵏ (t′ >>=ᶜ f′)
≈ᵏ->>=ᶜ {t = t} {t′} {f} {f′} e h = mk≈ᵏ λ O s ξ → trans (⟦>>=ᶜ⟧ t f O s ξ) (trans
  (>>=⊥-cong {μ = ⟦ t ⟧ O s} {⟦ t′ ⟧ O s} {λ p → ⟦ f (proj₁ p) ⟧ O (proj₂ p)} {λ p → ⟦ f′ (proj₁ p) ⟧ O (proj₂ p)}
             (run≈ᵏ e O s) (λ p → run≈ᵏ (h (proj₁ p)) O (proj₂ p)) ξ)
  (sym (⟦>>=ᶜ⟧ t′ f′ O s ξ)))

⟦mapᶜ⟧ : (f : X → Y) (t : Calls A X) (O : Oracle A S) (s : S)
       → ⟦ mapᶜ f t ⟧ O s ≈Mℚ Dmap⊥ (map₁ f) (⟦ t ⟧ O s)
⟦mapᶜ⟧ f (ret x) O s ξ = sym (>>=⊥-identityˡ (x , s) (return⊥ ∘ map₁ f) ξ)
⟦mapᶜ⟧ f (call c q k) O s ξ = trans
  (>>=⊥-congˡ (O s c q) (λ p → ⟦ mapᶜ f (k (proj₂ p)) ⟧ O (proj₁ p))
              (λ p → Dmap⊥ (map₁ f) (⟦ k (proj₂ p) ⟧ O (proj₁ p)))
              (λ p → ⟦mapᶜ⟧ f (k (proj₂ p)) O (proj₁ p)) ξ)
  (sym (>>=⊥-assoc (O s c q) (λ p → ⟦ k (proj₂ p) ⟧ O (proj₁ p)) (return⊥ ∘ map₁ f) ξ))
⟦mapᶜ⟧ f (coin μ k) O s ξ = trans
  (>>=ᴹ-congˡ μ (λ b → ⟦ mapᶜ f (k b) ⟧ O s) (λ b → Dmap⊥ (map₁ f) (⟦ k b ⟧ O s))
              (λ b → ⟦mapᶜ⟧ f (k b) O s) ξ)
  (sym (>>=ᴹ-assoc μ (λ b → ⟦ k b ⟧ O s) (kmaybe (return⊥ ∘ map₁ f)) ξ))
⟦mapᶜ⟧ f dead O s ξ = sym (>>=ᴹ-identityˡ nothing (kmaybe (return⊥ ∘ map₁ f)) ξ)

⟦reindex⟧ : (m : A ⇒ᴵ B) (t : Calls A X) (O : Oracle B S) (s : S) → ⟦ reindex m t ⟧ O s ≈Mℚ ⟦ t ⟧ (O ∘ᴼ m) s
⟦reindex⟧ m (ret x) O s = λ _ → refl
⟦reindex⟧ m (call c q k) O s ξ = trans
  (>>=⊥-congˡ (O s (ch m c) (qu m q)) (λ p → ⟦ reindex m (k (re m (proj₂ p))) ⟧ O (proj₁ p))
              (λ p → ⟦ k (re m (proj₂ p)) ⟧ (O ∘ᴼ m) (proj₁ p))
              (λ p → ⟦reindex⟧ m (k (re m (proj₂ p))) O (proj₁ p)) ξ)
  (sym (Dmap⊥->>=⊥ (map₂ (re m)) (O s (ch m c) (qu m q)) (λ p → ⟦ k (proj₂ p) ⟧ (O ∘ᴼ m) (proj₁ p)) ξ))
⟦reindex⟧ m (coin μ k) O s =
  >>=ᴹ-congˡ μ (λ b → ⟦ reindex m (k b) ⟧ O s) (λ b → ⟦ k b ⟧ (O ∘ᴼ m) s) λ b → ⟦reindex⟧ m (k b) O s
⟦reindex⟧ m dead O s = λ _ → refl

-- A closed tree reads the same against any oracle.
evalC-⟦⟧ : (t : Calls unitᴵ X) (O : Oracle unitᴵ S) (s : S) → evalC t ≈Mℚ Dmap⊥ proj₁ (⟦ t ⟧ O s)
evalC-⟦⟧ (ret x) O s ξ = sym (>>=⊥-identityˡ (x , s) (return⊥ ∘ proj₁) ξ)
evalC-⟦⟧ (call () _ _) O s
evalC-⟦⟧ (coin μ k) O s ξ = trans
  (>>=ᴹ-congˡ μ (λ b → evalC (k b)) (λ b → Dmap⊥ proj₁ (⟦ k b ⟧ O s)) (λ b → evalC-⟦⟧ (k b) O s) ξ)
  (sym (>>=ᴹ-assoc μ (λ b → ⟦ k b ⟧ O s) (kmaybe (return⊥ ∘ proj₁)) ξ))
evalC-⟦⟧ {S = S} dead O s ξ = sym (>>=ᴹ-identityˡ nothing (kmaybe (return⊥ ∘ proj₁ {B = λ _ → S})) ξ)

------------------------------------------------------------------------
-- Samplers

-- A finite tree of coins: total, and blind to every oracle.
data Coins (X : Set) : Set where
  done : X → Coins X
  toss : Dist-ℚ Bool → (Bool → Coins X) → Coins X

coins : Coins X → Calls A X
coins (done x)   = ret x
coins (toss μ k) = coin μ λ b → coins (k b)

sample : Coins X → Dist-ℚ X
sample (done x)   = return-ℚ x
sample (toss μ k) = μ >>=ᴹ λ b → sample (k b)

⟦coins⟧ : (κ : Coins X) (f : X → Calls A Y) (O : Oracle A S) (s : S)
        → ⟦ coins κ >>=ᶜ f ⟧ O s ≈Mℚ (sample κ >>=ᴹ λ x → ⟦ f x ⟧ O s)
⟦coins⟧ (done x)   f O s ξ = sym (>>=ᴹ-identityˡ x (λ x → ⟦ f x ⟧ O s) ξ)
⟦coins⟧ (toss μ k) f O s ξ = trans
  (>>=ᴹ-congˡ μ (λ b → ⟦ coins (k b) >>=ᶜ f ⟧ O s) (λ b → sample (k b) >>=ᴹ λ x → ⟦ f x ⟧ O s)
              (λ b → ⟦coins⟧ (k b) f O s) ξ)
  (sym (>>=ᴹ-assoc μ (λ b → sample (k b)) (λ x → ⟦ f x ⟧ O s) ξ))

------------------------------------------------------------------------
-- Protocols serving from oracles

regroup : (X × Y) × Z → (X × Z) × Y
regroup ((x , y) , z) = (x , z) , y

regraft : (X × Y) × (Z × U) → ((X × Z) × Y) × U
regraft ((x , y) , (z , u)) = ((x , z) , y) , u

infixr 9 _·_
_·_ : (P : Protocol A B) → Oracle A S → Oracle B (St P × S)
(P · O) (p , s) c q = Dmap⊥ regroup (⟦ step P p c q ⟧ O s)

module _ (P₂ : Protocol B C) (P₁ : Protocol A B) (O : Oracle A S) where

  ⟦serve⟧ : {b : Ch B} (k : R B b → Calls B (St P₂ × Y)) (u : Calls A (St P₁ × R B b)) (s : S)
          → ⟦ serve P₂ P₁ k u ⟧ O s
            ≈Mℚ (⟦ u ⟧ O s >>=⊥ λ p → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p))) (proj₁ (proj₁ p)) ⟧ O (proj₂ p))
  ⟦serve⟧ k (ret x) s ξ =
    sym (>>=⊥-identityˡ (x , s) (λ p → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p))) (proj₁ (proj₁ p)) ⟧ O (proj₂ p)) ξ)
  ⟦serve⟧ k (call a q k₁) s ξ = trans
    (>>=⊥-congˡ (O s a q) (λ p → ⟦ serve P₂ P₁ k (k₁ (proj₂ p)) ⟧ O (proj₁ p))
                (λ p → ⟦ k₁ (proj₂ p) ⟧ O (proj₁ p) >>=⊥ λ p′ →
                         ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p′))) (proj₁ (proj₁ p′)) ⟧ O (proj₂ p′))
                (λ p → ⟦serve⟧ k (k₁ (proj₂ p)) (proj₁ p)) ξ)
    (sym (>>=⊥-assoc (O s a q) (λ p → ⟦ k₁ (proj₂ p) ⟧ O (proj₁ p))
                     (λ p′ → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p′))) (proj₁ (proj₁ p′)) ⟧ O (proj₂ p′)) ξ))
  ⟦serve⟧ k (coin μ k₁) s ξ = trans
    (>>=ᴹ-congˡ μ (λ b → ⟦ serve P₂ P₁ k (k₁ b) ⟧ O s)
                (λ b → ⟦ k₁ b ⟧ O s >>=⊥ λ p′ → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p′))) (proj₁ (proj₁ p′)) ⟧ O (proj₂ p′))
                (λ b → ⟦serve⟧ k (k₁ b) s) ξ)
    (sym (>>=ᴹ-assoc μ (λ b → ⟦ k₁ b ⟧ O s)
                     (kmaybe λ p′ → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p′))) (proj₁ (proj₁ p′)) ⟧ O (proj₂ p′)) ξ))
  ⟦serve⟧ k dead s ξ =
    sym (>>=ᴹ-identityˡ nothing (kmaybe λ p′ → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p′))) (proj₁ (proj₁ p′)) ⟧ O (proj₂ p′)) ξ)

  ⟦graft⟧ : (t : Calls B (St P₂ × Y)) (s₁ : St P₁) (s : S)
          → ⟦ graft P₂ P₁ t s₁ ⟧ O s ≈Mℚ Dmap⊥ regraft (⟦ t ⟧ (P₁ · O) (s₁ , s))
  ⟦graft⟧ (ret x) s₁ s ξ = sym (>>=⊥-identityˡ (x , s₁ , s) (return⊥ ∘ regraft) ξ)
  ⟦graft⟧ {Y = Y} (call b q k) s₁ s ξ = trans (⟦serve⟧ k ν s ξ) (trans
    (>>=⊥-congˡ (⟦ ν ⟧ O s) (λ p → ⟦ graft P₂ P₁ (k (proj₂ (proj₁ p))) (proj₁ (proj₁ p)) ⟧ O (proj₂ p))
                (λ p → Dmap⊥ regraft (K (regroup p))) (λ p → ⟦graft⟧ (k (proj₂ (proj₁ p))) (proj₁ (proj₁ p)) (proj₂ p)) ξ)
    (sym (trans (>>=⊥-congʳ (return⊥ ∘ regraft) (Dmap⊥ regroup (⟦ ν ⟧ O s) >>=⊥ K) (⟦ ν ⟧ O s >>=⊥ K ∘ regroup)
                            (Dmap⊥->>=⊥ regroup (⟦ ν ⟧ O s) K) ξ)
                (>>=⊥-assoc (⟦ ν ⟧ O s) (K ∘ regroup) (return⊥ ∘ regraft) ξ))))
    where
    ν = step P₁ s₁ b q
    K : (St P₁ × S) × R B b → Dist⊥ ((St P₂ × Y) × (St P₁ × S))
    K z = ⟦ k (proj₂ z) ⟧ (P₁ · O) (proj₁ z)
  ⟦graft⟧ (coin μ k) s₁ s ξ = trans
    (>>=ᴹ-congˡ μ (λ b → ⟦ graft P₂ P₁ (k b) s₁ ⟧ O s) (λ b → Dmap⊥ regraft (⟦ k b ⟧ (P₁ · O) (s₁ , s)))
                (λ b → ⟦graft⟧ (k b) s₁ s) ξ)
    (sym (>>=ᴹ-assoc μ (λ b → ⟦ k b ⟧ (P₁ · O) (s₁ , s)) (kmaybe (return⊥ ∘ regraft)) ξ))
  ⟦graft⟧ dead s₁ s ξ = sym (>>=ᴹ-identityˡ nothing (kmaybe (return⊥ ∘ regraft)) ξ)

------------------------------------------------------------------------
-- Sampling simulations

-- `ρ` samples an `O₂`-state from an `O₁`-state, and answering commutes with it.
Samples : (S → Dist-ℚ T) → Oracle A S → Oracle A T → Set
Samples ρ O₁ O₂ = ∀ s c q → (ρ s >>=ᴹ λ t → O₂ t c q)
                            ≈Mℚ (O₁ s c q >>=⊥ λ p → ρ (proj₁ p) >>=ᴹ λ t → return⊥ (t , proj₂ p))

sample-⟦⟧ : {ρ : S → Dist-ℚ T} {O₁ : Oracle A S} {O₂ : Oracle A T} → Samples {A = A} ρ O₁ O₂
          → (t : Calls A X) (s : S)
          → (ρ s >>=ᴹ λ u → ⟦ t ⟧ O₂ u) ≈Mℚ (⟦ t ⟧ O₁ s >>=⊥ λ p → ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u))
sample-⟦⟧ {ρ = ρ} h (ret x) s ξ = sym (>>=⊥-identityˡ (x , s) (λ p → ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u)) ξ)
sample-⟦⟧ {S = S} {T = T} {A = A} {X = X} {ρ = ρ} {O₁ = O₁} {O₂ = O₂} h (call c q k) s ξ = trans
  (sym (>>=ᴹ-assoc (ρ s) (λ u → O₂ u c q) (kmaybe K₂) ξ)) (trans
  (>>=ᴹ-congʳ (kmaybe K₂) (ρ s >>=ᴹ λ u → O₂ u c q) (O₁ s c q >>=⊥ H) (h s c q) ξ) (trans
  (>>=⊥-assoc (O₁ s c q) H K₂ ξ) (trans
  (>>=⊥-congˡ (O₁ s c q) (λ p → H p >>=⊥ K₂) (λ p → ⟦ k (proj₂ p) ⟧ O₁ (proj₁ p) >>=⊥ G) inner ξ)
  (sym (>>=⊥-assoc (O₁ s c q) (λ p → ⟦ k (proj₂ p) ⟧ O₁ (proj₁ p)) G ξ)))))
  where
  G : X × S → Dist⊥ (X × T)
  G p = ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u)
  K₂ : T × R A c → Dist⊥ (X × T)
  K₂ p = ⟦ k (proj₂ p) ⟧ O₂ (proj₁ p)
  H : S × R A c → Dist⊥ (T × R A c)
  H p = ρ (proj₁ p) >>=ᴹ λ u → return⊥ (u , proj₂ p)
  inner : ∀ p → (H p >>=⊥ K₂) ≈Mℚ (⟦ k (proj₂ p) ⟧ O₁ (proj₁ p) >>=⊥ G)
  inner p ξ = trans (>>=ᴹ-assoc (ρ (proj₁ p)) (λ u → return⊥ (u , proj₂ p)) (kmaybe K₂) ξ) (trans
    (>>=ᴹ-congˡ (ρ (proj₁ p)) (λ u → return⊥ (u , proj₂ p) >>=⊥ K₂) (λ u → ⟦ k (proj₂ p) ⟧ O₂ u)
                (λ u → >>=⊥-identityˡ (u , proj₂ p) K₂) ξ)
    (sample-⟦⟧ h (k (proj₂ p)) (proj₁ p) ξ))
sample-⟦⟧ {S = S} {T = T} {X = X} {ρ = ρ} {O₁ = O₁} {O₂ = O₂} h (coin μ k) s ξ = trans
  (>>=ᴹ-comm (ρ s) μ (λ u b → ⟦ k b ⟧ O₂ u) ξ) (trans
  (>>=ᴹ-congˡ μ (λ b → ρ s >>=ᴹ λ u → ⟦ k b ⟧ O₂ u) (λ b → ⟦ k b ⟧ O₁ s >>=⊥ G) (λ b → sample-⟦⟧ h (k b) s) ξ)
  (sym (>>=ᴹ-assoc μ (λ b → ⟦ k b ⟧ O₁ s) (kmaybe G) ξ)))
  where
  G : X × S → Dist⊥ (X × T)
  G p = ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u)
sample-⟦⟧ {ρ = ρ} h dead s ξ = trans (>>=ᴹ-const (ρ s) (return-ℚ nothing) ξ)
  (sym (>>=ᴹ-identityˡ nothing (kmaybe λ p → ρ (proj₂ p) >>=ᴹ λ u → return⊥ (proj₁ p , u)) ξ))

first : (S → Dist-ℚ T) → S × U → Dist-ℚ (T × U)
first ρ (s , u) = ρ s >>=ᴹ λ t → return-ℚ (t , u)

first-init : (ρ : S → Dist-ℚ T) {s : S} {t : T} → ρ s ≈Mℚ return-ℚ t → (u : U) → first ρ (s , u) ≈Mℚ return-ℚ (t , u)
first-init ρ {s} {t} e u ξ = trans (>>=ᴹ-congʳ (λ t′ → return-ℚ (t′ , u)) (ρ s) (return-ℚ t) e ξ)
  (>>=ᴹ-identityˡ t (λ t′ → return-ℚ (t′ , u)) ξ)

second : (S → Dist-ℚ T) → U × S → Dist-ℚ (U × T)
second ρ (u , s) = ρ s >>=ᴹ λ t → return-ℚ (u , t)

infix 4 _⊑_
record _⊑_ (P P′ : Protocol A B) : Set₁ where
  field ρ      : St P → Dist-ℚ (St P′)
        ρ-init : ρ (init P) ≈Mℚ return-ℚ (init P′)
        ρ-step : ∀ {S} (O : Oracle A S) → Samples {A = B} (first ρ) (P · O) (P′ · O)
open _⊑_ public

sampling : {P P′ : Protocol A B} (ρ : St P → Coins (St P′)) → sample (ρ (init P)) ≈Mℚ return-ℚ (init P′)
         → (∀ s c q → (coins (ρ s) >>=ᶜ λ s′ → step P′ s′ c q)
                      ≈ᵏ (step P s c q >>=ᶜ λ z → coins (ρ (proj₁ z)) >>=ᶜ λ s′ → ret (s′ , proj₂ z)))
         → P ⊑ P′
sampling {A = A} {B = B} {P = P} {P′ = P′} ρ e h = record { ρ = sample ∘ ρ ; ρ-init = e ; ρ-step = go }
  where
  go : ∀ {S} (O : Oracle A S) → Samples {A = B} (first (sample ∘ ρ)) (P · O) (P′ · O)
  go {S} O (p , s) c q ξ = trans
    (Dmap->>= (_, s) (sample (ρ p)) (λ t → (P′ · O) t c q) ξ) (trans
    (sym (>>=ᴹ-assoc (sample (ρ p)) (λ p′ → ⟦ step P′ p′ c q ⟧ O s) (kmaybe (return⊥ ∘ regroup)) ξ)) (trans
    (>>=⊥-congʳ (return⊥ ∘ regroup) (sample (ρ p) >>=ᴹ λ p′ → ⟦ step P′ p′ c q ⟧ O s) (⟦ t >>=ᶜ K ⟧ O s)
                (λ ξ′ → trans (sym (⟦coins⟧ (ρ p) (λ p′ → step P′ p′ c q) O s ξ′)) (run≈ᵏ (h p c q) O s ξ′)) ξ) (trans
    (>>=⊥-congʳ (return⊥ ∘ regroup) (⟦ t >>=ᶜ K ⟧ O s) (⟦ t ⟧ O s >>=⊥ L) (λ ξ′ → trans (⟦>>=ᶜ⟧ t K O s ξ′)
                (>>=⊥-congˡ (⟦ t ⟧ O s) (λ w → ⟦ K (proj₁ w) ⟧ O (proj₂ w)) L
                            (λ w → ⟦coins⟧ (ρ (proj₁ (proj₁ w))) (λ s′ → ret (s′ , proj₂ (proj₁ w))) O (proj₂ w)) ξ′)) ξ) (trans
    (>>=⊥-assoc (⟦ t ⟧ O s) L (return⊥ ∘ regroup) ξ)
    (sym (trans (Dmap⊥->>=⊥ regroup (⟦ t ⟧ O s) G ξ)
                (>>=⊥-congˡ (⟦ t ⟧ O s) (G ∘ regroup) (λ w → L w >>=⊥ return⊥ ∘ regroup) pt ξ)))))))
    where
    t = step P p c q
    K : St P × R B c → Calls _ (St P′ × R B c)
    K z = coins (ρ (proj₁ z)) >>=ᶜ λ s′ → ret (s′ , proj₂ z)
    L : (St P × R B c) × S → Dist⊥ ((St P′ × R B c) × S)
    L w = sample (ρ (proj₁ (proj₁ w))) >>=ᴹ λ p′ → return⊥ ((p′ , proj₂ (proj₁ w)) , proj₂ w)
    G : (St P × S) × R B c → Dist⊥ ((St P′ × S) × R B c)
    G z = first (sample ∘ ρ) (proj₁ z) >>=ᴹ λ t′ → return⊥ (t′ , proj₂ z)
    pt : ∀ w → G (regroup w) ≈Mℚ (L w >>=⊥ return⊥ ∘ regroup)
    pt ((p₁ , r) , s₁) ξ′ = trans (Dmap->>= (_, s₁) (sample (ρ p₁)) (λ t′ → return⊥ (t′ , r)) ξ′)
      (sym (trans (>>=ᴹ-assoc (sample (ρ p₁)) (λ p′ → return⊥ ((p′ , r) , s₁)) (kmaybe (return⊥ ∘ regroup)) ξ′)
                  (>>=ᴹ-congˡ (sample (ρ p₁)) (λ p′ → return⊥ ((p′ , r) , s₁) >>=⊥ return⊥ ∘ regroup)
                              (λ p′ → return⊥ ((p′ , s₁) , r)) (λ p′ → >>=⊥-identityˡ ((p′ , r) , s₁) (return⊥ ∘ regroup)) ξ′)))

------------------------------------------------------------------------
-- Tensors and closed composites

-- A step relabelled into a tensor is served as the factor's, its state relabelled after.
·-mapᶜ : (m : A ⇒ᴵ C) (f : X → Y) (t : Calls A (X × Z)) (O : Oracle C S) (s : S)
       → Dmap⊥ regroup (⟦ mapᶜ (map₁ f) (reindex m t) ⟧ O s) ≈Mℚ Dmap⊥ (map₁ (map₁ f)) (Dmap⊥ regroup (⟦ t ⟧ (O ∘ᴼ m) s))
·-mapᶜ m f t O s ξ = trans
  (>>=⊥-congʳ (return⊥ ∘ regroup) (⟦ mapᶜ (map₁ f) (reindex m t) ⟧ O s) (Dmap⊥ (map₁ (map₁ f)) (⟦ t ⟧ (O ∘ᴼ m) s))
              (λ ξ′ → trans (⟦mapᶜ⟧ (map₁ f) (reindex m t) O s ξ′)
                            (>>=⊥-congʳ (return⊥ ∘ map₁ (map₁ f)) (⟦ reindex m t ⟧ O s) (⟦ t ⟧ (O ∘ᴼ m) s) (⟦reindex⟧ m t O s) ξ′)) ξ)
  (trans (Dmap⊥->>=⊥ (map₁ (map₁ f)) (⟦ t ⟧ (O ∘ᴼ m) s) (return⊥ ∘ regroup) ξ)
         (sym (Dmap⊥->>=⊥ regroup (⟦ t ⟧ (O ∘ᴼ m) s) (return⊥ ∘ map₁ (map₁ f)) ξ)))

⊑-⊗ˡ : {P P′ : Protocol A B} (N : Protocol C D) → P ⊑ P′ → P ⊗ᵖ N ⊑ P′ ⊗ᵖ N
⊑-⊗ˡ {A = A} {B = B} {C = C} {D = D} {P = P} {P′ = P′} N e = record
  { ρ = first (ρ e) ; ρ-init = first-init (ρ e) (ρ-init e) (init N) ; ρ-step = go }
  where
  G′ : ∀ {S Y} → ((St P × St N) × S) × Y → Dist⊥ (((St P′ × St N) × S) × Y)
  G′ z = first (first (ρ e)) (proj₁ z) >>=ᴹ λ t → return⊥ (t , proj₂ z)

  go : ∀ {S} (O : Oracle (A ⊗ᴵ C) S) → Samples {A = B ⊗ᴵ D} (first (first (ρ e))) ((P ⊗ᵖ N) · O) ((P′ ⊗ᵖ N) · O)
  go {S} O ((p , n) , s) (inj₁ b) q ξ = trans
    (Dmap->>= (_, s) (first (ρ e) (p , n)) (λ t → ((P′ ⊗ᵖ N) · O) t (inj₁ b) q) ξ) (trans
    (Dmap->>= (_, n) (ρ e p) (λ t → ((P′ ⊗ᵖ N) · O) (t , s) (inj₁ b) q) ξ) (trans
    (>>=ᴹ-congˡ (ρ e p) (λ p′ → ((P′ ⊗ᵖ N) · O) ((p′ , n) , s) (inj₁ b) q) (λ p′ → Dmap⊥ f (ν′ p′))
                (λ p′ → ·-mapᶜ ι₁ (_, n) (step P′ p′ b q) O s) ξ) (trans
    (sym (>>=ᴹ-assoc (ρ e p) ν′ (kmaybe (return⊥ ∘ f)) ξ)) (trans
    (>>=⊥-congʳ (return⊥ ∘ f) (ρ e p >>=ᴹ ν′) (ν >>=⊥ G)
                (λ ξ′ → trans (sym (Dmap->>= (_, s) (ρ e p) (λ t → (P′ · O₁) t b q) ξ′)) (ρ-step e O₁ (p , s) b q ξ′)) ξ) (trans
    (>>=⊥-assoc ν G (return⊥ ∘ f) ξ)
    (sym (trans (>>=⊥-congʳ G′ (((P ⊗ᵖ N) · O) ((p , n) , s) (inj₁ b) q) (Dmap⊥ f ν) (·-mapᶜ ι₁ (_, n) (step P p b q) O s) ξ)
         (trans (Dmap⊥->>=⊥ f ν G′ ξ) (>>=⊥-congˡ ν (G′ ∘ f) (λ z → G z >>=⊥ return⊥ ∘ f) pt ξ)))))))))
    where
    O₁ : Oracle A S
    O₁ = O ∘ᴼ ι₁ {A = A} {B = C}
    f : ∀ {X} → (X × S) × R B b → ((X × St N) × S) × R B b
    f = map₁ (map₁ (_, n))
    ν : Dist⊥ ((St P × S) × R B b)
    ν = (P · O₁) (p , s) b q
    ν′ : St P′ → Dist⊥ ((St P′ × S) × R B b)
    ν′ p′ = (P′ · O₁) (p′ , s) b q
    G : (St P × S) × R B b → Dist⊥ ((St P′ × S) × R B b)
    G z = first (ρ e) (proj₁ z) >>=ᴹ λ t → return⊥ (t , proj₂ z)
    pt : ∀ z → G′ (f z) ≈Mℚ (G z >>=⊥ return⊥ ∘ f)
    pt ((p₁ , s₁) , y) ξ′ = trans (Dmap->>= (_, s₁) (first (ρ e) (p₁ , n)) (λ t → return⊥ (t , y)) ξ′) (trans
      (Dmap->>= (_, n) (ρ e p₁) (λ t → return⊥ ((t , s₁) , y)) ξ′)
      (sym (trans (>>=ᴹ-assoc (first (ρ e) (p₁ , s₁)) (λ t → return⊥ (t , y)) (kmaybe (return⊥ ∘ f)) ξ′) (trans
           (>>=ᴹ-congˡ (first (ρ e) (p₁ , s₁)) (λ t → return⊥ (t , y) >>=⊥ return⊥ ∘ f) (λ t → return⊥ (f (t , y)))
                       (λ t → >>=⊥-identityˡ (t , y) (return⊥ ∘ f)) ξ′)
           (Dmap->>= (_, s₁) (ρ e p₁) (λ t → return⊥ (f (t , y))) ξ′)))))
  go {S} O ((p , n) , s) (inj₂ d) q ξ = trans
    (Dmap->>= (_, s) (first (ρ e) (p , n)) (λ t → ((P′ ⊗ᵖ N) · O) t (inj₂ d) q) ξ) (trans
    (Dmap->>= (_, n) (ρ e p) (λ t → ((P′ ⊗ᵖ N) · O) (t , s) (inj₂ d) q) ξ) (trans
    (>>=ᴹ-congˡ (ρ e p) (λ p′ → ((P′ ⊗ᵖ N) · O) ((p′ , n) , s) (inj₂ d) q) (λ p′ → Dmap⊥ (f p′) ν)
                (λ p′ → ·-mapᶜ ι₂ (p′ ,_) (step N n d q) O s) ξ) (trans
    (>>=ᴹ-comm⊥ (ρ e p) ν (λ p′ z → return⊥ (f p′ z)) ξ)
    (sym (trans (>>=⊥-congʳ G′ (((P ⊗ᵖ N) · O) ((p , n) , s) (inj₂ d) q) (Dmap⊥ (f p) ν) (·-mapᶜ ι₂ (p ,_) (step N n d q) O s) ξ)
         (trans (Dmap⊥->>=⊥ (f p) ν G′ ξ) (>>=⊥-congˡ ν (G′ ∘ f p) (λ z → ρ e p >>=ᴹ λ p′ → return⊥ (f p′ z)) pt ξ)))))))
    where
    f : ∀ {X} → X → (St N × S) × R D d → ((X × St N) × S) × R D d
    f x = map₁ (map₁ (x ,_))
    ν : Dist⊥ ((St N × S) × R D d)
    ν = (N · (O ∘ᴼ ι₂ {B = C} {A = A})) (n , s) d q
    pt : ∀ z → G′ (f p z) ≈Mℚ (ρ e p >>=ᴹ λ p′ → return⊥ (f p′ z))
    pt ((n₁ , s₁) , y) ξ′ = trans (Dmap->>= (_, s₁) (first (ρ e) (p , n₁)) (λ t → return⊥ (t , y)) ξ′)
                                  (Dmap->>= (_, n₁) (ρ e p) (λ t → return⊥ ((t , s₁) , y)) ξ′)

⊑-⊗ʳ : {P P′ : Protocol A B} (N : Protocol C D) → P ⊑ P′ → N ⊗ᵖ P ⊑ N ⊗ᵖ P′
⊑-⊗ʳ {A = A} {B = B} {C = C} {D = D} {P = P} {P′ = P′} N e = record
  { ρ = second (ρ e) ; ρ-step = go
  ; ρ-init = λ ξ → trans (>>=ᴹ-congʳ (λ t → return-ℚ (init N , t)) (ρ e (init P)) (return-ℚ (init P′)) (ρ-init e) ξ)
                         (>>=ᴹ-identityˡ (init P′) (λ t → return-ℚ (init N , t)) ξ) }
  where
  G′ : ∀ {S Y} → ((St N × St P) × S) × Y → Dist⊥ (((St N × St P′) × S) × Y)
  G′ z = first (second (ρ e)) (proj₁ z) >>=ᴹ λ t → return⊥ (t , proj₂ z)

  go : ∀ {S} (O : Oracle (C ⊗ᴵ A) S) → Samples {A = D ⊗ᴵ B} (first (second (ρ e))) ((N ⊗ᵖ P) · O) ((N ⊗ᵖ P′) · O)
  go {S} O ((n , p) , s) (inj₁ c) q ξ = trans
    (Dmap->>= (_, s) (second (ρ e) (n , p)) (λ t → ((N ⊗ᵖ P′) · O) t (inj₁ c) q) ξ) (trans
    (Dmap->>= (n ,_) (ρ e p) (λ t → ((N ⊗ᵖ P′) · O) (t , s) (inj₁ c) q) ξ) (trans
    (>>=ᴹ-congˡ (ρ e p) (λ p′ → ((N ⊗ᵖ P′) · O) ((n , p′) , s) (inj₁ c) q) (λ p′ → Dmap⊥ (f p′) ν)
                (λ p′ → ·-mapᶜ ι₁ (_, p′) (step N n c q) O s) ξ) (trans
    (>>=ᴹ-comm⊥ (ρ e p) ν (λ p′ z → return⊥ (f p′ z)) ξ)
    (sym (trans (>>=⊥-congʳ G′ (((N ⊗ᵖ P) · O) ((n , p) , s) (inj₁ c) q) (Dmap⊥ (f p) ν) (·-mapᶜ ι₁ (_, p) (step N n c q) O s) ξ)
         (trans (Dmap⊥->>=⊥ (f p) ν G′ ξ) (>>=⊥-congˡ ν (G′ ∘ f p) (λ z → ρ e p >>=ᴹ λ p′ → return⊥ (f p′ z)) pt ξ)))))))
    where
    f : ∀ {X} → X → (St N × S) × R D c → ((St N × X) × S) × R D c
    f x = map₁ (map₁ (_, x))
    ν : Dist⊥ ((St N × S) × R D c)
    ν = (N · (O ∘ᴼ ι₁ {A = C} {B = A})) (n , s) c q
    pt : ∀ z → G′ (f p z) ≈Mℚ (ρ e p >>=ᴹ λ p′ → return⊥ (f p′ z))
    pt ((n₁ , s₁) , y) ξ′ = trans (Dmap->>= (_, s₁) (second (ρ e) (n₁ , p)) (λ t → return⊥ (t , y)) ξ′)
                                  (Dmap->>= (n₁ ,_) (ρ e p) (λ t → return⊥ ((t , s₁) , y)) ξ′)
  go {S} O ((n , p) , s) (inj₂ b) q ξ = trans
    (Dmap->>= (_, s) (second (ρ e) (n , p)) (λ t → ((N ⊗ᵖ P′) · O) t (inj₂ b) q) ξ) (trans
    (Dmap->>= (n ,_) (ρ e p) (λ t → ((N ⊗ᵖ P′) · O) (t , s) (inj₂ b) q) ξ) (trans
    (>>=ᴹ-congˡ (ρ e p) (λ p′ → ((N ⊗ᵖ P′) · O) ((n , p′) , s) (inj₂ b) q) (λ p′ → Dmap⊥ f (ν′ p′))
                (λ p′ → ·-mapᶜ ι₂ (n ,_) (step P′ p′ b q) O s) ξ) (trans
    (sym (>>=ᴹ-assoc (ρ e p) ν′ (kmaybe (return⊥ ∘ f)) ξ)) (trans
    (>>=⊥-congʳ (return⊥ ∘ f) (ρ e p >>=ᴹ ν′) (ν >>=⊥ G)
                (λ ξ′ → trans (sym (Dmap->>= (_, s) (ρ e p) (λ t → (P′ · O₂) t b q) ξ′)) (ρ-step e O₂ (p , s) b q ξ′)) ξ) (trans
    (>>=⊥-assoc ν G (return⊥ ∘ f) ξ)
    (sym (trans (>>=⊥-congʳ G′ (((N ⊗ᵖ P) · O) ((n , p) , s) (inj₂ b) q) (Dmap⊥ f ν) (·-mapᶜ ι₂ (n ,_) (step P p b q) O s) ξ)
         (trans (Dmap⊥->>=⊥ f ν G′ ξ) (>>=⊥-congˡ ν (G′ ∘ f) (λ z → G z >>=⊥ return⊥ ∘ f) pt ξ)))))))))
    where
    O₂ : Oracle A S
    O₂ = O ∘ᴼ ι₂ {B = A} {A = C}
    f : ∀ {X} → (X × S) × R B b → ((St N × X) × S) × R B b
    f = map₁ (map₁ (n ,_))
    ν : Dist⊥ ((St P × S) × R B b)
    ν = (P · O₂) (p , s) b q
    ν′ : St P′ → Dist⊥ ((St P′ × S) × R B b)
    ν′ p′ = (P′ · O₂) (p′ , s) b q
    G : (St P × S) × R B b → Dist⊥ ((St P′ × S) × R B b)
    G z = first (ρ e) (proj₁ z) >>=ᴹ λ t → return⊥ (t , proj₂ z)
    pt : ∀ z → G′ (f z) ≈Mℚ (G z >>=⊥ return⊥ ∘ f)
    pt ((p₁ , s₁) , y) ξ′ = trans (Dmap->>= (_, s₁) (second (ρ e) (n , p₁)) (λ t → return⊥ (t , y)) ξ′) (trans
      (Dmap->>= (n ,_) (ρ e p₁) (λ t → return⊥ ((t , s₁) , y)) ξ′)
      (sym (trans (>>=ᴹ-assoc (first (ρ e) (p₁ , s₁)) (λ t → return⊥ (t , y)) (kmaybe (return⊥ ∘ f)) ξ′) (trans
           (>>=ᴹ-congˡ (first (ρ e) (p₁ , s₁)) (λ t → return⊥ (t , y) >>=⊥ return⊥ ∘ f) (λ t → return⊥ (f (t , y)))
                       (λ t → >>=⊥-identityˡ (t , y) (return⊥ ∘ f)) ξ′)
           (Dmap->>= (_, s₁) (ρ e p₁) (λ t → return⊥ (f (t , y))) ξ′)))))

-- The readout of a closed composite: the distinguisher's activation, read against the rest.
run-read : (D : Protocol B Ωᴵ) (P : Protocol A B) (G : Protocol unitᴵ A)
         → runᵖ ((D ∘ᵖ P) ∘ᵖ G) ≈Mℚ Dmap⊥ (λ z → proj₂ (proj₁ z)) (⟦ step D (init D) tt tt ⟧ (P · (G · none)) (init P , init G , tt))
run-read D P G ξ = trans
  (evalC-⟦⟧ (mapᶜ proj₂ u₂) none tt ξ) (trans
  (>>=⊥-congʳ (λ z → return⊥ (proj₁ z)) (⟦ mapᶜ proj₂ u₂ ⟧ none tt) (Dmap⊥ (map₁ proj₂) (⟦ u₂ ⟧ none tt)) (⟦mapᶜ⟧ proj₂ u₂ none tt) ξ) (trans
  (Dmap⊥->>=⊥ (map₁ proj₂) (⟦ u₂ ⟧ none tt) (λ z → return⊥ (proj₁ z)) ξ) (trans
  (>>=⊥-congʳ (λ z → return⊥ (proj₂ (proj₁ z))) (⟦ u₂ ⟧ none tt) (Dmap⊥ regraft (Dmap⊥ regraft μ))
              (λ ξ′ → trans (⟦graft⟧ (D ∘ᵖ P) G none u₁ (init G) tt ξ′)
                            (>>=⊥-congʳ (return⊥ ∘ regraft) (⟦ u₁ ⟧ (G · none) (init G , tt)) (Dmap⊥ regraft μ)
                                        (⟦graft⟧ D P (G · none) u₀ (init P) (init G , tt)) ξ′)) ξ) (trans
  (Dmap⊥->>=⊥ regraft (Dmap⊥ regraft μ) (λ z → return⊥ (proj₂ (proj₁ z))) ξ)
  (Dmap⊥->>=⊥ regraft μ (λ z → return⊥ (proj₂ (proj₁ (regraft z)))) ξ)))))
  where
  u₀ = step D (init D) tt tt
  u₁ = graft D P u₀ (init P)
  u₂ = graft (D ∘ᵖ P) G u₁ (init G)
  μ = ⟦ u₀ ⟧ (P · (G · none)) (init P , init G , tt)

⊑-run : {P P′ : Protocol A B} → P ⊑ P′ → (D : Protocol B Ωᴵ) (G : Protocol unitᴵ A)
      → runᵖ ((D ∘ᵖ P) ∘ᵖ G) ≈Mℚ runᵖ ((D ∘ᵖ P′) ∘ᵖ G)
⊑-run {P = P} {P′ = P′} e D G ξ = trans (run-read D P G ξ) (trans
  (>>=⊥-congˡ μ (λ w → return⊥ (proj₂ (proj₁ w))) (λ w → H w >>=⊥ return⊥ ∘ π′) pt ξ) (trans
  (sym (>>=⊥-assoc μ H (return⊥ ∘ π′) ξ)) (trans
  (>>=⊥-congʳ (return⊥ ∘ π′) (μ >>=⊥ H) (return-ℚ z₀′ >>=ᴹ λ v → ⟦ u₀ ⟧ (P′ · O) v)
              (λ ξ′ → trans (sym (sample-⟦⟧ (ρ-step e O) u₀ z₀ ξ′))
                            (>>=ᴹ-congʳ (λ v → ⟦ u₀ ⟧ (P′ · O) v) (first (ρ e) z₀) (return-ℚ z₀′)
                                        (first-init (ρ e) (ρ-init e) (init G , tt)) ξ′)) ξ) (trans
  (>>=⊥-congʳ (return⊥ ∘ π′) (return-ℚ z₀′ >>=ᴹ λ v → ⟦ u₀ ⟧ (P′ · O) v) (⟦ u₀ ⟧ (P′ · O) z₀′)
              (>>=ᴹ-identityˡ z₀′ (λ v → ⟦ u₀ ⟧ (P′ · O) v)) ξ)
  (sym (run-read D P′ G ξ))))))
  where
  O = G · none
  u₀ = step D (init D) tt tt
  z₀ = init P , init G , tt
  z₀′ = init P′ , init G , tt
  μ = ⟦ u₀ ⟧ (P · O) z₀
  π′ : (St D × Bool) × (St P′ × St G × ⊤) → Bool
  π′ z = proj₂ (proj₁ z)
  H : (St D × Bool) × (St P × St G × ⊤) → Dist⊥ ((St D × Bool) × (St P′ × St G × ⊤))
  H w = first (ρ e) (proj₂ w) >>=ᴹ λ v → return⊥ (proj₁ w , v)
  pt : ∀ w → return⊥ (proj₂ (proj₁ w)) ≈Mℚ (H w >>=⊥ return⊥ ∘ π′)
  pt w ξ′ = sym (trans (>>=ᴹ-assoc (first (ρ e) (proj₂ w)) (λ v → return⊥ (proj₁ w , v)) (kmaybe (return⊥ ∘ π′)) ξ′) (trans
    (>>=ᴹ-congˡ (first (ρ e) (proj₂ w)) (λ v → return⊥ (proj₁ w , v) >>=⊥ return⊥ ∘ π′) (λ _ → return⊥ (proj₂ (proj₁ w)))
                (λ v → >>=⊥-identityˡ (proj₁ w , v) (return⊥ ∘ π′)) ξ′)
    (>>=ᴹ-const (first (ρ e) (proj₂ w)) (return⊥ (proj₂ (proj₁ w))) ξ′)))
