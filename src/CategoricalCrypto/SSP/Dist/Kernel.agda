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
-- what lazy against eager sampling needs.  It survives tensoring with any
-- protocol (`⊑-⊗ˡ`, `⊑-⊗ʳ`) and leaves the readout of every closed composite
-- unchanged (`⊑-run`).

module CategoricalCrypto.SSP.Dist.Kernel where

open import Data.Bool.Base using (Bool)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product.Base
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (_∘_)
open import Level
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Structures using (IsEquivalence)

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

-- Sampling the first component.
first : (S → Dist-ℚ T) → S × U → Dist-ℚ (T × U)
first ρ (s , u) = ρ s >>=ᴹ λ t → return-ℚ (t , u)

first-bind : (ρ : S → Dist-ℚ T) (s : S) (u : U) (k : T × U → Dist-ℚ X)
           → (first ρ (s , u) >>=ᴹ k) ≈Mℚ (ρ s >>=ᴹ λ t → k (t , u))
first-bind ρ s u k ξ = trans (>>=ᴹ-assoc (ρ s) (λ t → return-ℚ (t , u)) k ξ)
  (>>=ᴹ-congˡ (ρ s) (λ t → return-ℚ (t , u) >>=ᴹ k) (λ t → k (t , u)) (λ t → >>=ᴹ-identityˡ (t , u) k) ξ)

first-init : (ρ : S → Dist-ℚ T) {s : S} {t : T} → ρ s ≈Mℚ return-ℚ t → (u : U) → first ρ (s , u) ≈Mℚ return-ℚ (t , u)
first-init ρ {s} {t} e u ξ = trans (>>=ᴹ-congʳ (λ t′ → return-ℚ (t′ , u)) (ρ s) (return-ℚ t) e ξ)
  (>>=ᴹ-identityˡ t (λ t′ → return-ℚ (t′ , u)) ξ)

infix 4 _⊑_
record _⊑_ (P P′ : Protocol A B) : Set₁ where
  field ρ      : St P → Dist-ℚ (St P′)
        ρ-init : ρ (init P) ≈Mℚ return-ℚ (init P′)
        ρ-step : ∀ {S} (O : Oracle A S) → Samples {A = B} (first ρ) (P · O) (P′ · O)
open _⊑_ public
