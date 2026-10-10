{-# OPTIONS --safe --without-K #-}

-- Nondeterministic choice in SSP, compiled pick-ahead
-- (`docs/uc-setup-nondeterministic.md` §2.4).  `Calls⁺ A S⃗` is `Calls A` with
-- `choose i k`: resume `k` with a pick for site `i`.  The sites of `S⃗` are the
-- channels of `Cᴵ⟦ S⃗ ⟧`, one choice interface `Cᴵ S` per entry, on which a pick
-- is a query answered `tt` — the choice factor ⊤ ⇿ S read call/return
-- (`flat-Cᴵ`).  `⌈ P ⌉` serves `Cᴵ⟦ S⃗ ⟧` beside `P`'s export: a pick is queued
-- on its site, a `choose` pops its site's oldest pick, and an empty queue is
-- `dead`.  A call/return step can neither call its export nor suspend, so a
-- pick has to arrive before the activation that consumes it.  `_∘⁺_` and
-- `_⊗⁺_` concatenate site lists, the lower (left) factor's first, as the grade
-- of `_∙_` does.  Site lists are explicit arguments wherever only `Cᴵ⟦_⟧` or
-- `Queues` mentions them: neither function is injective.
--
-- `⌈_⌉` is no `StdUCMorphism`: one acts on protocols by a functor, `A ⇒ B` to
-- `F A ⇒ F B`, while `⌈ P ⌉`'s codomain `Cᴵ⟦ S⃗ ⟧ ⊗ᴵ B` depends on `P`'s
-- sites.  It lands in graded homs `A ⇒ T₀ Cᴵ⟦ S⃗ ⟧ B` instead, and preserves
-- identities and composition only up to the unitor and the regrouping `join`
-- (`⌈⌉-plain`, `Choice.Compose`).  None is needed: `Protocol⁺` is syntax and
-- `⌈_⌉` its meaning, ND_B's morphisms at choice grades being the compiled
-- protocols.

open import Class.DecEq
open import Data.Bool.Base using (Bool)
open import Data.List.Base using (List; []; _∷_; _++_; _∷ʳ_)
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; maybe′)
open import Data.Product.Base
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.Unit.Base
open import Function.Base using (const; id; _∘_)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Level using (suc; 0ℓ)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Construct.Closure.Equivalence as EqC

open import ProbabilisticLogic.Distribution.RationalDist using (Dist-ℚ)

import CategoricalCrypto.Iface as Flat
open import CategoricalCrypto.SSP.Iface
open import CategoricalCrypto.SSP.Protocol

module CategoricalCrypto.ND.SSP.Choice where

private variable
  A A′ B C D : Iface
  S : Set
  S⃗ T⃗ : List Set
  X X′ Y : Set

------------------------------------------------------------------------
-- Choice interfaces
------------------------------------------------------------------------

Cᴵ : Set → Iface
Cᴵ S = record { Ch = ⊤ ; Q = const S ; R = const ⊤ ; Ch-dec = DecEq-⊤ }

Cᴵ⟦_⟧ : List Set → Iface
Cᴵ⟦ [] ⟧    = unitᴵ
Cᴵ⟦ S ∷ S⃗ ⟧ = Cᴵ S ⊗ᴵ Cᴵ⟦ S⃗ ⟧

flat-Cᴵ : (Flat.Pos (flat (Cᴵ S)) ↔ ⊤) × (Flat.Neg (flat (Cᴵ S)) ↔ S)
flat-Cᴵ = mk↔ₛ′ proj₂ (tt ,_) (λ _ → refl) (λ _ → refl) , mk↔ₛ′ proj₂ (tt ,_) (λ _ → refl) (λ _ → refl)

tt⟦_⟧ : (S⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) → R Cᴵ⟦ S⃗ ⟧ i
tt⟦ S ∷ S⃗ ⟧ (inj₁ _) = tt
tt⟦ S ∷ S⃗ ⟧ (inj₂ i) = tt⟦ S⃗ ⟧ i

tt⟦⟧-unique : (S⃗ : List Set) {i : Ch Cᴵ⟦ S⃗ ⟧} (r : R Cᴵ⟦ S⃗ ⟧ i) → r ≡ tt⟦ S⃗ ⟧ i
tt⟦⟧-unique (S ∷ S⃗) {inj₁ _} _ = refl
tt⟦⟧-unique (S ∷ S⃗) {inj₂ _} r = tt⟦⟧-unique S⃗ r

-- The regrouping of a concatenation, from the unitor and associator: `split`
-- is ND_B's comparison φ at the choice part, `join` its inverse.
join : (S⃗ T⃗ : List Set) → Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗ ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ++ T⃗ ⟧
join []      T⃗ = λᴵ
join (S ∷ S⃗) T⃗ = (idᴵ ⊗ᴵᴵ join S⃗ T⃗) ∘ᴵ αᴵ

split : (S⃗ T⃗ : List Set) → Cᴵ⟦ S⃗ ++ T⃗ ⟧ ⇒ᴵ Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗ ⟧
split []      T⃗ = ι₂
split (S ∷ S⃗) T⃗ = αᴵ⁻¹ ∘ᴵ (idᴵ ⊗ᴵᴵ split S⃗ T⃗)

split-join : (S⃗ T⃗ : List Set) (x : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗ ⟧)) → ch (split S⃗ T⃗) (ch (join S⃗ T⃗) x) ≡ x
split-join []      T⃗ (inj₂ _)        = refl
split-join (S ∷ S⃗) T⃗ (inj₁ (inj₁ _)) = refl
split-join (S ∷ S⃗) T⃗ (inj₁ (inj₂ i)) = cong (Sum.map₁ inj₂) (split-join S⃗ T⃗ (inj₁ i))
split-join (S ∷ S⃗) T⃗ (inj₂ j)        = cong (Sum.map₁ inj₂) (split-join S⃗ T⃗ (inj₂ j))

join-split : (S⃗ T⃗ : List Set) (c : Ch Cᴵ⟦ S⃗ ++ T⃗ ⟧) → ch (join S⃗ T⃗) (ch (split S⃗ T⃗) c) ≡ c
join-split []      T⃗ _        = refl
join-split (S ∷ S⃗) T⃗ (inj₁ _) = refl
join-split (S ∷ S⃗) T⃗ (inj₂ c) = trans (shift (ch (split S⃗ T⃗) c)) (cong inj₂ (join-split S⃗ T⃗ c))
  where
  shift : (y : Ch (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ Cᴵ⟦ T⃗ ⟧)) → ch (join (S ∷ S⃗) T⃗) (Sum.map₁ inj₂ y) ≡ inj₂ (ch (join S⃗ T⃗) y)
  shift (inj₁ _) = refl
  shift (inj₂ _) = refl

-- A pick for a relocated site, brought back.
↓ˡ : (S⃗ T⃗ : List Set) {i : Ch Cᴵ⟦ S⃗ ⟧} → Q Cᴵ⟦ S⃗ ++ T⃗ ⟧ (ch (join S⃗ T⃗) (inj₁ i)) → Q Cᴵ⟦ S⃗ ⟧ i
↓ˡ (S ∷ S⃗) T⃗ {inj₁ _} p = p
↓ˡ (S ∷ S⃗) T⃗ {inj₂ _} p = ↓ˡ S⃗ T⃗ p

↓ʳ : (S⃗ T⃗ : List Set) {j : Ch Cᴵ⟦ T⃗ ⟧} → Q Cᴵ⟦ S⃗ ++ T⃗ ⟧ (ch (join S⃗ T⃗) (inj₂ j)) → Q Cᴵ⟦ T⃗ ⟧ j
↓ʳ []      T⃗ p = p
↓ʳ (S ∷ S⃗) T⃗ p = ↓ʳ S⃗ T⃗ p

------------------------------------------------------------------------
-- Call trees with choices
------------------------------------------------------------------------

data Calls⁺ (A : Iface) (S⃗ : List Set) (X : Set) : Set where
  ret    : X → Calls⁺ A S⃗ X
  call   : (c : Ch A) → Q A c → (R A c → Calls⁺ A S⃗ X) → Calls⁺ A S⃗ X
  coin   : Dist-ℚ Bool → (Bool → Calls⁺ A S⃗ X) → Calls⁺ A S⃗ X
  dead   : Calls⁺ A S⃗ X
  choose : (i : Ch Cᴵ⟦ S⃗ ⟧) → (Q Cᴵ⟦ S⃗ ⟧ i → Calls⁺ A S⃗ X) → Calls⁺ A S⃗ X

mapᶜ⁺ : (X → Y) → Calls⁺ A S⃗ X → Calls⁺ A S⃗ Y
mapᶜ⁺ f (ret x)      = ret (f x)
mapᶜ⁺ f (call c q k) = call c q λ r → mapᶜ⁺ f (k r)
mapᶜ⁺ f (coin μ k)   = coin μ λ b → mapᶜ⁺ f (k b)
mapᶜ⁺ f dead         = dead
mapᶜ⁺ f (choose i k) = choose i λ p → mapᶜ⁺ f (k p)

reindex⁺ : A ⇒ᴵ A′ → Calls⁺ A S⃗ X → Calls⁺ A′ S⃗ X
reindex⁺ m (ret x)      = ret x
reindex⁺ m (call c q k) = call (ch m c) (qu m q) λ r → reindex⁺ m (k (re m r))
reindex⁺ m (coin μ k)   = coin μ λ b → reindex⁺ m (k b)
reindex⁺ m dead         = dead
reindex⁺ m (choose i k) = choose i λ p → reindex⁺ m (k p)

-- Sites go out through `σ`, picks come back.
relocate : (σ : Ch Cᴵ⟦ S⃗ ⟧ → Ch Cᴵ⟦ T⃗ ⟧) → (∀ {i} → Q Cᴵ⟦ T⃗ ⟧ (σ i) → Q Cᴵ⟦ S⃗ ⟧ i)
         → Calls⁺ A S⃗ X → Calls⁺ A T⃗ X
relocate σ back (ret x)      = ret x
relocate σ back (call c q k) = call c q λ r → relocate σ back (k r)
relocate σ back (coin μ k)   = coin μ λ b → relocate σ back (k b)
relocate σ back dead         = dead
relocate σ back (choose i k) = choose (σ i) λ p → relocate σ back (k (back p))

plainᶜ : Calls A X → Calls⁺ A S⃗ X
plainᶜ (ret x)      = ret x
plainᶜ (call c q k) = call c q λ r → plainᶜ (k r)
plainᶜ (coin μ k)   = coin μ λ b → plainᶜ (k b)
plainᶜ dead         = dead

infix 4 _≈ᶜ⁺_

data _≈ᶜ⁺_ {A : Iface} {S⃗ : List Set} {X : Set} : Calls⁺ A S⃗ X → Calls⁺ A S⃗ X → Set where
  ret    : ∀ {x x′} → x ≡ x′ → ret x ≈ᶜ⁺ ret x′
  call   : ∀ {c q k k′} → (∀ r → k r ≈ᶜ⁺ k′ r) → call c q k ≈ᶜ⁺ call c q k′
  coin   : ∀ {μ k k′} → (∀ b → k b ≈ᶜ⁺ k′ b) → coin μ k ≈ᶜ⁺ coin μ k′
  dead   : dead ≈ᶜ⁺ dead
  choose : ∀ {i k k′} → (∀ p → k p ≈ᶜ⁺ k′ p) → choose i k ≈ᶜ⁺ choose i k′

≈ᶜ⁺-refl : {t : Calls⁺ A S⃗ X} → t ≈ᶜ⁺ t
≈ᶜ⁺-refl {t = ret _}      = ret refl
≈ᶜ⁺-refl {t = call _ _ _} = call λ _ → ≈ᶜ⁺-refl
≈ᶜ⁺-refl {t = coin _ _}   = coin λ _ → ≈ᶜ⁺-refl
≈ᶜ⁺-refl {t = dead}       = dead
≈ᶜ⁺-refl {t = choose _ _} = choose λ _ → ≈ᶜ⁺-refl

------------------------------------------------------------------------
-- Protocols with choices
------------------------------------------------------------------------

record Protocol⁺ (S⃗ : List Set) (A B : Iface) : Set₁ where
  field St   : Set
        init : St
        step : St → (c : Ch B) → Q B c → Calls⁺ A S⃗ (St × R B c)
open Protocol⁺ public

plain : Protocol A B → Protocol⁺ S⃗ A B
plain P = record { St = St P ; init = init P ; step = λ s c q → plainᶜ (step P s c q) }

module _ (P₂ : Protocol⁺ T⃗ B C) (P₁ : Protocol⁺ S⃗ A B) where
  mutual
    graft⁺ : Calls⁺ B T⃗ (St P₂ × Y) → St P₁ → Calls⁺ A (S⃗ ++ T⃗) ((St P₂ × St P₁) × Y)
    graft⁺ (ret (s₂ , y)) s₁ = ret ((s₂ , s₁) , y)
    graft⁺ (call b q k)   s₁ = serve⁺ k (step P₁ s₁ b q)
    graft⁺ (coin μ k)     s₁ = coin μ λ x → graft⁺ (k x) s₁
    graft⁺ dead           s₁ = dead
    graft⁺ (choose j k)   s₁ = choose (ch (join S⃗ T⃗) (inj₂ j)) λ p → graft⁺ (k (↓ʳ S⃗ T⃗ p)) s₁

    serve⁺ : {b : Ch B} → (R B b → Calls⁺ B T⃗ (St P₂ × Y)) → Calls⁺ A S⃗ (St P₁ × R B b)
           → Calls⁺ A (S⃗ ++ T⃗) ((St P₂ × St P₁) × Y)
    serve⁺ k (ret (s₁ , r)) = graft⁺ (k r) s₁
    serve⁺ k (call a q k₁)  = call a q λ r → serve⁺ k (k₁ r)
    serve⁺ k (coin μ k₁)    = coin μ λ x → serve⁺ k (k₁ x)
    serve⁺ k dead           = dead
    serve⁺ k (choose i k₁)  = choose (ch (join S⃗ T⃗) (inj₁ i)) λ p → serve⁺ k (k₁ (↓ˡ S⃗ T⃗ p))

  infixl 9 _∘⁺_
  _∘⁺_ : Protocol⁺ (S⃗ ++ T⃗) A C
  _∘⁺_ = record
    { St   = St P₂ × St P₁
    ; init = init P₂ , init P₁
    ; step = λ (s₂ , s₁) c q → graft⁺ (step P₂ s₂ c q) s₁ }

infixr 10 _⊗⁺_

_⊗⁺_ : Protocol⁺ S⃗ A B → Protocol⁺ T⃗ C D → Protocol⁺ (S⃗ ++ T⃗) (A ⊗ᴵ C) (B ⊗ᴵ D)
_⊗⁺_ {S⃗} {T⃗ = T⃗} P P′ = record
  { St   = St P × St P′
  ; init = init P , init P′
  ; step = λ where
      (s , t) (inj₁ b) q →
        mapᶜ⁺ (map₁ (_, t)) (reindex⁺ ι₁ (relocate (ch (join S⃗ T⃗) ∘ inj₁) (↓ˡ S⃗ T⃗) (step P s b q)))
      (s , t) (inj₂ d) q →
        mapᶜ⁺ (map₁ (s ,_)) (reindex⁺ ι₂ (relocate (ch (join S⃗ T⃗) ∘ inj₂) (↓ʳ S⃗ T⃗) (step P′ t d q))) }

infix 4 _≲⁺_ _≈⁺_

record _≲⁺_ (P P′ : Protocol⁺ S⃗ A B) : Set where
  field θ      : St P → St P′
        θ-init : θ (init P) ≡ init P′
        θ-step : ∀ s c q → mapᶜ⁺ (map₁ θ) (step P s c q) ≈ᶜ⁺ step P′ (θ s) c q
open _≲⁺_ public

_≈⁺_ : Rel (Protocol⁺ S⃗ A B) (suc 0ℓ)
_≈⁺_ = EqC.EqClosure _≲⁺_

------------------------------------------------------------------------
-- Pick-ahead compilation
------------------------------------------------------------------------

Queues : List Set → Set
Queues []      = ⊤
Queues (S ∷ S⃗) = List S × Queues S⃗

empty : (S⃗ : List Set) → Queues S⃗
empty []      = tt
empty (S ∷ S⃗) = [] , empty S⃗

push : (S⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) → Q Cᴵ⟦ S⃗ ⟧ i → Queues S⃗ → Queues S⃗
push (S ∷ S⃗) (inj₁ _) p (q , qs) = q ∷ʳ p , qs
push (S ∷ S⃗) (inj₂ i) p (q , qs) = q , push S⃗ i p qs

pop : (S⃗ : List Set) (i : Ch Cᴵ⟦ S⃗ ⟧) → Queues S⃗ → Maybe (Q Cᴵ⟦ S⃗ ⟧ i × Queues S⃗)
pop (S ∷ S⃗) (inj₁ _) ([] , qs)    = nothing
pop (S ∷ S⃗) (inj₁ _) (p ∷ q , qs) = just (p , q , qs)
pop (S ∷ S⃗) (inj₂ i) (q , qs)     = Maybe.map (map₂ (q ,_)) (pop S⃗ i qs)

-- The queues ride along in the state.
resolve : Queues S⃗ → Calls⁺ A S⃗ (X × Y) → Calls A ((X × Queues S⃗) × Y)
resolve         qs (ret (x , y)) = ret ((x , qs) , y)
resolve         qs (call c q k)  = call c q λ r → resolve qs (k r)
resolve         qs (coin μ k)    = coin μ λ b → resolve qs (k b)
resolve         qs dead          = dead
resolve {S⃗} qs (choose i k)  = maybe′ (λ pq → resolve (proj₂ pq) (k (proj₁ pq))) dead (pop S⃗ i qs)

⌈_⌉ : Protocol⁺ S⃗ A B → Protocol A (Cᴵ⟦ S⃗ ⟧ ⊗ᴵ B)
⌈_⌉ {S⃗} P = record
  { St   = St P × Queues S⃗
  ; init = init P , empty S⃗
  ; step = λ where
      (s , qs) (inj₁ i) p → ret ((s , push S⃗ i p qs) , tt⟦ S⃗ ⟧ i)
      (s , qs) (inj₂ c) q → resolve qs (step P s c q) }

resolve-sim : {θ : X → X′} (t : Calls⁺ A S⃗ (X × Y)) {t′ : Calls⁺ A S⃗ (X′ × Y)}
            → mapᶜ⁺ (map₁ θ) t ≈ᶜ⁺ t′ → (qs : Queues S⃗)
            → mapᶜ (map₁ (map₁ θ)) (resolve qs t) ≈ᶜ resolve qs t′
resolve-sim         (ret _)      (ret refl) qs = ret refl
resolve-sim         (call _ _ k) (call e)   qs = call λ r → resolve-sim (k r) (e r) qs
resolve-sim         (coin _ k)   (coin e)   qs = coin λ b → resolve-sim (k b) (e b) qs
resolve-sim         dead         dead       qs = dead
resolve-sim {S⃗ = S⃗} (choose i k) (choose e) qs with pop S⃗ i qs
... | nothing        = dead
... | just (p , qs′) = resolve-sim (k p) (e p) qs′

⌈⌉-sim : {P P′ : Protocol⁺ S⃗ A B} → P ≲⁺ P′ → ⌈ P ⌉ ≲ᵖ ⌈ P′ ⌉
⌈⌉-sim {S⃗} {P = P} σ = record
  { θ      = map₁ (θ σ)
  ; θ-init = cong (_, empty S⃗) (θ-init σ)
  ; θ-step = λ where
      (s , qs) (inj₁ i) p → ret refl
      (s , qs) (inj₂ c) q → resolve-sim (step P s c q) (θ-step σ s c q) qs }

⌈⌉-resp : {P P′ : Protocol⁺ S⃗ A B} → P ≈⁺ P′ → ⌈ P ⌉ ≈ᵖ ⌈ P′ ⌉
⌈⌉-resp = EqC.gmap ⌈_⌉ ⌈⌉-sim

-- A choice-free protocol compiles to itself behind the unitor `λ⇐ = ⌜ λᴵ ⌝`.
⌈⌉-plain : (P : Protocol A B) → ⌈ plain {S⃗ = []} P ⌉ ≈ᵖ ⌜ λᴵ ⌝ ∘ᵖ P
⌈⌉-plain {A = A} {B = B} P = ≲⇒≈ᵖ record
  { θ = λ (s , _) → tt , s ; θ-init = refl
  ; θ-step = λ where
      (_ , _) (inj₁ ()) _
      (s , _) (inj₂ c) q → go (step P s c q) }
  where
  go : {c : Ch B} (t : Calls A (St P × R B c))
     → mapᶜ (map₁ λ (s , _) → tt , s) (resolve tt (plainᶜ t)) ≈ᶜ serve ⌜ λᴵ ⌝ P {b = c} (λ r → ret (tt , r)) t
  go (ret _)      = ret refl
  go (call _ _ k) = call λ r → go (k r)
  go (coin _ k)   = coin λ b → go (k b)
  go dead         = dead
