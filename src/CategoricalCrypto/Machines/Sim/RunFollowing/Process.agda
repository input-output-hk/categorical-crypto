{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Machines.Sim.RunFollowing.Process
  (World : Set) (initial : World) (_≤ʷ_ : World → World → Set)
  (reflʷ : ∀ {w} → w ≤ʷ w)
  (transʷ : ∀ {w w′ w″} → w ≤ʷ w′ → w′ ≤ʷ w″ → w ≤ʷ w″) where

open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Data.Product
open import Data.Sum.Base as Sum
open import Function.Base
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Behaviour.Congruence using (⊗₁ᴳ-raw)
open import CategoricalCrypto.UC.Machine.Dictionary
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.Machines.Sim.RunFollowing as RunFollowing

module F = RunFollowing World initial _≤ʷ_ reflʷ transʷ
open F using (Letters; Base; Related; project; _⊎ᴸ_)
private module G = MonoidalCategory (𝒢ₚᴹ 0ℓ)

record Interface : Set₁ where
  constructor _⇿ᴸ_
  field positive negative : Letters
open Interface public

base : Interface → Iface
base A = Base (positive A) ⇿ Base (negative A)

empty : Letters
empty = record { Base = ⊥ ; Related = λ _ → ⊥ ; project = λ _ _ x → x }

unit : Interface
unit = empty ⇿ᴸ empty

infixr 10 _⊗ᴸ_
_⊗ᴸ_ : Interface → Interface → Interface
A ⊗ᴸ B = (positive A ⊎ᴸ positive B) ⇿ᴸ (negative A ⊎ᴸ negative B)

inputs outputs : Interface → Interface → Letters
inputs A B = positive A ⊎ᴸ negative B
outputs A B = negative A ⊎ᴸ positive B

Stable : (A B : Interface) → Proc (base A) (base B) → Set₁
Stable A B p = F.Stable (inputs A B) (outputs A B) (λ _ → p)

Following : (A B : Interface) → (Bool → Proc (base A) (base B)) → Set₁
Following A B = F.Following (inputs A B) (outputs A B)

private variable A B C D : Interface

compose : Proc (base B) (base C) → Proc (base A) (base B) → Proc (base A) (base C)
compose {B} {C} {A} g f = Col.MT.traceᴹ _ _ _
  (sandwichᴹ (g T.⊗ᵉ f) Col.γᶠ Col.αᶠ)

tensor : Proc (base A) (base B) → Proc (base C) (base D) → Proc (base (A ⊗ᴸ C)) (base (B ⊗ᴸ D))
tensor f g = sandwichᴹ (f T.⊗ᵉ g) midfn midfn

private
  absorbed : {X Y X′ Y′ : Set} (p : MC.Machine X Y) (i : X′ → X) (o : Y → Y′)
    → (pureᶠ o MC.∘ᴹ (p MC.∘ᴹ pureᶠ i)) S.≈ᴹ sandwichᴹ p i o
  absorbed p i o = Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ (S.≲⇒≈ᴹ (T.pure-∘ʳ (K.pureᵏ i) p))
    S.○ᴹ S.≲⇒≈ᴹ (T.pure-∘ˡ (K.pureᵏ o) _)
    S.○ᴹ squeeze p i o V.Equiv.refl V.Equiv.refl

compose-correct : (g : Proc (base B) (base C)) (f : Proc (base A) (base B))
  → compose {B = B} {C = C} {A = A} g f S.≈ᴹ G._∘_ {Pos (base A) , Neg (base A)} {Pos (base B) , Neg (base B)} {Pos (base C) , Neg (base C)} g f
compose-correct {B} {C} {A} g f = S.⟺ᴹ (Col.TC.trace-resp-≈ᴹ
    {Pos (base A) ⊎ Neg (base C)} {Neg (base A) ⊎ Pos (base C)} {Neg (base B) ⊎ Pos (base B)}
    (absorbed (g T.⊗ᵉ f) Col.γᶠ Col.αᶠ))
  S.○ᴹ S.⟺ᴹ (Col.TC.trace-resp-≈ᴹ
    {Pos (base A) ⊎ Neg (base C)} {Neg (base A) ⊎ Pos (base C)} {Neg (base B) ⊎ Pos (base B)}
    (Cat.∘ᴹ-resp-≈ᴹ (Col.α-pure _ _ _ _) (Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ (Col.γ-pure _ _ _ _))))
  S.○ᴹ Col.compose-raw≈∘ᴳ g f

tensor-correct : (f : Proc (base A) (base B)) (g : Proc (base C) (base D))
  → tensor {A = A} {B = B} {C = C} {D = D} f g S.≈ᴹ G._⊗₁_ {Pos (base A) , Neg (base A)} {Pos (base B) , Neg (base B)}
      {Pos (base C) , Neg (base C)} {Pos (base D) , Neg (base D)} f g
tensor-correct f g = S.⟺ᴹ (absorbed (f T.⊗ᵉ g) midfn midfn)
  S.○ᴹ S.⟺ᴹ (Cat.∘ᴹ-resp-≈ᴹ midᴹ-pure (Cat.∘ᴹ-resp-≈ᴹ S.reflᴹ midᴹ-pure))
  S.○ᴹ ⊗₁ᴳ-raw f g

private
  γ-law : {A B C : Interface} → ∀ b w (x : Related (inputs A C ⊎ᴸ (negative B ⊎ᴸ positive B)) w)
    → project (inputs B C ⊎ᴸ inputs A B) b w (Col.γᶠ x)
      ≡ Col.γᶠ (project (inputs A C ⊎ᴸ (negative B ⊎ᴸ positive B)) b w x)
  γ-law b w (inj₁ (inj₁ _)) = refl
  γ-law b w (inj₁ (inj₂ _)) = refl
  γ-law b w (inj₂ (inj₁ _)) = refl
  γ-law b w (inj₂ (inj₂ _)) = refl

  α-law : {A B C : Interface} → ∀ b w (x : Related (outputs B C ⊎ᴸ outputs A B) w)
    → project (outputs A C ⊎ᴸ (negative B ⊎ᴸ positive B)) b w (Col.αᶠ x)
      ≡ Col.αᶠ (project (outputs B C ⊎ᴸ outputs A B) b w x)
  α-law b w (inj₁ (inj₁ _)) = refl
  α-law b w (inj₁ (inj₂ _)) = refl
  α-law b w (inj₂ (inj₁ _)) = refl
  α-law b w (inj₂ (inj₂ _)) = refl

  mid-in-law : {A B C D : Interface} → ∀ b w (x : Related (inputs (A ⊗ᴸ C) (B ⊗ᴸ D)) w)
    → project (inputs A B ⊎ᴸ inputs C D) b w (midfn x)
      ≡ midfn (project (inputs (A ⊗ᴸ C) (B ⊗ᴸ D)) b w x)
  mid-in-law b w (inj₁ (inj₁ _)) = refl
  mid-in-law b w (inj₁ (inj₂ _)) = refl
  mid-in-law b w (inj₂ (inj₁ _)) = refl
  mid-in-law b w (inj₂ (inj₂ _)) = refl

  mid-out-law : {A B C D : Interface} → ∀ b w (x : Related (outputs A B ⊎ᴸ outputs C D) w)
    → project (outputs (A ⊗ᴸ C) (B ⊗ᴸ D)) b w (midfn x)
      ≡ midfn (project (outputs A B ⊎ᴸ outputs C D) b w x)
  mid-out-law b w (inj₁ (inj₁ _)) = refl
  mid-out-law b w (inj₁ (inj₂ _)) = refl
  mid-out-law b w (inj₂ (inj₁ _)) = refl
  mid-out-law b w (inj₂ (inj₂ _)) = refl

compose-stable : {g : Proc (base B) (base C)} {f : Proc (base A) (base B)}
  → Stable B C g → Stable A B f → Stable A C (compose {B = B} {C = C} {A = A} g f)
compose-stable {B = B} {C = C} {A = A} g f = F.trace-stable
  (F.sandwich-stable (λ _ → Col.γᶠ) (λ _ → Col.αᶠ) (λ _ → Col.γᶠ) (λ _ → Col.αᶠ)
    (γ-law {A = A} {B = B} {C = C}) (α-law {A = A} {B = B} {C = C}) (F.stable-events g f))

tensor-stable : {f : Proc (base A) (base B)} {g : Proc (base C) (base D)}
  → Stable A B f → Stable C D g → Stable (A ⊗ᴸ C) (B ⊗ᴸ D) (tensor {A = A} {B = B} {C = C} {D = D} f g)
tensor-stable {A = A} {B = B} {C = C} {D = D} f g = F.sandwich-stable (λ _ → midfn) (λ _ → midfn) (λ _ → midfn) (λ _ → midfn)
  (mid-in-law {A = A} {B = B} {C = C} {D = D}) (mid-out-law {A = A} {B = B} {C = C} {D = D}) (F.stable-events f g)

compose-following-left : {g : Bool → Proc (base B) (base C)} {f : Proc (base A) (base B)}
  → Following B C g → Stable A B f → Following A C (λ b → compose {B = B} {C = C} {A = A} (g b) f)
compose-following-left {B = B} {C = C} {A = A} g f = F.trace-following
  (F.sandwich-following (λ _ → Col.γᶠ) (λ _ → Col.αᶠ) (λ _ → Col.γᶠ) (λ _ → Col.αᶠ)
    (γ-law {A = A} {B = B} {C = C}) (α-law {A = A} {B = B} {C = C}) (F.events-following-left g f))

compose-following-right : {g : Proc (base B) (base C)} {f : Bool → Proc (base A) (base B)}
  → Stable B C g → Following A B f → Following A C (λ b → compose {B = B} {C = C} {A = A} g (f b))
compose-following-right {B = B} {C = C} {A = A} g f = F.trace-following
  (F.sandwich-following (λ _ → Col.γᶠ) (λ _ → Col.αᶠ) (λ _ → Col.γᶠ) (λ _ → Col.αᶠ)
    (γ-law {A = A} {B = B} {C = C}) (α-law {A = A} {B = B} {C = C}) (F.events-following-right g f))

tensor-following-left : {f : Bool → Proc (base A) (base B)} {g : Proc (base C) (base D)}
  → Following A B f → Stable C D g → Following (A ⊗ᴸ C) (B ⊗ᴸ D) (λ b → tensor {A = A} {B = B} {C = C} {D = D} (f b) g)
tensor-following-left {A = A} {B = B} {C = C} {D = D} f g = F.sandwich-following (λ _ → midfn) (λ _ → midfn) (λ _ → midfn) (λ _ → midfn)
  (mid-in-law {A = A} {B = B} {C = C} {D = D}) (mid-out-law {A = A} {B = B} {C = C} {D = D}) (F.events-following-left f g)

tensor-following-right : {f : Proc (base A) (base B)} {g : Bool → Proc (base C) (base D)}
  → Stable A B f → Following C D g → Following (A ⊗ᴸ C) (B ⊗ᴸ D) (λ b → tensor {A = A} {B = B} {C = C} {D = D} f (g b))
tensor-following-right {A = A} {B = B} {C = C} {D = D} f g = F.sandwich-following (λ _ → midfn) (λ _ → midfn) (λ _ → midfn) (λ _ → midfn)
  (mid-in-law {A = A} {B = B} {C = C} {D = D}) (mid-out-law {A = A} {B = B} {C = C} {D = D}) (F.events-following-right f g)

wire : (Base (positive A) → Base (positive B)) → (Base (negative B) → Base (negative A)) → Proc (base A) (base B)
wire up down = pureᶠ (Sum.swap ∘ Sum.map up down)

wire-correct : (up : Base (positive A) → Base (positive B)) (down : Base (negative B) → Base (negative A))
  → wire {A = A} {B = B} up down S.≈ᴹ CategoricalCrypto.UC.Machine.wireᴹ {base A} {base B} up down
wire-correct up down = S.≲⇒≈ᴹ (S.mk-cong λ where
  (s , inj₁ x) → pureᴵ (Sum.swap ∘ Sum.map up down) (s , inj₁ x)
  (s , inj₂ y) → pureᴵ (Sum.swap ∘ Sum.map up down) (s , inj₂ y))

wire-stable : (up : Base (positive A) → Base (positive B)) (down : Base (negative B) → Base (negative A))
  (ru : ∀ w → Related (positive A) w → Related (positive B) w)
  (rd : ∀ w → Related (negative B) w → Related (negative A) w)
  → (∀ b w x → project (positive B) b w (ru w x) ≡ up (project (positive A) b w x))
  → (∀ b w y → project (negative A) b w (rd w y) ≡ down (project (negative B) b w y))
  → Stable A B (wire {A = A} {B = B} up down)
wire-stable up down ru rd eu ed = F.pure-stable (λ _ → Sum.swap ∘ Sum.map up down)
  (λ w → Sum.swap ∘ Sum.map (ru w) (rd w)) λ where
    b w (inj₁ x) → cong inj₂ (eu b w x)
    b w (inj₂ y) → cong inj₁ (ed b w y)
