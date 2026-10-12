{-# OPTIONS --safe --without-K --guardedness #-}

open import Data.Nat.Base using (ℕ)
module CategoricalCrypto.Symbolic.RunFollowing.Circuit (κ : ℕ) where

open import Categories.Category.Monoidal.Bundle
open import Categories.FreeMonoidal using (module FreeObjInterp; Mon)
open import Data.Bool.Base
open import Data.Empty.Polymorphic using () renaming (⊥-elim to ⊥ᵖ-elim)
open import Data.Product
open import Data.Sum.Base as Sum
open import Function.Base hiding (_∘_)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Machines.Pure
open import CategoricalCrypto.Machines.Sandwich
open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀
open import CategoricalCrypto.Symbolic.RunFollowing.PairEnc κ
import CategoricalCrypto.Symbolic.RunFollowing.Role as Roles
open import CategoricalCrypto.UC.Machine using (Proc)
open import CategoricalCrypto.UC.Machine.Dictionary
open import CategoricalCrypto.UC.Model.Seal
import CategoricalCrypto.Machines.Sim.RunFollowing.Process as Processes

open FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)

module R = Roles κ
module P = Processes World before _≤ʷ_ stay transʷ
private module G = MonoidalCategory 𝔾ᵒ
private module M = MonoidalCategory (𝒢ₚᴹ 0ℓ)

object : ObjTerm → P.Interface
object unit = P.unit
object (A ⊗₀ B) = object A P.⊗ᴸ object B
object (Var a) = R.alphabets pos (Var a) P.⇿ᴸ R.alphabets neg (Var a)

tree≡ᶜ : ∀ x → ⟦ x ⟧₀ ≡ ifaceᵒ (P.base (object x))
tree≡ᶜ unit = unitᵒ
tree≡ᶜ (A ⊗₀ B) = trans (cong₂ G._⊗₀_ (tree≡ᶜ A) (tree≡ᶜ B)) (⊗ᵒ (P.base (object A)) (P.base (object B)))
tree≡ᶜ (Var _) = refl

liftᶜ : ∀ {A B} → Proc (P.base (object A)) (P.base (object B)) → ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀
liftᶜ {A} {B} p = subst₂ G._⇒_ (sym (tree≡ᶜ A)) (sym (tree≡ᶜ B)) (procᵒ p)

private
  cast-∘ : ∀ {X Y Z} {A B C : Iface} (a : X ≡ ifaceᵒ A) (b : Y ≡ ifaceᵒ B) (c : Z ≡ ifaceᵒ C)
    (g : Proc B C) (f : Proc A B)
    → subst₂ G._⇒_ (sym a) (sym c) (procᵒ (M._∘_ {Pos A , Neg A} {Pos B , Neg B} {Pos C , Neg C} g f))
      G.≈ G._∘_ (subst₂ G._⇒_ (sym b) (sym c) (procᵒ g)) (subst₂ G._⇒_ (sym a) (sym b) (procᵒ f))
  cast-∘ refl refl refl g f = procᵒ-∘ g f

  cast-resp : ∀ {X Y} {A B : Iface} (a : X ≡ ifaceᵒ A) (b : Y ≡ ifaceᵒ B) {f g : Proc A B}
    → f S.≈ᴹ g → subst₂ G._⇒_ (sym a) (sym b) (procᵒ f) G.≈ subst₂ G._⇒_ (sym a) (sym b) (procᵒ g)
  cast-resp refl refl e = ≈ᴹ⇒≈ᵒ e

lift-compose : ∀ {A B C} (g : Proc (P.base (object B)) (P.base (object C))) (f : Proc (P.base (object A)) (P.base (object B)))
  → liftᶜ {A} {C} (P.compose {object B} {object C} {object A} g f) G.≈ G._∘_ (liftᶜ {B} {C} g) (liftᶜ {A} {B} f)
lift-compose {A} {B} {C} g f = G.Equiv.trans (cast-resp (tree≡ᶜ A) (tree≡ᶜ C) (P.compose-correct {object B} {object C} {object A} g f))
  (cast-∘ (tree≡ᶜ A) (tree≡ᶜ B) (tree≡ᶜ C) g f)

private
  join-object : ∀ {X Y} {A B : P.Interface} → X ≡ ifaceᵒ (P.base A) → Y ≡ ifaceᵒ (P.base B)
    → X G.⊗₀ Y ≡ ifaceᵒ (P.base (A P.⊗ᴸ B))
  join-object {A = A} {B = B} p q = trans (cong₂ G._⊗₀_ p q) (⊗ᵒ (P.base A) (P.base B))

opaque
  unfolding 𝔾ᵒ unitᵒ ⊗ᵒ ifaceᵒ procᵒ

  private
    cast-⊗ : ∀ {X Y Z W} {A B C D : Iface}
      (a : X ≡ ifaceᵒ A) (b : Y ≡ ifaceᵒ B) (c : Z ≡ ifaceᵒ C) (d : W ≡ ifaceᵒ D)
      (f : Proc A B) (g : Proc C D)
      → subst₂ G._⇒_ (sym (trans (cong₂ G._⊗₀_ a c) (⊗ᵒ A C))) (sym (trans (cong₂ G._⊗₀_ b d) (⊗ᵒ B D)))
          (procᵒ (M._⊗₁_ {Pos A , Neg A} {Pos B , Neg B} {Pos C , Neg C} {Pos D , Neg D} f g))
        G.≈ G._⊗₁_ (subst₂ G._⇒_ (sym a) (sym b) (procᵒ f)) (subst₂ G._⇒_ (sym c) (sym d) (procᵒ g))
    cast-⊗ refl refl refl refl f g = G.Equiv.refl

  private
    cast-id : ∀ {X} (A : P.Interface) (e : X ≡ ifaceᵒ (P.base A))
      → subst₂ G._⇒_ (sym e) (sym e) (procᵒ (P.wire {A} {A} (λ x → x) (λ x → x))) G.≈ G.id
    cast-id A refl = ≈ᴹ⇒≈ᵒ (S.≲⇒≈ᴹ (T.pureᴹ-cong λ i →
      K.pureᵏ-cong {h = Sum.swap ∘′ Sum.map (λ x → x) (λ x → x)} {k = Sum.swap}
        (λ { (inj₁ _) → refl ; (inj₂ _) → refl }) i ⟨≈⟩ ≈sym (swapᵏ i)))

    cast-λ⇒ : ∀ {X} (A : P.Interface) (e : X ≡ ifaceᵒ (P.base A))
      → subst₂ G._⇒_ (sym (trans (cong₂ G._⊗₀_ unitᵒ e) (⊗ᵒ (P.base P.unit) (P.base A)))) (sym e)
          (procᵒ (P.wire {P.unit P.⊗ᴸ A} {A} drop⇒ˡ inj₂)) G.≈ G.unitorˡ.from
    cast-λ⇒ A refl = ≈ᴹ⇒≈ᵒ (P.wire-correct {P.unit P.⊗ᴸ A} {A} drop⇒ˡ inj₂ S.○ᴹ λ⇒-λᴳ)

    cast-λ⇐ : ∀ {X} (A : P.Interface) (e : X ≡ ifaceᵒ (P.base A))
      → subst₂ G._⇒_ (sym e) (sym (trans (cong₂ G._⊗₀_ unitᵒ e) (⊗ᵒ (P.base P.unit) (P.base A))))
          (procᵒ (P.wire {A} {P.unit P.⊗ᴸ A} inj₂ drop⇒ˡ)) G.≈ G.unitorˡ.to
    cast-λ⇐ A refl = ≈ᴹ⇒≈ᵒ (P.wire-correct {A} {P.unit P.⊗ᴸ A} inj₂ drop⇒ˡ S.○ᴹ λ⇐-λᴳ)

    cast-ρ⇒ : ∀ {X} (A : P.Interface) (e : X ≡ ifaceᵒ (P.base A))
      → subst₂ G._⇒_ (sym (trans (cong₂ G._⊗₀_ e unitᵒ) (⊗ᵒ (P.base A) (P.base P.unit)))) (sym e)
          (procᵒ (P.wire {A P.⊗ᴸ P.unit} {A} drop⇒ʳ inj₁)) G.≈ G.unitorʳ.from
    cast-ρ⇒ A refl = ≈ᴹ⇒≈ᵒ (P.wire-correct {A P.⊗ᴸ P.unit} {A} drop⇒ʳ inj₁ S.○ᴹ ρ⇒-ρᴳ)

    cast-ρ⇐ : ∀ {X} (A : P.Interface) (e : X ≡ ifaceᵒ (P.base A))
      → subst₂ G._⇒_ (sym e) (sym (trans (cong₂ G._⊗₀_ e unitᵒ) (⊗ᵒ (P.base A) (P.base P.unit))))
          (procᵒ (P.wire {A} {A P.⊗ᴸ P.unit} inj₁ drop⇒ʳ)) G.≈ G.unitorʳ.to
    cast-ρ⇐ A refl = ≈ᴹ⇒≈ᵒ (P.wire-correct {A} {A P.⊗ᴸ P.unit} inj₁ drop⇒ʳ S.○ᴹ ρ⇐-ρᴳ)

    cast-α⇒ : ∀ {X Y Z} (A B C : P.Interface)
      (a : X ≡ ifaceᵒ (P.base A)) (b : Y ≡ ifaceᵒ (P.base B)) (c : Z ≡ ifaceᵒ (P.base C))
      → subst₂ G._⇒_ (sym (join-object {A = A P.⊗ᴸ B} {B = C} (join-object {A = A} {B = B} a b) c))
          (sym (join-object {A = A} {B = B P.⊗ᴸ C} a (join-object {A = B} {B = C} b c)))
          (procᵒ (P.wire {(A P.⊗ᴸ B) P.⊗ᴸ C} {A P.⊗ᴸ (B P.⊗ᴸ C)} Sum.assocʳ Sum.assocˡ)) G.≈ G.associator.from
    cast-α⇒ A B C refl refl refl = ≈ᴹ⇒≈ᵒ
      (P.wire-correct {(A P.⊗ᴸ B) P.⊗ᴸ C} {A P.⊗ᴸ (B P.⊗ᴸ C)} Sum.assocʳ Sum.assocˡ S.○ᴹ a⇒-α⇒)

    cast-α⇐ : ∀ {X Y Z} (A B C : P.Interface)
      (a : X ≡ ifaceᵒ (P.base A)) (b : Y ≡ ifaceᵒ (P.base B)) (c : Z ≡ ifaceᵒ (P.base C))
      → subst₂ G._⇒_ (sym (join-object {A = A} {B = B P.⊗ᴸ C} a (join-object {A = B} {B = C} b c)))
          (sym (join-object {A = A P.⊗ᴸ B} {B = C} (join-object {A = A} {B = B} a b) c))
          (procᵒ (P.wire {A P.⊗ᴸ (B P.⊗ᴸ C)} {(A P.⊗ᴸ B) P.⊗ᴸ C} Sum.assocˡ Sum.assocʳ)) G.≈ G.associator.to
    cast-α⇐ A B C refl refl refl = ≈ᴹ⇒≈ᵒ
      (P.wire-correct {A P.⊗ᴸ (B P.⊗ᴸ C)} {(A P.⊗ᴸ B) P.⊗ᴸ C} Sum.assocˡ Sum.assocʳ S.○ᴹ a⇐-α⇐)

  private
    tensor-path : ∀ {X Y} {A B A′ B′ : P.Interface}
      (p : X ≡ ifaceᵒ (P.base A)) (q : Y ≡ ifaceᵒ (P.base B)) (a : A ≡ A′) (b : B ≡ B′)
      → trans (trans (cong₂ G._⊗₀_ p q) (⊗ᵒ (P.base A) (P.base B)))
          (cong ifaceᵒ (cong P.base (cong₂ P._⊗ᴸ_ a b)))
        ≡ trans (cong₂ G._⊗₀_ (trans p (cong ifaceᵒ (cong P.base a))) (trans q (cong ifaceᵒ (cong P.base b))))
          (⊗ᵒ (P.base A′) (P.base B′))
    tensor-path refl refl refl refl = refl

lift-id : ∀ {A} → liftᶜ {A} {A} (P.wire {object A} {object A} (λ x → x) (λ x → x)) G.≈ G.id
lift-id {A} = cast-id (object A) (tree≡ᶜ A)

lift-λ⇒ : ∀ {A} → liftᶜ {unit ⊗₀ A} {A} (P.wire {object (unit ⊗₀ A)} {object A} drop⇒ˡ inj₂) G.≈ G.unitorˡ.from
lift-λ⇒ {A} = cast-λ⇒ (object A) (tree≡ᶜ A)

lift-λ⇐ : ∀ {A} → liftᶜ {A} {unit ⊗₀ A} (P.wire {object A} {object (unit ⊗₀ A)} inj₂ drop⇒ˡ) G.≈ G.unitorˡ.to
lift-λ⇐ {A} = cast-λ⇐ (object A) (tree≡ᶜ A)

lift-ρ⇒ : ∀ {A} → liftᶜ {A ⊗₀ unit} {A} (P.wire {object (A ⊗₀ unit)} {object A} drop⇒ʳ inj₁) G.≈ G.unitorʳ.from
lift-ρ⇒ {A} = cast-ρ⇒ (object A) (tree≡ᶜ A)

lift-ρ⇐ : ∀ {A} → liftᶜ {A} {A ⊗₀ unit} (P.wire {object A} {object (A ⊗₀ unit)} inj₁ drop⇒ʳ) G.≈ G.unitorʳ.to
lift-ρ⇐ {A} = cast-ρ⇐ (object A) (tree≡ᶜ A)

lift-α⇒ : ∀ {A B C} → liftᶜ {(A ⊗₀ B) ⊗₀ C} {A ⊗₀ (B ⊗₀ C)}
  (P.wire {object ((A ⊗₀ B) ⊗₀ C)} {object (A ⊗₀ (B ⊗₀ C))} Sum.assocʳ Sum.assocˡ) G.≈ G.associator.from
lift-α⇒ {A} {B} {C} = cast-α⇒ (object A) (object B) (object C) (tree≡ᶜ A) (tree≡ᶜ B) (tree≡ᶜ C)

lift-α⇐ : ∀ {A B C} → liftᶜ {A ⊗₀ (B ⊗₀ C)} {(A ⊗₀ B) ⊗₀ C}
  (P.wire {object (A ⊗₀ (B ⊗₀ C))} {object ((A ⊗₀ B) ⊗₀ C)} Sum.assocˡ Sum.assocʳ) G.≈ G.associator.to
lift-α⇐ {A} {B} {C} = cast-α⇐ (object A) (object B) (object C) (tree≡ᶜ A) (tree≡ᶜ B) (tree≡ᶜ C)

lift-tensor : ∀ {A B C D} (f : Proc (P.base (object A)) (P.base (object B))) (g : Proc (P.base (object C)) (P.base (object D)))
  → liftᶜ {A ⊗₀ C} {B ⊗₀ D} (P.tensor {object A} {object B} {object C} {object D} f g) G.≈ G._⊗₁_ (liftᶜ {A} {B} f) (liftᶜ {C} {D} g)
lift-tensor {A} {B} {C} {D} f g = G.Equiv.trans (cast-resp (tree≡ᶜ (A ⊗₀ C)) (tree≡ᶜ (B ⊗₀ D)) (P.tensor-correct {object A} {object B} {object C} {object D} f g))
  (cast-⊗ (tree≡ᶜ A) (tree≡ᶜ B) (tree≡ᶜ C) (tree≡ᶜ D) f g)

free-object : ∀ {x} → UnitFree x → object x ≡ (R.trees pos x P.⇿ᴸ R.trees neg x)
free-object {Var a} _ = refl
free-object {A ⊗₀ B} (ua , ub) = cong₂ P._⊗ᴸ_ (free-object ua) (free-object ub)
free-object {unit} ()

free-base : ∀ {x} → UnitFree x → P.base (object x) ≡ ⟦ x ⟧ᴵ
free-base u = cong P.base (free-object u)

free-path : ∀ {x} (u : UnitFree x) → trans (tree≡ᶜ x) (cong ifaceᵒ (free-base u)) ≡ tree≡ x u
free-path {Var a} _ = refl
free-path {A ⊗₀ B} (ua , ub) = trans (tensor-path (tree≡ᶜ A) (tree≡ᶜ B) (free-object ua) (free-object ub))
  (cong₂ (λ p q → trans (cong₂ G._⊗₀_ p q) (⊗ᵒ ⟦ A ⟧ᴵ ⟦ B ⟧ᴵ)) (free-path ua) (free-path ub))
free-path {unit} ()

private
  cast-leaf : ∀ {X Y} {A B A′ B′ : P.Interface}
    (p : X ≡ ifaceᵒ (P.base A)) (q : Y ≡ ifaceᵒ (P.base B)) (a : A ≡ A′) (b : B ≡ B′)
    (r : Σ[ f ∈ Proc (P.base A′) (P.base B′) ] P.Stable A′ B′ f)
    → subst₂ G._⇒_ (sym p) (sym q) (procᵒ (proj₁
        (subst₂ (λ A B → Σ[ f ∈ Proc (P.base A) (P.base B) ] P.Stable A B f) (sym a) (sym b) r)))
      ≡ subst₂ G._⇒_ (sym (trans p (cong ifaceᵒ (cong P.base a))))
          (sym (trans q (cong ifaceᵒ (cong P.base b)))) (procᵒ (proj₁ r))
  cast-leaf refl refl refl refl r = refl

record Context (A B : ObjTerm) (h : ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀) : Set₁ where
  field
    machine : Proc (P.base (object A)) (P.base (object B))
    stable : P.Stable (object A) (object B) machine
    correct : liftᶜ {A} {B} machine G.≈ h
open Context public

leaf-context : ∀ {x y} (ux : UnitFree x) (uy : UnitFree y) (p : Role x y) κ′ → κ′ ≢ κ → Context x y (leafᵒ (ux , uy , p) κ′)
leaf-context {x} {y} ux uy p κ′ fresh = record
  { machine = proj₁ paired ; stable = proj₂ paired
  ; correct = G.Equiv.trans (G.Equiv.reflexive equality)
      (treeᵒ-resp ux uy (≈ᴹ⇒≈ᵒ (sandwich-id (runᴿ κ′ p) (λ x → x) (λ x → x) (λ _ → refl) (λ _ → refl)))) }
  where
  paired : Σ[ f ∈ Proc (P.base (object x)) (P.base (object y)) ] P.Stable (object x) (object y) f
  paired = subst₂ (λ A B → Σ[ f ∈ Proc (P.base A) (P.base B) ] P.Stable A B f)
    (sym (free-object ux)) (sym (free-object uy)) (R.tree-role κ′ p , R.tree-role-stable κ′ fresh p)
  equality : liftᶜ {x} {y} (proj₁ paired) ≡ treeᵒ ux uy (procᵒ (R.tree-role κ′ p))
  equality = trans (cast-leaf {A = object x} {B = object y}
    (tree≡ᶜ x) (tree≡ᶜ y) (free-object ux) (free-object uy)
    (R.tree-role κ′ p , R.tree-role-stable κ′ fresh p))
    (cong₂ (λ a b → subst₂ G._⇒_ (sym a) (sym b) (procᵒ (R.tree-role κ′ p))) (free-path ux) (free-path uy))

private variable A B C D : ObjTerm

wire-context : ∀ {h : ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀}
  (up : F.Base (P.positive (object A)) → F.Base (P.positive (object B)))
  (down : F.Base (P.negative (object B)) → F.Base (P.negative (object A)))
  (ru : ∀ w → F.Related (P.positive (object A)) w → F.Related (P.positive (object B)) w)
  (rd : ∀ w → F.Related (P.negative (object B)) w → F.Related (P.negative (object A)) w)
  → (∀ b w x → F.project (P.positive (object B)) b w (ru w x) ≡ up (F.project (P.positive (object A)) b w x))
  → (∀ b w y → F.project (P.negative (object A)) b w (rd w y) ≡ down (F.project (P.negative (object B)) b w y))
  → liftᶜ {A} {B} (P.wire {object A} {object B} up down) G.≈ h → Context A B h
wire-context {A = A} {B} up down ru rd eu ed e = record
  { machine = P.wire {object A} {object B} up down
  ; stable = P.wire-stable {object A} {object B} up down ru rd eu ed ; correct = e }

id-context : Context A A G.id
id-context {A} = wire-context (λ x → x) (λ x → x) (λ _ x → x) (λ _ x → x)
  (λ _ _ _ → refl) (λ _ _ _ → refl) (lift-id {A})

compose-context : {g : ⟦ B ⟧₀ G.⇒ ⟦ C ⟧₀} {f : ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀}
  → Context B C g → Context A B f → Context A C (g G.∘ f)
compose-context {B} {C} {A} g f = record
  { machine = P.compose {object B} {object C} {object A} (machine g) (machine f)
  ; stable = P.compose-stable {B = object B} {C = object C} {A = object A} (stable g) (stable f)
  ; correct = G.Equiv.trans (lift-compose {A} {B} {C} (machine g) (machine f)) (G.∘-resp-≈ (correct g) (correct f)) }

tensor-context : {f : ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀} {g : ⟦ C ⟧₀ G.⇒ ⟦ D ⟧₀}
  → Context A B f → Context C D g → Context (A ⊗₀ C) (B ⊗₀ D) (f G.⊗₁ g)
tensor-context {A} {B} {C} {D} f g = record
  { machine = P.tensor {object A} {object B} {object C} {object D} (machine f) (machine g)
  ; stable = P.tensor-stable {A = object A} {B = object B} {C = object C} {D = object D} (stable f) (stable g)
  ; correct = G.Equiv.trans (lift-tensor {A} {B} {C} {D} (machine f) (machine g)) (G.⊗.F-resp-≈ (correct f , correct g)) }

private
  closed : Closed Context
  closed = record
    { P-id = id-context
    ; P-∘ = compose-context
    ; P-⊗ = tensor-context
    ; P-λ⇒ = λ {A} → wire-context drop⇒ˡ inj₂ (λ _ → Sum.[ ⊥ᵖ-elim , (λ x → x) ]′) (λ _ → inj₂)
        (λ where _ _ (inj₁ ()) ; _ _ (inj₂ _) → refl) (λ _ _ _ → refl) (lift-λ⇒ {A})
    ; P-λ⇐ = λ {A} → wire-context inj₂ drop⇒ˡ (λ _ → inj₂) (λ _ → Sum.[ ⊥ᵖ-elim , (λ x → x) ]′)
        (λ _ _ _ → refl) (λ where _ _ (inj₁ ()) ; _ _ (inj₂ _) → refl) (lift-λ⇐ {A})
    ; P-ρ⇒ = λ {A} → wire-context drop⇒ʳ inj₁ (λ _ → Sum.[ (λ x → x) , ⊥ᵖ-elim ]′) (λ _ → inj₁)
        (λ where _ _ (inj₁ _) → refl ; _ _ (inj₂ ())) (λ _ _ _ → refl) (lift-ρ⇒ {A})
    ; P-ρ⇐ = λ {A} → wire-context inj₁ drop⇒ʳ (λ _ → inj₁) (λ _ → Sum.[ (λ x → x) , ⊥ᵖ-elim ]′)
        (λ _ _ _ → refl) (λ where _ _ (inj₁ _) → refl ; _ _ (inj₂ ())) (lift-ρ⇐ {A})
    ; P-α⇒ = λ {A} {B} {C} → wire-context Sum.assocʳ Sum.assocˡ (λ _ → Sum.assocʳ) (λ _ → Sum.assocˡ)
        (λ where _ _ (inj₁ (inj₁ _)) → refl ; _ _ (inj₁ (inj₂ _)) → refl ; _ _ (inj₂ _) → refl)
        (λ where _ _ (inj₁ _) → refl ; _ _ (inj₂ (inj₁ _)) → refl ; _ _ (inj₂ (inj₂ _)) → refl) (lift-α⇒ {A} {B} {C})
    ; P-α⇐ = λ {A} {B} {C} → wire-context Sum.assocˡ Sum.assocʳ (λ _ → Sum.assocˡ) (λ _ → Sum.assocʳ)
        (λ where _ _ (inj₁ _) → refl ; _ _ (inj₂ (inj₁ _)) → refl ; _ _ (inj₂ (inj₂ _)) → refl)
        (λ where _ _ (inj₁ (inj₁ _)) → refl ; _ _ (inj₁ (inj₂ _)) → refl ; _ _ (inj₂ _) → refl) (lift-α⇐ {A} {B} {C})
    ; P-σ = λ { ⦃ () ⦄ } }

context : (c : HomTerm A B) (ι : Occ c → ℕ) → (∀ o → ι o ≢ κ) → Context A B ⟦ c ⟧[ ι ]
context = ⟦⟧[]-ind Context closed (λ κ′ → κ′ ≢ κ) λ (ux , uy , p) κ′ → leaf-context ux uy p κ′

record Circuit (A B : ObjTerm) (h : Bool → ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀) : Set₁ where
  field
    machine : Bool → Proc (P.base (object A)) (P.base (object B))
    following : P.Following (object A) (object B) machine
    correct : ∀ b → liftᶜ {A} {B} (machine b) G.≈ h b

compose-left : {g : Bool → ⟦ B ⟧₀ G.⇒ ⟦ C ⟧₀} {f : ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀}
  → Circuit B C g → Context A B f → Circuit A C (λ b → g b G.∘ f)
compose-left {B} {C} {A} g f = record
  { machine = λ b → P.compose {object B} {object C} {object A} (Circuit.machine g b) (machine f)
  ; following = P.compose-following-left {B = object B} {C = object C} {A = object A} (Circuit.following g) (stable f)
  ; correct = λ b → G.Equiv.trans (lift-compose {A} {B} {C} (Circuit.machine g b) (machine f)) (G.∘-resp-≈ (Circuit.correct g b) (correct f)) }

compose-right : {g : ⟦ B ⟧₀ G.⇒ ⟦ C ⟧₀} {f : Bool → ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀}
  → Context B C g → Circuit A B f → Circuit A C (λ b → g G.∘ f b)
compose-right {B} {C} {A} g f = record
  { machine = λ b → P.compose {object B} {object C} {object A} (machine g) (Circuit.machine f b)
  ; following = P.compose-following-right {B = object B} {C = object C} {A = object A} (stable g) (Circuit.following f)
  ; correct = λ b → G.Equiv.trans (lift-compose {A} {B} {C} (machine g) (Circuit.machine f b)) (G.∘-resp-≈ (correct g) (Circuit.correct f b)) }

tensor-right : {f : ⟦ A ⟧₀ G.⇒ ⟦ B ⟧₀} {g : Bool → ⟦ C ⟧₀ G.⇒ ⟦ D ⟧₀}
  → Context A B f → Circuit C D g → Circuit (A ⊗₀ C) (B ⊗₀ D) (λ b → f G.⊗₁ g b)
tensor-right {A} {B} {C} {D} f g = record
  { machine = λ b → P.tensor {object A} {object B} {object C} {object D} (machine f) (Circuit.machine g b)
  ; following = P.tensor-following-right {A = object A} {B = object B} {C = object C} {D = object D} (stable f) (Circuit.following g)
  ; correct = λ b → G.Equiv.trans (lift-tensor {A} {B} {C} {D} (machine f) (Circuit.machine g b)) (G.⊗.F-resp-≈ (correct f , Circuit.correct g b)) }
