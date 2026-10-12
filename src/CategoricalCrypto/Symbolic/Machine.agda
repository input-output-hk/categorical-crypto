{-# OPTIONS --safe #-}

-- The fine symbolic setup has a relational machine interpretation. Allocations
-- are arbitrary names, so this interpretation deliberately forgets freshness;
-- it does not preserve the observational kernel of `Symbolic.Setup`.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Machine (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor.Monoidal
open import Categories.Functor.Presheaf.Morphism
open import Categories.NaturalTransformation hiding (id)
open import Data.Bool.Base
open import Data.Fin.Base hiding (lower)
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Product
open import Data.Sum.Base
open import Function.Base using (_∘′_)
open import Level hiding (suc)
import Relation.Binary.Bundles as RB

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import CategoricalCrypto.Channel.Core hiding (_⊗₀_) renaming (app to apply)
open import CategoricalCrypto.Machine.Core hiding (id; _∘_; _⊗₁_)
open import CategoricalCrypto.Standard2.Morphism
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.UCSetup.Morphism

import CategoricalCrypto.Machine.Core as CC
import CategoricalCrypto.Machine.Iso as MI
import CategoricalCrypto.Machine.UC as Iso

private
  variable
    x y : ObjTerm
    n : ℕ
    Γ : Fin n → List (Signature.Sort 𝔖)
    O : List Kind
    Δ : List (Signature.Sort 𝔖)

open Terms 𝔖
open EqTheory E
open Run E
open Channel

atomᶜ : Atom → Channel
atomᶜ a = alphabet pos a ⇿ alphabet neg a

⟦v⟧ᴿ : ⟦ Mon ⟧ᵥ
⟦v⟧ᴿ = fromMC Iso.machines noSymmetric

open FreeObjInterp Mon Atom ⟦v⟧ᴿ atomᶜ

-- Stating the tensor clause generically avoids unfolding the machine bundle.
module _ {o ℓ e} (v : ⟦ Mon ⟧ᵥ {o} {ℓ} {e}) (a : Atom → ⟦_⟧ᵥ.Cat.Obj v) where
  private module Obj = FreeObjInterp Mon Atom v a
  tensor-step : (x y : ObjTerm) → Obj.⟦ x ⊗₀ y ⟧₀ ≡ ⟦_⟧ᵥ.Cat._⊗₀_ v Obj.⟦ x ⟧₀ Obj.⟦ y ⟧₀
  tensor-step _ _ = refl

mirror : (x y : ObjTerm) → ⟦ x ⊗₀ y ⟧₀ ≡ (⟦ y ⟧₀ CategoricalCrypto.Channel.Core.⊗₀ ⟦ x ⟧₀)
mirror = tensor-step ⟦v⟧ᴿ atomᶜ

mode : Dir → Mode
mode pos = In
mode neg = Out

readᶜ : (d : Dir) (x : ObjTerm) → modeType (mode d) ⟦ x ⟧₀ → Alphabet d x
readᶜ pos unit ()
readᶜ neg unit ()
readᶜ d (x ⊗₀ y) m = [ inj₂ ∘′ readᶜ d y , inj₁ ∘′ readᶜ d x ]′
  (destruct-⊗ {m = mode d} (subst (modeType (mode d)) (mirror x y) m))
readᶜ pos (Var _) m = m
readᶜ neg (Var _) m = m

writeᶜ : (d : Dir) (x : ObjTerm) → Alphabet d x → modeType (mode d) ⟦ x ⟧₀
writeᶜ d unit ()
writeᶜ d (x ⊗₀ y) m = subst (modeType (mode d)) (sym (mirror x y))
  (construct-⊗ {m = mode d} ([ inj₂ ∘′ writeᶜ d x , inj₁ ∘′ writeᶜ d y ]′ m))
writeᶜ pos (Var _) m = m
writeᶜ neg (Var _) m = m

decodeᴿ : (x y : ObjTerm) → inType (⟦ x ⟧₀ ⊗ᵀ ⟦ y ⟧₀) → Input x y
decodeᴿ x y m = decode x y ([ inj₁ ∘′ readᶜ pos x , inj₂ ∘′ readᶜ neg y ]′ (destruct-⊗ {m = In} m))

encodeᴿ : (x y : ObjTerm) → Emission (Outs x y) → outType (⟦ x ⟧₀ ⊗ᵀ ⟦ y ⟧₀)
encodeᴿ x y e = construct-⊗ {m = Out}
  ([ inj₁ ∘′ writeᶜ neg x , inj₂ ∘′ writeᶜ pos y ]′ (encode x y e))

execᴿ : (ℕ → Name) → React n Γ O Δ → Frame Δ → ℕ → Config n Γ × Emission O
execᴿ draw (test ζ ζ′ t e) φ j = if does (ζ ⟨ φ ⟩ ≟E ζ′ ⟨ φ ⟩) then execᴿ draw t φ j else execᴿ draw e φ j
execᴿ draw (new _ t) φ j = execᴿ draw t (name (draw j) ∷ φ) (suc j)
execᴿ draw (emit c ρs o π) φ j = config c (canon* (ρs ⟨ φ ⟩*)) j , o ↦ canonᵛ (payload _ π φ)

stepᴿ : (ℕ → Name) → (p : Role x y) → Config (Role.n p) (Role.Γ p) → Input x y
      → Config (Role.n p) (Role.Γ p) × Emission (Outs x y)
stepᴿ draw p (config c φ j) (i ↦ v) = execᴿ draw (Role.react p c i (branch v)) (++⁺ (carry v) φ) j

roleMachine : UnitFree x × UnitFree y × Role x y → Machine ⟦ x ⟧₀ ⟦ y ⟧₀
roleMachine {x} {y} (_ , _ , p) = MkMachine {State = Config (Role.n p) (Role.Γ p)} λ s i o s′ →
  Σ[ draw ∈ (ℕ → Name) ] let s″ , e = stepᴿ draw p s (decodeᴿ x y i) in s′ ≡ s″ × o ≡ just (encodeᴿ x y e)

relational : FreeFunctorData symData
relational = record { ⟦v⟧ = ⟦v⟧ᴿ ; ⟦_⟧ᵖ₀ = atomᶜ ; ⟦_⟧ᵖ₁ = roleMachine }

Fᴿ : StrongMonoidalFunctor 𝔻𝕐 Iso.machines
Fᴿ = freeStrongMonoidal relational

-- Check the test adapter at a neutral bundle, without expanding machine trace
-- constructors during conversion of the free interpretation.
module TestOutput {o ℓ e} (ffd : FreeFunctorData symData {o} {ℓ} {e})
  (let module I = FreeFunctorData ffd) (R : I.C.Obj) (out : I.⟦ Var verdict ⟧₀ I.C.⇒ R) where
  private
    module D = I.C
    module Fn = FreeFunctor ffd
  output : {A Y : ObjTerm} → HomTerm (Y ⊗₀ A) (Var verdict) → I.⟦ Y ⊗₀ A ⟧₀ D.⇒ R
  output T = out D.∘ Fn.⟦ T ⟧₁

  output-cong : {A Y : ObjTerm} {T T′ : HomTerm (Y ⊗₀ A) (Var verdict)}
              → T ≈Term T′ → output T D.≈ output T′
  output-cong e = D.∘-resp-≈ʳ (Fn.⟦⟧-resp-≈ e)

  input-pull : {A B Y : ObjTerm} → HomTerm B A → I.⟦ Y ⊗₀ B ⟧₀ D.⇒ I.⟦ Y ⊗₀ A ⟧₀
  input-pull {Y = Y} f = D.id {I.⟦ Y ⟧₀} D.⊗₁ Fn.⟦ f ⟧₁

  output-pull : {A B Y : ObjTerm} → HomTerm B A → HomTerm (Y ⊗₀ A) (Var verdict)
              → I.⟦ Y ⊗₀ B ⟧₀ D.⇒ R
  output-pull {A} {B} {Y} f T = output {A} {Y} T D.∘ input-pull {A} {B} {Y} f

  output-natural : {A B Y : ObjTerm} (f : HomTerm B A) (T : HomTerm (Y ⊗₀ A) (Var verdict))
    → output (T ∘ (id ⊗₁ f)) D.≈ output-pull {A} {B} {Y} f T
  output-natural f T = D.sym-assoc

private
  module F = StrongMonoidalFunctor Fᴿ
  module Interp = FreeFunctor relational

untick : Machine (atomᶜ verdict) ℰ-Out
untick = FunctionMachine λ m → [ (λ b → just (construct-⊗ {m = Out} (inj₂ b))) , (λ ()) ]′ (destruct-⊗ {m = In} m)

private
  module Output = TestOutput relational ℰ-Out untick

reindex-cong : {X X′ R : Channel} (p : X ≡ X′) {f g : Machine X R}
  → f MI.≅ᴹ g
  → subst (λ Z → Machine Z R) p f MI.≅ᴹ subst (λ Z → Machine Z R) p g
reindex-cong refl e = e

reindex-compose : {X X′ Y Y′ R : Channel} (p : X ≡ X′) (q : Y ≡ Y′)
  (m : Machine Y R) (f : Machine X Y)
  → subst (λ Z → Machine Z R) p (m CC.∘ f)
    ≡ (subst (λ Z → Machine Z R) q m CC.∘ subst₂ Machine p q f)
reindex-compose refl refl m f = refl

input-pull-eq : {A B Y : ObjTerm} (f : HomTerm B A)
  → subst₂ Machine (mirror Y B) (mirror Y A) (Output.input-pull {A} {B} {Y} f)
    ≡ (Interp.⟦ f ⟧₁ CC.⊗₁ CC.id {⟦ Y ⟧₀})
input-pull-eq f = refl

toᴿ : {A : ObjTerm} → Test A → Iso.Test ⟦ A ⟧₀
toᴿ {A} (Y , T) = ⟦ Y ⟧₀ , subst (λ X → Machine X ℰ-Out) (mirror Y A) (Output.output {A} {Y} T)

toᴿ-cong : {A : ObjTerm} {t t′ : Test A} → SameTerm t t′ → Iso.SameTest (toᴿ t) (toᴿ t′)
toᴿ-cong {A} {Y , T} {.Y , T′} (same e) = Iso.same
  (reindex-cong (mirror Y A) {f = Output.output {A} {Y} T} {g = Output.output {A} {Y} T′}
    (Output.output-cong {A} {Y} {T} {T′} e))

toᴿ-natural : {A B : ObjTerm} (f : HomTerm B A) (t : Test A)
            → Iso.SameTest (toᴿ (pullᵗ f t)) (Iso.test-map (Interp.⟦ f ⟧₁) (toᴿ t))
toᴿ-natural {A} {B} f (Y , T) = Iso.same {A = ⟦ B ⟧₀} {Y = ⟦ Y ⟧₀}
  (subst (λ m → proj₂ (toᴿ (pullᵗ f (Y , T))) MI.≅ᴹ m)
    (trans (reindex-compose (mirror Y B) (mirror Y A)
      (Output.output {A} {Y} T) (Output.input-pull {A} {B} {Y} f))
      (cong (λ m → proj₂ (toᴿ (Y , T)) CC.∘ m) (input-pull-eq {A} {B} {Y} f)))
    (reindex-cong (mirror Y B)
      {f = Output.output {B} {Y} (T ∘ (id ⊗₁ f))} {g = Output.output-pull {A} {B} {Y} f T}
      (Output.output-natural {A} {B} {Y} f T)))

νᴿ : PresheafMorphism F.F ℰ≅ Iso.ℰ-tests
νᴿ .PresheafMorphism.ν .NaturalTransformation.η A =
  record { to = λ t → toᴿ (lower t) ; cong = λ e → toᴿ-cong (lower e) }
νᴿ .PresheafMorphism.ν .NaturalTransformation.commute f {t} = toᴿ-natural f (lower t)
νᴿ .PresheafMorphism.ν .NaturalTransformation.sym-commute {Y = B} f {t} =
  RB.Setoid.sym (Iso.Test-setoid ⟦ B ⟧₀) (toᴿ-natural f (lower t))

sym≅→iso : UCSetupMorphism Sym≅.StdSetup Iso.StdSetup
sym≅→iso = StdUCMorphism 𝔻𝕐 Iso.machines ℰ≅ Iso.ℰ-tests Fᴿ νᴿ
