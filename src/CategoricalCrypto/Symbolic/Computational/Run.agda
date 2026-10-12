{-# OPTIONS --safe --without-K --guardedness #-}

-- Computational execution of every role, without a resource or security claim.
-- Primitive algorithms consume explicit randomness arguments; `new` samples
-- independently at each execution. No symbolic normalizer runs on bitstrings.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Computational.Run (𝔖 : Signature) where

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Categories.Functor.Monoidal
open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base
open import Data.Product
open import Data.Sum.Base hiding (map₂)
open import Data.Unit
open import Function.Base using (_∘′_)
open import Level using (0ℓ)
open import Relation.Binary.Definitions hiding (Sym)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

open import ProbabilisticLogic.Dp

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Model.Seal

import CategoricalCrypto.Machines.Core as Core

open Signature 𝔖
open Terms 𝔖

record Scheme : Set₁ where
  field
    Bits  : Set
    impl  : (f : Sym) → ℕ → All (λ _ → Bits) (dom f) → Bits
    nonce : ℕ → Dₚ Bits
    _≟ᵇ_  : DecidableEquality Bits
    tag   : Sort → Bits → Bits

module Execution (sch : Scheme) where
  open Scheme sch

  private
    module G = MonoidalCategory 𝔾ᵒ
    module MC = Core (𝒱ₚ 0ℓ)
    variable
      Δ ss : List Sort
      s : Sort
      k : Kind
      x y : ObjTerm
      n : ℕ
      Γ : Fin n → List Sort
      O : List Kind

  Valueᶜ : Kind → Set
  Valueᶜ (msg _) = Bits
  Valueᶜ flag = Bool
  Valueᶜ tick = ⊤

  Frameᶜ : List Sort → Set
  Frameᶜ = All (λ _ → Bits)

  evalᶜ : ℕ → Rcp Δ s → Frameᶜ Δ → Bits
  evalᶜ* : ℕ → All (Rcp Δ) ss → Frameᶜ Δ → Frameᶜ ss
  evalᶜ η (var i) φ = Data.List.Relation.Unary.All.lookup φ i
  evalᶜ η (mine _ ()) φ
  evalᶜ η (app f rs) φ = tag (cod f) (impl f η (evalᶜ* η rs φ))
  evalᶜ* η [] φ = []
  evalᶜ* η (r ∷ rs) φ = evalᶜ η r φ ∷ evalᶜ* η rs φ

  alphabetᶜ : Dir → Atom → Set
  alphabetᶜ _ (port _ _) = Bits
  alphabetᶜ pos verdict = Bool
  alphabetᶜ neg verdict = ⊤
  alphabetᶜ _ void = ⊥

  Alphabetᶜ : Dir → ObjTerm → Set
  Alphabetᶜ d unit = ⊥
  Alphabetᶜ d (x ⊗₀ y) = Alphabetᶜ d x ⊎ Alphabetᶜ d y
  Alphabetᶜ d (Var a) = alphabetᶜ d a

  readᶜ : (d : Dir) (x : ObjTerm) → Alphabetᶜ d x → Σ[ k ∈ Kind ] k ∈ Kinds d x × Valueᶜ k
  readᶜ d (x ⊗₀ y) (inj₁ m) = let k , i , v = readᶜ d x m in k , ∈-++⁺ˡ i , v
  readᶜ d (x ⊗₀ y) (inj₂ m) = let k , i , v = readᶜ d y m in k , ∈-++⁺ʳ (Kinds d x) i , v
  readᶜ pos (Var (port _ _)) v = msg _ , here refl , v
  readᶜ neg (Var (port _ _)) v = msg _ , here refl , v
  readᶜ pos (Var verdict) b = flag , here refl , b
  readᶜ neg (Var verdict) v = tick , here refl , v
  readᶜ d (Var void) ()
  readᶜ d unit ()

  writeᶜ : (d : Dir) (x : ObjTerm) → k ∈ Kinds d x → Valueᶜ k → Alphabetᶜ d x
  writeᶜ d (x ⊗₀ y) i v = [ inj₁ ∘′ (λ j → writeᶜ d x j v) , inj₂ ∘′ (λ j → writeᶜ d y j v) ]′ (∈-++⁻ (Kinds d x) i)
  writeᶜ pos (Var (port _ _)) (here refl) v = v
  writeᶜ neg (Var (port _ _)) (here refl) v = v
  writeᶜ pos (Var verdict) (here refl) v = v
  writeᶜ neg (Var verdict) (here refl) v = v
  writeᶜ pos (Var (port _ _)) (there ()) v
  writeᶜ neg (Var (port _ _)) (there ()) v
  writeᶜ pos (Var verdict) (there ()) v
  writeᶜ neg (Var verdict) (there ()) v
  writeᶜ pos (Var void) () v
  writeᶜ neg (Var void) () v
  writeᶜ d unit () v

  data Inputᶜ (x y : ObjTerm) : Set where
    _↦ᶜ_ : ∀ {k} → k ∈ Ins x y → Valueᶜ k → Inputᶜ x y

  data Emissionᶜ (O : List Kind) : Set where
    _↦ᶜ_ : ∀ {k} → k ∈ O → Valueᶜ k → Emissionᶜ O

  decodeᶜ : ∀ x y → Alphabetᶜ pos x ⊎ Alphabetᶜ neg y → Inputᶜ x y
  decodeᶜ x y (inj₁ m) = let _ , i , v = readᶜ pos x m in ∈-++⁺ˡ i ↦ᶜ v
  decodeᶜ x y (inj₂ m) = let _ , i , v = readᶜ neg y m in ∈-++⁺ʳ (Kinds pos x) i ↦ᶜ v

  encodeᶜ : ∀ x y → Emissionᶜ (Outs x y) → Alphabetᶜ neg x ⊎ Alphabetᶜ pos y
  encodeᶜ x y (i ↦ᶜ v) = [ inj₁ ∘′ (λ j → writeᶜ neg x j v) , inj₂ ∘′ (λ j → writeᶜ pos y j v) ]′ (∈-++⁻ (Kinds neg x) i)

  branchᶜ : Valueᶜ k → Branch k
  branchᶜ {msg _} _ = tt
  branchᶜ {flag} b = b
  branchᶜ {tick} _ = tt

  carryᶜ : Valueᶜ k → Frameᶜ (carried k)
  carryᶜ {msg _} v = v ∷ []
  carryᶜ {flag} _ = []
  carryᶜ {tick} _ = []

  payloadᶜ : ℕ → (k : Kind) → Payload Δ k → Frameᶜ Δ → Valueᶜ k
  payloadᶜ η (msg _) r φ = evalᶜ η r φ
  payloadᶜ η flag b φ = b
  payloadᶜ η tick v φ = v

  record Configᶜ (n : ℕ) (Γ : Fin n → List Sort) : Set where
    constructor configᶜ
    field control : Fin n
          registers : Frameᶜ (Γ control)

  initᶜ : (p : Role x y) → Configᶜ (Role.n p) (Role.Γ p)
  initᶜ p = configᶜ (Role.start p) (subst Frameᶜ (sym (Role.fresh p)) [])

  execᶜ : ℕ → React n Γ O Δ → Frameᶜ Δ → Dₚ (Configᶜ n Γ × Emissionᶜ O)
  execᶜ η (test r r′ t e) φ = if does (evalᶜ η r φ ≟ᵇ evalᶜ η r′ φ) then execᶜ η t φ else execᶜ η e φ
  execᶜ η (new s t) φ = nonce η >>=ₚ λ v → execᶜ η t (tag s v ∷ φ)
  execᶜ η (emit c rs o π) φ = returnₚ (configᶜ c (evalᶜ* η rs φ) , o ↦ᶜ payloadᶜ η _ π φ)

  stepᶜ : ℕ → (p : Role x y) → Configᶜ (Role.n p) (Role.Γ p) → Inputᶜ x y
        → Dₚ (Configᶜ (Role.n p) (Role.Γ p) × Emissionᶜ (Outs x y))
  stepᶜ η p (configᶜ c φ) (i ↦ᶜ v) = execᶜ η (Role.react p c i (branchᶜ v)) (++⁺ (carryᶜ v) φ)

  ⟦_⟧ᴵ : ObjTerm → Iface
  ⟦ x ⟧ᴵ = Alphabetᶜ pos x ⇿ Alphabetᶜ neg x

  runᶜ : ℕ → Role x y → Proc ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ
  runᶜ {x} {y} η p = MC.mk (initˢ (Configᶜ (Role.n p) (Role.Γ p)) (initᶜ p))
    λ (cfg , m) → mapₚ (map₂ (encodeᶜ x y)) (stepᶜ η p cfg (decodeᶜ x y m))

  ⟦v⟧ᶜ : ⟦ Mon ⟧ᵥ
  ⟦v⟧ᶜ = fromMC 𝔾ᵒ noSymmetric

  atomᵒ : Atom → G.Obj
  atomᵒ a = ifaceᵒ (alphabetᶜ pos a ⇿ alphabetᶜ neg a)

  open FreeObjInterp Mon Atom ⟦v⟧ᶜ atomᵒ

  tree≡ : (x : ObjTerm) → UnitFree x → ⟦ x ⟧₀ ≡ ifaceᵒ ⟦ x ⟧ᴵ
  tree≡ (x ⊗₀ y) (ux , uy) = trans (cong₂ G._⊗₀_ (tree≡ x ux) (tree≡ y uy)) (⊗ᵒ ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ)
  tree≡ (Var _) _ = refl
  tree≡ unit ()

  leafᵒ : ℕ → UnitFree x × UnitFree y × Role x y → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
  leafᵒ {x} {y} η (ux , uy , p) = subst₂ G._⇒_ (sym (tree≡ x ux)) (sym (tree≡ y uy)) (procᵒ (runᶜ η p))

  Fᶜ : ℕ → StrongMonoidalFunctor 𝔻𝕐 𝔾ᵒ
  Fᶜ η = freeStrongMonoidal record { ⟦v⟧ = ⟦v⟧ᶜ ; ⟦_⟧ᵖ₀ = atomᵒ ; ⟦_⟧ᵖ₁ = leafᵒ η }
