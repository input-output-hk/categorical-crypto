{-# OPTIONS --safe --without-K #-}

-- Dolev–Yao roles, the generators of the symbolic setup: finite reactive
-- programs whose registers and emissions are recipes over their own frame (the
-- roles of `canettiherzog2006` Def 1 p. 389; the basic processes of
-- `comonlundhcortier2008` §3.3 pp. 10–12).  An activation runs a decision tree
-- — guards modulo E, fresh names, then one emission and a jump — and names
-- enter a role only through `new`.  `Run.emits⊢`: whatever a role emits is
-- deducible from what it received and its own names, so roles are DY deducers.
-- See docs/uc-setup-symbolic.md §3.3.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Role (𝔖 : Signature) where

open import Categories.FreeMonoidal
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
open import Data.Sum.Base
open import Data.Unit
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary using (∅; _⊆_)

import CategoricalCrypto.Symbolic.Deduction as Deduction

open Signature 𝔖
open Terms 𝔖

------------------------------------------------------------------------
-- Atoms and their alphabets

-- `port s t` carries sort `s` on `Pos` and `t` on `Neg` (`Iface.agda`);
-- `verdict` is `UC.Machine.Ωᴵ`; `void` is the empty interface closures leave.
data Atom : Set where
  port    : (pos neg : Sort) → Atom
  verdict : Atom
  void    : Atom

private
  port-injective : ∀ {s t s′ t′} → port s t ≡ port s′ t′ → s ≡ s′ × t ≡ t′
  port-injective refl = refl , refl

_≟ᴬ_ : DecidableEquality Atom
port s t ≟ᴬ port s′ t′ with s ≟ˢ s′ | t ≟ˢ t′
... | yes refl | yes refl = yes refl
... | no s≢s′  | _        = no (s≢s′ ∘ proj₁ ∘ port-injective)
... | yes _    | no t≢t′  = no (t≢t′ ∘ proj₂ ∘ port-injective)
port _ _ ≟ᴬ verdict  = no λ ()
port _ _ ≟ᴬ void     = no λ ()
verdict  ≟ᴬ port _ _ = no λ ()
verdict  ≟ᴬ verdict  = yes refl
verdict  ≟ᴬ void     = no λ ()
void     ≟ᴬ port _ _ = no λ ()
void     ≟ᴬ verdict  = no λ ()
void     ≟ᴬ void     = yes refl

open FreeMonoidalHelper Mon Atom

-- Direction of travel: `pos` rightwards, `neg` leftwards.
data Dir : Set where
  pos neg : Dir

-- What crosses an atom in one direction: a term, a verdict bit, or the tick
-- that asks for one.
data Kind : Set where
  msg  : Sort → Kind
  flag : Kind
  tick : Kind

Value : Kind → Set
Value (msg s) = Tm s
Value flag    = Bool
Value tick    = ⊤

kinds : Dir → Atom → List Kind
kinds pos (port s _) = msg s ∷ []
kinds neg (port _ t) = msg t ∷ []
kinds pos verdict    = flag ∷ []
kinds neg verdict    = tick ∷ []
kinds _   void       = []

Kinds : Dir → ObjTerm → List Kind
Kinds d unit     = []
Kinds d (A ⊗₀ B) = Kinds d A ++ Kinds d B
Kinds d (Var a)  = kinds d a

-- The alphabets the semantics reads an object at: `Alphabet pos x ⇿
-- Alphabet neg x` is definitionally the `_⊗ᴵ_`-tree of the atoms' interfaces.
alphabet : Dir → Atom → Set
alphabet pos (port s _) = Tm s
alphabet neg (port _ t) = Tm t
alphabet pos verdict    = Bool
alphabet neg verdict    = ⊤
alphabet _   void       = ⊥

Alphabet : Dir → ObjTerm → Set
Alphabet d unit     = ⊥
Alphabet d (A ⊗₀ B) = Alphabet d A ⊎ Alphabet d B
Alphabet d (Var a)  = alphabet d a

read : ∀ d x → Alphabet d x → Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k
read d   (A ⊗₀ B) (inj₁ m) = let k , i , v = read d A m in k , ∈-++⁺ˡ i , v
read d   (A ⊗₀ B) (inj₂ m) = let k , i , v = read d B m in k , ∈-++⁺ʳ (Kinds d A) i , v
read pos (Var (port s _)) v = msg s , here refl , v
read neg (Var (port _ t)) v = msg t , here refl , v
read pos (Var verdict)    b = flag , here refl , b
read neg (Var verdict)    _ = tick , here refl , tt
read pos (Var void)       ()
read neg (Var void)       ()
read _   unit             ()

write : ∀ d x {k} → k ∈ Kinds d x → Value k → Alphabet d x
write d   (A ⊗₀ B)         i           v = [ (λ j → inj₁ (write d A j v)) , (λ j → inj₂ (write d B j v)) ]′
                                             (∈-++⁻ (Kinds d A) i)
write pos (Var (port _ _)) (here refl) v = v
write neg (Var (port _ _)) (here refl) v = v
write pos (Var verdict)    (here refl) b = b
write neg (Var verdict)    (here refl) _ = tt
write pos (Var (port _ _)) (there ())  _
write neg (Var (port _ _)) (there ())  _
write pos (Var verdict)    (there ())  _
write neg (Var verdict)    (there ())  _
write pos (Var void)       ()          _
write neg (Var void)       ()          _
write _   unit             ()          _

------------------------------------------------------------------------
-- Roles

-- A role on `x ⇒ y` is activated on `Pos` of `x` and `Neg` of `y`, and emits
-- on `Neg` of `x` and `Pos` of `y` (`UC.Machine.Proc`).
Ins Outs : ObjTerm → ObjTerm → List Kind
Ins  x y = Kinds pos x ++ Kinds neg y
Outs x y = Kinds neg x ++ Kinds pos y

data Input (x y : ObjTerm) : Set where
  _↦_ : ∀ {k} → k ∈ Ins x y → Value k → Input x y

data Emission (O : List Kind) : Set where
  _↦_ : ∀ {k} → k ∈ O → Value k → Emission O

decode : ∀ x y → Alphabet pos x ⊎ Alphabet neg y → Input x y
decode x y (inj₁ m) = let _ , i , v = read pos x m in ∈-++⁺ˡ i ↦ v
decode x y (inj₂ m) = let _ , i , v = read neg y m in ∈-++⁺ʳ (Kinds pos x) i ↦ v

encode : ∀ x y → Emission (Outs x y) → Alphabet neg x ⊎ Alphabet pos y
encode x y (i ↦ v) = [ (λ j → inj₁ (write neg x j v)) , (λ j → inj₂ (write pos y j v)) ]′
                       (∈-++⁻ (Kinds neg x) i)

-- A role branches on the bit it receives; a received term is pushed on its frame.
Branch : Kind → Set
Branch flag = Bool
Branch _    = ⊤

carried : Kind → List Sort
carried (msg s) = s ∷ []
carried _       = []

branch : ∀ {k} → Value k → Branch k
branch {msg _} _ = tt
branch {flag}  b = b
branch {tick}  _ = tt

carry : ∀ {k} → Value k → Frame (carried k)
carry {msg _} t = t ∷ []
carry {flag}  _ = []
carry {tick}  _ = []

-- Recipes over the frame alone: a role holds no name it did not draw.
Rcp : List Sort → Sort → Set
Rcp Δ = Recipe Δ ∅

Payload : List Sort → Kind → Set
Payload Δ (msg s) = Rcp Δ s
Payload Δ flag    = Bool
Payload Δ tick    = ⊤

private variable
  s    : Sort
  Δ ss : List Sort
  k    : Kind
  x y  : ObjTerm

-- One activation over frame `Δ`, with control points `Fin n` keeping frames `Γ`.
data React (n : ℕ) (Γ : Fin n → List Sort) (O : List Kind) : List Sort → Set where
  test : Rcp Δ s → Rcp Δ s → React n Γ O Δ → React n Γ O Δ → React n Γ O Δ
  new  : ∀ s → React n Γ O (s ∷ Δ) → React n Γ O Δ
  emit : (c : Fin n) → All (Rcp Δ) (Γ c) → k ∈ O → Payload Δ k → React n Γ O Δ

record Role (x y : ObjTerm) : Set where
  field
    n     : ℕ
    Γ     : Fin n → List Sort
    start : Fin n
    fresh : Γ start ≡ []
    react : (c : Fin n) {k : Kind} → k ∈ Ins x y → Branch k → React n Γ (Outs x y) (carried k ++ Γ c)

-- The reaction tables of the roles shaped like `p`.
Reactions : Role x y → Set
Reactions {x} {y} p =
  (c : Fin (Role.n p)) {k : Kind} → k ∈ Ins x y → Branch k → React (Role.n p) (Role.Γ p) (Outs x y) (carried k ++ Role.Γ p c)

-- `comonlundhcortier2008` §3.3: a failed guard emits a fixed message and the
-- process stops.  Here the message is a ground payload and stopping is a jump
-- to a control point that answers every activation in the same way.  CLC's
-- well-formedness guard `M` needs check symbols in the signature.
GroundPayload : ∀ k → Payload Δ k → Set
GroundPayload (msg _) ζ = Ground ζ
GroundPayload flag    _ = ⊤
GroundPayload tick    _ = ⊤

module _ {n} {Γ : Fin n → List Sort} {O : List Kind} (h : Fin n) where
  data Halts : ∀ {Δ} → React n Γ O Δ → Set where
    halts : {ρs : All (Rcp Δ) (Γ h)} {o : k ∈ O} {π : Payload Δ k}
          → GroundPayload k π → Halts (emit h ρs o π)

  data Guarded : ∀ {Δ} → React n Γ O Δ → Set where
    test : {ζ ζ′ : Rcp Δ s} {t e : React n Γ O Δ} → Guarded t → Halts e → Guarded (test ζ ζ′ t e)
    new  : {t : React n Γ O (s ∷ Δ)} → Guarded t → Guarded (new s t)
    emit : {c : Fin n} {ρs : All (Rcp Δ) (Γ c)} {o : k ∈ O} {π : Payload Δ k} → Guarded (emit c ρs o π)

record Simple (p : Role x y) : Set where
  field
    halt    : Fin (Role.n p)
    halted  : ∀ {k} (i : k ∈ Ins x y) b → Halts halt (Role.react p halt i b)
    guarded : ∀ c {k} (i : k ∈ Ins x y) b → Guarded halt (Role.react p c i b)

------------------------------------------------------------------------
-- Running a role, and the Dolev–Yao property

record Config (n : ℕ) (Γ : Fin n → List Sort) : Set where
  constructor config
  field
    control   : Fin n
    registers : Frame (Γ control)
    counter   : ℕ
open Config public

init : (p : Role x y) → Config (Role.n p) (Role.Γ p)
init p = config (Role.start p) (subst Frame (sym (Role.fresh p)) []) 0

payload : ∀ k → Payload Δ k → Frame Δ → Value k
payload (msg _) ζ φ = ζ ⟨ φ ⟩
payload flag    b _ = b
payload tick    _ _ = tt

-- The terms received over a history of inputs, newest first.
Received : List (Input x y) → List Sort
Received []                   = []
Received (_↦_ {k} _ _ ∷ hist) = carried k ++ Received hist

received : (hist : List (Input x y)) → Frame (Received hist)
received []               = []
received ((_ ↦ v) ∷ hist) = ++⁺ (carry v) (received hist)

Own : ℕ → Name → Set
Own κ (κ′ , _) = κ′ ≡ κ

module Run (E : EqTheory 𝔖) where
  open EqTheory E
  open Deduction 𝔖 E

  private variable
    n : ℕ
    Γ : Fin n → List Sort
    O : List Kind

  -- What a role emits and stores is canonical (`EqTheory.canon`).
  canonᵛ : ∀ {k} → Value k → Value k
  canonᵛ {msg _} t = canon t
  canonᵛ {flag}  b = b
  canonᵛ {tick}  _ = tt

  canon* : Frame Δ → Frame Δ
  canon* []      = []
  canon* (t ∷ φ) = canon t ∷ canon* φ

  -- Occurrence `κ` draws its `j`-th fresh name as `(κ , j)`.
  exec : (κ : ℕ) → React n Γ O Δ → Frame Δ → ℕ → Config n Γ × Emission O
  exec κ (test ζ ζ′ t e) φ j = if does (ζ ⟨ φ ⟩ ≟E ζ′ ⟨ φ ⟩) then exec κ t φ j else exec κ e φ j
  exec κ (new _ t)       φ j = exec κ t (name (κ , j) ∷ φ) (suc j)
  exec κ (emit c ρs o π) φ j = config c (canon* (ρs ⟨ φ ⟩*)) j , o ↦ canonᵛ (payload _ π φ)

  step : (κ : ℕ) (p : Role x y) → Config (Role.n p) (Role.Γ p) → Input x y
       → Config (Role.n p) (Role.Γ p) × Emission (Outs x y)
  step κ p (config c φ j) (i ↦ v) = exec κ (Role.react p c i (branch v)) (++⁺ (carry v) φ) j

  -- An emitted term is deducible; a bit or a tick carries no term.
  Known : Knowledge Δ → Emission O → Set
  Known K (_↦_ {msg _} _ t) = K ⊢ t
  Known K (_↦_ {flag}  _ _) = ⊤
  Known K (_↦_ {tick}  _ _) = ⊤

  Deduced : Knowledge Δ → Config n Γ × Emission O → Set
  Deduced K (cfg , em) = Each (K ⊢_) (registers cfg) × Known K em

  exec⊢ : ∀ {κ} {K : Knowledge ss} → Own κ ⊆ proj₂ K
        → (t : React n Γ O Δ) {φ : Frame Δ} {j : ℕ} → Each (K ⊢_) φ → Deduced K (exec κ t φ j)
  exec⊢ h (test ζ ζ′ t e) {φ} ds with ζ ⟨ φ ⟩ ≟E ζ′ ⟨ φ ⟩
  ... | yes _ = exec⊢ h t ds
  ... | no _  = exec⊢ h e ds
  exec⊢ h (new _ t) ds = exec⊢ h t (⊢-owned (h refl) ∷ ds)
  exec⊢ {K = K} h (emit _ ρs o π) {φ} ds = regs⊢ ρs , known⊢ _ π
    where
    rcp⊢ : (ρ : Rcp _ s) → K ⊢ canon (ρ ⟨ φ ⟩)
    rcp⊢ ρ = ⊢-cut ds (λ ()) (ρ , ≈E.sym (canon-≈E _))
    regs⊢ : (ρs : All (Rcp _) ss) → Each (K ⊢_) (canon* (ρs ⟨ φ ⟩*))
    regs⊢ []       = []
    regs⊢ (ρ ∷ ρs) = rcp⊢ ρ ∷ regs⊢ ρs
    known⊢ : ∀ k {o : k ∈ _} (π : Payload _ k) → Known K (o ↦ canonᵛ (payload k π φ))
    known⊢ (msg _) ρ = rcp⊢ ρ
    known⊢ flag    _ = tt
    known⊢ tick    _ = tt

  private
    carry⊢ : ∀ {own} {Ψ : Frame ss} {φ : Frame Δ} (v : Value k)
           → Each ((Ψ , own) ⊢_) φ → Each ((++⁺ (carry v) Ψ , own) ⊢_) (++⁺ (carry v) φ)
    carry⊢ {k = msg _} _ ds = ⊢-entry (here refl) ∷ mapᴱ ⊢-wk ds
    carry⊢ {k = flag}  _ ds = ds
    carry⊢ {k = tick}  _ ds = ds

    cleared : ∀ {P : ∀ {s} → Tm s → Set} {ss} (e : [] ≡ ss) → Each P (subst Frame e [])
    cleared refl = []

  step⊢ : ∀ κ (p : Role x y) {Ψ : Frame ss} {cfg : Config (Role.n p) (Role.Γ p)}
          (i : k ∈ Ins x y) (v : Value k) → Each ((Ψ , Own κ) ⊢_) (registers cfg)
        → Deduced (++⁺ (carry v) Ψ , Own κ) (step κ p cfg (i ↦ v))
  step⊢ κ p {cfg = config c _ _} i v ds = exec⊢ (λ e → e) (Role.react p c i (branch v)) (carry⊢ v ds)

  module _ (κ : ℕ) (p : Role x y) where
    -- The configuration after a history of inputs, newest first.
    after : List (Input x y) → Config (Role.n p) (Role.Γ p)
    after []          = init p
    after (inp ∷ hist) = proj₁ (step κ p (after hist) inp)

    after⊢ : (hist : List (Input x y)) → Each ((received hist , Own κ) ⊢_) (registers (after hist))
    after⊢ []          = cleared (sym (Role.fresh p))
    after⊢ ((i ↦ v) ∷ hist) = proj₁ (step⊢ κ p i v (after⊢ hist))

    -- Roles are DY deducers: an emission is deducible from every term received
    -- so far, its trigger included, and the names of the emitting occurrence.
    emits⊢ : (hist : List (Input x y)) (inp : Input x y)
           → Known (received (inp ∷ hist) , Own κ) (proj₂ (step κ p (after hist) inp))
    emits⊢ hist (i ↦ v) = proj₂ (step⊢ κ p i v (after⊢ hist))

  -- Values equal modulo E.
  _≈ᵛ_ : ∀ {k} → Value k → Value k → Set
  _≈ᵛ_ {msg _} = _≈E_
  _≈ᵛ_ {flag}  = _≡_
  _≈ᵛ_ {tick}  = _≡_

  -- Two programs of one shape whose recipes agree modulo E on every frame.
  data ReactE {n} {Γ : Fin n → List Sort} {O : List Kind} : ∀ {Δ} → React n Γ O Δ → React n Γ O Δ → Set where
    test : {ζ₁ ζ₁′ ζ₂ ζ₂′ : Rcp Δ s} {t t′ e e′ : React n Γ O Δ}
         → (∀ φ → ζ₁ ⟨ φ ⟩ ≈E ζ₂ ⟨ φ ⟩) → (∀ φ → ζ₁′ ⟨ φ ⟩ ≈E ζ₂′ ⟨ φ ⟩)
         → ReactE t t′ → ReactE e e′ → ReactE (test ζ₁ ζ₁′ t e) (test ζ₂ ζ₂′ t′ e′)
    new  : {t t′ : React n Γ O (s ∷ Δ)} → ReactE t t′ → ReactE (new s t) (new s t′)
    emit : {c : Fin n} {ρs ρs′ : All (Rcp Δ) (Γ c)} {o : k ∈ O} {π π′ : Payload Δ k}
         → (∀ φ → All₂ _≈E_ (ρs ⟨ φ ⟩*) (ρs′ ⟨ φ ⟩*)) → (∀ φ → payload k π φ ≈ᵛ payload k π′ φ)
         → ReactE (emit c ρs o π) (emit c ρs′ o π′)

  private
    canon*-cong : {φ ψ : Frame Δ} → All₂ _≈E_ φ ψ → canon* φ ≡ canon* ψ
    canon*-cong []       = refl
    canon*-cong (e ∷ es) = cong₂ _∷_ (≈E⇒canon e) (canon*-cong es)

    canonᵛ-cong : ∀ {k} {v v′ : Value k} → v ≈ᵛ v′ → canonᵛ v ≡ canonᵛ v′
    canonᵛ-cong {msg _} e = ≈E⇒canon e
    canonᵛ-cong {flag}  e = e
    canonᵛ-cong {tick}  _ = refl

  -- E-equal programs run alike: what they emit and store is canonical.
  exec-≈E : ∀ {κ} {t t′ : React n Γ O Δ} → ReactE t t′ → ∀ φ j → exec κ t φ j ≡ exec κ t′ φ j
  exec-≈E (test {ζ₁ = ζ₁} {ζ₁′} {ζ₂} {ζ₂′} e₁ e₂ rt re) φ j with ζ₁ ⟨ φ ⟩ ≟E ζ₁′ ⟨ φ ⟩ | ζ₂ ⟨ φ ⟩ ≟E ζ₂′ ⟨ φ ⟩
  ... | yes _ | yes _ = exec-≈E rt φ j
  ... | no _  | no _  = exec-≈E re φ j
  ... | yes a | no ¬b = ⊥-elim (¬b (≈E.trans (≈E.sym (e₁ φ)) (≈E.trans a (e₂ φ))))
  ... | no ¬a | yes b = ⊥-elim (¬a (≈E.trans (e₁ φ) (≈E.trans b (≈E.sym (e₂ φ)))))
  exec-≈E {κ = κ} (new rt) φ j = exec-≈E rt (name (κ , j) ∷ φ) (suc j)
  exec-≈E (emit {c = c} {o = o} es ev) φ j =
    cong₂ _,_ (cong (λ ψ → config c ψ j) (canon*-cong (es φ))) (cong {B = Emission _} (o ↦_) (canonᵛ-cong (ev φ)))

  step-≈E : ∀ κ (p : Role x y) {r : Reactions p}
          → (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
          → ∀ cfg inp → step κ p cfg inp ≡ step κ (record p { react = r }) cfg inp
  step-≈E κ p e (config c φ j) (i ↦ v) = exec-≈E (e c i (branch v)) (++⁺ (carry v) φ) j
