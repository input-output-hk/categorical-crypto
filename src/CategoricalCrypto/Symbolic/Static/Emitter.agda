{-# OPTIONS --safe --without-K #-}

-- Frame emitters, the processes static equivalence is about
-- (`abadi2018applied` Lemma 4.2 p. 15): a role that draws the names `Ν` on its
-- first activation and answers a query on port `j` with entry `j` of the
-- recipes `ζs` over them, canonical as every emission is (`frame`).  A port
-- carries one sort both ways, and a query is any term of it.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Static.Emitter (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Symbolic.Deduction 𝔖 E
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖

open Signature 𝔖
open Terms 𝔖
open EqTheory E
open Run E

private variable
  s     : Sort
  Δ Δ′ Ν : List Sort
  k     : Kind
  n     : ℕ
  Γ     : Fin n → List Sort
  O     : List Kind

------------------------------------------------------------------------
-- Ports

Ports : List Sort → ObjTerm
Ports []      = Var void
Ports (s ∷ Δ) = Var (port s s) ⊗₀ Ports Δ

ports-free : (Δ : List Sort) → UnitFree (Ports Δ)
ports-free []      = tt
ports-free (_ ∷ Δ) = tt , ports-free Δ

-- Entry `j`'s port, in either direction.
port↦ : (d : Dir) → s ∈ Δ → msg s ∈ Kinds d (Ports Δ)
port↦ pos (here refl) = here refl
port↦ pos (there j)   = there (port↦ pos j)
port↦ neg (here refl) = here refl
port↦ neg (there j)   = there (port↦ neg j)

-- A letter on a port is a letter for some entry.
onPort : (d : Dir) {Δ : List Sort} {P : Kind → Set} → (∀ {s} → s ∈ Δ → P (msg s))
       → k ∈ Kinds d (Ports Δ) → P k
onPort pos {[]}    p ()
onPort pos {_ ∷ _} p (here refl) = p (here refl)
onPort pos {_ ∷ _} {P} p (there i) = onPort pos {P = P} (λ j → p (there j)) i
onPort neg {[]}    p ()
onPort neg {_ ∷ _} p (here refl) = p (here refl)
onPort neg {_ ∷ _} {P} p (there i) = onPort neg {P = P} (λ j → p (there j)) i

onPort-port↦ : (d : Dir) {P : Kind → Set} (p : ∀ {s} → s ∈ Δ → P (msg s)) (j : s ∈ Δ)
             → onPort d {P = P} p (port↦ d j) ≡ p j
onPort-port↦ pos p (here refl) = refl
onPort-port↦ pos {P} p (there j) = onPort-port↦ pos {P = P} (λ j′ → p (there j′)) j
onPort-port↦ neg p (here refl) = refl
onPort-port↦ neg {P} p (there j) = onPort-port↦ neg {P = P} (λ j′ → p (there j′)) j

------------------------------------------------------------------------
-- The emitter

-- Registers set entry by entry.
regs : (Ν : List Sort) → (∀ {s} → s ∈ Ν → Rcp Δ′ s) → All (Rcp Δ′) Ν
regs []      _ = []
regs (_ ∷ Ν) f = f (here refl) ∷ regs Ν (λ i → f (there i))

-- Drawing `Ν` pushes its names on the frame, the last one drawn first.
news : (Ν : List Sort) → React n Γ O (Ν ++ Δ) → React n Γ O Δ
news []      t = t
news (s ∷ Ν) t = news Ν (new s t)

Γᵉ : List Sort → Fin 2 → List Sort
Γᵉ _ zero    = []
Γᵉ Ν (suc _) = Ν

module _ (Ν : List Sort) (ζs : All (Rcp Ν) Δ) where

  Reaction : Fin 2 → Kind → Set
  Reaction c k = React 2 (Γᵉ Ν) (Kinds pos (Ports Δ)) (carried k ++ Γᵉ Ν c)

  -- At `zero` the names are drawn; from then on they are the registers.
  answerᵉ : (c : Fin 2) → s ∈ Δ → Reaction c (msg s)
  answerᵉ zero    j = news Ν (emit (suc zero) (regs Ν λ i → var (∈-++⁺ˡ i)) (port↦ pos j)
                                   (bind (λ i → var (∈-++⁺ˡ i)) (λ ()) (lookup ζs j)))
  answerᵉ (suc _) j = emit (suc zero) (regs Ν λ i → var (there i)) (port↦ pos j)
                           (bind (λ i → var (there i)) (λ ()) (lookup ζs j))

  emitter : Role (Var void) (Ports Δ)
  emitter = record
    { n = 2 ; Γ = Γᵉ Ν ; start = zero ; fresh = refl
    ; react = λ c i _ → onPort neg {P = Reaction c} (answerᵉ c) i }

  react-port↦ : (c : Fin 2) (j : s ∈ Δ) → onPort neg {P = Reaction c} (answerᵉ c) (port↦ neg j) ≡ answerᵉ c j
  react-port↦ c = onPort-port↦ neg (answerᵉ c)

Emitter : (Ν : List Sort) → All (Rcp Ν) Δ → HomTerm (Var void) (Ports Δ)
Emitter {Δ = Δ} Ν ζs = var (tt , ports-free Δ , emitter Ν ζs)

------------------------------------------------------------------------
-- What occurrence `κ` emits

-- The names occurrence `κ` draws from counter `j`, as `news` pushes them.
drawn : ℕ → ℕ → (Ν : List Sort) → Frame Ν
drawn κ j []      = []
drawn κ j (_ ∷ Ν) = name (κ , length Ν + j) ∷ drawn κ j Ν

frame : ℕ → (Ν : List Sort) → All (Rcp Ν) Δ → Frame Δ
frame κ Ν ζs = canon* (ζs ⟨ drawn κ 0 Ν ⟩*)

exec-news : (κ : ℕ) (Ν : List Sort) (t : React n Γ O (Ν ++ Δ)) (φ : Frame Δ) (j : ℕ)
          → exec κ (news Ν t) φ j ≡ exec κ t (++⁺ (drawn κ j Ν) φ) (length Ν + j)
exec-news κ []      t φ j = refl
exec-news κ (s ∷ Ν) t φ j = exec-news κ Ν (new s t) φ j

private
  regs-⟨⟩ : {f : ∀ {s} → s ∈ Ν → Rcp Δ′ s} {φ : Frame Δ′} (d : Frame Ν)
          → (∀ {s} (i : s ∈ Ν) → f i ⟨ φ ⟩ ≡ lookup d i) → regs Ν f ⟨ φ ⟩* ≡ d
  regs-⟨⟩ []      _ = refl
  regs-⟨⟩ (t ∷ d) e = cong₂ _∷_ (e (here refl)) (regs-⟨⟩ d λ i → e (there i))

  lookup-++⁺ˡ : (d : Frame Ν) (φ : Frame Δ) (i : s ∈ Ν) → lookup (++⁺ d φ) (∈-++⁺ˡ i) ≡ lookup d i
  lookup-++⁺ˡ (_ ∷ _) φ (here refl) = refl
  lookup-++⁺ˡ (_ ∷ d) φ (there i)   = lookup-++⁺ˡ d φ i

  lookup-canon* : (φ : Frame Δ) (i : s ∈ Δ) → lookup (canon* φ) i ≡ canon (lookup φ i)
  lookup-canon* (_ ∷ _) (here refl) = refl
  lookup-canon* (_ ∷ φ) (there i)   = lookup-canon* φ i

  canon*-≈E : (φ : Frame Δ) → All₂ _≈E_ (canon* φ) φ
  canon*-≈E []      = []
  canon*-≈E (t ∷ φ) = canon-≈E t ∷ canon*-≈E φ

  canon*-idem : (φ : Frame Δ) → canon* (canon* φ) ≡ canon* φ
  canon*-idem []      = refl
  canon*-idem (t ∷ φ) = cong₂ _∷_ (≈E⇒canon (canon-≈E t)) (canon*-idem φ)

frame-entry : (κ : ℕ) (Ν : List Sort) (ζs : All (Rcp Ν) Δ) (j : s ∈ Δ)
            → lookup (frame κ Ν ζs) j ≡ canon (lookup ζs j ⟨ drawn κ 0 Ν ⟩)
frame-entry κ Ν ζs j = trans (lookup-canon* (ζs ⟨ drawn κ 0 Ν ⟩*) j) (cong canon (lookup-⟨⟩* ζs _ j))

-- After the first activation: the names drawn, kept canonical.
ready : ℕ → (Ν : List Sort) → Config 2 (Γᵉ Ν)
ready κ Ν = config (suc zero) (canon* (drawn κ 0 Ν)) (length Ν + 0)

module _ (κ : ℕ) (Ν : List Sort) (ζs : All (Rcp Ν) Δ) where

  private
    out : Frame Ν → s ∈ Δ → Tm s → Config 2 (Γᵉ Ν) × Emission (Kinds pos (Ports Δ))
    out ρ j t = config (suc zero) ρ (length Ν + 0) , port↦ pos j ↦ t

  first : (j : s ∈ Δ) (q : Tm s)
        → step κ (emitter Ν ζs) (init (emitter Ν ζs)) (port↦ neg j ↦ q)
        ≡ (ready κ Ν , port↦ pos j ↦ lookup (frame κ Ν ζs) j)
  first j q = begin
      step κ (emitter Ν ζs) (init (emitter Ν ζs)) (port↦ neg j ↦ q)
    ≡⟨ cong (λ t → exec κ t (q ∷ []) 0) (react-port↦ Ν ζs zero j) ⟩
      exec κ (answerᵉ Ν ζs zero j) (q ∷ []) 0
    ≡⟨ exec-news κ Ν _ (q ∷ []) 0 ⟩
      out (canon* (regs Ν (λ i → var (∈-++⁺ˡ i)) ⟨ D ⟩*)) j
          (canon (bind (λ i → var (∈-++⁺ˡ i)) (λ ()) (lookup ζs j) ⟨ D ⟩))
    ≡⟨ cong₂ (λ ρ t → out (canon* ρ) j (canon t))
             (regs-⟨⟩ (drawn κ 0 Ν) (lookup-++⁺ˡ (drawn κ 0 Ν) (q ∷ [])))
             (bind-⟨⟩≡ (lookup-++⁺ˡ (drawn κ 0 Ν) (q ∷ [])) (lookup ζs j)) ⟩
      out (canon* (drawn κ 0 Ν)) j (canon (lookup ζs j ⟨ drawn κ 0 Ν ⟩))
    ≡⟨ cong (out (canon* (drawn κ 0 Ν)) j) (sym (frame-entry κ Ν ζs j)) ⟩
      out (canon* (drawn κ 0 Ν)) j (lookup (frame κ Ν ζs) j) ∎
    where
    open ≡-Reasoning
    D = ++⁺ (drawn κ 0 Ν) (q ∷ [])

  later : (j : s ∈ Δ) (q : Tm s)
        → step κ (emitter Ν ζs) (ready κ Ν) (port↦ neg j ↦ q)
        ≡ (ready κ Ν , port↦ pos j ↦ lookup (frame κ Ν ζs) j)
  later j q = begin
      step κ (emitter Ν ζs) (ready κ Ν) (port↦ neg j ↦ q)
    ≡⟨ cong (λ t → exec κ t (q ∷ R) (length Ν + 0)) (react-port↦ Ν ζs (suc zero) j) ⟩
      out (canon* (regs Ν (λ i → var (there i)) ⟨ q ∷ R ⟩*)) j
          (canon (bind (λ i → var (there i)) (λ ()) (lookup ζs j) ⟨ q ∷ R ⟩))
    ≡⟨ cong₂ (λ ρ t → out (canon* ρ) j (canon t))
             (regs-⟨⟩ R λ _ → refl) (bind-⟨⟩≡ (λ _ → refl) (lookup ζs j)) ⟩
      out (canon* R) j (canon (lookup ζs j ⟨ R ⟩))
    ≡⟨ cong₂ (λ ρ t → out ρ j t) (canon*-idem (drawn κ 0 Ν))
             (≈E⇒canon (⟨⟩-cong (canon*-≈E (drawn κ 0 Ν)) (lookup ζs j))) ⟩
      out R j (canon (lookup ζs j ⟨ drawn κ 0 Ν ⟩))
    ≡⟨ cong (out R j) (sym (frame-entry κ Ν ζs j)) ⟩
      out R j (lookup (frame κ Ν ζs) j) ∎
    where
    open ≡-Reasoning
    R = canon* (drawn κ 0 Ν)
