{-# OPTIONS --safe --without-K #-}

-- The tester of `Static.Distinguish`.  Its registers hold one slot per port of
-- `Ports Δ`: on the tick it fills them with names of its own, then queries the
-- ports from the last down, each answer overwriting its slot (`refresh`).
-- After the first port it draws the names `Θ` and answers whether two recipes
-- over `Θ` and the slots agree.  `stage c` is the program once ports `c` and up
-- are answered, so a run is an induction on `c` (`Distinguish.Run`).

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Static.Distinguish.Tester (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; fromℕ; inject₁)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-lookup)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻∘++⁺; ++⁺∘++⁻)
open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary using (∅)

open import CategoricalCrypto.Symbolic.Deduction 𝔖 E
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.Symbolic.Static.Emitter 𝔖 E

import Data.List.Base as List

open Signature 𝔖
open Terms 𝔖
open EqTheory E
open Run E

private variable
  s     : Sort
  Δ Θ Λ : List Sort

------------------------------------------------------------------------
-- Slots

set : s ∈ Δ → Tm s → Frame Δ → Frame Δ
set (here refl) t (_ ∷ R) = t ∷ R
set (there j)   t (r ∷ R) = r ∷ set j t R

skip : ∀ {s′ x y} → s′ ∈ x ∷ Δ → s′ ∈ x ∷ y ∷ Δ
skip (here e)  = here e
skip (there i) = there (there i)

-- The registers after an answer on port `j`.
refresh : (j : s ∈ Δ) → All (Rcp (s ∷ Δ)) Δ
refresh {Δ = _ ∷ Δ} (here refl) = var (here refl) ∷ regs Δ (λ i → var (there (there i)))
refresh {Δ = _ ∷ _} (there j)   = var (there (here refl)) ∷ bind* (λ i → var (skip i)) (λ p → p) (refresh j)

regs-⟨⟩ : {f : ∀ {s} → s ∈ Θ → Rcp Λ s} {F : Frame Λ} (d : Frame Θ)
        → (∀ {s} (i : s ∈ Θ) → f i ⟨ F ⟩ ≡ lookup d i) → regs Θ f ⟨ F ⟩* ≡ d
regs-⟨⟩ []      _ = refl
regs-⟨⟩ (t ∷ d) e = cong₂ _∷_ (e (here refl)) (regs-⟨⟩ d λ i → e (there i))

refresh-⟨⟩ : (j : s ∈ Δ) (t : Tm s) (R : Frame Δ) → refresh j ⟨ t ∷ R ⟩* ≡ set j t R
refresh-⟨⟩ (here refl) t (_ ∷ R) = cong (t ∷_) (regs-⟨⟩ R λ _ → refl)
refresh-⟨⟩ (there j)   t (r ∷ R) = cong (r ∷_) (trans (bind-⟨⟩≡* skip-⟨⟩ (refresh j)) (refresh-⟨⟩ j t R))
  where
  skip-⟨⟩ : ∀ {s′} (i : s′ ∈ _ ∷ _) → var {own = ∅} (skip i) ⟨ t ∷ r ∷ R ⟩ ≡ lookup (t ∷ R) i
  skip-⟨⟩ (here refl) = refl
  skip-⟨⟩ (there _)   = refl

-- `R` agrees with `φ` modulo E at the positions from `c` up.
From : Fin (suc (length Δ)) → Frame Δ → Frame Δ → Set
From zero    R       φ       = All₂ _≈E_ R φ
From (suc c) (_ ∷ R) (_ ∷ φ) = From c R φ

From-top : (R φ : Frame Δ) → From (fromℕ (length Δ)) R φ
From-top []      []      = []
From-top (_ ∷ R) (_ ∷ φ) = From-top R φ

From-canon : (c : Fin (suc (length Δ))) {R φ : Frame Δ} → From c R φ → From c (canon* R) φ
From-canon zero    a = go a
  where
  go : {R φ : Frame Δ} → All₂ _≈E_ R φ → All₂ _≈E_ (canon* R) φ
  go []                   = []
  go {R = r ∷ _} (e ∷ es) = ≈E.trans (canon-≈E r) e ∷ go es
From-canon (suc c) {_ ∷ R} {_ ∷ φ} a = From-canon c {R} {φ} a

From-step : (i : Fin (length Δ)) {t : Tm (List.lookup Δ i)} {R φ : Frame Δ}
          → From (suc i) R φ → t ≈E lookup φ (∈-lookup i) → From (inject₁ i) (set (∈-lookup i) t R) φ
From-step {_ ∷ _} zero    {R = _ ∷ _} {_ ∷ _} a e = e ∷ a
From-step {_ ∷ _} (suc i) {t} {_ ∷ R} {_ ∷ φ} a e = From-step i {t} {R} {φ} a e

------------------------------------------------------------------------
-- Ports and frames

lookup-++⁺ˡ : (D : Frame Θ) (F : Frame Λ) (i : s ∈ Θ) → lookup (++⁺ D F) (∈-++⁺ˡ i) ≡ lookup D i
lookup-++⁺ˡ (_ ∷ _) F (here refl) = refl
lookup-++⁺ˡ (_ ∷ D) F (there i)   = lookup-++⁺ˡ D F i

lookup-++⁺ʳ : (D : Frame Θ) (F : Frame Λ) (i : s ∈ Λ) → lookup (++⁺ D F) (∈-++⁺ʳ Θ i) ≡ lookup F i
lookup-++⁺ʳ []      F i = refl
lookup-++⁺ʳ (_ ∷ D) F i = lookup-++⁺ʳ D F i

read-write : (d : Dir) (j : s ∈ Δ) (t : Tm s)
           → read d (Ports Δ) (write d (Ports Δ) (port↦ d j) t) ≡ (msg s , port↦ d j , t)
read-write pos (here refl) t = refl
read-write neg (here refl) t = refl
read-write {Δ = x ∷ _} pos (there j) t = cong (λ r → proj₁ r , ∈-++⁺ʳ (msg x ∷ []) (proj₁ (proj₂ r)) , proj₂ (proj₂ r)) (read-write pos j t)
read-write {Δ = x ∷ _} neg (there j) t = cong (λ r → proj₁ r , ∈-++⁺ʳ (msg x ∷ []) (proj₁ (proj₂ r)) , proj₂ (proj₂ r)) (read-write neg j t)

-- A query, as the emitter reads it.
decode-query : (j : s ∈ Δ) (q : Tm s)
             → decode (Var void) (Ports Δ) (inj₂ (write neg (Ports Δ) (port↦ neg j) q)) ≡ (port↦ neg j ↦ q)
decode-query {Δ = Δ} j q = cong {B = Input (Var void) (Ports Δ)} (λ r → proj₁ (proj₂ r) ↦ proj₂ (proj₂ r)) (read-write neg j q)

------------------------------------------------------------------------
-- The tester

Γᵀ : (Δ : List Sort) → Fin (suc (length Δ)) → List Sort
Γᵀ _ zero    = []
Γᵀ Δ (suc _) = Δ

Oᵀ : List Sort → List Kind
Oᵀ Δ = Outs (Ports Δ) (Var verdict)

query↦ : s ∈ Δ → msg s ∈ Oᵀ Δ
query↦ j = ∈-++⁺ˡ (port↦ neg j)

verdict↦ : (Δ : List Sort) → flag ∈ Oᵀ Δ
verdict↦ Δ = ∈-++⁺ʳ (Kinds neg (Ports Δ)) (here refl)

answerIn : s ∈ Δ → Tm s → Input (Ports Δ) (Var verdict)
answerIn j t = ∈-++⁺ˡ (port↦ pos j) ↦ t

encode-query : (j : s ∈ Δ) (q : Tm s)
             → encode (Ports Δ) (Var verdict) (query↦ j ↦ q) ≡ inj₁ (write neg (Ports Δ) (port↦ neg j) q)
encode-query {Δ = Δ} j q =
  cong [ (λ i → inj₁ (write neg (Ports Δ) i q)) , (λ i → inj₂ (write pos (Var verdict) i q)) ]′
       (++⁻∘++⁺ (Kinds neg (Ports Δ)) (inj₁ (port↦ neg j)))

encode-verdict : (b : Bool) → encode (Ports Δ) (Var verdict) (verdict↦ Δ ↦ b) ≡ inj₂ b
encode-verdict {Δ} b =
  cong [ (λ i → inj₁ (write neg (Ports Δ) i b)) , (λ i → inj₂ (write pos (Var verdict) i b)) ]′
       (++⁻∘++⁺ (Kinds neg (Ports Δ)) (inj₂ (here refl)))

decode-answer : (j : s ∈ Δ) (t : Tm s) → decode (Ports Δ) (Var verdict) (inj₁ (write pos (Ports Δ) (port↦ pos j) t)) ≡ answerIn j t
decode-answer {Δ = Δ} j t = cong {B = Input (Ports Δ) (Var verdict)} (λ r → ∈-++⁺ˡ (proj₁ (proj₂ r)) ↦ proj₂ (proj₂ r)) (read-write pos j t)

-- The slots, filled with the names drawn on the tick.
slots₀ : All (Rcp (Δ ++ [])) Δ
slots₀ {Δ} = regs Δ (λ i → var (∈-++⁺ˡ i))

private
  if-same : {A : Set} (X : Bool → A) (b : Bool) → (if b then X true else X false) ≡ X b
  if-same X true  = refl
  if-same X false = refl

  does-≈ : {a a′ b b′ : Tm s} → a ≈E a′ → b ≈E b′ → does (a ≟E b) ≡ does (a′ ≟E b′)
  does-≈ {a = a} {a′} {b} {b′} ea eb with a ≟E b | a′ ≟E b′
  ... | yes _ | yes _ = refl
  ... | no _  | no _  = refl
  ... | yes p | no ¬q = ⊥-elim (¬q (≈E.trans (≈E.sym ea) (≈E.trans p eb)))
  ... | no ¬p | yes q = ⊥-elim (¬p (≈E.trans ea (≈E.trans q (≈E.sym eb))))

module _ {Δ : List Sort} (Θ : List Sort) {s₀ : Sort} (ẑ ẑ′ : Rcp (Θ ++ Δ) s₀) where

  private
    N : ℕ
    N = suc (length Δ)

    Reactᵀ : List Sort → Set
    Reactᵀ = React N (Γᵀ Δ) (Oᵀ Δ)

  -- A drawn name in place, a slot through `ρs`.
  slot : All (Rcp Λ) Δ → s ∈ Θ ⊎ s ∈ Δ → Rcp (Θ ++ Λ) s
  slot ρs (inj₁ θ) = var (∈-++⁺ˡ θ)
  slot ρs (inj₂ i) = bind (λ q → var (∈-++⁺ʳ Θ q)) (λ p → p) (lookup ρs i)

  rebase : All (Rcp Λ) Δ → Rcp (Θ ++ Δ) s → Rcp (Θ ++ Λ) s
  rebase ρs = bind (λ p → slot ρs (∈-++⁻ Θ p)) (λ p → p)

  final : All (Rcp Λ) Δ → Reactᵀ Λ
  final ρs = news Θ (test (rebase ρs ẑ) (rebase ρs ẑ′) (emit zero [] (verdict↦ Δ) true) (emit zero [] (verdict↦ Δ) false))

  stage : Fin N → All (Rcp Λ) Δ → Reactᵀ Λ
  stage zero    ρs = final ρs
  stage (suc i) ρs = emit (suc i) ρs (query↦ (∈-lookup {xs = Δ} i)) (lookup ρs (∈-lookup i))

  private
    halt : Reactᵀ Λ
    halt = emit zero [] (verdict↦ Δ) false

    answer : (c : Fin N) → s ∈ Δ → Reactᵀ (s ∷ Γᵀ Δ c)
    answer zero    _ = halt
    answer (suc i) j = stage (inject₁ i) (refresh j)

    onTick : (c : Fin N) → Reactᵀ (Γᵀ Δ c)
    onTick zero    = news Δ (stage (fromℕ (length Δ)) slots₀)
    onTick (suc _) = halt

    P : Fin N → Kind → Set
    P c k = Branch k → Reactᵀ (carried k ++ Γᵀ Δ c)

    dispatch : (c : Fin N) {k : Kind} → k ∈ Kinds pos (Ports Δ) ⊎ k ∈ Kinds neg (Var verdict) → P c k
    dispatch c (inj₁ j)           = onPort pos {Δ} {P = P c} (λ j _ → answer c j) j
    dispatch c (inj₂ (here refl)) = λ _ → onTick c
    dispatch c (inj₂ (there ()))

  tester : Role (Ports Δ) (Var verdict)
  tester = record
    { n = N ; Γ = Γᵀ Δ ; start = zero ; fresh = refl
    ; react = λ c i → dispatch c (∈-++⁻ (Kinds pos (Ports Δ)) i) }

  ----------------------------------------------------------------------
  -- Its steps

  step-tick : ∀ κ → step κ tester (init tester) (decode (Ports Δ) (Var verdict) (inj₂ tt))
                  ≡ exec κ (stage (fromℕ (length Δ)) slots₀) (++⁺ (drawn κ 0 Δ) []) (length Δ + 0)
  step-tick κ = trans (cong (λ d → exec κ (dispatch zero d tt) [] 0) (++⁻∘++⁺ (Kinds pos (Ports Δ)) (inj₂ (here refl))))
                      (exec-news κ Δ _ [] 0)

  step-answer : ∀ κ (i : Fin (length Δ)) (j : s ∈ Δ) t (R : Frame Δ) m
              → step κ tester (config (suc i) R m) (answerIn j t) ≡ exec κ (stage (inject₁ i) (refresh j)) (t ∷ R) m
  step-answer κ i j t R m =
    trans (cong (λ d → exec κ (dispatch (suc i) d tt) (t ∷ R) m) (++⁻∘++⁺ (Kinds pos (Ports Δ)) (inj₁ (port↦ pos j))))
          (cong (λ f → exec κ (f tt) (t ∷ R) m) (onPort-port↦ pos {P = P (suc i)} (λ j _ → answer (suc i) j) j))

  exec-final : ∀ κ (ρs : All (Rcp Λ) Δ) (F : Frame Λ) m
             → exec κ (stage zero ρs) F m
             ≡ (config zero [] (length Θ + m) , verdict↦ Δ ↦ does (rebase ρs ẑ ⟨ ++⁺ (drawn κ m Θ) F ⟩ ≟E rebase ρs ẑ′ ⟨ ++⁺ (drawn κ m Θ) F ⟩))
  exec-final κ ρs F m = trans (exec-news κ Θ _ F m) (if-same (λ b → config zero [] (length Θ + m) , verdict↦ Δ ↦ b) _)

  -- The verdict reads the slots modulo E.
  verdict-≈ : (ρs : All (Rcp Λ) Δ) (D : Frame Θ) (F : Frame Λ) {φ : Frame Δ} → All₂ _≈E_ (ρs ⟨ F ⟩*) φ
            → does (rebase ρs ẑ ⟨ ++⁺ D F ⟩ ≟E rebase ρs ẑ′ ⟨ ++⁺ D F ⟩) ≡ does (ẑ ⟨ ++⁺ D φ ⟩ ≟E ẑ′ ⟨ ++⁺ D φ ⟩)
  verdict-≈ ρs D F {φ} a = does-≈ (bind-⟨⟩ (λ p → slot ρs (∈-++⁻ Θ p)) (λ p → p) ok ẑ) (bind-⟨⟩ (λ p → slot ρs (∈-++⁻ Θ p)) (λ p → p) ok ẑ′)
    where
    at : ∀ {s} (x : s ∈ Θ ⊎ s ∈ Δ) → slot ρs x ⟨ ++⁺ D F ⟩ ≈E lookup (++⁺ D φ) ([ ∈-++⁺ˡ , ∈-++⁺ʳ Θ ]′ x)
    at (inj₁ θ) = ≈E.reflexive (trans (lookup-++⁺ˡ D F θ) (sym (lookup-++⁺ˡ D φ θ)))
    at (inj₂ i) = ≈E.trans (≈E.reflexive (trans (bind-⟨⟩≡ (lookup-++⁺ʳ D F) (lookup ρs i)) (sym (lookup-⟨⟩* ρs F i))))
                           (≈E.trans (lookup₂ a i) (≈E.reflexive (sym (lookup-++⁺ʳ D φ i))))

    ok : ∀ {s} (p : s ∈ Θ ++ Δ) → slot ρs (∈-++⁻ Θ p) ⟨ ++⁺ D F ⟩ ≈E lookup (++⁺ D φ) p
    ok p = subst (λ q → slot ρs (∈-++⁻ Θ p) ⟨ ++⁺ D F ⟩ ≈E lookup (++⁺ D φ) q) (++⁺∘++⁻ Θ p) (at (∈-++⁻ Θ p))
