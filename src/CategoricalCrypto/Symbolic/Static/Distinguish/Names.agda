{-# OPTIONS --safe --without-K #-}

-- Repeated names use the first matching table slot.  The table need not be
-- deduplicated: its unused slots merely allocate unused fresh names.

module CategoricalCrypto.Symbolic.Static.Distinguish.Names where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ; _+_; _<_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Role Σ₀ using (Rcp)
open import CategoricalCrypto.Symbolic.Static.Emitter Σ₀ E₀ using (drawn; frame; frame-entry)
open import CategoricalCrypto.Symbolic.Static.Distinguish.Tester Σ₀ E₀ using (lookup-++⁺ˡ; lookup-++⁺ʳ)

import Data.Nat.Properties as Nat

open Terms Σ₀
open EqTheory E₀

private variable
  Δ : List ⊤
  own : Name → Set
  ns : List Name

foreigns : ∀ {s} → Recipe Δ own s → List Name
foreigns* : ∀ {ss} → All (Recipe Δ own) ss → List Name
foreigns (var _) = []
foreigns (mine n _) = n ∷ []
foreigns (app _ ζs) = foreigns* ζs
foreigns* [] = []
foreigns* (ζ ∷ ζs) = foreigns ζ ++ foreigns* ζs

owned : ∀ {s} (ζ : Recipe Δ own s) → All own (foreigns ζ)
owned* : ∀ {ss} (ζs : All (Recipe Δ own) ss) → All own (foreigns* ζs)
owned (var _) = []
owned (mine _ p) = p ∷ []
owned (app _ ζs) = owned* ζs
owned* [] = []
owned* (ζ ∷ ζs) = ++⁺ (owned ζ) (owned* ζs)

Covers : ∀ {s} → List Name → Recipe Δ own s → Set
Covers* : ∀ {ss} → List Name → All (Recipe Δ own) ss → Set
Covers _ (var _) = ⊤
Covers ns (mine n _) = n ∈ ns
Covers ns (app _ ζs) = Covers* ns ζs
Covers* _ [] = ⊤
Covers* ns (ζ ∷ ζs) = Covers ns ζ × Covers* ns ζs

cover : ∀ {s} (ζ : Recipe Δ own s) → (∀ {n} → n ∈ foreigns ζ → n ∈ ns) → Covers ns ζ
cover* : ∀ {ss} (ζs : All (Recipe Δ own) ss) → (∀ {n} → n ∈ foreigns* ζs → n ∈ ns) → Covers* ns ζs
cover (var _) _ = tt
cover (mine _ _) h = h (here refl)
cover (app _ ζs) h = cover* ζs h
cover* [] _ = tt
cover* (ζ ∷ ζs) h = cover ζ (λ p → h (∈-++⁺ˡ p)) , cover* ζs (λ p → h (∈-++⁺ʳ (foreigns ζ) p))

sorts : List Name → List ⊤
sorts [] = []
sorts (_ ∷ ns) = tt ∷ sorts ns

length-sorts : ∀ ns → length (sorts ns) ≡ length ns
length-sorts [] = refl
length-sorts (_ ∷ ns) = cong Data.Nat.Base.suc (length-sorts ns)

listed : (ns : List Name) → Frame (sorts ns)
listed [] = []
listed (n ∷ ns) = name n ∷ listed ns

locate : (ns : List Name) (n : Name) → n ∈ ns → tt ∈ sorts ns
locate [] _ ()
locate (m ∷ ns) n p with n ≟ₙ m
... | yes _ = here refl
... | no neq with p
...   | here e = ⊥-elim (neq e)
...   | there p′ = there (locate ns n p′)

locate-listed : (ns : List Name) (n : Name) (p : n ∈ ns) → lookup (listed ns) (locate ns n p) ≡ name n
locate-listed [] _ ()
locate-listed (m ∷ ns) n p with n ≟ₙ m
... | yes e = cong name (sym e)
... | no neq with p
...   | here e = ⊥-elim (neq e)
...   | there p′ = locate-listed ns n p′

choose : List Name → ℕ → ℕ → Name → Name
choose [] _ _ n = n
choose (m ∷ ns) κ c n with n ≟ₙ m
... | yes _ = κ , length ns + c
... | no _ = choose ns κ c n

locate-drawn : ∀ (ns : List Name) κ c n (p : n ∈ ns)
             → lookup (drawn κ c (sorts ns)) (locate ns n p) ≡ name (choose ns κ c n)
locate-drawn [] _ _ _ ()
locate-drawn (m ∷ ns) κ c n p with n ≟ₙ m
... | yes _ = cong (λ j → name (κ , j + c)) (length-sorts ns)
... | no neq with p
...   | here e = ⊥-elim (neq e)
...   | there p′ = locate-drawn ns κ c n p′

hat : ∀ {s} (ζ : Recipe Δ own s) → Covers ns ζ → Rcp (sorts ns ++ Δ) s
hat* : ∀ {ss} (ζs : All (Recipe Δ own) ss) → Covers* ns ζs → All (Rcp (sorts ns ++ Δ)) ss
hat (var i) _ = var (∈-++⁺ʳ (sorts _) i)
hat {ns = ns} (mine n _) p = var (∈-++⁺ˡ (locate ns n p))
hat (app f ζs) ps = app f (hat* ζs ps)
hat* [] _ = []
hat* (ζ ∷ ζs) (p , ps) = hat ζ p ∷ hat* ζs ps

ren-fix : ∀ {s} (ρ : Name → Name) (t : Tm s) → (∀ {n} → n ∈ names t → ρ n ≡ n) → ren ρ t ≡ t
ren-fix* : ∀ {ss} (ρ : Name → Name) (ts : All Tm ss) → (∀ {n} → n ∈ names* ts → ρ n ≡ n) → ren* ρ ts ≡ ts
ren-fix ρ (name n) h = cong name (h (here refl))
ren-fix ρ (app f ts) h = cong (app f) (ren-fix* ρ ts h)
ren-fix* _ [] _ = refl
ren-fix* ρ (t ∷ ts) h = cong₂ _∷_ (ren-fix ρ t (λ p → h (∈-++⁺ˡ p))) (ren-fix* ρ ts (λ p → h (∈-++⁺ʳ (names t) p)))

choose-fix : ∀ ns κ c n → (∀ {m} → m ∈ ns → m ≢ n) → choose ns κ c n ≡ n
choose-fix [] _ _ _ _ = refl
choose-fix (m ∷ ns) κ c n h with n ≟ₙ m
... | yes e = ⊥-elim (h (here refl) (sym e))
... | no _ = choose-fix ns κ c n (λ p → h (there p))

forward : ∀ {s} (ns : List Name) (ζ : Recipe Δ own s) (p : Covers ns ζ) κ c (φ : Frame Δ)
        → (∀ {n} → n ∈ names* φ → choose ns κ c n ≡ n)
        → ren (choose ns κ c) (ζ ⟨ φ ⟩) ≡ hat ζ p ⟨ ++⁺ (drawn κ c (sorts ns)) φ ⟩
forward* : ∀ {ss} (ns : List Name) (ζs : All (Recipe Δ own) ss) (ps : Covers* ns ζs) κ c (φ : Frame Δ)
         → (∀ {n} → n ∈ names* φ → choose ns κ c n ≡ n)
         → ren* (choose ns κ c) (ζs ⟨ φ ⟩*) ≡ hat* ζs ps ⟨ ++⁺ (drawn κ c (sorts ns)) φ ⟩*
forward ns (var i) _ κ c φ h =
  trans (ren-fix _ (lookup φ i) (λ p → h (lookup-names φ i p))) (sym (lookup-++⁺ʳ (drawn κ c (sorts ns)) φ i))
  where
  lookup-names : ∀ {s} (φ : Frame Δ) (i : s ∈ Δ) {n : Name} → n ∈ names (lookup φ i) → n ∈ names* φ
  lookup-names (t ∷ _) (here refl) p = ∈-++⁺ˡ p
  lookup-names (t ∷ φ) (there i) p = ∈-++⁺ʳ (names t) (lookup-names φ i p)
forward {s = tt} ns (mine n _) p κ c φ _ =
  sym (trans (lookup-++⁺ˡ (drawn κ c (sorts ns)) φ (locate ns n p)) (locate-drawn ns κ c n p))
forward ns (app f ζs) ps κ c φ h = cong (app f) (forward* ns ζs ps κ c φ h)
forward* _ [] _ _ _ _ _ = refl
forward* ns (ζ ∷ ζs) (p , ps) κ c φ h = cong₂ _∷_ (forward ns ζ p κ c φ h) (forward* ns ζs ps κ c φ h)

code : (ns : List Name) → ℕ → tt ∈ sorts ns → ℕ
code (_ ∷ ns) c (here refl) = length ns + c
code (_ ∷ ns) c (there i) = code ns c i

code< : ∀ ns c (i : tt ∈ sorts ns) → code ns c i < length ns + c
code< (_ ∷ _) _ (here refl) = Nat.≤-refl
code< (_ ∷ ns) c (there i) = Nat.m<n⇒m<1+n (code< ns c i)

original : (ns : List Name) → tt ∈ sorts ns → Name
original (n ∷ _) (here refl) = n
original (_ ∷ ns) (there i) = original ns i

back : List Name → ℕ → ℕ → Name
back [] _ _ = 0 , 0
back (n ∷ ns) c j with j Nat.≟ (length ns + c)
... | yes _ = n
... | no _ = back ns c j

back-code : ∀ ns c (i : tt ∈ sorts ns) → back ns c (code ns c i) ≡ original ns i
back-code (n ∷ ns) c (here refl) with (length ns + c) Nat.≟ (length ns + c)
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)
back-code (n ∷ ns) c (there i) with code ns c i Nat.≟ (length ns + c)
... | yes e = ⊥-elim (Nat.<⇒≢ (code< ns c i) e)
... | no _ = back-code ns c i

restore : List Name → ℕ → ℕ → ℕ → ℕ → Name → Name
restore ns κ κᵀ κᵉ c (a , j) with a Nat.≟ κᵉ
... | yes _ = κ , j
... | no _ with a Nat.≟ κᵀ
...   | yes _ = back ns c j
...   | no _ = a , j

restore-emitter : ∀ ns κ κᵀ κᵉ c j → restore ns κ κᵀ κᵉ c (κᵉ , j) ≡ (κ , j)
restore-emitter ns κ κᵀ κᵉ c j with κᵉ Nat.≟ κᵉ
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

restore-tester : ∀ ns κ κᵀ κᵉ c j → κᵀ ≢ κᵉ → restore ns κ κᵀ κᵉ c (κᵀ , j) ≡ back ns c j
restore-tester ns κ κᵀ κᵉ c j neq with κᵀ Nat.≟ κᵉ
... | yes e = ⊥-elim (neq e)
... | no _ with κᵀ Nat.≟ κᵀ
...   | yes _ = refl
...   | no neq′ = ⊥-elim (neq′ refl)

lookup-drawn : ∀ ns κ c (i : tt ∈ sorts ns) → lookup (drawn κ c (sorts ns)) i ≡ name (κ , code ns c i)
lookup-drawn (_ ∷ ns) κ c (here refl) = cong (λ j → name (κ , j + c)) (length-sorts ns)
lookup-drawn (_ ∷ ns) κ c (there i) = lookup-drawn ns κ c i

lookup-listed : ∀ ns (i : tt ∈ sorts ns) → lookup (listed ns) i ≡ name (original ns i)
lookup-listed (_ ∷ _) (here refl) = refl
lookup-listed (_ ∷ ns) (there i) = lookup-listed ns i

restore-entry : ∀ ns κ κᵀ κᵉ c (i : tt ∈ sorts ns) → κᵀ ≢ κᵉ
              → ren (restore ns κ κᵀ κᵉ c) (lookup (drawn κᵀ c (sorts ns)) i) ≡ lookup (listed ns) i
restore-entry ns κ κᵀ κᵉ c i neq = trans (cong (ren _) (lookup-drawn ns κᵀ c i))
  (trans (cong name (trans (restore-tester ns κ κᵀ κᵉ c _ neq) (back-code ns c i))) (sym (lookup-listed ns i)))

backward : ∀ {s} (ns : List Name) (ζ : Recipe Δ own s) (p : Covers ns ζ) κ κᵀ κᵉ c (φ ψ : Frame Δ)
         → κᵀ ≢ κᵉ → (∀ (i : tt ∈ Δ) → ren (restore ns κ κᵀ κᵉ c) (lookup ψ i) ≈E lookup φ i)
         → ren (restore ns κ κᵀ κᵉ c) (hat ζ p ⟨ ++⁺ (drawn κᵀ c (sorts ns)) ψ ⟩) ≈E ζ ⟨ φ ⟩
backward* : ∀ {ss} (ns : List Name) (ζs : All (Recipe Δ own) ss) (ps : Covers* ns ζs) κ κᵀ κᵉ c (φ ψ : Frame Δ)
          → κᵀ ≢ κᵉ → (∀ (i : tt ∈ Δ) → ren (restore ns κ κᵀ κᵉ c) (lookup ψ i) ≈E lookup φ i)
          → All₂ _≈E_ (ren* (restore ns κ κᵀ κᵉ c) (hat* ζs ps ⟨ ++⁺ (drawn κᵀ c (sorts ns)) ψ ⟩*)) (ζs ⟨ φ ⟩*)
backward {s = tt} ns (var i) _ κ κᵀ κᵉ c φ ψ _ h =
  trans (cong (λ t → nf (ren (restore ns κ κᵀ κᵉ c) t)) (lookup-++⁺ʳ (drawn κᵀ c (sorts ns)) ψ i)) (h i)
backward {s = tt} ns (mine n _) p κ κᵀ κᵉ c φ ψ neq _ = cong nf
  (trans (cong (ren (restore ns κ κᵀ κᵉ c)) (lookup-++⁺ˡ (drawn κᵀ c (sorts ns)) ψ (locate ns n p)))
    (trans (restore-entry ns κ κᵀ κᵉ c (locate ns n p) neq) (locate-listed ns n p)))
backward ns (app f ζs) ps κ κᵀ κᵉ c φ ψ neq h = app-cong f (backward* ns ζs ps κ κᵀ κᵉ c φ ψ neq h)
backward* _ [] _ _ _ _ _ _ _ _ _ = []
backward* ns (ζ ∷ ζs) (p , ps) κ κᵀ κᵉ c φ ψ neq h = backward ns ζ p κ κᵀ κᵉ c φ ψ neq h ∷ backward* ns ζs ps κ κᵀ κᵉ c φ ψ neq h

ren-rcp : ∀ {s} (ρ : Name → Name) (ζ : Rcp Δ s) (φ ψ : Frame Δ)
        → (∀ {s} (i : s ∈ Δ) → ren ρ (lookup φ i) ≈E lookup ψ i) → ren ρ (ζ ⟨ φ ⟩) ≈E ζ ⟨ ψ ⟩
ren-rcp* : ∀ {ss} (ρ : Name → Name) (ζs : All (Rcp Δ) ss) (φ ψ : Frame Δ)
         → (∀ {s} (i : s ∈ Δ) → ren ρ (lookup φ i) ≈E lookup ψ i) → All₂ _≈E_ (ren* ρ (ζs ⟨ φ ⟩*)) (ζs ⟨ ψ ⟩*)
ren-rcp _ (var i) _ _ h = h i
ren-rcp _ (mine _ ()) _ _ _
ren-rcp ρ (app f ζs) φ ψ h = app-cong f (ren-rcp* ρ ζs φ ψ h)
ren-rcp* _ [] _ _ _ = []
ren-rcp* ρ (ζ ∷ ζs) φ ψ h = ren-rcp ρ ζ φ ψ h ∷ ren-rcp* ρ ζs φ ψ h

frame-restore : ∀ ns κ κᵀ κᵉ c (Ν : List ⊤) (ζs : All (Rcp Ν) Δ) (i : tt ∈ Δ)
              → ren (restore ns κ κᵀ κᵉ c) (lookup (frame κᵉ Ν ζs) i) ≈E lookup (frame κ Ν ζs) i
frame-restore ns κ κᵀ κᵉ c Ν ζs i =
  trans (cong (λ t → nf (ren ρ t)) (frame-entry κᵉ Ν ζs i))
    (trans (ren-cong ρ {t = canon rawᵉ} {u = rawᵉ} (canon-≈E rawᵉ))
      (trans (ren-rcp ρ (lookup ζs i) (drawn κᵉ 0 Ν) (drawn κ 0 Ν) at)
        (trans (sym (canon-≈E raw)) (cong nf (sym (frame-entry κ Ν ζs i))))))
  where
  ρ = restore ns κ κᵀ κᵉ c
  rawᵉ = lookup ζs i ⟨ drawn κᵉ 0 Ν ⟩
  raw = lookup ζs i ⟨ drawn κ 0 Ν ⟩

  at : ∀ {s} (j : s ∈ Ν) → ren ρ (lookup (drawn κᵉ 0 Ν) j) ≈E lookup (drawn κ 0 Ν) j
  at = go Ν
    where
    go : ∀ (Ν : List ⊤) {s} (j : s ∈ Ν) → ren ρ (lookup (drawn κᵉ 0 Ν) j) ≈E lookup (drawn κ 0 Ν) j
    go (_ ∷ Ν) (here refl) = ≈E.reflexive (cong name (restore-emitter ns κ κᵀ κᵉ c (length Ν + 0)))
    go (_ ∷ Ν) (there j) = go Ν j
