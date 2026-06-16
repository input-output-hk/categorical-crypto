{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Shared comparison arithmetic for the inversion-count development:
-- the decidable-bracket congruence `dec-cong` and the Boolean `<?ℕ`
-- comparison toolkit (`cmpB`), used by both `InversionsDichotomy`
-- (the descent dichotomy) and `InversionsRec` (the Lehmer recursion).
------------------------------------------------------------------------

module Categories.PermuteCoherence.InversionsArith where

open import Data.Nat.Base using (ℕ; suc; _<_; s≤s⁻¹; s<s; s<s⁻¹)
open import Data.Nat.Properties using () renaming (_<?_ to _<?ℕ_)
open import Data.Fin.Base using (Fin) renaming (suc to fsuc)
open import Data.Fin.Properties using () renaming (_<?_ to _<?F_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable
  using (⌊_⌋; isYes≗does; dec-true; dec-false; toWitness)
open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; subst)

------------------------------------------------------------------------
-- 1. Decidable-bracket congruence under logical equivalence.

dec-cong : {A B : Set} (a? : Dec A) (b? : Dec B)
         → (A → B) → (B → A) → ⌊ a? ⌋ ≡ ⌊ b? ⌋
dec-cong (yes _) (yes _) _ _ = refl
dec-cong (no  _) (no  _) _ _ = refl
dec-cong (yes a) (no ¬b) f _ = ⊥-elim (¬b (f a))
dec-cong (no ¬a) (yes b) _ g = ⊥-elim (¬a (g b))

------------------------------------------------------------------------
-- 2. The Boolean ℕ-comparison and its reflection.

cmpB : ℕ → ℕ → Bool
cmpB a b = ⌊ a <?ℕ b ⌋

cmpB-true : {a b : ℕ} → a < b → cmpB a b ≡ true
cmpB-true {a} {b} a<b = trans (isYes≗does (a <?ℕ b)) (dec-true (a <?ℕ b) a<b)

cmpB-false : {a b : ℕ} → ¬ (a < b) → cmpB a b ≡ false
cmpB-false {a} {b} ¬a<b = trans (isYes≗does (a <?ℕ b)) (dec-false (a <?ℕ b) ¬a<b)

-- `cmpB` depends only on the underlying `<` proposition.
cmpB-iff : {a b c d : ℕ} → (a < b → c < d) → (c < d → a < b)
         → cmpB a b ≡ cmpB c d
cmpB-iff {a} {b} {c} {d} fwd bwd = dec-cong (a <?ℕ b) (c <?ℕ d) fwd bwd

-- Shift both arguments by one.
cmpB-suc : (a b : ℕ) → cmpB (suc a) (suc b) ≡ cmpB a b
cmpB-suc a b = cmpB-iff s≤s⁻¹ s<s

-- Reverse bridge: a `true` comparison yields the `<` witness.
cmpB-true⁻ : {a b : ℕ} → cmpB a b ≡ true → a < b
cmpB-true⁻ {a} {b} eq = toWitness {a? = a <?ℕ b} (subst T (sym eq) tt)

------------------------------------------------------------------------
-- 3. The `Fin`-level suc-shift of the comparison bracket.

suc-<-bracket : {N : ℕ} (a c : Fin N) → ⌊ fsuc a <?F fsuc c ⌋ ≡ ⌊ a <?F c ⌋
suc-<-bracket a c = dec-cong (fsuc a <?F fsuc c) (a <?F c) s<s⁻¹ s<s
