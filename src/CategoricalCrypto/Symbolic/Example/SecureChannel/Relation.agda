{-# OPTIONS --safe --without-K --guardedness #-}

open import Data.Nat.Base using (ℕ)

module CategoricalCrypto.Symbolic.Example.SecureChannel.Relation (κ : ℕ) where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Product
open import Data.Sum.Base
open import Data.Unit.Base
open import Function.Bundles using (mk⇔)
open import Relation.Nullary.Decidable using (does-⇔)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no; does)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Term.PairEnc.Cipher
open import CategoricalCrypto.Symbolic.Fine Σ₀ using (Var)
open import CategoricalCrypto.Symbolic.Role Σ₀
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀ using (runᴿ)
open import CategoricalCrypto.Symbolic.RunFollowing.PairEnc κ
open import CategoricalCrypto.Symbolic.RunFollowing.Role κ using (inputs; outputs)
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol hiding (drop)

open Terms Σ₀
open EqTheory E₀
open Run E₀ hiding (after)

role : Bool → Role (Var void) ports
role b = channel (not b) false

InputLetters OutputLetters : F.Letters
InputLetters = inputs (Var void) ports
OutputLetters = outputs (Var void) ports

data State : World → Set where
  idle : State before
  waiting : ∀ {m} → State (after m)
  stopped : ∀ w → ℕ → State w

current-cipher : Bool → Plaintext → Msg
current-cipher b m = expand b (after m) (name key)

current-cipher-real : ∀ m → current-cipher true m ≡ cipher (message m) key coins
current-cipher-real m = [≔]-here

current-cipher-dummy : ∀ m → current-cipher false m ≡ cipher zero-message key coins
current-cipher-dummy m = [≔]-here

current-cipher-normal : ∀ b m → nf (current-cipher b m) ≡ current-cipher b m
current-cipher-normal b m = expand-canon b (after m) (name key)

known-message : ∀ b m → expand b (after m) (message m) ≡ message m
known-message b m = promote-expand b accept (message m) (fresh-key m)

error-term : Msg
error-term = app (cst 2) []

error-legal : ∀ w → Legal w error-term
error-legal before ()
error-legal (after _) = tt

error-expand : ∀ b w → expand b w error-term ≡ error-term
error-expand b before = refl
error-expand true (after _) = refl
error-expand false (after _) = refl

project-state : ∀ b w → State w → Config 3 Γ
project-state b .before idle = init (role b)
project-state b .(after m) (waiting {m}) = config pending (name key ∷ current-cipher b m ∷ message m ∷ []) 2
project-state b w (stopped _ j) = config finished [] j

private
  failed : ∀ w j → F.Turn State (F.Related OutputLetters) w
  failed w j = F.turn w stay (stopped w j) (inj₂ (inj₂ error-term , error-legal w))

  delivered : ∀ m → F.Turn State (F.Related OutputLetters) (after m)
  delivered m = F.turn (after m) stay (stopped (after m) 2) (inj₂ (inj₂ (message m) , tt))

  accepted : ∀ {P : Set} (d : Dec P) → does d ≡ true → P
  accepted (yes p) _ = p
  accepted (no _) ()

  response : ∀ w → State w × F.Related InputLetters w → F.Turn State (F.Related OutputLetters) w
  response .before (idle , inj₁ (() , _))
  response .before (idle , inj₂ (inj₁ _ , _)) = failed before 0
  response .before (idle , inj₂ (inj₂ t , p)) = F.turn (after m) accept waiting (inj₂ (inj₁ (name key) , tt))
    where m = select (letter t p)
  response .(after m) (waiting {m} , inj₁ (() , _))
  response .(after m) (waiting {m} , inj₂ (inj₁ t , _)) with does (t ≟E name key)
  ... | true = delivered m
  ... | false = failed (after m) 2
  response .(after m) (waiting {m} , inj₂ (inj₂ _ , _)) = failed (after m) 2
  response w (stopped _ j , inj₁ (() , _))
  response w (stopped _ j , inj₂ _) = failed w j

  projected : ∀ b w (t : F.Turn State (F.Related OutputLetters) w)
    → Config 3 Γ × (Alphabet neg (Var void) ⊎ Alphabet pos ports)
  projected b w t = project-state b (F.world t) (F.state t) , F.project OutputLetters b (F.world t) (F.output t)

  decrypt-delivers : ∀ m t → t ≈E current-cipher true m
    → nf (app dec (t ∷ name key ∷ [])) ≡ message m
  decrypt-delivers m t e = trans
    (app-cong dec {ts = t ∷ name key ∷ []} {us = cipher (message m) key coins ∷ name key ∷ []}
      (trans e (cong nf (current-cipher-real m)) ∷ refl ∷ []))
    (trans (⟶-nf {t = app dec (cipher (message m) key coins ∷ name key ∷ [])}
      (root (dec-enc {x = message m} {k = name key} {r = name coins}))) (normal m))

  pending-result : Bool → Plaintext → Msg → Bool → Config 3 Γ × (Alphabet neg (Var void) ⊎ Alphabet pos ports)
  pending-result b m t decision = if decision
    then config finished [] 2 , inj₂ (inj₂ (if b then nf (app dec (t ∷ name key ∷ [])) else nf (message m)))
    else config finished [] 2 , inj₂ (inj₂ error-term)

  concrete-pending : ∀ b m t → Data.Product.map₂ (encode (Var void) ports)
    (step κ (role b) (project-state b (after m) waiting) (here refl ↦ t))
    ≡ pending-result b m t (Relation.Nullary.does (t ≟E current-cipher b m))
  concrete-pending true m t with Relation.Nullary.does (t ≟E current-cipher true m)
  ... | true = refl
  ... | false = refl
  concrete-pending false m t with Relation.Nullary.does (t ≟E current-cipher false m)
  ... | true = refl
  ... | false = refl

  abstract-pending : ∀ b m t p → projected b (after m) (response (after m) (waiting , inj₂ (inj₁ t , p)))
    ≡ pending-result b m (expand b (after m) t) (Relation.Nullary.does (t ≟E name key))
  abstract-pending true m t p with does (t ≟E name key) in e
  ... | true rewrite known-message true m | decrypt-delivers m (expand true (after m) t)
    (expand-cong true (after m) {t = t} {u = name key} (accepted (t ≟E name key) e)) = refl
  ... | false rewrite error-expand true (after m) = refl
  abstract-pending false m t p with does (t ≟E name key)
  ... | true rewrite known-message false m | normal m = refl
  ... | false rewrite error-expand false (after m) = refl

  pending-law : ∀ b m t p → projected b (after m) (response (after m) (waiting , inj₂ (inj₁ t , p)))
    ≡ Data.Product.map₂ (encode (Var void) ports)
      (step κ (role b) (project-state b (after m) waiting) (here refl ↦ expand b (after m) t))
  pending-law b m t p = trans (abstract-pending b m t p) (trans
    (cong (pending-result b m (expand b (after m) t)) (sym
      (does-⇔ (mk⇔ (expand-equation b (after m)) (expand-cong b (after m)))
        (expand b (after m) t ≟E current-cipher b m) (t ≟E name key))))
    (sym (concrete-pending b m (expand b (after m) t))))

  response-law : ∀ b w (s : State w) x → projected b w (response w (s , x))
    ≡ Data.Product.map₂ (encode (Var void) ports)
      (step κ (role b) (project-state b w s) (decode (Var void) ports (F.project InputLetters b w x)))
  response-law true before idle (inj₁ (() , _))
  response-law false before idle (inj₁ (() , _))
  response-law true before idle (inj₂ (inj₁ t , p)) = refl
  response-law false before idle (inj₂ (inj₁ t , p)) = refl
  response-law true before idle (inj₂ (inj₂ t , p)) rewrite current-cipher-real (select (letter t p)) = refl
  response-law false before idle (inj₂ (inj₂ t , p)) rewrite current-cipher-dummy (select (letter t p)) = refl
  response-law true (after m) waiting (inj₁ (() , _))
  response-law false (after m) waiting (inj₁ (() , _))
  response-law true (after m) waiting (inj₂ (inj₁ t , p)) = pending-law true m t p
  response-law false (after m) waiting (inj₂ (inj₁ t , p)) = pending-law false m t p
  response-law true (after m) waiting (inj₂ (inj₂ t , p)) rewrite error-expand true (after m) = refl
  response-law false (after m) waiting (inj₂ (inj₂ t , p)) rewrite error-expand false (after m) = refl
  response-law true w (stopped _ j) (inj₁ (() , _))
  response-law false w (stopped _ j) (inj₁ (() , _))
  response-law true w (stopped _ j) (inj₂ (inj₁ t , p)) rewrite error-expand true w = refl
  response-law true w (stopped _ j) (inj₂ (inj₂ t , p)) rewrite error-expand true w = refl
  response-law false w (stopped _ j) (inj₂ (inj₁ t , p)) rewrite error-expand false w = refl
  response-law false w (stopped _ j) (inj₂ (inj₂ t , p)) rewrite error-expand false w = refl

channel-following : F.Following InputLetters OutputLetters (λ b → runᴿ κ (role b))
channel-following = record
  { State = State ; project-state = project-state
  ; point = returnₚ idle ; point-law = λ b → >>=ₚ-identityˡ _ _
  ; act = λ w sx → returnₚ (response w sx)
  ; act-law = λ b w s x → >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡ (response-law b w s x) }
