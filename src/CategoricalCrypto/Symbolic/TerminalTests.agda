{-# OPTIONS --safe --without-K #-}

module CategoricalCrypto.Symbolic.TerminalTests where

open import Categories.FreeMonoidal
open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base
open import Data.List.Base
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Maybe.Base
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality

open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Role Σ₀

open FreeMonoidalHelper Mon Atom
open Terms Σ₀
open Run E₀

forwarding : Role (Var verdict) (Var verdict)
forwarding = record
  { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) b → emit zero [] (there (here refl)) b
      zero (there (here refl)) _ → emit zero [] (there (here refl)) false }

forwarding-ground-guarded : GroundGuarded forwarding
forwarding-ground-guarded = record
  { ground-control = zero
  ; ground-at-control = λ { (here refl) _ → ground-jump tt ; (there (here refl)) _ → ground-jump tt }
  ; ground-guards = λ { zero (here refl) _ → emit ; zero (there (here refl)) _ → emit } }

forwarding-still-responds : proj₂ (step 0 forwarding (init forwarding) (here refl ↦ true))
  ≡ there (here refl) ↦ true
forwarding-still-responds = refl

private
  flag-of : Emission (Outs (Var verdict) (Var verdict)) → Bool
  flag-of (here refl ↦ _) = false
  flag-of (there (here refl) ↦ b) = b
  flag-of (there (there ()) ↦ _)

-- GroundGuarded permits input-dependent replies; no fixed terminal output does.
forwarding-not-terminal : (err : TerminalOutput (Outs (Var verdict) (Var verdict)))
  → Terminal forwarding err → ⊥
forwarding-not-terminal err record { terminal = suc () }
forwarding-not-terminal err record { terminal = zero ; boundary = bd } =
  different (cong flag-of (trans true-output (sym false-output)))
  where
  true-output : (there (here refl) ↦ true) ≡ terminal-emission err
  true-output = proj₁ (proj₂ (terminal-jump-exec (bd (here refl) true) 0 [] 0))
  false-output : (there (here refl) ↦ false) ≡ terminal-emission err
  false-output = proj₁ (proj₂ (terminal-jump-exec (bd (here refl) false) 0 [] 0))
  different : true ≡ false → ⊥
  different ()

verdict-once : Role (Var verdict) (Var verdict)
verdict-once = record
  { n = 2 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) b → emit (suc zero) [] (there (here refl)) b
      zero (there (here refl)) _ → emit (suc zero) [] (there (here refl)) true
      (suc zero) (here refl) _ → emit (suc zero) [] (there (here refl)) false
      (suc zero) (there (here refl)) _ → emit (suc zero) [] (there (here refl)) false }

verdict-error : TerminalOutput (Outs (Var verdict) (Var verdict))
verdict-error = terminal-output flag (there (here refl)) false

verdict-terminal : Terminal verdict-once verdict-error
verdict-terminal = record
  { terminal = suc zero
  ; boundary = λ { (here refl) _ → terminal-jump ; (there (here refl)) _ → terminal-jump }
  ; failures = λ { zero (here refl) _ → emit ; zero (there (here refl)) _ → emit
                  ; (suc zero) (here refl) _ → emit ; (suc zero) (there (here refl)) _ → emit } }

verdict-emitted-once : (suffix : List (Input (Var verdict) (Var verdict)))
  → run-terminal 7 verdict-once verdict-terminal (init verdict-once) ((here refl ↦ true) ∷ suffix)
    ≡ (config (suc zero) [] 0 , (there (here refl) ↦ true) ∷ [])
verdict-emitted-once suffix rewrite terminal-no-further-behavior 7 verdict-once verdict-terminal
  (config (suc zero) [] 0) suffix refl = refl

post-verdict-no-activation : (i : Input (Var verdict) (Var verdict))
  → step-terminal 7 verdict-once verdict-terminal (config (suc zero) [] 0) i ≡ nothing
post-verdict-no-activation i = step-terminal-stopped 7 verdict-once verdict-terminal (config (suc zero) [] 0) i refl

-- The total runner remains distinct: it still executes the boundary row.
total-boundary-still-emits : proj₂ (step 7 verdict-once (config (suc zero) [] 0) (here refl ↦ true))
  ≡ there (here refl) ↦ false
total-boundary-still-emits = refl

wire : ObjTerm
wire = Var (port tt tt)

guarded-verdict : Role wire (Var verdict)
guarded-verdict = record
  { n = 2 ; Γ = λ _ → [] ; start = zero ; fresh = refl
  ; react = λ where
      zero (here refl) _ → test (var (here refl)) (app (cst 0) [])
        (emit (suc zero) [] (there (here refl)) true) (emit (suc zero) [] (there (here refl)) false)
      zero (there (here refl)) _ → emit (suc zero) [] (there (here refl)) false
      (suc zero) (here refl) _ → emit (suc zero) [] (there (here refl)) false
      (suc zero) (there (here refl)) _ → emit (suc zero) [] (there (here refl)) false }

guard-error : TerminalOutput (Outs wire (Var verdict))
guard-error = terminal-output flag (there (here refl)) false

guard-terminal : Terminal guarded-verdict guard-error
guard-terminal = record
  { terminal = suc zero
  ; boundary = λ { (here refl) _ → terminal-jump ; (there (here refl)) _ → terminal-jump }
  ; failures = λ { zero (here refl) _ → test emit terminal-jump ; zero (there (here refl)) _ → emit
                  ; (suc zero) (here refl) _ → emit ; (suc zero) (there (here refl)) _ → emit } }

failed-guard-stops : (suffix : List (Input wire (Var verdict)))
  → run-terminal 7 guarded-verdict guard-terminal (init guarded-verdict)
      ((here refl ↦ app (cst 1) []) ∷ suffix)
    ≡ (config (suc zero) [] 0 , (there (here refl) ↦ false) ∷ [])
failed-guard-stops suffix rewrite terminal-no-further-behavior 7 guarded-verdict guard-terminal
  (config (suc zero) [] 0) suffix refl = refl

successful-guard-verdict : step-terminal 7 guarded-verdict guard-terminal (init guarded-verdict)
  (here refl ↦ app (cst 0) []) ≡ just (config (suc zero) [] 0 , there (here refl) ↦ true)
successful-guard-verdict = refl
