{-# OPTIONS --safe --without-K --guardedness #-}

module CategoricalCrypto.Symbolic.Example.SecureChannel.Negative where

open import Categories.Category
open import Categories.Category.Monoidal.Bundle
open import Data.Bool.Base
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using ()
open import Data.List.Base
open import Data.List.Relation.Unary.All hiding (reduce)
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Sum.Base hiding (reduce)
open import Data.Unit.Base
open import Function.Bundles using (Equivalence)
open import Function.Definitions using (Injective)
open import Level using (0ℓ; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Advantage using (returnₚ-bool-injective)
open import ProbabilisticLogic.Dp.Reasoning
open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Machines.Pointwise
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀
open import CategoricalCrypto.Symbolic.Role Σ₀
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀
open import CategoricalCrypto.Symbolic.Setup Σ₀ E₀
open import CategoricalCrypto.Symbolic.Example.SecureChannel.Protocol
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal
import CategoricalCrypto.Machines.Collapse as Col
import CategoricalCrypto.UC.Seam.Plug as Plug

private module G = MonoidalCategory 𝔾ᵒ
open Terms Σ₀
open Run E₀
open Category.HomReasoning FreeMonoidal

chosen : Msg
chosen = app (cst 11) []

Γᵀ : Fin.Fin 3 → List ⊤
Γᵀ _ = []

private
  answer : ∀ {Δ} → Bool → React 3 Γᵀ (Outs ports (Var verdict)) Δ
  answer b = emit finished [] (there (there (here refl))) b

  request : ∀ {Δ} → React 3 Γᵀ (Outs ports (Var verdict)) Δ
  request = emit pending [] (there (here refl)) (closed-payload (msg tt) (app (cst 11) []))

  compare : React 3 Γᵀ (Outs ports (Var verdict)) (tt ∷ [])
  compare = test (var (here refl)) (app (cst 11) []) (answer true) (answer false)

tester-role : Role ports (Var verdict)
tester-role = record
  { n = 3 ; Γ = Γᵀ ; start = Fin.zero ; fresh = refl
  ; react = λ where
      Fin.zero (here refl) _ → answer false
      Fin.zero (there (here refl)) _ → answer false
      Fin.zero (there (there (here refl))) _ → request
      Fin.zero (there (there (there ()))) _
      (Fin.suc Fin.zero) (here refl) _ → compare
      (Fin.suc Fin.zero) (there (here refl)) _ → answer false
      (Fin.suc Fin.zero) (there (there (here refl))) _ → answer false
      (Fin.suc Fin.zero) (there (there (there ()))) _
      (Fin.suc (Fin.suc Fin.zero)) (here refl) _ → answer false
      (Fin.suc (Fin.suc Fin.zero)) (there (here refl)) _ → answer false
      (Fin.suc (Fin.suc Fin.zero)) (there (there (here refl))) _ → answer false
      (Fin.suc (Fin.suc Fin.zero)) (there (there (there ()))) _ }

tester : HomTerm ports (Var verdict)
tester = var ((tt , tt) , tt , tester-role)

private
  cipher : Bool → ℕ → Msg
  cipher dummy κ = app enc ((if dummy then app (cst 0) [] else chosen) ∷ name (κ , 0) ∷ name (κ , 1) ∷ [])
  exposed : Bool → Bool → ℕ → Msg
  exposed dummy leak κ = if leak then chosen else cipher dummy κ
  ready : Bool → ℕ → Config 3 Γ
  ready dummy κ = config pending (name (κ , 0) ∷ cipher dummy κ ∷ chosen ∷ []) 2

  channel-request : ∀ dummy leak κ → step κ (channel dummy leak) (init (channel dummy leak)) (there (here refl) ↦ chosen)
    ≡ (ready dummy κ , here refl ↦ exposed dummy leak κ)
  channel-request false false κ = refl
  channel-request false true κ = refl
  channel-request true false κ = refl
  channel-request true true κ = refl

  tester-response : ∀ dummy leak κᵀ κ → step κᵀ tester-role (config pending [] 0) (here refl ↦ exposed dummy leak κ)
    ≡ (config finished [] 0 , there (there (here refl)) ↦ leak)
  tester-response false false κᵀ κ = refl
  tester-response false true κᵀ κ = refl
  tester-response true false κᵀ κ = refl
  tester-response true true κᵀ κ = refl

  tree-∘ : ∀ {X Y Y′ Z} (q : Y ≡ Y′) (g : Y G.⇒ Z) (f : X G.⇒ Y)
    → subst₂ G._⇒_ q refl g G.∘ subst₂ G._⇒_ refl q f ≡ g G.∘ f
  tree-∘ refl _ _ = refl

module Pass (dummy leak : Bool) (κᵀ κ : ℕ) where
  K = runᴿ κᵀ tester-role
  u = runᴿ κ (channel dummy leak)
  module P = Plug.Plugged ⟦ ports ⟧ᴵ K u

  private
    toLoop : Config 3 Γ → Config 3 Γᵀ × Emission (Outs ports (Var verdict))
      → MC.obj P.Sᴷ × ((Data.Empty.⊥ ⊎ Bool) ⊎ (Alphabet neg ports ⊎ Alphabet pos ports))
    toLoop es r = (proj₁ r , es) , Col.outᵍ (encode ports (Var verdict) (proj₂ r))

    tester-pass : ∀ cfg es m {r} → step κᵀ tester-role cfg (decode ports (Var verdict) m) ≡ r
      → (MC.step K (cfg , m) >>=ₚ λ r → returnₚ ((proj₁ r , es) , Col.outᵍ (proj₂ r))) ≈ₚ returnₚ (toLoop es r)
    tester-pass cfg es m e = >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡ (cong (toLoop es) e)

    channel-pass : P.kᴷ ((config pending [] 0 , init (channel dummy leak)) , inj₂ (inj₁ (inj₂ chosen)))
      ≈ₚ returnₚ ((config pending [] 0 , ready dummy κ) , inj₂ (inj₂ (inj₁ (exposed dummy leak κ))))
    channel-pass = >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡
      (cong (λ r → (config pending [] 0 , proj₁ r) , Col.outᶠ (encode (Var void) ports (proj₂ r))) (channel-request dummy leak κ))

  obs : Obs (procᵒ K G.∘ procᵒ u) ≈ₚ returnₚ leak
  obs = runᴹ-resp-≈ᴹ {Ωᴵ} (unprocᵒ-∘ {unitᴵ} {⟦ ports ⟧ᴵ} {Ωᴵ} K u) (ask tt out)
    ⟨≈⟩ P.collapse ⟨≈⟩ P.observe
    ⟨≈⟩ bindˣ (P.point-red ⟨≈⟩ >>=ₚ-identityˡ _ _ ⟨≈⟩ >>=ₚ-identityˡ _ _)
    ⟨≈⟩ >>=ₚ-identityˡ _ _
    ⟨≈⟩ bindˣ (tester-pass (init tester-role) (init (channel dummy leak)) (inj₂ tt) refl)
    ⟨≈⟩ >>=ₚ-identityˡ _ _
    ⟨≈⟩ bindˣ (P.loop-pass (config pending [] 0 , init (channel dummy leak)) (inj₁ (inj₂ chosen))
      (config pending [] 0 , ready dummy κ) (inj₂ (inj₂ (inj₁ (exposed dummy leak κ)))) channel-pass
      ⟨≈⟩ P.loop-pass (config pending [] 0 , ready dummy κ) (inj₂ (inj₁ (exposed dummy leak κ)))
        (config finished [] 0 , ready dummy κ) (inj₁ (inj₂ leak))
        (tester-pass (config pending [] 0) (ready dummy κ) (inj₁ (inj₁ (exposed dummy leak κ))) (tester-response dummy leak κᵀ κ)))
    ⟨≈⟩ P.cont-red ((config finished [] 0 , ready dummy κ) , inj₁ (inj₂ leak))

circuit : Bool → Bool → HomTerm (Var void) (Var verdict)
circuit dummy leak = tester ∘ var (tt , (tt , tt) , channel dummy leak)

run : ∀ dummy leak (ι : Occ (circuit dummy leak) → ℕ) → Obs ⟦ circuit dummy leak ⟧[ ι ] ≈ₚ returnₚ leak
run dummy leak ι = ≡⇒≈ₚ (cong Obs (tree-∘ (sym (tree≡ ports (tt , tt))) _ _))
  ⟨≈⟩ Pass.obs dummy leak (ι (inj₁ tt)) (ι (inj₂ tt))

private
  reduce : ∀ (f : HomTerm (Var void) ports) → ((tester ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐ ≈Term tester ∘ f
  reduce f = begin
    ((tester ∘ λ⇒) ∘ id ⊗₁ f) ∘ λ⇐  ≈⟨ assoc ○ assoc ⟩
    tester ∘ (λ⇒ ∘ (id ⊗₁ f ∘ λ⇐))  ≈⟨ refl⟩∘⟨ (⟺ assoc) ⟩
    tester ∘ ((λ⇒ ∘ id ⊗₁ f) ∘ λ⇐)  ≈⟨ refl⟩∘⟨ (λ⇒∘id⊗f≈f∘λ⇒ ⟩∘⟨refl) ⟩
    tester ∘ ((f ∘ λ⇒) ∘ λ⇐)        ≈⟨ refl⟩∘⟨ (assoc ○ (refl⟩∘⟨ λ⇒∘λ⇐≈id) ○ idʳ) ⟩
    tester ∘ f ∎

  source : eval (tester ∘ leaky) true
  source = named naming fresh (run false true naming)
    where
    naming : Occ (tester ∘ leaky) → ℕ
    naming (inj₁ _) = 0
    naming (inj₂ _) = 1
    fresh : Injective _≡_ _≡_ naming
    fresh {inj₁ tt} {inj₁ tt} _ = refl
    fresh {inj₂ tt} {inj₂ tt} _ = refl
    fresh {inj₁ tt} {inj₂ tt} ()
    fresh {inj₂ tt} {inj₁ tt} ()

  transfer : ∀ {f} → leaky Sym.≈ℰ f → eval (tester ∘ f) true
  transfer e = Equivalence.to (eval-cong (reduce _) true)
    (Equivalence.to (same⁻¹ (lower (Sym.KE.run∼ e {lift (unit , tester ∘ λ⇒)})) λ⇐ true)
      (Equivalence.from (eval-cong (reduce leaky) true) source))

leaky≉simulated : ¬ (leaky Sym.≈ℰ simulated)
leaky≉simulated e = contradiction (returnₚ-bool-injective
  (≈sym (run true false (eval.naming target)) ⟨≈⟩ eval.answer target))
  where
  target = transfer e
  contradiction : false ≢ true
  contradiction ()

leaky≉real : ¬ (leaky Sym.≈ℰ smt)
leaky≉real e = contradiction (returnₚ-bool-injective
  (≈sym (run false false (eval.naming target)) ⟨≈⟩ eval.answer target))
  where
  target = transfer e
  contradiction : false ≢ true
  contradiction ()
