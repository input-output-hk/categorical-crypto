{-# OPTIONS --safe --without-K --guardedness #-}

-- Two worlds that differ in a pair of frames `φ`, `ψ`, related letter by
-- letter: a term of the left world is the same recipe over `φ` as its partner
-- in the right world is over `ψ` (`Same`), with the recipe's names foreign to
-- both.  When `φ ≈ₛ ψ` every role preserves the relation — its guards agree by
-- static equivalence, and the names it draws are foreign — so a role run on
-- related letters (`apexᴿ`) is the apex of a relational simulation of the role
-- by itself (`apex≲`, `Machines.Sim.Relational`); its point and step are the
-- couplings of the two runs.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Static.Same (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Data.Bool.Base using (Bool)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Pointwise using (module MC; module K)
open import CategoricalCrypto.Machines.Sim.Relational.Pointwise
open import CategoricalCrypto.Symbolic.Deduction 𝔖 E
open import CategoricalCrypto.Symbolic.Fine 𝔖 using (ObjTerm; unit; _⊗₀_; Var)
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.Symbolic.Semantics 𝔖 E using (runᴿ)
open import CategoricalCrypto.UC.Machine using (Proc; initˢ)

open Signature 𝔖
open Terms 𝔖
open EqTheory E
open Run E

private variable
  s     : Sort
  k     : Kind
  n     : ℕ
  O     : List Kind
  x y   : ObjTerm
  Δ′ ss : List Sort
  Γ     : Fin n → List Sort

-- Which world a projection reads.
data Side : Set where
  l r : Side

pick : {A : Set} → Side → A → A → A
pick l a _ = a
pick r _ b = b

pick-same : {A : Set} (w : Side) (a : A) → pick w a a ≡ a
pick-same l _ = refl
pick-same r _ = refl

module _ {Δ : List Sort} (φ ψ : Frame Δ) where

  record Same (u u′ : Tm s) : Set where
    constructor same
    field
      recipe : Recipe Δ (Foreign φ ψ) s
      left   : u ≈E recipe ⟨ φ ⟩
      right  : u′ ≈E recipe ⟨ ψ ⟩

  record Pair (s : Sort) : Set where
    constructor pair
    field
      fst snd : Tm s
      rel     : Same fst snd

  ----------------------------------------------------------------------
  -- The apex alphabets: related pairs on ports, the bare letters elsewhere

  alphabetᵃ : Dir → Atom → Set
  alphabetᵃ pos (port s _) = Pair s
  alphabetᵃ neg (port _ t) = Pair t
  alphabetᵃ pos verdict    = Bool
  alphabetᵃ neg verdict    = ⊤
  alphabetᵃ pos void       = ⊥
  alphabetᵃ neg void       = ⊥

  π : Side → (d : Dir) (a : Atom) → alphabetᵃ d a → alphabet d a
  π w pos (port _ _) = λ q → pick w (Pair.fst q) (Pair.snd q)
  π w neg (port _ _) = λ q → pick w (Pair.fst q) (Pair.snd q)
  π _ pos verdict    = λ b → b
  π _ neg verdict    = λ u → u
  π _ pos void       = λ e → e
  π _ neg void       = λ e → e

  Alphabetᵃ : Dir → ObjTerm → Set
  Alphabetᵃ d unit     = ⊥
  Alphabetᵃ d (A ⊗₀ B) = Alphabetᵃ d A ⊎ Alphabetᵃ d B
  Alphabetᵃ d (Var a)  = alphabetᵃ d a

  Π : Side → (d : Dir) (x : ObjTerm) → Alphabetᵃ d x → Alphabet d x
  Π w d unit     = λ e → e
  Π w d (A ⊗₀ B) = Sum.map (Π w d A) (Π w d B)
  Π w d (Var a)  = π w d a

  -- What a role on `x ⇒ y` reads and writes.
  Πᴵ : Side → (x y : ObjTerm) → Alphabetᵃ pos x ⊎ Alphabetᵃ neg y → Alphabet pos x ⊎ Alphabet neg y
  Πᴵ w x y = Sum.map (Π w pos x) (Π w neg y)

  Πᴼ : Side → (x y : ObjTerm) → Alphabetᵃ neg x ⊎ Alphabetᵃ pos y → Alphabet neg x ⊎ Alphabet pos y
  Πᴼ w x y = Sum.map (Π w neg x) (Π w pos y)

  ----------------------------------------------------------------------
  -- Related values, inputs, emissions and configurations

  data SameValue : (k : Kind) → Value k → Value k → Set where
    msgᵛ  : {u u′ : Tm s} → Same u u′ → SameValue (msg s) u u′
    flagᵛ : (b : Bool) → SameValue flag b b
    tickᵛ : SameValue tick tt tt

  data SameInput {x y : ObjTerm} : Input x y → Input x y → Set where
    _↦_ : (i : k ∈ Ins x y) {v v′ : Value k} → SameValue k v v′ → SameInput (i ↦ v) (i ↦ v′)

  data SameEmission {O : List Kind} : Emission O → Emission O → Set where
    _↦_ : (o : k ∈ O) {v v′ : Value k} → SameValue k v v′ → SameEmission (o ↦ v) (o ↦ v′)

  data SameCfg {n} {Γ : Fin n → List Sort} : Config n Γ → Config n Γ → Set where
    same-cfg : {c : Fin n} {ρ ρ′ : Frame (Γ c)} {j : ℕ} → All₂ Same ρ ρ′
             → SameCfg (config c ρ j) (config c ρ′ j)

  private
    data SameRead (d : Dir) (x : ObjTerm)
         : (Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k) → (Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k) → Set where
      same-read : (i : k ∈ Kinds d x) {v v′ : Value k} → SameValue k v v′ → SameRead d x (k , i , v) (k , i , v′)

    read-same : (d : Dir) (x : ObjTerm) (a : Alphabetᵃ d x)
              → SameRead d x (read d x (Π l d x a)) (read d x (Π r d x a))
    read-same d (A ⊗₀ B) (inj₁ m) with read d A (Π l d A m) | read d A (Π r d A m) | read-same d A m
    ... | _ | _ | same-read i sv = same-read (∈-++⁺ˡ i) sv
    read-same d (A ⊗₀ B) (inj₂ m) with read d B (Π l d B m) | read d B (Π r d B m) | read-same d B m
    ... | _ | _ | same-read i sv = same-read (∈-++⁺ʳ (Kinds d A) i) sv
    read-same pos (Var (port _ _)) (pair _ _ ρ) = same-read (here refl) (msgᵛ ρ)
    read-same neg (Var (port _ _)) (pair _ _ ρ) = same-read (here refl) (msgᵛ ρ)
    read-same pos (Var verdict)    b            = same-read (here refl) (flagᵛ b)
    read-same neg (Var verdict)    tt           = same-read (here refl) tickᵛ
    read-same pos (Var void)       ()
    read-same neg (Var void)       ()
    read-same _   unit             ()

  decode-same : (x y : ObjTerm) (a : Alphabetᵃ pos x ⊎ Alphabetᵃ neg y)
              → SameInput (decode x y (Πᴵ l x y a)) (decode x y (Πᴵ r x y a))
  decode-same x y (inj₁ m) with read pos x (Π l pos x m) | read pos x (Π r pos x m) | read-same pos x m
  ... | _ | _ | same-read i sv = ∈-++⁺ˡ i ↦ sv
  decode-same x y (inj₂ m) with read neg y (Π l neg y m) | read neg y (Π r neg y m) | read-same neg y m
  ... | _ | _ | same-read i sv = ∈-++⁺ʳ (Kinds pos x) i ↦ sv

  writeᵃ : (d : Dir) (x : ObjTerm) → k ∈ Kinds d x → {v v′ : Value k} → SameValue k v v′ → Alphabetᵃ d x
  writeᵃ d (A ⊗₀ B) i sv =
    [ (λ j → inj₁ (writeᵃ d A j sv)) , (λ j → inj₂ (writeᵃ d B j sv)) ]′ (∈-++⁻ (Kinds d A) i)
  writeᵃ pos (Var (port _ _)) (here refl) (msgᵛ ρ)  = pair _ _ ρ
  writeᵃ neg (Var (port _ _)) (here refl) (msgᵛ ρ)  = pair _ _ ρ
  writeᵃ pos (Var verdict)    (here refl) (flagᵛ b) = b
  writeᵃ neg (Var verdict)    (here refl) tickᵛ     = tt
  writeᵃ pos (Var (port _ _)) (there ()) _
  writeᵃ neg (Var (port _ _)) (there ()) _
  writeᵃ pos (Var verdict)    (there ()) _
  writeᵃ neg (Var verdict)    (there ()) _
  writeᵃ pos (Var void)       ()         _
  writeᵃ neg (Var void)       ()         _
  writeᵃ _   unit             ()         _

  Π-writeᵃ : (w : Side) (d : Dir) (x : ObjTerm) (i : k ∈ Kinds d x) {v v′ : Value k} (sv : SameValue k v v′)
           → Π w d x (writeᵃ d x i sv) ≡ write d x i (pick w v v′)
  Π-writeᵃ w d (A ⊗₀ B) i sv with ∈-++⁻ (Kinds d A) i
  ... | inj₁ j = cong inj₁ (Π-writeᵃ w d A j sv)
  ... | inj₂ j = cong inj₂ (Π-writeᵃ w d B j sv)
  Π-writeᵃ w pos (Var (port _ _)) (here refl) (msgᵛ _)  = refl
  Π-writeᵃ w neg (Var (port _ _)) (here refl) (msgᵛ _)  = refl
  Π-writeᵃ w pos (Var verdict)    (here refl) (flagᵛ b) = sym (pick-same w b)
  Π-writeᵃ w neg (Var verdict)    (here refl) tickᵛ     = sym (pick-same w tt)
  Π-writeᵃ w pos (Var (port _ _)) (there ()) _
  Π-writeᵃ w neg (Var (port _ _)) (there ()) _
  Π-writeᵃ w pos (Var verdict)    (there ()) _
  Π-writeᵃ w neg (Var verdict)    (there ()) _
  Π-writeᵃ w pos (Var void)       ()         _
  Π-writeᵃ w neg (Var void)       ()         _
  Π-writeᵃ w _   unit             ()         _

  encodeᵃ : (x y : ObjTerm) {e e′ : Emission (Outs x y)} → SameEmission e e′ → Alphabetᵃ neg x ⊎ Alphabetᵃ pos y
  encodeᵃ x y (o ↦ sv) =
    [ (λ j → inj₁ (writeᵃ neg x j sv)) , (λ j → inj₂ (writeᵃ pos y j sv)) ]′ (∈-++⁻ (Kinds neg x) o)

  Πᴼ-encodeᵃ : (w : Side) (x y : ObjTerm) {e e′ : Emission (Outs x y)} (se : SameEmission e e′)
             → Πᴼ w x y (encodeᵃ x y se) ≡ encode x y (pick w e e′)
  Πᴼ-encodeᵃ l x y (o ↦ sv) with ∈-++⁻ (Kinds neg x) o
  ... | inj₁ j = cong inj₁ (Π-writeᵃ l neg x j sv)
  ... | inj₂ j = cong inj₂ (Π-writeᵃ l pos y j sv)
  Πᴼ-encodeᵃ r x y (o ↦ sv) with ∈-++⁻ (Kinds neg x) o
  ... | inj₁ j = cong inj₁ (Π-writeᵃ r neg x j sv)
  ... | inj₂ j = cong inj₂ (Π-writeᵃ r pos y j sv)

  init-same : (p : Role x y) → SameCfg (init p) (init p)
  init-same p = same-cfg (cleared (sym (Role.fresh p)))
    where
    cleared : ∀ {ss} (e : [] ≡ ss) → All₂ Same (subst Frame e []) (subst Frame e [])
    cleared refl = []

  ----------------------------------------------------------------------
  -- Every role preserves the relation

  module _ (equiv : φ ≈ₛ ψ) where

    private
      recipes : {ρ ρ′ : Frame Δ′} → All₂ Same ρ ρ′ → ∀ {s} → s ∈ Δ′ → Recipe Δ (Foreign φ ψ) s
      recipes rs i = Same.recipe (lookup₂ rs i)

      over-φ : {ρ ρ′ : Frame Δ′} (rs : All₂ Same ρ ρ′) (ζ : Rcp Δ′ s)
             → ζ ⟨ ρ ⟩ ≈E bind (recipes rs) (λ ()) ζ ⟨ φ ⟩
      over-φ rs ζ = ≈E.sym (bind-⟨⟩ (recipes rs) (λ ()) (λ i → ≈E.sym (Same.left (lookup₂ rs i))) ζ)

      over-ψ : {ρ ρ′ : Frame Δ′} (rs : All₂ Same ρ ρ′) (ζ : Rcp Δ′ s)
             → ζ ⟨ ρ′ ⟩ ≈E bind (recipes rs) (λ ()) ζ ⟨ ψ ⟩
      over-ψ rs ζ = ≈E.sym (bind-⟨⟩ (recipes rs) (λ ()) (λ i → ≈E.sym (Same.right (lookup₂ rs i))) ζ)

      -- A guard decides alike in both worlds: static equivalence.
      guard : {ρ ρ′ : Frame Δ′} (rs : All₂ Same ρ ρ′) (ζ ζ′ : Rcp Δ′ s)
            → ζ ⟨ ρ ⟩ ≈E ζ′ ⟨ ρ ⟩ → ζ ⟨ ρ′ ⟩ ≈E ζ′ ⟨ ρ′ ⟩
      guard rs ζ ζ′ e = ≈E.trans (over-ψ rs ζ) (≈E.trans
        (Equivalence.to (equiv (bind (recipes rs) (λ ()) ζ) (bind (recipes rs) (λ ()) ζ′))
          (≈E.trans (≈E.sym (over-φ rs ζ)) (≈E.trans e (over-φ rs ζ′))))
        (≈E.sym (over-ψ rs ζ′)))

      guard⁻ : {ρ ρ′ : Frame Δ′} (rs : All₂ Same ρ ρ′) (ζ ζ′ : Rcp Δ′ s)
             → ζ ⟨ ρ′ ⟩ ≈E ζ′ ⟨ ρ′ ⟩ → ζ ⟨ ρ ⟩ ≈E ζ′ ⟨ ρ ⟩
      guard⁻ rs ζ ζ′ e = ≈E.trans (over-φ rs ζ) (≈E.trans
        (Equivalence.from (equiv (bind (recipes rs) (λ ()) ζ) (bind (recipes rs) (λ ()) ζ′))
          (≈E.trans (≈E.sym (over-ψ rs ζ)) (≈E.trans e (over-ψ rs ζ′))))
        (≈E.sym (over-φ rs ζ′)))

    -- `fresh`: the names occurrence `κ` draws are foreign to both frames.
    module _ {κ : ℕ} (fresh : ∀ j → Foreign φ ψ (κ , j)) where

      exec-same : (t : React n Γ O Δ′) {ρ ρ′ : Frame Δ′} {j : ℕ} → All₂ Same ρ ρ′
                → SameCfg (proj₁ (exec κ t ρ j)) (proj₁ (exec κ t ρ′ j))
                × SameEmission (proj₂ (exec κ t ρ j)) (proj₂ (exec κ t ρ′ j))
      exec-same (test ζ ζ′ t e) {ρ} {ρ′} rs with ζ ⟨ ρ ⟩ ≟E ζ′ ⟨ ρ ⟩ | ζ ⟨ ρ′ ⟩ ≟E ζ′ ⟨ ρ′ ⟩
      ... | yes _ | yes _ = exec-same t rs
      ... | no _  | no _  = exec-same e rs
      ... | yes a | no ¬b = ⊥-elim (¬b (guard rs ζ ζ′ a))
      ... | no ¬a | yes b = ⊥-elim (¬a (guard⁻ rs ζ ζ′ b))
      exec-same (new _ t) {j = j} rs = exec-same t (same (mine (κ , j) (fresh j)) ≈E.refl ≈E.refl ∷ rs)
      exec-same {Δ′ = Δ′} (emit {k = k} _ ρs o pl) {ρ} {ρ′} rs = same-cfg (regs-same ρs) , o ↦ value-same k pl
        where
        related : (ζ : Rcp Δ′ s) → Same (canon (ζ ⟨ ρ ⟩)) (canon (ζ ⟨ ρ′ ⟩))
        related ζ = same (bind (recipes rs) (λ ()) ζ) (≈E.trans (canon-≈E _) (over-φ rs ζ))
                                                      (≈E.trans (canon-≈E _) (over-ψ rs ζ))

        regs-same : (ρs : All (Rcp Δ′) ss) → All₂ Same (canon* (ρs ⟨ ρ ⟩*)) (canon* (ρs ⟨ ρ′ ⟩*))
        regs-same []       = []
        regs-same (ζ ∷ ρs) = related ζ ∷ regs-same ρs

        value-same : ∀ k (v : Payload Δ′ k) → SameValue k (canonᵛ (payload k v ρ)) (canonᵛ (payload k v ρ′))
        value-same (msg _) ζ = msgᵛ (related ζ)
        value-same flag    b = flagᵛ b
        value-same tick    _ = tickᵛ

      step-same : (p : Role x y) {cfg cfg′ : Config (Role.n p) (Role.Γ p)} {inp inp′ : Input x y}
                → SameCfg cfg cfg′ → SameInput inp inp′
                → SameCfg (proj₁ (step κ p cfg inp)) (proj₁ (step κ p cfg′ inp′))
                × SameEmission (proj₂ (step κ p cfg inp)) (proj₂ (step κ p cfg′ inp′))
      step-same p {config c _ _} (same-cfg rs) (i ↦ msgᵛ q)  = exec-same (Role.react p c i tt) (q ∷ rs)
      step-same p {config c _ _} (same-cfg rs) (i ↦ flagᵛ b) = exec-same (Role.react p c i b) rs
      step-same p {config c _ _} (same-cfg rs) (i ↦ tickᵛ)   = exec-same (Role.react p c i tt) rs

      ------------------------------------------------------------------
      -- The apex: a role run on both worlds' letters at once

      module _ {x y : ObjTerm} (p : Role x y) where

        Stateᵃ : Set
        Stateᵃ = Σ[ cc ∈ Config (Role.n p) (Role.Γ p) × Config (Role.n p) (Role.Γ p) ] SameCfg (proj₁ cc) (proj₂ cc)

        stepᵃ : Stateᵃ → Alphabetᵃ pos x ⊎ Alphabetᵃ neg y → Stateᵃ × (Alphabetᵃ neg x ⊎ Alphabetᵃ pos y)
        stepᵃ ((c , c′) , rc) a = ((proj₁ out , proj₁ out′) , proj₁ sm) , encodeᵃ x y (proj₂ sm)
          where
          out  = step κ p c  (decode x y (Πᴵ l x y a))
          out′ = step κ p c′ (decode x y (Πᴵ r x y a))
          sm   = step-same p rc (decode-same x y a)

        apexᴿ : Proc (Alphabetᵃ pos x ⇿ Alphabetᵃ neg x) (Alphabetᵃ pos y ⇿ Alphabetᵃ neg y)
        apexᴿ = MC.mk (initˢ Stateᵃ ((init p , init p) , init-same p)) λ (st , a) → returnₚ (stepᵃ st a)

        private
          stepˡ : (w : Side) (st : Stateᵃ) (a : Alphabetᵃ pos x ⊎ Alphabetᵃ neg y)
                → (pick w (proj₁ (proj₁ (proj₁ (stepᵃ st a)))) (proj₂ (proj₁ (proj₁ (stepᵃ st a))))
                  , Πᴼ w x y (proj₂ (stepᵃ st a)))
                ≡ Data.Product.map₂ (encode x y)
                    (step κ p (pick w (proj₁ (proj₁ st)) (proj₂ (proj₁ st))) (decode x y (Πᴵ w x y a)))
          stepˡ l ((c , c′) , rc) a = cong (_ ,_) (Πᴼ-encodeᵃ l x y (proj₂ (step-same p rc (decode-same x y a))))
          stepˡ r ((c , c′) , rc) a = cong (_ ,_) (Πᴼ-encodeᵃ r x y (proj₂ (step-same p rc (decode-same x y a))))

        -- Each world's run is a simulation of the apex along its projections.
        apex≲ : (w : Side) → apexᴿ RS.≲[ K.pureᵏ (Πᴵ w x y) ∣ K.pureᵏ (Πᴼ w x y) ] runᴿ κ p
        apex≲ w = simFn[] (λ st → pick w (proj₁ (proj₁ st)) (proj₂ (proj₁ st))) (Πᴵ w x y) (Πᴼ w x y)
          (λ _ → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ (cong returnₚ (pick-same w (init p))))
          λ (st , a) → >>=ₚ-identityˡ _ _ ⟨≈⟩ ≡⇒≈ₚ (cong returnₚ (stepˡ w st a))
