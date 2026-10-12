{-# OPTIONS --safe --without-K --guardedness #-}

open import Data.Nat.Base using (ℕ; suc)

module CategoricalCrypto.Symbolic.RunFollowing.Role (κ : ℕ) where

open import Data.Bool.Base
open import Data.Empty
open import Data.Fin.Base using (Fin)
open import Data.List.Base hiding (lookup)
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Data.List.Relation.Unary.Any hiding (lookup)
open import Data.Product
open import Data.Sum.Base as Sum
open import Data.Unit.Base
open import Function.Base
open import Function.Bundles using (mk⇔)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using (does-⇔)

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Machines.Sandwich using (sandwichᴹ)
open import CategoricalCrypto.Symbolic.Term
open import CategoricalCrypto.Symbolic.Term.PairEnc
open import CategoricalCrypto.Symbolic.Fine Σ₀ using (ObjTerm; Var; unit; _⊗₀_)
open import CategoricalCrypto.Symbolic.Role Σ₀
open import CategoricalCrypto.Symbolic.Semantics Σ₀ E₀ using (runᴿ; ⟦_⟧ᴵ)
open import CategoricalCrypto.Symbolic.RunFollowing.PairEnc κ
open import CategoricalCrypto.UC.Machine using (Proc)

open Terms Σ₀
open EqTheory E₀
open Run E₀ hiding (after)

private variable
  Δ ss : List ⊤
  n : ℕ
  Γ : Fin n → List ⊤
  O : List Kind
  x y : ObjTerm
  w w′ : World
  b : Bool

expand-lookup : ∀ b w (ρ : Frame Δ) {s} (i : s ∈ Δ) → lookup (expand* b w ρ) i ≡ expand b w (lookup ρ i)
expand-lookup b w (_ ∷ _) (here refl) = refl
expand-lookup b w (_ ∷ ρ) (there i) = expand-lookup b w ρ i

expand-recipe : ∀ b w (ζ : Rcp Δ tt) ρ → ζ ⟨ expand* b w ρ ⟩ ≡ expand b w (ζ ⟨ ρ ⟩)
expand-recipes : ∀ b w (ζs : All (Rcp Δ) ss) ρ → ζs ⟨ expand* b w ρ ⟩* ≡ expand* b w (ζs ⟨ ρ ⟩*)
expand-recipe b w (var i) ρ = expand-lookup b w ρ i
expand-recipe b w (mine _ ()) ρ
expand-recipe b w (app f ζs) ρ = trans (cong (app f) (expand-recipes b w ζs ρ)) (sym (expand-app b w f _))
expand-recipes b w [] ρ = refl
expand-recipes b w (ζ ∷ ζs) ρ = cong₂ _∷_ (expand-recipe b w ζ ρ) (expand-recipes b w ζs ρ)

canon-recipe : ∀ b w (ζ : Rcp Δ tt) ρ → nf (ζ ⟨ expand* b w ρ ⟩) ≡ expand b w (nf (ζ ⟨ ρ ⟩))
canon-recipe b w ζ ρ = trans (cong nf (expand-recipe b w ζ ρ)) (expand-canon b w (ζ ⟨ ρ ⟩))

canon-recipes : ∀ b w (ζs : All (Rcp Δ) ss) ρ
  → canon* (ζs ⟨ expand* b w ρ ⟩*) ≡ expand* b w (canon* (ζs ⟨ ρ ⟩*))
canon-recipes b w [] ρ = refl
canon-recipes b w (ζ ∷ ζs) ρ = cong₂ _∷_ (canon-recipe b w ζ ρ) (canon-recipes b w ζs ρ)

expand-value : ∀ b w k → Value k → Value k
expand-value b w (msg tt) = expand b w
expand-value b w flag = λ v → v
expand-value b w tick = λ v → v

expand-config : ∀ b w → Config n Γ → Config n Γ
expand-config b w (config c ρ j) = config c (expand* b w ρ) j

expand-emission : ∀ b w → Emission O → Emission O
expand-emission b w (_↦_ {k} o v) = o ↦ expand-value b w k v

expand-input : ∀ b w → Input x y → Input x y
expand-input b w (_↦_ {k} i v) = i ↦ expand-value b w k v

LegalValue : World → (k : Kind) → Value k → Set
LegalValue w (msg tt) = Legal w
LegalValue w flag = λ _ → ⊤
LegalValue w tick = λ _ → ⊤

LegalEmission : World → Emission O → Set
LegalEmission w (_↦_ {k} _ v) = LegalValue w k v

LegalConfig : World → Config n Γ → Set
LegalConfig w cfg = Each (Legal w) (registers cfg)

module _ (κ′ : ℕ) (foreign : κ′ ≢ κ) where
  private
    name-foreign : ∀ j → (κ′ , j) ≢ key
    name-foreign j e = foreign (cong proj₁ e)

    new-legal : ∀ w j → Legal w (name (κ′ , j))
    new-legal before j (here e) = name-foreign j (sym e)
    new-legal before j (there ())
    new-legal (after _) j = tt

    guard-forward : ∀ b w (ζ ζ′ : Rcp Δ tt) ρ → ζ ⟨ ρ ⟩ ≈E ζ′ ⟨ ρ ⟩
      → ζ ⟨ expand* b w ρ ⟩ ≈E ζ′ ⟨ expand* b w ρ ⟩
    guard-forward b w ζ ζ′ ρ e = trans (canon-recipe b w ζ ρ) (trans (cong (expand b w) e) (sym (canon-recipe b w ζ′ ρ)))

    guard-backward : ∀ b w (ζ ζ′ : Rcp Δ tt) ρ → ζ ⟨ expand* b w ρ ⟩ ≈E ζ′ ⟨ expand* b w ρ ⟩
      → ζ ⟨ ρ ⟩ ≈E ζ′ ⟨ ρ ⟩
    guard-backward b w ζ ζ′ ρ e = expand-injective b w
      (trans (sym (canon-recipe b w ζ ρ)) (trans e (canon-recipe b w ζ′ ρ)))

  exec-expand : ∀ b w (t : React n Γ O Δ) ρ j
    → exec κ′ t (expand* b w ρ) j
      ≡ Data.Product.map (expand-config b w) (expand-emission b w) (exec κ′ t ρ j)
  exec-expand b w (test {s = tt} ζ ζ′ t e) ρ j
    rewrite does-⇔ (mk⇔ (guard-backward b w ζ ζ′ ρ) (guard-forward b w ζ ζ′ ρ))
      (ζ ⟨ expand* b w ρ ⟩ ≟E ζ′ ⟨ expand* b w ρ ⟩) (ζ ⟨ ρ ⟩ ≟E ζ′ ⟨ ρ ⟩)
    with does (ζ ⟨ ρ ⟩ ≟E ζ′ ⟨ ρ ⟩)
  ... | true = exec-expand b w t ρ j
  ... | false = exec-expand b w e ρ j
  exec-expand b w (new tt t) ρ j =
    trans (cong (λ z → exec κ′ t (z ∷ expand* b w ρ) (suc j)) (sym (expand-fresh b w (κ′ , j) (name-foreign j))))
      (exec-expand b w t (name (κ′ , j) ∷ ρ) (suc j))
  exec-expand {Δ = Δ} b w (emit {k = k} c ζs o v) ρ j = cong₂ _,_
    (cong (λ z → config c z j) (canon-recipes b w ζs ρ)) (cong (o ↦_) (value k v))
    where
    value : ∀ k (v : Payload Δ k) → canonᵛ (payload k v (expand* b w ρ)) ≡ expand-value b w k (canonᵛ (payload k v ρ))
    value (msg tt) ζ = canon-recipe b w ζ ρ
    value flag v = refl
    value tick v = refl

  exec-legal : ∀ w (t : React n Γ O Δ) (ρ : Frame Δ) j → Each (Legal w) ρ
    → LegalConfig w (proj₁ (exec κ′ t ρ j)) × LegalEmission w (proj₂ (exec κ′ t ρ j))
  exec-legal w (test {s = tt} ζ ζ′ t e) ρ j legal with does (ζ ⟨ ρ ⟩ ≟E ζ′ ⟨ ρ ⟩)
  ... | true = exec-legal w t ρ j legal
  ... | false = exec-legal w e ρ j legal
  exec-legal w (new tt t) ρ j legal = exec-legal w t (name (κ′ , j) ∷ ρ) (suc j) (new-legal w j ∷ legal)
  exec-legal {Δ = Δ} w (emit {k = k} c ζs o v) ρ j legal = regs ζs , value k v
    where
    legal-recipe : (ζ : Rcp Δ tt) → Legal w (nf (ζ ⟨ ρ ⟩))
    legal-recipe ζ = canon-legal w (ζ ⟨ ρ ⟩) (recipe-legal w ζ ρ legal)
    regs : (ζs : All (Rcp Δ) ss) → Each (Legal w) (canon* (ζs ⟨ ρ ⟩*))
    regs [] = []
    regs (ζ ∷ ζs) = legal-recipe ζ ∷ regs ζs
    value : ∀ k (v : Payload Δ k) → LegalValue w k (canonᵛ (payload k v ρ))
    value (msg tt) ζ = legal-recipe ζ
    value flag _ = tt
    value tick _ = tt

  step-expand : ∀ b w (p : Role x y) cfg inp → step κ′ p (expand-config b w cfg) (expand-input b w inp)
    ≡ Data.Product.map (expand-config b w) (expand-emission b w) (step κ′ p cfg inp)
  step-expand b w p (config c ρ j) (_↦_ {msg tt} i v) = exec-expand b w (Role.react p c i tt) (v ∷ ρ) j
  step-expand b w p (config c ρ j) (_↦_ {flag} i v) = exec-expand b w (Role.react p c i v) ρ j
  step-expand b w p (config c ρ j) (_↦_ {tick} i v) = exec-expand b w (Role.react p c i tt) ρ j

  step-legal : ∀ w (p : Role x y) cfg {k} (i : k ∈ Ins x y) (v : Value k)
    → LegalConfig w cfg → LegalValue w k v
    → LegalConfig w (proj₁ (step κ′ p cfg (i ↦ v))) × LegalEmission w (proj₂ (step κ′ p cfg (i ↦ v)))
  step-legal w p (config c ρ j) {msg tt} i v rs pv = exec-legal w (Role.react p c i tt) (v ∷ ρ) j (pv ∷ rs)
  step-legal w p (config c ρ j) {flag} i v rs pv = exec-legal w (Role.react p c i v) ρ j rs
  step-legal w p (config c ρ j) {tick} i v rs pv = exec-legal w (Role.react p c i tt) ρ j rs

expand-alphabet : ∀ b w d x → Alphabet d x → Alphabet d x
expand-alphabet b w d (A ⊗₀ B) = Sum.map (expand-alphabet b w d A) (expand-alphabet b w d B)
expand-alphabet b w pos (Var (port tt tt)) = expand b w
expand-alphabet b w neg (Var (port tt tt)) = expand b w
expand-alphabet b w pos (Var verdict) = λ a → a
expand-alphabet b w neg (Var verdict) = λ a → a
expand-alphabet b w pos (Var void) = λ ()
expand-alphabet b w neg (Var void) = λ ()
expand-alphabet b w d unit = λ ()

LegalAlphabet : World → ∀ d x → Alphabet d x → Set
LegalAlphabet w d (A ⊗₀ B) (inj₁ a) = LegalAlphabet w d A a
LegalAlphabet w d (A ⊗₀ B) (inj₂ b) = LegalAlphabet w d B b
LegalAlphabet w pos (Var (port tt tt)) = Legal w
LegalAlphabet w neg (Var (port tt tt)) = Legal w
LegalAlphabet w pos (Var verdict) = λ _ → ⊤
LegalAlphabet w neg (Var verdict) = λ _ → ⊤
LegalAlphabet w pos (Var void) = λ ()
LegalAlphabet w neg (Var void) = λ ()
LegalAlphabet w d unit = λ ()

alphabets : ∀ d x → F.Letters
alphabets d x = record
  { Base = Alphabet d x ; Related = λ w → Σ (Alphabet d x) (LegalAlphabet w d x)
  ; project = λ b w a → expand-alphabet b w d x (proj₁ a) }

private
  projected-read : ∀ b w (d : Dir) (x : ObjTerm) (q : Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k)
    → Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k
  projected-read b w d x (k , i , v) = k , i , expand-value b w k v

  read-expand : ∀ b w d x a → read d x (expand-alphabet b w d x a) ≡ projected-read b w d x (read d x a)
  read-expand b w d (A ⊗₀ B) (inj₁ a) rewrite read-expand b w d A a with read d A a
  ... | k , i , v = refl
  read-expand b w d (A ⊗₀ B) (inj₂ a) rewrite read-expand b w d B a with read d B a
  ... | k , i , v = refl
  read-expand b w pos (Var (port tt tt)) a = refl
  read-expand b w neg (Var (port tt tt)) a = refl
  read-expand b w pos (Var verdict) a = refl
  read-expand b w neg (Var verdict) a = refl
  read-expand b w pos (Var void) ()
  read-expand b w neg (Var void) ()
  read-expand b w d unit ()

  read-legal : ∀ w d x a → LegalAlphabet w d x a
    → LegalValue w (proj₁ (read d x a)) (proj₂ (proj₂ (read d x a)))
  read-legal w d (A ⊗₀ B) (inj₁ a) p with read d A a | read-legal w d A a p
  ... | k , i , v | q = q
  read-legal w d (A ⊗₀ B) (inj₂ a) p with read d B a | read-legal w d B a p
  ... | k , i , v | q = q
  read-legal w pos (Var (port tt tt)) a p = p
  read-legal w neg (Var (port tt tt)) a p = p
  read-legal w pos (Var verdict) a p = tt
  read-legal w neg (Var verdict) a p = tt
  read-legal w pos (Var void) ()
  read-legal w neg (Var void) ()
  read-legal w d unit ()

  write-expand : ∀ b w d x {k} (i : k ∈ Kinds d x) v
    → expand-alphabet b w d x (write d x i v) ≡ write d x i (expand-value b w k v)
  write-expand b w d (A ⊗₀ B) i v with ∈-++⁻ (Kinds d A) i
  ... | inj₁ j = cong inj₁ (write-expand b w d A j v)
  ... | inj₂ j = cong inj₂ (write-expand b w d B j v)
  write-expand b w pos (Var (port tt tt)) (here refl) v = refl
  write-expand b w neg (Var (port tt tt)) (here refl) v = refl
  write-expand b w pos (Var verdict) (here refl) v = refl
  write-expand b w neg (Var verdict) (here refl) v = refl
  write-expand b w pos (Var (port tt tt)) (there ()) v
  write-expand b w neg (Var (port tt tt)) (there ()) v
  write-expand b w pos (Var verdict) (there ()) v
  write-expand b w neg (Var verdict) (there ()) v
  write-expand b w pos (Var void) () v
  write-expand b w neg (Var void) () v
  write-expand b w d unit () v

  write-legal : ∀ w d x {k} (i : k ∈ Kinds d x) v → LegalValue w k v → LegalAlphabet w d x (write d x i v)
  write-legal w d (A ⊗₀ B) i v p with ∈-++⁻ (Kinds d A) i
  ... | inj₁ j = write-legal w d A j v p
  ... | inj₂ j = write-legal w d B j v p
  write-legal w pos (Var (port tt tt)) (here refl) v p = p
  write-legal w neg (Var (port tt tt)) (here refl) v p = p
  write-legal w pos (Var verdict) (here refl) v p = tt
  write-legal w neg (Var verdict) (here refl) v p = tt
  write-legal w pos (Var (port tt tt)) (there ()) v p
  write-legal w neg (Var (port tt tt)) (there ()) v p
  write-legal w pos (Var verdict) (there ()) v p
  write-legal w neg (Var verdict) (there ()) v p
  write-legal w pos (Var void) () v p
  write-legal w neg (Var void) () v p
  write-legal w d unit () v p

inputs outputs : ObjTerm → ObjTerm → F.Letters
inputs x y = alphabets pos x F.⊎ᴸ alphabets neg y
outputs x y = alphabets neg x F.⊎ᴸ alphabets pos y

input-term : ∀ w x y → F.Related (inputs x y) w → Alphabet pos x ⊎ Alphabet neg y
input-term w x y (inj₁ a) = inj₁ (proj₁ a)
input-term w x y (inj₂ a) = inj₂ (proj₁ a)

private
  decode-expand : ∀ b w x y a → decode x y (F.project (inputs x y) b w a)
    ≡ expand-input b w (decode x y (input-term w x y a))
  decode-expand b w x y (inj₁ (a , p)) rewrite read-expand b w pos x a with read pos x a
  ... | k , i , v = refl
  decode-expand b w x y (inj₂ (a , p)) rewrite read-expand b w neg y a with read neg y a
  ... | k , i , v = refl

  decode-legal : ∀ w x y a → let i = decode x y (input-term w x y a) in
    (case i of λ { (_↦_ {k} _ v) → LegalValue w k v })
  decode-legal w x y (inj₁ (a , p)) with read pos x a | read-legal w pos x a p
  ... | k , i , v | q = q
  decode-legal w x y (inj₂ (a , p)) with read neg y a | read-legal w neg y a p
  ... | k , i , v | q = q

  lift-output : ∀ w x y (e : Emission (Outs x y)) → LegalEmission w e → F.Related (outputs x y) w
  lift-output w x y (_↦_ {k} i v) p with ∈-++⁻ (Kinds neg x) i
  ... | inj₁ j = inj₁ (write neg x j v , write-legal w neg x j v p)
  ... | inj₂ j = inj₂ (write pos y j v , write-legal w pos y j v p)

  output-project : ∀ b w x y e p → F.project (outputs x y) b w (lift-output w x y e p)
    ≡ encode x y (expand-emission b w e)
  output-project b w x y (_↦_ {k} i v) p with ∈-++⁻ (Kinds neg x) i
  ... | inj₁ j = cong inj₁ (write-expand b w neg x j v)
  ... | inj₂ j = cong inj₂ (write-expand b w pos y j v)

  promote-alphabet : ∀ (e : w ≤ʷ w′) d x a → LegalAlphabet w d x a → LegalAlphabet w′ d x a
  promote-alphabet e d (A ⊗₀ B) (inj₁ a) p = promote-alphabet e d A a p
  promote-alphabet e d (A ⊗₀ B) (inj₂ a) p = promote-alphabet e d B a p
  promote-alphabet e pos (Var (port tt tt)) a p = promote-legal e p
  promote-alphabet e neg (Var (port tt tt)) a p = promote-legal e p
  promote-alphabet e pos (Var verdict) a p = tt
  promote-alphabet e neg (Var verdict) a p = tt
  promote-alphabet e pos (Var void) ()
  promote-alphabet e neg (Var void) ()
  promote-alphabet e d unit ()

  promote-registers : (e : w ≤ʷ w′) (ρ : Frame Δ) → Each (Legal w) ρ → Each (Legal w′) ρ
  promote-registers e [] [] = []
  promote-registers e (_ ∷ ρ) (p ∷ ps) = promote-legal e p ∷ promote-registers e ρ ps

  promote-frames : ∀ b (e : w ≤ʷ w′) (ρ : Frame Δ) → Each (Legal w) ρ → expand* b w′ ρ ≡ expand* b w ρ
  promote-frames b e [] [] = refl
  promote-frames b e (t ∷ ρ) (p ∷ ps) = cong₂ _∷_ (promote-expand b e t p) (promote-frames b e ρ ps)

module _ (κ′ : ℕ) (foreign : κ′ ≢ κ) (p : Role x y) where
  private
    cleared : ∀ {Δ} (e : [] ≡ Δ) → Each (Legal w) (subst Frame e [])
    cleared refl = []

    initial-expand : ∀ b w → expand-config b w (init p) ≡ init p
    initial-expand b w = cong (λ ρ → config (Role.start p) ρ 0) (empty (sym (Role.fresh p)))
      where
      empty : ∀ {Δ} (e : [] ≡ Δ) → expand* b w (subst Frame e []) ≡ subst Frame e []
      empty refl = refl

    State : World → Set
    State w = Σ (Config (Role.n p) (Role.Γ p)) (LegalConfig w)

    act : ∀ w → State w × F.Related (inputs x y) w → State w × F.Related (outputs x y) w
    act w ((cfg , legal) , a) with decode x y (input-term w x y a) | decode-legal w x y a
    ... | i ↦ v | pv = (proj₁ result , proj₁ preserved) , lift-output w x y (proj₂ result) (proj₂ preserved)
      where
      result = step κ′ p cfg (i ↦ v)
      preserved = step-legal κ′ foreign w p cfg i v legal pv

    act-project : ∀ b w (s : State w) a → Data.Product.map (expand-config b w ∘ proj₁) (F.project (outputs x y) b w) (act w (s , a))
      ≡ Data.Product.map₂ (encode x y) (step κ′ p (expand-config b w (proj₁ s)) (decode x y (F.project (inputs x y) b w a)))
    act-project b w (cfg , legal) a rewrite decode-expand b w x y a with decode x y (input-term w x y a) | decode-legal w x y a
    ... | i ↦ v | pv = trans (cong (expand-config b w (proj₁ result) ,_) (output-project b w x y (proj₂ result) (proj₂ preserved)))
      (sym (cong (Data.Product.map₂ (encode x y)) (step-expand κ′ foreign b w p cfg (i ↦ v))))
      where
      result = step κ′ p cfg (i ↦ v)
      preserved = step-legal κ′ foreign w p cfg i v legal pv

  role-stable : F.Stable (inputs x y) (outputs x y) (λ _ → runᴿ κ′ p)
  role-stable = record
    { State = State
    ; project-state = λ b w s → expand-config b w (proj₁ s)
    ; point = λ w → returnₚ (init p , cleared {w = w} (sym (Role.fresh p)))
    ; point-law = λ b w → >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡ (initial-expand b w)
    ; act = λ w sx → returnₚ (act w sx)
    ; act-law = λ b w s a → >>=ₚ-identityˡ _ _ ⟨≈⟩ ret≡ (act-project b w s a)
    ; promote = λ e (cfg , legal) → cfg , promote-registers e (registers cfg) legal
    ; promote-law = λ b e (cfg , legal) → cong (λ ρ → config (control cfg) ρ (counter cfg))
      (promote-frames b e (registers cfg) legal) }

Nested : World → Dir → ObjTerm → Set
Nested w d (A ⊗₀ B) = Nested w d A ⊎ Nested w d B
Nested w d (Var a) = Σ (Alphabet d (Var a)) (LegalAlphabet w d (Var a))
Nested w d unit = Alphabet d unit

nested-project : ∀ b w d x → Nested w d x → Alphabet d x
nested-project b w d (A ⊗₀ B) = Sum.map (nested-project b w d A) (nested-project b w d B)
nested-project b w d (Var a) = expand-alphabet b w d (Var a) ∘ proj₁
nested-project b w d unit = λ ()

trees : ∀ d x → F.Letters
trees d x = record { Base = Alphabet d x ; Related = λ w → Nested w d x ; project = λ b w → nested-project b w d x }

to-flat : ∀ w d x → Nested w d x → F.Related (alphabets d x) w
to-flat w d (A ⊗₀ B) (inj₁ a) = inj₁ (proj₁ q) , proj₂ q
  where q = to-flat w d A a
to-flat w d (A ⊗₀ B) (inj₂ b) = inj₂ (proj₁ q) , proj₂ q
  where q = to-flat w d B b
to-flat w d (Var a) x = x
to-flat w d unit ()

from-flat : ∀ w d x → F.Related (alphabets d x) w → Nested w d x
from-flat w d (A ⊗₀ B) (inj₁ a , p) = inj₁ (from-flat w d A (a , p))
from-flat w d (A ⊗₀ B) (inj₂ b , p) = inj₂ (from-flat w d B (b , p))
from-flat w d (Var a) x = x
from-flat w d unit (() , _)

to-flat-project : ∀ b w d x a → F.project (alphabets d x) b w (to-flat w d x a) ≡ F.project (trees d x) b w a
to-flat-project b w d (A ⊗₀ B) (inj₁ a) = cong inj₁ (to-flat-project b w d A a)
to-flat-project b w d (A ⊗₀ B) (inj₂ a) = cong inj₂ (to-flat-project b w d B a)
to-flat-project b w d (Var _) a = refl
to-flat-project b w d unit ()

from-flat-project : ∀ b w d x a → F.project (trees d x) b w (from-flat w d x a) ≡ F.project (alphabets d x) b w a
from-flat-project b w d (A ⊗₀ B) (inj₁ a , p) = cong inj₁ (from-flat-project b w d A (a , p))
from-flat-project b w d (A ⊗₀ B) (inj₂ a , p) = cong inj₂ (from-flat-project b w d B (a , p))
from-flat-project b w d (Var _) a = refl
from-flat-project b w d unit (() , _)

tree-role : ∀ κ′ (p : Role x y) → Proc ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ
tree-role κ′ p = sandwichᴹ (runᴿ κ′ p) (λ x → x) (λ x → x)

tree-role-stable : ∀ κ′ → κ′ ≢ κ → (p : Role x y)
  → F.Stable (trees pos x F.⊎ᴸ trees neg y) (trees neg x F.⊎ᴸ trees pos y) (λ _ → tree-role κ′ p)
tree-role-stable {x = x} {y = y} κ′ foreign p = F.sandwich-stable (λ _ x → x) (λ _ x → x)
  (λ w → Sum.map (to-flat w pos x) (to-flat w neg y))
  (λ w → Sum.map (from-flat w neg x) (from-flat w pos y))
  (λ where b w (inj₁ a) → cong inj₁ (to-flat-project b w pos x a) ; b w (inj₂ a) → cong inj₂ (to-flat-project b w neg y a))
  (λ where b w (inj₁ a) → cong inj₁ (from-flat-project b w neg x a) ; b w (inj₂ a) → cong inj₂ (from-flat-project b w pos y a))
  (role-stable κ′ foreign p)
