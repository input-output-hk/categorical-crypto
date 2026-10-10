{-# OPTIONS --safe --without-K #-}

-- Pairing and randomised symmetric encryption: the signature Σ₀ and the
-- equations E₀ of `comonlundhcortier2008` Examples 3.1 and 3.3 (pp. 9–10),
-- oriented into a convergent rewrite system.  `nf` computes normal forms
-- bottom up and `E₀` decides `=E` by comparing them; `≈E⇔⟷*` shows that this
-- is the equational theory the three rules generate.

module CategoricalCrypto.Symbolic.Term.PairEnc where

open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat
open import Data.Nat.Induction
open import Data.Product
open import Data.Unit
open import Function.Base
open import Function.Bundles using (_⇔_; mk⇔)
open import Induction.WellFounded
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure; symmetric)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import CategoricalCrypto.Symbolic.Term

import Data.Nat.Properties as ℕ
import Relation.Binary.Construct.On as On

data Op : Set where
  pair fst snd enc dec : Op
  cst                  : ℕ → Op   -- public constants, CLC's `0ₗ` among them

-- `enc` takes plaintext, key and randomness: CLC's `{x}ʳₖ`.
arity : Op → List ⊤
arity pair    = tt ∷ tt ∷ []
arity fst     = tt ∷ []
arity snd     = tt ∷ []
arity enc     = tt ∷ tt ∷ tt ∷ []
arity dec     = tt ∷ tt ∷ []
arity (cst _) = []

private
  code : Op → ℕ
  code pair    = 0
  code fst     = 1
  code snd     = 2
  code enc     = 3
  code dec     = 4
  code (cst n) = 5 + n

  code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′
  code-injective {pair}  {pair}  refl = refl
  code-injective {fst}   {fst}   refl = refl
  code-injective {snd}   {snd}   refl = refl
  code-injective {enc}   {enc}   refl = refl
  code-injective {dec}   {dec}   refl = refl
  code-injective {cst _} {cst _} refl = refl

_≟ᵒ_ : DecidableEquality Op
o ≟ᵒ o′ = map′ code-injective (cong code) (code o ℕ.≟ code o′)

Σ₀ : Signature
Σ₀ = record
  { Sort = ⊤ ; Sym = Op ; dom = arity ; cod = λ _ → tt ; _≟ˢ_ = λ _ _ → yes refl ; _≟ᶠ_ = _≟ᵒ_ }

open Terms Σ₀

Msg : Set
Msg = Tm tt

pattern ⟪_,_⟫ x y        = app pair (x ∷ y ∷ [])
pattern π₁ t             = app fst (t ∷ [])
pattern π₂ t             = app snd (t ∷ [])
pattern enc⟨_,_,_⟩ x k r = app enc (x ∷ k ∷ r ∷ [])
pattern dec⟨_,_⟩ c k     = app dec (c ∷ k ∷ [])

private variable
  ss              : List ⊤
  x y k k′ r t u v : Msg
  ts us           : All Tm ss
  f               : Op

------------------------------------------------------------------------
-- The rewrite system

infix 4 _⟶ʳ_ _⟶_ _⟶ᵃ_ _⟶*_

-- E₀, oriented
data _⟶ʳ_ : Msg → Msg → Set where
  π₁⟨,⟩   : π₁ ⟪ x , y ⟫ ⟶ʳ x
  π₂⟨,⟩   : π₂ ⟪ x , y ⟫ ⟶ʳ y
  dec-enc : dec⟨ enc⟨ x , k , r ⟩ , k ⟩ ⟶ʳ x

-- one step anywhere in a term, or anywhere in one component of a tuple
data _⟶_ : Msg → Msg → Set
data _⟶ᵃ_ : ∀ {ss} → All Tm ss → All Tm ss → Set

data _⟶_ where
  root : t ⟶ʳ u → t ⟶ u
  arg  : ts ⟶ᵃ us → app f ts ⟶ app f us

data _⟶ᵃ_ where
  here  : t ⟶ u → (t ∷ ts) ⟶ᵃ (u ∷ ts)
  there : ts ⟶ᵃ us → (t ∷ ts) ⟶ᵃ (t ∷ us)

_⟶*_ : Msg → Msg → Set
_⟶*_ = Star _⟶_

Normal : Msg → Set
Normal t = ∀ {u} → ¬ t ⟶ u

------------------------------------------------------------------------
-- Normal forms

π₁′ π₂′ : Msg → Msg
π₁′ ⟪ x , _ ⟫ = x
π₁′ t         = π₁ t
π₂′ ⟪ _ , y ⟫ = y
π₂′ t         = π₂ t

dec′ : Msg → Msg → Msg
dec′ c@(enc⟨ x , k′ , _ ⟩) k with k ≟ᵗ k′
... | yes _ = x
... | no _  = dec⟨ c , k ⟩
dec′ c k = dec⟨ c , k ⟩

-- application to normal arguments: a destructor meeting its constructor contracts
app↓ : (f : Op) → All Tm (arity f) → Msg
app↓ fst (t ∷ [])     = π₁′ t
app↓ snd (t ∷ [])     = π₂′ t
app↓ dec (c ∷ k ∷ []) = dec′ c k
app↓ f   ts           = app f ts

nf  : Msg → Msg
nf* : All Tm ss → All Tm ss
nf (name n)   = name n
nf (app f ts) = app↓ f (nf* ts)
nf* []       = []
nf* (t ∷ ts) = nf t ∷ nf* ts

-- `app↓` contracts a root redex, or there is none.
data Head (f : Op) (us : All Tm (arity f)) : Msg → Set where
  contract : app f us ⟶ʳ u → Head f us u
  stuck    : (∀ {u} → ¬ app f us ⟶ʳ u) → Head f us (app f us)

private
  dec-stuck : ¬ k ≡ k′ → ¬ dec⟨ enc⟨ x , k′ , r ⟩ , k ⟩ ⟶ʳ u
  dec-stuck k≢k′ dec-enc = k≢k′ refl

app↓-view : ∀ f us → Head f us (app↓ f us)
app↓-view pair    _                         = stuck λ ()
app↓-view enc     _                         = stuck λ ()
app↓-view (cst _) _                         = stuck λ ()
app↓-view fst     (⟪ _ , _ ⟫ ∷ [])          = contract π₁⟨,⟩
app↓-view fst     (name _ ∷ [])             = stuck λ ()
app↓-view fst     (π₁ _ ∷ [])               = stuck λ ()
app↓-view fst     (π₂ _ ∷ [])               = stuck λ ()
app↓-view fst     (enc⟨ _ , _ , _ ⟩ ∷ [])   = stuck λ ()
app↓-view fst     (dec⟨ _ , _ ⟩ ∷ [])       = stuck λ ()
app↓-view fst     (app (cst _) [] ∷ [])     = stuck λ ()
app↓-view snd     (⟪ _ , _ ⟫ ∷ [])          = contract π₂⟨,⟩
app↓-view snd     (name _ ∷ [])             = stuck λ ()
app↓-view snd     (π₁ _ ∷ [])               = stuck λ ()
app↓-view snd     (π₂ _ ∷ [])               = stuck λ ()
app↓-view snd     (enc⟨ _ , _ , _ ⟩ ∷ [])   = stuck λ ()
app↓-view snd     (dec⟨ _ , _ ⟩ ∷ [])       = stuck λ ()
app↓-view snd     (app (cst _) [] ∷ [])     = stuck λ ()
app↓-view dec     (enc⟨ _ , k′ , _ ⟩ ∷ k ∷ []) with k ≟ᵗ k′
... | yes refl = contract dec-enc
... | no k≢k′  = stuck (dec-stuck k≢k′)
app↓-view dec     (name _ ∷ _ ∷ [])         = stuck λ ()
app↓-view dec     (⟪ _ , _ ⟫ ∷ _ ∷ [])      = stuck λ ()
app↓-view dec     (π₁ _ ∷ _ ∷ [])           = stuck λ ()
app↓-view dec     (π₂ _ ∷ _ ∷ [])           = stuck λ ()
app↓-view dec     (dec⟨ _ , _ ⟩ ∷ _ ∷ [])   = stuck λ ()
app↓-view dec     (app (cst _) [] ∷ _ ∷ []) = stuck λ ()

private
  ∷-cong : {t u : Msg} {ts us : All Tm ss} → t ≡ u → ts ≡ us → (All Tm (tt ∷ ss) ∋ t ∷ ts) ≡ u ∷ us
  ∷-cong refl refl = refl

  normal-args : Each Normal us → ∀ {vs} → ¬ us ⟶ᵃ vs
  normal-args (n ∷ _)  (here s)  = n s
  normal-args (_ ∷ ns) (there a) = normal-args ns a

  ⟶ʳ-normal : Each Normal us → app f us ⟶ʳ u → Normal u
  ⟶ʳ-normal (n ∷ [])     π₁⟨,⟩   s = n (arg (here s))
  ⟶ʳ-normal (n ∷ [])     π₂⟨,⟩   s = n (arg (there (here s)))
  ⟶ʳ-normal (n ∷ _ ∷ []) dec-enc s = n (arg (here s))

nf-normal  : (t : Msg) → Normal (nf t)
nf-normal* : (ts : All Tm ss) → Each Normal (nf* ts)
nf-normal (name _) (root ())
nf-normal (app f ts) with app↓ f (nf* ts) | app↓-view f (nf* ts)
... | _ | contract r = ⟶ʳ-normal (nf-normal* ts) r
... | _ | stuck ¬r   = λ { (root r) → ¬r r ; (arg a) → normal-args (nf-normal* ts) a }
nf-normal* []       = []
nf-normal* (t ∷ ts) = nf-normal t ∷ nf-normal* ts

nf-reduces  : (t : Msg) → t ⟶* nf t
nf-reduces* : (ts : All Tm ss) → Star _⟶ᵃ_ ts (nf* ts)
nf-reduces (name _)   = ε
nf-reduces (app f ts) = gmap (app f) arg (nf-reduces* ts) ◅◅ contract* f (nf* ts)
  where
  contract* : ∀ f us → app f us ⟶* app↓ f us
  contract* f us with app↓ f us | app↓-view f us
  ... | _ | contract r = root r ◅ ε
  ... | _ | stuck _    = ε
nf-reduces* []       = ε
nf-reduces* (t ∷ ts) = gmap (_∷ ts) here (nf-reduces t) ◅◅ gmap (nf t ∷_) there (nf-reduces* ts)

⟶-nf  : t ⟶ u → nf t ≡ nf u
⟶ᵃ-nf : ts ⟶ᵃ us → nf* ts ≡ nf* us
⟶-nf (root π₁⟨,⟩) = refl
⟶-nf (root π₂⟨,⟩) = refl
⟶-nf (root (dec-enc {k = k})) with nf k ≟ᵗ nf k
... | yes _  = refl
... | no k≢k = ⊥-elim (k≢k refl)
⟶-nf (arg {f = f} a) = cong (app↓ f) (⟶ᵃ-nf a)
⟶ᵃ-nf (here s)  = ∷-cong (⟶-nf s) refl
⟶ᵃ-nf (there a) = ∷-cong refl (⟶ᵃ-nf a)

⟶*-nf : t ⟶* u → nf t ≡ nf u
⟶*-nf ε        = refl
⟶*-nf (s ◅ ss) = trans (⟶-nf s) (⟶*-nf ss)

-- Every rule shrinks the term, so the system terminates.
size  : Msg → ℕ
size* : All Tm ss → ℕ
size (name _)   = 1
size (app _ ts) = suc (size* ts)
size* []       = 0
size* (t ∷ ts) = size t + size* ts

private
  sub₁ : ∀ t (ts : All Tm ss) → size t < suc (size* (t ∷ ts))
  sub₁ t ts = s≤s (ℕ.m≤m+n (size t) (size* ts))

  sub₂ : ∀ t u (ts : All Tm ss) → size u < suc (size* (t ∷ u ∷ ts))
  sub₂ t u ts = s≤s (ℕ.≤-trans (ℕ.m≤m+n (size u) (size* ts)) (ℕ.m≤n+m _ (size t)))

⟶-size  : t ⟶ u → size u < size t
⟶ᵃ-size : ts ⟶ᵃ us → size* us < size* ts
⟶-size (root (π₁⟨,⟩ {x} {y}))       = ℕ.<-trans (sub₁ x (y ∷ [])) (sub₁ ⟪ x , y ⟫ [])
⟶-size (root (π₂⟨,⟩ {x} {y}))       = ℕ.<-trans (sub₂ x y []) (sub₁ ⟪ x , y ⟫ [])
⟶-size (root (dec-enc {x} {k} {r})) = ℕ.<-trans (sub₁ x (k ∷ r ∷ [])) (sub₁ enc⟨ x , k , r ⟩ (k ∷ []))
⟶-size (arg a)        = s≤s (⟶ᵃ-size a)
⟶ᵃ-size {ts = _ ∷ ts} (here s) = ℕ.+-monoˡ-< (size* ts) (⟶-size s)
⟶ᵃ-size {ts = t ∷ _}  (there a) = ℕ.+-monoʳ-< (size t) (⟶ᵃ-size a)

terminating : WellFounded (flip _⟶_)
terminating = Subrelation.wellFounded ⟶-size (On.wellFounded size <-wellFounded)

confluent : t ⟶* u → t ⟶* v → ∃[ w ] u ⟶* w × v ⟶* w
confluent {t} {u} {v} p q =
  nf t , subst (u ⟶*_) (sym (⟶*-nf p)) (nf-reduces u) , subst (v ⟶*_) (sym (⟶*-nf q)) (nf-reduces v)

------------------------------------------------------------------------
-- The equational theory

private
  ⟶-ren  : ∀ ρ → t ⟶ u → ren ρ t ⟶ ren ρ u
  ⟶ᵃ-ren : ∀ ρ → ts ⟶ᵃ us → ren* ρ ts ⟶ᵃ ren* ρ us
  ⟶-ren ρ (root π₁⟨,⟩)   = root π₁⟨,⟩
  ⟶-ren ρ (root π₂⟨,⟩)   = root π₂⟨,⟩
  ⟶-ren ρ (root dec-enc) = root dec-enc
  ⟶-ren ρ (arg a)        = arg (⟶ᵃ-ren ρ a)
  ⟶ᵃ-ren ρ (here s)  = here (⟶-ren ρ s)
  ⟶ᵃ-ren ρ (there a) = there (⟶ᵃ-ren ρ a)

  nf-ren : ∀ ρ t → nf (ren ρ t) ≡ nf (ren ρ (nf t))
  nf-ren ρ t = ⟶*-nf (gmap (ren ρ) (⟶-ren ρ) (nf-reduces t))

  All₂-nf : All₂ (λ t u → nf t ≡ nf u) ts us → nf* ts ≡ nf* us
  All₂-nf []       = refl
  All₂-nf (e ∷ es) = ∷-cong e (All₂-nf es)

E₀ : EqTheory Σ₀
E₀ = record
  { _≈E_       = λ t u → nf t ≡ nf u
  ; isEquiv    = record { refl = refl ; sym = sym ; trans = trans }
  ; app-cong   = λ f es → cong (app↓ f) (All₂-nf es)
  ; ren-cong   = λ ρ {_} {t} {u} e →
      trans (nf-ren ρ t) (trans (cong (nf ∘ ren ρ) e) (sym (nf-ren ρ u)))
  ; _≟E_       = λ t u → nf t ≟ᵗ nf u
  ; nontrivial = λ _ → name (0 , 0) , name (0 , 1) , λ ()
  }

≈E⇔⟷* : nf t ≡ nf u ⇔ EqClosure _⟶_ t u
≈E⇔⟷* {t} {u} = mk⇔ to from
  where
  forward : ∀ {t u} → t ⟶* u → EqClosure _⟶_ t u
  forward = gmap id fwd
  to : nf t ≡ nf u → EqClosure _⟶_ t u
  to e = forward (nf-reduces t) ◅◅ subst (λ w → EqClosure _⟶_ w u) (sym e) (symmetric _⟶_ (forward (nf-reduces u)))
  from : ∀ {t u} → EqClosure _⟶_ t u → nf t ≡ nf u
  from ε             = refl
  from (fwd s ◅ ss) = trans (⟶-nf s) (from ss)
  from (bwd s ◅ ss) = trans (sym (⟶-nf s)) (from ss)
