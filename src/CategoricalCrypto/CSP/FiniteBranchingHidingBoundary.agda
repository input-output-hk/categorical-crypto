{-# OPTIONS --safe --without-K --guardedness #-}

-- Binary silent selection preserves every finite b.a* observation, but its
-- infinite selection path diverges only before b. Hiding a distinguishes
-- exact divergence after b even with finite total one-step branching.
module CategoricalCrypto.CSP.FiniteBranchingHidingBoundary where

open import Data.Bool.Base
open import Data.Empty
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base
open import Data.Nat.Base
open import Data.Nat.Properties using (+-suc)
open import Data.Product.Base hiding (map)
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

import CategoricalCrypto.CSP.FiniteBranching as Branching
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.Process as Process

data Event : Set where a b : Event

module O = Operators Event Bool (λ _ → true)
module L = Process Event O.Index ⊤
module P = Parallel Event Bool (λ _ → true)
module F = Branching Event O.Index ⊤
open O
open L
open L.Tree
open F

private variable
  t : Tree
  l : Label
  xs : List Visible

walk : ℕ → Tree
walk zero = stop
force (walk (suc n)) = react (λ { a → just (walk n); b → nothing }) (λ _ → nothing)

begin : ℕ → Tree
force (begin n) = react (λ { a → nothing; b → just (walk n) }) (λ _ → nothing)

mutual
  select : ℕ → Tree
  force (select n) = react (λ _ → nothing) (choose n)

  choose : ℕ → Index → Maybe Tree
  choose n (raw false) = just (select (suc n))
  choose n (raw true) = just (begin n)
  choose n _ = nothing

loop : Tree
force loop = react (λ { a → just loop; b → nothing }) (λ _ → nothing)

spec impl : Tree
spec = select zero
impl = begin-loop
  where
  begin-loop : Tree
  force begin-loop = react (λ { a → nothing; b → just loop }) (λ _ → nothing)

word : ℕ → List Visible
word zero = []
word (suc n) = event a ∷ word n

select-step : ∀ n {q} → select n ─[ l ]→ q
  → (l , q) ≡ (τ , select (suc n)) ⊎ (l , q) ≡ (τ , begin n)
select-step n (sRet ())
select-step n (sSil ())
select-step n (sVis refl ())
select-step n (sTau {i = raw false} refl refl) = inj₁ refl
select-step n (sTau {i = raw true} refl refl) = inj₂ refl
select-step n (sTau {i = left _} refl ())
select-step n (sTau {i = right _} refl ())
select-step n (sTau {i = silence} refl ())
select-step n (sTau {i = commitment _} refl ())
select-step n (sTau {i = concealed _} refl ())

stop-finite : FiniteSteps stop
FiniteSteps.successors stop-finite = []
FiniteSteps.sound stop-finite ()
FiniteSteps.cover stop-finite step = ⊥-elim (stop-no-step step)

walk-finite : ∀ n → FiniteSteps (walk n)
walk-finite zero = stop-finite
FiniteSteps.successors (walk-finite (suc n)) = (visible (event a) , walk n) ∷ []
FiniteSteps.sound (walk-finite (suc n)) (here refl) = sVis refl refl
FiniteSteps.sound (walk-finite (suc n)) (there ())
FiniteSteps.cover (walk-finite (suc n)) (sRet ())
FiniteSteps.cover (walk-finite (suc n)) (sSil ())
FiniteSteps.cover (walk-finite (suc n)) (sVis {e = a} refl refl) = here refl
FiniteSteps.cover (walk-finite (suc n)) (sVis {e = b} refl ())
FiniteSteps.cover (walk-finite (suc n)) (sTau refl ())

begin-finite : ∀ n → FiniteSteps (begin n)
FiniteSteps.successors (begin-finite n) = (visible (event b) , walk n) ∷ []
FiniteSteps.sound (begin-finite n) (here refl) = sVis refl refl
FiniteSteps.sound (begin-finite n) (there ())
FiniteSteps.cover (begin-finite n) (sRet ())
FiniteSteps.cover (begin-finite n) (sSil ())
FiniteSteps.cover (begin-finite n) (sVis {e = a} refl ())
FiniteSteps.cover (begin-finite n) (sVis {e = b} refl refl) = here refl
FiniteSteps.cover (begin-finite n) (sTau refl ())

select-finite : ∀ n → FiniteSteps (select n)
FiniteSteps.successors (select-finite n) = (τ , select (suc n)) ∷ (τ , begin n) ∷ []
FiniteSteps.sound (select-finite n) (here refl) = sTau {i = raw false} refl refl
FiniteSteps.sound (select-finite n) (there (here refl)) = sTau {i = raw true} refl refl
FiniteSteps.sound (select-finite n) (there (there ()))
FiniteSteps.cover (select-finite n) step with select-step n step
... | inj₁ refl = here refl
... | inj₂ refl = there (here refl)

loop-finite : FiniteSteps loop
FiniteSteps.successors loop-finite = (visible (event a) , loop) ∷ []
FiniteSteps.sound loop-finite (here refl) = sVis refl refl
FiniteSteps.sound loop-finite (there ())
FiniteSteps.cover loop-finite (sRet ())
FiniteSteps.cover loop-finite (sSil ())
FiniteSteps.cover loop-finite (sVis {e = a} refl refl) = here refl
FiniteSteps.cover loop-finite (sVis {e = b} refl ())
FiniteSteps.cover loop-finite (sTau refl ())

impl-finite : FiniteSteps impl
FiniteSteps.successors impl-finite = (visible (event b) , loop) ∷ []
FiniteSteps.sound impl-finite (here refl) = sVis refl refl
FiniteSteps.sound impl-finite (there ())
FiniteSteps.cover impl-finite (sRet ())
FiniteSteps.cover impl-finite (sSil ())
FiniteSteps.cover impl-finite (sVis {e = a} refl ())
FiniteSteps.cover impl-finite (sVis {e = b} refl refl) = here refl
FiniteSteps.cover impl-finite (sTau refl ())

stop-branching : FinitelyBranching stop
FinitelyBranching.finite stop-branching = stop-finite
FinitelyBranching.after stop-branching step = ⊥-elim (stop-no-step step)

walk-branching : ∀ n → FinitelyBranching (walk n)
FinitelyBranching.finite (walk-branching n) = walk-finite n
FinitelyBranching.after (walk-branching zero) step = ⊥-elim (stop-no-step step)
FinitelyBranching.after (walk-branching (suc n)) (sRet ())
FinitelyBranching.after (walk-branching (suc n)) (sSil ())
FinitelyBranching.after (walk-branching (suc n)) (sVis {e = a} refl refl) = walk-branching n
FinitelyBranching.after (walk-branching (suc n)) (sVis {e = b} refl ())
FinitelyBranching.after (walk-branching (suc n)) (sTau refl ())

begin-branching : ∀ n → FinitelyBranching (begin n)
FinitelyBranching.finite (begin-branching n) = begin-finite n
FinitelyBranching.after (begin-branching n) (sRet ())
FinitelyBranching.after (begin-branching n) (sSil ())
FinitelyBranching.after (begin-branching n) (sVis {e = a} refl ())
FinitelyBranching.after (begin-branching n) (sVis {e = b} refl refl) = walk-branching n
FinitelyBranching.after (begin-branching n) (sTau refl ())

select-branching : ∀ n → FinitelyBranching (select n)
FinitelyBranching.finite (select-branching n) = select-finite n
FinitelyBranching.after (select-branching n) step with select-step n step
... | inj₁ refl = select-branching (suc n)
... | inj₂ refl = begin-branching n

loop-branching : FinitelyBranching loop
FinitelyBranching.finite loop-branching = loop-finite
FinitelyBranching.after loop-branching (sRet ())
FinitelyBranching.after loop-branching (sSil ())
FinitelyBranching.after loop-branching (sVis {e = a} refl refl) = loop-branching
FinitelyBranching.after loop-branching (sVis {e = b} refl ())
FinitelyBranching.after loop-branching (sTau refl ())

impl-branching : FinitelyBranching impl
FinitelyBranching.finite impl-branching = impl-finite
FinitelyBranching.after impl-branching (sRet ())
FinitelyBranching.after impl-branching (sSil ())
FinitelyBranching.after impl-branching (sVis {e = a} refl ())
FinitelyBranching.after impl-branching (sVis {e = b} refl refl) = loop-branching
FinitelyBranching.after impl-branching (sTau refl ())

spec-branching : FinitelyBranching spec
spec-branching = select-branching zero

walk-noτ : ∀ n → ¬ (walk n ─[ τ ]→ t)
walk-noτ zero = stop-no-step
walk-noτ (suc n) (sSil ())
walk-noτ (suc n) (sTau refl ())

begin-noτ : ∀ n → ¬ (begin n ─[ τ ]→ t)
begin-noτ n (sSil ())
begin-noτ n (sTau refl ())

loop-noτ : ¬ (loop ─[ τ ]→ t)
loop-noτ (sSil ())
loop-noτ (sTau refl ())

impl-noτ : ¬ (impl ─[ τ ]→ t)
impl-noτ (sSil ())
impl-noτ (sTau refl ())

loop-path : Executes loop xs t → xs ≡ word (length xs)
loop-path done = refl
loop-path (silent-step step rest) = ⊥-elim (loop-noτ step)
loop-path (visible-step (sRet ()) rest)
loop-path (visible-step (sVis {e = a} refl refl) rest) = cong (event a ∷_) (loop-path rest)
loop-path (visible-step (sVis {e = b} refl ()) rest)

walk-executes : ∀ n → Executes (walk n) (word n) stop
walk-executes zero = done
walk-executes (suc n) = visible-step (sVis refl refl) (walk-executes n)

walk-prefix : ∀ n k → Executes (walk (n + k)) (word n) (walk k)
walk-prefix zero k = done
walk-prefix (suc n) k = visible-step (sVis refl refl) (walk-prefix n k)

select-prefix : ∀ n k {xs t} → Executes (select (n + k)) xs t → Executes (select k) xs t
select-prefix zero k path = path
select-prefix (suc n) k {xs} {t} path = silent-step (sTau {i = raw false} refl refl)
  (select-prefix n (suc k)
    (subst (λ j → Executes (select j) xs t) (sym (+-suc n k)) path))

select-executes : ∀ n k → Executes (select k) (event b ∷ word n) (walk k)
select-executes n k = select-prefix n k
  (silent-step (sTau {i = raw true} refl refl)
    (visible-step (sVis refl refl) (walk-prefix n k)))

trace-inclusion : ∀ xs → Trace impl xs → Trace spec xs
trace-inclusion .[] (_ , done) = spec , done
trace-inclusion xs (_ , silent-step step rest) = ⊥-elim (impl-noτ step)
trace-inclusion xs (_ , visible-step (sRet ()) rest)
trace-inclusion xs (_ , visible-step (sVis {e = a} refl ()) rest)
trace-inclusion (event b ∷ xs) (_ , visible-step (sVis {e = b} refl refl) rest) = stop ,
  subst (λ ys → Executes spec (event b ∷ ys) stop) (sym (loop-path rest))
    (select-executes (length xs) zero)

failure-inclusion : ∀ xs refusal → Failure impl xs refusal → Failure spec xs refusal
failure-inclusion .[] refusal (_ , done , stable , refuses) = begin zero ,
  silent-step (sTau {i = raw true} refl refl) done ,
  ((λ _ → begin-noτ zero) , (λ { _ _ (sRet ()) })) , reject
  where
  reject : ∀ e → refusal e → ∀ q → ¬ (begin zero ─[ visible e ]→ q)
  reject _ offered _ (sRet ())
  reject (event a) offered _ (sVis refl ())
  reject (event b) offered _ (sVis refl refl) = refuses (event b) offered loop (sVis refl refl)
failure-inclusion xs refusal (_ , silent-step step rest , refused) = ⊥-elim (impl-noτ step)
failure-inclusion xs refusal (_ , visible-step (sRet ()) rest , refused)
failure-inclusion xs refusal (_ , visible-step (sVis {e = a} refl ()) rest , refused)
failure-inclusion (event b ∷ xs) refusal (_ , visible-step (sVis {e = b} refl refl) rest , refused) = stop ,
  subst (λ ys → Executes spec (event b ∷ ys) stop) (sym (loop-path rest))
    (select-executes (length xs) zero) ,
  stable-stop , (λ _ _ _ → stop-no-step)

loop-no-divergence : ¬ (Divergence loop xs)
loop-no-divergence (_ , done , d) = loop-noτ (Diverges.step d)
loop-no-divergence (_ , silent-step step rest , d) = loop-noτ step
loop-no-divergence (_ , visible-step (sRet ()) rest , d)
loop-no-divergence (_ , visible-step (sVis {e = a} refl refl) rest , d) = loop-no-divergence (_ , rest , d)
loop-no-divergence (_ , visible-step (sVis {e = b} refl ()) rest , d)

impl-no-divergence : ¬ (Divergence impl xs)
impl-no-divergence (_ , done , d) = impl-noτ (Diverges.step d)
impl-no-divergence (_ , silent-step step rest , d) = impl-noτ step
impl-no-divergence (_ , visible-step (sRet ()) rest , d)
impl-no-divergence (_ , visible-step (sVis {e = a} refl ()) rest , d)
impl-no-divergence (_ , visible-step (sVis {e = b} refl refl) rest , d) = loop-no-divergence (_ , rest , d)

divergence-inclusion : ∀ xs → Divergence impl xs → Divergence spec xs
divergence-inclusion xs d = ⊥-elim (impl-no-divergence d)

select-diverges : ∀ n → Diverges (select n)
Diverges.next (select-diverges n) = select (suc n)
Diverges.step (select-diverges n) = sTau {i = raw false} refl refl
Diverges.rest (select-diverges n) = select-diverges (suc n)

spec-diverges-at-empty : Divergence spec []
spec-diverges-at-empty = spec , done , select-diverges zero

walk-no-divergence : ∀ n → ¬ (Divergence (walk n) xs)
walk-no-divergence zero (_ , done , d) = stop-not-divergent d
walk-no-divergence zero (_ , silent-step step rest , d) = stop-no-step step
walk-no-divergence zero (_ , visible-step step rest , d) = stop-no-step step
walk-no-divergence (suc n) (_ , done , d) = walk-noτ (suc n) (Diverges.step d)
walk-no-divergence (suc n) (_ , silent-step step rest , d) = walk-noτ (suc n) step
walk-no-divergence (suc n) (_ , visible-step (sRet ()) rest , d)
walk-no-divergence (suc n) (_ , visible-step (sVis {e = a} refl refl) rest , d) =
  walk-no-divergence n (_ , rest , d)
walk-no-divergence (suc n) (_ , visible-step (sVis {e = b} refl ()) rest , d)

begin-no-divergence : ∀ n → ¬ (Divergence (begin n) xs)
begin-no-divergence n (_ , done , d) = begin-noτ n (Diverges.step d)
begin-no-divergence n (_ , silent-step step rest , d) = begin-noτ n step
begin-no-divergence n (_ , visible-step (sRet ()) rest , d)
begin-no-divergence n (_ , visible-step (sVis {e = a} refl ()) rest , d)
begin-no-divergence n (_ , visible-step (sVis {e = b} refl refl) rest , d) =
  walk-no-divergence n (_ , rest , d)

select-after-b : ∀ n → Executes (select n) (event b ∷ xs) t → ¬ (Diverges t)
select-after-b n (silent-step (sSil ()) rest) d
select-after-b n (silent-step (sTau {i = raw false} refl refl) rest) d = select-after-b (suc n) rest d
select-after-b n (silent-step (sTau {i = raw true} refl refl) rest) d = begin-no-divergence n (_ , rest , d)
select-after-b n (silent-step (sTau {i = left _} refl ()) rest) d
select-after-b n (silent-step (sTau {i = right _} refl ()) rest) d
select-after-b n (silent-step (sTau {i = silence} refl ()) rest) d
select-after-b n (silent-step (sTau {i = commitment _} refl ()) rest) d
select-after-b n (silent-step (sTau {i = concealed _} refl ()) rest) d
select-after-b n (visible-step (sVis refl ()) rest) d

select-no-divergence-after-b : ∀ n → ¬ (Divergence (select n) (event b ∷ xs))
select-no-divergence-after-b n (_ , path , d) = select-after-b n path d

spec-no-exact-b-prefix : ∀ n → ¬ (Divergence spec (event b ∷ word n))
spec-no-exact-b-prefix n = select-no-divergence-after-b zero

hide-a : Event → Bool
hide-a a = true
hide-a b = false

hidden : Tree → Tree
hidden = Hide hide-a

hidden-loop-diverges : Diverges (hidden loop)
Diverges.next hidden-loop-diverges = hidden loop
Diverges.step hidden-loop-diverges = P.hide-hidden hide-a refl (sVis {e = a} refl refl)
Diverges.rest hidden-loop-diverges = hidden-loop-diverges

hidden-impl-exact-b : Divergence (hidden impl) (event b ∷ [])
hidden-impl-exact-b = hidden loop ,
  visible-step (P.hide-keep hide-a refl (sVis {e = b} refl refl)) done , hidden-loop-diverges

hidden-walk-no-divergence : ∀ n → ¬ (Divergence (hidden (walk n)) xs)
hidden-walk-no-divergence n (_ , done , d) = reject
  (P.hide-silent-invert hide-a (Diverges.step d)) (Diverges.rest d)
  where
  reject : ∀ {t} → P.HideSilent hide-a (walk n) t → Diverges t → ⊥
  reject (P.original step) tail = walk-noτ n step
  reject (P.concealed-event inside step) tail = finite n step tail
    where
    finite : ∀ n {e q} → walk n ─[ visible (event e) ]→ q → Diverges (hidden q) → ⊥
    finite zero step tail = stop-no-step step
    finite (suc n) (sVis {e = a} refl refl) tail = hidden-walk-no-divergence n (_ , done , tail)
    finite (suc n) (sVis {e = b} refl ()) tail
hidden-walk-no-divergence n (_ , silent-step step rest , d) = reject (P.hide-silent-invert hide-a step) rest d
  where
  reject : ∀ {q t xs} → P.HideSilent hide-a (walk n) q → Executes q xs t → Diverges t → ⊥
  reject (P.original step) rest d = walk-noτ n step
  reject (P.concealed-event inside step) rest d = finite n step rest d
    where
    finite : ∀ n {e q t xs} → walk n ─[ visible (event e) ]→ q
      → Executes (hidden q) xs t → Diverges t → ⊥
    finite zero step rest d = stop-no-step step
    finite (suc n) (sVis {e = a} refl refl) rest d = hidden-walk-no-divergence n (_ , rest , d)
    finite (suc n) (sVis {e = b} refl ()) rest d
hidden-walk-no-divergence zero (_ , visible-step (sRet ()) rest , d)
hidden-walk-no-divergence zero (_ , visible-step (sVis {e = a} refl ()) rest , d)
hidden-walk-no-divergence zero (_ , visible-step (sVis {e = b} refl ()) rest , d)
hidden-walk-no-divergence (suc n) (_ , visible-step (sRet ()) rest , d)
hidden-walk-no-divergence (suc n) (_ , visible-step (sVis {e = a} refl ()) rest , d)
hidden-walk-no-divergence (suc n) (_ , visible-step (sVis {e = b} refl ()) rest , d)

hidden-begin-no-divergence-after-b : ∀ n → ¬ (Divergence (hidden (begin n)) (event b ∷ xs))
hidden-begin-no-divergence-after-b n (_ , silent-step step rest , d) = reject (P.hide-silent-invert hide-a step)
  where
  reject : ∀ {q} → P.HideSilent hide-a (begin n) q → ⊥
  reject (P.original step) = begin-noτ n step
  reject (P.concealed-event {e = a} inside (sVis refl ()))
  reject (P.concealed-event {e = b} () step)
hidden-begin-no-divergence-after-b n (_ , visible-step (sVis refl refl) rest , d) =
  hidden-walk-no-divergence n (_ , rest , d)

hidden-select-after-b : ∀ n → Executes (hidden (select n)) (event b ∷ xs) t → ¬ (Diverges t)
hidden-select-after-b n (silent-step step rest) d with P.hide-silent-invert hide-a step
... | P.original (sSil ())
... | P.original (sTau {i = raw false} refl refl) = hidden-select-after-b (suc n) rest d
... | P.original (sTau {i = raw true} refl refl) = hidden-begin-no-divergence-after-b n (_ , rest , d)
... | P.original (sTau {i = left _} refl ())
... | P.original (sTau {i = right _} refl ())
... | P.original (sTau {i = silence} refl ())
... | P.original (sTau {i = commitment _} refl ())
... | P.original (sTau {i = concealed _} refl ())
... | P.concealed-event inside (sVis refl ())
hidden-select-after-b n (visible-step (sVis refl ()) rest) d

hidden-select-no-divergence-after-b : ∀ n → ¬ (Divergence (hidden (select n)) (event b ∷ xs))
hidden-select-no-divergence-after-b n (_ , path , d) = hidden-select-after-b n path d

hidden-spec-no-exact-b : ¬ (Divergence (hidden spec) (event b ∷ []))
hidden-spec-no-exact-b = hidden-select-no-divergence-after-b zero

hiding-breaks-exact-divergence-inclusion :
  ¬ (∀ xs → Divergence (hidden impl) xs → Divergence (hidden spec) xs)
hiding-breaks-exact-divergence-inclusion inclusion =
  hidden-spec-no-exact-b (inclusion (event b ∷ []) hidden-impl-exact-b)
