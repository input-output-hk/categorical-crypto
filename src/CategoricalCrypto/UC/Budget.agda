{-# OPTIONS --safe --without-K #-}

-- Query budgets: the resource doctrine, one layer out from the qualitative
-- core.
--
-- Natural-number rates are a model datum, not part of general UC — a setup with
-- no cost algebra still has environments, simulators and `_≤UC_`.  So `Budget`
-- is a separate record, and the layers that want it (`UC.Audit`, `UC.Family`)
-- take it as a module parameter.

open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)

open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Nat.Properties
  using ( *-assoc; *-comm; *-identityʳ; *-mono-≤; *-monoˡ-≤; *-monoʳ-≤; m≤m⊔n; m≤n⊔m
        ; ⊔-assoc; ⊔-idem; ⊔-lub; ≤-reflexive; ≤-trans; module ≤-Reasoning )
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; sym; trans; module ≡-Reasoning)

module CategoricalCrypto.UC.Budget where

-- The closure properties the indexed family category consumes, and nothing
-- else: this record is PLUMBING, not the definition of a query bound.  A query
-- bound with content is the amortised-potential certificate of
-- `CategoricalCrypto.UC.QueryBound`, whose counting theorem is what forbids the
-- degenerate `QB c f = ⊤`; here `QB` is a parameter, so the laws alone cannot
-- forbid it.
--
-- Where the reference arc asked eleven laws, twelve stand, and the difference
-- is bookkeeping: its tensor law splits into `qb-T₁`/`qb-sub` (the two
-- one-sided actions).  A product law `qb-⊗₁` is not asked for because
-- `f ⊗₁ g ≈ f ⊗₁ id ∘ id ⊗₁ g`, so `qb-∘`/`qb-sub`/`qb-T₁`/`qb-resp-≈` already
-- certify it at `(c ⊔ 1) * (c′ ⊔ 1)`.
--
-- The four unitor certificates are what `UC.Family` spends to make the
-- levelwise category monoidal: the unitors of `Fam` are the base's, levelwise,
-- and a `Fam`-hom is a hom plus a polynomial bound.
record Budget {o ℓ e} (M : MonoidalCategory o ℓ e) (qs : Level)
            : Set (o ⊔ ℓ ⊔ e ⊔ suc qs) where
  open MonoidalCategory M

  field
    QB        : ℕ → {A B : Obj} → A ⇒ B → Set qs
    qb-id     : {A : Obj} → QB 1 (id {A})
    qb-∘      : {A B C : Obj} {c c′ : ℕ} {g : B ⇒ C} {f : A ⇒ B}
              → QB c g → QB c′ f → QB (c ℕ.* c′) (g ∘ f)
    qb-resp-≈ : {A B : Obj} {c : ℕ} {f g : A ⇒ B} → f ≈ g → QB c f → QB c g
    qb-mono   : {A B : Obj} {c c′ : ℕ} {f : A ⇒ B} → c ℕ.≤ c′ → QB c f → QB c′ f
    -- `_⊔ 1_`, not `c`: the bypassed interface's own downward relay is one
    -- completed event that an activation from above must have deposited for,
    -- so a rate of zero cannot survive the action.  This is the reference
    -- arc's `qb-⊗` at `c ⊔ 1`, the identity leg's budget being 1.
    qb-T₁     : {Y A B : Obj} {c : ℕ} {f : A ⇒ B} → QB c f → QB (c ℕ.⊔ 1) (id {Y} ⊗₁ f)
    qb-sub    : {X Y A : Obj} {c : ℕ} {s : X ⇒ Y} → QB c s → QB (c ℕ.⊔ 1) (s ⊗₁ id {A})
    qb-a⇒     : {X Y A : Obj} → QB 1 (associator.to {X} {Y} {A})
    qb-a⇐     : {X Y A : Obj} → QB 1 (associator.from {X} {Y} {A})
    qb-λ⇒     : {A : Obj} → QB 1 (unitorˡ.from {A})
    qb-λ⇐     : {A : Obj} → QB 1 (unitorˡ.to {A})
    qb-ρ⇒     : {A : Obj} → QB 1 (unitorʳ.from {A})
    qb-ρ⇐     : {A : Obj} → QB 1 (unitorʳ.to {A})

-- The budget a context's two legs afford a strategy playing in its place.  The
-- test's own `c` is what bounds crossings into the plugged interface: the
-- closure of a CLOSED context supplies only ancilla and input responses, so the
-- conservative bound is `c` alone.  The product form is kept for the closures
-- that do relay downwards, but GUARDED at `c′ ⊔ 1`, because a closure with no
-- downward port certifies at `QB 0` and an unguarded `c * 0` charges a context
-- that genuinely queries to a strategy that cannot query at all (external theory
-- review, finding 1).  This is `qb-T₁`'s `c ⊔ 1` guard, one level up and for the
-- same reason.  The principled eventual form is a port-specific bound on
-- crossings into the DISTINGUISHED hole rather than a product of two whole-hom
-- budgets; `docs/protocol-rewrite.md` prices it, and it is not built.
ctxBudget : ℕ → ℕ → ℕ
ctxBudget c c′ = c ℕ.* (c′ ℕ.⊔ 1)

-- What absorbing a morphism of cost `cs` into a context's test costs the
-- strategy playing in that context's place: the allowance rescaled by the
-- absorbed morphism's own budget, guarded exactly as `ctxBudget` guards its.
simCost : ℕ → ℕ → ℕ
simCost q cs = q ℕ.* (cs ℕ.⊔ 1)

-- The guard is what makes the rescaling an INCREASE, whatever the absorbed
-- morphism costs: an adversary the original budget affords the adjusted one
-- affords too.
q≤simCost : (q cs : ℕ) → q ℕ.≤ simCost q cs
q≤simCost q cs = ≤-trans (≤-reflexive (sym (*-identityʳ q))) (*-monoʳ-≤ q (m≤n⊔m cs 1))

-- …and it does not matter which of the context's two legs is charged, which is
-- what lets an absorption be read as a substitution in the allowance alone.
-- Absorptions reach the test through `qb-∘`, so this is the whole arithmetic
-- of every allowance substitution below the quantitative composition theorems.
ctxBudget-simCost : (c c′ cs : ℕ)
                  → ctxBudget (c ℕ.* (cs ℕ.⊔ 1)) c′ ≡ simCost (ctxBudget c c′) cs
ctxBudget-simCost c c′ cs = begin
  (c ℕ.* (cs ℕ.⊔ 1)) ℕ.* (c′ ℕ.⊔ 1)  ≡⟨ *-assoc c (cs ℕ.⊔ 1) (c′ ℕ.⊔ 1) ⟩
  c ℕ.* ((cs ℕ.⊔ 1) ℕ.* (c′ ℕ.⊔ 1))  ≡⟨ cong (c ℕ.*_) (*-comm (cs ℕ.⊔ 1) (c′ ℕ.⊔ 1)) ⟩
  c ℕ.* ((c′ ℕ.⊔ 1) ℕ.* (cs ℕ.⊔ 1))  ≡⟨ *-assoc c (c′ ℕ.⊔ 1) (cs ℕ.⊔ 1) ⟨
  (c ℕ.* (c′ ℕ.⊔ 1)) ℕ.* (cs ℕ.⊔ 1)  ∎
  where open ≡-Reasoning

-- The same, at the budget `qb-sub ∘ qb-T₁` actually hands back: the guard is
-- idempotent, so absorbing through the action costs no more than absorbing.
ctxBudget-absorb : (c c′ cs : ℕ)
                 → ctxBudget (c ℕ.* ((cs ℕ.⊔ 1) ℕ.⊔ 1)) c′ ≡ simCost (ctxBudget c c′) cs
ctxBudget-absorb c c′ cs =
  trans (cong (λ k → ctxBudget (c ℕ.* k) c′)
              (trans (⊔-assoc cs 1 1) (cong (cs ℕ.⊔_) (⊔-idem 1))))
        (ctxBudget-simCost c c′ cs)

-- Absorbing into the CLOSURE instead: `ctxBudget` guards its second leg rather
-- than multiplying by it, so what comes out is a BOUND where the two identities
-- above are exact.  This is why a composition that moves a process into a
-- closure needs the schedule's monotonicity and one that moves a morphism into
-- a test does not.
ctxBudget-closure≤ : (c c′ cs : ℕ)
                   → ctxBudget c ((cs ℕ.⊔ 1) ℕ.* c′) ℕ.≤ simCost (ctxBudget c c′) cs
ctxBudget-closure≤ c c′ cs = begin
  c ℕ.* (((cs ℕ.⊔ 1) ℕ.* c′) ℕ.⊔ 1)  ≤⟨ *-monoʳ-≤ c inner ⟩
  c ℕ.* ((c′ ℕ.⊔ 1) ℕ.* (cs ℕ.⊔ 1))  ≡⟨ *-assoc c (c′ ℕ.⊔ 1) (cs ℕ.⊔ 1) ⟨
  (c ℕ.* (c′ ℕ.⊔ 1)) ℕ.* (cs ℕ.⊔ 1)  ∎
  where
  open ≤-Reasoning

  inner : ((cs ℕ.⊔ 1) ℕ.* c′) ℕ.⊔ 1 ℕ.≤ (c′ ℕ.⊔ 1) ℕ.* (cs ℕ.⊔ 1)
  inner = ⊔-lub (≤-trans (≤-reflexive (*-comm (cs ℕ.⊔ 1) c′))
                         (*-monoˡ-≤ (cs ℕ.⊔ 1) (m≤m⊔n c′ 1)))
                (*-mono-≤ (m≤n⊔m c′ 1) (m≤n⊔m cs 1))
