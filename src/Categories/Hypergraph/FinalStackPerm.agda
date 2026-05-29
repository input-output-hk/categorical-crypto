{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Generic combinatorial `final-stack-↭`, carrier-agnostic.
--
-- Given the four firing permutations of two independent edges fired in
-- both orders from a common stack `s`, the two final stacks are `_↭_`.
-- This is PURE permutation algebra on the stacks (no morphisms, no
-- hypergraph, no SMC) — so it is shared by both the APROP-level chase
-- (`Discharge/Sub/FinalStackPerm.agda`) and the SMC `Steps` level.
--
-- The construction augments both final stacks by the common prefix
-- `a₁ ++ a₂`, routes both through `b₂ ++ b₁ ++ s`, and cancels the
-- prefix with `++-cancelˡ-↭` (iterated `drop-∷`).
--
-- This needs CANCELLATION, which is genuinely not derivable from the
-- commutative-monoid structure of `_↭_` alone (a `(ℕ, max)` model
-- satisfies the four hypotheses but refutes the conclusion).  But
-- cancellation is a 4-line consequence of stdlib's `drop-∷`.
--
-- `--safe --without-K` clean.  No postulates.
--------------------------------------------------------------------------------

module Categories.Hypergraph.FinalStackPerm where

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp

private
  variable
    ℓ : Level
    A : Set ℓ

--------------------------------------------------------------------------------
-- ## list-prefix cancellation for `_↭_` (from stdlib `drop-∷`).

++-cancelˡ-↭
  : (pre : List A) {xs ys : List A}
  → pre ++ xs Perm.↭ pre ++ ys
  → xs Perm.↭ ys
++-cancelˡ-↭ []        p = p
++-cancelˡ-↭ (x ∷ pre) p = ++-cancelˡ-↭ pre (PermProp.drop-∷ p)

--------------------------------------------------------------------------------
-- ## The final-stack permutation.
--
-- Naming: aᵢ = ein eᵢ, bᵢ = eout eᵢ, rⱼ = the residual stacks.
--
--   p1  : s ↭ a₁ ++ r₁
--   p12 : b₁ ++ r₁ ↭ a₂ ++ r₁₂
--   p2  : s ↭ a₂ ++ r₂
--   p21 : b₂ ++ r₂ ↭ a₁ ++ r₂₁
--   ⇒   b₂ ++ r₁₂ ↭ b₁ ++ r₂₁

final-stack-↭
  : (a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ s : List A)
  → s Perm.↭ a₁ ++ r₁
  → b₁ ++ r₁ Perm.↭ a₂ ++ r₁₂
  → s Perm.↭ a₂ ++ r₂
  → b₂ ++ r₂ Perm.↭ a₁ ++ r₂₁
  → b₂ ++ r₁₂ Perm.↭ b₁ ++ r₂₁
final-stack-↭ a₁ b₁ a₂ b₂ r₁ r₁₂ r₂ r₂₁ s p1 p12 p2 p21 =
  ++-cancelˡ-↭ a₂ (++-cancelˡ-↭ a₁ augmented)
  where
    open Perm.PermutationReasoning

    -- LHS augmented by prefix (a₁ ++ a₂) routes to b₂ ++ b₁ ++ s.
    lhs-chain
      : a₁ ++ a₂ ++ b₂ ++ r₁₂ Perm.↭ b₂ ++ b₁ ++ s
    lhs-chain = begin
        a₁ ++ a₂ ++ b₂ ++ r₁₂
      ↭⟨ PermProp.++⁺ˡ a₁ (PermProp.shifts a₂ b₂) ⟩
        a₁ ++ b₂ ++ a₂ ++ r₁₂
      ↭⟨ PermProp.++⁺ˡ a₁ (PermProp.++⁺ˡ b₂ (Perm.↭-sym p12)) ⟩
        a₁ ++ b₂ ++ b₁ ++ r₁
      ↭⟨ PermProp.shifts a₁ b₂ ⟩
        b₂ ++ a₁ ++ b₁ ++ r₁
      ↭⟨ PermProp.++⁺ˡ b₂ (PermProp.shifts a₁ b₁) ⟩
        b₂ ++ b₁ ++ a₁ ++ r₁
      ↭⟨ PermProp.++⁺ˡ b₂ (PermProp.++⁺ˡ b₁ (Perm.↭-sym p1)) ⟩
        b₂ ++ b₁ ++ s
      ∎

    -- RHS augmented by prefix (a₁ ++ a₂) routes to b₂ ++ b₁ ++ s.
    rhs-chain
      : a₁ ++ a₂ ++ b₁ ++ r₂₁ Perm.↭ b₂ ++ b₁ ++ s
    rhs-chain = begin
        a₁ ++ a₂ ++ b₁ ++ r₂₁
      ↭⟨ PermProp.shifts a₁ a₂ ⟩
        a₂ ++ a₁ ++ b₁ ++ r₂₁
      ↭⟨ PermProp.++⁺ˡ a₂ (PermProp.shifts a₁ b₁) ⟩
        a₂ ++ b₁ ++ a₁ ++ r₂₁
      ↭⟨ PermProp.++⁺ˡ a₂ (PermProp.++⁺ˡ b₁ (Perm.↭-sym p21)) ⟩
        a₂ ++ b₁ ++ b₂ ++ r₂
      ↭⟨ PermProp.shifts a₂ b₁ ⟩
        b₁ ++ a₂ ++ b₂ ++ r₂
      ↭⟨ PermProp.++⁺ˡ b₁ (PermProp.shifts a₂ b₂) ⟩
        b₁ ++ b₂ ++ a₂ ++ r₂
      ↭⟨ PermProp.++⁺ˡ b₁ (PermProp.++⁺ˡ b₂ (Perm.↭-sym p2)) ⟩
        b₁ ++ b₂ ++ s
      ↭⟨ PermProp.shifts b₁ b₂ ⟩
        b₂ ++ b₁ ++ s
      ∎

    augmented
      : a₁ ++ a₂ ++ b₂ ++ r₁₂ Perm.↭ a₁ ++ a₂ ++ b₁ ++ r₂₁
    augmented = Perm.trans lhs-chain (Perm.↭-sym rhs-chain)
