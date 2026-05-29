{-# OPTIONS --safe --with-K #-}

--------------------------------------------------------------------------------
-- Step ① of the discharge plan: `process-steps-final-↭`.
--
-- The final stack of `process-steps` respects an edge-permutation:
--
--   es ↭ es'  →  proj₁ (process-steps es s af) ↭ proj₁ (process-steps es' s af')
--
-- Proved via a NET-MULTISET INVARIANT
--
--   proj₁ (process-steps es s af) ++ consumed es  ↭  s ++ produced es
--
-- which inducts on the edge LIST (so no intermediate `AllFire` witness is
-- needed — sidestepping the `trans`-case problem of an induction on the
-- edge-permutation).  The permutation then enters only through pure
-- list-`↭` lemmas (`consumed`/`produced` respect `↭`) plus cancellation.
--
-- `--safe`.  No postulates.  Vlab-independent (the stack fold ignores
-- the morphisms), but stated over `Steps n vlab` to match `Steps`.
--------------------------------------------------------------------------------

open import Categories.FreeMonoidal

module Categories.FreeSMC.ProcessFinal
  (d : FreeMonoidalData) ⦃ s≤v : Symm ≤ FreeMonoidalData.v d ⦄ where

open FreeMonoidalData d using (X)
open import Categories.FreeSMC.Steps d
open import Categories.Hypergraph.FinalStackPerm using (++-cancelˡ-↭)

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (ℕ)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermProp
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

private
  variable
    n : ℕ
    vlab : Fin n → X

--------------------------------------------------------------------------------
-- ## `boundary`: concatenated input/output lists of an edge sequence.

boundary
  : ∀ (h : Step n vlab → List (Fin n)) → Steps n vlab → List (Fin n)
boundary h []       = []
boundary h (e ∷ es) = h e ++ boundary h es

consumed produced : Steps n vlab → List (Fin n)
consumed {n} {vlab} = boundary (ein-of  n vlab)
produced {n} {vlab} = boundary (eout-of n vlab)

-- `boundary h` respects an edge-permutation.
boundary-resp-↭
  : ∀ (h : Step n vlab → List (Fin n)) {es es' : Steps n vlab}
  → es Perm.↭ es'
  → boundary h es Perm.↭ boundary h es'
boundary-resp-↭ h Perm.refl              = Perm.refl
boundary-resp-↭ h (Perm.prep e p)        = PermProp.++⁺ˡ (h e) (boundary-resp-↭ h p)
boundary-resp-↭ h (Perm.swap e₁ e₂ p)    =
  Perm.trans (PermProp.++⁺ˡ (h e₁) (PermProp.++⁺ˡ (h e₂) (boundary-resp-↭ h p)))
             (PermProp.shifts (h e₁) (h e₂))
boundary-resp-↭ h (Perm.trans p q)       =
  Perm.trans (boundary-resp-↭ h p) (boundary-resp-↭ h q)

--------------------------------------------------------------------------------
-- ## The net-multiset invariant.

process-net
  : ∀ (n : ℕ) (vlab : Fin n → X)
      (es : Steps n vlab) (s : List (Fin n)) (af : AllFire n vlab es s)
  → proj₁ (process-steps n vlab es s af) ++ consumed es
    Perm.↭
    s ++ produced es
process-net n vlab []                       s _ = Perm.↭-refl
process-net n vlab ((ein , eout , op) ∷ es) s (rest , perm , af) =
  let F  = proj₁ (process-steps n vlab es (eout ++ rest) af)
      ih = process-net n vlab es (eout ++ rest) af
  in begin
       F ++ (ein ++ consumed es)
         ↭⟨ PermProp.shifts F ein ⟩
       ein ++ (F ++ consumed es)
         ↭⟨ PermProp.++⁺ˡ ein ih ⟩
       ein ++ ((eout ++ rest) ++ produced es)
         ↭⟨ PermProp.++⁺ˡ ein (Perm.↭-reflexive (++-assoc eout rest (produced es))) ⟩
       ein ++ (eout ++ (rest ++ produced es))
         ↭⟨ PermProp.shifts ein eout ⟩
       eout ++ (ein ++ (rest ++ produced es))
         ↭⟨ PermProp.++⁺ˡ eout (Perm.↭-reflexive (sym (++-assoc ein rest (produced es)))) ⟩
       eout ++ ((ein ++ rest) ++ produced es)
         ↭⟨ PermProp.++⁺ˡ eout (PermProp.++⁺ʳ (produced es) (Perm.↭-sym perm)) ⟩
       eout ++ (s ++ produced es)
         ↭⟨ PermProp.shifts eout s ⟩
       s ++ (eout ++ produced es)
     ∎
  where open Perm.PermutationReasoning

--------------------------------------------------------------------------------
-- ## Right-cancellation (from the left-cancellation in FinalStackPerm).

++-cancelʳ-↭
  : ∀ {xs ys : List (Fin n)} (zs : List (Fin n))
  → xs ++ zs Perm.↭ ys ++ zs
  → xs Perm.↭ ys
++-cancelʳ-↭ {xs = xs} {ys} zs p =
  ++-cancelˡ-↭ zs
    (Perm.trans (PermProp.++-comm zs xs)
                (Perm.trans p (PermProp.++-comm ys zs)))

--------------------------------------------------------------------------------
-- ## The headline: final stack respects an edge-permutation.

process-steps-final-↭
  : ∀ (n : ℕ) (vlab : Fin n → X)
      (es es' : Steps n vlab) (s : List (Fin n))
      (es-↭ : es Perm.↭ es')
      (af : AllFire n vlab es s) (af' : AllFire n vlab es' s)
  → proj₁ (process-steps n vlab es  s af)
    Perm.↭
    proj₁ (process-steps n vlab es' s af')
process-steps-final-↭ n vlab es es' s es-↭ af af' =
  ++-cancelʳ-↭ (consumed es')
    (begin
       proj₁ (process-steps n vlab es s af) ++ consumed es'
         ↭⟨ PermProp.++⁺ˡ _ (Perm.↭-sym (boundary-resp-↭ (ein-of n vlab) es-↭)) ⟩
       proj₁ (process-steps n vlab es s af) ++ consumed es
         ↭⟨ process-net n vlab es s af ⟩
       s ++ produced es
         ↭⟨ PermProp.++⁺ˡ s (boundary-resp-↭ (eout-of n vlab) es-↭) ⟩
       s ++ produced es'
         ↭⟨ Perm.↭-sym (process-net n vlab es' s af') ⟩
       proj₁ (process-steps n vlab es' s af') ++ consumed es'
     ∎)
  where open Perm.PermutationReasoning
