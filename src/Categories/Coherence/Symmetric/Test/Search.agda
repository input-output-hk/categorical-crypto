{-# OPTIONS --safe --without-K #-}

-- Ordered enumeration is observable by deep rewriting, not just by searchIso.
-- Exercise the matching kernel directly so both sides of the index cutoff and
-- nonempty initial maps are covered independently of graph translation.
module Categories.Coherence.Symmetric.Test.Search where

open import Categories.APROP
open import Categories.APROP.Hypergraph.Model.Core
open import Categories.APROP.Hypergraph.Model.Iso
import Categories.APROP.Hypergraph.Model.FromAPROP as FromAPROP
import Categories.APROP.Hypergraph.Solver.FinSignature as FinSignature
open import Categories.APROP.Hypergraph.Solver.Match.PBij
import Categories.APROP.Hypergraph.Solver.Match.Search as Search
import Categories.APROP.Hypergraph.Solver.Match.Verify as Verify
import Categories.APROP.Hypergraph.Solver.Rewrite.SubMatch as SubMatch
open import Categories.FreeMonoidal

open import Data.Bool.Base
open import Data.Fin as Fin using (Fin; zero; suc; toℕ; inject₁; fromℕ)
import Data.Fin.Properties as Fin
open import Data.List.Base
open import Data.Maybe.Base as Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat as Nat
open import Data.Product using (_×_; _,_; proj₂)
open import Function
open import Relation.Binary.PropositionalEquality

private
  open FreeMonoidalHelper Symm (Fin 1)

  arity : Fin 2 → ObjTerm × ObjTerm
  arity zero = unit , unit
  arity (suc zero) = Var zero , Var zero

  module Sig = FinSignature Fin._≟_ arity
  open FromAPROP Sig.finSig
  open Search Sig.finSig
  module V = Verify Sig.finSig
  open SubMatch Sig.finSig

  scalars : ℕ → Hypergraph FlatGen
  scalars n = record
    { nV = 0 ; vlab = λ () ; nE = n
    ; ein = λ _ → [] ; eout = λ _ → []
    ; elab = λ _ → flat (Sig.gen zero)
    ; dom = [] ; cod = [] }

  chain : ℕ → Hypergraph FlatGen
  chain n = record
    { nV = Nat.suc n ; vlab = λ _ → zero ; nE = n
    ; ein = λ e → inject₁ e ∷ [] ; eout = λ e → suc e ∷ []
    ; elab = λ _ → flat (Sig.gen (suc zero))
    ; dom = zero ∷ [] ; cod = fromℕ n ∷ [] }

  identity : ∀ {n} → PBij n n
  identity = record { forward = just ; backward = just }

  images : ∀ {n m} → PBij n m → List (Maybe ℕ)
  images {n} ψ = map (Maybe.map toℕ ∘ forward ψ) (allFin n)

  shifted : ℕ → ℕ → List (Maybe ℕ)
  shifted n k = map (just ∘ (k +_) ∘ toℕ) (allFin n)

  results : (H J : Hypergraph FlatGen)
          → PBij (Hypergraph.nV H) (Hypergraph.nV J)
          → PBij (Hypergraph.nE H) (Hypergraph.nE J) → List (List (Maybe ℕ))
  results H J φ ψ = map (images ∘ proj₂) (searchAll H J φ ψ)

  certified : (H J : Hypergraph FlatGen)
            → PBij (Hypergraph.nV H) (Hypergraph.nV J)
            → PBij (Hypergraph.nE H) (Hypergraph.nE J) → List (List (Maybe ℕ))
  certified H J φ ψ =
    map (λ iso → map (just ∘ toℕ ∘ _≅ᴴ_.ψ iso) (allFin (Hypergraph.nE H)))
      (mapMaybe (λ { (φ' , ψ') → V.Verify.verify H J φ' ψ' }) (searchAll H J φ ψ))

  permutations₃ : List (List (Maybe ℕ))
  permutations₃ =
    (just 0 ∷ just 1 ∷ just 2 ∷ []) ∷ (just 0 ∷ just 2 ∷ just 1 ∷ []) ∷
    (just 1 ∷ just 0 ∷ just 2 ∷ []) ∷ (just 1 ∷ just 2 ∷ just 0 ∷ []) ∷
    (just 2 ∷ just 0 ∷ just 1 ∷ []) ∷ (just 2 ∷ just 1 ∷ just 0 ∷ []) ∷ []

  seeded₄ : PBij 4 4
  seeded₄ = record
    { forward = λ where
        zero → nothing
        (suc zero) → just (suc (suc zero))
        (suc (suc zero)) → nothing
        (suc (suc (suc zero))) → just zero
    ; backward = λ where
        zero → just (suc (suc (suc zero)))
        (suc zero) → nothing
        (suc (suc zero)) → just (suc zero)
        (suc (suc (suc zero))) → nothing }

  seeded-order : List (List (Maybe ℕ))
  seeded-order = (just 1 ∷ just 2 ∷ just 3 ∷ just 0 ∷ []) ∷
                 (just 3 ∷ just 2 ∷ just 1 ∷ just 0 ∷ []) ∷ []

  swapped₂ : PBij 2 2
  swapped₂ = record { forward = p ; backward = p }
    where
      p : PartialMap 2 2
      p zero = just (suc zero)
      p (suc zero) = just zero

  sparse : ∀ {n} → PBij n n
  sparse = record { forward = p ; backward = p }
    where
      p : ∀ {n} → PartialMap n n
      p e = if (toℕ e Nat.≡ᵇ 0) ∨ (toℕ e Nat.≡ᵇ 15) ∨ (toℕ e Nat.≡ᵇ 31)
            then just e else nothing

  almost : PBij 32 32
  almost = record { forward = p ; backward = p }
    where
      p : PartialMap 32 32
      p e = if (toℕ e Nat.≡ᵇ 0) ∨ (toℕ e Nat.≡ᵇ 31) then nothing else just e

empty-zero-fuel : results (scalars 0) (scalars 0) emptyBij emptyBij ≡ [] ∷ []
empty-zero-fuel = refl

missing-zero-fuel : results (scalars 1) (scalars 0) emptyBij emptyBij ≡ []
missing-zero-fuel = refl

last-fuel-step : certified (scalars 1) (scalars 1) emptyBij emptyBij ≡ (just 0 ∷ []) ∷ []
last-fuel-step = refl

complete-enumeration : results (scalars 3) (scalars 3) emptyBij emptyBij ≡ permutations₃
complete-enumeration = refl

complete-certificates : certified (scalars 3) (scalars 3) emptyBij emptyBij ≡ permutations₃
complete-certificates = refl

populated-map-order : results (scalars 4) (scalars 4) emptyBij seeded₄ ≡ seeded-order
populated-map-order = refl

populated-map-certificates : certified (scalars 4) (scalars 4) emptyBij seeded₄ ≡ seeded-order
populated-map-certificates = refl

already-complete : results (scalars 4) (scalars 4) emptyBij identity ≡ shifted 4 0 ∷ []
already-complete = refl

misplaced-seed-rejected : certified (chain 2) (chain 2) identity swapped₂ ≡ []
misplaced-seed-rejected = refl

scan-31 : results (chain 31) (chain 33) emptyBij emptyBij
        ≡ shifted 31 0 ∷ shifted 31 1 ∷ shifted 31 2 ∷ []
scan-31 = refl

indexed-32 : results (chain 32) (chain 33) emptyBij emptyBij
           ≡ shifted 32 0 ∷ shifted 32 1 ∷ []
indexed-32 = refl

indexed-33 : certified (chain 33) (chain 33) emptyBij emptyBij ≡ shifted 33 0 ∷ []
indexed-33 = refl

small-host-scan : results (chain 32) (chain 31) emptyBij emptyBij ≡ []
small-host-scan = refl

indexed-populated : certified (chain 32) (chain 32) identity sparse ≡ shifted 32 0 ∷ []
indexed-populated = refl

scalar-32-fallback : certified (scalars 32) (scalars 32) emptyBij almost
                   ≡ shifted 32 0 ∷
                     map (λ e → just (if toℕ e Nat.≡ᵇ 0 then 31 else
                                       if toℕ e Nat.≡ᵇ 31 then 0 else toℕ e)) (allFin 32) ∷ []
scalar-32-fallback = refl

submatch-occurrence-order :
  map (λ emb → map (toℕ ∘ _↪ᴴ_.φ emb) (allFin 33)) (subMatchAll (chain 32) (chain 33))
  ≡ map toℕ (allFin 33) ∷ map (Nat.suc ∘ toℕ) (allFin 33) ∷ []
submatch-occurrence-order = refl
