{-# OPTIONS --safe --without-K #-}

--------------------------------------------------------------------------------
-- Go/no-go spike for `deepFoc`: the canonical NON-SYNTACTIC redex.
--
--   s  = (b ⊗ d) ∘ (a ⊗ c)        (two parallel wires, generators interleaved)
--   lᵗ = b ∘ a                     (the top wire's composite)
--
-- By interchange `s = (b∘a) ⊗ (d∘c)` as a diagram, but `b ∘ a` is NOT a
-- subterm of `s` as written: `a` and `b` live in different operands of the
-- outer `∘`.  So term-level focusing fails (negative control), while the
-- hypergraph route — subMatch, hole-carve, decode, focus-the-hole — finds it,
-- and the resulting frame certifies against `⟪ s ⟫` by `findIso` (exactly the
-- obligation `rewriteH!` imposes).  Each `refl` forces full reduction of the
-- pipeline at type-check time.
--------------------------------------------------------------------------------

module Categories.APROP.Hypergraph.Solver.DeepTests where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin using (Fin; zero)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; from-just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Categories.APROP using (APROPSignature; module APROP)
open import Categories.FreeMonoidal
open import Categories.APROP.Hypergraph.Solver.Signature using (APROPSignatureDec)

X : Set
X = Fin 1

open FreeMonoidalHelper Symm X using (ObjTerm; Var; _⊗₀_)

private
  x : ObjTerm
  x = Var zero

data MyMor : ObjTerm → ObjTerm → Set where
  a b c d : MyMor x x

_≟-MyMor_ : ∀ {A B} → DecidableEquality (MyMor A B)
a ≟-MyMor a = yes refl
a ≟-MyMor b = no λ ()
a ≟-MyMor c = no λ ()
a ≟-MyMor d = no λ ()
b ≟-MyMor a = no λ ()
b ≟-MyMor b = yes refl
b ≟-MyMor c = no λ ()
b ≟-MyMor d = no λ ()
c ≟-MyMor a = no λ ()
c ≟-MyMor b = no λ ()
c ≟-MyMor c = yes refl
c ≟-MyMor d = no λ ()
d ≟-MyMor a = no λ ()
d ≟-MyMor b = no λ ()
d ≟-MyMor c = no λ ()
d ≟-MyMor d = yes refl

mySig : APROPSignature
mySig = record { X = X ; mor = MyMor }

mySigDec : APROPSignatureDec
mySigDec = record { sig = mySig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-MyMor_ }

open import Categories.APROP.Hypergraph.Translation mySig using (⟪_⟫)
open import Categories.APROP.Hypergraph.Solver.FindIso mySigDec using (findIso)
open import Categories.APROP.Hypergraph.Solver.Carve mySigDec using (focusAt)
open import Categories.APROP.Hypergraph.Solver.Deep mySigDec using (deepFoc)
open APROP mySig hiding (X; ObjTerm; Var; _⊗₀_)

private
  lᵗ : HomTerm x x
  lᵗ = Agen b ∘ Agen a

  s : HomTerm (x ⊗₀ x) (x ⊗₀ x)
  s = (Agen b ⊗₁ Agen d) ∘ (Agen a ⊗₁ Agen c)

--------------------------------------------------------------------------------
-- A helper: "deepFoc finds a position AND the auto-constructed frame
-- certifies against ⟪ s ⟫" — the exact obligations `rewriteDeep!` imposes.

private
  certifies : ∀ {A B P Q} → HomTerm A B → HomTerm P Q → Bool
  certifies s lᵗ with deepFoc s lᵗ
  ... | nothing               = false
  ... | just (k , pre , post) = is-just (findIso ⟪ s ⟫ ⟪ post ∘ (id {k} ⊗₁ lᵗ) ∘ pre ⟫)

--------------------------------------------------------------------------------
-- 1. The canonical interchange case.
-- Negative control: the redex is NOT a subterm, so syntactic focusing fails …

syntactic-fails : is-just (focusAt s lᵗ) ≡ false
syntactic-fails = refl

-- … but the hypergraph route finds it and the frame certifies.

deep-certifies : certifies s lᵗ ≡ true
deep-certifies = refl

--------------------------------------------------------------------------------
-- 2. Redex across a braiding: `a` enters on the SECOND wire and crosses the
-- σ to feed `b`.  Connectivity through σ is pure wiring, so the hypergraph
-- search is unaffected.

deep-σ-crossing
  : certifies ((Agen b ⊗₁ Agen d) ∘ σ ∘ (Agen c ⊗₁ Agen a)) lᵗ ≡ true
deep-σ-crossing = refl

--------------------------------------------------------------------------------
-- 3. Parallel (DISCONNECTED) redex: the rule's LHS `a ⊗ c` has two hypergraph
-- components.  The matcher binds them independently; the carve still yields a
-- single convex hole.

deep-parallel
  : certifies s (Agen a ⊗₁ Agen c) ≡ true
deep-parallel = refl

--------------------------------------------------------------------------------
-- 4. NON-CONVEX occurrence rejected: in the sequential chain `b ∘ c ∘ a`,
-- the disconnected redex `a ⊗ b` *matches* edge-wise, but the complement
-- path  a → c → b  leaves the redex and re-enters it, so the carved graph is
-- cyclic through the hole.  The Kahn ordering gets stuck and `deepFoc`
-- correctly returns nothing (a non-convex match has no pushout complement).

deep-non-convex-rejected
  : is-just (deepFoc (Agen b ∘ Agen c ∘ Agen a) (Agen a ⊗₁ Agen b)) ≡ false
deep-non-convex-rejected = refl

--------------------------------------------------------------------------------
-- 5. KNOWN LIMITATION — identity wires in the rule LHS: `⟪ a ⊗ id ⟫` has a
-- bare wire vertex incident to no edge, which the edge-driven matcher can
-- never bind, so `subMatch` (hence `deepFoc`) fails.  State such rules
-- without the padding (`a`, not `a ⊗ id`) — the frame's `id {k} ⊗ –` pad
-- plays that role — or fall back to the manual `rewriteH!`.

deep-id-wire-limitation
  : is-just (deepFoc (Agen a ⊗₁ Agen b) (Agen a ⊗₁ id {x})) ≡ false
deep-id-wire-limitation = refl

--------------------------------------------------------------------------------
-- 6. Duplicate generator labels force backtracking: in `(b ⊗ b) ∘ (a ⊗ c)`
-- both `b`-edges are shape-compatible with the rule's `b`, but only the one
-- fed by `a` satisfies the connectivity constraint.  The DFS must reject the
-- wrong pairing and backtrack.

deep-backtracking
  : certifies ((Agen b ⊗₁ Agen b) ∘ (Agen a ⊗₁ Agen c)) lᵗ ≡ true
deep-backtracking = refl

--------------------------------------------------------------------------------
-- 7. Carve with a permuted boundary: a σ *below* the whole diagram, so the
-- carved context's input interface is a nontrivial permutation.

deep-permuted-boundary
  : certifies ((Agen b ⊗₁ Agen d) ∘ (Agen a ⊗₁ Agen c) ∘ σ {x} {x}) lᵗ ≡ true
deep-permuted-boundary = refl

--------------------------------------------------------------------------------
-- Multi-arity signature: a merge `m : x ⊗ x → x`, a split `e : x → x ⊗ x`,
-- a unary `k : x → x`, and a scalar-ish `u : unit → x`.

module ArityTests where

  open FreeMonoidalHelper Symm X using () renaming (unit to unitᵗ)

  data AMor : ObjTerm → ObjTerm → Set where
    m : AMor (x ⊗₀ x) x
    e : AMor x (x ⊗₀ x)
    k : AMor x x
    u : AMor unitᵗ x

  _≟-AMor_ : ∀ {A B} → DecidableEquality (AMor A B)
  m ≟-AMor m = yes refl
  e ≟-AMor e = yes refl
  k ≟-AMor k = yes refl
  u ≟-AMor u = yes refl

  aSig : APROPSignature
  aSig = record { X = X ; mor = AMor }

  aSigDec : APROPSignatureDec
  aSigDec = record { sig = aSig ; _≟X_ = _≟F_ ; _≟-mor_ = _≟-AMor_ }

  open import Categories.APROP.Hypergraph.Translation aSig using ()
    renaming (⟪_⟫ to ⟪_⟫ᵃ)
  open import Categories.APROP.Hypergraph.Solver.FindIso aSigDec using ()
    renaming (findIso to findIsoᵃ)
  open import Categories.APROP.Hypergraph.Solver.Deep aSigDec using ()
    renaming (deepFoc to deepFocᵃ)
  open APROP aSig using () renaming
    ( HomTerm to HomTermᵃ ; Agen to Agenᵃ ; id to idᵃ ; _∘_ to _∘ᵃ_
    ; _⊗₁_ to _⊗₁ᵃ_ ; σ to σᵃ )

  private
    certifiesᵃ : ∀ {A B P Q} → HomTermᵃ A B → HomTermᵃ P Q → Bool
    certifiesᵃ s' l' with deepFocᵃ s' l'
    ... | nothing               = false
    ... | just (k' , pre , post) =
          is-just (findIsoᵃ ⟪ s' ⟫ᵃ ⟪ post ∘ᵃ (idᵃ {k'} ⊗₁ᵃ l') ∘ᵃ pre ⟫ᵃ)

  ------------------------------------------------------------------------------
  -- 8. Multi-wire redex: the split-then-process composite `(k ⊗ k) ∘ e`
  -- carved out from under the closing merge `m`.

  deep-multiwire
    : certifiesᵃ (Agenᵃ m ∘ᵃ (Agenᵃ k ⊗₁ᵃ Agenᵃ k) ∘ᵃ Agenᵃ e)
                 ((Agenᵃ k ⊗₁ᵃ Agenᵃ k) ∘ᵃ Agenᵃ e) ≡ true
  deep-multiwire = refl

  ------------------------------------------------------------------------------
  -- 9. Scalar redex: `u : unit → x` has an EMPTY input interface, so the hole
  -- edge has no inputs (ready immediately in the topological order) and the
  -- frame's `pre` context ends in a unit wire.

  deep-scalar
    : certifiesᵃ (Agenᵃ m ∘ᵃ (Agenᵃ u ⊗₁ᵃ Agenᵃ k)) (Agenᵃ u) ≡ true
  deep-scalar = refl

  ------------------------------------------------------------------------------
  -- 10. Swapped merge arguments: in `m ∘ σ ∘ (k ⊗ k)` the merge consumes the
  -- two `k` outputs in swapped order; matching the rule `m ∘ (k ⊗ k)` forces
  -- the search to pair the (identically labelled) `k`-edges crosswise.

  deep-swapped-merge
    : certifiesᵃ (Agenᵃ m ∘ᵃ σᵃ ∘ᵃ (Agenᵃ k ⊗₁ᵃ Agenᵃ k))
                 (Agenᵃ m ∘ᵃ (Agenᵃ k ⊗₁ᵃ Agenᵃ k)) ≡ true
  deep-swapped-merge = refl

  ------------------------------------------------------------------------------
  -- 11. KNOWN LIMITATION — purely structural rule LHS: `σ` (or `id`, or any
  -- coherence morphism) translates to a hypergraph with NO edges, so the
  -- edge-driven matcher has nothing to bind and `deepFoc` fails.  Such
  -- "rules" are free coherence facts: discharge them with `solveH!` instead.

  deep-structural-limitation
    : is-just (deepFocᵃ (σᵃ {x} {x} ∘ᵃ (Agenᵃ k ⊗₁ᵃ Agenᵃ k)) (σᵃ {x} {x}))
      ≡ false
  deep-structural-limitation = refl
