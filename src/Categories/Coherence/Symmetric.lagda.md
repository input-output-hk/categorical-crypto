# Symmetric-monoidal coherence and rewriting

Prove equations in a symmetric monoidal category `C` by describing its morphisms
as free terms over a finite table of opaque generators. `solveH!` handles
category laws, monoidal coherence, symmetry, naturality and interchange.
The rewriting operations additionally use equations supplied by the caller.

This is the user-facing entry point. The search and certificate machinery lives
in `Categories.APROP.Hypergraph.Solver.*`, with soundness proved in
`Categories.APROP.Hypergraph.Soundness`. Tests live in
`Categories.Coherence.Symmetric.Test`.

```agda
{-# OPTIONS --safe --without-K #-}

open import Level
open import Categories.Category.Monoidal.Bundle

module Categories.Coherence.Symmetric where

open import Data.Bool
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product
open import Data.Vec

import Categories.APROP.Hypergraph.Solver.Frontend.FinSetup as FinSetup
open import Categories.FreeMonoidal public
open import Categories.Functor using (Functor)
```

## `Solver`: configuring the finite signature

Import `Categories.Coherence.Symmetric`, then `module S = Solver C objects generators`
(or `open` it):

* `objects : Vec C.Obj k` lists the interpretations of the object atoms `Fin k`.
* Obtain `ObjTerm` from `FreeMonoidalHelper Symm (Fin k)`.
* `generators` is a vector of triples `(s , t , morphism)`, where
  `s t : ObjTerm` and the morphism has type `⟦ s ⟧₀ C.⇒ ⟦ t ⟧₀`.

The resulting module `S` is the free term language. Write `S.Agen (gen i)` for
generator `i`, and use `S.id`, `S._∘_`, `S._⊗₁_`, the associators and unitors, and
`S.σ` to build morphism terms. `⟦_⟧₁` interprets them in `C`.

```agda
module Solver
  {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
  (let module C = SymmetricMonoidalCategory C)
  {k n : ℕ}
  (objects : Vec C.Obj k)
  (let module Impl = FinSetup C objects)
  (generators : Vec (Σ[ s ∈ Impl.ObjTerm ] Σ[ t ∈ Impl.ObjTerm ] Impl.⟦ s ⟧₀ C.⇒ Impl.⟦ t ⟧₀) n)
  where
  open Impl public using (⟦_⟧₀)
  open Impl.WithGen generators public
  open Drv
  open S

  open import Categories.APROP.Hypergraph.Solver.Frontend.Rewrite finSig
  open import Categories.APROP.Hypergraph.Solver.Rewrite.Balance finSig
  open import Categories.APROP.Hypergraph.Solver.Rewrite.Carve finSig
  open import Categories.APROP.Hypergraph.Solver.Rewrite.Deep finSig
  open import Categories.APROP.Hypergraph.Solver.Split finSig

  private
    variable A B P Q Z : ObjTerm
```

## `solveH!`: equations between free terms

`solveH! f g` proves `⟦ f ⟧₁ C.≈ ⟦ g ⟧₁` when the coherence search succeeds for
the parallel terms `f` and `g`. Its hidden `T (is-just ...)` argument is an
inferred success gate: for concrete terms, a successful computation reduces it
to a uniquely inhabited type. The rewriting operations below use the same
convention for occurrence search and frame certification; callers normally
omit these arguments.

`solveH` is the lower-level alternative when a hypergraph-isomorphism
certificate is already available.

```agda
  solveH! : (f g : HomTerm A B) → {_ : T (is-just (solveTerm? f g))} → ⟦ f ⟧₁ C.≈ ⟦ g ⟧₁
  solveH! f g {pf} = Functor.F-resp-≈ freeFunctor (to-witness-T (solveTerm? f g) pf)
```

## Single-step rewriting

Each operation takes parallel terms `lᵗ rᵗ` and a caller-proved equation
`⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁`. The rule is applied from left to right.

`rewriteH! s t pre post lᵗ rᵗ rule` uses an explicit context:
`post S.∘ (S.id {k} S.⊗₁ lᵗ) S.∘ pre`, with `k` carrying the bypass wires.
The two inferred coherence gates identify `s` and `t` with this frame before
and after replacing `lᵗ` by `rᵗ`.

`rewriteAutoₙ! s lᵗ rᵗ n rule` searches the term tree for an occurrence.
It tests the whole term first, then descends right-to-left through composition
and tensor. A candidate must have matching object terms at its endpoints,
but need only agree with `lᵗ` by coherence, not by literal syntax.

`rewriteDeepₙ! s lᵗ rᵗ n rule` instead searches the diagram for a carvable
(convex), possibly disconnected occurrence, independent of term bracketing.
In both operations, `n` is a zero-based index into the computed candidate list,
and the result proves an equation to the computed replacement frame.
`rewriteDeepTo! s t lᵗ rᵗ n rule` additionally checks a caller-stated endpoint
`t`, keeping the computed frame out of a multi-step derivation's type.

```agda
  rewriteH!
    : (s t : HomTerm A B) (pre : HomTerm A (Z ⊗₀ P)) (post : HomTerm (Z ⊗₀ Q) B)
    → (lᵗ rᵗ : HomTerm P Q)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {_ : T (is-just (solveTerm? s (post ∘ (id {Z} ⊗₁ lᵗ) ∘ pre)))}
    → {_ : T (is-just (solveTerm? t (post ∘ (id {Z} ⊗₁ rᵗ) ∘ pre)))}
    → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁
  rewriteH! s t pre post lᵗ rᵗ rule {p₁} {p₂} =
    C.Equiv.trans (solveH! s (post ∘ (id ⊗₁ lᵗ) ∘ pre) {p₁})
      (C.Equiv.trans
        (C.∘-resp-≈ʳ (C.∘-resp-≈ˡ (C.⊗.F-resp-≈ (C.Equiv.refl , rule))))
        (C.Equiv.sym (solveH! t (post ∘ (id ⊗₁ rᵗ) ∘ pre) {p₂})))

  rewriteAutoₙ!
    : (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q) (n : ℕ)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (focusAtₙ s lᵗ n))}
    → {_     : T (is-just (solveTerm? s (focFrame s lᵗ lᵗ n found)))}
    → ⟦ s ⟧₁ C.≈ ⟦ focFrame s lᵗ rᵗ n found ⟧₁
  rewriteAutoₙ! s lᵗ rᵗ n rule {found} {cert} =
    C.Equiv.trans (solveH! s (focFrame s lᵗ lᵗ n found) {cert})
      (R.frame-rule-step (λ h → h) lᵗ rᵗ rule (focusAtₙ s lᵗ n) found)

  rewriteDeepₙ!
    : (s : HomTerm A B) (lᵗ rᵗ : HomTerm P Q) (n : ℕ)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (deepFocₙ s lᵗ n))}
    → {_     : T (is-just (solveTerm? s (deepFrame s lᵗ lᵗ n found)))}
    → ⟦ s ⟧₁ C.≈ ⟦ deepFrame s lᵗ rᵗ n found ⟧₁
  rewriteDeepₙ! s lᵗ rᵗ n rule {found} {cert} =
    C.Equiv.trans (solveH! s (deepFrame s lᵗ lᵗ n found) {cert})
      (R.frame-rule-step reassocBal lᵗ rᵗ rule (deepFocₙ s lᵗ n) found)

  rewriteDeepTo!
    : (s t : HomTerm A B) (lᵗ rᵗ : HomTerm P Q) (n : ℕ)
    → ⟦ lᵗ ⟧₁ C.≈ ⟦ rᵗ ⟧₁
    → {found : T (is-just (deepFocₙ s lᵗ n))}
    → {_     : T (is-just (solveTerm? s (deepFrame s lᵗ lᵗ n found)))}
    → {_     : T (is-just (solveTerm? t (deepFrame s lᵗ rᵗ n found)))}
    → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁
  rewriteDeepTo! s t lᵗ rᵗ n rule {found} {c₁} {c₂} =
    C.Equiv.trans (rewriteDeepₙ! s lᵗ rᵗ n rule {found} {c₁})
      (C.Equiv.sym (solveH! t (deepFrame s lᵗ rᵗ n found) {c₂}))
```

## `drive` / `normalize!` / `normalizeTo!`: repeated rewriting

Package a directional rule as `mkRule lᵗ rᵗ rule`. Given a list of such rules,
`drive rules fuel s` returns a term together with a proof that its interpretation
equals `⟦ s ⟧₁`. `normalize! rules fuel s` projects that proof;
`normalizeTo! s t rules fuel` additionally certifies that the result agrees with
the stated endpoint `t` by coherence.

Each round tries rules in list order, at each rule's first deep focus only.
If that focus fails certification, later focuses of the same rule are not
tried. After a firing, the next round restarts at the beginning of the rule list.
Fuel bounds certified firings, not progress: a reflexive or recreating rule can
consume it without simplifying the term. Stopping at zero fuel, or because none
of the tried focuses certifies, does not guarantee a normal form or a complete
sweep of the occurrences.

```agda
  normalize!
    : (rules : List Rule) (fuel : ℕ) → ∀ {A B} (s : HomTerm A B)
    → ⟦ s ⟧₁ C.≈ ⟦ proj₁ (drive rules fuel s) ⟧₁
  normalize! rules fuel s = proj₂ (drive rules fuel s)

  normalizeTo!
    : (s t : HomTerm A B) (rules : List Rule) (fuel : ℕ)
    → {_ : T (is-just (solveTerm? (proj₁ (drive rules fuel s)) t))}
    → ⟦ s ⟧₁ C.≈ ⟦ t ⟧₁
  normalizeTo! s t rules fuel {c} = C.Equiv.trans (proj₂ D) (solveH! (proj₁ D) t {c})
    where D = drive rules fuel s
```

## Example

Two distinct object atoms `a` and `b` represent `A` and `B`, with opaque
endomorphisms `f` and `g` on their respective wires. The rewriting example
additionally assumes `square : f ∘ f ≈ id` and cancels the two copies of `f`.

```agda
private
  module Example {o ℓ e : Level} (C : SymmetricMonoidalCategory o ℓ e)
    (let open SymmetricMonoidalCategory C)
    (A B : Obj) (f : A ⇒ A) (g : B ⇒ B) where

    open FreeMonoidalHelper Symm (Fin 2) using (ObjTerm; Var)

    σ : ∀ {X Y} → (X ⊗₀ Y) ⇒ (Y ⊗₀ X)
    σ = braiding.⇒.η (_ , _)

    a b : ObjTerm
    a = Var (# 0)
    b = Var (# 1)

    open Solver C (A ∷ B ∷ []) ((a , a , f) ∷ (b , b , g) ∷ [])

    fᵗ : S.HomTerm a a
    fᵗ = S.Agen (gen (# 0))

    gᵗ : S.HomTerm b b
    gᵗ = S.Agen (gen (# 1))

    conjugate : σ ∘ (g ⊗₁ f) ∘ σ ≈ f ⊗₁ g
    conjugate = solveH! (S.σ S.∘ (gᵗ S.⊗₁ fᵗ) S.∘ S.σ) (fᵗ S.⊗₁ gᵗ)

    cancel : (square : f ∘ f ≈ id) → σ ∘ g ⊗₁ f ∘ σ ∘ f ⊗₁ id ≈ id {A} ⊗₁ g
    cancel square =
      rewriteDeepTo! (S.σ S.∘ (gᵗ S.⊗₁ fᵗ) S.∘ S.σ S.∘ fᵗ S.⊗₁ S.id)
        (S.id {a} S.⊗₁ gᵗ) (fᵗ S.∘ fᵗ) S.id 0 square
```

## Scope and limitations

The coherence search is sound but incomplete. It works fine in many common cases
and its coverage is tested in `Categories.Coherence.Symmetric.Test`.
