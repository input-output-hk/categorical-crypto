# Two proof tactics that would have paid for themselves

While mechanising APROP completeness (the `decode-⊗-shape` / `nf-bracket` chain)
two patterns showed up again and again, each costing 20–60 lines of hand-written
bookkeeping per occurrence. Neither is *hard* — both are mechanical — which is
exactly why they are good candidates for automation. This note describes what
each tactic would do and shows a concrete before/after drawn from the code we
actually wrote.

Both are "macros" in the loose sense: a `solveX : … → a ≈Term b` that the user
calls in one line where today there is a `begin … ∎` ladder or a `where`-block of
equality lemmas. Tactic 1 is best realised by reflection (it reasons about the
*shape* of `subst₂`/list-append goals); tactic 2 can be either a small reflection
macro or just a well-chosen combinator library.

---

## Tactic 1 — a `subst₂` / list-append **framing solver**

### The problem

Every "box on a block" lemma has to move a `FlatGen`/`box-of` term across a
re-association of the vertex list and re-express it through the
`unflatten (xs ++ ys) ≅ unflatten xs ⊗₀ unflatten ys` isomorphism (`uf++` /
`BTC`). The *content* is trivial — the underlying morphism never changes — but
the proof is a tower of:

* `subst₂ HomTerm (cong unflatten eq₁) (cong unflatten eq₂) _`,
* equality lemmas `eq₁, eq₂` assembled from `map-++`, `++-assoc`, `whole-eq`,
* `subst₂-resp-≈Term`, `≡⇒≈Term`, and a final `reframe` step.

These goals are *decidable by computation*: both sides are built from the same
generators, and the boundary equalities are forced by the list shapes. Yet Agda
makes you write them out.

### A real instance (`Sub/DecodeTensorShape.agda`, `box-suffix-framed`)

```agda
box-suffix-framed eiBlk eoBlk rgBlk Rblk g =
  ≈-Term-trans (≡⇒≈Term decomp)
    (≈-Term-trans (subst₂-resp-≈Term (cong unflatten Cei) (cong unflatten Ceo)
                     (subst₂-resp-≈Term (cong unflatten Bei) (cong unflatten Beo)
                        (BoxAssoc.box-suffix
                           (map vlab eiBlk) (map vlab eoBlk)
                           (map vlab rgBlk) (map vlab Rblk) g)))
                  reframe)
  where
    eiL = map vlab eiBlk
    …
    Aei = sym (++-assoc eiL rgL RL)
    Aeo = sym (++-assoc eoL rgL RL)
    Bei = cong (_++ RL) (sym (map-++ vlab eiBlk rgBlk))
    Beo = cong (_++ RL) (sym (map-++ vlab eoBlk rgBlk))
    Cei = sym (map-++ vlab (eiBlk ++ rgBlk) Rblk)
    Ceo = sym (map-++ vlab (eoBlk ++ rgBlk) Rblk)
    decomp  : … -- 10 more lines relating two subst₂ stacks
    reframe : … -- another ~10 lines
```

The six `Aei … Ceo` equalities plus `decomp`/`reframe` are *pure plumbing*: they
exist only to line up `map vlab (xs ++ ys)` with `map vlab xs ++ map vlab ys`
and to re-bracket the appends. We wrote this kind of block by hand roughly six
times across `DecodeTensorShape` and `BlockNFNf2`.

### What the tactic would do

`solve-frame : (goal : LHS ≈Term RHS) → LHS ≈Term RHS`, where the macro:

1. reflects both sides into a small AST of `box-of`, `_⊗₁_`, `id`, `uf++`/`from`,
   and `subst₂ HomTerm (cong unflatten _) (cong unflatten _) _` nodes;
2. normalises the *vertex-list* indices using a decision procedure for
   `++`/`map`/`whole-eq` equality (this is just `map-++` + `++-assoc` +
   `cong unflatten`, which are confluent rewrite rules);
3. discharges the morphism equality by `subst₂`-cancellation (`subst₂-resp-≈Term`
   composed with the proven `subst₂-*` algebra already collected in
   `Sub/HomTermTransport.agda`).

### After

```agda
box-suffix-framed eiBlk eoBlk rgBlk Rblk g = solve-frame
  (BoxAssoc.box-suffix (map vlab eiBlk) (map vlab eoBlk)
                       (map vlab rgBlk) (map vlab Rblk) g)
```

The single load-bearing input (`BoxAssoc.box-suffix`) stays explicit; everything
else — the six equality witnesses, `decomp`, `reframe`, the nested
`subst₂-resp-≈Term` — is produced by the macro. We already took a first step in
this direction by hand: the generic `BlockBoxSuffix.box-suffix-framed` collapses
the *per-call* instances to one-liners, but the framing engine inside it is still
bespoke. The tactic generalises that engine to any `box`/`⊗`/`uf++` framing goal.

---

## Tactic 2 — an `≈Term` **⊗-regroup** reasoning combinator

### The problem

Bifunctoriality (`⊗-∘-dist : (f ∘ h) ⊗₁ (g ∘ k) ≈Term (f ⊗₁ g) ∘ (h ⊗₁ k)`) is
applied constantly, but never on the nose: to use it you first pad each factor
with `id` via `idˡ`/`idʳ`, apply `⊗-∘-dist`, then strip the `id`s again with
`⊗-resp-≈`. The result is a recurring 4–6 step ladder whose only real content is
"regroup this `⊗` of composites into a composite of `⊗`s, splitting the work as
`X` on the left and `Y` on the right."

### A real instance (`Sub/BlockNFNf2.agda`)

```agda
box-e e ⊗₁ pvl ρ
  ≈⟨ ⊗-resp-≈ (≈-Term-sym idˡ) (≈-Term-sym idʳ) ⟩
(id {Aeout e} ∘ box-e e) ⊗₁ (pvl ρ ∘ id {R-obj rest})
  ≈⟨ ⊗-∘-dist ⟩
(id {Aeout e} ⊗₁ pvl ρ) ∘ (box-e e ⊗₁ id {R-obj rest}) ∎
```

and the mirror image a few lines up:

```agda
(box-e e ∘ id {Aein e}) ⊗₁ (id {R-obj rest'} ∘ pvl ρ)
  ≈⟨ ⊗-resp-≈ idʳ idˡ ⟩
box-e e ⊗₁ pvl ρ
```

The `idˡ`/`idʳ`/`⊗-resp-≈` lines carry no information — they only insert and
delete the identities that `⊗-∘-dist` needs. These ladders appear in
`both-as-fire`, `fire-mid-decomp`, the box-slide lemmas, and the `BlockBracket`
`isoˡ`/`isoʳ` fields.

### What the tactic would do

A pair of combinators that bundle the pad/apply/strip dance:

```agda
-- regroup  f⊗g  as  (f ⊗ id) then (id ⊗ g)   [factor f first]
⊗-split-l : (f ⊗₁ g) ≈Term (id ⊗₁ g) ∘ (f ⊗₁ id)
⊗-split-r : (f ⊗₁ g) ≈Term (f ⊗₁ id) ∘ (id ⊗₁ g)
-- and the inverse "merge two stacked ⊗s into one"
⊗-merge   : (f ⊗₁ g) ∘ (h ⊗₁ k) ≈Term (f ∘ h) ⊗₁ (g ∘ k)
```

each proved *once* from `⊗-∘-dist` + `idˡ`/`idʳ` + `⊗-resp-≈`. A reflection
variant `solve-⊗ : LHS ≈Term RHS` could go further and re-associate an arbitrary
tensor-of-composites tree to match a requested grouping, choosing the
`id`-insertions automatically (the free-strict-monoidal interchange normal form).

### After

```agda
box-e e ⊗₁ pvl ρ
  ≈⟨ ⊗-split-l ⟩
(id {Aeout e} ⊗₁ pvl ρ) ∘ (box-e e ⊗₁ id {R-obj rest}) ∎
```

Three steps become one, and the reader sees the *intent* ("split, factoring the
box first") instead of the `id`-bookkeeping. Across the files above this removes
~40 ladder steps.

---

## Why these two specifically

They sit at the boundary between the genuinely categorical content (which stays
explicit and reviewable — `box-suffix`, `⊗-∘-dist`, the Kelly residual) and pure
syntactic plumbing (list-append re-association, `id`-padding). Automating the
plumbing shrinks proofs, makes the load-bearing steps visually obvious, and — for
the framing solver — removes the single most error-prone hand-step in the whole
`decode-⊗-shape` development (getting a `cong unflatten` equality backwards).

Neither requires new axioms: the framing solver bottoms out in the proven
`Sub/HomTermTransport.agda` `subst₂` algebra, and the ⊗-regroup combinators bottom
out in the `FreeMonoidal` bifunctor laws.
