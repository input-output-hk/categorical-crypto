# Wave C spike verdict: VIABLE (full elimination)

## Question
Is `coeC`/`coeD`'s definitional `refl ↦ h` reduction load-bearing in any
COMPUTATION-relevant position (something a test's `Is-just`/`refl` depends on
reducing), as opposed to only appearing inside propositional soundness
proofs/statements?

## Findings (by classification of every `coeC`/`coeD`/`reidx` occurrence in src/Categories)

- **`coeC` / `coeD`**: appear EXCLUSIVELY inside soundness lemmas — every
  occurrence is the subject of a `≈Term` statement or sits inside such a proof
  (`coeC-resp`, `coeC-trans`, `merge-ρ`, `split-ρ`, `merge-assoc`, `split-assoc`,
  `rpad-fuse`, `BoxSound`, `∘ᵈ-sound`, `shiftL/R-sound`, `tensorD-sound`,
  `reflect-sound`, …). NONE appears inside a definition that the decision
  procedure forces to reduce (`reflect`, `embed`, `_∘ᵈ_`, `boxD`, `shiftL/R`,
  `tensorD`, `≟DiagU`, `norm`). ⇒ purely propositional ⇒ eliminable.

- **`reidx`**: IS load-bearing in computation — it is used inside `reflect`
  (`reflect (g ∘ʷ f) = reflect f ∘ᵈ reidx (sym (out-reflect f)) (reflect g)`,
  `reflect (boxʷ g) = reidx (++-identityʳ _) (boxD g)`), inside `shiftL`,
  `shiftR`, `tensorD`. But it is the DiagU→DiagU transport, the exact analog of
  NormalizeI's `substDiagU`, which is ALSO load-bearing there and already lives
  happily inside the decision procedure. Unifying `reidx`↔`substDiagU` is a
  definitional-shape rename (`refl ↦ d` for both), reduction-safe.

## Decisive site
`SolverTests.Decision.decide?` (a local copy in the test file) and the real
front-end `SolverReflect.DecideCore.Decide.decideW` both:
  1. pattern-match on `reflect f ≟DiagU reflect g` (the `with`-scrutinee), and
  2. carry the `reflect-sound`-derived soundness term ONLY as the PAYLOAD of the
     resulting `just`.
`Is-just (decide? …)` / `solveMor!` therefore force only `≟DiagU` (hence
`reflect`) to reduce — never `coeC`/`reflect-sound`. `decideW` already routes
`reflect-sound` through `coeC-as-castW` immediately, i.e. it never relies on the
`coeC refl ↦ h` definitional step. Changing the soundness-statement vocabulary
from `coeC e h` to `castW e ∘ h` cannot affect any decision reduction.

## Verdict
VIABLE — proceed to STEP 1 (full elimination of `coeC`/`coeD` in favour of
`castW`, unify `reidx`/`out-reidx`/`⟦reidx⟧` with
`substDiagU`/`substDiagU-out`/`⟦substDiagU⟧`).
