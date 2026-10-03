# A mathematical guide to the machine model

Names are `module :: name`, with modules relative to `CategoricalCrypto` unless they
start with `ProbabilisticLogic`.
Signatures, quantifier orders and operational counterparts are in
`docs/state-event-contract.md` §1; the model's size and the options for simplifying it
are in `docs/simplification-options.md`.

## 1. Probability

A subprobability is a coinductive delay of biased coins, and its value is the
supremum of its finite approximants, so divergence carries no mass.

- `ProbabilisticLogic.Dp :: Dₚ`: the rational probabilistic delay monad.
- `ProbabilisticLogic.Dp.Advantage :: Pr≤`, `Upper`, `_≈ₚ[_]_`: the approximant at depth
  `k`, the one-sided bound "every approximant is at most `r`", two-sided closeness.
- `ProbabilisticLogic.Distribution.RationalDist.Partial :: Dist⊥` and
  `ProbabilisticLogic.Distribution.RationalDist.Expectation :: Pr₁⊥`: the exact layer 1.
- `ProbabilisticLogic.Distribution.Uniform.Decay :: Negligible`, `UC.Approximate :: NegligibleBound`: decay faster than every inverse
  polynomial, for a schedule and for a schedule read at every polynomial allowance.

## 2. Machines

A machine `A → B` is a Mealy machine in the Kleisli category of `Dₚ`: machines compose
in sequence (`_∘ᴹ_`), processes (`𝒢ₚ`-homs) by Elgot iteration over their shared
interface (the ⊕-trace), and machines are equal when a zig-zag of
state simulations connects them.

- `Machines.Core :: State`, `Machine`, `St`, `_∘ᴹ_`: pointed state object, machine,
  carrier, composition.
- `Machines.Sim :: _≲_`, `_≈ᴹ_`: a state simulation, and its equivalence closure.
- `Machines.Category :: Mealy-Category`; `Machines.G :: Mealy-Gᴹ`: the category, and
  its G-construction, which is where interface polarity comes from.
- `Machines.Base :: Elgotₚ`, `𝒢ₚ`: the iteration at `Dₚ`, and the resulting category.
  A state object is pointed (`Machines.Core :: State.point`, possibly effectful, since in
  a Kleisli category the unit is not initial) and carries no `discard`.

## 3. Processes

A process is a `𝒢ₚ`-hom between interfaces, and a protocol is a state machine on call
trees that compiles to a process.

- `Machines.Run :: Proc`, `runᴹ`; `UC.Machine :: 𝒫ᴵ`, `Ωᴵ`: processes, a closed
  process's run against a strategy, their category, the verdict interface.
- `Protocol :: Protocol`; `Protocol.Machine :: morphism`, `MSt`: a protocol and its
  compiled process (state `idle | wait`).
- `Strategy :: Strat`, `asks≤`: a finite adaptive environment tree with coin nodes, and
  its query count (a cap of 0 is allowed).
- `UC.Model.Family.Emulation :: Systems`: `(n : ℕ) → Protocol unitᴵ (B n)`, a
  security-parameter family of closed protocols.

## 4. Observations

An observation is the mass of the `true` verdict: it is computed exactly on call trees,
and it agrees with the machine run past some finite depth.

- `Protocol.Observe :: Pr`: the verdict probability of a protocol against a strategy.
- `Protocol.Machine.Agree :: prAgree`, `upper-run`, `run-upper`: from some depth on, the
  compiled run's approximant equals `Pr`, and bounds move across that equality.
- `UC.Seam :: strategyEnv`; `UC.Seam.Adequacy :: adequacy`: a strategy embedded as an
  environment process observes what `runᴹ` observes.
- `UC.Model.Seal :: 𝔾ᵒ`, `unprocᵒ`: the opaque seal that the abstract theory sees, and
  the coercion that every state read must cross.
- `UC.Evaluation :: Evaluation`, `Standard2 :: StdUC`, `UCSetup :: UCSetup`,
  `Abstract2 :: _≤UC_`, `dummy-complete`: the generic UC order: some simulator makes the
  two sides agree in every environment.

## 5. Resource admission

A context is admitted at an allowance when it has a query-count certificate, and the
comparison bounds every admitted context's advantage by a schedule read at that allowance.

- `UC.QueryBound :: Certified`, `QB`, `qb-closed`; `UC.Machine.Grading :: gradingᴹ`: a
  potential-function certificate, its `_≈ᴹ_`-closure, the free certificate of a closed
  process, and the certificates as a graded subcategory over positive rates.
- `UC.Quantitative.Family :: _≈ctx[_]_`, `_≤UC[_,_]_`, `_≤UC^ωᵉ_`: closeness at every
  level for every certified context (`UC.Quantitative.Contextual._≈ᵁᵠ[_]_` levelwise,
  §6), the version with a simulator family and schedule (a fixed witness), and the
  version that hides both and asks only that the schedule be negligible.
- `UC.Quantitative.Family :: ≤UC[]-trans`, `seqError`, `≤UC[]-compose`, `composeError`:
  sequential composition and composition along `_∙ᶠ_` (simulator `sf ⊗^ω t`), each at
  its error formula; every allowance substitution there is by a certified rate.
- `UC.Model.Family.Emulation :: _≈ᶠ[_]_`, `_≈ᶠᴺ_`: the family comparison on protocol
  images, and "some negligible schedule bounds it". This relation is symmetric and has
  no simulator, and it is not identified with `Abstract2._≤UC_`.
- `UC.Model.Family.Emulation :: ≈ᶠ-runs`, `≤UC[]⇒≤UCᴺ`: the comparison read at an
  embedded strategy's run, and the route from a fixed witness to the canonical
  negligible order.

## 6. Approximate spaces

An approximate space is a carrier with closeness indexed by an ordered error. A map
keeps a bound (nonexpansive), transforms it (controlled), or also reindexes which tests
an allowance admits (filtered); the query-sensitive comparison of §5 is the admitted
agreement of one filtered space of tests.

- `Approx.Error :: OrderedErrorAlgebra`, `Approximation`, `Refinement`, `_∼ᵃ_`: errors
  (a preorder with a monotone sum and a unit `ε₀` up to `⊑` in one direction, not an
  ordered monoid), closeness at an error, the positivity the all-positive collapse
  needs, and that collapse. `ℚ-ordered` is the instance in use; `ℕ-unrefinable` shows a
  refinement is extra data.
- `Approx.Space :: ApproxSpace`, `zeroSetoid`: spaces, and their equality at zero
  error.
- `Approx.Separating :: Sequences`, `positive-identifies`, `zero-separates`: rational
  sequences under eventual closeness, where `2⁻ⁿ` and `0` are identified at every
  positive error and separated at zero error, so an exact bound is not asked to respect
  the all-positive collapse. `Approx.Error.ℚ-metric` is the faithful metric a negative closeness statement
  needs at the model level.
- `Approx.Small :: SmallClass`, `Collapse._∼Small_`: closeness at some error of a class
  containing zero and closed under addition, an equivalence with no refinement spent;
  `UC.Approximate.Local._∼ᴺ_` is it at the negligible class.
- `Approx.Controlled :: Control`, `Controlled`: a monotone, zero-preserving,
  subadditive error transformation, and the maps that transform their bound by one.
- `Approx.Schedule :: pointwise`: schedule-valued errors as an instance, over the
  security parameter or over rates; substituting an allowance is an exact control.
- `Approx.Filtered :: FilteredSpace`, `Filtered`, `_≈ᵃ[_]_`: spaces with an
  allowance-indexed admission, maps carrying a control and a monotone allowance map,
  and closeness on admitted elements.
- `Approx.Evaluation :: QEvaluation`, `qual₊`, `qualBy`: the quantitative
  readout, observing the hom equality exactly, and the qualitative readouts it induces.
- `UC.Quantitative.Query :: filteredᵠ`, `pullᵠ`: tests compared through
  certified closures at a schedule read off the closure's rate, and pullback along a
  rated morphism as a filtered map (both indices reindexed by the rate).
- `UC.Quantitative.Contextual :: _≈ᵁᵠ[_]_`, `ctx⇒agree`, `agree⇒ctx`, `absorb-testᵠ`,
  `absorb-closureᵠ`: the query-sensitive comparison, which certifies only the test and
  the closure, never the compared morphisms; it is `_≈ᵃ[_]_` for `filteredᵠ`, and its two
  substitution principles are the allowance map and the control of `pullᵠ`, both exact.
- `UC.Quantitative.EventLift`: event bounds at the compiled monitor (§7).

## 7. Events

An event is a Boolean on protocol states. Its probability is the COMPLETED-RUN hit
probability: `Bad` is sampled at the initial state and after each completed activation,
and it is returned only when the run finishes. A bound on the event is a one-sided bound
over every admitted context that reads it through a monitor.

- `Protocol.Observe :: hitFrom`, `PrHit`, `BoundedHit`: the completed-run hit
  probability, and its bound at a capped allowance.
- `Protocol.Safety :: hit≤badProb⊥`, `hit-bounded`: domination by prefix reachability,
  and a supermartingale certificate that discharges `BoundedHit`.
- `Strategy :: watchFrom`; `UC.Machine.Monitor :: monitorᴹ`, `accᴹ`, `monitor-flag`;
  `UC.Machine.StateEvent.Read :: flagReader`: a watched strategy, the same watch as a
  process, the monitored process as the flag wire of its accumulator
  (`monitorᴹ report ∘ u ≈ accᴹ report u ▷ reported report u`), and the event `Reader`
  that reads its flag.
- `UC.Machine.EventBounds :: Reader`, `BoundedAt`, `Boundedᴺ`: event bounds against
  certified contexts, for fixed and negligible schedules. The slack is chosen after the
  allowance and uniformly over contexts.
- `UC.Machine.EventBounds :: advReader`, `AdvBoundedAt`, `bounded-absorb`: an adversary as
  a `Reader` between the test and the process, a bound at every adversary of a rate, and
  its carry along an exact factoring `f ≈ subᴵ s ∘ g` — the simulator's rate multiplies
  the adversary's, the context cap is untouched, and no slack is paid. The toy instance
  is `Examples.HashForward.UC :: hf-bounded`.
- `UC.Quantitative.EventLift :: Hitsᴺ`, `hitsᵘ`, `hits⇒bounded`: event bounds at the
  monitored readout. `hitsᵘ` lifts a bound on strategies at cap `q` to all contexts at
  cap `q` (it is `stateLift` at `accᴹ`, through `monitor-flag` and
  `Monitor.flag-agree`); `hits⇒bounded` reads a context bound back at a strategy.
- `UC.Machine.StateEvent :: _▷_`: a state event as a flag port of the machine.
- `UC.Machine.StateEvent.Read :: stateRead`, `StateBoundedAt`, `StateBoundedᴺ`: the flag
  read at completion in an ordinary experiment, and its bounds as instances of
  `EventBounds`.
- `UC.Machine.StateEvent.Adequacy :: stateBounded⇒hit`, `hit⇒stateBounded`: at a protocol
  image, `BoundedHit` at cap `q` and `StateBoundedAt` at cap `q` imply each other with no
  slack.
- `UC.Machine.StateEvent.Lift :: stateLift`: a bound at every embedded strategy of cap
  `q` bounds every admitted context of cap `q`.

## 8. The ledger instance

The ideal ledger preserves value against polynomially bounded contexts, and any family
that is `_≈ᶠᴺ_`-close to it inherits that bound.

- `Examples.ChimericLedger.Property :: PreservesValue`, `ideal-preserves-value`,
  `preservesValue⇒saturated`: `Hitsᴺ` at the audit monitor with the birthday schedule
  `εᴸ`, the ideal case, and the bound read at embedded strategies.
- `Examples.ChimericLedger.Transfer :: preserves-value-transfer`: the headline,
  `R ≈ᶠᴺ Ideal a V → PreservesValue (genesisTotal V) R`.
- `Examples.ChimericLedger.Property :: StateSafe`, `TruthfulAudit`, `ideal-truthful`,
  `preservesValue⇒stateSafe`, `ideal-conserves-value`: state-event safety
  (`StateBoundedᴺ` of a supplied test), the one-sided detection premise, and the
  step from observable safety plus detection to state-event safety.
- `Examples.ChimericLedger.Transfer :: ledger-uc-to-state`, `ledger-conserves-value-from-hash`,
  `liar-not-truthful`, `ledger-hit-family-negligible`: the transferred state-event
  bound, its conservation instance over any emulating hash, the lying counterexample,
  and the operational corollary at the embedded strategies.
- `Examples.ChimericLedger.Transfer :: chimeric-not-preserving`, `ideal-spends-genesis`:
  a replaying variant that loses value, and the ideal ledger spending its genesis
  with probability 1.
