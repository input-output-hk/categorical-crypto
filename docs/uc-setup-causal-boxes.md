# A UC setup of causal boxes

Plan, 2026-10-09.  Nothing here was typechecked; every Agda block is a design.  Paper
references are to `portmann2017` (arXiv v3) unless another bibkey is given.

## 1. Summary

The setup is `StdUC 𝕃ᶜᵇ ℰᶜᵇ` for classical causal boxes on positions 𝒯 = ℕ.  Objects are pairs of
slot alphabets (⊗ = ×).  A `Box A B` runs each position in two phases, ↑ left→right then ↓
right→left, so its only delayed path is caller-input → caller-output.  ⊗ is Portmann's parallel
composition (Def. 6.1), ∘ his composition operation (Def. 6.6) in one pass, tests are his
distinguishers (Def. 7.1) through `UC.Core.Evaluation`; resources are his (X,Y)-boxes on ℕ.  The
closest setup is the random-systems plan (𝔾ᴿ): same object shape and adaptive-environment equality.
**No `UCSetupMorphism` connects causal boxes to 𝔾ᵒ, 𝔾ᴿ, machine-iso, SSP, IPDL or ITM** (§4.1–4.3):
internal rounds are free there and cost a position here (time), and their ⊗ never acts on two
factors at once while Def. 6.1 does (concurrency).  What exists is internal (§4.4): `regrade`
(generic, built as `Abstract2.Regrade.inclusion`), change of distribution monad, distinguisher-class
`changeKernel`s.

## 2. The source model

- **Positions.** A countable poset 𝒯 (§3.1); ℕ "might be sufficient" for "synchronized systems
  which are divided in rounds", while arbitrary environments need a dense 𝒯 such as ℚ (§3.1).
- **Wires.** Fock space F(ℂ^{d_A} ⊗ ℓ²(𝒯)) (§3.3, Eq. 8); classically, multisets of (value,
  position).  F(H_A) ⊗ F(H_B) ≅ F(H_A ⊕ H_B) (Eq. 9) merges wires, Eq. 10 splits them.  One "may
  consider only systems that produce at most one message or never produce multiple messages at
  the same position" (§3.3).
- **Causality.** Cuts (Def. 4.2); χ preserves unions (15), is monotone (16), strict, χ(C) ⊊ C
  (17), and reaches each point in finitely many steps (18) (Def. 4.3; total orders: App. D,
  Def. D.1, Lemma D.2).  (18) excludes Zeno loops (§4.3, outputs at 0, ½, ¾, …).
- **Causal box** (Def. 4.5): CPTP maps Φ^C : T(F_X^{χ(C)}) → T(F_Y^C), consistent,
  Φ^C = tr_{D∖C} ∘ Φ^D (19), and causal (20)/(21).  Subnormalized boxes are post-selected normalized
  ones (Def. 4.7).  Every box splits into one isometry per step (Def. 5.3, Prop. 5.4).
- **Composition.** Φ∥Ψ = {Φ^C ⊗ Ψ^C}, χ_Γ = χ_Φ ∪ χ_Ψ (Def. 6.1, Prop. 6.2, Lemma G.1).  Loop,
  classically Q_{CD|A}(d|a) = Σ_c P_{CD|AB}(c, d | a, c) (§6.2, Def. 6.3, Prop. 6.5).  Composition
  = ∥ then loops (Def. 6.6), with closure (Thm 6.7).  ∥ is associative (Lemma 6.8), commutes with
  loops (Lemma 6.9), loops commute (Lemma 6.10), hence composition-order independence (Thm 6.11).
- **No identity.** "A loop 'takes no time', but plugging in a causal box would incur a delay since
  the identity is not a causal operation" (§7).  Likewise in `matt2018` §6.1 (copying input to two
  outputs "is not a causal system"; zero-delay systems forbid "arbitrary connections"), and in AC,
  which only postulates the neutral converter (`maurer2011` Def. 14 (ii), fn. 22).  *Correction to
  the brief:* the paper proves no SMC-with-trace theorem; Thms 6.7/6.11 and Lemmas 6.8–6.10 are the
  identity-free content of one.
- **Equality, distance.** Equal iff all Φ^C are.  A distinguisher is a box D̂, a termination t_D
  and a wiring that may add loops (Def. 7.1).  D[Φ] reads DΦ's one-dimensional output wire within
  𝒯^{≤t_D} as vacuum or not; d_𝒟 = sup_{D∈𝒟} δ(D[Φ], D[Ψ]) (Def. 7.2) is a pseudo-metric, and a
  metric over all distinguishers (Thm 7.3).  Limit distinguishers change nothing (Def. F.2,
  Lemma F.4, Remark F.5).
- **AC/CC.** ∆^D(R,S) is the statistical distance of DR, DS and ∆^𝒟 = sup (`maurer2011` §6.1,
  `maurer2011cc` §3.5, §4.5).  Classes closed under emulating converters and resources
  (`maurer2011` Def. 16, `maurer2011cc` Lemma 1) are the presheaf condition below.
  `maurerrenner2016` Lemma 5: πR ≈ Sσ gives a construction.
- **Random systems** (§4.1): conditionals p_{Y_i | X^i Y^{i−1}}, equivalent iff equal (`maurer2002`
  Def. 3, `maurer2007` §2.1).  Several query types share "the union of the query sets", one query per
  activation (`maurer2002` §3.1); cascade is Def. 8.

## 3. The `StdUC` instantiation

### 3.1 Decisions

- **Classical, 𝒯 = ℕ** (§3.1's round case).  Environments act only at integer positions; ℚ and
  partial orders are out of scope (§5).
- **At most one message per wire per position** (§3.3's licence): `⟦ wire V ⟧ = Maybe V`, `nothing`
  the vacuum; a batch is one `List V` message.  Not bags: a multiset letter is a permutation
  setoid, and `DiscreteMonad` is only applied at `≡`-setoids (`Categories/Monad/Discrete.agda`).
- **Per-step kernels; cumulative Φ^{≤t} derived** (`⟦_⟧≤`, §3.6).  Stochastic machine traces are
  exactly causal processes (`bonchidilavore2025` Def. 6.1, Prop. 6.9, Cor. 6.13); Portmann's loop
  is built per step (Prop. 5.4).  Cumulative maps would make (19) a marginal equation at every
  construction, and their loops need conditionals (`bonchidilavore2025` Def. 6.2).
- **Causality by typing; no clock wire; no coinduction.** `up` takes no caller-side input, so
  every cycle through a composite is cut by a state; positions are `run`'s ℕ index.  A clock wire
  on `Machines/Core` fails: interfaces pair by the coproduct (`Machines/Tensor.agda` header), so a
  tick reaches one factor of `f ⊗ g` and the factors keep separate clocks.
- **No trace, no G-construction.** `GConstruction`'s unit laws spend yanking (`identityˡ-raw` uses
  `trace-gyank`).  A yanking trace on machines "has to solve the loop inside one step — unbounded
  Elgot iteration" (`Machines/Iteration.agda`), fuel-free in `Machines/Base` only because Dₚ's
  `botₚ` is a value.  Here that iteration is the unbounded run of causal steps inside a position
  that (17)/(18) forbid.  With identities present, only one path class can carry Portmann's
  delay; it is caller-in → caller-out.  ∘ is the guarded trace over it (`goncharov2018` Def. 1,
  Def. 25): one ↑ and one ↓ pass per position.
- **Monad.** `Mo : DiscreteMonad 0ℓ` (the `SFunM` pattern) at `SFunPartial.Dist⊥ᴰ`: rational
  subdistributions = subnormalized boxes (Def. 4.7); `--safe --without-K`, no `--guardedness`.
- **Equality: behavioural and adaptive.** Equal verdict distributions against every environment
  holding all four bundles, at every horizon.  This is the RS plan's `≈ᴿ` with exact `≈ᴹ` for
  `∼ᵃ` (Dist⊥ masses are rationals).  Environments are machines, not `Strategy.Strat` trees, so
  absorbing a box into one pairs states.  The non-adaptive equality is derived.

### 3.2 Objects

```agda
-- CausalBox/Face.agda
data Wires : Set₁ where
  ∅    : Wires
  wire : Set → Wires
  _⊕_  : Wires → Wires → Wires

⟦_⟧ʷ : Wires → Set                        -- what the wires carry during one position
⟦ ∅ ⟧ʷ      = ⊤
⟦ wire V ⟧ʷ = Maybe V
⟦ w ⊕ v ⟧ʷ  = ⟦ w ⟧ʷ × ⟦ v ⟧ʷ

record Face : Set₁ where                  -- slot alphabets, not `Iface`'s message types; Pos rightwards, Neg leftwards
  constructor _⇅_
  field Pos Neg : Set
open Face public

_⊗ᶠ_ : Face → Face → Face
(P ⇅ N) ⊗ᶠ (P′ ⇅ N′) = (P × P′) ⇅ (N × N′)  -- both factors at every position: Def. 6.1's concurrency

unitᶠ : Face
unitᶠ = ⊤ ⇅ ⊤

face : Wires → Wires → Face               -- face (w ⊕ w′) (v ⊕ v′) ≡ face w v ⊗ᶠ face w′ v′ by refl (Eq. 9's role)
face w v = ⟦ w ⟧ʷ ⇅ ⟦ v ⟧ʷ
```

### 3.3 Boxes, composition, tensor, loops

```agda
-- CausalBox/Box.agda: --safe --without-K; imports Categories.Monad.Discrete, Data.Product.Base,
-- Data.Unit.Base, Level, CategoricalCrypto.CausalBox.Face
module CategoricalCrypto.CausalBox.Box (Mo : DiscreteMonad 0ℓ) where
open DiscreteMonad Mo
private variable A B C D : Face; P N U : Set

-- ↑ reads the callee side A and writes the caller side B; ↓ the converse.  `up` has no `Neg B`
-- argument, so B's output at t never reads B's input at t: Eq. 20 with χ(≤t) = ≤t−1 on that
-- path and χ = id on A⁺→B⁺, B⁻→A⁻, A⁺→A⁻.  `init` is pure; the first `up` draws randomness.
record Box (A B : Face) : Set₁ where
  field St Res : Set
        init   : St
        up     : St × Pos A → M (Res × Pos B)
        down   : Res × Neg B → M (St × Neg A)

idᵇ : Box A A
idᵇ = record { St = ⊤ ; Res = ⊤ ; init = tt
             ; up = λ (_ , p) → return (tt , p) ; down = λ (_ , n) → return (tt , n) }

opaque   -- nominal composites, as `Machines.Core._∘ᴹ_`
  -- Def. 6.6 on every wire of B: f's B⁺ into g in ↑, g's B⁻ into f in ↓.  The cycle
  -- B⁺ → g → B⁻ → f → B⁺ is cut by f's state, so one pass suffices.
  _∘ᵇ_ : Box B C → Box A B → Box A C
  g ∘ᵇ f = record
    { St = G.St × F.St ; Res = G.Res × F.Res ; init = G.init , F.init
    ; up   = λ ((sg , sf) , a) → F.up (sf , a) >>= λ (rf , b) → G.up (sg , b) >>= λ (rg , c) →
                                   return ((rg , rf) , c)
    ; down = λ ((rg , rf) , c) → G.down (rg , c) >>= λ (sg , b) → F.down (rf , b) >>= λ (sf , a) →
                                   return ((sg , sf) , a) }
    where module F = Box f; module G = Box g

  -- Def. 6.1: independent draws; `>>=-comm` makes their order immaterial.
  _⊗ᵇ_ : Box A B → Box C D → Box (A ⊗ᶠ C) (B ⊗ᶠ D)
  f ⊗ᵇ g = record
    { St = F.St × G.St ; Res = F.Res × G.Res ; init = F.init , G.init
    ; up   = λ ((sf , sg) , (a , c)) → F.up (sf , a) >>= λ (rf , b) → G.up (sg , c) >>= λ (rg , d) →
                                         return ((rf , rg) , (b , d))
    ; down = λ ((rf , rg) , (b , d)) → F.down (rf , b) >>= λ (sf , a) → G.down (rg , d) >>= λ (sg , c) →
                                         return ((sf , sg) , (a , c)) }
    where module F = Box f; module G = Box g

statelessᵇ : (Pos A → Pos B) → (Neg B → Neg A) → Box A B
statelessᵇ u d = record { St = ⊤ ; Res = ⊤ ; init = tt
                        ; up = λ (_ , p) → return (tt , u p) ; down = λ (_ , n) → return (tt , d n) }
-- λ⇒ᵇ ρ⇒ᵇ α⇒ᵇ σᵇ and inverses: statelessᵇ of the ×-shuffles (cf. `SFunM.Monoidal`'s statelessᵉ)

-- Loops (Def. 6.3) on caller-side wires: a reflector above the box returns in ↓ the U it took in
-- ↑ of the same position, guarded by `up`'s blindness to `Neg`.  Callee-side loops (A⁻ into A⁺)
-- would close a zero-delay cycle and do not exist.
reflectᵇ : Box (U ⇅ U) unitᶠ
reflectᵇ = record { St = ⊤ ; Res = U ; init = tt
                  ; up = λ (_ , u) → return (u , tt) ; down = λ (u , _) → return (tt , u) }

loopᵇ : Box A ((P × U) ⇅ (N × U)) → Box A (P ⇅ N)
loopᵇ f = ρ⇒ᵇ ∘ᵇ (idᵇ ⊗ᵇ reflectᵇ) ∘ᵇ f
```

One position is a Kleisli optic (St × Pos A, St × Neg A) → (Pos B, Neg B) with residual `Res`
(`riley2018` Def. 2.0.1); the state crosses positions as in an effectful Mealy machine
(`bonchidilavore2025` Def. 3.2).  `Res` is data, never quotiented, because `≈ᵇ` is behavioural.

### 3.4 The hom-equality

```agda
-- CausalBox/Behaviour.agda
-- An environment of a box A → B holds all four bundles: the system below and the test above,
-- sharing memory (Def. 7.1 with t_D the horizon).
record Env (A B : Face) : Set₁ where
  field St Res  : Set
        init    : St
        feed    : St → M (Res × Pos A)            -- A⁺ at t, from positions < t
        react   : Res × Pos B → M (Res × Neg B)   -- B⁻ at t after B⁺ at t: Portmann's zero-delay loop
        absorb  : Res × Neg A → M St
        verdict : St → Bool

step : (f : Box A B) (e : Env A B) → Box.St f × Env.St e → M (Box.St f × Env.St e)
step f e (s , σ) = feed σ >>= λ (ρ , a) → up (s , a) >>= λ (r , b) → react (ρ , b) >>= λ (ρ′ , n) →
                   down (r , n) >>= λ (s′ , a′) → absorb (ρ′ , a′) >>= λ σ′ → return (s′ , σ′)
  where open Box f; open Env e

runFrom : (f : Box A B) (e : Env A B) → ℕ → Box.St f × Env.St e → M Bool
runFrom f e zero    (_ , σ) = return (Env.verdict e σ)
runFrom f e (suc t) p       = step f e p >>= runFrom f e t

run : Box A B → Env A B → ℕ → M Bool
run f e t = runFrom f e t (Box.init f , Env.init e)

infix 4 _≈ᵇ_
_≈ᵇ_ : Box A B → Box A B → Set₁
f ≈ᵇ g = (e : Env A B) (t : ℕ) → run f e t ≈ᴹ run g e t

-- A simulation gives ≈ᵇ by induction on t (cf. `SFunM.Properties.trace-sim`).  Its data: state
-- maps φ ψ, `φ (init f) ≡ init g`, and kernels intertwined up to ≈ᴹ.
≈ᵇ-sim : Sim f g → f ≈ᵇ g
-- Absorption moves a box into the environment (CausalBox/Behaviour/Absorb.agda).
_⋉_    : Box B C → Env A C → Env A B                    -- g joins the test above
_⋊_    : Box A B → Env A C → Env B C                    -- f joins the system below
_⋉ʳ_   : Box C D → Env (A ⊗ᶠ C) (B ⊗ᶠ D) → Env A B      -- a parallel factor joins
run-∘ˡ : run (g ∘ᵇ f) e t ≈ᴹ run f (g ⋉ e) t            -- same draws in the same order
run-∘ʳ : run (g ∘ᵇ f) e t ≈ᴹ run g (f ⋊ e) t
run-⊗  : run (f ⊗ᵇ g) e t ≈ᴹ run f (g ⋉ʳ e) t           -- two swaps of independent draws: `>>=-comm-y`
```

Each of `∘ᵇ-resp-≈ᵇ` and `⊗ᵇ-resp-≈ᵇ` is two absorptions plus the hypotheses.  `SFunM.Monoidal`'s
`⊗ᵉ-resp-≈`, by contrast, needs `⊗-split` and a trace lemma.  The associativity and unit laws are
simulations along state re-bracketing; interchange and braiding naturality are simulations up to
`>>=-comm-y`.  Coherence relates stateless boxes, so it is pointwise on ×-shuffles
(`statelessᵇ-∘`, `statelessᵇ-⊗`, `statelessᵇ-cong`).

### 3.5 The monoidal category

```agda
-- CausalBox/Category.agda, CausalBox/Monoidal.agda (parametrised by Mo)
𝕃-Category : Category (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝕃-Category = categoryHelper record
  { Obj = Face ; _⇒_ = Box ; _≈_ = _≈ᵇ_ ; id = idᵇ ; _∘_ = _∘ᵇ_
  ; assoc = ≈ᵇ-sim assoc-sim ; identityˡ = ≈ᵇ-sim idˡ-sim ; identityʳ = ≈ᵇ-sim idʳ-sim
  ; equiv = ≈ᵇ-isEquivalence ; ∘-resp-≈ = ∘ᵇ-resp-≈ᵇ }

𝕃-Monoidal : Monoidal 𝕃-Category
𝕃-Monoidal = monoidalHelper 𝕃-Category record
  { ⊗ = record { F₀ = uncurry _⊗ᶠ_ ; F₁ = uncurry _⊗ᵇ_ ; identity = ≈ᵇ-sim id⊗id-sim
               ; homomorphism = ⊗ᵇ-interchange ; F-resp-≈ = uncurry ⊗ᵇ-resp-≈ᵇ }
  ; unit = unitᶠ
  ; unitorˡ = record { from = λ⇒ᵇ ; to = λ⇐ᵇ ; iso = record { isoˡ = λ-isoˡ ; isoʳ = λ-isoʳ } }
  ; unitorʳ = ρ-isoᵇ ; associator = α-isoᵇ                       -- same shape, stateless
  ; unitorˡ-commute = λ-commuteᵇ ; unitorʳ-commute = ρ-commuteᵇ ; assoc-commute = α-commuteᵇ
  ; triangle = triangleᵇ ; pentagon = pentagonᵇ }

𝕃-Symmetric : Symmetric 𝕃-Monoidal
𝕃-Symmetric = symmetricHelper 𝕃-Monoidal record
  { braiding = niHelper record { η = λ _ → σᵇ ; η⁻¹ = λ _ → σᵇ ; commute = λ _ → braiding-commuteᵇ ; iso = λ _ → σ-isoᵇ }
  ; commutative = σ-involutiveᵇ ; hexagon = hexagonᵇ }

𝕃 : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
𝕃 = record { U = 𝕃-Category ; monoidal = 𝕃-Monoidal }
```

### 3.6 Faithfulness to the paper

```agda
-- CausalBox/Portmann.agda
Resource : Set → Set → Set₁               -- Portmann's (X,Y)-box on ℕ: `up` reads only the state
Resource X Y = Box unitᶠ (Y ⇅ X)

⟦_⟧≤ : Resource X Y → (t : ℕ) → Vec X t → M (Vec Y (suc t))          -- Φ^{≤t}, compact form (21)
consistent   : Total m → (Vec.init <$>ᴹ ⟦ m ⟧≤ (suc t) (xs ∷ʳ x)) ≈ᴹ ⟦ m ⟧≤ t xs   -- (19)
loop-formula : (m : Resource (X × U) (Y × U)) (xs : Vec X t)
             → ⟦ loopᵇ m ⟧≤ t xs ≈ᴹ (Vec.map proj₁ <$>ᴹ feedback m t xs)    -- Def. 6.3's classical formula
```

`feedback` returns position k's U-output as position k's U-input: Σ_c P(c, d | a, c), position by
position.  (20) holds by typing.  (19) needs `Total m`: under Dist⊥ a failure at t+1 erases the
histories up to t, so subnormalized boxes satisfy (19) only as ≤ (= for their normalized dilations,
Def. 4.7).  Thm 6.7 is typing (converter ∘ resource is a resource); Lemmas 6.8–6.10 and Thm 6.11
are 𝕃's monoidal laws, interchange and symmetry.

### 3.7 Distinguishers, seal, setup

```agda
-- CausalBox/Seal.agda — the whole bundle behind `opaque`, per `UC/Model/Seal.agda`
opaque
  𝕃ᶜᵇ : MonoidalCategory (suc 0ℓ) (suc 0ℓ) (suc 0ℓ)
  𝕃ᶜᵇ = CBM.𝕃 Dist⊥ᴰ
∣𝕃ᶜᵇ∣ = MonoidalCategory.U 𝕃ᶜᵇ
opaque   -- coercions exported from inside the seal, as `ifaceᵒ`/`procᵒ`; also faceᶜᵇ, boxᶜᵇ, ⊗ᶜᵇ
  unfolding 𝕃ᶜᵇ
  unboxᶜᵇ : faceᶜᵇ A ⇒ faceᶜᵇ B → Box A B
  ≈ᶜᵇ⇒≈ᵇ  : {f g : faceᶜᵇ A ⇒ faceᶜᵇ B} → f ≈ g → unboxᶜᵇ f ≈ᵇ unboxᶜᵇ g

-- CausalBox/Observation.agda
Ωᶜᵇ : Face
Ωᶜᵇ = face (wire ⊤) ∅          -- Def. 7.1's one-dimensional output wire; nothing flows down

pulses : Env unitᶠ Ωᶜᵇ          -- P₀/P₁ of Def. 7.1: has the output wire left the vacuum?
pulses = record { St = Bool ; Res = Bool ; init = false ; feed = λ seen → return (seen , tt)
                ; react = λ (seen , w) → return (seen ∨ is-just w , tt)
                ; absorb = λ (seen , _) → return seen ; verdict = id }

Verdicts : Setoid 0ℓ 0ℓ          -- t_D ↦ distribution of D[Φ], all horizons at once (Lemma F.4, Remark F.5)
Verdicts = record { Carrier = ℕ → Dist⊥ Bool ; _≈_ = λ v w → ∀ t → DiscreteMonad._≈ᴹ_ Dist⊥ᴰ (v t) (w t) ; … }

evaluationᶜᵇ : Evaluation ∣𝕃ᶜᵇ∣ 0ℓ 0ℓ
evaluationᶜᵇ = record
  { J = faceᶜᵇ unitᶠ ; Ω = faceᶜᵇ Ωᶜᵇ ; S = Verdicts
  ; eval = record { to   = λ c t → run (unboxᶜᵇ c) pulses (suc t)
                  ; cong = λ c≈c′ t → ≈ᶜᵇ⇒≈ᵇ c≈c′ pulses (suc t) } }

-- CausalBox/Setup.agda
open Evaluation evaluationᶜᵇ public
open Observable observable public using (Test; _≋_; ≋-isEquivalence; ℰ₀)
  renaming (≈⇒≋ to ≈ᶜᵇ⇒≋; ℰᴼ to ℰᶜᵇ)
open Std2.StdUC 𝕃ᶜᵇ ℰᶜᵇ public
```

- **Tests.** ℰᶜᵇ(A) is the tests `A ⇒ Ωᶜᵇ` (Def. 7.1's D̂ with its loops: a test may reflect A⁺
  into A⁻ in the same position), equal when every resource below gives equal verdicts at every
  horizon; the action is precomposition (Def. 16's closure under emulation).  Unlike
  `UC.Machine.Ωᴵ`, `Ωᶜᵇ` needs no tick: the run is clock-driven, not activation-driven.
- **Levels.** `Evaluation` at cs = ℓs = 0ℓ over homs at `suc 0ℓ` gives `ℰᶜᵇ : Presheaf ∣𝕃ᶜᵇ∣
  (Setoids (suc 0ℓ) (suc 0ℓ))`, as ℰᵒ and ℰᴿ; `StdSetup` is at `suc 0ℓ` in all eight levels.
- **Thm 7.3, metric half:** `ℰ-full-on-resources : (∀ e → observe e m S.≈ observe e m′) → m ≈ m′`
  for `m m′ : J ⇒ A`; an `Env unitᶠ A` is played by a test pulsing at the horizon iff its verdict
  is true, as in the proof of Thm 7.3.

### 3.8 Grading

ℳ = `curriedTensor 𝕃ᶜᵇ` is right.  Adversary and environment both sit on a protocol's caller side
(`A ⇒ X ⊗ᶠ B`), so an input from either reaches either at the next position; an adversary
`X ⇒ X′` may react to leakage within the position; the dummy adversary is `idᵇ`.  Time-invariant
grades would be wrong: timeouts and relativistic attacks are time-dependent (§1.4), and simulators
must reproduce real-world timing.  `WideSubcategory` is the wrong tool besides: it restricts 𝒞,
not ℐ, and `W-sub : (c : X ℐ.⇒ Y) → W (sub c)` forces closure under `c ⊗ᵇ id` for every grade c,
which time-invariance fails (strict boxes fail `W-id`); it fits feasibility (`maurer2011` Def. 17).
A restricted grading, e.g. efficient simulators, is a pullback along ι : 𝒥 → 𝕃ᶜᵇ
(`Abstract2.Regrade`, §4.4).

## 4. Morphisms

### 4.1 Random systems → causal boxes (`docs/uc-setup-random-systems.md`): does not exist

The candidate with time = activation count needs causal boxes at Dₚ.  RS kernels are Dₚ, and no
monad morphism Dₚ → Dist⊥ exists: Dₚ masses are lower reals "never formed" (`Dp.agda`).  So it
runs at `CausalBox.Box Dₚ-DiscreteMonad`, under `--guardedness`.

```agda
F₀ : Iface → Face
F₀ (P ⇿ N) = face (wire P) (wire N)               -- Maybe P ⇅ Maybe N
F₁ : Proc A B → Box (F₀ A) (F₀ B)                  -- one activation per message
--   ↑: callee answer a runs `MC.step h (s , inj₁ a)`; a caller answer leaves now, a re-query is
--      stashed for this position's ↓; a caller answer pending from the last ↓ leaves now.
--   ↓: caller query b runs `MC.step h (s , inj₂ b)`; a callee query leaves now, a caller answer
--      waits for the next ↑ (caller-in → caller-out is delayed).
--   Two messages for one port, or an input while busy: crash (`botₚ`).
--   St = Maybe (MC.St h) × Maybe (Pos B), so the first ↑ draws `MC.point`.
-- Φ = F, with ⊗-homo : F₀ X ⊗ᶠ F₀ Y ⇒ F₀ (X ⊗ᴵ Y) := ↑ multiplex (crash on just , just), ↓ demultiplex
-- κ : F₀ (X ⊗ᴵ A) ⇒ F₀ X ⊗ᶠ F₀ A           := ↑ demultiplex, ↓ multiplex (crash on just , just)
-- ν.η e := adapt ∘ᵇ F₁ e     -- adapt : F₀ Ωᴵ ⇒ Ωᶜᵇ ticks at position 0, pulses iff the verdict is true
```

| obligation (`GradedKleisliMorphism`, `PresheafMorphism`) | status |
|---|---|
| `F.F-resp-≈` (≈ᴿ ⇒ ≈ᵇ) | plausible: an RS strategy plays an `Env` for `F₁ h` (one-message positions ↦ activations, collisions crash both) |
| `F.identity` | holds: the wire never stashes, so never collides |
| `F.homomorphism` | **fails (time)** |
| `Φ.⊗-homo` natural, `κ-sub`, `κ-ext` | **fail (concurrency)** |
| `ν.commute` | fails with `F.homomorphism`; a closure below exposes it |

*Time.* Let f answer every query with 0, g answer a caller query with 0 after querying f twice,
and k answer every query with 0 directly; g ∘ f ≈ᴿ k.  `F₁ (g ∘ f) ≈ᵇ F₁ k` answers a position-t
query at t+1.  `F₁ g ∘ᵇ F₁ f` answers at t+2: f answers at t+1, g re-queries in that ↓, f answers
at t+2.  "Query at 0, pulse iff an answer is present at 1" has advantage 1.  No other convention
helps: g′ ∘ f ≈ᴿ k for g′ with any number of rounds, so the round count is not an ≈ᴿ-invariant,
but every round crosses a delayed path (Def. 4.3 (17)) and adds a position.

*Concurrency.* The ↑-letter (just p , just p′) of F₀ X ⊗ᶠ F₀ Y has no image in Maybe (P ⊎ P′) that
commutes with the projections.  Dropping, crashing or delaying breaks `⊗-homo`'s naturality
against `F₁ f ⊗ᵇ F₁ g` when f answers in a position where g only stashes.  Bag objects (Eq. 9)
make F₀ strict monoidal, but then `F₁ h` must serialise simultaneous messages.  A composite
serialises globally (one token through g ∘ f), its images locally.  For the uniform-random policy,
and for any order fixed by message content, g can tag forwarded queries so that `F₁ f` meets them
in the opposite of `F₁ g`'s order, while g ∘ f keeps them aligned.  `F.homomorphism` fails again.

*What survives.* (1) Unidirectionally, Maurer's random systems under cascade (Def. 8) *are*
non-strict causal processes with one message per position (`SFunM.SFunᵉ`, `eval` equality; not a
UC setup).  (2) The paper's own reading (§1.4; §9 "Non-deterministic systems") sends an untimed
system to the *set* of its timed realisations: lax (F g ∘ F f ⊆ F (g ∘ f)), outside
`UCSetupMorphism`, whose κ laws are equations (cf. landscape §5).

### 4.2 Causal boxes → random systems or 𝔾ᵒ: does not exist

κ : F (X ⊗ᶠ A) ⇒ Φ X ⊗ᴵ F A would have to turn one position letter carrying traffic for both factors
into interleaved activations.  A `Machines/Core` activation consumes one letter of one factor and
emits exactly one letter.  The second factor's letter would have to be invented, or held until
something outside both factors activates the holder, i.e. a scheduler (§4.3).

### 4.3 Other setups; asynchronous models

- **None either way:** `docs/uc-setup-ssp.md` (sequential ⊗, calls inlined in zero time),
  `docs/uc-setup-ipdl.md` (untimed `≈_ε`), `docs/uc-setup-itm.md`, machine-iso, `Examples/RelSetup`:
  time hits every zero-time composition, concurrency every interleaving or sequential ⊗.
  `docs/uc-setup-symbolic.md`: none designed here (a timed symbolic model would meet §4.4b's
  possibilistic image; that plan's call).

**Why RSIM and task-PIOA land here and not in 𝔾ᵒ.** In RSIM "we have exactly one active machine
at any time": outputs wait in buffers until the holder of a clock port schedules them, else the
default scheduler X runs (`backes2007rsim` §3.5).  Task-PIOAs resolve choices by a scheduler
σ : Frags*(P) → SubDisc(D) or an oblivious task schedule ρ = T₁T₂… (`canetti2006taskpioa` §2,
Def. 1).  𝔾ᵒ composes by the ⊕-trace, which delivers an emitted letter to its unique recipient at
once (procedure-call scheduling, the only schedule it expresses).  A message waiting on a third
party's decision has no image, and that party (RSIM's current-scheduler variable, task-PIOA's ρ)
ranges over the whole closed collection, not a morphism, so no functor carries it.  In causal
boxes scheduling becomes timing: a buffer releases at the position an adversary signals, unknown
scheduling is a family of boxes over all timings, secure for every member ("equivalent to
considering the worst case scheduling … sound in a model with multiple adversaries", §1.4), and
simultaneous deliveries are one product letter.

### 4.4 Morphisms that exist (all inside causal boxes)

**(a) `regrade` (generic; built: `Abstract2/Regrade.agda`).**  For a setup 𝕊 and a lax monoidal
ι : 𝒥 → ℐ, `Regrade.regraded 𝕊 ι` = (𝒞, 𝒥, `∘-Monoidal ℳ ι` — `Graded.Pullback.pullbackM`, ℰ), and
`regrade` is `Regrade.inclusion` = (Id, ι, id, `idᵛ ℰ`).  The pullback's refl's survive `FromMonad`'s
triple (`R.T₀`, `R.sub`, `R.return`, `R.μ`, pinned in `Abstract2/Regrade/Pin.agda`); κ-ext is
`identityˡ`, `assoc` and `ext-resp-≈`, no round-trip lemma.  A restricted-grade `≤UC` crosses into
the full one by `unrestrict-≤UC-gs` (target `GradeStable`, `Transfer.transfer` with `idᵛ-epi`), or
with no `GradeStable` by `Preserves.unrestrict-≤UC` when ι is essentially surjective with split
comparisons — the efficient-simulator grading keeps all grades, so this one applies; full ι reflects
it (`restrict-≤UC`).  `docs/uc-setup-nondeterministic.md` §1 has the theorem.

**(b) Change of distribution monad (`CausalBox/Morphism.agda`, the `SFunM.Morphism` pattern).**
For θ : Mo ⇒ No with `θ-cong`/`θ-return`/`θ-bind`, `mapᵇ θ` post-composes `up`/`down` with θ,
keeping states and objects: strict monoidal, so `StdUCMorphism` with ν.η e = `mapᵇ θ e`.
Obligations: `θ-run : θ (run f e t) ≈ run (mapᵇ θ f) (mapᵉ θ e) t` (induction on t), and, for
`F-resp-≈` and ν's `cong`, a section of θ on environments (every No-environment the image of an
Mo-one up to verdicts).  supp⊥ : Dist⊥ᴰ ⇒ `SFunPossibility.Listᴰ` has one (uniform weights): the
possibilistic image.  Dist⊥ᴰ ⇒ Dₚ is blocked: only `Dp.Coin.coinₚ : Dist-ℚ Bool → Dₚ Bool` exists.

**(c) `changeKernel`.** Fixed-horizon → limit distinguishers (Def. F.2): readout's monotone limit as
a `Data.Rational.LowerReal`, ν = id, `Epi`, equal kernels (Lemma F.4, Remark F.5).  All → feasible
distinguishers: `Abstract2/WideSubcategory` with an efficiency predicate and a `Restriction`.

## 5. Hard parts and risks

- **Guardedness, quotients, K.** None needed: Dist⊥, recursion on ℕ, records; `--guardedness`
  would enter only with a Dₚ instance (§4.1, infective).  Bags avoided, residuals unquotiented,
  equality a setoid.  Σ/× records and pattern lambdas, no index unification.
- **Levels.** `Env : Set₁` puts `_≈ᵇ_` at `suc 0ℓ`, so 𝕃 is (suc 0ℓ)³ as 𝔾ᵒ; ℰᶜᵇ at
  cs = ℓs = `suc 0ℓ` matches ℰᵒ, ℰᴿ.  Bool-coin trees would give `Set` at the cost of tree surgery.
- **Performance.** Seal from the start (`UC/Model/Seal.agda`: `open StdUC` 12 GiB unsealed vs 7 s
  sealed); 𝕃 has no G-construction or trace, so measure both.  `_∘ᵇ_`/`_⊗ᵇ_` `opaque` with
  `unfolding` in law modules; `run-⊗` (seven binds, two swaps) and interchange in their own modules
  (`Machines/G.agda`: 397 s fused vs 7 s + 7 s split).
- **Faithfulness gaps.** 𝒯 = ℕ (no environment between positions); ≤ 1 message per wire per
  position; (19) only for total boxes; adaptive ⇒ non-adaptive equality, converse needs
  conditionals (as in the RS plan).
- **GradeStable**, needed only for `bridge`/`transfer` into this setup: 𝔾ᵒ lacks it, machine-iso
  has it via joint-ancilla tests (`Machine/UC.agda` `grade-stable`); here `GradeStableFromTests`
  with θ the stateless associator box.
- **Disagreements.** With the brief: no SMC-with-trace theorem (§2), no strong `RS → CB` (§4.1),
  `WideSubcategory` does not restrict grading (§3.8).  With Main's "common target" framing and the
  landscape graph: causal boxes are an island for `UCSetupMorphism`, reachable only laxly, which
  agrees with landscape §5's lax crossing.

## 6. Work breakdown

Check each module with `pagda --useUntracked false check src/CategoricalCrypto/<M>.agda -- +RTS
-M3G -H1G -RTS` (warm budget 60 s + LOC/4 s), empty warning grep, escape-hatch baseline unchanged
(house rules 3, 5, 6); OPTIONS `--safe --without-K` everywhere.

1. `CausalBox/Face.agda`: exports `face-⊕` (`refl`).
2. `CausalBox/Box.agda` (Mo): `Box`, `idᵇ`, opaque `_∘ᵇ_`/`_⊗ᵇ_`, structural boxes, `reflectᵇ`, `loopᵇ`.
3. `CausalBox/Behaviour.agda`: `Env`, `run`, `_≈ᵇ_`, `Sim`; exports `≈ᵇ-sim`, `statelessᵇ-∘/-⊗/-cong`.
4. `CausalBox/Behaviour/Absorb.agda`: `run-∘ˡ/ʳ`, `run-⊗`; exports `∘ᵇ-resp-≈ᵇ`, `⊗ᵇ-resp-≈ᵇ`.
5. `CausalBox/Category.agda`, `CausalBox/Monoidal.agda` (interchange split out if over budget):
   exports `𝕃-Category`, `𝕃-Symmetric`, `𝕃`.
6. `CausalBox/Seal.agda`, `CausalBox/Observation.agda`: exports `𝕃ᶜᵇ`, coercions, `evaluationᶜᵇ`;
   record warm times sealed vs unsealed.
7. `CausalBox/Setup.agda`: exports `StdSetup`, `_≤UC_`, `UC-compose`, `dummy-complete` —
   **acceptance of the setup**.
8. `CausalBox/Portmann.agda`: exports `Resource`, `⟦_⟧≤`, `consistent`, `loop-formula`,
   `ℰ-full-on-resources`.
9. `regrade`: import `Abstract2/Regrade.agda` (built), no change to `UCSetup/Morphism.agda`.
10. Optional `CausalBox/Morphism.agda`: `mapᵇ`, `θ-run`, the supp⊥ `StdUCMorphism`.
11. Closure check (`CategoricalCrypto`, `*Tests`); add the causal-box node, with no edges to the
    reactive world, to `docs/uc-setup-landscape.md` §5.

## 7. Sources

Used: `portmann2017`, `matt2018`, `goncharov2018`, `bonchidilavore2025`, `riley2018`, `maurer2002`,
`maurer2007`, `maurer2011`, `maurer2011cc`, `maurerrenner2016`, `lochbihler2019cc` (Def. 2: CryptHOL's
resource ∥ takes sum-typed queries, i.e. interleaves), `backes2007rsim`, `canetti2006taskpioa`.
Newly archived (with INDEX lines): `matt2018.pdf`/`.txt` (arXiv:1609.04293v2, Portmann's [53]; new
`refs.bib` entry, doi:10.1016/j.tcs.2018.06.001) and `goncharov2018.pdf`/`.txt` (arXiv:1802.08756;
bib entry pre-existing).  No download was blocked.
