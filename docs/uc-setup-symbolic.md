# The symbolic (Dolev–Yao) UC setup — plan

Plan of 2026-10-09, updated 2026-10-12. Steps 1–9 of §6 are built for the single-sorted
pairing/encryption theory E₀; static equivalence implies kernel equality for arbitrary signatures
and admissible theories. The multi-sort converse remains unproved (§3.7). Step 10 proves `smt≤ideal` for a
fixed-public-message fragment; environment-selected interactive messages are not covered (§6).
Steps 11–13 distinguish formal interpretations and derived conditional results from the missing
cryptographic reduction (§4.3). Statements about unwritten modules are design claims.
`[INFERENCE]` marks reasoning backed by neither a read source nor the tree. Citations are
`bibkey §/Def/p.` with printed pages (`docs/kb/sources/papers/INDEX.md`). Short names: CLC =
`comonlundhcortier2008`, CH = `canettiherzog2006`, BPW = `backes2003library`, AR = `abadirogaway2002`.

## 1. Summary

`Sym = StdUC 𝔻𝕐 ℰˢʸᵐ`, where 𝔻𝕐 is the free monoidal category (`Categories/FreeMonoidal.agda`)
on **Dolev–Yao roles**: finite reactive programs whose outputs are recipes over their own frame
(CH's roles, CLC's basic processes). Hom-equality is coherence `_≈Term_`. Tests are DY roles with
an ancilla, as in `Machine/UC.agda`. Two tests are equal when the same verdicts are possible under
some *globally fresh* naming, run in 𝔾ᵒ at term alphabets. The kernel is DY trace (may-testing)
equivalence; E is a kernel fact, because roles emit and store canonical forms; `GradeStable` holds
without hypotheses. The syntactic twin `Sym≅` maps to `Sym` (`changeKernel`) and to
machine-iso (`StdUCMorphism`). Its unrestricted computational execution lands in 𝔾ᵒ, not in the
query-certified family category `Famᴹ`. A separate certificate-bearing source `Sym≅ᶜ` maps to
`ucSetupᴺ`. A context-uniform operational backtranslation implies a feasible comparison theorem;
neither that backtranslation from cryptographic games nor full computational UC soundness is
established. No interpretation of `Sym`'s observational quotient is claimed.

## 2. The source model

**Terms and knowledge.** Sorted signature, names and variables (`abadi2018applied` §2.1
pp. 3–5). An equational theory is a sort-respecting, non-trivial congruence, closed under
substitution for variables and names (§2.2 p. 6). DY cancellation (`dolevyao1983` §II-A p. 200,
§III-B p. 202) is the first destructor theory; these theories are convergent rewrite systems
(`blanchet2016proverif` §2.4 pp. 25–26). A frame `νñ.σ` is the exposed knowledge
(`abadi2018applied` §2.1 p. 4). Deducibility has four rules (`abadicortier2006` §2.3 p. 6). By
Prop 1 (p. 6), `φ ⊢ M` iff `ζσ =E M` for some recipe ζ with `fn(ζ) ∩ ñ = ∅`. Static equivalence
is Defs 1–2 p. 7 (`abadi2018applied` Defs 4.2–4.3 p. 15), and it is not the same as `⊢`
(Props 3–4 p. 8).

**Attacker.** It reads everything, applies public operations and its own keys, and starts and
answers sessions (`dolevyao1983` §I pp. 198–199). It is a closed process over public symbols
(`blanchet2016proverif` Def 3.1 p. 43), or a nondeterministic machine drawing from the closure of
its knowledge (CH §2.2 pp. 389–390).

**Composition and tensor.** Applied-π has `|`, `ν`, `!`, `if M = N` and I/O; `≡` includes
α-renaming and `Rewrite` by E (`abadi2018applied` §2.1 pp. 3–4, §2.2 p. 7). An adversary attaches
by `|` with the shared channels restricted (`delaune2009simulation` Def 6 p. 173;
`bohlunruh2013` Def 4.2 p. 33). The tensor is `|` on disjoint names (Thm 5.37(ii) p. 59). Fresh
names are global: `(Red Res)` picks `a′ ∉ Npub ∪ Npriv` (`blanchet2016proverif` Fig. 2.4 p. 26).
Token-passing variants exist: CH's roles `S × A × M → A × A × S` (Def 1 p. 389); BPW's `TH_H`,
one machine over a term database (§4 pp. 7–10); and CLC's
`cin(x).if … then cout(t) else cout(⊥)·0`, with all I/O through the attacker (§3.3 pp. 10–12).

**Equality and security.** Observational equivalence (`abadi2018applied` Def 4.1 p. 14) is
labelled bisimilarity (Thm 4.1 p. 17); diff-equivalence is finer (`blanchet2016proverif`
Thm 3.5 p. 74). In symbolic UC, `P ≤ Q` iff `∃ (S, φ, n). P ≋ νn.(Qφ | S)` (`bohlunruh2013`
Def 4.3 p. 33). This equals the black-box and `∀A ∃S` forms (Lemma 4.4 p. 34) and is closed under
`|`, `ν`, renamings and `!!`, but not `!` (p. 36, Thm 5.37 p. 59). `delaune2009simulation` uses a
preorder (Def 2 p. 173), under which SS = BB = UC (Thm 16 p. 175). The symbolic outcome is a barb,
not an advantage.

**Computational soundness.**
- AR Thm 1 (§5.2 p. 118) is passive: for acyclic expressions and type-0 encryption, pattern
  equivalence (§3.2 pp. 109–111) implies indistinguishability. Completeness fails (p. 124).
- BPW Thm 7.1 p. 33: the real library realizes `TH_H` under EUF-CMA and IND-CCA2 (Defs 5.1–5.2).
  It leaks lengths and has a commitment problem (§2.2 p. 5).
- CH Lemma 1 p. 394: concrete traces are DY-valid with overwhelming probability, even against
  unbounded environments, because encryption is `Fcpke` (p. 395, Fig. 4 p. 393).
- CLC Thm 12 p. 20: `P₁ ∼o P₂ ⇒ [[P₁]] ≈ [[P₂]]`, where `≈` is negligible advantage for PPT
  attackers (Defs 2, 4 pp. 6–7). It assumes simple processes with a key hierarchy (Def 11 p. 19)
  and joint IND-CPA + INT-CTXT (Defs 8–9 p. 15), and needs tags (§5.1 p. 19), observable lengths
  (§3.2 p. 10) and honest keys (p. 15). Non-failing `else` is open (§8 p. 34).

## 3. The `StdUC` instantiation

### 3.1 Decisions

**Process model (b): DY machines, presented by syntax.** Morphisms are circuits of DY roles;
`Machine/Core` relations serve only as one semantics (§4.2). Four reasons:
1. *Attackers must be DY.* Tests compose with every morphism, because `ℰ` is a presheaf.
   Generating 𝒞 from DY roles makes every morphism DY, with no `W` and no closure proofs.
2. *Interpretation needs programs* that evaluate recipes (AR Fig. 1 p. 118; CLC §4.3 p. 14).
   Relations have neither recipes nor a `Dₚ` image (landscape §2).
3. *Freshness is global.* With locally chosen names an environment may pick the protocol's key,
   and possibilistically that run counts. Names located at occurrences give `(Red Res)`.
4. *Token passing*, as in all targets and in CH, BPW and CLC. A racy `|` would turn functoriality
   into a scheduling theorem.

Option (a) brings α-equivalence, `≡`, extrusion and races. Option (c), `Examples/RelSetup.agda`,
is one-shot and ×-tensored: it hosts passive static equivalence (`otp-perfect`) and is joined to
`Sym` only laxly (landscape §§3, 5).

**Not a restriction of machine-iso**, contra `Abstract2/WideSubcategory.agda:3-6`, for three
reasons. `SetupSubcategory` is wide, and DY-definability means nothing on channels without terms.
`Restriction.ν` must be a setoid map into `ι*ℰ`, whose `_≅ᴹ_` is finer than symbolic test
equality. And relations have no programs. So `Sym` is a free setup plus `changeKernel`.

**Observation runs in 𝔾ᵒ at term alphabets.** 𝔾ᵒ provides initial states (`θ-point` sits inside
`_≈ᴹ_`, `Machines/Sim.agda:42-44`), answers on every activation (CLC fails with `cout(⊥)`, not
silence), is `--without-K`, and lets the soundness proof compare two runs of a single model.
Roles are deterministic. Nondeterminism enters only as `∀` over attacker roles (deterministic
strategies realize every trace) and `∃` over fresh names.

### 3.2 Signature, terms, equational theory, deducibility

Built: `Symbolic/Term.agda`, `Symbolic/Term/PairEnc.agda`, `Symbolic/Deduction.agda`, all
`--safe --without-K`; `Symbolic/{Test,TheoryTests}.agda` exercise them. Freshness uses
located names, as §5 risk 1 recommends: the occurrence bijections cost 24 cases in `Decorated`
(§3.5).

```agda
-- CategoricalCrypto.Symbolic.Term
record Signature : Set₁ where
  field Sort Sym : Set ; dom : Sym → List Sort ; cod : Sym → Sort
        _≟ˢ_ : DecidableEquality Sort ; _≟ᶠ_ : DecidableEquality Sym
Name = ℕ × ℕ                                    -- (occurrence code, counter); §3.5
_≟ₙ_ : DecidableEquality Name
module Terms (𝔖 : Signature) where              -- downstream: `open Terms 𝔖`
  data Tm : Sort → Set where
    name : Name → Tm s
    app  : (f : Sym) → All Tm (dom f) → Tm (cod f)
  Frame = All Tm                                 -- every name of a frame is restricted
  Substitution = ∀ {s} → Name → Tm s
  substᵗ : Substitution → Tm s → Tm s            -- substᵗ*, on tuples
  renˢ : (Sort → Name → Name) → Tm s → Tm s    -- sort-indexed name renaming
  ren : (Name → Name) → Tm s → Tm s ; names : Tm s → List Name   -- and ren*, names* on tuples
  data Each (P : ∀ {s} → Tm s → Set) : All Tm ss → Set            -- lookupᴱ, mapᴱ
  data All₂ (R : ∀ {s} → Tm s → Tm s → Set) : All Tm ss → All Tm ss → Set
  _≟ᵗ_ : DecidableEquality (Tm s)               -- decided in Σ Sort Tm, read back by UIP
  data Recipe (Δ : List Sort) (own : Name → Set) : Sort → Set where
    var  : s ∈ Δ → Recipe Δ own s
    mine : (n : Name) → own n → Recipe Δ own s
    app  : (f : Sym) → All (Recipe Δ own) (dom f) → Recipe Δ own (cod f)
  _⟨_⟩ : Recipe Δ own s → Frame Δ → Tm s       -- and _⟨_⟩* on tuples
  bind : (∀ {s} → s ∈ Δ → Recipe Δ′ own′ s) → own ⊆ own′ → Recipe Δ own s → Recipe Δ′ own′ s
  Ground : Recipe Δ own s → Set                 -- no `var`
record EqTheory (𝔖 : Signature) : Set₁ where   -- abadi2018applied §2.2 p. 6
  field _≈E_       : ∀ {s} → Tm s → Tm s → Set
        isEquiv    : ∀ {s} → IsEquivalence (_≈E_ {s})
        app-cong   : ∀ f {ts us} → All₂ _≈E_ ts us → app f ts ≈E app f us
        subst-cong : ∀ (σ : Substitution) {s} {t u : Tm s}
                   → t ≈E u → substᵗ σ t ≈E substᵗ σ u
        _≟E_       : ∀ {s} → Decidable (_≈E_ {s})  -- guards are computed (§3.5)
        nontrivial : ∀ s → ∃₂ λ (t u : Tm s) → ¬ t ≈E u
        canon      : ∀ {s} → Tm s → Tm s           -- what roles emit and store (§3.3)
        canon-≈E   : ∀ {s} (t : Tm s) → canon t ≈E t
        ≈E⇒canon   : ∀ {s} {t u : Tm s} → t ≈E u → canon t ≡ canon u
        canon-names : ∀ {s} (t : Tm s) → names (canon t) ⊆ names t
  module ≈E {s} = IsEquivalence (isEquiv {s}) ; Tm-setoid : Sort → Setoid 0ℓ 0ℓ
  ren-cong  : ∀ ρ {s} {t u : Tm s} → t ≈E u → ren ρ t ≈E ren ρ u
  renˢ-cong : ∀ ρ {s} {t u : Tm s} → t ≈E u → renˢ ρ t ≈E renˢ ρ u
  fresh-name : ∀ {s n} {t : Tm s} → n ∉ names t → ¬ name n ≈E t
  name-injective : ∀ {s n m} → name {s} n ≈E name m → n ≡ m
  distinct-names : ∀ {s n m} → n ≢ m → ¬ name {s} n ≈E name m

-- CategoricalCrypto.Symbolic.Term.PairEnc: CLC Examples 3.1 and 3.3 (pp. 9–10)
data Op : Set where pair fst snd enc dec : Op ; cst : ℕ → Op   -- enc: plaintext, key, coins
Σ₀ : Signature                                  -- one sort, ⊤; Msg = Tm tt
data _⟶ʳ_ : Msg → Msg → Set where              -- E₀ oriented
  π₁⟨,⟩ : π₁ ⟪ x , y ⟫ ⟶ʳ x ; π₂⟨,⟩ : π₂ ⟪ x , y ⟫ ⟶ʳ y ; dec-enc : dec⟨ enc⟨ x , k , r ⟩ , k ⟩ ⟶ʳ x
data _⟶_ : Msg → Msg → Set                     -- root, arg: one step anywhere
nf : Msg → Msg ; app↓ : (f : Op) → All Tm (arity f) → Msg       -- nf (app f ts) = app↓ f (nf* ts)
nf-normal : (t : Msg) → Normal (nf t) ; nf-reduces : (t : Msg) → t ⟶* nf t
⟶-nf : t ⟶ u → nf t ≡ nf u ; terminating : WellFounded (flip _⟶_)
confluent : t ⟶* u → t ⟶* v → ∃[ w ] u ⟶* w × v ⟶* w
E₀ : EqTheory Σ₀                                -- t ≈E u = nf t ≡ nf u; canon = nf
≈E⇔⟷* : nf t ≡ nf u ⇔ EqClosure _⟶_ t u         -- the theory the three rules generate

-- CategoricalCrypto.Symbolic.Deduction (𝔖 : Signature) (E : EqTheory 𝔖)
Knowledge Δ = Frame Δ × (Name → Set)            -- exposed frame, names the deducer may use
_⊢_ : Knowledge Δ → Tm s → Set                  -- abadicortier2006 Prop 1, as definition
K ⊢ M = Σ[ ζ ∈ Recipe _ (proj₂ K) _ ] ζ ⟨ proj₁ K ⟩ ≈E M
data _⊢ᵢ_ (K : Knowledge Δ) : Tm s → Set where  -- the rules of §2.3 p. 6
  entry : (i : s ∈ Δ) → K ⊢ᵢ lookup (proj₁ K) i ; owned : proj₂ K n → K ⊢ᵢ name n
  apply : Each (K ⊢ᵢ_) ts → K ⊢ᵢ app f ts       ; conv  : K ⊢ᵢ M → M ≈E M′ → K ⊢ᵢ M′
⊢⇔⊢ᵢ : K ⊢ M ⇔ K ⊢ᵢ M
⊢-cut : Each (K ⊢_) φ → own ⊆ proj₂ K → (φ , own) ⊢ M → K ⊢ M   -- with ⊢-conv, ⊢-entry,
⊢-wk  : (φ , own) ⊢ M → (t ∷ φ , own) ⊢ M                      --   ⊢-owned, ⊢-own, bind-⟨⟩
⊬-fresh : n ∉ names* φ → ¬ own n → ¬ (φ , own) ⊢ name {s} n
Foreign φ ψ n = n ∉ names* φ × n ∉ names* ψ
_≈ₛ_ : Frame Δ → Frame Δ → Set                 -- Def 2 p. 7; abadi2018applied Def 4.3
φ ≈ₛ ψ = ∀ {s} (ζ ζ′ : Recipe _ (Foreign φ ψ) s) → (ζ ⟨ φ ⟩ ≈E ζ′ ⟨ φ ⟩) ⇔ (ζ ⟨ ψ ⟩ ≈E ζ′ ⟨ ψ ⟩)
```

**Admissible theory contract.** The existing `EqTheory` is strengthened, rather than
adding a parallel weak semantics or an optional admissibility wrapper. Its closure
law substitutes a term of the occurrence's sort for each sorted name occurrence;
the same raw code at two sorts may have independent images. Uniform `ren-cong` and
sort-indexed `renˢ-cong` are derived laws, not additional fields. E₀ satisfies the
stronger law: substitution preserves each pairing/decryption rewrite step, and
substituting before or after normalization gives E-equal results. Every other E₀
requirement, including `canon-names`, is retained.

`fresh-name` follows from this closure and per-sort `nontrivial`: if `name n ≈E t`
and `t` does not mention `n`, replace `n` at that sort by either of two inequivalent
witness terms. Both substitutions fix `t`, forcing the witnesses equal. Hence
distinct raw names at one sort are inequivalent. `Terms.recipe-names` says an
evaluated recipe uses only frame names or names granted by `own`; `⊬-fresh` thus
rules out public guessing of a name absent from the exposed frame and not owned.
The absence premise is syntactic and conservative: it does not prove confidentiality
of a secret already occurring inside an exposed ciphertext.
`Role.Run.emits≉fresh` combines `⊬-fresh` with the unchanged `emits⊢` theorem:
an emitted term cannot be E-equal to such an unreceived, unowned name.

`TheoryTests.Collapse` checks the historical renaming-only counterinstance without
retaining an obsolete `EqTheory` record. A one-sort signature has public constants
`c₀,c₁`; canonicalization maps every name to `c₀` and keeps the constants distinct.
Its equivalence, congruence, arbitrary-renaming closure, decidability, per-sort
nontriviality, canonical-form laws, and no-invented-name law all hold. Its public
constant recipe passes a fresh-name equality guard, and an owned name equals every
other name. `collapse-not-subst-closed` disproves the stronger closure by substituting
`c₁` for the secret; `collapse-not-EqTheory` rules out any admissible `EqTheory`
representing that relation. `TheoryTests.Supported` exercises the actual E₀
deduction API and `Role.Run.exec`: public guesses and another occurrence's fresh
name are rejected, while equality with the same raw name still succeeds.

**Representation limit.** Terms are sorted but `Name`, `own`, `Role.Own`, and
`Foreign` still range over raw pairs of naturals. Ownership of a code grants
`mine n` at every sort; `TheoryTests.SortedOccurrences.owned-at-two-sorts` is a checked
witness. Its admissible two-sort free theory also demonstrates independent
sort-preserving substitution images. This contract repair is not a sorted-name
representation migration, nor a public/restricted-name redesign of private frames.
`Role.Own κ` grants every counter with occurrence code `κ`, not just already
allocated counters; it is a conservative deducibility overapproximation, not an
exact allocated-name inventory. The non-guessability theorem requires `¬ Own κ n`,
so it protects another occurrence's unseen name, not an unallocated future counter
of the same occurrence under that overapproximation.

Departures from the first draft, all forced:
- `Signature` gains `_≟ᶠ_`: syntactic term equality, hence a decidable E, needs it. The sort
  decision is `_≟ˢ_`, since `_≟_` clashes on opening.
- `app f ts ≡ app f us` cannot be split without K, because the index `cod f` is not a pattern.
  `_≟ᵗ_` therefore decides equality in `Σ Sort Tm` and reads it back with `Decidable⇒UIP`. Σ₀
  has the single sort `⊤`, so `cod f` reduces and its rules can match terms with known heads.
- The term layer is a named module `Terms 𝔖`; an anonymous one cannot be opened at 𝔖.
- Recipes, `bind` and `Ground` live in `Term`, not `Deduction`, because roles need them without
  E. A role recipe is `Recipe Δ ∅`.
- `Sym` clashes with `Relation.Binary.Definitions.Sym`, and `_⊢_`, `_∈_` clash with
  `Relation.Unary`; import those with `using`.
- `EqTheory` gains canonical forms (step 8). Roles emit and store `canon` of what they compute, so
  programs equal modulo E have *equal* steps and `emit-≈E` (§3.6) is a functional simulation.
  The price is a convergent theory, the class §2 names; E₀'s canonical forms are its normal forms.
  `canon-names` ensures canonicalization cannot invent private names; E₀ proves it by name
  preservation along reduction. Message relations are now available (§3.7).

### 3.3 Dolev–Yao roles: the generators

Built: `Symbolic/Role.agda` (6 s warm). Atoms are ports. `port s t` carries sort `s` on `Pos`
and sort `t` on `Neg` (`Iface.agda:3-5`). `verdict` is `Ωᴵ = Bool ⇿ ⊤`, and `void` is the empty
interface. On each activation a role runs a decision tree: guards, fresh names, then one emission
and a jump.

```agda
-- CategoricalCrypto.Symbolic.Role (𝔖 : Signature)
data Atom : Set where port : (pos neg : Sort) → Atom ; verdict void : Atom
_≟ᴬ_ : DecidableEquality Atom
open FreeMonoidalHelper Mon Atom                       -- ObjTerm
data Dir : Set where pos neg : Dir                     -- rightwards, leftwards
data Kind : Set where msg : Sort → Kind ; flag tick : Kind
Value : Kind → Set                                     -- Tm s, Bool, ⊤
kinds : Dir → Atom → List Kind ; Kinds : Dir → ObjTerm → List Kind        -- `++` at ⊗₀
alphabet : Dir → Atom → Set ; Alphabet : Dir → ObjTerm → Set              -- `⊎` at ⊗₀, ⊥ at unit
read  : ∀ d x → Alphabet d x → Σ[ k ∈ Kind ] k ∈ Kinds d x × Value k
write : ∀ d x {k} → k ∈ Kinds d x → Value k → Alphabet d x
Ins Outs : ObjTerm → ObjTerm → List Kind               -- Ins x y = Kinds pos x ++ Kinds neg y
data Input (x y : ObjTerm) : Set where _↦_ : k ∈ Ins x y → Value k → Input x y
data Emission (O : List Kind) : Set where _↦_ : k ∈ O → Value k → Emission O
decode : ∀ x y → Alphabet pos x ⊎ Alphabet neg y → Input x y
encode : ∀ x y → Emission (Outs x y) → Alphabet neg x ⊎ Alphabet pos y
Branch : Kind → Set                                    -- Bool on `flag`, ⊤ otherwise
carried : Kind → List Sort ; branch : Value k → Branch k ; carry : Value k → Frame (carried k)
Rcp Δ = Recipe Δ ∅                                     -- a role holds no name it did not draw
Payload : List Sort → Kind → Set                       -- Rcp Δ s, Bool, ⊤
data React (n : ℕ) (Γ : Fin n → List Sort) (O : List Kind) : List Sort → Set where
  test : Rcp Δ s → Rcp Δ s → React n Γ O Δ → React n Γ O Δ → React n Γ O Δ
  new  : ∀ s → React n Γ O (s ∷ Δ) → React n Γ O Δ
  emit : (c : Fin n) → All (Rcp Δ) (Γ c) → k ∈ O → Payload Δ k → React n Γ O Δ
record Role (x y : ObjTerm) : Set where
  field n : ℕ ; Γ : Fin n → List Sort ; start : Fin n ; fresh : Γ start ≡ []
        react : (c : Fin n) {k : Kind} → k ∈ Ins x y → Branch k
              → React n Γ (Outs x y) (carried k ++ Γ c)
Reactions : Role x y → Set                     -- `react`'s type at p's shape
data GroundJump (h : Fin n) : React n Γ O Δ → Set   -- ground emission jumping to h
data GroundGuards (h : Fin n) : React n Γ O Δ → Set -- every failed test is a GroundJump
record GroundGuarded (p : Role x y) : Set where
  field ground-control : Fin (Role.n p)
        ground-at-control : ∀ {k} (i : k ∈ Ins x y) b
          → GroundJump ground-control (Role.react p ground-control i b)
        ground-guards : ∀ c {k} (i : k ∈ Ins x y) b
          → GroundGuards ground-control (Role.react p c i b)
record TerminalOutput (O : List Kind) : Set where
  constructor terminal-output
  field kind : Kind ; output-port : kind ∈ O ; value : Payload [] kind
record Terminal (p : Role x y) (err : TerminalOutput (Outs x y)) : Set where
  field terminal : Fin (Role.n p)
        boundary : ∀ {k} (i : k ∈ Ins x y) b
          → TerminalJump terminal err (Role.react p terminal i b)
        failures : ∀ c {k} (i : k ∈ Ins x y) b
          → TerminalGuards terminal err (Role.react p c i b)
record Config (n : ℕ) (Γ : Fin n → List Sort) : Set where
  constructor config ; field control : Fin n ; registers : Frame (Γ control) ; counter : ℕ
init : (p : Role x y) → Config (Role.n p) (Role.Γ p)
received : (hist : List (Input x y)) → Frame (Received hist)   -- newest first
Own : ℕ → Name → Set ; Own κ (κ′ , _) = κ′ ≡ κ
module Run (E : EqTheory 𝔖) where
  canonᵛ : Value k → Value k ; canon* : Frame Δ → Frame Δ           -- `canon` on terms
  exec : (κ : ℕ) → React n Γ O Δ → Frame Δ → ℕ → Config n Γ × Emission O   -- names (κ , j)
  exec κ (emit c ρs o π) φ j = config c (canon* (ρs ⟨ φ ⟩*)) j , o ↦ canonᵛ (payload _ π φ)
  step : (κ : ℕ) (p : Role x y) → Config (Role.n p) (Role.Γ p) → Input x y
       → Config (Role.n p) (Role.Γ p) × Emission (Outs x y)
  step-terminal : (κ : ℕ) (p : Role x y) → Terminal p err → Config (Role.n p) (Role.Γ p)
    → Input x y → Maybe (Config (Role.n p) (Role.Γ p) × Emission (Outs x y))
  run-terminal : (κ : ℕ) (p : Role x y) → Terminal p err → Config (Role.n p) (Role.Γ p)
    → List (Input x y) → Config (Role.n p) (Role.Γ p) × List (Emission (Outs x y))
  Known : Knowledge Δ → Emission O → Set               -- an emitted term is deducible
  exec⊢ : Own κ ⊆ proj₂ K → (t : React n Γ O Δ) → Each (K ⊢_) φ → Deduced K (exec κ t φ j)
  after : (κ : ℕ) (p : Role x y) → List (Input x y) → Config (Role.n p) (Role.Γ p)
  emits⊢ : ∀ κ p (hist : List (Input x y)) (inp : Input x y)
         → Known (received (inp ∷ hist) , Own κ) (proj₂ (step κ p (after κ p hist) inp))
  _≈ᵛ_ : Value k → Value k → Set                       -- _≈E_ on terms, _≡_ otherwise
  data ReactE : React n Γ O Δ → React n Γ O Δ → Set    -- one shape, recipes ≈E at every frame
  exec-≈E : ReactE t t′ → ∀ φ j → exec κ t φ j ≡ exec κ t′ φ j
  step-≈E : (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
          → ∀ cfg inp → step κ p cfg inp ≡ step κ (record p { react = r }) cfg inp
```

A role's frame grows at the front: a received term and a `new` name are pushed. `emits⊢` says
roles are DY deducers: what occurrence κ emits is deducible from every term it has received,
its trigger included, together with its own names `(κ , _)`. The recipe is the emitting branch's
`Rcp`, with each `new` turned into `mine` (`exec⊢`, `⊢-cut`). Ports are kinds listed in tensor
order. A role branches on a received bit, so a verdict in its domain can be read, and it pushes
a received term on its frame. `GroundGuarded` only requires ground output on failed guards
and at a designated control: ground flags can still depend on input bits, and different
failed guards can emit different constants. It is not the CLC §3.3 terminal contract.

`Terminal p err` is a separate, opt-in contract. `err` fixes one output port and closed
payload; `TerminalJump` requires exactly that emission followed by a jump to `terminal`,
and `TerminalGuards` imposes this on every guard-failure branch. The boundary row is fixed
too. `Run.step-terminal` checks the actual control before executing a reaction: at
`terminal` it returns `nothing`, without evaluating guards, drawing names, changing
registers/counter, or emitting anything. `Run.run-terminal` executes finite input histories.
`terminal-jump-exec` derives the fixed error, destination control and unchanged fresh counter;
`terminal-no-further-behavior` proves every suffix at that control leaves the complete
configuration unchanged with an empty output trace. `post-terminal-transition` applies
that theorem after a transition reaches the designated terminal control.

This models the `cout(⊥) · 0` boundary in CLC §3.3, not a translation of all CLC basic
processes. The generic total `Run.step` and `Fine` remain unrestricted and do **not**
silently terminate at this control. `Symbolic/TerminalTests.agda` checks a one-state
bit-forwarder that is `GroundGuarded` but cannot be `Terminal` for any fixed error,
a verdict emitted exactly once with arbitrary silent suffixes, and both successful and
failed guards through the opt-in runtime. It also checks that the original total runner
still emits at the boundary. CLC's well-formedness guard `M` needs check symbols in the
signature (step 13). Everything is first-order data in `Set`, as `FreeMonoidalData.mor`
requires. Unbounded
sessions are a single role that dispatches on session tags. This is `bohlunruh2013`'s `!!`
(Def 5.11 p. 42), the only replication their composition theorem covers. An emission and the
stored registers are canonical (§3.2): `emits⊢` still holds through `⊢-conv`, and `exec-≈E`
follows by `≈E⇒canon`, guards agreeing because both sides of a `test` are E-equal.

`Symbolic/Test.agda` checks that `⟦_⟧ᴵ` (§3.5) is the `_⊗ᴵ_`-tree on the nose, with `unitᴵ` at
`unit` and `Bool ⇿ ⊤` (`Ωᴵ`) at `verdict`; it runs `step` on a concrete role and checks
`emit-≈E` at Σ₀ (a role answering `π₁ ⟪ x , x ⟫` against one answering `x`).

### 3.4 The category and its hom-setoid

Built: `Symbolic/Fine.agda` (80 lines, 10 s warm).

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Symbolic.Fine (𝔖 : Signature) where
UnitFree : ObjTerm → Set                           -- no `unit` leaf; ⊤ at `Var`, × at ⊗₀
symData : FreeMonoidalData {0ℓ}
symData = record { v = Mon ; X = Atom ; mor = λ x y → UnitFree x × UnitFree y × Role x y }
open FreeMonoidal symData public                   -- ObjTerm, HomTerm, _≈Term_, FMC
𝔻𝕐 : MonoidalCategory 0ℓ 0ℓ 0ℓ
𝔻𝕐 = FMC
Test : ObjTerm → Set
Test A = Σ[ Y ∈ ObjTerm ] HomTerm (Y ⊗₀ A) (Var verdict)   -- ancilla on the grade side
pullᵗ : HomTerm B A → Test A → Test B               -- (Y , T) ↦ (Y , T ∘ id ⊗₁ f)
data SameTerm {A} : Test A → Test A → Set where
  same : T ≈Term T′ → SameTerm (Y , T) (Y , T′)
ℰᵗ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids 0ℓ 0ℓ)   -- F₁ = pullᵗ
ℰ≅ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids (suc 0ℓ) (suc 0ℓ))
ℰ≅ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵗ
module Sym≅ = StdUC 𝔻𝕐 ℰ≅                          -- `Sym≅.UC-compose` instantiated
```

Departures: `Fine` takes no E, since roles do not depend on it; `Test`, `pullᵗ` and `UnitFree` live
here, shared by `Sym≅` and `Sym`; `homˢ` was dropped (nothing uses it); `Sym≅` is a module, not an
`open … public`, because `StdUC`'s category names clash with the term syntax.

Hom-equality is `_≈Term_` (`FreeMonoidal.agda:140-164`): coherence only, and finer than `_≅ᴹ_` on
purpose. It has two jobs: `F-resp-≈` for every outgoing functor, which comes free
(`⟦⟧-resp-≈`, lines 466-490), and `≈C⇒≈ℰ`. E-equality, name renaming and bookkeeping are kernel
facts, and `≈ℰ = ≈ᵁ` (§3.6). The alternatives gain nothing:
- Bisimulation up to E proves no new UC statement and needs a congruence proof.
- The kernel quotient would turn soundness into `F-resp-≈` and block §4.2.
- `Factorization` never changes a hom-equality.

`Mon` is enough: the UC structure uses only α, and `Famᴹ` is a plain `MonoidalCategory`
(`LocallyGraded/Family.agda:115`).

### 3.5 Observation with located names

```agda
-- Categories.FreeMonoidal.Decorated (built; 151 lines, 4 s warm)
module Categories.FreeMonoidal.Decorated
  {ℓ′ o ℓ e d} (dat : FreeMonoidalData {ℓ′}) (⟦v⟧ : ⟦ v ⟧ᵥ {o} {ℓ} {e}) (⟦_⟧ᵖ₀ : X → C.Obj)
  (D : Set d) (⟦_⟧ᵈ : ∀ {x y} → mor x y → D → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀) where
Occ : HomTerm A B → Set
Occ (var _) = ⊤ ; Occ (g ∘ f) = Occ g ⊎ Occ f ; Occ (f ⊗₁ g) = Occ f ⊎ Occ g ; Occ _ = ⊥
⟦_⟧[_] : (f : HomTerm A B) → (Occ f → D) → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
⟦ var p ⟧[ ι ]  = ⟦ p ⟧ᵈ (ι tt)
⟦ g ∘ f ⟧[ ι ]  = ⟦ g ⟧[ ι ∘′ inj₁ ] C.∘ ⟦ f ⟧[ ι ∘′ inj₂ ]
⟦ f ⊗₁ g ⟧[ ι ] = ⟦ f ⟧[ ι ∘′ inj₁ ] C.⊗₁ ⟦ g ⟧[ ι ∘′ inj₂ ]   -- structural: as FreeFunctor
⟦⟧[]-cong : (f : HomTerm A B) → (∀ x → ι x ≡ ι′ x) → ⟦ f ⟧[ ι ] ≡ ⟦ f ⟧[ ι′ ]
⟦⟧[]-resp-≈ : f ≈Term g → Σ[ π ∈ Occ f ↔ Occ g ] (∀ ι → ⟦ f ⟧[ ι ∘′ Inverse.to π ] C.≈ ⟦ g ⟧[ ι ])

-- CategoricalCrypto.Symbolic.Semantics (built; 205 lines, 12 s warm)
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Semantics (𝔖 : Signature) (E : EqTheory 𝔖) where
atomᴵ : Atom → Iface ; atomᴵ a = alphabet pos a ⇿ alphabet neg a   -- Tm s ⇿ Tm t ; Ωᴵ ; unitᴵ
⟦_⟧ᴵ  : ObjTerm → Iface ; ⟦ x ⟧ᴵ = Alphabet pos x ⇿ Alphabet neg x  -- the _⊗ᴵ_-tree of atomᴵ
⟦v⟧ᵒ = fromMC 𝔾ᵒ noSymmetric ; open FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)
tree≡ : (x : ObjTerm) → UnitFree x → ⟦ x ⟧₀ ≡ ifaceᵒ ⟦ x ⟧ᴵ        -- ⊗ᵒ at ⊗₀, refl at Var
treeᵒ : UnitFree x → UnitFree y → ifaceᵒ ⟦ x ⟧ᴵ G.⇒ ifaceᵒ ⟦ y ⟧ᴵ → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
treeᵒ-resp : f G.≈ g → treeᵒ ux uy f G.≈ treeᵒ ux uy g
runᴿ : ℕ → Role x y → Proc ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ
runᴿ κ p = MC.mk (initˢ (Config (Role.n p) (Role.Γ p)) (init p))
  λ (cfg , m) → returnₚ (map₂ (encode x y) (step κ p cfg (decode x y m)))
runᴿ-≈E : (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
        → procᵒ (runᴿ κ p) G.≈ procᵒ (runᴿ κ (record p { react = r }))   -- θ = id, ≈ᴹ⇒≈ᵒ
leafᵒ : UnitFree x × UnitFree y × Role x y → ℕ → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
leafᵒ (ux , uy , p) κ = treeᵒ ux uy (procᵒ (runᴿ κ p))
open Decorated symData ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ) ℕ leafᵒ public
record eval (c : HomTerm (Var void) (Var verdict)) (b : Bool) : Set where   -- possible verdict
  constructor named
  field naming : Occ c → ℕ ; fresh : Injective _≡_ _≡_ naming ; answer : Obs ⟦ c ⟧[ naming ] ≈ₚ returnₚ b
eval-cong : c ≈Term c′ → ∀ b → eval c b ⇔ eval c′ b       -- ⟦⟧[]-resp-≈, ⟦⟧[]-cong, obs-resp
```

`treeᵒ` coerces along `⊗ᵒ` (`Seal.agda:87-88`); at a single atom it is `refl`, so a role on atoms
is its `procᵒ` on the nose. Generator boundaries are unit-free because `G.unit ≠ ifaceᵒ unitᴵ`
(`Observation.agda:15-22`). Each occurrence gets its own name supply,
attackers included, so an attacker holds a protocol name only once it has been sent one. The
`∃ι` absorbs re-bracketing, so no equivariance lemma is needed here. A naming `ι′` of `c′` gives
`c` the naming `ι′ ∘ to π` directly. A naming `ι` of `c` gives `c′` the naming `ι ∘ from π`, and
`⟦⟧[]-cong` closes the gap, because `from ∘ to` is the identity only pointwise. Equivariance
(`ren-cong`, guards modulo E) makes the verdict independent of `ι`; only the soundness proof
uses it.

Departures: `eval` is a record, not a `Σ`. As a definition it unfolds into `_≈ₚ_`'s rationals
whenever unification meets a meta, and `Setup`'s presheaf then exhausted a 3 GiB heap; as a record
type, unification compares circuits. The two-role example is private to the module: a tester draws
a name, sends it to an echo and answers `true` on the reply, under the naming `[ 0 , 1 ]`. Its run
crosses the seal with `unprocᵒ-∘`, then `UC.Seam.Plug` (`collapse`, `observe`, two `loop-pass`es).
The loop passes are given their states and messages, because unification cannot invert `kᴳ`.

### 3.6 The DY-environment presheaf and the setup

Built: `Symbolic/Setup.agda` (163 lines, 14 s warm).

```agda
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Setup (𝔖 : Signature) (E : EqTheory 𝔖) where
Closure A = HomTerm (Var void) A
Agree T T′ = ∀ (m : Closure (Y ⊗₀ A)) b → eval (T ∘ m) b ⇔ eval (T′ ∘ m) b
data SameObs {A} : Test A → Test A → Set where
  same : Agree T T′ → SameObs (Y , T) (Y , T′)
same⁻¹ : SameObs (Y , T) (Y , T′) → Agree T T′          -- Decidable⇒UIP (≟ObjTerm _≟ᴬ_)
term⇒obs : SameTerm t t′ → SameObs t t′                  -- eval-cong
ℰᵒᵇˢ : Presheaf (MonoidalCategory.U 𝔻𝕐) (Setoids 0ℓ 0ℓ)  -- F₁ = pullᵗ; laws: ℰᵗ's, by term⇒obs
ℰˢʸᵐ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵒᵇˢ
module Sym = StdUC 𝔻𝕐 ℰˢʸᵐ
regroup : ((T ∘ α⇒) ∘ id ⊗₁ h) ∘ (α⇐ ∘ m) ≈Term (T ∘ id ⊗₁ (id ⊗₁ h)) ∘ m
grade-stable : Sym.GradeStable      -- (Y , T) on Z ⊗₀ C is (Y ⊗₀ Z , T ∘ α⇒) on C
≈ᵁ⇔≈ℰ : f Sym.≈ᵁ g ⇔ f Sym.≈ℰ g    -- ≈ᵁ⇒≈ℰ, bridge grade-stable
leaf-≈ℰ : (∀ κ → leafᵒ p κ G.≈ leafᵒ q κ) → var p Sym.≈ℰ var q
emit-≈E : (p : Role x y) {r : Reactions p}            -- E lives in the kernel
        → (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
        → var (ux , uy , p) Sym.≈ℰ var (ux , uy , record p { react = r })
```

Departures: `Sym` is a module like `Sym≅` (§3.4), not `open StdUC … public`. `emit-≈E` compares a
role with another reaction table of its shape: `ReactE (react p c i) (react q c i)` needs one set
of control points. It is `leaf-≈ℰ` at `runᴿ-≈E`, so it rests on canonical emissions (§3.2).
`leaf-≈ℰ` holds because occurrences are counted by shape, so one naming serves both circuits.

The kernel `f ≈ℰ g` holds iff every DY environment and closure sharing an ancilla allows the
same verdicts; it is trace (may-testing) equivalence against DY contexts. Diff-equivalence
implies `∼o`, which implies this kernel, so ProVerif proofs certify it `[INFERENCE: needs a
translation of roles into applied-π]`. On frame emitters the kernel is static equivalence
for E₀ (`Symbolic/Static/PairEnc.≈ℰ⇔≈ₛ`); the multi-sort converse is not established
under the admissible theory contract (§3.7). `≤UC` is `bohlunruh2013` Def 4.3, and `≤UCᵈ⇔≤UC` is their
Lemma 4.4, here without hypotheses. The reflexivity concern of
`delaune2009simulation` (p. 175) does not arise: `≤UC-refl` takes `s = a`.

**Levels, options, layout.** 𝔻𝕐 lives at `0ℓ`. Tests are lifted to `cs = ℓs = suc 0ℓ`, which
matches machine-iso, ℰᵒ, ℰᴿ and `ucSetupᴺ` (`Enrichment.agda:46`). So
`Sym : UCSetup 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ (suc 0ℓ) (suc 0ℓ)`. Everything is `--safe --without-K`, with
two exceptions: `--guardedness` from `Semantics` on, and K in `Symbolic/Machine.agda`. The modules
under `Symbolic/` are `Term`, `Term/PairEnc`, `Deduction`, `Role`, `Test`, `Fine`, `Semantics`,
`Setup`, `Static`, `Machine`, `Computational`, `Soundness` and `Example/SecureChannel`. General additions:
`freeStrongMonoidal`, `Categories/FreeMonoidal/Decorated.agda`, and `transfer⁺` in
`Abstract2/Morphism.agda`.

### 3.7 Relational simulation and static equivalence

`Machines/Sim/Relational.agda` presents a relation by an apex machine and two
simulation legs. Each `_≲[ μᵢ ∣ μₒ ]_` carries **three** purity witnesses: its state
map (`leg-pure`), input map (`input-pure`), and output map (`output-pure`). At
`Kl(Dₚ)`, purity means equivalence to `returnₚ` composed with an ordinary function;
none of these projections can draw randomness. The apex initial distribution has
the two worlds' initial distributions as deterministic pushforwards. For every apex
state and input, its transition has as pushforwards the two step distributions at
the projected state/input. Thus these are couplings of the corresponding
**subdistributions** (divergence may lose mass), supported on the image of the two
projections. No injectivity or functional dependence between the worlds is assumed.
For an abstract categorical base the API asserts pure commuting squares, not a
measure-theoretic coupling theorem. No stochastic-interface relational API is retained.

```agda
_≲[_∣_]_ : Machine A B → (A ⇒ A′) → (B ⇒ B′) → Machine A′ B′ → Set _
RelSim : (Aᴿ ⇒ A) → (Aᴿ ⇒ A′) → (Bᴿ ⇒ B) → (Bᴿ ⇒ B′)
       → Machine A B → Machine A′ B′ → Set _
≲⇔≲[id] : f ≲ g ⇔ f ≲[ id ∣ id ] g
≲⇒relsim : f ≲ g → RelSim id id id id f g
relsim⇒≈ᴹ : RelSim id id id id f g → f ≈ᴹ g
```

`∘ᴹ-relsim`, `⊗ᵉ-relsim` and `trace-relsim` preserve the pure-interface span. The
feedback theorem takes separate purity witnesses for both worlds' input, output,
and loop projections: purity of a sum map cannot be eliminated in an abstract
`PureSub`. It uses `iter-transfer` on the paired state/loop variable.
`UC/Machine/Relational` carries this through G-composition and tensor (`HSim-∘`,
`HSim-⊗`); its `Map` contains ordinary functions on both polarities.
`UC/Model/Relational` exports that same function-map contract across the seal.
`relsim⇒≈ᴿ` gives equality against every machine distinguisher, not just equality
of one finite run.

`UC/Machine/RelationalTests` exercises functional-graph compatibility, behavioural
consequence, tensor, feedback, G-composition/tensor, and a nonidentity pure-interface
span that flips the visible bit while forgetting hidden state. `coin-flipped-span`
also starts with a faircoin apex: its deterministic right state projection complements
the shared sample, preserving the faircoin marginal while relating opposite hidden
bits and visible letters. Its faircoin **interface-map** counterexample, in contrast,
commutes with the identity-machine step square but
cannot be a deterministic projection: every point event has probability `½`, whereas
a deterministic value has probability one for its own point event. The tests prove
`¬ IsPure faircoin-map`, exclude a simulation and a `RelSim` with that output leg,
and separately exclude a `RelSim` with that input leg. Commutation without interface
purity therefore does not justify the ordinary
deterministic-marginal interpretation.

For symbolic contexts, `Static/Same` relates terms computed by the same recipe over
two frames; an apex role preserves this relation, including fresh allocations and
guards. `Static/Relational.relsim⇒≈ℰ` lifts the leaf span through the whole circuit.
This proves the following statement for every `𝔖` and `E`:

```agda
-- Symbolic.Static 𝔖 E
≈ₛ⇒≈ℰ : {Δ Ν : List Sort} {ζs ζs′ : All (Rcp Ν) Δ}
      → (∀ κ → frame κ Ν ζs ≈ₛ frame κ Ν ζs′)
      → Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′

-- Symbolic.Static.PairEnc (Σ₀/E₀ only)
≈ℰ⇔≈ₛ : {Δ Ν : List ⊤} {ζs ζs′ : All (Rcp Ν) Δ}
      → (Emitter Ν ζs Sym.≈ℰ Emitter Ν ζs′)
      ⇔ (∀ κ → frame κ Ν ζs ≈ₛ frame κ Ν ζs′)
```

`Static/Distinguish` proves the converse at E₀. Its tester queries every port,
allocates fresh names for the foreign names in the two recipes, and compares their
evaluations. `Distinguish/Run.run` proves the verdict under every naming, including
empty and multi-port frames. If kernel equality changes the existential naming,
a possibly non-injective renaming restores both the emitter's names and the
recipe's foreign names. There is no additional hypothesis on E₀.

**Multi-sort scope.** `Name = ℕ × ℕ` and recipe ownership remain unsorted:
`mine n` can occur at two sorts, whereas roles allocate a new raw name at each
`new s`. This is a representation limitation, not a demonstrated impossibility of
the static converse for admissible `EqTheory`.

The historical renaming-only contract admitted a proposed obstruction with distinct
sorts `s₁,s₂,s_f,s_y,s_m,s_c`, public `c₁ ≠ c₂ : s_m`,
`f : s₁ × s₂ → s_f`, `seal : s_m × s_y → s_c`, and
`open : s_c × s_f → s_m`, normalized by
`open(seal(x,y),f(name {s₁} n,name {s₂} n)) → x`.
Ordinary uniform name renaming preserves the shared raw code. Arbitrary
sort-preserving name-to-term substitution does not: map the `s₁` occurrence to
`name n₁` and the `s₂` occurrence to `name n₂`, where `n₁ ≠ n₂`. The substituted
left side is irreducible under that rule while the substituted right side remains
`x`. This semantic argument was not an Agda counterinstance; it is excluded by
the stronger closure and cannot refute a generic converse for the supported class.
Recipe-variable substitution alone is a different law and does not establish
admissibility.

`Deduction.SortBlind` records preservation under `Terms.renˢ`; every admissible
theory now has the witness `EqTheory.renˢ-cong`, including E₀'s existing
`Static/PairEnc.sort-blind`. The checked converse remains the E₀ theorem above:
generalizing its tester and naming-recovery proof to arbitrary sorted signatures
is not implemented, and no impossibility theorem is claimed for that class.
The computational steps 11–13 must use the actual E₀ theorem when they need this
equivalence.

## 4. Morphisms

`Sym≅ = StdUC 𝔻𝕐 ℰ≅` (built, §3.4) has the same tests, compared by `SameTerm (Y , T) (Y , T′) =
T ≈Term T′`. It shares 𝒞, ℐ and ℳ with `Sym`. The maps of §4.1–4.2 start from this syntactic
equality; §4.3 uses a separate certificate-bearing source with the same coherence equality.

### 4.1 `Sym≅ → Sym`

Built, in `Symbolic/Setup.agda`:

```agda
coarse : PresheafMorphism idF ℰ≅ ℰˢʸᵐ
coarse = record { ν = ntHelper record
  { η = λ _ → record { to = λ t → t ; cong = λ { (lift s) → lift (term⇒obs s) } }
  ; commute = λ _ → Setoid.refl (Functor.₀ ℰˢʸᵐ _) } }
coarse-epi : PresheafMorphism.Epi coarse
fine→sym : UCSetupMorphism Sym≅.StdSetup Sym.StdSetup
fine→sym = changeKernel ℰ≅ ℰˢʸᵐ coarse
```

`coarse` is Epi (`coarse-epi`). So `epi⇒preserves` and `Transfer.transfer` (with `grade-stable`)
carry every `Sym≅` emulation to `Sym`.

### 4.2 `Sym≅ → machine-iso`; no observational-quotient interpretation

`Symbolic/Machine.agda` implements:

```agda
Fᴿ : StrongMonoidalFunctor 𝔻𝕐 Machine.UC.machines
νᴿ : PresheafMorphism (StrongMonoidalFunctor.F Fᴿ) ℰ≅ Machine.UC.ℰ-tests
sym≅→iso : UCSetupMorphism Sym≅.StdSetup Machine.UC.StdSetup
```

`roleMachine` executes a role as a relation on its symbolic configurations. `new` chooses
arbitrary names, including names already used; equality guards use E, and emissions/registers
are canonicalized with E. There is no global freshness or initial-state condition in this
target semantics. The reversed machine tensor makes
`⟦ Y ⊗₀ A ⟧₀ = ⟦ A ⟧₀ ⊗₀ ⟦ Y ⟧₀` match the target's test shape.
`untick` removes the verdict interface's administrative input.

The free interpretation supplies functoriality and strong-monoidal coherence. `toᴿ-cong`
uses only source coherence, and `toᴿ-natural` uses machine associativity; `StdUCMorphism`
supplies the κ laws. These obligations make no cryptographic assertion. The public
`InterpretationTests.relational-consumer` instantiates the morphism at Σ₀/E₀.

This is not a map out of `Sym`'s observational quotient: source equality there quantifies
globally fresh DY contexts, whereas target equality is state isomorphism and target contexts
may be arbitrary relations on terms. The construction provides neither preservation of
that observational kernel nor an Epi/Mono/UC-transfer artifact.

### 4.3 Computational interpretation, admissibility, and conditional soundness

**Execution without certificates.** `Symbolic/Computational/Run.agda` defines `Scheme`
and `Execution`. A scheme supplies a carrier `Bits`, parameter-indexed primitive algorithms
`impl`, a nonce distribution, decidable bitstring equality, and sort tags. `evalᶜ` runs these
algorithms on recipes; `execᶜ` implements guards, independent nonce draws, and emissions.
No symbolic normalizer runs on bitstrings. `Scheme` itself asserts neither correct equations,
uniform nonce sampling, disjoint/injective tags, polynomial time, nor encryption security.

For every scheme, `Execution.runᶜ` compiles every role to an actual `Proc`, and
`Execution.Fᶜ η : StrongMonoidalFunctor 𝔻𝕐 𝔾ᵒ` extends the generators freely.
This unrestricted interpretation is a raw family of 𝔾ᵒ morphisms, **not** a morphism into
`Famᴹ`: the family category requires query-bound certificates.

**The universal rate-one claim is false.** One emission per activation does not mean one
query per activation **from above**. `Computational/Obstruction.backwards` receives a domain
`Pos` input and emits downward immediately, without budget from a codomain activation.
For any sort, any scheme with an inhabitant `b : Bits`, and any natural rate `c`, the module proves:

```agda
no-backwards-certificate : (c : ℕ) → ¬ Certified c (runᶜ 0 (backwards s))
```

Its single state cannot strictly decrease its potential on that downward response. The
certificate's refined response type is empty, but the actual response has mass one; coherence
would force `1 ≤ 0`. This refutes the proposed direct `rate-one` construction, not merely a
particular proof attempt. The theorem is about `Certified` for the actual runtime; it does not
silently assert the stronger statement about `QB`'s machine-equivalence closure.

**The certificate-bearing interpretation.** `Symbolic/Computational.agda` defines a distinct
`CertifiedSource sch`. Its generators contain unit-free endpoint witnesses, a role, a positive
natural rate, and a direct certificate for that role's actual runtime at every parameter:

```agda
bounded : (η : ℕ) → Certified (value rate) (Execution.runᶜ sch η role)
Fᶜ : StrongMonoidalFunctor 𝔻𝕐ᶜ Famᴹ
fine→comp : UCSetupMorphism Sym≅ᶜ.StdSetup ucSetupᴺ
```

`Sym≅ᶜ.StdSetup = StdUC 𝔻𝕐ᶜ ℰ≅ᶜ` is a new syntactic setup, not an alias for unrestricted
`Fine.Sym≅`. A generator carries the constant polynomial schedule `λ _ → rate`.
`certified⇒QB` and `qbᵒ` put its execution in the family grading, and `freeStrongMonoidal`
extends it to circuits. `νᶜ` closes the test ancilla with `deadᶠ`, compares only syntactic
coherence, and is natural by tensor interchange and left-unitor naturality.
This formal setup morphism makes no computational-security claim.

`InterpretationTests.CertifiedForward` supplies a real rate-one certificate for a forwarding
role for **every** scheme, constructs its generator, pins the carried schedule, consumes
`fine→comp`, and also consumes the backwards obstruction. Query admissibility is separate
from `SimpleC` and from feasibility.

**The derived theorem and its exact prerequisite.** `Symbolic/Soundness.agda` keeps the honest
source unrestricted and defines `SimpleC` pointwise on generator occurrences. `Feasible` is
an external predicate on certified tests and closures. A `Context` contains an arbitrary family
ancilla, such a test and closure, and their feasibility witnesses. Honest interpreted systems
are raw 𝔾ᵒ families; `_≈ᶠ_` compares the resulting Bool subdistributions negligibly in every
feasible context. It is not the target setup's canonical observational kernel.

`SimpleC` uses the repository's `Role.Simple`, not a proved CLC simple-process translation.
That predicate requires ground emissions on guard failure and at a designated halt control,
but does not require a uniform terminal response or enforce `cout(⊥) · 0`; a verdict role can
keep forwarding input bits there. The backtranslation must cover this actual, weaker class.

The strengthened `EqTheory` closes under sorted name-to-term substitution and retains
per-sort nontriviality. Its derived `fresh-name` and `name-injective` exclude equating a name
with a term that does not contain it, and identify E-equal names. `Deduction.⊬-fresh` rules out
deducing a name literally absent from a frame and not granted by ownership; `Run.emits≉fresh`
applies this fact to actual role emissions. These results close the old generic fresh-name
collapse attack, but do not establish secrecy of keys occurring inside ciphertexts or a
computational nonce-guessing bound. Raw name identity and ownership remain unsorted (§3.2).

`Backtranslation.extract` must, for each context and spectator family `W`, supply **before
choosing an honest system**:

- a parameter-indexed sampling distribution and symbolic test/closure for each sample;
- a `Maybe Bool` result for each simple honest circuit, with exact classification by symbolic
  `eval` (`nothing` accounts for no verdict);
- one context-dependent negligible error, uniform in the honest circuit, relating its actual
  computational observation to the sampled symbolic result.

No field mentions a pair of protocols, symbolic kernel equality, or the desired preservation
conclusion. `Derived.sound⁺` genuinely derives that conclusion: source kernel equality and
the classification laws make the sampled results agree; two operational approximation bounds
then give error `ε + ε`. Its inputs are `Backtranslation`, `SimpleC f`, `SimpleC g`, and
`f Sym.≈ℰ g`; its output quantifies every `W` and every feasible context.
`ConditionalConsumer.normalized-output` applies it to the Σ₀/E₀ echo and projected-pair echo.
The consumer remains parameterized by `Backtranslation`; it is not a constructed crypto
instance.

`Derived.sound-≤UC` additionally requires `SimpleC` for the symbolic dummy simulator chosen
by `Sym.≤UC⇒dummy`. It returns `DummyWitness`: that same explicit simulator, with negligible
agreement in every spectator/feasible context. It does **not** return the target's
adversary-quantified `≤UC`. No feasibility closure law is supplied to absorb arbitrary
computational adversaries, so that stronger UC corollary remains unproved.
`ConditionalConsumer.normalized-dummy` consumes this corollary from the concrete
`normalized-UC` source emulation; it has the same explicit backtranslation prerequisite.

**Determinism is not the missing CLC bridge.** `Soundness/Deterministic.trace⇒bisim` proves that
equal exact labeled traces of two total deterministic Mealy transitions yield a strong
bisimulation; `ExactEcho.echo-determinate` uses it on symbolic-role transitions. `Sym.≈ℰ`
instead compares verdicts of closed DY contexts, and CLC compares labeled frames modulo
static equivalence and applied-π observational equivalence. Neither required correspondence
follows from the exact-trace lemma, and no `det⇒∼o` theorem is claimed.

**Missing mathematical prerequisites, not assumed conclusions.** There is no constructed
`Backtranslation`, `CSSignature`, or `CSHyp` instance in this development. In particular the
repository has no reduction from joint IND-CPA/INT-CTXT to the labeled-frame attacker
extraction required above. Establishing computational soundness from those games needs:

| missing ingredient | intended source |
|---|---|
| correct tagged algorithms realizing E on honest values | AR §5.1; CLC §4.3 |
| labeled-frame simulation and attacker extraction from joint IND-CPA/INT-CTXT | CLC Defs 8–9, Thm 12 and Lemma 15 |
| a uniform-terminal CLC restriction for honest roles, rather than identifying it with the weaker `Role.Simple` | CLC §3.3 |
| key-level/acyclicity restrictions and one-use randomness discipline | CLC §3 and Def 11 |
| parsing and length observability, dishonest/registered-key rules, and a concrete PPT model | CLC §§3–5; `uc-setup-itm.md` §5.6 |
| quantitative nonce-guessing bound for a concrete uniform sampler | CH p. 395; BPW §5.3 |
| relation between this verdict kernel and the literature's frame/trace/observational semantics | CLC §§3–6; applied-π semantics |
| feasibility closure sufficient for adversary-quantified computational UC transfer | `uc-setup-itm.md` §5.6 |

These requirements are not replaced by a record field assuming `sound⁺`. The formal
interpretations, concrete certificate obstruction, exact-trace theorem, and derived
backtranslation implication are the reachable results; the advertised game-based
computational soundness and full UC transfer are not completed.

### 4.4 Other planned setups

None to or from `uc-setup-random-systems.md` (§4.3), `uc-setup-itm.md` (§4.4 there),
`uc-setup-ssp.md`, `uc-setup-ipdl.md` (both probabilistic, so §4.3 applies), or
`Examples/RelSetup.agda` (lax crossing). None to or from `uc-setup-causal-boxes.md` (§4 there):
zero-time rounds with an interleaving ⊗ have no causal-box image. A timed symbolic model is out
of scope.

## 5. Hard parts and risks

1. **Freshness.** Located names cost an occurrence bijection per `≈Term` constructor, about 25
   cases. The alternative is nominal sets with equivariance on every morphism. §4.2
   over-approximates freshness and transfers nothing. *Settled: located names.* The bijections
   are 24 cases in `Categories/FreeMonoidal/Decorated.agda`, 4 s warm. Coherence-only cases are
   isos of empty types. The rest are `⊎-assoc`, `⊎-cong` and seven small sum isos.
2. **No quotients.** Terms stay raw: `Tm-setoid` appears only in guards and deducibility. Guards
   are computed, so E must be decidable, and roles emit and store canonical forms, so `emit-≈E`
   carries E (§3.2): a convergent theory (`abadicortier2006` Props 3–4). `Term/PairEnc.E₀`
   decides by normal forms, which are its canonical forms.
3. **K and the seal.** K appears only in `Symbolic/Machine.agda`, as coinfectivity forces;
   `SameObs` inverts through `Decidable⇒UIP`. Generators go through `procᵒ`/`treeᵒ`. Never
   `unfolding 𝔾ᵒ` beside `StdUC` (12 GiB, `Enrichment.agda:12-13`); `Sym`'s `StdUC` is over 𝔻𝕐.
   Types at `curriedTensor machines` cost 9–15 min (`Machine/MonoidalCategory.agda:95-98`), so
   state them over abstract bundles, as in `Machine.UC.Kleisli`.
4. **Definitional matches.** The family interpretation reaches verdict `Δ Ωᵒ` through
   `atomᶠ`; `deadᶠ` coerces its empty interface using `unitᵒ` and `ifaceᵒ-onto`.
5. **Scope.** The family map needs per-generator query admissibility, and CLC's game-based
   soundness needs labeled-frame extraction plus a correspondence to this verdict kernel.
   Exact deterministic traces alone do not provide that correspondence (§4.3).
6. **Disagreements.**
   - Landscape: the symbolic setup is not "possibilistic next to machine-iso". It is
     deterministic up to names and has no morphism to machine-iso.
   - The comment at `WideSubcategory.agda:3-6` should point to §3.1.
   - "ν Mono ⇒ soundness": Mono gives completeness, not soundness (§4.3).
   - Memo §4.1 proposes `𝔽(Σ)/E`, a separate ℐ, and a deducibility kernel `≈s`. But E needs no
     quotient, ℐ = 𝒞 suffices, deducibility is not `≈s` (Props 3–4), and verdict tests already
     give `≈s` on frames.

## 6. Work breakdown

Each step lands in the named module and is accepted when green under the house gate with the
listed exports.

1. `Abstract2/Morphism.agda`: `transfer⁺`, with `transfer` re-derived and its type unchanged.
2. `Categories/FreeMonoidal.agda`: `freeStrongMonoidal`, reused by the ITM plan.
3. `Categories/FreeMonoidal/Decorated.agda`: `⟦⟧[]-resp-≈`, generic in `⟦v⟧`. **Built.**
4. `Symbolic/{Term,Deduction}.agda`: `⊢⇔⊢ᵢ`, plus a convergent pairing/encryption theory. **Built**,
   with the theory in `Symbolic/Term/PairEnc.agda` (§3.2).
5. `Symbolic/Role.agda`: `Role`, `GroundGuarded`, opt-in `Terminal`, a decidable `Atom`,
   and `emits⊢`. **Built** (§3.3); `Symbolic/{Test,TerminalTests}.agda` consume both runtimes.
6. `Symbolic/Fine.agda`: `Sym≅`, with `Sym≅.UC-compose` instantiated. **Built** (§3.4).
7. `Symbolic/Semantics.agda`: `eval-cong`, plus a two-role example that evaluates to `true`.
   **Built** (§3.5), with `runᴿ-≈E`.
8. `Symbolic/Setup.agda`: hypothesis-free `grade-stable`, `≈ᵁ⇔≈ℰ`, `emit-≈E`, `fine→sym`.
   **Built** (§3.6, §4.1), with `leaf-≈ℰ` and `coarse-epi`; `emit-≈E` needed canonical forms
   in `EqTheory` and `Role.Run` (§3.2), and `Symbolic/Test.agda` checks it at Σ₀.
9. `Symbolic/Static.agda`: generic `≈ₛ⇒≈ℰ`; `Static/PairEnc.agda`: E₀ `≈ℰ⇔≈ₛ`.
   **Built**, with `Static/{Emitter,Same,Relational,Distinguish}` and
   `Distinguish/{Tester,Run,Names}`. The functional case, feedback and G closure are
   in `Machines/Sim/Relational`, `UC/Machine/Relational`, `UC/Model/Relational`.
   `Symbolic/StaticTests` exercises the public equivalence. The multi-sort
   converse for admissible theories remains unproved; the historical weak-contract
   counterexample does not apply to the substitution-closed class (§3.7).
10. `Symbolic/Example/SecureChannel.agda`: the compatible fixed-public-message E₀
    fragment has the Eve-only `real≈simulated`, `real≤simulated` and the full
    honest/Eve-port `smt≤ideal`. The real protocol is the tensor of the ciphertext
    emitter and an honest emitter delivering `cst n`; the ideal leaves the Eve
    interface void and delivers the same `cst n`. The non-identity simulator is
    `Emitter keys (ciphertext 0)`, supplying `enc(cst 0, k′, r)`. `emitter-emits`
    and `Apex.context` carry the ciphertext span beside the unchanged honest wire;
    dummy completeness turns it into realization. `StaticTests` checks the public
    theorem. This is **not** the environment-selected-message interactive channel:
    that requires a relation following the plaintext across the run, whereas
    step 9's apex is parameterized by fixed frames. Step 9 alone is not that theorem.

11. `Symbolic/Machine.agda`: `sym≅→iso`. Formal relational interpretation of `Sym≅`;
    freshness and observational-kernel preservation are not asserted (§4.2).
12. `Symbolic/Computational{,/Run,/Obstruction}.agda`: unrestricted execution into 𝔾ᵒ;
    `fine→comp` from the distinct certificate-bearing `Sym≅ᶜ`; and
    `no-backwards-certificate`. The original universal rate-one source claim is false.
13. `Symbolic/Soundness{,/Deterministic}.agda`: exact-trace `trace⇒bisim` and the derived
    `Backtranslation → sound⁺`/`sound-≤UC` results, consumed by `InterpretationTests`.
    Game-based backtranslation, `det⇒∼o`, and the full computational UC order remain
    unavailable for the precise mathematical reasons in §4.3.
14. Docs: a pointer in the `WideSubcategory.agda` header, and `Sym` in landscape §5.

## 7. Sources

`backes2007rsim`, and `hofheinz2013` (via the ITM plan). `lowe1996` and `paulson1998inductive`
are background only.

Newly archived with PDF, `.txt`, INDEX lines and the `refs.bib` block "Symbolic UC setup plan":
`dolevyao1983` (`web.archive.org` copy of the `www.cs.huji.ac.il` file), `abadirogaway2002`,
`backes2003library` (ePrint 2003/015, converted from PostScript), `comonlundhcortier2008` (author
report, revised December 2008), `delaune2009simulation`, and `bohlunruh2013` (ePrint 2013/062;
its `.txt` drops some glyphs). No download was blocked.
