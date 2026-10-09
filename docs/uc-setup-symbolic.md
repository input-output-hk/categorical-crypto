# The symbolic (Dolev–Yao) UC setup — plan

Plan of 2026-10-09; nothing is typechecked, and statements about unwritten modules are design
claims. `[INFERENCE]` marks reasoning backed by neither a read source nor the tree. Citations are
`bibkey §/Def/p.` with printed pages (`docs/kb/sources/papers/INDEX.md`). Short names: CLC =
`comonlundhcortier2008`, CH = `canettiherzog2006`, BPW = `backes2003library`, AR = `abadirogaway2002`.

## 1. Summary

`Sym = StdUC 𝔻𝕐 ℰˢʸᵐ`, where 𝔻𝕐 is the free monoidal category (`Categories/FreeMonoidal.agda`)
on **Dolev–Yao roles**: finite reactive programs whose outputs are recipes over their own frame
(CH's roles, CLC's basic processes). Hom-equality is coherence `_≈Term_`. Tests are DY roles with
an ancilla, as in `Machine/UC.agda`. Two tests are equal when the same verdicts are possible under
some *globally fresh* naming, run in 𝔾ᵒ at term alphabets. The kernel is DY trace (may-testing)
equivalence; E is a kernel fact; `GradeStable` holds without hypotheses. Morphisms leave from the
syntactic twin `Sym≅`: to `Sym` (`changeKernel`), to machine-iso and to `ucSetupᴺ` (both
`StdUCMorphism`, unconditional). Computational soundness is a side-conditioned theorem over the
last. Nothing leaves `Sym` itself.

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

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Symbolic.Term where
record Signature : Set₁ where
  field Sort Sym : Set ; dom : Sym → List Sort ; cod : Sym → Sort ; _≟_ : DecidableEquality Sort
module _ (𝔖 : Signature) where
  open Signature 𝔖
  Name : Set
  Name = ℕ × ℕ                                   -- (occurrence code, counter); §3.5
  data Tm : Sort → Set where
    name : ∀ {s} → Name → Tm s
    app  : (f : Sym) → All Tm (dom f) → Tm (cod f)
  ren : (Name → Name) → ∀ {s} → Tm s → Tm s

  record EqTheory : Set₁ where                   -- abadi2018applied §2.2 p. 6
    field
      _≈E_       : ∀ {s} → Tm s → Tm s → Set
      isEquiv    : ∀ {s} → IsEquivalence (_≈E_ {s})
      app-cong   : ∀ f {ts us} → All₂ _≈E_ ts us → app f ts ≈E app f us
      ren-cong   : ∀ ρ {s} {t u : Tm s} → t ≈E u → ren ρ t ≈E ren ρ u
      _≟E_       : ∀ {s} → Decidable (_≈E_ {s})  -- guards are computed (§3.5)
      nontrivial : ∀ s → ∃₂ λ (t u : Tm s) → ¬ t ≈E u
    Tm-setoid : Sort → Setoid 0ℓ 0ℓ
    Tm-setoid s = record { Carrier = Tm s ; _≈_ = _≈E_ ; isEquivalence = isEquiv }

-- CategoricalCrypto.Symbolic.Deduction (𝔖 : Signature) (E : EqTheory 𝔖), same options
Frame : List Sort → Set
Frame = All Tm
data Recipe (Δ : List Sort) (own : Name → Set) : Sort → Set where    -- public symbols
  var  : ∀ {s} → s ∈ Δ → Recipe Δ own s
  mine : ∀ {s} n → own n → Recipe Δ own s
  app  : (f : Sym) → All (Recipe Δ own) (dom f) → Recipe Δ own (cod f)
_⊢_ : Frame Δ × (Name → Set) → Tm s → Set      -- abadicortier2006 Prop 1, as definition
(φ , own) ⊢ M = Σ[ ζ ∈ Recipe Δ own _ ] ζ ⟨ φ ⟩ ≈E M
data _⊢ᵢ_ (K : Frame Δ × (Name → Set)) : Tm s → Set where   -- the rules of §2.3 p. 6
  entry : (i : s ∈ Δ) → K ⊢ᵢ lookup (proj₁ K) i
  owned : proj₂ K n → K ⊢ᵢ name n
  apply : All (K ⊢ᵢ_) ts → K ⊢ᵢ app f ts
  conv  : K ⊢ᵢ M → M ≈E M′ → K ⊢ᵢ M′
⊢⇔⊢ᵢ : K ⊢ M ⇔ K ⊢ᵢ M
_≈ₛ_ : Frame Δ → Frame Δ → Set                 -- Def 2 p. 7; abadi2018applied Def 4.3
φ ≈ₛ ψ = ∀ {s} (ζ ζ′ : Recipe Δ (Foreign φ ψ) s) → (ζ ⟨ φ ⟩ ≈E ζ′ ⟨ φ ⟩) ⇔ (ζ ⟨ ψ ⟩ ≈E ζ′ ⟨ ψ ⟩)
```

### 3.3 Dolev–Yao roles: the generators

Atoms are ports. `port s t` carries sort `s` on `Pos` and sort `t` on `Neg` (𝔾ᵒ polarity,
`Iface.agda:3-5`). `verdict` is `Ωᴵ = Bool ⇿ ⊤`, and `void` is the closure source `𝟘ᵒ` on which
`Obs` is typed. On each input a role runs a decision tree — guards, fresh names, then one
emission and a jump.

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Symbolic.Role (𝔖 : Signature) where
data Atom : Set where
  port : (pos neg : Sort) → Atom ; verdict void : Atom
open FreeMonoidalHelper Mon Atom using (ObjTerm; flatten)
data Rcp (Δ : List Sort) : Sort → Set where            -- frame only: no built-in names
  var : ∀ {s} → s ∈ Δ → Rcp Δ s
  app : (f : Sym) → All (Rcp Δ) (dom f) → Rcp Δ (cod f)
data React (n : ℕ) (Γ : Fin n → List Sort) (O : List Kind) : List Sort → Set where
  test : ∀ {Δ s} → Rcp Δ s → Rcp Δ s → React n Γ O Δ → React n Γ O Δ → React n Γ O Δ
  new  : ∀ {Δ} s → React n Γ O (s ∷ Δ) → React n Γ O Δ
  emit : ∀ {Δ} (c : Fin n) → All (Rcp Δ) (Γ c) → (o : Out O) → Payload Δ o → React n Γ O Δ
record Role (x y : ObjTerm) : Set where              -- CLC basic processes, general `else`
  field
    n     : ℕ
    Γ     : Fin n → List Sort                        -- frame kept at each control point
    start : Fin n
    fresh : Γ start ≡ []                             -- secrets arise only through `new`
    react : (c : Fin n) (i : In x y) → React n Γ (Outs x y) (Γ c ++ carried i)
Simple : Role x y → Set                              -- CLC §3.3: `else` emits ⊥ and stops
-- a role is a DY deducer: every emitted term is deducible from what it received plus its own
-- fresh names (abadicortier2006 Prop 1; the recipe is the emitting branch's `Rcp`)
emits⊢ : Emits p c i m → (received c i , ownNames κ) ⊢ m
```

`In x y` lists the `Pos`-ports of `flatten x` together with the `Neg`-ports of `flatten y`;
`Outs x y` lists the converse. A `Payload` is a recipe, or a `Bool` on `verdict`. Everything is
first-order data in `Set`, as `FreeMonoidalData.mor` requires. Unbounded sessions are a single
role that dispatches on session tags. This is `bohlunruh2013`'s `!!` (Def 5.11 p. 42), the only
replication their composition theorem covers.

### 3.4 The category and its hom-setoid

```agda
{-# OPTIONS --safe --without-K #-}
module CategoricalCrypto.Symbolic.Fine (𝔖 : Signature) (E : EqTheory 𝔖) where
symData : FreeMonoidalData {0ℓ}
symData = record { v = Mon ; X = Atom ; mor = λ x y → UnitFree x × UnitFree y × Role x y }
open FreeMonoidal symData public                   -- ObjTerm, HomTerm, _≈Term_, FMC
𝔻𝕐 : MonoidalCategory 0ℓ 0ℓ 0ℓ
𝔻𝕐 = FMC
homˢ : ObjTerm → ObjTerm → Setoid 0ℓ 0ℓ             -- (HomTerm A B , _≈Term_)
homˢ A B = Category.hom-setoid FreeMonoidal {A} {B}
```

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
{-# OPTIONS --safe --without-K #-}
module Categories.FreeMonoidal.Decorated      -- new, general: one datum per generator occurrence
  (d : FreeMonoidalData) (⟦v⟧ : ⟦ v ⟧ᵥ) (⟦_⟧ᵖ₀ : X → C.Obj) (D : Set)
  (⟦_⟧ᵈ : ∀ {x y} → mor x y → D → ⟦ x ⟧₀ C.⇒ ⟦ y ⟧₀) where
Occ : HomTerm A B → Set
Occ (var _) = ⊤ ; Occ (g ∘ f) = Occ g ⊎ Occ f ; Occ (f ⊗₁ g) = Occ f ⊎ Occ g ; Occ _ = ⊥
⟦_⟧[_] : (f : HomTerm A B) → (Occ f → D) → ⟦ A ⟧₀ C.⇒ ⟦ B ⟧₀
⟦ var p ⟧[ ι ]  = ⟦ p ⟧ᵈ (ι tt)
⟦ g ∘ f ⟧[ ι ]  = ⟦ g ⟧[ ι ∘ inj₁ ] C.∘ ⟦ f ⟧[ ι ∘ inj₂ ]
⟦ f ⊗₁ g ⟧[ ι ] = ⟦ f ⟧[ ι ∘ inj₁ ] C.⊗₁ ⟦ g ⟧[ ι ∘ inj₂ ]   -- structural: as FreeFunctor
⟦⟧[]-resp-≈ : f ≈Term g → Σ[ π ∈ Occ f ↔ Occ g ] (∀ ι → ⟦ f ⟧[ ι ∘ Inverse.to π ] C.≈ ⟦ g ⟧[ ι ])

{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Semantics (𝔖 : Signature) (E : EqTheory 𝔖) where
atomᴵ : Atom → Iface
atomᴵ (port s t) = Tm s ⇿ Tm t ; atomᴵ verdict = Ωᴵ ; atomᴵ void = unitᴵ
runᴿ : ℕ → Role x y → Proc ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ   -- (control, frame, counter); names (κ , i); returnₚ
open Decorated symData (fromMC 𝔾ᵒ noSymmetric) (ifaceᵒ ∘ atomᴵ) ℕ
  (λ (ux , uy , p) κ → treeᵒ ux uy (procᵒ (runᴿ κ p)))
eval : HomTerm (Var void) (Var verdict) → Bool → Set      -- possible under fresh naming
eval c b = Σ[ ι ∈ (Occ c → ℕ) ] Injective _≡_ _≡_ ι × Obs ⟦ c ⟧[ ι ] ≈ₚ returnₚ b
eval-cong : c ≈Term c′ → ∀ b → eval c b ⇔ eval c′ b       -- ⟦⟧[]-resp-≈, obs-resp
```

`treeᵒ` coerces along `⊗ᵒ` (`Seal.agda:86-87`). Generator boundaries are unit-free because
`G.unit ≠ ifaceᵒ unitᴵ` (`Observation.agda:15-22`). Each occurrence gets its own name supply,
attackers included, so an attacker holds a protocol name only once it has been sent one. The
`∃ι` absorbs re-bracketing, so no equivariance lemma is needed here. Equivariance (`ren-cong`,
guards modulo E) makes the verdict independent of `ι`; only the soundness proof uses it.

### 3.6 The DY-environment presheaf and the setup

```agda
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Setup (𝔖 : Signature) (E : EqTheory 𝔖) where
Test Closure : ObjTerm → Set
Test A    = Σ[ Y ∈ ObjTerm ] HomTerm (Y ⊗₀ A) (Var verdict)   -- ancilla on the grade side
Closure A = HomTerm (Var void) A
data SameObs {A} : Test A → Test A → Set where   -- inverted via Decidable⇒UIP (≟ObjTerm)
  same : ∀ {Y E E′} → (∀ (m : Closure (Y ⊗₀ A)) b → eval (E ∘ m) b ⇔ eval (E′ ∘ m) b)
       → SameObs (Y , E) (Y , E′)
ℰᵒᵇˢ : Presheaf FreeMonoidal (Setoids 0ℓ 0ℓ)
ℰᵒᵇˢ = record
  { F₀ = λ A → record { Carrier = Test A ; _≈_ = SameObs ; isEquivalence = … }
  ; F₁ = λ f → record { to   = λ (Y , E) → Y , E ∘ (id ⊗₁ f)
                       ; cong = λ { (same h) → same λ m → h ((id ⊗₁ f) ∘ m) ⟨eval-cong assoc⟩ } }
  ; identity = … ; homomorphism = … ; F-resp-≈ = … }     -- eval-cong at coherence equations
ℰˢʸᵐ : Presheaf FreeMonoidal (Setoids (suc 0ℓ) (suc 0ℓ))
ℰˢʸᵐ = LiftSetoids (suc 0ℓ) (suc 0ℓ) ∘F ℰᵒᵇˢ
open StdUC 𝔻𝕐 ℰˢʸᵐ public

grade-stable : GradeStable   -- Machine/UC.agda:164-171, ancilla left: (Y,E) on Z ⊗ B is (Y ⊗ Z, E ∘ α⇒)
≈ᵁ⇔≈ℰ : f ≈ᵁ g ⇔ f ≈ℰ g
emit-≈E : (∀ c i → ReactE (react p c i) (react q c i)) → var p ≈ℰ var q   -- E lives in the kernel
```

The kernel `f ≈ℰ g` holds iff every DY environment and closure sharing an ancilla allows the
same verdicts; it is trace (may-testing) equivalence against DY contexts. Diff-equivalence
implies `∼o`, which implies this kernel, so ProVerif proofs certify it `[INFERENCE: needs a
translation of roles into applied-π]`. On frame emitters the kernel is static equivalence
(`abadi2018applied` Lemma 4.2 p. 15). `≤UC` is `bohlunruh2013` Def 4.3, and `≤UCᵈ⇔≤UC` is their
Lemma 4.4, here without hypotheses. The reflexivity concern of `delaune2009simulation` (p. 175)
does not arise: `≤UC-refl` takes `s = a`.

**Levels, options, layout.** 𝔻𝕐 lives at `0ℓ`. Tests are lifted to `cs = ℓs = suc 0ℓ`, which
matches machine-iso, ℰᵒ, ℰᴿ and `ucSetupᴺ` (`Enrichment.agda:46`). So
`Sym : UCSetup 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ (suc 0ℓ) (suc 0ℓ)`. Everything is `--safe --without-K`, with
two exceptions: `--guardedness` from `Semantics` on, and K in `Symbolic/Machine.agda`. The modules
under `Symbolic/` are `Term`, `Deduction`, `Role`, `Fine`, `Semantics`, `Setup`, `Static`,
`Machine`, `Computational`, `Soundness` and `Example/SecureChannel`. General additions:
`freeStrongMonoidal`, `Categories/FreeMonoidal/Decorated.agda`, and `transfer⁺` in
`Abstract2/Morphism.agda`.

## 4. Morphisms

`Sym≅ = StdUC 𝔻𝕐 ℰ≅` has the same tests, compared by `SameTerm (Y , E) (Y , E′) = E ≈Term E′`. It
shares 𝒞, ℐ and ℳ with `Sym`. Every morphism starts from it, so each `ν`'s `cong` is
`⟦⟧-resp-≈`.

### 4.1 `Sym≅ → Sym`

```agda
coarse : PresheafMorphism idF ℰ≅ ℰˢʸᵐ
coarse = record { ν = ntHelper record
  { η = λ _ → record { to = λ t → t
                     ; cong = λ { (lift (same e)) → lift (same λ m → eval-cong (∘-resp-≈ e ≈-Term-refl)) } }
  ; commute = λ _ → refl } }
fine→sym : UCSetupMorphism Sym≅.StdSetup StdSetup
fine→sym = changeKernel ℰ≅ ℰˢʸᵐ coarse
```

`coarse` is Epi. So `epi⇒preserves` and `Transfer.transfer` (with `grade-stable`) carry every
`Sym≅` emulation to `Sym`.

### 4.2 `Sym≅ → machine-iso`; nothing from `Sym`

```agda
{-# OPTIONS --safe #-}
module CategoricalCrypto.Symbolic.Machine (𝔖 : Signature) (E : EqTheory 𝔖) where
relational : FreeFunctorData symData
relational = record
  { ⟦v⟧   = fromMC machines noSymmetric                 -- Machine.UC.machines (reversed)
  ; ⟦_⟧ᵖ₀ = λ { (port s t) → Tm s ⇿ Tm t ; verdict → Bool ⇿ ⊤ ; void → I }
  ; ⟦_⟧ᵖ₁ = roleMachine }            -- guards as ≈E; `new` picks any name; always `just`
Fᴿ : StrongMonoidalFunctor 𝔻𝕐 machines
Fᴿ = freeStrongMonoidal relational                      -- Φ = Fᴿ, κ = Oplax.δ = id
νᴿ : PresheafMorphism (StrongMonoidalFunctor.F Fᴿ) ℰ≅ ℰ-tests
νᴿ = record { ν = ntHelper record
  { η = λ A → record { to   = λ (Y , E) → ⟦ Y ⟧₀ , untick CC.∘ ⟦ E ⟧₁   -- untick : Bool ⇿ ⊤ ⇒ ℰ-Out
                     ; cong = λ { (lift (same e)) → same (refl⟩∘⟨ ⟦⟧-resp-≈ e) } }
  ; commute = λ f → same ∘-assoc-≅ᴹ } }
sym≅→iso : UCSetupMorphism Sym≅.StdSetup Machine.UC.StdSetup
sym≅→iso = StdUCMorphism 𝔻𝕐 machines ℰ≅ ℰ-tests Fᴿ νᴿ
```

Reversal makes the shapes agree: `⟦ Y ⊗₀ A ⟧₀ = ⟦ A ⟧₀ ⊗₀ ⟦ Y ⟧₀`, which is machine-iso's
`Machine (A ⊗₀ Y) ℰ-Out`. None of the obligations is cryptographic. `F-resp-≈` is free;
strong-monoidal coherence follows from `⊗₁-id` and `∘-identityˡ-≅ᴹ`; the κ laws come from
`StdUCMorphism`; naturality is `∘-assoc-≅ᴹ`. This is the "forget E, terms as sets" map, and E
survives only in guards. It transfers nothing: `νᴿ` is not Epi (most machine-iso tests are not
DY) and not Mono (different circuits can have isomorphic semantics).

`Sym → machine-iso` does not exist, for three reasons:
- `cong` would need observationally equal tests to be state-isomorphic;
- machine-iso's environments are arbitrary relations on raw terms, which see through encryption,
  so no coarser test equality respects `Sym`'s kernel;
- `⟦_⟧[_]` is not a functor.

The same three reasons exclude `Sym → 𝔾ᵒ` at term alphabets.

### 4.3 Computational soundness over `Sym≅ → ucSetupᴺ`

**Target.** `UC.Model.Family.ucSetupᴺ = StdUC Famᴹ ℰᴺ`, the negligible tier over 𝔾ᵒ. Random
systems 𝔾ᴿ has no asymptotic tier (`uc-setup-random-systems.md` §3.1). Exact (Δ = 0) soundness
into 𝔾ᴿ fails as soon as names appear: a `Dₚ` machine samples them from a finite space, so they
can be guessed with positive probability (CH p. 395; BPW §5.3 p. 19). RS identities still reach
this target through that plan's `≈ᴿ ⇒ 𝔾ᵒ.≈ᵁ`.

```agda
{-# OPTIONS --safe --without-K --guardedness #-}
module CategoricalCrypto.Symbolic.Computational (𝔖 : Signature) (E : EqTheory 𝔖) where
record Scheme : Set₁ where                    -- CoSP's computational implementation; AR Fig. 1
  field Bits  : Set
        impl  : (f : Sym) → ℕ → All (λ _ → Bits) (dom f) → Bits   -- coins are explicit names
        nonce : ℕ → Dₚ Bits                                       -- uniform on {0,1}^η
        _≟ᵇ_  : DecidableEquality Bits
        tag   : Sort → Bits → Bits                                -- CLC §5.1 p. 19
computational : Scheme → FreeFunctorData symData
computational sch = record
  { ⟦v⟧   = fromMC Famᴹ noSymmetric
  ; ⟦_⟧ᵖ₀ = λ { (port _ _) → ifaceᶠ (λ _ → Bits ⇿ Bits) ; verdict → Δ Ωᵒ ; void → Δ 𝟘ᵒ }
  ; ⟦_⟧ᵖ₁ = λ (_ , _ , p) → family (λ η → treeᵒ … (procᵒ (runᶜ sch η p))) (rate-one p) }
Fᶜ : Scheme → StrongMonoidalFunctor 𝔻𝕐 Famᴹ                  -- Φ = Fᶜ, κ = Oplax.δ = id
Fᶜ = freeStrongMonoidal ∘ computational
νᶜ : (sch : Scheme) → PresheafMorphism (StrongMonoidalFunctor.F (Fᶜ sch)) ℰ≅ ℰᴺ
νᶜ sch .η A = λ (Y , E) → ⟦ E ⟧₁ Famᴹ.∘ (deadᶠ Famᴹ.⊗₁ Famᴹ.id) Famᴹ.∘ Famᴹ.λ⇐  -- ancilla closed
fine→comp : Scheme → UCSetupMorphism Sym≅.StdSetup ucSetupᴺ
fine→comp sch = StdUCMorphism 𝔻𝕐 Famᴹ ℰ≅ ℰᴺ (Fᶜ sch) (νᶜ sch)      -- ℰᴺ = UCSetup.ℰ ucSetupᴺ
```

| obligation | discharged by | crypto |
|---|---|---|
| functor, `F-resp-≈`, strong monoidal | `freeFunctor`, `⟦⟧-resp-≈`, `freeStrongMonoidal` | none |
| `κ-return`, `κ-ext`, `κ-sub` | `StdUCMorphism` | none |
| generators land in `Famᴹ` | `rate-one`: each reaction emits one message | none |
| `νᶜ` cong (from `ℰ≅`), naturality | `⟦⟧-resp-≈`, `≈⇒≋`; `⊗-∘-dist`, `λ⇐` naturality | none |
| `νᶜ` cong from `ℰˢʸᵐ` (`Sym → ucSetupᴺ`) | soundness with arbitrary DY tests as honest systems | open: non-failing `else` (CLC §8 p. 34) |

**Where soundness lives.** Soundness is preservation of the kernel. `Mono` gives *reflection*
(`mono⇒reflects`, `Presheaf/Morphism.agda:81-83`), i.e. computational ⇒ symbolic; that is
completeness, the other half of CH Thm 1, and it fails in AR (p. 124). Preservation would follow
from `Epi` (`epi⇒preserves`, lines 73-79), but `νᶜ` is not Epi: few PPT distinguishers are images
of DY tests. `Factorization (fine→comp sch)` puts the content in the right place. The image
kernel is agreement under *interpreted* DY attackers. Passing from it to the target kernel,
across the Mono half `image-morphism`, is exactly CH Lemma 1: on interpreted protocols, every
feasible attacker behaves like an interpreted DY attacker. `sound⁺` proves the composite
directly, for simple honest systems and under side conditions:

```agda
module Soundness (sch : Scheme) (Feasible : ∀ {A B} → A Famᴹ.⇒ B → Set)   -- itm §5.6: open
                 (hyp : CSHyp sch Feasible) where
  open Transfer (fine→comp sch)
  _≈ᶠ_ : A Famᴹ.⇒ B → A Famᴹ.⇒ B → Set     -- agreement on Feasible tests/closures: no kernel
  sound⁺ : ∀ {A B} {f g : HomTerm A B} → SimpleC f → SimpleC g
         → f ≈ℰ g → ∀ Y′ → Famᴹ.id {Y′} Famᴹ.⊗₁ F.₁ f ≈ᶠ Famᴹ.id {Y′} Famᴹ.⊗₁ F.₁ g
record CSSignature : Set₁ where              -- CLC §3, made compositional
  field sig : Signature ; level : Sort → Maybe ℕ   -- enc at level ℓ+1 takes keys of level ≤ ℓ
        lenTest : … ; typed : … ; randOne : …      -- §3.2 p. 10; §5.1 p. 19; §3.3 p. 11
record CSHyp (sch : Scheme) (Feasible : …) : Set₁ where
  field correct  : Realizes sch E                  -- E-axioms on tagged honest values
        ind-cpa  : LR-CPA₀ sch ≈ᶠ LR-CPA₁ sch      -- joint IND-CPA = AR type 3 (CLC Def 8)
        int-ctxt : CTXT₀ sch ≈ᶠ CTXT₁ sch          -- CLC Def 9
```

| ingredient of `sound⁺` | hypothesis | source |
|---|---|---|
| E-equal honest terms evaluate equally | `correct` | AR §5.1; CLC §4.3 p. 14 |
| ciphertexts hide plaintexts | joint IND-CPA + INT-CTXT; IND-CCA2, EUF-CMA for public-key encryption and signatures | CLC Thm 12; BPW Defs 5.1–5.2, Thm 7.1 |
| no key cycles | key-level sorts (sufficient for CLC Def 11 `[INFERENCE]`) | CLC Def 11 p. 19; AR §3.1 |
| parsing, lengths | `tag`/`typed`; lengths observable in guards | CLC §5.1 p. 19, §3.2 p. 10; BPW §2.2 |
| honest systems | `SimpleC f`, `SimpleC g`: every occurrence `Simple` | CLC §3.3 pp. 10–12 |
| dishonest keys, PPT attackers | `Feasible` on tests and closures (registered keys, time bounds) | CLC p. 15, Defs 2, 4; itm §5.6 |
| nonce guessing | none (statistical, `≤ q·2^{-η}`) | CH p. 395; BPW §5.3 p. 19 |
| trace vs `∼o` | roles deterministic, hence determinate | lemma `det⇒∼o` (§6 step 13) |

**The hypotheses are neither a `WideSubcategory` nor data of `F`.** Feasible machines form no
category: no identity is a priori polynomial, and the double repeater breaks composition. This
obstruction is `uc-setup-itm.md` §5.6, after `hofheinz2013`; a feasible target is unowned and
open. A feasible-closure presheaf on `Famᴹ` is not functorial along infeasible maps. So
`Feasible` and the security artifacts are side conditions of the theorem, and `F` needs only the
algorithms. The source restrictions are pointwise (`SimpleC`) or live in the signature
(`CSSignature`), so `Sym`'s attackers keep full DY strength. Restricting `Sym` to simple roles
would weaken its tests and make soundness *harder*.

**From kernels to emulation.** `Transfer.transfer` needs `Epi` and a target `GradeStable`. Neither
holds here: ℰᵒ is not `GradeStable` (`uc-setup-random-systems.md` §5.3). A pointwise variant
takes exactly what `sound⁺` provides:

```agda
transfer⁺ : (f≤g : f S.≤UC g) (let s₀ = proj₁ (S.≤UC⇒dummy f≤g))   -- Abstract2/Morphism, Transfer
          → (∀ Y′ → S′.T₁ Y′ (F.₁ f) S′.≈ℰ S′.T₁ Y′ (F.₁ (S.sub s₀ S.𝒞.∘ g)))
          → G f S′.≤UC G g
-- transfer = transfer⁺ fed λ Y′ → gs′ Y′ (epi⇒preserves-≈ℰ epi …)
```

The proof is `transfer`'s, with `T₁ Y′ κ` post-composed (`T-homomorphism`, `≈ℰ-cong-post`), and
it already covers information-theoretic interpretations. The computational corollary is a
side-conditioned twin:
`sound-≤UC : SimpleC f → SimpleC g → SimpleC s₀ → f ≤UC g → ≤UCᶠ (G f) (G g)`.
The simulator is honest in the ideal world, so it must be simple too. How side-conditioned
emulations compose is open (`uc-setup-itm.md` §5.6). Inside `Sym`, `UC-compose` and
`dummy-complete` stay unconditional; only the final emulation crosses.

**Ideal interpretation, rejected.** Interpreting encryption by `Fcpke` or `TH_H` would make
soundness statistical and condition-free (CH p. 395). But the table would then be shared across
morphisms, so `F` would be neither local nor a functor. The sharing analysis is in §3.3 of the
2026-07-31 memo `docs/uc-symbolic-crypto.md` (main checkout, untracked).

### 4.4 Other planned setups

None to or from `uc-setup-random-systems.md` (§4.3), `uc-setup-itm.md` (§4.4 there),
`uc-setup-ssp.md`, `uc-setup-ipdl.md` (both probabilistic, so §4.3 applies), or
`Examples/RelSetup.agda` (lax crossing). None to or from `uc-setup-causal-boxes.md` (§4 there):
zero-time rounds with an interleaving ⊗ have no causal-box image. A timed symbolic model is out
of scope.

## 5. Hard parts and risks

1. **Freshness.** Located names cost an occurrence bijection per `≈Term` constructor, about 25
   cases. The alternative is nominal sets with equivariance on every morphism. §4.2
   over-approximates freshness and transfers nothing.
2. **No quotients.** Terms stay raw: `Tm-setoid` appears only in guards and deducibility, and
   `emit-≈E` carries E. Guards are computed, so E must be decidable (convergent theories;
   `abadicortier2006` Props 3–4).
3. **K and the seal.** K appears only in `Symbolic/Machine.agda`, as coinfectivity forces;
   `SameObs` inverts through `Decidable⇒UIP`. Generators go through `procᵒ`/`treeᵒ`. Never
   `unfolding 𝔾ᵒ` beside `StdUC` (12 GiB, `Enrichment.agda:12-13`); `Sym`'s `StdUC` is over 𝔻𝕐.
   Types at `curriedTensor machines` cost 9–15 min (`Machine/MonoidalCategory.agda:95-98`), so
   state them over abstract bundles, as in `Machine.UC.Kleisli`.
4. **Definitional matches.** `F₀ (Var verdict)` must be `Δ Ωᵒ` on the nose
   (`UC/Family.agda:115`), or `νᶜ` needs a coercion. `deadᶠ` is built at `objᵒ G.unit`.
5. **Scope.** CLC covers symmetric encryption, pairing, simple processes and `∼o`. Our kernel is
   trace-style, so `det⇒∼o` is needed. Public-key primitives have only realization results (BPW,
   CH). The proof is research-grade (CLC §§5–6, Lemma 15 p. 22).
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
3. `Categories/FreeMonoidal/Decorated.agda`: `⟦⟧[]-resp-≈`, generic in `⟦v⟧`.
4. `Symbolic/{Term,Deduction}.agda`: `⊢⇔⊢ᵢ`, plus a convergent pairing/encryption theory.
5. `Symbolic/Role.agda`: `Role`, `Simple`, a decidable `Atom`, and `emits⊢`, which shows that roles
   are DY deducers.
6. `Symbolic/Fine.agda`: `Sym≅`, with `Sym≅.UC-compose` instantiated.
7. `Symbolic/Semantics.agda`: `eval-cong`, plus a two-role example that evaluates to `true`.
8. `Symbolic/Setup.agda`: hypothesis-free `grade-stable`, `≈ᵁ⇔≈ℰ`, `emit-≈E`, `fine→sym`.
9. `Symbolic/Static.agda`: `≈ℰ⇔≈ₛ` on frame emitters.
10. `Symbolic/Example/SecureChannel.agda`: `smt≤ideal`, with simulator `enc(0_ℓ, k′, r)`
    (proved by `dummy-complete` and step 9).
11. `Symbolic/Machine.agda`: `sym≅→iso`, with a warm check inside the budget.
12. `Symbolic/Computational.agda`: `fine→comp`.
13. `Symbolic/Soundness.agda`: `det⇒∼o`, `sound⁺`, `sound-≤UC`. Pairing and symmetric encryption
    first, with `Feasible` abstract and no postulates.
14. Docs: a pointer in the `WideSubcategory.agda` header, and `Sym` in landscape §5.

## 7. Sources

Used: `abadi2018applied`, `abadicortier2006`, `blanchet2016proverif`, `canettiherzog2006`,
`backes2007rsim`, and `hofheinz2013` (via the ITM plan). `lowe1996` and `paulson1998inductive`
are background only.

Newly archived with PDF, `.txt`, INDEX lines and the `refs.bib` block "Symbolic UC setup plan":
`dolevyao1983` (`web.archive.org` copy of the `www.cs.huji.ac.il` file), `abadirogaway2002`,
`backes2003library` (ePrint 2003/015, converted from PostScript), `comonlundhcortier2008` (author
report, revised December 2008), `delaune2009simulation`, and `bohlunruh2013` (ePrint 2013/062;
its `.txt` drops some glyphs). No download was blocked.
