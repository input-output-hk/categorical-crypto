{-# OPTIONS --safe --without-K #-}

-- The closed extraction game, and its ε.
--
-- Two reactive kernels over the same adversary alphabet — `respR`, the real
-- commitment protocol talking to a lazily sampled oracle, and `respI`, the
-- ideal functionality with the extracting simulator in front of it — and the
-- statement that no adaptive adversary of `m` queries tells them apart by more
-- than `(m² + m)·2⁻ᵏ + m·2⁻ᵏ`.
--
-- The coupling `respB` runs ONE oracle table and emits both answers.  They
-- differ only at an opening that the receiver accepts and the simulator cannot
-- deliver, and `agree-off` says the two flags already cover that: a repeat in
-- the oracle's answer log (`Potential.collision-cert`) or a fresh sample
-- landing on the outstanding commitment digest (`Potential.rare-cert`, drift
-- `2⁻ᵏ` by `guess-drift` — the point is drawn BY the oracle at the query, so
-- `docs/ro-game-hop.md`'s fixed-secret caveat does not bite).  `∨-cert` adds
-- them and `hop-bound` assembles; no new induction and no new supermartingale.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true; _∨_)
open import Data.Bool.Properties using (∨-identityʳ; ∨-zeroʳ)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _*_; _+_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (+-identityʳ; +-monoʳ-≤; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (head) renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (yes; no; ⌊_⌋)

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform using
  (0≤inv-pow-2; bool→ℚ; fromℕ; inv-pow-2; uniform-Vec)

module CategoricalCrypto.Examples.ROCommitment.Game (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import ProbabilisticLogic.Distribution.Uniform.Duplicate k using (dup; memb)

------------------------------------------------------------------------
-- The alphabet and the three state spaces

-- What a corrupted committer can do: query the oracle, send the commitment,
-- send the opening.
data Q : Set where
  askQ : Pt → Q
  comQ : Dig → Q
  opnQ : Bool → Dig → Q

-- …and what it sees back, the receiver's own reaction included.
data R : Set where
  ansR  : Dig → R
  rcptR : R
  outR  : Bool → R
  failR : R
  idleR : R

-- The commitment digest, and the bit the simulator extracted for it.
Com : Set
Com = Maybe (Dig × Bool)

St StR StI : Set
St  = Tbl × (Com × Bool)      -- the coupling: table, commitment, the hit flag
StR = Tbl × Maybe Dig         -- the real game: table, commitment
StI = Tbl × Com               -- the ideal game: table, commitment + extraction

tblOf : St → Tbl
tblOf (t , _ , _) = t

hitOf : St → Bool
hitOf (_ , _ , f) = f

logOf : St → List Dig
logOf (t , _ , _) = answers t

digOf : Com → Maybe Dig
digOf nothing        = nothing
digOf (just (c , _)) = just c

eraseR : St → StR
eraseR (t , m , _) = t , digOf m

eraseI : St → StI
eraseI (t , m , _) = t , m

------------------------------------------------------------------------
-- The lazily sampled oracle

-- The reference games carry no flag, so their oracle is the same function at
-- any ancilla; the coupling's additionally records a sample that lands on the
-- outstanding digest.
fetchT : {M : Set} → Tbl × M → Pt → Dist-ℚ ((Tbl × M) × Dig)
fetchT (t , m) x with lookupPt t x
... | just d  = return-ℚ ((t , m) , d)
... | nothing = uniform-Vec k >>=ᴹ λ h → return-ℚ (((x , h) ∷ t , m) , h)

raise : Com → Dig → Bool
raise nothing        _ = false
raise (just (c , _)) h = ⌊ h ≟ c ⌋

fetch : St → Pt → Dist-ℚ (St × Dig)
fetch (t , m , f) x with lookupPt t x
... | just d  = return-ℚ ((t , m , f) , d)
... | nothing = uniform-Vec k >>=ᴹ λ h → return-ℚ (((x , h) ∷ t , m , f ∨ raise m h) , h)

lookup-here : (x : Pt) (d : Dig) (L : Tbl) → lookupPt ((x , d) ∷ L) x ≡ just d
lookup-here x d L with x ≟ x
... | yes _  = refl
... | no  ne = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- The two games and the coupling

-- The receiver accepts an opening whose digest is the one it stored; the
-- functionality opens only when the extraction agrees with the claim too.
realOpen : Dig → Bool → Dig → R
realOpen c b h = cond ⌊ h ≟ c ⌋ (outR b) failR

idealOpen : Dig → Bool → Bool → Dig → R
idealOpen c e b h = cond ⌊ h ≟ c ⌋ (cond ⌊ b ≟ e ⌋ (outR e) failR) failR

askX : {M : Set} → Tbl × M → Pt → Dist-ℚ ((Tbl × M) × R)
askX s x = fetchT s x >>=ᴹ λ u → return-ℚ (proj₁ u , ansR (proj₂ u))

comR : StR → Dig → Dist-ℚ (StR × R)
comR (t , nothing) c = return-ℚ ((t , just c) , rcptR)
comR (t , just c)  _ = return-ℚ ((t , just c) , idleR)

opnR : StR → Bool → Dig → Dist-ℚ (StR × R)
opnR (t , nothing) _ _ = return-ℚ ((t , nothing) , idleR)
opnR (t , just c)  b r = fetchT (t , just c) (b ∷ᵛ r) >>=ᴹ λ u →
  return-ℚ (proj₁ u , realOpen c b (proj₂ u))

respR : StR → Q → Dist-ℚ (StR × R)
respR s (askQ x)   = askX s x
respR s (comQ c)   = comR s c
respR s (opnQ b r) = opnR s b r

comI : StI → Dig → Dist-ℚ (StI × R)
comI (t , nothing) c = return-ℚ ((t , just (c , extract c t)) , rcptR)
comI (t , just m)  _ = return-ℚ ((t , just m) , idleR)

opnI : StI → Bool → Dig → Dist-ℚ (StI × R)
opnI (t , nothing)      _ _ = return-ℚ ((t , nothing) , idleR)
opnI (t , just (c , e)) b r = fetchT (t , just (c , e)) (b ∷ᵛ r) >>=ᴹ λ u →
  return-ℚ (proj₁ u , idealOpen c e b (proj₂ u))

respI : StI → Q → Dist-ℚ (StI × R)
respI s (askQ x)   = askX s x
respI s (comQ c)   = comI s c
respI s (opnQ b r) = opnI s b r

askB : St → Pt → Dist-ℚ (St × (R × R))
askB s x = fetch s x >>=ᴹ λ u → return-ℚ (proj₁ u , (ansR (proj₂ u) , ansR (proj₂ u)))

comB : St → Dig → Dist-ℚ (St × (R × R))
comB (t , nothing , f) c = return-ℚ ((t , just (c , extract c t) , f) , (rcptR , rcptR))
comB (t , just m , f)  _ = return-ℚ ((t , just m , f) , (idleR , idleR))

opnB : St → Bool → Dig → Dist-ℚ (St × (R × R))
opnB (t , nothing , f)      _ _ = return-ℚ ((t , nothing , f) , (idleR , idleR))
opnB (t , just (c , e) , f) b r = fetch (t , just (c , e) , f) (b ∷ᵛ r) >>=ᴹ λ u →
  return-ℚ (proj₁ u , (realOpen c b (proj₂ u) , idealOpen c e b (proj₂ u)))

respB : St → Q → Dist-ℚ (St × (R × R))
respB s (askQ x)   = askB s x
respB s (comQ c)   = comB s c
respB s (opnQ b r) = opnB s b r

-- The bad event: a repeat in the oracle's answer log, or a sample that hit the
-- outstanding commitment digest.
bad : St → Bool
bad (t , _ , f) = dup (answers t) ∨ f

module C = Coupling bad respB

s₀ : St
s₀ = [] , nothing , false

sR₀ : StR
sR₀ = [] , nothing

sI₀ : StI
sI₀ = [] , nothing

------------------------------------------------------------------------
-- The invariant: the extraction is pinned unless the flags are up

Good : Com → Tbl → Set
Good nothing        _ = ⊤
Good (just (c , e)) t = Pins c e t

Inv : St → Set
Inv (t , m , f) = (dup (answers t) ∨ f) ≡ true ⊎ Good m t

inv₀ : Inv s₀
inv₀ = inj₂ tt

private
  -- Both flags are monotone, so a run that is already bad stays bad.
  bad-grow : (L : List Dig) (d : Dig) (g g′ : Bool) → (g ≡ true → g′ ≡ true)
           → (dup L ∨ g) ≡ true → (dup (d ∷ L) ∨ g′) ≡ true
  bad-grow L d g g′ up e = aux (dup L) refl
    where
    aux : (x : Bool) → dup L ≡ x → (dup (d ∷ L) ∨ g′) ≡ true
    aux true  dl = cong (_∨ g′) (trans (cong (memb d L ∨_) dl) (∨-zeroʳ (memb d L)))
    aux false dl = trans (cong (dup (d ∷ L) ∨_) (up (trans (sym (cong (_∨ g) dl)) e)))
                         (∨-zeroʳ (dup (d ∷ L)))

  keep-true : (g : Bool) → g ≡ true → (g ∨ false) ≡ true
  keep-true g e = cong (_∨ false) e

-- A fresh sample either hits the outstanding digest — and then the flag is up
-- — or adds no preimage of it.
inv-sample : (t : Tbl) (m : Com) (f : Bool) (x : Pt) (h : Dig)
           → Inv (t , m , f) → Inv ((x , h) ∷ t , m , f ∨ raise m h)
inv-sample t nothing        f x h _   = inj₂ tt
inv-sample t (just (c , e)) f x h inv with h ≟ c
... | yes _  = inj₁ (trans (cong (dup (h ∷ answers t) ∨_) (∨-zeroʳ f))
                           (∨-zeroʳ (dup (h ∷ answers t))))
... | no h≢c = case inv of λ where
  (inj₁ bt) → inj₁ (bad-grow (answers t) h f (f ∨ false) (keep-true f) bt)
  (inj₂ gd) → inj₂ (pins-∷ c e x h t h≢c gd)

-- …and the commitment pins the extraction at a duplicate-free log.
inv-commit : (t : Tbl) (f : Bool) (c : Dig) → Inv (t , just (c , extract c t) , f)
inv-commit t f c = aux (dup (answers t)) refl
  where
  aux : (x : Bool) → dup (answers t) ≡ x → Inv (t , just (c , extract c t) , f)
  aux true  dl = inj₁ (cong (_∨ f) dl)
  aux false dl = inj₂ (pins-extract c t dl)

-- The agreement off the bad event: an accepted opening whose point is in the
-- table opens to the extracted bit, so the two games answer alike.
agree-off : (t : Tbl) (c : Dig) (e f b : Bool) (x : Pt) (d : Dig)
          → Inv (t , just (c , e) , f) → (dup (answers t) ∨ f) ≡ false
          → lookupPt t x ≡ just d → head x ≡ b
          → realOpen c b d ≡ idealOpen c e b d
agree-off t c e f b x d inv nb hit hx with d ≟ c
... | no  _   = refl
... | yes d≡c with b ≟ e
...   | yes b≡e = cong outR b≡e
...   | no  b≢e = ⊥-elim (b≢e (trans (sym hx) (pins-lookup c e t x d hit pins d≡c)))
  where
  pins : Pins c e t
  pins = case inv of λ where
    (inj₁ bt) → case trans (sym bt) nb of λ ()
    (inj₂ p)  → p

------------------------------------------------------------------------
-- Both marginals are the reference games

module _ {M : Set} (er : Com → M) where

  ec : St → Tbl × M
  ec (t , m , _) = t , er m

  -- One oracle call, coupled: the two tables move alike, the post-state keeps
  -- the invariant, and the point just fetched is in the table — which is what
  -- `agree-off` needs and what the `with` alone would have thrown away.
  fetch-bis : (s : St) (x : Pt) (G : St × Dig → ℚ) (G′ : (Tbl × M) × Dig → ℚ)
            → Inv s
            → ((u : St × Dig) (u′ : (Tbl × M) × Dig)
               → ec (proj₁ u) ≡ proj₁ u′ → Inv (proj₁ u)
               → lookupPt (tblOf (proj₁ u)) x ≡ just (proj₂ u)
               → proj₂ u ≡ proj₂ u′ → G u ≡ G′ u′)
            → E (fetch s x) G ≡ E (fetchT (ec s) x) G′
  fetch-bis (t , m , f) x G G′ inv pt with lookupPt t x in eq
  ... | just d  = trans (lookupᴰℚ-return _ G)
                 (trans (pt _ _ refl inv eq refl) (sym (lookupᴰℚ-return _ G′)))
  ... | nothing = trans (E-bind (uniform-Vec k) _ G)
                 (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) pw)
                        (sym (E-bind (uniform-Vec k) _ G′)))
    where
    pw : (h : Dig) → E (return-ℚ (((x , h) ∷ t , m , f ∨ raise m h) , h)) G
                   ≡ E (return-ℚ (((x , h) ∷ t , er m) , h)) G′
    pw h = trans (lookupᴰℚ-return _ G)
          (trans (pt _ _ refl (inv-sample t m f x h inv) (lookup-here x h t) refl)
                 (sym (lookupᴰℚ-return _ G′)))

-- The real marginal: the coupling's first answer IS the real game's.
stepR : StepBisim C.realK respR (λ s sR → eraseR s ≡ sR)
stepR s@(t , m , f) .(eraseR s) refl (askQ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (askB s x) F)
 (trans (E-bind (fetch s x) _ (λ w → F (C.fR w)))
 (trans (fetch-bis digOf s x _ _ (inj₁ refl) prem)
        (sym (E-bind (fetchT (eraseR s) x) _ F′))))
  where
  prem : (u : St × Dig) (u′ : StR × Dig) → eraseR (proj₁ u) ≡ proj₁ u′ → Inv (proj₁ u)
       → lookupPt (tblOf (proj₁ u)) x ≡ just (proj₂ u) → proj₂ u ≡ proj₂ u′
       → E (return-ℚ (proj₁ u , (ansR (proj₂ u) , ansR (proj₂ u)))) (λ w → F (C.fR w))
         ≡ E (return-ℚ (proj₁ u′ , ansR (proj₂ u′))) F′
  prem u u′ er _ _ ea = trans (lookupᴰℚ-return _ _)
    (trans (pt _ _ er (cong ansR ea)) (sym (lookupᴰℚ-return _ F′)))
stepR (t , nothing , f) .(t , nothing) refl (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR _ F)
 (trans (lookupᴰℚ-return _ _)
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return _ F′))))
stepR (t , just m , f) .(t , digOf (just m)) refl (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR _ F)
 (trans (lookupᴰℚ-return _ _)
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return _ F′))))
stepR (t , nothing , f) .(t , nothing) refl (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR _ F)
 (trans (lookupᴰℚ-return _ _)
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return _ F′))))
stepR s@(t , just (c , e) , f) .(t , just c) refl (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR _ F)
 (trans (E-bind (fetch s (b ∷ᵛ r)) _ (λ w → F (C.fR w)))
 (trans (fetch-bis digOf s (b ∷ᵛ r) _ _ (inj₁ refl) prem)
        (sym (E-bind (fetchT (t , just c) (b ∷ᵛ r)) _ F′))))
  where
  prem : (u : St × Dig) (u′ : StR × Dig) → eraseR (proj₁ u) ≡ proj₁ u′ → Inv (proj₁ u)
       → lookupPt (tblOf (proj₁ u)) (b ∷ᵛ r) ≡ just (proj₂ u) → proj₂ u ≡ proj₂ u′
       → E (return-ℚ (proj₁ u , (realOpen c b (proj₂ u) , idealOpen c e b (proj₂ u))))
           (λ w → F (C.fR w))
         ≡ E (return-ℚ (proj₁ u′ , realOpen c b (proj₂ u′))) F′
  prem u u′ er _ _ ea = trans (lookupᴰℚ-return _ _)
    (trans (pt _ _ er (cong (realOpen c b) ea)) (sym (lookupᴰℚ-return _ F′)))

-- The ideal marginal: the coupling's second answer is the ideal game's, and at
-- a good post-state the copied first answer is the same thing (`agree-off`).
stepI : StepBisim C.idealK respI (λ s sI → (eraseI s ≡ sI) × Inv s)
stepI s@(t , m , f) .(eraseI s) (refl , inv) (askQ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (askB s x) F)
 (trans (E-bind (fetch s x) _ (λ w → F (C.fI w)))
 (trans (fetch-bis (λ z → z) s x _ _ inv prem)
        (sym (E-bind (fetchT (eraseI s) x) _ F′))))
  where
  prem : (u : St × Dig) (u′ : StI × Dig) → eraseI (proj₁ u) ≡ proj₁ u′ → Inv (proj₁ u)
       → lookupPt (tblOf (proj₁ u)) x ≡ just (proj₂ u) → proj₂ u ≡ proj₂ u′
       → E (return-ℚ (proj₁ u , (ansR (proj₂ u) , ansR (proj₂ u)))) (λ w → F (C.fI w))
         ≡ E (return-ℚ (proj₁ u′ , ansR (proj₂ u′))) F′
  prem u u′ er iv _ ea = trans (lookupᴰℚ-return _ _)
    (trans (cong (λ z → F (proj₁ u , z)) (cond-diag (bad (proj₁ u)) (ansR (proj₂ u))))
    (trans (pt _ _ (er , iv) (cong ansR ea)) (sym (lookupᴰℚ-return _ F′))))
stepI (t , nothing , f) .(t , nothing) (refl , inv) (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI _ F)
 (trans (lookupᴰℚ-return _ _)
 (trans (cong (λ z → F (t , just (c , extract c t) , f , z)) (cond-diag _ rcptR))
 (trans (pt _ _ (refl , inv-commit t f c) refl) (sym (lookupᴰℚ-return _ F′)))))
stepI (t , just m , f) .(t , just m) (refl , inv) (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI _ F)
 (trans (lookupᴰℚ-return _ _)
 (trans (cong (λ z → F (t , just m , f , z)) (cond-diag _ idleR))
 (trans (pt _ _ (refl , inv) refl) (sym (lookupᴰℚ-return _ F′)))))
stepI (t , nothing , f) .(t , nothing) (refl , inv) (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI _ F)
 (trans (lookupᴰℚ-return _ _)
 (trans (cong (λ z → F (t , nothing , f , z)) (cond-diag _ idleR))
 (trans (pt _ _ (refl , inv) refl) (sym (lookupᴰℚ-return _ F′)))))
stepI s@(t , just (c , e) , f) .(t , just (c , e)) (refl , inv) (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI _ F)
 (trans (E-bind (fetch s (b ∷ᵛ r)) _ (λ w → F (C.fI w)))
 (trans (fetch-bis (λ z → z) s (b ∷ᵛ r) _ _ inv prem)
        (sym (E-bind (fetchT (t , just (c , e)) (b ∷ᵛ r)) _ F′))))
  where
  collapse : (u : St × Dig) → Inv (proj₁ u)
           → lookupPt (tblOf (proj₁ u)) (b ∷ᵛ r) ≡ just (proj₂ u)
           → comOf (proj₁ u) ≡ just (c , e)
           → cond (bad (proj₁ u)) (idealOpen c e b (proj₂ u)) (realOpen c b (proj₂ u))
             ≡ idealOpen c e b (proj₂ u)
  collapse u iv hit cm = aux (bad (proj₁ u)) refl
    where
    aux : (x : Bool) → bad (proj₁ u) ≡ x
        → cond (bad (proj₁ u)) (idealOpen c e b (proj₂ u)) (realOpen c b (proj₂ u))
          ≡ idealOpen c e b (proj₂ u)
    aux true  bt = cong (λ z → cond z (idealOpen c e b (proj₂ u)) (realOpen c b (proj₂ u))) bt
    aux false bt = trans (cong (λ z → cond z (idealOpen c e b (proj₂ u))
                                             (realOpen c b (proj₂ u))) bt)
                         (reduce (proj₁ u) iv bt hit cm)

    reduce : (v : St) → Inv v → bad v ≡ false
           → lookupPt (tblOf v) (b ∷ᵛ r) ≡ just (proj₂ u) → comOf v ≡ just (c , e)
           → realOpen c b (proj₂ u) ≡ idealOpen c e b (proj₂ u)
    reduce (t′ , just (c′ , e′) , f′) iv′ bt hit′ refl =
      agree-off t′ c e f′ b (b ∷ᵛ r) (proj₂ u) iv′ bt hit′ refl

  prem : (u : St × Dig) (u′ : StI × Dig) → eraseI (proj₁ u) ≡ proj₁ u′ → Inv (proj₁ u)
       → lookupPt (tblOf (proj₁ u)) (b ∷ᵛ r) ≡ just (proj₂ u) → proj₂ u ≡ proj₂ u′
       → E (return-ℚ (proj₁ u , (realOpen c b (proj₂ u) , idealOpen c e b (proj₂ u))))
           (λ w → F (C.fI w))
         ≡ E (return-ℚ (proj₁ u′ , idealOpen c e b (proj₂ u′))) F′
  prem u u′ er iv hit ea = trans (lookupᴰℚ-return _ _)
    (trans (cong (λ z → F (proj₁ u , z)) (collapse u iv hit (comKept u er)))
    (trans (pt _ _ (er , iv) (cong (idealOpen c e b) ea)) (sym (lookupᴰℚ-return _ F′))))

------------------------------------------------------------------------
-- The two potentials

private
  -- The oracle's answer log either stays put or gains one fresh sample, and
  -- the hit flag rises by at most 2⁻ᵏ per call: `fetch` is where both happen.
  fetch-log : (s : St) (x : Pt) (F : List Dig → ℚ)
            → (E (fetch s x) (λ u → F (logOf (proj₁ u))) ≡ F (logOf s))
            ⊎ (E (fetch s x) (λ u → F (logOf (proj₁ u)))
               ≡ E (uniform-Vec k) (λ h → F (h ∷ logOf s)))
  fetch-log (t , m , f) x F with lookupPt t x
  ... | just d  = inj₁ (lookupᴰℚ-return _ _)
  ... | nothing = inj₂ (trans (E-bind (uniform-Vec k) _ _)
                              (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                                (λ h → lookupᴰℚ-return _ _)))

  0≤drift : (g : Bool) → bool→ℚ g ≤ℚ bool→ℚ g +ℚ inv-pow-2 k
  0≤drift g = ≤-trans (≤-reflexive (sym (+-identityʳ (bool→ℚ g))))
                      (+-monoʳ-≤ (bool→ℚ g) (0≤inv-pow-2 k))

  fetch-hit : (s : St) (x : Pt)
            → E (fetch s x) (λ u → bool→ℚ (hitOf (proj₁ u)))
              ≤ℚ bool→ℚ (hitOf s) +ℚ inv-pow-2 k
  fetch-hit (t , nothing , f) x with lookupPt t x
  ... | just d  = ≤-trans (≤-reflexive (lookupᴰℚ-return _ _)) (0≤drift f)
  ... | nothing = ≤-trans (≤-reflexive (trans (E-bind (uniform-Vec k) _ _)
                            (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                                     (λ h → lookupᴰℚ-return _ _))
                                   (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                                            (λ _ → cong bool→ℚ (∨-identityʳ f)))
                                          (E-const (uniform-Vec k) (bool→ℚ f))))))
                          (0≤drift f)
  fetch-hit (t , just (c , e) , f) x with lookupPt t x
  ... | just d  = ≤-trans (≤-reflexive (lookupᴰℚ-return _ _)) (0≤drift f)
  ... | nothing = ≤-trans (≤-reflexive (trans (E-bind (uniform-Vec k) _ _)
                            (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                              (λ h → lookupᴰℚ-return _ _))))
                          (guess-drift k f c)

  viaR : (s : St) (q : Q) (P : St × R → ℚ)
       → E (C.realK s q) P ≡ E (respB s q) (λ w → P (C.fR w))
  viaR s q P = lookupᴰℚ-Dmap C.fR (respB s q) P

keep-or-sample : KeepOrSample k C.realK logOf
keep-or-sample s (askQ x) F =
  shift (trans (viaR s (askQ x) _)
                (trans (E-bind (fetch s x) _ _)
                       (lookupᴰℚ-cong-P (entries (fetch s x))
                         (λ u → lookupᴰℚ-return _ _))))
        (fetch-log s x F)
  where
  shift : {a b : ℚ} → a ≡ b
        → (b ≡ F (logOf s)) ⊎ (b ≡ E (uniform-Vec k) (λ h → F (h ∷ logOf s)))
        → (a ≡ F (logOf s)) ⊎ (a ≡ E (uniform-Vec k) (λ h → F (h ∷ logOf s)))
  shift e (inj₁ z) = inj₁ (trans e z)
  shift e (inj₂ z) = inj₂ (trans e z)
keep-or-sample (t , nothing , f) (comQ c) F =
  inj₁ (trans (viaR _ (comQ c) _) (lookupᴰℚ-return _ _))
keep-or-sample (t , just m , f) (comQ c) F =
  inj₁ (trans (viaR _ (comQ c) _) (lookupᴰℚ-return _ _))
keep-or-sample (t , nothing , f) (opnQ b r) F =
  inj₁ (trans (viaR _ (opnQ b r) _) (lookupᴰℚ-return _ _))
keep-or-sample s@(t , just (c , e) , f) (opnQ b r) F =
  shift (trans (viaR s (opnQ b r) _)
                (trans (E-bind (fetch s (b ∷ᵛ r)) _ _)
                       (lookupᴰℚ-cong-P (entries (fetch s (b ∷ᵛ r)))
                         (λ u → lookupᴰℚ-return _ _))))
        (fetch-log s (b ∷ᵛ r) F)
  where
  shift : {a b : ℚ} → a ≡ b
        → (b ≡ F (logOf s)) ⊎ (b ≡ E (uniform-Vec k) (λ h → F (h ∷ logOf s)))
        → (a ≡ F (logOf s)) ⊎ (a ≡ E (uniform-Vec k) (λ h → F (h ∷ logOf s)))
  shift e (inj₁ z) = inj₁ (trans e z)
  shift e (inj₂ z) = inj₂ (trans e z)

rare-raise : RareRaise C.realK hitOf (inv-pow-2 k)
rare-raise s (askQ x) =
  ≤-trans (≤-reflexive (trans (viaR s (askQ x) _)
                        (trans (E-bind (fetch s x) _ _)
                               (lookupᴰℚ-cong-P (entries (fetch s x))
                                 (λ u → lookupᴰℚ-return _ _)))))
          (fetch-hit s x)
rare-raise (t , nothing , f) (comQ c) =
  ≤-trans (≤-reflexive (trans (viaR _ (comQ c) _) (lookupᴰℚ-return _ _))) (0≤drift f)
rare-raise (t , just m , f) (comQ c) =
  ≤-trans (≤-reflexive (trans (viaR _ (comQ c) _) (lookupᴰℚ-return _ _))) (0≤drift f)
rare-raise (t , nothing , f) (opnQ b r) =
  ≤-trans (≤-reflexive (trans (viaR _ (opnQ b r) _) (lookupᴰℚ-return _ _))) (0≤drift f)
rare-raise s@(t , just (c , e) , f) (opnQ b r) =
  ≤-trans (≤-reflexive (trans (viaR s (opnQ b r) _)
                        (trans (E-bind (fetch s (b ∷ᵛ r)) _ _)
                               (lookupᴰℚ-cong-P (entries (fetch s (b ∷ᵛ r)))
                                 (λ u → lookupᴰℚ-return _ _)))))
          (fetch-hit s (b ∷ᵛ r))

------------------------------------------------------------------------
-- The bound

ε : ℕ → ℚ
ε m = fromℕ (m * m + m) *ℚ inv-pow-2 k +ℚ fromℕ m *ℚ inv-pow-2 k

cert : SuperCert C.realK bad s₀ ε
cert = ∨-cert (collision-cert k C.realK logOf s₀ refl keep-or-sample)
              (rare-cert C.realK hitOf s₀ (inv-pow-2 k) (0≤inv-pow-2 k) refl rare-raise)

-- For every adversary of at most `m` oracle-or-protocol queries, the real
-- commitment game and the ideal one with the extracting simulator differ by at
-- most `(m² + m)·2⁻ᵏ + m·2⁻ᵏ`.
extraction-bound : (m : ℕ) (d : Strat Q R) → asks≤ m d
                 → ∣ Pr₁ (runWith respI sI₀ d) -ℚ Pr₁ (runWith respR sR₀ d) ∣ℚ ≤ℚ ε m
extraction-bound = hop-bound bad respB respR respI s₀ sR₀ sI₀
  (λ d → runWith-bisim C.realK respR _ stepR d s₀ sR₀ refl)
  (λ d → runWith-bisim C.idealK respI _ stepI d s₀ sI₀ (refl , inv₀))
  cert
