{-# OPTIONS --safe --without-K #-}

-- The closed extraction game and its ε.
--
-- `respR` is the real protocol against a lazily sampled oracle, `respI` the
-- ideal functionality behind the extracting simulator; no adaptive adversary
-- of `m` queries tells them apart by more than `(m² + m)·2⁻ᵏ + m·2⁻ᵏ`.  The
-- coupling `respB` runs one oracle table and emits both answers.  They differ
-- only at an opening the receiver accepts and the simulator cannot deliver,
-- which `agree-off` puts under two flags: a repeat in the oracle's answer log
-- (`Potential.collision-cert`) or a fresh sample landing on the outstanding
-- digest (`Potential.rare-cert`).  The digest is drawn by the oracle at the
-- query, so `docs/ro-game-hop.md`'s fixed-secret caveat does not apply.

open import Class.DecEq

open import Data.Bool.Base
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.Empty
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using (+-identityʳ; +-monoʳ-≤; ≤-reflexive; ≤-trans)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; map)
open import Data.Unit.Base
open import Data.Vec.Base using (head; tail) renaming (_∷_ to _∷ᵛ_)
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Partial using (cond; cond-diag)
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform

module CategoricalCrypto.Examples.ROCommitment.Game (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k
open import CategoricalCrypto.Examples.ROCommitment.Oracle k
open import ProbabilisticLogic.Distribution.Uniform.Duplicate k

------------------------------------------------------------------------
-- The alphabet and the three state spaces

data Q : Set where
  askQ : Pt → Q
  comQ : Dig → Q
  opnQ : Bool → Dig → Q

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
StR = Tbl × Maybe Dig
StI = Tbl × Com

tblOf : St → Tbl
tblOf (t , _ , _) = t

hitOf : St → Bool
hitOf (_ , _ , f) = f

comOf : St → Com
comOf (_ , m , _) = m

logOf : St → List Dig
logOf (t , _ , _) = answers t

digOf : Com → Maybe Dig
digOf nothing        = nothing
digOf (just (c , _)) = just c

------------------------------------------------------------------------
-- The coupling's oracle

-- `Oracle.fetchT` that also raises the hit flag when a fresh sample lands on
-- the outstanding commitment digest.
raise : Com → Dig → Bool
raise nothing        _ = false
raise (just (c , _)) h = ⌊ h ≟ c ⌋

fetch : St → Pt → Dist-ℚ (St × Dig)
fetch (t , m , f) x = case lookupPt t x of λ where
  (just d) → return-ℚ ((t , m , f) , d)
  nothing → uniform-Vec k >>=ᴹ λ h → return-ℚ (((x , h) ∷ t , m , f ∨ raise m h) , h)

------------------------------------------------------------------------
-- The two games and the coupling

realOpen : Dig → Bool → Dig → R
realOpen c b h = cond ⌊ h ≟ c ⌋ (outR b) failR

idealOpen : Dig → Bool → Bool → Dig → R
idealOpen c e b h = cond ⌊ h ≟ c ⌋ (cond ⌊ b ≟ e ⌋ (outR e) failR) failR

askX : {M : Set} → Tbl × M → Pt → Dist-ℚ ((Tbl × M) × R)
askX (t , m) x = fetchT (_, m) t x >>=ᴹ λ u → return-ℚ (proj₁ u , ansR (proj₂ u))

comR : StR → Dig → Dist-ℚ (StR × R)
comR (t , nothing) c = return-ℚ ((t , just c) , rcptR)
comR (t , just c)  _ = return-ℚ ((t , just c) , idleR)

opnR : StR → Bool → Dig → Dist-ℚ (StR × R)
opnR (t , nothing) _ _ = return-ℚ ((t , nothing) , idleR)
opnR (t , just c)  b r = fetchT (_, just c) t (b ∷ᵛ r) >>=ᴹ λ u →
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
opnI (t , just (c , e)) b r = fetchT (_, just (c , e)) t (b ∷ᵛ r) >>=ᴹ λ u →
  return-ℚ (proj₁ u , idealOpen c e b (proj₂ u))

respI : StI → Q → Dist-ℚ (StI × R)
respI s (askQ x)   = askX s x
respI s (comQ c)   = comI s c
respI s (opnQ b r) = opnI s b r

-- The two coupled answers to a sampled point.
ansB : St × Dig → St × (R × R)
ansB u = proj₁ u , (ansR (proj₂ u) , ansR (proj₂ u))

opnAns : Dig → Bool → Bool → St × Dig → St × (R × R)
opnAns c e b u = proj₁ u , (realOpen c b (proj₂ u) , idealOpen c e b (proj₂ u))

askB : St → Pt → Dist-ℚ (St × (R × R))
askB s x = Dmap ansB (fetch s x)

comB : St → Dig → Dist-ℚ (St × (R × R))
comB (t , nothing , f) c = return-ℚ ((t , just (c , extract c t) , f) , (rcptR , rcptR))
comB (t , just m , f)  _ = return-ℚ ((t , just m , f) , (idleR , idleR))

opnB : St → Bool → Dig → Dist-ℚ (St × (R × R))
opnB (t , nothing , f)      _ _ = return-ℚ ((t , nothing , f) , (idleR , idleR))
opnB (t , just (c , e) , f) b r = Dmap (opnAns c e b) (fetch (t , just (c , e) , f) (b ∷ᵛ r))

respB : St → Q → Dist-ℚ (St × (R × R))
respB s (askQ x)   = askB s x
respB s (comQ c)   = comB s c
respB s (opnQ b r) = opnB s b r

bad : St → Bool
bad s = dup (logOf s) ∨ hitOf s

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
  bad-grow : (L : List Dig) (d : Dig) (g g′ : Bool) → (g ≡ true → g′ ≡ true)
           → (dup L ∨ g) ≡ true → (dup (d ∷ L) ∨ g′) ≡ true
  bad-grow L d g g′ up e = aux (dup L) refl
    where
    aux : (x : Bool) → dup L ≡ x → (dup (d ∷ L) ∨ g′) ≡ true
    aux true  dl = cong (_∨ g′) (trans (cong (memb d L ∨_) dl) (∨-zeroʳ (memb d L)))
    aux false dl = trans (cong (dup (d ∷ L) ∨_) (up (trans (sym (cong (_∨ g) dl)) e)))
                         (∨-zeroʳ (dup (d ∷ L)))

inv-sample : (t : Tbl) (m : Com) (f : Bool) (x : Pt) (h : Dig)
           → Inv (t , m , f) → Inv ((x , h) ∷ t , m , f ∨ raise m h)
inv-sample t nothing        f x h _   = inj₂ tt
inv-sample t (just (c , e)) f x h inv with h ≟ c
... | yes _  = inj₁ (trans (cong (dup (h ∷ answers t) ∨_) (∨-zeroʳ f))
                           (∨-zeroʳ (dup (h ∷ answers t))))
... | no h≢c = case inv of λ where
  (inj₁ bt) → inj₁ (bad-grow (answers t) h f (f ∨ false) (cong (_∨ false)) bt)
  (inj₂ gd) → inj₂ (pins-∷ c e x h t h≢c gd)

inv-commit : (t : Tbl) (f : Bool) (c : Dig) → Inv (t , just (c , extract c t) , f)
inv-commit t f c = aux (dup (answers t)) refl
  where
  aux : (x : Bool) → dup (answers t) ≡ x → Inv (t , just (c , extract c t) , f)
  aux true  dl = inj₁ (cong (_∨ f) dl)
  aux false dl = inj₂ (pins-extract c t dl)

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

  -- The `lookupPt … ≡ just (proj₂ u)` premise is what `agree-off` needs, and
  -- what a bare `with` would discard.
  fetch-bis : (s : St) (x : Pt) (G : St × Dig → ℚ) (G′ : (Tbl × M) × Dig → ℚ)
            → Inv s
            → ((u : St × Dig) (u′ : (Tbl × M) × Dig)
               → ec (proj₁ u) ≡ proj₁ u′ → Inv (proj₁ u) → comOf (proj₁ u) ≡ comOf s
               → lookupPt (tblOf (proj₁ u)) x ≡ just (proj₂ u)
               → proj₂ u ≡ proj₂ u′ → G u ≡ G′ u′)
            → E (fetch s x) G ≡ E (fetchT (_, er (comOf s)) (tblOf s) x) G′
  fetch-bis (t , m , f) x G G′ inv pt with lookupPt t x in eq
  ... | just d  = E-return-cong _ _ G G′ (pt _ _ refl inv refl eq refl)
  ... | nothing = trans
    (lookupᴰℚ-Dmap (λ h → ((x , h) ∷ t , m , f ∨ raise m h) , h) (uniform-Vec k) G)
   (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) λ h →
            pt _ _ refl (inv-sample t m f x h inv) refl (lookup-here x h t) refl)
          (sym (lookupᴰℚ-Dmap (λ h → ((x , h) ∷ t , er m) , h) (uniform-Vec k) G′)))

eraseR : St → StR
eraseR = ec digOf

eraseI : St → StI
eraseI = ec id

-- Both relations carry the invariant, because `fetch-bis` needs it to re-establish
-- it — the real side never reads it.
_≋R_ : St → StR → Set
s ≋R sR = (eraseR s ≡ sR) × Inv s

_≋I_ : St → StI → Set
s ≋I sI = (eraseI s ≡ sI) × Inv s

stepR : StepBisim C.realK respR _≋R_
stepR s@(t , m , f) _ (refl , inv) (askQ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (askB s x) F)
 (trans (lookupᴰℚ-Dmap ansB (fetch s x) (λ w → F (C.fR w)))
 (trans (fetch-bis digOf s x _ _ inv λ _ _ er iv _ _ ea → pt _ _ (er , iv) (cong ansR ea))
        (sym (lookupᴰℚ-Dmap (λ u → proj₁ u , ansR (proj₂ u)) (fetchT (_, digOf m) t x) F′))))
stepR (t , nothing , f) _ (refl , inv) (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (comB (t , nothing , f) c) F)
        (E-return-cong ((t , just (c , extract c t) , f) , (rcptR , rcptR))
                       ((t , just c) , rcptR) (λ w → F (C.fR w)) F′
                       (pt _ _ (refl , inv-commit t f c) refl))
stepR (t , just (c′ , e′) , f) _ (refl , inv) (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (comB (t , just (c′ , e′) , f) c) F)
        (E-return-cong ((t , just (c′ , e′) , f) , (idleR , idleR))
                       ((t , just c′) , idleR) (λ w → F (C.fR w)) F′ (pt _ _ (refl , inv) refl))
stepR (t , nothing , f) _ (refl , inv) (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (opnB (t , nothing , f) b r) F)
        (E-return-cong ((t , nothing , f) , (idleR , idleR))
                       ((t , nothing) , idleR) (λ w → F (C.fR w)) F′ (pt _ _ (refl , inv) refl))
stepR s@(t , just (c , e) , f) _ (refl , inv) (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (opnB s b r) F)
 (trans (lookupᴰℚ-Dmap (opnAns c e b) (fetch s (b ∷ᵛ r)) (λ w → F (C.fR w)))
 (trans (fetch-bis digOf s (b ∷ᵛ r) _ _ inv λ _ _ er iv _ _ ea →
          pt _ _ (er , iv) (cong (realOpen c b) ea))
        (sym (lookupᴰℚ-Dmap (λ u → proj₁ u , realOpen c b (proj₂ u))
               (fetchT (_, just c) t (b ∷ᵛ r)) F′))))

stepI : StepBisim C.idealK respI _≋I_
stepI s@(t , m , f) _ (refl , inv) (askQ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (askB s x) F)
 (trans (lookupᴰℚ-Dmap ansB (fetch s x) (λ w → F (C.fI w)))
 (trans (fetch-bis id s x _ _ inv λ u _ er iv _ _ ea →
          trans (cong (λ z → F (proj₁ u , z)) (cond-diag (bad (proj₁ u)) (ansR (proj₂ u))))
                (pt _ _ (er , iv) (cong ansR ea)))
        (sym (lookupᴰℚ-Dmap (λ u → proj₁ u , ansR (proj₂ u)) (fetchT (_, m) t x) F′))))
stepI (t , nothing , f) _ (refl , inv) (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (comB (t , nothing , f) c) F)
        (E-return-cong ((t , just (c , extract c t) , f) , (rcptR , rcptR))
                       ((t , just (c , extract c t)) , rcptR) (λ w → F (C.fI w)) F′
          (trans (cong (λ z → F ((t , just (c , extract c t) , f) , z))
                       (cond-diag (bad (t , just (c , extract c t) , f)) rcptR))
                 (pt _ _ (refl , inv-commit t f c) refl)))
stepI (t , just (c′ , e′) , f) _ (refl , inv) (comQ c) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (comB (t , just (c′ , e′) , f) c) F)
        (E-return-cong ((t , just (c′ , e′) , f) , (idleR , idleR))
                       ((t , just (c′ , e′)) , idleR) (λ w → F (C.fI w)) F′
          (trans (cong (λ z → F ((t , just (c′ , e′) , f) , z))
                       (cond-diag (bad (t , just (c′ , e′) , f)) idleR))
                 (pt _ _ (refl , inv) refl)))
stepI (t , nothing , f) _ (refl , inv) (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (opnB (t , nothing , f) b r) F)
        (E-return-cong ((t , nothing , f) , (idleR , idleR))
                       ((t , nothing) , idleR) (λ w → F (C.fI w)) F′
          (trans (cong (λ z → F ((t , nothing , f) , z)) (cond-diag (bad (t , nothing , f)) idleR))
                 (pt _ _ (refl , inv) refl)))
stepI s@(t , just (c , e) , f) _ (refl , inv) (opnQ b r) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (opnB s b r) F)
 (trans (lookupᴰℚ-Dmap (opnAns c e b) (fetch s (b ∷ᵛ r)) (λ w → F (C.fI w)))
 (trans (fetch-bis id s (b ∷ᵛ r) _ _ inv λ u _ er iv cm hit ea →
          trans (cong (λ z → F (proj₁ u , z)) (collapse (proj₁ u) (proj₂ u) iv cm hit))
                (pt _ _ (er , iv) (cong (idealOpen c e b) ea)))
        (sym (lookupᴰℚ-Dmap (λ u → proj₁ u , idealOpen c e b (proj₂ u))
               (fetchT (_, just (c , e)) t (b ∷ᵛ r)) F′))))
  where
  -- Off the bad event the receiver's verdict is the functionality's, so the
  -- coupling's copy of the real answer is the ideal one after all.
  collapse : (v : St) (d : Dig) → Inv v → comOf v ≡ just (c , e)
           → lookupPt (tblOf v) (b ∷ᵛ r) ≡ just d
           → cond (bad v) (idealOpen c e b d) (realOpen c b d) ≡ idealOpen c e b d
  collapse v d iv cm hit = aux (bad v) refl
    where
    reduce : (w : St) → Inv w → comOf w ≡ just (c , e) → bad w ≡ false
           → lookupPt (tblOf w) (b ∷ᵛ r) ≡ just d
           → realOpen c b d ≡ idealOpen c e b d
    reduce (t′ , _ , f′) iv′ refl bt hit′ =
      agree-off t′ c e f′ b (b ∷ᵛ r) d iv′ bt hit′ refl

    aux : (z : Bool) → bad v ≡ z
        → cond (bad v) (idealOpen c e b d) (realOpen c b d) ≡ idealOpen c e b d
    aux true  bt = cong (λ z → cond z (idealOpen c e b d) (realOpen c b d)) bt
    aux false bt = trans (cong (λ z → cond z (idealOpen c e b d) (realOpen c b d)) bt)
                         (reduce v iv cm bt hit)

------------------------------------------------------------------------
-- The two potentials

private
  viaR : (s : St) (q : Q) (P : St × R → ℚ)
       → E (C.realK s q) P ≡ E (respB s q) (λ w → P (C.fR w))
  viaR s q P = lookupᴰℚ-Dmap C.fR (respB s q) P

  askQ-red : (s : St) (x : Pt) (P : St × R → ℚ)
           → E (respB s (askQ x)) (λ w → P (C.fR w))
             ≡ E (fetch s x) (λ u → P (proj₁ u , ansR (proj₂ u)))
  askQ-red s x P = lookupᴰℚ-Dmap ansB (fetch s x) (λ w → P (C.fR w))

  opnQ-red : (t : Tbl) (c : Dig) (e f b : Bool) (r : Dig) (P : St × R → ℚ)
           → E (respB (t , just (c , e) , f) (opnQ b r)) (λ w → P (C.fR w))
             ≡ E (fetch (t , just (c , e) , f) (b ∷ᵛ r))
                 (λ u → P (proj₁ u , realOpen c b (proj₂ u)))
  opnQ-red t c e f b r P =
    lookupᴰℚ-Dmap (opnAns c e b) (fetch (t , just (c , e) , f) (b ∷ᵛ r)) (λ w → P (C.fR w))

  idle-red : (s s′ : St) (a : R × R) (q : Q) (P : St × R → ℚ)
           → respB s q ≡ return-ℚ (s′ , a)
           → E (C.realK s q) P ≡ P (s′ , proj₁ a)
  idle-red s s′ a q P eq = trans (viaR s q P)
    (trans (cong (λ μ → E μ (λ w → P (C.fR w))) eq)
           (lookupᴰℚ-return (s′ , a) (λ w → P (C.fR w))))

  logP : {A : Set} → (List Dig → ℚ) → St × A → ℚ
  logP F sr = F (logOf (proj₁ sr))

  hitP : {A : Set} → St × A → ℚ
  hitP sr = bool→ℚ (hitOf (proj₁ sr))

  fetch-log : (s : St) (x : Pt) (F : List Dig → ℚ)
            → (E (fetch s x) (logP F) ≡ F (logOf s))
            ⊎ (E (fetch s x) (logP F) ≡ E (uniform-Vec k) (λ h → F (h ∷ logOf s)))
  fetch-log (t , m , f) x F with lookupPt t x
  ... | just d  = inj₁ (lookupᴰℚ-return ((t , m , f) , d) (logP F))
  ... | nothing =
    inj₂ (lookupᴰℚ-Dmap (λ h → ((x , h) ∷ t , m , f ∨ raise m h) , h) (uniform-Vec k) (logP F))

  fetch-hit : (s : St) (x : Pt) → E (fetch s x) hitP ≤ℚ bool→ℚ (hitOf s) +ℚ inv-pow-2 k
  fetch-hit (t , m , f) x with lookupPt t x
  ... | just d  = ≤-trans (≤-reflexive (lookupᴰℚ-return ((t , m , f) , d) hitP)) (0≤drift k f)
  ... | nothing = ≤-trans
    (≤-reflexive (lookupᴰℚ-Dmap (λ h → ((x , h) ∷ t , m , f ∨ raise m h) , h) (uniform-Vec k) hitP))
    (drift m)
    where
    drift : (m : Com) → E (uniform-Vec k) (λ h → bool→ℚ (f ∨ raise m h)) ≤ℚ bool→ℚ f +ℚ inv-pow-2 k
    drift nothing        = drift-∧ k f false (tail x)
    drift (just (c , _)) = guess-drift k f c

keep-or-sample : KeepOrSample k C.realK logOf
keep-or-sample s (askQ x) F = map (trans red) (trans red) (fetch-log s x F)
  where
  red : E (C.realK s (askQ x)) (logP F) ≡ E (fetch s x) (logP F)
  red = trans (viaR s (askQ x) (logP F)) (askQ-red s x (logP F))
keep-or-sample (t , nothing , f) (comQ c) F = inj₁ (idle-red (t , nothing , f)
  (t , just (c , extract c t) , f) (rcptR , rcptR) (comQ c)
  (logP F) refl)
keep-or-sample (t , just m , f) (comQ c) F = inj₁ (idle-red (t , just m , f)
  (t , just m , f) (idleR , idleR) (comQ c) (logP F) refl)
keep-or-sample (t , nothing , f) (opnQ b r) F = inj₁ (idle-red (t , nothing , f)
  (t , nothing , f) (idleR , idleR) (opnQ b r) (logP F) refl)
keep-or-sample s@(t , just (c , e) , f) (opnQ b r) F =
  map (trans red) (trans red) (fetch-log s (b ∷ᵛ r) F)
  where
  red : E (C.realK s (opnQ b r)) (logP F) ≡ E (fetch s (b ∷ᵛ r)) (logP F)
  red = trans (viaR s (opnQ b r) (logP F)) (opnQ-red t c e f b r (logP F))

rare-raise : RareRaise C.realK hitOf (inv-pow-2 k)
rare-raise s (askQ x) = ≤-trans
  (≤-reflexive (trans (viaR s (askQ x) hitP) (askQ-red s x hitP)))
  (fetch-hit s x)
rare-raise (t , nothing , f) (comQ c) = ≤-trans
  (≤-reflexive (idle-red (t , nothing , f) (t , just (c , extract c t) , f)
    (rcptR , rcptR) (comQ c) hitP refl))
  (0≤drift k f)
rare-raise (t , just m , f) (comQ c) = ≤-trans
  (≤-reflexive (idle-red (t , just m , f) (t , just m , f) (idleR , idleR)
    (comQ c) hitP refl))
  (0≤drift k f)
rare-raise (t , nothing , f) (opnQ b r) = ≤-trans
  (≤-reflexive (idle-red (t , nothing , f) (t , nothing , f) (idleR , idleR)
    (opnQ b r) hitP refl))
  (0≤drift k f)
rare-raise s@(t , just (c , e) , f) (opnQ b r) = ≤-trans
  (≤-reflexive (trans (viaR s (opnQ b r) hitP) (opnQ-red t c e f b r hitP)))
  (fetch-hit s (b ∷ᵛ r))

------------------------------------------------------------------------
-- The bound

ε : ℕ → ℚ
ε m = fromℕ (m * m + m) *ℚ inv-pow-2 k +ℚ fromℕ m *ℚ inv-pow-2 k

cert : SuperCert C.realK bad s₀ ε
cert = ∨-cert (collision-cert k C.realK logOf s₀ refl keep-or-sample)
              (rare-cert C.realK hitOf s₀ (inv-pow-2 k) (0≤inv-pow-2 k) refl rare-raise)

extraction-bound : (m : ℕ) (d : Strat Q R) → asks≤ m d
                 → ∣ Pr₁ (runWith respI sI₀ d) -ℚ Pr₁ (runWith respR sR₀ d) ∣ℚ
                   ≤ℚ ε m
extraction-bound = hop-bound bad respB respR respI s₀ sR₀ sI₀
  (λ d → runWith-bisim C.realK respR _≋R_ stepR d s₀ sR₀ (refl , inv₀))
  (λ d → runWith-bisim C.idealK respI _≋I_ stepI d s₀ sI₀ (refl , inv₀))
  cert
