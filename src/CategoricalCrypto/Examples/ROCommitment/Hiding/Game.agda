{-# OPTIONS --safe --without-K #-}

-- The closed hiding game, and its ε.
--
-- Three reactive kernels over one alphabet: `respRʰ`, the real protocol, which
-- draws the opening randomness AT THE COMMITMENT and keeps it; `respLʰ`, the
-- same protocol with that draw deferred to the step that could read it; and
-- `respIʰ`, `F_com` with the programming simulator in front of it.
--
-- The hop proved here is `respLʰ` against `respIʰ`.  The two kernels differ at
-- exactly one place — an oracle query, while a commitment is outstanding, that
-- hits the deferred opening point — so the coupling is one clause wide, the
-- flag is raised by a FRESH uniform draw at each query and `Potential.rare-cert`
-- with `guess-drift` bounds it by `m·2⁻ᵏ`.
--
-- `respRʰ` is defined beside them but NOT identified with `respLʰ`: that is the
-- residual `docs/fcom-hiding.md` states and prices.  `hiding-bound-defer` is
-- the theorem that turns it into the full statement, and `defer-commit` — an
-- instance of `GamePlaying.Defer.runWith-avg` — is the half of the residual
-- that IS exact, the real game's own draw moved to the start of the run.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true; _∧_; _∨_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  (+-identityʳ; +-mono-≤; +-monoʳ-≤; ∣p+q∣≤∣p∣+∣q∣; ≤-reflexive; ≤-trans)
open import Data.Rational.Properties.Ext using (telescope)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base using (head; tail) renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Defer
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.GamePlaying.Potential
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform using
  (0≤inv-pow-2; bool→ℚ; fromℕ; inv-pow-2; uniform-Vec)

module CategoricalCrypto.Examples.ROCommitment.Hiding.Game (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k using (Dig; Pt; Tbl)
open import CategoricalCrypto.Examples.ROCommitment.Oracle k

------------------------------------------------------------------------
-- The alphabet and the three state spaces

-- What the corrupted receiver and the environment between them can do: query
-- the oracle, have the honest committer commit to a bit, have it open.
data Qʰ : Set where
  askQʰ : Pt → Qʰ
  comQʰ : Bool → Qʰ
  opnQʰ : Qʰ

data Rʰ : Set where
  ansRʰ  : Dig → Rʰ
  comRʰ  : Dig → Rʰ
  opnRʰ  : Bool → Dig → Rʰ
  idleRʰ : Rʰ

-- The commitment on the table: the digest published, the bit, and whether the
-- opening has gone out.
Comʰ : Set
Comʰ = Maybe (Dig × Bool × Bool)

-- …and what the real game keeps instead, the opening randomness included.
ComRʰ : Set
ComRʰ = Maybe (Dig × Bool × Dig × Bool)

St StLʰ StRʰ : Set
St   = Tbl × Comʰ × Bool         -- the coupling: + the hit flag
StLʰ = Tbl × Comʰ                -- the deferred and the ideal games
StRʰ = Maybe Dig × Tbl × ComRʰ   -- the real game: + the secret, planted or not

eraseʰ : St → StLʰ
eraseʰ (t , m , _) = t , m

hitOf : St → Bool
hitOf (_ , _ , f) = f

------------------------------------------------------------------------
-- The point the deferred game watches for

-- Does this query name the commitment's own point, for THIS draw of the
-- opening randomness?  Only while a commitment is outstanding: before one
-- there is no point to hit, and after the opening the point is in the table,
-- where both games read it.
hitAt : Comʰ → Pt → Dig → Bool
hitAt (just (_ , b , false)) x ρ = ⌊ head x ≟ b ⌋ ∧ ⌊ ρ ≟ tail x ⌋
hitAt (just (_ , _ , true))  _ _ = false
hitAt nothing                _ _ = false

-- …and what the real committer's own table entry answers there.
pinAt : Comʰ → Dig → Dig
pinAt (just (c , _ , _)) _ = c
pinAt nothing            d = d

-- The outcome of one step in each game, NAMED.  `_>>=ᴹ_` is a defined
-- function, so no `E-bind` rewrite below can recover a continuation from a
-- kernel by unification; every one of them has to be pointed at.
outAskB : Comʰ → Bool → Pt → Tbl × Dig → Dig → St × (Rʰ × Rʰ)
outAskB m f x u ρ = ( (proj₁ u , m , f ∨ hitAt m x ρ)
                    , ( ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u))
                      , ansRʰ (proj₂ u) ) )

outAskL : Comʰ → Pt → Tbl × Dig → Dig → StLʰ × Rʰ
outAskL m x u ρ =
  (proj₁ u , m) , ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u))

outAskI : Comʰ → Tbl × Dig → StLʰ × Rʰ
outAskI m u = (proj₁ u , m) , ansRʰ (proj₂ u)

outComB : Tbl → Bool → Bool → Dig → St × (Rʰ × Rʰ)
outComB t b f c = (t , just (c , b , false) , f) , (comRʰ c , comRʰ c)

outComL : Tbl → Bool → Dig → StLʰ × Rʰ
outComL t b c = (t , just (c , b , false)) , comRʰ c

outOpnB : Tbl → Dig → Bool → Bool → Dig → St × (Rʰ × Rʰ)
outOpnB t c b f r =
  ((b ∷ᵛ r , c) ∷ t , just (c , b , true) , f) , (opnRʰ b r , opnRʰ b r)

outOpnL : Tbl → Dig → Bool → Dig → StLʰ × Rʰ
outOpnL t c b r = ((b ∷ᵛ r , c) ∷ t , just (c , b , true)) , opnRʰ b r

outAskR : Maybe Dig → ComRʰ → Tbl × Dig → StRʰ × Rʰ
outAskR mr z u = (mr , proj₁ u , z) , ansRʰ (proj₂ u)

outComR : Dig → Bool → Tbl × Dig → StRʰ × Rʰ
outComR r b u = (just r , proj₁ u , just (proj₂ u , b , r , false)) , comRʰ (proj₂ u)

------------------------------------------------------------------------
-- The real game: the opening randomness drawn at the commitment

-- The first component is the secret, PLANTED or not yet drawn.  `comR` is the
-- only step that looks at it, and it draws it when it is not there; that is
-- what `defer-commit` below is about.
askR : StRʰ → Pt → Dist-ℚ (StRʰ × Rʰ)
askR (mr , t , z) x = fetchT id t x >>=ᴹ λ u → return-ℚ (outAskR mr z u)

comAt : Dig → Tbl → Bool → Dist-ℚ (StRʰ × Rʰ)
comAt r t b = fetchT id t (b ∷ᵛ r) >>=ᴹ λ u → return-ℚ (outComR r b u)

comR : StRʰ → Bool → Dist-ℚ (StRʰ × Rʰ)
comR (just r  , t , nothing) b = comAt r t b
comR (nothing , t , nothing) b = uniform-Vec k >>=ᴹ λ r → comAt r t b
comR (mr , t , just z)       _ = return-ℚ ((mr , t , just z) , idleRʰ)

opnR : StRʰ → Dist-ℚ (StRʰ × Rʰ)
opnR (mr , t , just (c , b , r , false)) =
  return-ℚ ((mr , t , just (c , b , r , true)) , opnRʰ b r)
opnR (mr , t , just (c , b , r , true))  =
  return-ℚ ((mr , t , just (c , b , r , true)) , idleRʰ)
opnR (mr , t , nothing)                  = return-ℚ ((mr , t , nothing) , idleRʰ)

respRʰ : StRʰ → Qʰ → Dist-ℚ (StRʰ × Rʰ)
respRʰ s (askQʰ x) = askR s x
respRʰ s (comQʰ b) = comR s b
respRʰ s opnQʰ     = opnR s

------------------------------------------------------------------------
-- The deferred game and the ideal game

-- The commitment and the opening are the SAME step in both.  At the
-- commitment a fresh uniform digest goes out — in the real world it is
-- `H(b ∷ r)` at a point nothing has queried, in the ideal world the
-- simulator's `c*`.  At the opening `r` is drawn and its point is PROGRAMMED
-- to that digest, which is where the real world's table entry already was.
comL : StLʰ → Bool → Dist-ℚ (StLʰ × Rʰ)
comL (t , nothing) b = uniform-Vec k >>=ᴹ λ c → return-ℚ (outComL t b c)
comL (t , just m)  _ = return-ℚ ((t , just m) , idleRʰ)

opnL : StLʰ → Dist-ℚ (StLʰ × Rʰ)
opnL (t , just (c , b , false)) =
  uniform-Vec k >>=ᴹ λ r → return-ℚ (outOpnL t c b r)
opnL (t , just (c , b , true))  = return-ℚ ((t , just (c , b , true)) , idleRʰ)
opnL (t , nothing)              = return-ℚ ((t , nothing) , idleRʰ)

-- The one place the two games part: the deferred game draws the opening
-- randomness afresh at every query and answers the published digest on a hit.
askL : StLʰ → Pt → Dist-ℚ (StLʰ × Rʰ)
askL (t , m) x =
  fetchT id t x >>=ᴹ λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskL m x u ρ)

askI : StLʰ → Pt → Dist-ℚ (StLʰ × Rʰ)
askI (t , m) x = fetchT id t x >>=ᴹ λ u → return-ℚ (outAskI m u)

respLʰ respIʰ : StLʰ → Qʰ → Dist-ℚ (StLʰ × Rʰ)
respLʰ s (askQʰ x) = askL s x
respLʰ s (comQʰ b) = comL s b
respLʰ s opnQʰ     = opnL s
respIʰ s (askQʰ x) = askI s x
respIʰ s (comQʰ b) = comL s b
respIʰ s opnQʰ     = opnL s

------------------------------------------------------------------------
-- The coupling

askB : St → Pt → Dist-ℚ (St × (Rʰ × Rʰ))
askB (t , m , f) x =
  fetchT id t x >>=ᴹ λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskB m f x u ρ)

comB : St → Bool → Dist-ℚ (St × (Rʰ × Rʰ))
comB (t , nothing , f) b = uniform-Vec k >>=ᴹ λ c → return-ℚ (outComB t b f c)
comB (t , just m , f)  _ = return-ℚ ((t , just m , f) , (idleRʰ , idleRʰ))

opnB : St → Dist-ℚ (St × (Rʰ × Rʰ))
opnB (t , just (c , b , false) , f) =
  uniform-Vec k >>=ᴹ λ r → return-ℚ (outOpnB t c b f r)
opnB (t , just (c , b , true) , f)  =
  return-ℚ ((t , just (c , b , true) , f) , (idleRʰ , idleRʰ))
opnB (t , nothing , f)              = return-ℚ ((t , nothing , f) , (idleRʰ , idleRʰ))

respBʰ : St → Qʰ → Dist-ℚ (St × (Rʰ × Rʰ))
respBʰ s (askQʰ x) = askB s x
respBʰ s (comQʰ b) = comB s b
respBʰ s opnQʰ     = opnB s

module C = Coupling hitOf respBʰ

s₀ : St
s₀ = [] , nothing , false

sL₀ sI₀ : StLʰ
sL₀ = [] , nothing
sI₀ = [] , nothing

sR₀ : StRʰ
sR₀ = nothing , [] , nothing

------------------------------------------------------------------------
-- Both marginals are the reference games

private
  -- The coupled query, expanded: the table's draw, then the deferred game's
  -- own draw of the opening randomness.
  ask-redᴮ : (t : Tbl) (m : Comʰ) (f : Bool) (x : Pt) (G : St × (Rʰ × Rʰ) → ℚ)
           → E (askB (t , m , f) x) G
             ≡ E (fetchT id t x)
                 (λ u → E (uniform-Vec k) (λ ρ → G (outAskB m f x u ρ)))
  ask-redᴮ t m f x G = trans
    (E-bind (fetchT id t x)
      (λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskB m f x u ρ)) G)
    (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u → trans
      (E-bind (uniform-Vec k) (λ ρ → return-ℚ (outAskB m f x u ρ)) G)
      (lookupᴰℚ-cong-P (entries (uniform-Vec k))
        (λ ρ → lookupᴰℚ-return (outAskB m f x u ρ) G))))

  ask-redᴸ : (t : Tbl) (m : Comʰ) (x : Pt) (G : StLʰ × Rʰ → ℚ)
           → E (askL (t , m) x) G
             ≡ E (fetchT id t x) (λ u → E (uniform-Vec k) (λ ρ → G (outAskL m x u ρ)))
  ask-redᴸ t m x G = trans
    (E-bind (fetchT id t x)
      (λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskL m x u ρ)) G)
    (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u → trans
      (E-bind (uniform-Vec k) (λ ρ → return-ℚ (outAskL m x u ρ)) G)
      (lookupᴰℚ-cong-P (entries (uniform-Vec k))
        (λ ρ → lookupᴰℚ-return (outAskL m x u ρ) G))))

  ask-redᴵ : (t : Tbl) (m : Comʰ) (x : Pt) (G : StLʰ × Rʰ → ℚ)
           → E (askI (t , m) x) G
             ≡ E (fetchT id t x) (λ u → G (outAskI m u))
  ask-redᴵ t m x G = trans
    (E-bind (fetchT id t x) (λ u → return-ℚ (outAskI m u)) G)
    (lookupᴰℚ-cong-P (entries (fetchT id t x))
      (λ u → lookupᴰℚ-return (outAskI m u) G))

  -- Off the flag the deferred game's answer IS the ideal one, and on the flag
  -- the coupling hands the ideal one over; so the ideal marginal always reads
  -- the table's value.
  collapseᴵ : (g h : Bool) (a d : Dig)
            → cond (g ∨ h) (ansRʰ d) (ansRʰ (cond h a d)) ≡ ansRʰ d
  collapseᴵ true  _     _ _ = refl
  collapseᴵ false true  _ _ = refl
  collapseᴵ false false _ _ = refl

_≋L_ _≋I_ : St → StLʰ → Set
s ≋L sL = eraseʰ s ≡ sL
s ≋I sI = eraseʰ s ≡ sI

-- The deferred marginal: the coupling's FIRST answer is the deferred game's.
stepL : StepBisim C.realK respLʰ _≋L_
stepL (t , m , f) _ refl (askQʰ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (askB (t , m , f) x) F)
 (trans (ask-redᴮ t m f x (λ w → F (C.fR w)))
 (trans (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u →
          lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ ρ → pt _ _ refl refl)))
        (sym (ask-redᴸ t m x F′))))
stepL (t , nothing , f) _ refl (comQʰ b) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (comB (t , nothing , f) b) F)
 (trans (E-bind (uniform-Vec k) (λ c → return-ℚ (outComB t b f c)) (λ w → F (C.fR w)))
 (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ c →
          trans (lookupᴰℚ-return (outComB t b f c) (λ w → F (C.fR w)))
                (trans (pt _ _ refl refl)
                       (sym (lookupᴰℚ-return (outComL t b c) F′)))))
        (sym (E-bind (uniform-Vec k) (λ c → return-ℚ (outComL t b c)) F′))))
stepL (t , just m , f) _ refl (comQʰ b) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (comB (t , just m , f) b) F)
 (trans (lookupᴰℚ-return ((t , just m , f) , (idleRʰ , idleRʰ)) (λ w → F (C.fR w)))
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return ((t , just m) , idleRʰ) F′))))
stepL (t , just (c , b , false) , f) _ refl opnQʰ F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (opnB (t , just (c , b , false) , f)) F)
 (trans (E-bind (uniform-Vec k) (λ r → return-ℚ (outOpnB t c b f r))
                (λ w → F (C.fR w)))
 (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ r →
          trans (lookupᴰℚ-return (outOpnB t c b f r) (λ w → F (C.fR w)))
                (trans (pt _ _ refl refl)
                       (sym (lookupᴰℚ-return (outOpnL t c b r) F′)))))
        (sym (E-bind (uniform-Vec k) (λ r → return-ℚ (outOpnL t c b r)) F′))))
stepL (t , just (c , b , true) , f) _ refl opnQʰ F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (opnB (t , just (c , b , true) , f)) F)
 (trans (lookupᴰℚ-return ((t , just (c , b , true) , f) , (idleRʰ , idleRʰ))
                         (λ w → F (C.fR w)))
 (trans (pt _ _ refl refl)
        (sym (lookupᴰℚ-return ((t , just (c , b , true)) , idleRʰ) F′))))
stepL (t , nothing , f) _ refl opnQʰ F F′ pt =
  trans (lookupᴰℚ-Dmap C.fR (opnB (t , nothing , f)) F)
 (trans (lookupᴰℚ-return ((t , nothing , f) , (idleRʰ , idleRʰ)) (λ w → F (C.fR w)))
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return ((t , nothing) , idleRʰ) F′))))

-- The ideal marginal: the coupling's second answer is the ideal game's, and
-- the deferred game's own draw is invisible to it (`E-const`).
stepI : StepBisim C.idealK respIʰ _≋I_
stepI (t , m , f) _ refl (askQʰ x) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (askB (t , m , f) x) F)
 (trans (ask-redᴮ t m f x (λ w → F (C.fI w)))
 (trans (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u → trans
          (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ ρ → trans
            (cong (λ z → F ((proj₁ u , m , f ∨ hitAt m x ρ) , z))
                  (collapseᴵ f (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u)))
            (pt _ _ refl refl)))
          (E-const (uniform-Vec k) (F′ (outAskI m u)))))
        (sym (ask-redᴵ t m x F′))))
stepI (t , nothing , f) _ refl (comQʰ b) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (comB (t , nothing , f) b) F)
 (trans (E-bind (uniform-Vec k) (λ c → return-ℚ (outComB t b f c)) (λ w → F (C.fI w)))
 (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ c →
          trans (lookupᴰℚ-return (outComB t b f c) (λ w → F (C.fI w)))
         (trans (cong (λ z → F ((t , just (c , b , false) , f) , z))
                      (cond-diag f (comRʰ c)))
                (trans (pt _ _ refl refl)
                       (sym (lookupᴰℚ-return (outComL t b c) F′))))))
        (sym (E-bind (uniform-Vec k) (λ c → return-ℚ (outComL t b c)) F′))))
stepI (t , just m , f) _ refl (comQʰ b) F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (comB (t , just m , f) b) F)
 (trans (lookupᴰℚ-return ((t , just m , f) , (idleRʰ , idleRʰ)) (λ w → F (C.fI w)))
 (trans (cong (λ z → F ((t , just m , f) , z)) (cond-diag f idleRʰ))
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return ((t , just m) , idleRʰ) F′)))))
stepI (t , just (c , b , false) , f) _ refl opnQʰ F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (opnB (t , just (c , b , false) , f)) F)
 (trans (E-bind (uniform-Vec k) (λ r → return-ℚ (outOpnB t c b f r))
                (λ w → F (C.fI w)))
 (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ r →
          trans (lookupᴰℚ-return (outOpnB t c b f r) (λ w → F (C.fI w)))
         (trans (cong (λ z → F (((b ∷ᵛ r , c) ∷ t , just (c , b , true) , f) , z))
                      (cond-diag f (opnRʰ b r)))
                (trans (pt _ _ refl refl)
                       (sym (lookupᴰℚ-return (outOpnL t c b r) F′))))))
        (sym (E-bind (uniform-Vec k) (λ r → return-ℚ (outOpnL t c b r)) F′))))
stepI (t , just (c , b , true) , f) _ refl opnQʰ F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (opnB (t , just (c , b , true) , f)) F)
 (trans (lookupᴰℚ-return ((t , just (c , b , true) , f) , (idleRʰ , idleRʰ))
                         (λ w → F (C.fI w)))
 (trans (cong (λ z → F ((t , just (c , b , true) , f) , z)) (cond-diag f idleRʰ))
 (trans (pt _ _ refl refl)
        (sym (lookupᴰℚ-return ((t , just (c , b , true)) , idleRʰ) F′)))))
stepI (t , nothing , f) _ refl opnQʰ F F′ pt =
  trans (lookupᴰℚ-Dmap C.fI (opnB (t , nothing , f)) F)
 (trans (lookupᴰℚ-return ((t , nothing , f) , (idleRʰ , idleRʰ)) (λ w → F (C.fI w)))
 (trans (cong (λ z → F ((t , nothing , f) , z)) (cond-diag f idleRʰ))
 (trans (pt _ _ refl refl) (sym (lookupᴰℚ-return ((t , nothing) , idleRʰ) F′)))))

------------------------------------------------------------------------
-- The potential: the flag rises by 2⁻ᵏ per query

private
  0≤drift : (g : Bool) → bool→ℚ g ≤ℚ bool→ℚ g +ℚ inv-pow-2 k
  0≤drift g = ≤-trans (≤-reflexive (sym (+-identityʳ (bool→ℚ g))))
                      (+-monoʳ-≤ (bool→ℚ g) (0≤inv-pow-2 k))

  -- A flag the kernel raises by comparing a FRESH uniform draw against a point
  -- it names: `guess-drift` when the head matches, nothing at all when it does
  -- not.  The draw is what makes the drift provable — a `r` already in the
  -- state is one the next query hits with probability 1.
  drift-∧ : (g a : Bool) (p : Dig)
          → E (uniform-Vec k) (λ ρ → bool→ℚ (g ∨ (a ∧ ⌊ ρ ≟ p ⌋)))
            ≤ℚ bool→ℚ g +ℚ inv-pow-2 k
  drift-∧ g true  p = guess-drift k g p
  drift-∧ g false p = ≤-trans
    (≤-reflexive (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                          (λ _ → cong bool→ℚ (∨-identityʳ g)))
                        (E-const (uniform-Vec k) (bool→ℚ g))))
    (0≤drift g)

  hit-drift : (m : Comʰ) (g : Bool) (x : Pt)
            → E (uniform-Vec k) (λ ρ → bool→ℚ (g ∨ hitAt m x ρ))
              ≤ℚ bool→ℚ g +ℚ inv-pow-2 k
  hit-drift (just (_ , b , false)) g x = drift-∧ g ⌊ head x ≟ b ⌋ (tail x)
  hit-drift (just (_ , _ , true))  g x = drift-∧ g false (tail x)
  hit-drift nothing                g x = drift-∧ g false (tail x)

  hitP : St × Rʰ → ℚ
  hitP sr = bool→ℚ (hitOf (proj₁ sr))

  -- A query that does not reach the oracle leaves the flag where it was.
  idle-red : (s s′ : St) (a : Rʰ × Rʰ) (q : Qʰ)
           → respBʰ s q ≡ return-ℚ (s′ , a) → hitOf s′ ≡ hitOf s
           → E (C.realK s q) hitP ≡ bool→ℚ (hitOf s)
  idle-red s s′ a q eq hs =
    trans (lookupᴰℚ-Dmap C.fR (respBʰ s q) hitP)
   (trans (cong (λ μ → E μ (λ w → hitP (C.fR w))) eq)
   (trans (lookupᴰℚ-return (s′ , a) (λ w → hitP (C.fR w))) (cong bool→ℚ hs)))

  -- …and one that only SAMPLES leaves it where it was too.
  draw-red : (s : St) (q : Qʰ) (κ : Dig → St × (Rʰ × Rʰ))
           → respBʰ s q ≡ (uniform-Vec k >>=ᴹ λ a → return-ℚ (κ a))
           → (∀ a → hitOf (proj₁ (κ a)) ≡ hitOf s)
           → E (C.realK s q) hitP ≡ bool→ℚ (hitOf s)
  draw-red s q κ eq hs =
    trans (lookupᴰℚ-Dmap C.fR (respBʰ s q) hitP)
   (trans (cong (λ μ → E μ (λ w → hitP (C.fR w))) eq)
   (trans (E-bind (uniform-Vec k) (λ a → return-ℚ (κ a)) (λ w → hitP (C.fR w)))
   (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
            (λ a → trans (lookupᴰℚ-return (κ a) (λ w → hitP (C.fR w)))
                         (cong bool→ℚ (hs a))))
          (E-const (uniform-Vec k) (bool→ℚ (hitOf s))))))

rare-raise : RareRaise C.realK hitOf (inv-pow-2 k)
rare-raise (t , m , f) (askQʰ x) = ≤-trans
  (≤-reflexive (trans (lookupᴰℚ-Dmap C.fR (askB (t , m , f) x) hitP)
                      (ask-redᴮ t m f x (λ w → hitP (C.fR w)))))
  (≤-trans (E-mono (fetchT id t x)
             (λ u → E (uniform-Vec k) (λ ρ → hitP (C.fR (outAskB m f x u ρ))))
             (λ _ → bool→ℚ f +ℚ inv-pow-2 k) (λ u → hit-drift m f x))
           (≤-reflexive (E-const (fetchT id t x) (bool→ℚ f +ℚ inv-pow-2 k))))
rare-raise (t , nothing , f) (comQʰ b) = ≤-trans
  (≤-reflexive (draw-red (t , nothing , f) (comQʰ b)
    (λ c → (t , just (c , b , false) , f) , (comRʰ c , comRʰ c)) refl (λ _ → refl)))
  (0≤drift f)
rare-raise (t , just m , f) (comQʰ b) = ≤-trans
  (≤-reflexive (idle-red (t , just m , f) (t , just m , f) (idleRʰ , idleRʰ)
    (comQʰ b) refl refl))
  (0≤drift f)
rare-raise (t , just (c , b , false) , f) opnQʰ = ≤-trans
  (≤-reflexive (draw-red (t , just (c , b , false) , f) opnQʰ
    (λ r → ((b ∷ᵛ r , c) ∷ t , just (c , b , true) , f) , (opnRʰ b r , opnRʰ b r))
    refl (λ _ → refl)))
  (0≤drift f)
rare-raise (t , just (c , b , true) , f) opnQʰ = ≤-trans
  (≤-reflexive (idle-red (t , just (c , b , true) , f) (t , just (c , b , true) , f)
    (idleRʰ , idleRʰ) opnQʰ refl refl))
  (0≤drift f)
rare-raise (t , nothing , f) opnQʰ = ≤-trans
  (≤-reflexive (idle-red (t , nothing , f) (t , nothing , f) (idleRʰ , idleRʰ)
    opnQʰ refl refl))
  (0≤drift f)

------------------------------------------------------------------------
-- Deferred sampling at the real game

-- The secret is unread until the commitment hashes with it, so planting it at
-- the start and averaging over the plant is the same run as drawing it there.
-- Before the commitment the family is the planted one and the state has
-- nothing planted; after it the family is constant, which is where `E-const`
-- collapses the average the draw has just created.
_≋P_ : (Dig → StRʰ) → StRʰ → Set
f ≋P s = (Σ[ t ∈ Tbl ] ((∀ r → f r ≡ (just r , t , nothing))
                        × (s ≡ (nothing , t , nothing))))
       ⊎ (∀ r → f r ≡ s)

private
  ask-redᴿ : (mr : Maybe Dig) (t : Tbl) (z : ComRʰ) (x : Pt) (G : StRʰ × Rʰ → ℚ)
           → E (askR (mr , t , z) x) G
             ≡ E (fetchT id t x) (λ u → G (outAskR mr z u))
  ask-redᴿ mr t z x G = trans
    (E-bind (fetchT id t x) (λ u → return-ℚ (outAskR mr z u)) G)
    (lookupᴰℚ-cong-P (entries (fetchT id t x))
      (λ u → lookupᴰℚ-return (outAskR mr z u) G))

  module _ (F F′ : StRʰ × Rʰ → ℚ)
           (pt : (g : Dig → StRʰ × Rʰ) (w : StRʰ × Rʰ)
               → (λ r → proj₁ (g r)) ≋P proj₁ w → (∀ r → proj₂ (g r) ≡ proj₂ w)
               → E (uniform-Vec k) (λ r → F (g r)) ≡ F′ w) where

    -- the premise at a CONSTANT family: the two integrands agree everywhere
    hereP : (w : StRʰ × Rʰ) → F w ≡ F′ w
    hereP w = trans (sym (E-const (uniform-Vec k) (F w)))
                    (pt (λ _ → w) w (inj₂ (λ _ → refl)) (λ _ → refl))

avg-commit : AvgBisim (uniform-Vec k) respRʰ respRʰ _≋P_
avg-commit f s (inj₁ (t , ff , refl)) (askQʰ x) F F′ pt = trans
  (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
           (λ r → trans (cong (λ z → E (respRʰ z (askQʰ x)) F) (ff r))
                        (ask-redᴿ (just r) t nothing x F)))
         (E-swap (uniform-Vec k) (fetchT id t x)
           (λ r u → F ((just r , proj₁ u , nothing) , ansRʰ (proj₂ u)))))
  (trans (lookupᴰℚ-cong-P (entries (fetchT id t x))
           (λ u → pt (λ r → (just r , proj₁ u , nothing) , ansRʰ (proj₂ u))
                     ((nothing , proj₁ u , nothing) , ansRʰ (proj₂ u))
                     (inj₁ (proj₁ u , (λ _ → refl) , refl)) (λ _ → refl)))
         (sym (ask-redᴿ nothing t nothing x F′)))
avg-commit f s (inj₁ (t , ff , refl)) (comQʰ b) F F′ pt = trans
  (lookupᴰℚ-cong-P (entries (uniform-Vec k))
    (λ r → trans (cong (λ z → E (respRʰ z (comQʰ b)) F) (ff r))
                 (lookupᴰℚ-cong-P (entries (comAt r t b)) (hereP F F′ pt))))
  (sym (E-bind (uniform-Vec k) (λ r → comAt r t b) F′))
avg-commit f s (inj₁ (t , ff , refl)) opnQʰ F F′ pt = trans
  (lookupᴰℚ-cong-P (entries (uniform-Vec k))
    (λ r → trans (cong (λ z → E (respRʰ z opnQʰ) F) (ff r))
                 (lookupᴰℚ-return ((just r , t , nothing) , idleRʰ) F)))
  (trans (pt (λ r → (just r , t , nothing) , idleRʰ) ((nothing , t , nothing) , idleRʰ)
             (inj₁ (t , (λ _ → refl) , refl)) (λ _ → refl))
         (sym (lookupᴰℚ-return ((nothing , t , nothing) , idleRʰ) F′)))
avg-commit f s (inj₂ ff) q F F′ pt = trans
  (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
           (λ r → cong (λ z → E (respRʰ z q) F) (ff r)))
         (E-const (uniform-Vec k) (E (respRʰ s q) F)))
  (lookupᴰℚ-cong-P (entries (respRʰ s q)) (hereP F F′ pt))

-- The real game draws its secret at the commitment, and that IS its average
-- over a secret planted at the start — the identity `docs/fcom-extraction.md`
-- item 2 calls `defer`, here at this game.
defer-commit : (d : Strat Qʰ Rʰ)
             → E (uniform-Vec k) (λ r → Pr₁ (runWith respRʰ (just r , [] , nothing) d))
               ≡ Pr₁ (runWith respRʰ sR₀ d)
defer-commit d = runWith-avg (uniform-Vec k) respRʰ respRʰ _≋P_ avg-commit d
  (λ r → just r , [] , nothing) sR₀ (inj₁ ([] , (λ _ → refl) , refl))

------------------------------------------------------------------------
-- The bound

εᴸ : ℕ → ℚ
εᴸ m = fromℕ m *ℚ inv-pow-2 k

cert : SuperCert C.realK hitOf s₀ εᴸ
cert = rare-cert C.realK hitOf s₀ (inv-pow-2 k) (0≤inv-pow-2 k) refl rare-raise

-- For every adversary of at most `m` activations, `F_com` with the programming
-- simulator and the commitment protocol with its opening randomness DEFERRED
-- differ by at most `m·2⁻ᵏ`.
hiding-bound : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
             → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respLʰ sL₀ d) ∣ℚ ≤ℚ εᴸ m
hiding-bound = hop-bound hitOf respBʰ respLʰ respIʰ s₀ sL₀ sI₀
  (λ d → runWith-bisim C.realK respLʰ _≋L_ stepL d s₀ sL₀ refl)
  (λ d → runWith-bisim C.idealK respIʰ _≋I_ stepI d s₀ sI₀ refl)
  cert

-- …and the statement the residual buys: with the deferred game identified with
-- the real one at `ε′`, the ideal world is within `ε′ + m·2⁻ᵏ` of the protocol
-- that draws `r` at the commitment.  `docs/fcom-hiding.md` states what `ε′`
-- costs and why it is NOT zero.
hiding-bound-defer : {ε′ : ℕ → ℚ}
                   → ((m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
                      → ∣ Pr₁ (runWith respLʰ sL₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
                        ≤ℚ ε′ m)
                   → (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
                   → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
                     ≤ℚ εᴸ m +ℚ ε′ m
hiding-bound-defer {ε′} dfr m d le = ≤-trans
  (≤-trans (≤-reflexive (cong ∣_∣ℚ (sym (telescope pI pL pR))))
           (∣p+q∣≤∣p∣+∣q∣ (pI -ℚ pL) (pL -ℚ pR)))
  (+-mono-≤ (hiding-bound m d le) (dfr m d le))
  where
  pI = Pr₁ (runWith respIʰ sI₀ d)
  pL = Pr₁ (runWith respLʰ sL₀ d)
  pR = Pr₁ (runWith respRʰ sR₀ d)
