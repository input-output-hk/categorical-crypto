{-# OPTIONS --safe --without-K #-}

-- The deferred-sampling hop of the hiding game: `respLʰ` against `respRʰ`.
--
-- The two games draw the opening randomness at different moments, so they are
-- identical-until-bad and not equal (`docs/fcom-hiding.md`).  Both halves of
-- the argument are AVERAGES over the plant: the real game with its secret
-- planted at the start is the real game (`Game.defer-commit`), the deferred
-- game with the same plant read at the opening is the deferred game
-- (`defer-hop`), and between the two planted games there is a per-plant
-- coupling whose flag is small only ON AVERAGE — the adversary that knows the
-- plant hits it with probability 1.
--
-- The two divergences the flag pays for, `2⁻ᵏ` each per activation:
--
--   • the adversary names the plant while the commitment is outstanding —
--     the real game answers that point out of its table with the published
--     digest, the deferred game draws afresh.  It also covers the COMMITMENT
--     step, where the real game reads `H(b ∷ r)` out of the table if that
--     point was queried before: it could only have been queried by naming the
--     plant, so the flag is already up (`Fresh`).
--   • the deferred game's own fresh test hits — it then answers the published
--     digest at a point the real game has nothing special at (`hitAt`).
--
-- Nothing rises once the commitment is OPEN: the plant is public by then, the
-- two tables answer alike everywhere, and `Average.Frozen` is what lets the
-- adversary's later queries depend on the plant at all.

open import Class.DecEq

open import Data.Bool.Base using (Bool; false; true; _∧_; _∨_)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import Data.List.NonEmpty as NE using ()
open import Data.List.Relation.Unary.All as ListAll using ()
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product.Base using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; 0ℚ)
  renaming (_+_ to _+ℚ_; _*_ to _*ℚ_; _-_ to _-ℚ_; ∣_∣ to ∣_∣ℚ; _≤_ to _≤ℚ_)
open import Data.Rational.Properties using
  ( +-identityˡ; +-identityʳ; +-mono-≤; +-monoʳ-≤; +-monoˡ-≤; *-distribʳ-+
  ; *-distribˡ-+; ≤-reflexive; ≤-trans )
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (head; tail) renaming (_∷_ to _∷ᵛ_)
open import Function.Base using (case_of_; id)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable.Core using (⌊_⌋; yes; no)

open import CategoricalCrypto.GamePlaying
open import CategoricalCrypto.GamePlaying.Average
open import CategoricalCrypto.GamePlaying.Defer
open import CategoricalCrypto.GamePlaying.Hop
open import CategoricalCrypto.Interaction
open import CategoricalCrypto.Strategy
open import ProbabilisticLogic.Distribution.RationalDist
open import ProbabilisticLogic.Distribution.RationalDist.Expectation
open import ProbabilisticLogic.Distribution.Uniform using
  (0≤inv-pow-2; P-uniform-Vec; bool→ℚ; fromℕ; fromℕ-+; inv-pow-2; uniform-Vec)

module CategoricalCrypto.Examples.ROCommitment.Hiding.Defer (k : ℕ) where

open import CategoricalCrypto.Examples.ROCommitment.Extraction k using
  (Dig; Pt; Tbl; lookup-here; lookup-there; lookupPt)
open import CategoricalCrypto.Examples.ROCommitment.Hiding.Game k
open import CategoricalCrypto.Examples.ROCommitment.Oracle k

------------------------------------------------------------------------
-- Reading the table, and the two shapes one query's draw comes in

private
  os-any : {A : Set} (μ : Dist-ℚ A) → OnSupport (λ _ → ⊤) μ
  os-any μ = ListAll.universal (λ _ → tt) (NE.toList (entries μ))

  ∨-≤ : (a b : Bool) → bool→ℚ (a ∨ b) ≤ℚ bool→ℚ a +ℚ bool→ℚ b
  ∨-≤ true  b = ≤-trans (≤-reflexive (sym (+-identityʳ (bool→ℚ true))))
                        (+-monoʳ-≤ (bool→ℚ true) (0≤bool b))
  ∨-≤ false b = ≤-reflexive (sym (+-identityˡ (bool→ℚ b)))

  ⌊⌋-false : {A : Set} ⦃ _ : DecEq A ⦄ {x y : A} → ⌊ x ≟ y ⌋ ≡ false → x ≢ y
  ⌊⌋-false {x = x} {y} eq with x ≟ y
  ... | no ne = ne

------------------------------------------------------------------------
-- The deferred game with the opening randomness PLANTED

-- Is the commitment still a secret?  Nothing the adversary does after the
-- opening can tell the two games apart, which is what freezes the flag.
preOpen : Comʰ → Bool
preOpen (just (_ , _ , true))  = false
preOpen (just (_ , _ , false)) = true
preOpen nothing                = true

-- The adversary has named the plant while it is still a secret.
guessAt : Comʰ → Dig → Pt → Bool
guessAt m r x = preOpen m ∧ ⌊ r ≟ tail x ⌋

-- …and the flag: that, or the deferred game's own fresh test hitting.
riseAt : Comʰ → Dig → Pt → Dig → Bool
riseAt m r x ρ = hitAt m x ρ ∨ guessAt m r x

StPʰ : Set
StPʰ = Dig × Tbl × Comʰ × Bool

flagP : StPʰ → Bool
flagP (_ , _ , _ , f) = f

Opened : StPʰ → Set
Opened (_ , _ , just (_ , _ , true)  , _) = ⊤
Opened (_ , _ , just (_ , _ , false) , _) = ⊥
Opened (_ , _ , nothing              , _) = ⊥

outAskP : Dig → Comʰ → Bool → Pt → Tbl × Dig → Dig → StPʰ × Rʰ
outAskP r m f x u ρ = ( (r , proj₁ u , m , f ∨ riseAt m r x ρ)
                      , ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u)) )

outComP : Dig → Tbl → Bool → Bool → Dig → StPʰ × Rʰ
outComP r t b f c = (r , t , just (c , b , false) , f) , comRʰ c

outOpnP : Dig → Tbl → Dig → Bool → Bool → StPʰ × Rʰ
outOpnP r t c b f = (r , (b ∷ᵛ r , c) ∷ t , just (c , b , true) , f) , opnRʰ b r

askP : StPʰ → Pt → Dist-ℚ (StPʰ × Rʰ)
askP (r , t , m , f) x =
  fetchT id t x >>=ᴹ λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskP r m f x u ρ)

comP : StPʰ → Bool → Dist-ℚ (StPʰ × Rʰ)
comP (r , t , nothing  , f) b = uniform-Vec k >>=ᴹ λ c → return-ℚ (outComP r t b f c)
comP (r , t , just mm  , f) _ = return-ℚ ((r , t , just mm , f) , idleRʰ)

opnP : StPʰ → Dist-ℚ (StPʰ × Rʰ)
opnP (r , t , just (c , b , false) , f) = return-ℚ (outOpnP r t c b f)
opnP (r , t , just (c , b , true)  , f) = return-ℚ ((r , t , just (c , b , true) , f) , idleRʰ)
opnP (r , t , nothing              , f) = return-ℚ ((r , t , nothing , f) , idleRʰ)

respPʰ : StPʰ → Qʰ → Dist-ℚ (StPʰ × Rʰ)
respPʰ s (askQʰ x) = askP s x
respPʰ s (comQʰ b) = comP s b
respPʰ s opnQʰ     = opnP s

sP₀ : Dig → StPʰ
sP₀ r = r , [] , nothing , false

ask-redᴾ : (r : Dig) (t : Tbl) (m : Comʰ) (f : Bool) (x : Pt) (G : StPʰ × Rʰ → ℚ)
         → E (askP (r , t , m , f) x) G
           ≡ E (fetchT id t x) (λ u → E (uniform-Vec k) (λ ρ → G (outAskP r m f x u ρ)))
ask-redᴾ r t m f x = E-bind₂ (fetchT id t x) (uniform-Vec k) (outAskP r m f x)

------------------------------------------------------------------------
-- Deferring the plant: the planted game, averaged, IS the deferred game

eraseP : StPʰ → StLʰ
eraseP (_ , t , m , _) = t , m

-- Before the opening the plant is unread, so a family of planted states is
-- one deferring state with a flag hung on it.  At the opening the planted run
-- has its draw already and the deferring run makes it — that is where
-- `runWith-avg` merges the two averages — and after it the family is
-- CONSTANT, as it must be: `opnRʰ b r` is the first answer that depends on
-- the plant, so the distinguisher's later queries do too.
_≋D_ : (Dig → StPʰ) → StLʰ → Set
f ≋D s = (Σ[ t ∈ Tbl ] Σ[ m ∈ Comʰ ] Σ[ φ ∈ (Dig → Bool) ]
            ((∀ r → f r ≡ (r , t , m , φ r)) × (s ≡ (t , m))))
       ⊎ (Σ[ r₀ ∈ Dig ] Σ[ t ∈ Tbl ] Σ[ c ∈ Dig ] Σ[ b ∈ Bool ] Σ[ fl ∈ Bool ]
            ((∀ r → f r ≡ (r₀ , t , just (c , b , true) , fl))
             × (s ≡ (t , just (c , b , true)))))

private
  PtD : (StPʰ × Rʰ → ℚ) → (StLʰ × Rʰ → ℚ) → Set
  PtD F F′ = (g : Dig → StPʰ × Rʰ) (w : StLʰ × Rʰ) → (λ r → proj₁ (g r)) ≋D proj₁ w
           → (∀ r → proj₂ (g r) ≡ proj₂ w) → E (uniform-Vec k) (λ r → F (g r)) ≡ F′ w

  const-collapse : (q : Qʰ) (F : StPʰ × Rʰ → ℚ) {f : Dig → StPʰ} {w : StPʰ}
                 → (∀ r → f r ≡ w)
                 → E (uniform-Vec k) (λ r → E (respPʰ (f r) q) F) ≡ E (respPʰ w q) F
  const-collapse q F {w = w} ff =
    trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
            (λ r → cong (λ z → E (respPʰ z q) F) (ff r)))
          (E-const (uniform-Vec k) (E (respPʰ w q) F))

  -- the premise at a constant family, where the average collapses: past the
  -- opening the planted run and the deferring run are the same run.
  hereD : (F : StPʰ × Rʰ → ℚ) (F′ : StLʰ × Rʰ → ℚ) → PtD F F′
        → (r₀ : Dig) (t : Tbl) (c : Dig) (b fl : Bool) (a : Rʰ)
        → F ((r₀ , t , just (c , b , true) , fl) , a) ≡ F′ ((t , just (c , b , true)) , a)
  hereD F F′ pt r₀ t c b fl a =
    trans (sym (E-const (uniform-Vec k) (F ((r₀ , t , just (c , b , true) , fl) , a))))
          (pt (λ _ → (r₀ , t , just (c , b , true) , fl) , a) ((t , just (c , b , true)) , a)
              (inj₂ (r₀ , t , c , b , fl , (λ _ → refl) , refl)) (λ _ → refl))

avg-defer : AvgBisim (uniform-Vec k) respPʰ respLʰ _≋D_
avg-defer f s (inj₁ (t , m , φ , ff , refl)) (askQʰ x) F F′ pt =
  trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
          (λ r → trans (cong (λ z → E (respPʰ z (askQʰ x)) F) (ff r))
                       (ask-redᴾ r t m (φ r) x F)))
 (trans (E-swap (uniform-Vec k) (fetchT id t x)
          (λ r u → E (uniform-Vec k) (λ ρ → F (outAskP r m (φ r) x u ρ))))
 (trans (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u →
           trans (E-swap (uniform-Vec k) (uniform-Vec k)
                   (λ r ρ → F (outAskP r m (φ r) x u ρ)))
                 (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ ρ →
                    pt (λ r → outAskP r m (φ r) x u ρ) (outAskL m x u ρ)
                       (inj₁ ( proj₁ u , m , (λ r → φ r ∨ riseAt m r x ρ)
                             , (λ r → refl) , refl))
                       (λ r → refl)))))
        (sym (ask-redᴸ t m x F′))))
avg-defer f s (inj₁ (t , nothing , φ , ff , refl)) (comQʰ b) F F′ pt =
  trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
          (λ r → trans (cong (λ z → E (respPʰ z (comQʰ b)) F) (ff r))
                       (lookupᴰℚ-Dmap (outComP r t b (φ r)) (uniform-Vec k) F)))
 (trans (E-swap (uniform-Vec k) (uniform-Vec k) (λ r c → F (outComP r t b (φ r) c)))
 (trans (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ c →
           pt (λ r → outComP r t b (φ r) c) (outComL t b c)
              (inj₁ (t , just (c , b , false) , φ , (λ r → refl) , refl)) (λ r → refl)))
        (sym (lookupᴰℚ-Dmap (outComL t b) (uniform-Vec k) F′))))
avg-defer f s (inj₁ (t , just mm , φ , ff , refl)) (comQʰ b) F F′ pt =
  trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
          (λ r → trans (cong (λ z → E (respPʰ z (comQʰ b)) F) (ff r))
                       (lookupᴰℚ-return ((r , t , just mm , φ r) , idleRʰ) F)))
 (trans (pt (λ r → (r , t , just mm , φ r) , idleRʰ) ((t , just mm) , idleRʰ)
            (inj₁ (t , just mm , φ , (λ r → refl) , refl)) (λ r → refl))
        (sym (lookupᴰℚ-return ((t , just mm) , idleRʰ) F′)))
avg-defer f s (inj₁ (t , just (c , b , false) , φ , ff , refl)) opnQʰ F F′ pt =
  trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
          (λ r → trans (cong (λ z → E (respPʰ z opnQʰ) F) (ff r))
                 (trans (lookupᴰℚ-return (outOpnP r t c b (φ r)) F)
                        (hereD F F′ pt r ((b ∷ᵛ r , c) ∷ t) c b (φ r) (opnRʰ b r)))))
        (sym (lookupᴰℚ-Dmap (outOpnL t c b) (uniform-Vec k) F′))
avg-defer f s (inj₁ (t , just (c , b , true) , φ , ff , refl)) opnQʰ F F′ pt =
  trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
          (λ r → trans (cong (λ z → E (respPʰ z opnQʰ) F) (ff r))
                       (lookupᴰℚ-return ((r , t , just (c , b , true) , φ r) , idleRʰ) F)))
 (trans (pt (λ r → (r , t , just (c , b , true) , φ r) , idleRʰ)
            ((t , just (c , b , true)) , idleRʰ)
            (inj₁ (t , just (c , b , true) , φ , (λ r → refl) , refl)) (λ r → refl))
        (sym (lookupᴰℚ-return ((t , just (c , b , true)) , idleRʰ) F′)))
avg-defer f s (inj₁ (t , nothing , φ , ff , refl)) opnQʰ F F′ pt =
  trans (lookupᴰℚ-cong-P (entries (uniform-Vec k))
          (λ r → trans (cong (λ z → E (respPʰ z opnQʰ) F) (ff r))
                       (lookupᴰℚ-return ((r , t , nothing , φ r) , idleRʰ) F)))
 (trans (pt (λ r → (r , t , nothing , φ r) , idleRʰ) ((t , nothing) , idleRʰ)
            (inj₁ (t , nothing , φ , (λ r → refl) , refl)) (λ r → refl))
        (sym (lookupᴰℚ-return ((t , nothing) , idleRʰ) F′)))
avg-defer f s (inj₂ (r₀ , t , c , b , fl , ff , refl)) (askQʰ x) F F′ pt =
  trans (const-collapse (askQʰ x) F ff)
 (trans (ask-redᴾ r₀ t (just (c , b , true)) fl x F)
 (trans (lookupᴰℚ-cong-P (entries (fetchT id t x)) (λ u →
           lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ ρ →
             hereD F F′ pt r₀ (proj₁ u) c b (fl ∨ riseAt (just (c , b , true)) r₀ x ρ)
               (ansRʰ (proj₂ u)))))
        (sym (ask-redᴸ t (just (c , b , true)) x F′))))
avg-defer f s (inj₂ (r₀ , t , c , b , fl , ff , refl)) (comQʰ b′) F F′ pt =
  trans (const-collapse (comQʰ b′) F ff)
 (trans (lookupᴰℚ-return ((r₀ , t , just (c , b , true) , fl) , idleRʰ) F)
 (trans (hereD F F′ pt r₀ t c b fl idleRʰ)
        (sym (lookupᴰℚ-return ((t , just (c , b , true)) , idleRʰ) F′))))
avg-defer f s (inj₂ (r₀ , t , c , b , fl , ff , refl)) opnQʰ F F′ pt =
  trans (const-collapse opnQʰ F ff)
 (trans (lookupᴰℚ-return ((r₀ , t , just (c , b , true) , fl) , idleRʰ) F)
 (trans (hereD F F′ pt r₀ t c b fl idleRʰ)
        (sym (lookupᴰℚ-return ((t , just (c , b , true)) , idleRʰ) F′))))

-- The real game draws the opening randomness at the opening, and that IS the
-- average over a plant nothing before the opening reads.
defer-hop : (d : Strat Qʰ Rʰ)
          → E (uniform-Vec k) (λ r → Pr₁ (runWith respPʰ (sP₀ r) d))
            ≡ Pr₁ (runWith respLʰ sL₀ d)
defer-hop d = runWith-avg (uniform-Vec k) respPʰ respLʰ _≋D_ avg-defer d sP₀ sL₀
  (inj₁ ([] , nothing , (λ _ → false) , (λ r → refl) , refl))

------------------------------------------------------------------------
-- The two games' tables, and where they part

-- The real game's table, read as the deferred game's plus the commitment's
-- own point: `H(b ∷ r)` is filed there at the COMMITMENT and here only at the
-- opening, so off that one point the two answer alike.
TblAt : Comʰ → Dig → Tbl → Pt → Maybe Dig
TblAt (just (c , b , false)) r t = lookupPt ((b ∷ᵛ r , c) ∷ t)
TblAt (just (_ , _ , true))  _ t = lookupPt t
TblAt nothing                _ t = lookupPt t

-- …and its commitment record, which is the deferred game's plus the plant.
recOf : Comʰ → Dig → ComRʰ
recOf (just (c , b , o)) r = just (c , b , r , o)
recOf nothing            _ = nothing

-- No tabulated point names the plant.  This is what stops the real game's
-- commitment step from reading `H(b ∷ r)` straight out of the table, and a
-- query that destroys it has raised the flag on its way.
Fresh : Comʰ → Dig → Tbl → Set
Fresh nothing  r t = ∀ b → lookupPt t (b ∷ᵛ r) ≡ nothing
Fresh (just _) _ _ = ⊤

_≋J_ : StPʰ → StRʰ → Set
(r , t , m , f) ≋J (mr , t′ , z) =
  (f ≡ false) × (mr ≡ just r) × (z ≡ recOf m r)
  × (∀ y → lookupPt t′ y ≡ TblAt m r t y) × Fresh m r t

private
  tail-≢ : (r : Dig) (x : Pt) (b : Bool) → ⌊ r ≟ tail x ⌋ ≡ false → x ≢ (b ∷ᵛ r)
  tail-≢ r x b g refl = ⌊⌋-false g refl

  tblAt-miss : (m : Comʰ) (r : Dig) (t : Tbl) (x : Pt)
             → TblAt m r t x ≡ nothing → lookupPt t x ≡ nothing
  tblAt-miss (just (c , b , false)) r t x with x ≟ (b ∷ᵛ r)
  ... | yes _ = λ eq → case eq of λ ()
  ... | no  _ = id
  tblAt-miss (just (_ , _ , true)) r t x = id
  tblAt-miss nothing               r t x = id

  same-at : (m : Comʰ) (r : Dig) (t t′ : Tbl) (x : Pt)
          → (∀ y → lookupPt t′ y ≡ TblAt m r t y) → guessAt m r x ≡ false
          → lookupPt t′ x ≡ lookupPt t x
  same-at nothing               r t t′ x tbl g = tbl x
  same-at (just (_ , _ , true)) r t t′ x tbl g = tbl x
  same-at (just (c , b , false)) r t t′ x tbl g =
    trans (tbl x) (lookup-there x (b ∷ᵛ r) c t (tail-≢ r x b g))

  tbl-∷ : (m : Comʰ) (r : Dig) (t t′ : Tbl) (x : Pt) (h : Dig)
        → (∀ y → lookupPt t′ y ≡ TblAt m r t y) → guessAt m r x ≡ false
        → ∀ y → lookupPt ((x , h) ∷ t′) y ≡ TblAt m r ((x , h) ∷ t) y
  tbl-∷ nothing r t t′ x h tbl g y with y ≟ x
  ... | yes _ = refl
  ... | no  _ = tbl y
  tbl-∷ (just (_ , _ , true)) r t t′ x h tbl g y with y ≟ x
  ... | yes _ = refl
  ... | no  _ = tbl y
  tbl-∷ (just (c , b , false)) r t t′ x h tbl g y with y ≟ (b ∷ᵛ r)
  ... | yes refl = trans (lookup-there (b ∷ᵛ r) x h t′ (λ e → tail-≢ r x b g (sym e)))
                         (trans (tbl (b ∷ᵛ r)) (lookup-here (b ∷ᵛ r) c t))
  ... | no ne with y ≟ x
  ... | yes _ = refl
  ... | no  _ = trans (tbl y) (lookup-there y (b ∷ᵛ r) c t ne)

  fresh-∷ : (m : Comʰ) (r : Dig) (t : Tbl) (x : Pt) (h : Dig)
          → Fresh m r t → guessAt m r x ≡ false → Fresh m r ((x , h) ∷ t)
  fresh-∷ nothing  r t x h frs g b =
    trans (lookup-there (b ∷ᵛ r) x h t (λ e → tail-≢ r x b g (sym e))) (frs b)
  fresh-∷ (just _) _ _ _ _ _ _ = tt

-- The real game's own fetch, driven by the deferred game's draw where the two
-- tables agree and by its own entry where they do not.
fetchR : Tbl → Pt → Dig → Tbl × Dig
fetchR t′ x h with lookupPt t′ x
... | just d  = t′ , d
... | nothing = (x , h) ∷ t′ , h

fetchR-hit : (t′ : Tbl) (x : Pt) (d h : Dig) → lookupPt t′ x ≡ just d
           → fetchR t′ x h ≡ (t′ , d)
fetchR-hit t′ x d h eq rewrite eq = refl

fetchR-miss : (t′ : Tbl) (x : Pt) (h : Dig) → lookupPt t′ x ≡ nothing
            → fetchR t′ x h ≡ ((x , h) ∷ t′ , h)
fetchR-miss t′ x h eq rewrite eq = refl

------------------------------------------------------------------------
-- The coupling, up to the flag

good-J : (s : StPʰ) (s′ : StRʰ) → s ≋J s′ → flagP s ≡ false
good-J (r , t , m , f) (mr , t′ , z) (ef , _) = ef

private
  -- Neither kernel draws and neither parts from the other: the join is the
  -- pair of outcomes.  Every activation but an oracle query and the
  -- commitment is of this shape in one game or the other.
  idle-join : (w : StPʰ × Rʰ) (w′ : StRʰ × Rʰ) → proj₁ w ≋J proj₁ w′ → proj₂ w ≡ proj₂ w′
            → Σ[ ν ∈ Dist-ℚ ((StPʰ × Rʰ) × (StRʰ × Rʰ)) ]
                ( (∀ F  → E ν (λ p → F  (proj₁ p)) ≡ E (return-ℚ w ) F )
                × (∀ F′ → E ν (λ p → F′ (proj₂ p)) ≡ E (return-ℚ w′) F′)
                × OnSupport (λ p → (flagP (proj₁ (proj₁ p)) ≡ true)
                                 ⊎ ((proj₁ (proj₁ p) ≋J proj₁ (proj₂ p))
                                    × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) ν )
  idle-join w w′ rel ans = return-ℚ (w , w′)
    , (λ F  → trans (lookupᴰℚ-return (w , w′) (λ p → F  (proj₁ p)))
                    (sym (lookupᴰℚ-return w  F )))
    , (λ F′ → trans (lookupᴰℚ-return (w , w′) (λ p → F′ (proj₂ p)))
                    (sym (lookupᴰℚ-return w′ F′)))
    , OnSupport-return (inj₂ (rel , ans))

join-J : JoinStep respPʰ respRʰ flagP _≋J_
join-J (r , t , m , f) (mr , t′ , z) (refl , refl , refl , tbl , frs) (askQʰ x) =
  νa , mgL , mgR , sup
  where
  κa : Tbl × Dig → Dig → (StPʰ × Rʰ) × (StRʰ × Rʰ)
  κa u ρ = outAskP r m false x u ρ
         , outAskR (just r) (recOf m r) (fetchR t′ x (proj₂ u))

  νa = fetchT id t x >>=ᴹ λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (κa u ρ)

  mgL : ∀ F → E νa (λ p → F (proj₁ p)) ≡ E (askP (r , t , m , false) x) F
  mgL F = trans (E-bind₂ (fetchT id t x) (uniform-Vec k) κa (λ p → F (proj₁ p)))
                (sym (ask-redᴾ r t m false x F))

  redR : (F : StRʰ × Rʰ → ℚ)
       → E (fetchT id t x) (λ u → F (outAskR (just r) (recOf m r) (fetchR t′ x (proj₂ u))))
         ≡ E (fetchT id t′ x) (λ u′ → F (outAskR (just r) (recOf m r) u′))
  redR F = aux (lookupPt t′ x) refl
    where
    Rout : Tbl × Dig → ℚ
    Rout u′ = F (outAskR (just r) (recOf m r) u′)

    aux : (o : Maybe Dig) → lookupPt t′ x ≡ o
        → E (fetchT id t x) (λ u → Rout (fetchR t′ x (proj₂ u)))
          ≡ E (fetchT id t′ x) Rout
    aux (just d) eq′ =
      trans (trans (lookupᴰℚ-cong-P (entries (fetchT id t x))
                     (λ u → cong Rout (fetchR-hit t′ x d (proj₂ u) eq′)))
                   (E-const (fetchT id t x) (Rout (t′ , d))))
            (sym (trans (cong (λ ν → E ν Rout) (fetchT-hit id t′ x d eq′))
                        (lookupᴰℚ-return (t′ , d) Rout)))
    aux nothing eq′ =
      trans (trans (cong (λ ν → E ν (λ u → Rout (fetchR t′ x (proj₂ u))))
                         (fetchT-miss id t x (tblAt-miss m r t x (trans (sym (tbl x)) eq′))))
            (trans (lookupᴰℚ-Dmap (λ h → (x , h) ∷ t , h) (uniform-Vec k)
                     (λ u → Rout (fetchR t′ x (proj₂ u))))
                   (lookupᴰℚ-cong-P (entries (uniform-Vec k))
                     (λ h → cong Rout (fetchR-miss t′ x h eq′)))))
            (sym (trans (cong (λ ν → E ν Rout) (fetchT-miss id t′ x eq′))
                        (lookupᴰℚ-Dmap (λ h → (x , h) ∷ t′ , h) (uniform-Vec k) Rout)))

  mgR : ∀ F → E νa (λ p → F (proj₂ p)) ≡ E (askR (just r , t′ , recOf m r) x) F
  mgR F = trans (E-bind₂ (fetchT id t x) (uniform-Vec k) κa (λ p → F (proj₂ p)))
         (trans (lookupᴰℚ-cong-P (entries (fetchT id t x))
                  (λ u → E-const (uniform-Vec k)
                           (F (outAskR (just r) (recOf m r) (fetchR t′ x (proj₂ u))))))
         (trans (redR F) (sym (ask-redᴿ (just r) t′ (recOf m r) x F))))

  stp : (u : Tbl × Dig) (ρ : Dig)
      → (proj₁ u ≡ t × lookupPt t x ≡ just (proj₂ u))
      ⊎ (proj₁ u ≡ (x , proj₂ u) ∷ t × lookupPt t x ≡ nothing)
      → (false ∨ (hitAt m x ρ ∨ guessAt m r x) ≡ true)
      ⊎ ( ((r , proj₁ u , m , false ∨ (hitAt m x ρ ∨ guessAt m r x))
             ≋J (just r , proj₁ (fetchR t′ x (proj₂ u)) , recOf m r))
        × (ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u))
             ≡ ansRʰ (proj₂ (fetchR t′ x (proj₂ u)))) )
  stp u ρ us with hitAt m x ρ in eqh | guessAt m r x in eqg
  ... | true  | _    = inj₁ refl
  ... | false | true = inj₁ refl
  ... | false | false = inj₂ (good us)
    where
    good : (proj₁ u ≡ t × lookupPt t x ≡ just (proj₂ u))
         ⊎ (proj₁ u ≡ (x , proj₂ u) ∷ t × lookupPt t x ≡ nothing)
         → ((r , proj₁ u , m , false) ≋J (just r , proj₁ (fetchR t′ x (proj₂ u)) , recOf m r))
           × (ansRʰ (proj₂ u) ≡ ansRʰ (proj₂ (fetchR t′ x (proj₂ u))))
    good (inj₁ (pu , hit))
      rewrite pu
            | fetchR-hit t′ x (proj₂ u) (proj₂ u)
                (trans (same-at m r t t′ x tbl eqg) hit) = (refl , refl , refl , tbl , frs) , refl
    good (inj₂ (pu , miss))
      rewrite pu
            | fetchR-miss t′ x (proj₂ u) (trans (same-at m r t t′ x tbl eqg) miss) =
      (refl , refl , refl , tbl-∷ m r t t′ x (proj₂ u) tbl eqg
      , fresh-∷ m r t x (proj₂ u) frs eqg) , refl

  sup : OnSupport (λ p → (flagP (proj₁ (proj₁ p)) ≡ true)
                       ⊎ ((proj₁ (proj₁ p) ≋J proj₁ (proj₂ p))
                          × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) νa
  sup = OnSupport-bind (fetchT id t x)
          (λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (κa u ρ)) (fetchT-sup t x) λ u us →
        OnSupport-bind {P = λ _ → ⊤} (uniform-Vec k) (λ ρ → return-ℚ (κa u ρ))
          (os-any (uniform-Vec k)) λ ρ _ → OnSupport-return (stp u ρ us)
join-J (r , t , nothing , f) (mr , t′ , z) (refl , refl , refl , tbl , frs) (comQʰ b) =
  νc , mgL , mgR , sup
  where
  κc : Dig → (StPʰ × Rʰ) × (StRʰ × Rʰ)
  κc c = outComP r t b false c
       , ((just r , (b ∷ᵛ r , c) ∷ t′ , just (c , b , r , false)) , comRʰ c)

  νc = uniform-Vec k >>=ᴹ λ c → return-ℚ (κc c)

  -- the real game's commitment step draws too: its own point is untabulated,
  -- because a query that tabulated it would have named the plant.
  missR : lookupPt t′ (b ∷ᵛ r) ≡ nothing
  missR = trans (tbl (b ∷ᵛ r)) (frs b)

  mgL : ∀ F → E νc (λ p → F (proj₁ p)) ≡ E (comP (r , t , nothing , false) b) F
  mgL F = trans (lookupᴰℚ-Dmap κc (uniform-Vec k) (λ p → F (proj₁ p)))
                (sym (lookupᴰℚ-Dmap (outComP r t b false) (uniform-Vec k) F))

  mgR : ∀ F → E νc (λ p → F (proj₂ p)) ≡ E (comR (just r , t′ , nothing) b) F
  mgR F = trans (lookupᴰℚ-Dmap κc (uniform-Vec k) (λ p → F (proj₂ p)))
          (sym (trans (lookupᴰℚ-Dmap (outComR r b) (fetchT id t′ (b ∷ᵛ r)) F)
               (trans (cong (λ ν → E ν (λ u → F (outComR r b u)))
                            (fetchT-miss id t′ (b ∷ᵛ r) missR))
                      (lookupᴰℚ-Dmap (λ h → (b ∷ᵛ r , h) ∷ t′ , h) (uniform-Vec k)
                        (λ u → F (outComR r b u))))))

  stp : (c : Dig)
      → ((r , t , just (c , b , false) , false)
           ≋J (just r , (b ∷ᵛ r , c) ∷ t′ , just (c , b , r , false)))
        × (comRʰ c ≡ comRʰ c)
  stp c = (refl , refl , refl , tblc , tt) , refl
    where
    tblc : ∀ y → lookupPt ((b ∷ᵛ r , c) ∷ t′) y ≡ lookupPt ((b ∷ᵛ r , c) ∷ t) y
    tblc y with y ≟ (b ∷ᵛ r)
    ... | yes _ = refl
    ... | no  _ = tbl y

  sup : OnSupport (λ p → (flagP (proj₁ (proj₁ p)) ≡ true)
                       ⊎ ((proj₁ (proj₁ p) ≋J proj₁ (proj₂ p))
                          × (proj₂ (proj₁ p) ≡ proj₂ (proj₂ p)))) νc
  sup = OnSupport-bind {P = λ _ → ⊤} (uniform-Vec k) (λ c → return-ℚ (κc c))
          (os-any (uniform-Vec k)) λ c _ → OnSupport-return (inj₂ (stp c))
join-J (r , t , just mm , f) (mr , t′ , z) (refl , refl , refl , tbl , frs) (comQʰ b) =
  idle-join ((r , t , just mm , false) , idleRʰ)
            ((just r , t′ , recOf (just mm) r) , idleRʰ)
            (refl , refl , refl , tbl , frs) refl
join-J (r , t , just (c , b , false) , f) (mr , t′ , z)
       (refl , refl , refl , tbl , frs) opnQʰ =
  idle-join (outOpnP r t c b false) ((just r , t′ , just (c , b , r , true)) , opnRʰ b r)
            (refl , refl , refl , tbl , tt) refl
join-J (r , t , just (c , b , true) , f) (mr , t′ , z)
       (refl , refl , refl , tbl , frs) opnQʰ =
  idle-join ((r , t , just (c , b , true) , false) , idleRʰ)
            ((just r , t′ , just (c , b , r , true)) , idleRʰ)
            (refl , refl , refl , tbl , frs) refl
join-J (r , t , nothing , f) (mr , t′ , z) (refl , refl , refl , tbl , frs) opnQʰ =
  idle-join ((r , t , nothing , false) , idleRʰ) ((just r , t′ , nothing) , idleRʰ)
            (refl , refl , refl , tbl , frs) refl

------------------------------------------------------------------------
-- The flag's average drift: 2⁻ᵏ for the guess, 2⁻ᵏ for the test

εᴾ : ℚ
εᴾ = inv-pow-2 k +ℚ inv-pow-2 k

-- The families one distinguisher can chase at every plant at once: while the
-- plant is a secret the table, the commitment and the answers are the same
-- whatever it is, and only the flag knows which plant it is running at.
RelP : (Dig → StPʰ) → Set
RelP f = Σ[ t ∈ Tbl ] Σ[ m ∈ Comʰ ] Σ[ φ ∈ (Dig → Bool) ] (∀ r → f r ≡ (r , t , m , φ r))

mono-P : Monotone respPʰ flagP
mono-P (r , t , m , f) (askQʰ x) eq =
  OnSupport-bind {P = λ _ → ⊤} (fetchT id t x)
    (λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskP r m f x u ρ))
    (os-any (fetchT id t x)) λ u _ →
  OnSupport-bind {P = λ _ → ⊤} (uniform-Vec k) (λ ρ → return-ℚ (outAskP r m f x u ρ))
    (os-any (uniform-Vec k)) λ ρ _ → OnSupport-return (cong (_∨ riseAt m r x ρ) eq)
mono-P (r , t , nothing , f) (comQʰ b) eq =
  OnSupport-bind {P = λ _ → ⊤} (uniform-Vec k) (λ c → return-ℚ (outComP r t b f c))
    (os-any (uniform-Vec k)) λ c _ → OnSupport-return eq
mono-P (r , t , just mm , f) (comQʰ b) eq = OnSupport-return eq
mono-P (r , t , just (c , b , false) , f) opnQʰ eq = OnSupport-return eq
mono-P (r , t , just (c , b , true) , f) opnQʰ eq = OnSupport-return eq
mono-P (r , t , nothing , f) opnQʰ eq = OnSupport-return eq

frozen-P : Frozen respPʰ flagP Opened
frozen-P (r , t , just (c , b , true) , f) (askQʰ x) _ =
  OnSupport-bind {P = λ _ → ⊤} (fetchT id t x)
    (λ u → uniform-Vec k >>=ᴹ λ ρ → return-ℚ (outAskP r (just (c , b , true)) f x u ρ))
    (os-any (fetchT id t x)) λ u _ →
  OnSupport-bind {P = λ _ → ⊤} (uniform-Vec k)
    (λ ρ → return-ℚ (outAskP r (just (c , b , true)) f x u ρ))
    (os-any (uniform-Vec k)) λ ρ _ → OnSupport-return (tt , ∨-identityʳ f)
frozen-P (r , t , just (c , b , true) , f) (comQʰ b′) _ = OnSupport-return (tt , refl)
frozen-P (r , t , just (c , b , true) , f) opnQʰ      _ = OnSupport-return (tt , refl)

private
  0≤εᴾ : 0ℚ ≤ℚ εᴾ
  0≤εᴾ = ≤-trans (≤-reflexive (sym (+-identityʳ 0ℚ)))
                 (+-mono-≤ (0≤inv-pow-2 k) (0≤inv-pow-2 k))

  pull-B : {A : Set} (ν : Dist-ℚ A) (Y : A → ℚ) (B : ℚ)
         → E ν (λ a → Y a +ℚ B) ≡ E ν Y +ℚ B
  pull-B ν Y B = trans (E-add ν Y (λ _ → B)) (cong (E ν Y +ℚ_) (E-const ν B))

  -- a fresh uniform draw tested against one point, behind a gate
  ∧-mass : (a : Bool) (p : Dig)
         → E (uniform-Vec k) (λ ρ → bool→ℚ (a ∧ ⌊ ρ ≟ p ⌋)) ≤ℚ inv-pow-2 k
  ∧-mass true  p = ≤-reflexive (P-uniform-Vec k p)
  ∧-mass false p = ≤-trans (≤-reflexive (E-const (uniform-Vec k) 0ℚ)) (0≤inv-pow-2 k)

  hit-mass : (m : Comʰ) (x : Pt)
           → E (uniform-Vec k) (λ ρ → bool→ℚ (hitAt m x ρ)) ≤ℚ inv-pow-2 k
  hit-mass (just (_ , b , false)) x = ∧-mass ⌊ head x ≟ b ⌋ (tail x)
  hit-mass (just (_ , _ , true))  x = ∧-mass false (tail x)
  hit-mass nothing                x = ∧-mass false (tail x)

  -- …and the plant, which is where the average does the work the state
  -- cannot: at a FIXED plant this is 1 for the query that names it.
  guess-mass : (m : Comʰ) (x : Pt)
             → E (uniform-Vec k) (λ r → bool→ℚ (guessAt m r x)) ≤ℚ inv-pow-2 k
  guess-mass (just (_ , _ , false)) x = ≤-reflexive (P-uniform-Vec k (tail x))
  guess-mass nothing                x = ≤-reflexive (P-uniform-Vec k (tail x))
  guess-mass (just (_ , _ , true))  x =
    ≤-trans (≤-reflexive (E-const (uniform-Vec k) 0ℚ)) (0≤inv-pow-2 k)

  inner-drift : (m : Comʰ) (φ : Dig → Bool) (x : Pt) (ρ : Dig)
              → E (uniform-Vec k) (λ r → bool→ℚ (φ r ∨ riseAt m r x ρ))
                ≤ℚ E (uniform-Vec k) (λ r → bool→ℚ (φ r))
                   +ℚ (bool→ℚ (hitAt m x ρ) +ℚ inv-pow-2 k)
  inner-drift m φ x ρ = ≤-trans
    (E-mono (uniform-Vec k) (λ r → bool→ℚ (φ r ∨ riseAt m r x ρ))
            (λ r → bool→ℚ (φ r) +ℚ (bool→ℚ (hitAt m x ρ) +ℚ bool→ℚ (guessAt m r x)))
            (λ r → ≤-trans (∨-≤ (φ r) (riseAt m r x ρ))
                     (+-monoʳ-≤ (bool→ℚ (φ r)) (∨-≤ (hitAt m x ρ) (guessAt m r x)))))
    (≤-trans
      (≤-reflexive (trans
        (E-add (uniform-Vec k) (λ r → bool→ℚ (φ r))
               (λ r → bool→ℚ (hitAt m x ρ) +ℚ bool→ℚ (guessAt m r x)))
        (cong (E (uniform-Vec k) (λ r → bool→ℚ (φ r)) +ℚ_)
          (trans (E-add (uniform-Vec k) (λ _ → bool→ℚ (hitAt m x ρ))
                        (λ r → bool→ℚ (guessAt m r x)))
                 (cong (_+ℚ E (uniform-Vec k) (λ r → bool→ℚ (guessAt m r x)))
                       (E-const (uniform-Vec k) (bool→ℚ (hitAt m x ρ))))))))
      (+-monoʳ-≤ (E (uniform-Vec k) (λ r → bool→ℚ (φ r)))
                 (+-monoʳ-≤ (bool→ℚ (hitAt m x ρ)) (guess-mass m x))))

  rise-drift : (t : Tbl) (m : Comʰ) (φ : Dig → Bool) (x : Pt)
             → E (fetchT id t x) (λ u → E (uniform-Vec k) (λ ρ →
                 E (uniform-Vec k) (λ r → bool→ℚ (φ r ∨ riseAt m r x ρ))))
               ≤ℚ E (uniform-Vec k) (λ r → bool→ℚ (φ r)) +ℚ εᴾ
  rise-drift t m φ x = ≤-trans
    (≤-reflexive (E-const (fetchT id t x)
      (E (uniform-Vec k) (λ ρ → E (uniform-Vec k) (λ r → bool→ℚ (φ r ∨ riseAt m r x ρ))))))
    (≤-trans
      (E-mono (uniform-Vec k)
        (λ ρ → E (uniform-Vec k) (λ r → bool→ℚ (φ r ∨ riseAt m r x ρ)))
        (λ ρ → Φ +ℚ (bool→ℚ (hitAt m x ρ) +ℚ inv-pow-2 k)) (inner-drift m φ x))
      (≤-trans
        (≤-reflexive (trans
          (E-add (uniform-Vec k) (λ _ → Φ)
                 (λ ρ → bool→ℚ (hitAt m x ρ) +ℚ inv-pow-2 k))
          (cong₂ _+ℚ_ (E-const (uniform-Vec k) Φ)
            (trans (E-add (uniform-Vec k) (λ ρ → bool→ℚ (hitAt m x ρ))
                          (λ _ → inv-pow-2 k))
                   (cong (E (uniform-Vec k) (λ ρ → bool→ℚ (hitAt m x ρ)) +ℚ_)
                         (E-const (uniform-Vec k) (inv-pow-2 k)))))))
        (+-monoʳ-≤ Φ (+-monoˡ-≤ (inv-pow-2 k) (hit-mass m x)))))
    where Φ = E (uniform-Vec k) (λ r → bool→ℚ (φ r))

  -- an activation the flag cannot rise at still has to fit the budget
  idle-drift : (f : Dig → StPʰ) (φ : Dig → Bool) → (∀ r → flagP (f r) ≡ φ r)
             → (X B : ℚ) → X ≤ℚ E (uniform-Vec k) (λ r → bool→ℚ (φ r)) +ℚ B
             → X ≤ℚ (E (uniform-Vec k) (λ r → bool→ℚ (flagP (f r))) +ℚ εᴾ) +ℚ B
  idle-drift f φ fl X B le = ≤-trans le
    (+-monoˡ-≤ B (≤-trans
      (≤-reflexive (lookupᴰℚ-cong-P (entries (uniform-Vec k)) (λ r → cong bool→ℚ (sym (fl r)))))
      (≤-trans (≤-reflexive (sym (+-identityʳ _)))
               (+-monoʳ-≤ (E (uniform-Vec k) (λ r → bool→ℚ (flagP (f r)))) 0≤εᴾ))))

drift-P : AvgDrift (uniform-Vec k) respPʰ flagP RelP Opened εᴾ
drift-P f (askQʰ x) (t , m , φ , ff) F B cont =
  ≤-trans (≤-reflexive expand) (≤-trans bounded (≤-trans (≤-reflexive collect) final))
  where
  Rise : Dig → Dig → ℚ
  Rise ρ r = bool→ℚ (φ r ∨ riseAt m r x ρ)

  Val Bnd : Tbl × Dig → ℚ
  Val u = E (uniform-Vec k) (λ ρ → E (uniform-Vec k) (λ r → F r (outAskP r m (φ r) x u ρ)))
  Bnd u = E (uniform-Vec k) (λ ρ → E (uniform-Vec k) (Rise ρ) +ℚ B)

  expand : E (uniform-Vec k) (λ r → E (respPʰ (f r) (askQʰ x)) (F r))
         ≡ E (fetchT id t x) Val
  expand = trans
    (lookupᴰℚ-cong-P (entries (uniform-Vec k))
      (λ r → trans (cong (λ z → E (respPʰ z (askQʰ x)) (F r)) (ff r))
                   (ask-redᴾ r t m (φ r) x (F r))))
    (trans (E-swap (uniform-Vec k) (fetchT id t x)
             (λ r u → E (uniform-Vec k) (λ ρ → F r (outAskP r m (φ r) x u ρ))))
           (lookupᴰℚ-cong-P (entries (fetchT id t x))
             (λ u → E-swap (uniform-Vec k) (uniform-Vec k)
                      (λ r ρ → F r (outAskP r m (φ r) x u ρ)))))

  bounded : E (fetchT id t x) Val ≤ℚ E (fetchT id t x) Bnd
  bounded = E-mono (fetchT id t x) Val Bnd λ u →
    E-mono (uniform-Vec k)
      (λ ρ → E (uniform-Vec k) (λ r → F r (outAskP r m (φ r) x u ρ)))
      (λ ρ → E (uniform-Vec k) (Rise ρ) +ℚ B)
      λ ρ → cont (λ r → outAskP r m (φ r) x u ρ)
              (inj₁ ( ansRʰ (cond (hitAt m x ρ) (pinAt m (proj₂ u)) (proj₂ u))
                    , (proj₁ u , m , (λ r → φ r ∨ riseAt m r x ρ) , (λ r → refl))
                    , (λ r → refl) ))

  collect : E (fetchT id t x) Bnd
          ≡ E (fetchT id t x) (λ u → E (uniform-Vec k) (λ ρ → E (uniform-Vec k) (Rise ρ)))
            +ℚ B
  collect = trans
    (lookupᴰℚ-cong-P (entries (fetchT id t x))
      (λ u → pull-B (uniform-Vec k) (λ ρ → E (uniform-Vec k) (Rise ρ)) B))
    (pull-B (fetchT id t x)
      (λ u → E (uniform-Vec k) (λ ρ → E (uniform-Vec k) (Rise ρ))) B)

  final : E (fetchT id t x) (λ u → E (uniform-Vec k) (λ ρ → E (uniform-Vec k) (Rise ρ)))
            +ℚ B
        ≤ℚ (E (uniform-Vec k) (λ r → bool→ℚ (flagP (f r))) +ℚ εᴾ) +ℚ B
  final = +-monoˡ-≤ B (≤-trans (rise-drift t m φ x)
    (+-monoˡ-≤ εᴾ (≤-reflexive (lookupᴰℚ-cong-P (entries (uniform-Vec k))
      (λ r → cong bool→ℚ (sym (cong flagP (ff r))))))))
drift-P f (comQʰ b) (t , nothing , φ , ff) F B cont =
  idle-drift f φ (λ r → cong flagP (ff r)) _ B (≤-trans
    (≤-reflexive (trans
      (lookupᴰℚ-cong-P (entries (uniform-Vec k))
        (λ r → trans (cong (λ z → E (respPʰ z (comQʰ b)) (F r)) (ff r))
                     (lookupᴰℚ-Dmap (outComP r t b (φ r)) (uniform-Vec k) (F r))))
      (E-swap (uniform-Vec k) (uniform-Vec k)
        (λ r c → F r (outComP r t b (φ r) c)))))
    (≤-trans
      (E-mono (uniform-Vec k) (λ c → E (uniform-Vec k) (λ r → F r (outComP r t b (φ r) c)))
        (λ c → E (uniform-Vec k) (λ r → bool→ℚ (φ r)) +ℚ B)
        (λ c → cont (λ r → outComP r t b (φ r) c)
                 (inj₁ ( comRʰ c
                       , (t , just (c , b , false) , φ , (λ r → refl))
                       , (λ r → refl)))))
      (≤-reflexive (E-const (uniform-Vec k)
        (E (uniform-Vec k) (λ r → bool→ℚ (φ r)) +ℚ B)))))
drift-P f (comQʰ b) (t , just mm , φ , ff) F B cont =
  idle-drift f φ (λ r → cong flagP (ff r)) _ B (≤-trans
    (≤-reflexive (lookupᴰℚ-cong-P (entries (uniform-Vec k))
      (λ r → trans (cong (λ z → E (respPʰ z (comQʰ b)) (F r)) (ff r))
                   (lookupᴰℚ-return ((r , t , just mm , φ r) , idleRʰ) (F r)))))
    (cont (λ r → (r , t , just mm , φ r) , idleRʰ)
      (inj₁ (idleRʰ , (t , just mm , φ , (λ r → refl)) , (λ r → refl)))))
drift-P f opnQʰ (t , just (c , b , false) , φ , ff) F B cont =
  idle-drift f φ (λ r → cong flagP (ff r)) _ B (≤-trans
    (≤-reflexive (lookupᴰℚ-cong-P (entries (uniform-Vec k))
      (λ r → trans (cong (λ z → E (respPʰ z opnQʰ) (F r)) (ff r))
                   (lookupᴰℚ-return (outOpnP r t c b (φ r)) (F r)))))
    (cont (λ r → outOpnP r t c b (φ r)) (inj₂ (λ r → tt))))
drift-P f opnQʰ (t , just (c , b , true) , φ , ff) F B cont =
  idle-drift f φ (λ r → cong flagP (ff r)) _ B (≤-trans
    (≤-reflexive (lookupᴰℚ-cong-P (entries (uniform-Vec k))
      (λ r → trans (cong (λ z → E (respPʰ z opnQʰ) (F r)) (ff r))
                   (lookupᴰℚ-return ((r , t , just (c , b , true) , φ r) , idleRʰ) (F r)))))
    (cont (λ r → (r , t , just (c , b , true) , φ r) , idleRʰ)
      (inj₁ (idleRʰ , (t , just (c , b , true) , φ , (λ r → refl)) , (λ r → refl)))))
drift-P f opnQʰ (t , nothing , φ , ff) F B cont =
  idle-drift f φ (λ r → cong flagP (ff r)) _ B (≤-trans
    (≤-reflexive (lookupᴰℚ-cong-P (entries (uniform-Vec k))
      (λ r → trans (cong (λ z → E (respPʰ z opnQʰ) (F r)) (ff r))
                   (lookupᴰℚ-return ((r , t , nothing , φ r) , idleRʰ) (F r)))))
    (cont (λ r → (r , t , nothing , φ r) , idleRʰ)
      (inj₁ (idleRʰ , (t , nothing , φ , (λ r → refl)) , (λ r → refl)))))

------------------------------------------------------------------------
-- The bound

-- Averaged over the plant, the flag is up with probability at most `2m·2⁻ᵏ`
-- after `m` activations — the statement no `SuperCert` can make, since at any
-- one plant the next query hits it with probability 1.
flag-bound : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
           → E (uniform-Vec k) (λ r → badProb respPʰ flagP (sP₀ r) d) ≤ℚ fromℕ m *ℚ εᴾ
flag-bound m d le = ≤-trans
  (badProb-avg (uniform-Vec k) respPʰ flagP RelP Opened εᴾ 0≤εᴾ mono-P frozen-P drift-P
    m d sP₀ le (inj₁ ([] , nothing , (λ _ → false) , (λ r → refl))))
  (≤-reflexive (trans (cong (_+ℚ fromℕ m *ℚ εᴾ) (E-const (uniform-Vec k) 0ℚ))
                      (+-identityˡ (fromℕ m *ℚ εᴾ))))

per-plant : (d : Strat Qʰ Rʰ) (r : Dig)
          → ∣ Pr₁ (runWith respPʰ (sP₀ r) d)
              -ℚ Pr₁ (runWith respRʰ (just r , [] , nothing) d) ∣ℚ
            ≤ℚ badProb respPʰ flagP (sP₀ r) d
per-plant d r = runWith-join respPʰ respRʰ flagP _≋J_ good-J join-J d (sP₀ r)
  (just r , [] , nothing) (refl , refl , refl , (λ y → refl) , (λ b → refl))

-- `2m·2⁻ᵏ`: one `2⁻ᵏ` per activation for the guess at the plant — which the
-- commitment step's own divergence is already paid for by — and one for the
-- deferred game's fresh test.
defer-hiding : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
             → ∣ Pr₁ (runWith respLʰ sL₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
               ≤ℚ fromℕ (m + m) *ℚ inv-pow-2 k
defer-hiding m d le = ≤-trans
  (≤-trans
    (≤-reflexive (cong₂ (λ a b → ∣ a -ℚ b ∣ℚ) (sym (defer-hop d)) (sym (defer-commit d))))
    (≤-trans (E-abs-diff (uniform-Vec k) PrP PrR)
             (E-mono (uniform-Vec k) (λ r → ∣ PrP r -ℚ PrR r ∣ℚ)
                     (λ r → badProb respPʰ flagP (sP₀ r) d) (per-plant d))))
  (≤-trans (flag-bound m d le) (≤-reflexive (sym (split m))))
  where
  PrP PrR : Dig → ℚ
  PrP r = Pr₁ (runWith respPʰ (sP₀ r) d)
  PrR r = Pr₁ (runWith respRʰ (just r , [] , nothing) d)

  split : (n : ℕ) → fromℕ (n + n) *ℚ inv-pow-2 k ≡ fromℕ n *ℚ εᴾ
  split n = trans (cong (_*ℚ inv-pow-2 k) (fromℕ-+ n n))
                  (trans (*-distribʳ-+ (inv-pow-2 k) (fromℕ n) (fromℕ n))
                         (sym (*-distribˡ-+ (fromℕ n) (inv-pow-2 k) (inv-pow-2 k))))

-- …and the statement `Game.hiding-bound-defer` was stated to take: `F_com`
-- with the programming simulator is within `3m·2⁻ᵏ` of the protocol that
-- draws its opening randomness at the commitment.
hiding-bound-total : (m : ℕ) (d : Strat Qʰ Rʰ) → asks≤ m d
                   → ∣ Pr₁ (runWith respIʰ sI₀ d) -ℚ Pr₁ (runWith respRʰ sR₀ d) ∣ℚ
                     ≤ℚ εᴸ m +ℚ fromℕ (m + m) *ℚ inv-pow-2 k
hiding-bound-total = hiding-bound-defer defer-hiding
