{-# OPTIONS --safe --without-K --guardedness #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module CategoricalCrypto.CSP.SemanticInvariance (Sort : Set) (Payload : Sort → Set)
  (Sort-≟ : DecidableEquality Sort) where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Empty
open import Data.Maybe.Base hiding (map)
open import Data.Product.Base hiding (map)
open import Data.Sum.Base hiding (map)
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import CategoricalCrypto.CSP.ClassTransport Sort Payload
open import CategoricalCrypto.CSP.Coherence Sort Payload Sort-≟
open import CategoricalCrypto.CSP.ComponentTransport Sort Payload
open import CategoricalCrypto.CSP.Interface Sort Payload
open import CategoricalCrypto.CSP.Network Sort Payload
open import CategoricalCrypto.CSP.Observation Sort Payload
open import CategoricalCrypto.CSP.Operational Sort Payload
open import CategoricalCrypto.CSP.Structure Sort Payload
open import CategoricalCrypto.CSP.Transport Sort Payload

open Interface
open Component
open Port

module Derived {A B : Interface} {F G : Network A B} (iso : F ≅ G) where
  module I = _≅_ iso
  module P = Embedding I.forward
  module Q = Embedding I.backward
  module EF = Execution F
  module EG = Execution G
  module WF = Wiring F
  module WG = Wiring G
  module C = Classes iso

  f : EF.Box → EG.Box
  f = P.box-map

  g : EG.Box → EF.Box
  g = Q.box-map

  cf : EF.Box → Component
  cf = Boxes.label (Network.components F)

  cg : EG.Box → Component
  cg = Boxes.label (Network.components G)

  path : ∀ j → cf (g j) ≡ cg j
  path j = trans (P.box-label (g j)) (cong cg (I.boxes-right j))

  map : WF.State → WG.State
  map q j = cast-tree (path j) (q (g j))

  Matches : WF.State → WG.State → Set
  Matches q r = ∀ j → cast-tree (path j) (q (g j)) ≡ r j

  initial-matches : Matches WF.initial-state WG.initial-state
  initial-matches j = cast-initial (path j)

  port-inverse : ∀ {c d} (eq : c ≡ d) p → cast-port eq (cast-port (sym eq) p) ≡ p
  port-inverse refl p = refl

  incidence : ∀ {j p n} → WF.Connected (Network.local-wire F (g j , p)) n
    → WG.Connected (Network.local-wire G (j , cast-port (path j) p)) (P.name-map n)
  incidence {j} {p} {n} conn = subst
    (λ kp → WG.Connected (Network.local-wire G kp) (P.name-map n))
    (port-pair (I.boxes-right j) (P.box-label (g j)) p) (C.forward-incidence conn)
    where
    port-pair : ∀ {i j c} (eq : i ≡ j) (e : c ≡ cg i) p
      → (i , cast-port e p) ≡ (j , cast-port (trans e (cong cg eq)) p)
    port-pair refl e p = cong (λ r → _ , r) (cast-port-coherent _ _ p)

  reflection : ∀ {j p n} → WG.Connected (Network.local-wire G (j , p)) (P.name-map n)
    → WF.Connected (Network.local-wire F (g j , cast-port (sym (path j)) p)) n
  reflection {j} {p} {n} conn = WF.join
    (subst (λ r → WF.Connected (Network.local-wire F (g j , r)) (Q.name-map (P.name-map n)))
      (cast-port-coherent (Q.box-label j) (sym (path j)) p) (C.backward-incidence conn))
    (I.names-left n)

  mapped-ret : ∀ {q r} → Matches q r → EF.AllRet q → EG.AllRet r
  mapped-ret match ready j = subst (λ t → EG.Local.Tree.force {k = j} t ≡ EG.Local.ret {k = j} tt)
    (match j) (cast-ret (path j) (ready (g j)))

  g-injective : ∀ {i j} → g i ≡ g j → i ≡ j
  g-injective {i} {j} eq = trans (sym (I.boxes-right i))
    (trans (cong f eq) (I.boxes-right j))

  module Gathering {n x q q′ r m} (match : Matches q r) (a : EF.Gather n x q q′)
    (bridge : WG.Connected (P.name-map n) m) where
    module S = EF.Gather a

    ty : WF.name-sort n ≡ WG.name-sort m
    ty = trans (P.name-type n) (WG.connected-type bridge)

    selected : (j : EG.Box) → Maybe (EG.LocalPort j)
    selected j = Data.Maybe.Base.map (cast-port (path j)) (S.selected (g j))

    choice : ∀ {j p} → selected j ≡ just p
      → Σ (EF.LocalPort (g j)) (λ s → S.selected (g j) ≡ just s × cast-port (path j) s ≡ p)
    choice {j} eq with S.selected (g j) in chosen
    ... | nothing = ⊥-elim (nothing≢just eq)
      where nothing≢just : ∀ {T : Set} {t : T} → nothing ≢ just t
            nothing≢just ()
    ... | just s = s , refl , just-injective eq
      where just-injective : ∀ {T : Set} {s t : T} → just s ≡ just t → s ≡ t
            just-injective refl = refl

    choose : ∀ {j p} → S.selected (g j) ≡ just p → selected j ≡ just (cast-port (path j) p)
    choose eq = cong (Data.Maybe.Base.map _) eq

    on-wire : ∀ {j p} → selected j ≡ just p → WG.Connected (Network.local-wire G (j , p)) m
    on-wire {j} eq with choice eq
    ... | p , chosen , refl = WG.join (incidence (S.on-wire chosen)) bridge

    incident : ∀ {j} p → WG.Connected (Network.local-wire G (j , p)) m
      → Σ (EG.LocalPort j) (λ s → selected j ≡ just s)
    incident {j} p conn with S.incident (cast-port (sym (path j)) p)
      (reflection (WG.join conn (WG.reverse bridge)))
    ... | s , chosen = cast-port (path j) s , choose chosen

    advances : ∀ {j p} (chosen : selected j ≡ just p)
      → EG.Local._─[_]→_ j (r j)
        (EG.Local.visible {k = j} (EG.Local.event {k = j}
          (p , subst Payload (sym (EG.class-payload (on-wire chosen))) (subst Payload ty x))))
        (map q′ j)
    advances {j} chosen with choice chosen
    ... | p , source , refl = subst
      (λ value → EG.Local._─[_]→_ j (r j)
        (EG.Local.visible {k = j} (EG.Local.event {k = j} (cast-port (path j) p , value))) (map q′ j))
      payload (subst (λ t → EG.Local._─[_]→_ j t _ _) (match j)
        (cast-offer (path j) (S.advances source)))
      where
      payload : subst Payload (port-sort (path j) p)
          (subst Payload (sym (EF.class-payload (S.on-wire source))) x)
        ≡ subst Payload (sym (EG.class-payload (WG.join (incidence (S.on-wire source)) bridge)))
            (subst Payload ty x)
      payload =
        let a = sym (EF.class-payload (S.on-wire source))
            b = port-sort (path j) p
            c = ty
            d = sym (EG.class-payload (WG.join (incidence (S.on-wire source)) bridge))
        in trans (payload-compose a b x)
          (trans (payload-coherent (trans a b) (trans c d) x) (sym (payload-compose c d x)))

    absent : ∀ {j} → selected j ≡ nothing → map q′ j ≡ r j
    absent {j} eq with S.selected (g j) in chosen
    ... | nothing = trans (cong (cast-tree (path j)) (S.absent chosen)) (match j)
    ... | just p = ⊥-elim (just≢nothing eq)
      where just≢nothing : ∀ {T : Set} {t : T} → just t ≢ nothing
            just≢nothing ()

    lift-choice : ∀ {k} p → S.selected k ≡ just p
      → Σ EG.Box (λ j → Σ (EG.LocalPort j) (λ s → selected j ≡ just s
        × polarity (ports (boundary (cg j)) s) ≡ polarity (ports (boundary (cf k)) p)
        × g j ≡ k))
    lift-choice {k} p chosen = lift-at (f k) (I.boxes-left k) p chosen
      where
      lift-at : ∀ {k} j (eq : g j ≡ k) p → S.selected k ≡ just p
        → Σ EG.Box (λ h → Σ (EG.LocalPort h) (λ s → selected h ≡ just s
          × polarity (ports (boundary (cg h)) s) ≡ polarity (ports (boundary (cf k)) p)
          × g h ≡ k))
      lift-at j refl p chosen = j , cast-port (path j) p , choose chosen ,
        sym (port-polarity (path j) p) , refl

    result : EG.Gather m (subst Payload ty x) r (map q′)
    result = record
      { selected = selected ; incident = incident ; on-wire = on-wire
      ; advances = advances ; absent = absent
      ; inhabited = let k , p , chosen = S.inhabited
                        j , s , target , _ = lift-choice p chosen
                    in j , s , target }

    support : EF.OutputSupport a → EG.OutputSupport result
    support supp =
      let k , p , source , out = EF.OutputSupport.provider supp
          j , s , chosen , pol , inv = lift-choice p source
      in record { provider = j , s , chosen , trans pol out
      ; unique-output = λ { {k = h} ch out →
          let p , source , eq = choice ch
              source-output = trans (port-polarity (path h) p)
                (trans (cong (λ z → polarity (ports (boundary (cg h)) z)) eq) out)
          in g-injective (trans (EF.OutputSupport.unique-output supp source source-output) (sym inv)) } }

    handshake : EF.Handshake a → EG.Handshake result
    handshake hand =
      let k , p , source , inp , distinct = EF.Handshake.listener hand
          j , s , chosen , pol , inv = lift-choice p source
          provider-k , provider-p , provider-source , provider-output =
            EF.OutputSupport.provider (EF.Handshake.output-support hand)
          provider-j , provider-s , provider-chosen , provider-pol , provider-inv =
            lift-choice provider-p provider-source
      in record { output-support = support (EF.Handshake.output-support hand)
      ; listener = j , s , chosen , trans pol inp ,
          (λ eq → distinct (trans (sym inv) (trans (cong g eq) provider-inv))) }

    input-support : (∀ {k p} → S.selected k ≡ just p
      → polarity (ports (boundary (cf k)) p) ≡ input)
      → ∀ {j p} → selected j ≡ just p → polarity (ports (boundary (cg j)) p) ≡ input
    input-support all {j} chosen =
      let p , source , eq = choice chosen
      in trans (sym (cong (λ p → polarity (ports (boundary (cg j)) p)) eq))
        (trans (sym (port-polarity (path j) p)) (all source))

  update-at : ∀ {q k i t} (eq : i ≡ k)
    → EF.update k t q i ≡ cast-tree (cong cf (sym eq)) t
  update-at {k = k} refl with index-equality (Boxes.shape (Network.components F)) k k
  ... | yes eq rewrite Decidable⇒UIP.≡-irrelevant
    (index-equality (Boxes.shape (Network.components F))) eq refl = refl
  ... | no neq = ⊥-elim (neq refl)

  update-away : ∀ {q k i t} → k ≢ i → EF.update k t q i ≡ q i
  update-away {k = k} {i} neq with index-equality (Boxes.shape (Network.components F)) k i
  ... | yes eq = ⊥-elim (neq eq)
  ... | no _ = refl

  internal-tree : ∀ {k} → EF.Local.Tree k → EG.Local.Tree (f k)
  internal-tree {k} t = cast-tree (path (f k)) (cast-tree (cong cf (sym (I.boxes-left k))) t)

  internal-step : ∀ {q r k t} → Matches q r → EF.Local._─[_]→_ k (q k) EF.Local.τ t
    → EG.Local._─[_]→_ (f k) (r (f k)) EG.Local.τ (internal-tree t)
  internal-step {q} {r} {k} {t} match step = subst
    (λ s → EG.Local._─[_]→_ (f k) s EG.Local.τ (internal-tree t)) (match (f k))
    (cast-silent (path (f k)) (at (I.boxes-left k) step))
    where
    at : ∀ {i k t} (eq : i ≡ k) → EF.Local._─[_]→_ k (q k) EF.Local.τ t
      → EF.Local._─[_]→_ i (q i) EF.Local.τ (cast-tree (cong cf (sym eq)) t)
    at refl step = step

  internal-matches : ∀ {q r k t} → Matches q r
    → Matches (EF.update k t q) (EG.update (f k) (internal-tree t) r)
  internal-matches {q} {r} {k} {t} match j
    with index-equality (Boxes.shape (Network.components G)) (f k) j
  ... | yes refl = cong (cast-tree (path (f k))) (update-at (I.boxes-left k))
  ... | no neq = trans (cong (cast-tree (path j)) (update-away source-away)) (match j)
    where
    source-away : k ≢ g j
    source-away eq = neq (trans (cong f eq) (I.boxes-right j))

  data Related : EF.Configuration → EG.Configuration → Set where
    running : ∀ {q r} → Matches q r → Related (EF.running q) (EG.running r)
    completed : Related EF.completed EG.completed

  forward : ∀ {p r p′ l} → Related p r → EF._─[_]→_ p l p′
    → Σ EG.Configuration (λ r′ → EG._─[_]→_ r l r′ × Related p′ r′)
  forward (running match) (EF.internal step) =
    _ , EG.internal (internal-step match step) , running (internal-matches match)
  forward (running {q} {r} match) (EF.exterior {q′ = q′} {e = e} x gather compatible) =
    EG.running (map q′) , subst (λ l → EG._─[_]→_ (EG.running r) (EG.visible (EG.event (e , l))) _)
      payload (EG.exterior (subst Payload T.ty x) T.result (boundary-ok compatible)) , running (λ _ → refl)
    where
    module T = Gathering match gather (P.external e)
    boundary-ok : EF.BoundaryCompatible gather → EG.BoundaryCompatible T.result
    boundary-ok (EF.input-boundary pol all) = EG.input-boundary pol (T.input-support all)
    boundary-ok (EF.output-boundary pol supp) = EG.output-boundary pol (T.support supp)
    payload : subst Payload (EG.external-sort e) (subst Payload T.ty x)
      ≡ subst Payload (EF.external-sort e) x
    payload = trans (payload-compose T.ty (EG.external-sort e) x)
      (payload-coherent (trans T.ty (EG.external-sort e)) (EF.external-sort e) x)
  forward (running {q} {r} match) (EF.hidden {q′ = q′} {n = n} x gather priv hand) =
    EG.running (map q′) , EG.hidden (subst Payload T.ty x) T.result
      (C.private-forward priv) (T.handshake hand) , running (λ _ → refl)
    where module T = Gathering match gather WG.same
  forward (running {q} {r} match) (EF.finish k ready) = EG.completed ,
    EG.finish (f k) (mapped-ret {q = q} {r = r} match ready) , completed

  -- The backward label path need not cancel the forward path on Branch:Set.
  -- Its inverse replaces it only for tree transport; finite port-path
  -- coherence preserves the original incidence proof without Component UIP.
  inverse-embedding : Embedding G F
  inverse-embedding = record
    { box-map = g ; box-label = λ j → sym (path j)
    ; name-map = Q.name-map ; name-type = Q.name-type
    ; connected = Q.connected ; external = Q.external
    ; local = λ j p → subst
        (λ s → WF.Connected (Q.name-map (Network.local-wire G (j , p))) (Network.local-wire F (g j , s)))
        (cast-port-coherent (Q.box-label j) (sym (path j)) p) (Q.local j p) }

  inverse-iso : G ≅ F
  inverse-iso = record
    { forward = inverse-embedding ; backward = I.forward
    ; boxes-left = I.boxes-right ; boxes-right = I.boxes-left
    ; names-left = I.names-right ; names-right = I.names-left }

  inverse-path : ∀ k → cg (f k) ≡ cf k
  inverse-path k = trans (sym (path (f k))) (cong cf (I.boxes-left k))

  unmap : WG.State → WF.State
  unmap r k = cast-tree (inverse-path k) (r (f k))

  inverse-matches : ∀ {q r} → Matches q r → ∀ k → unmap r k ≡ q k
  inverse-matches {q} {r} match k = trans
    (cast-tree-compose (sym (path (f k))) (cong cf (I.boxes-left k)) (r (f k)))
    (trans (cong (cast-tree (cong cf (I.boxes-left k)))
      (trans (cong (cast-tree (sym (path (f k)))) (sym (match (f k))))
        (cast-tree-inverse (path (f k)) (q (g (f k))))))
      (indexed-cast q (I.boxes-left k)))

  map-unmap : ∀ r j → map (unmap r) j ≡ r j
  map-unmap r j rewrite Decidable⇒UIP.≡-irrelevant
    (index-equality (Boxes.shape (Network.components F))) (I.boxes-left (g j)) (cong g (I.boxes-right j))
    = trans (roundtrip (I.boxes-right j) (r (f (g j)))) (indexed-cast r (I.boxes-right j))
    where
    roundtrip : ∀ {i j} (eq : i ≡ j) t
      → cast-tree (path j) (cast-tree (trans (sym (path i)) (cong cf (cong g eq))) t)
        ≡ cast-tree (cong cg eq) t
    roundtrip {i} refl t = trans
      (cong (cast-tree (path i)) (cast-tree-compose (sym (path i)) refl t))
      (cast-tree-inverse′ (path i) t)

  restore-matches : ∀ {q r} → (∀ k → unmap r k ≡ q k) → Matches q r
  restore-matches {q} {r} match j = trans
    (sym (cong (cast-tree (path j)) (match (g j)))) (map-unmap r j)

structural→operational : ∀ {A B} {F G : Network A B} → F ≅ G → OperationalTransport F G
structural→operational iso = record
  { Related = D.Related ; initial = D.running D.initial-matches
  ; forward = D.forward ; backward = backward }
  where
  module D = Derived iso
  module R = Derived D.inverse-iso

  reverse-related : ∀ {p q} → D.Related p q → R.Related q p
  reverse-related (D.running match) = R.running (D.inverse-matches match)
  reverse-related D.completed = R.completed

  restore-related : ∀ {p q} → R.Related q p → D.Related p q
  restore-related (R.running match) = D.running (D.restore-matches match)
  restore-related R.completed = D.completed

  backward : ∀ {p q q′ l} → D.Related p q → R.EF._─[_]→_ q l q′
    → Σ R.EG.Configuration (λ p′ → R.EG._─[_]→_ p l p′ × D.Related p′ q′)
  backward related step =
    let p′ , matched , related′ = R.forward (reverse-related related) step
    in p′ , matched , restore-related related′

observations-respect : ∀ {A B} {F G : Network A B} → F ≅ G → observations F ≈ᴼ observations G
observations-respect iso = record
  { traces = λ xs → S.trace-forward xs , S.trace-backward xs
  ; failures = λ xs refusal → S.failure-forward xs refusal , S.failure-backward xs refusal
  ; divergences = λ xs → S.silent-divergence-forward xs , S.silent-divergence-backward xs }
  where module S = Soundness (structural→operational iso)
