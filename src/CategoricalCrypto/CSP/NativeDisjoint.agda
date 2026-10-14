{-# OPTIONS --safe --without-K --guardedness #-}

-- Injective renameMap fragment of CSP/Rename.agda:179–195 at
-- agda-cardano-common 9a40d1de330f376c3a102e7c9f1282f4fa830a7e.
-- Boolean namespaces have a per-box left inverse; there is no relational fan-in
-- and hence no renaming commitment. Local branch indices remain arbitrary.
module CategoricalCrypto.CSP.NativeDisjoint (X B : Set) where

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Bool.Base
open import Data.Empty
open import Data.Maybe.Base
open import Data.Product.Base
open import Data.Sum.Base
open import Data.Unit.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

open import CategoricalCrypto.CSP.Interface ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Network ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Operational ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Plugging ⊤ (λ _ → X)
open import CategoricalCrypto.CSP.Separation ⊤ (λ _ → X)
import CategoricalCrypto.CSP.Confinement as Confinement
import CategoricalCrypto.CSP.NativeCorrespondence as Common
import CategoricalCrypto.CSP.NativeOperators as Operators
import CategoricalCrypto.CSP.NativeParallel as Parallel
import CategoricalCrypto.CSP.Process as Core
import CategoricalCrypto.CSP.SingleBox as Single

module O = Operators (Bool × X) B (λ _ → false)
module G = Core (Bool × X) O.Index ⊤
module L = Core (⊤ × X) O.Index ⊤
module P = Parallel (Bool × X) B (λ _ → false)
module C = Confinement (Bool × X) O.Index ⊤
module U = Common X B
open G.Tree
open L.Tree renaming (force to local-force)

mutual
  rename-map : Bool → Maybe L.Tree → Maybe G.Tree
  rename-map side nothing = nothing
  rename-map side (just p′) = just (Rename side p′)

  rename-visible : Bool → (⊤ × X → Maybe L.Tree) → Bool × X → Maybe G.Tree
  rename-visible false v (false , x) = rename-map false (v (tt , x))
  rename-visible false v (true , x) = nothing
  rename-visible true v (false , x) = nothing
  rename-visible true v (true , x) = rename-map true (v (tt , x))

  rename-force : Bool → L.Node → G.Node
  rename-force side (L.ret tt) = G.ret tt
  rename-force side (L.sil p′) = G.sil (Rename side p′)
  rename-force side (L.react v b) = G.react (rename-visible side v) (λ i → rename-map side (b i))

  Rename : Bool → L.Tree → G.Tree
  force (Rename side p) = rename-force side (local-force p)

localV : L.Node → ⊤ × X → Maybe L.Tree
localV (L.react v _) = v
localV _ _ = nothing

localT : L.Node → O.Index → Maybe L.Tree
localT (L.react _ b) = b
localT (L.sil p) O.silence = just p
localT (L.sil _) _ = nothing
localT (L.ret _) _ = nothing

local-silent-view : ∀ {p p′} → L._─[_]→_ p L.τ p′ → Σ O.Index (λ i → localT (local-force p) i ≡ just p′)
local-silent-view (L.sSil eq) = O.silence , cong (λ n → localT n O.silence) eq
local-silent-view (L.sTau {i = i} eq offered) = i , trans (cong (λ n → localT n i) eq) offered

local-view-silent-node : ∀ {p p′ i} n → local-force p ≡ n → localT n i ≡ just p′ → L._─[_]→_ p L.τ p′
local-view-silent-node (L.ret tt) eq ()
local-view-silent-node {i = O.silence} (L.sil r) eq refl = L.sSil eq
local-view-silent-node {i = O.raw _} (L.sil r) eq ()
local-view-silent-node {i = O.left _} (L.sil r) eq ()
local-view-silent-node {i = O.right _} (L.sil r) eq ()
local-view-silent-node {i = O.commitment _} (L.sil r) eq ()
local-view-silent-node {i = O.concealed _} (L.sil r) eq ()
local-view-silent-node (L.react v b) eq offered = L.sTau eq offered

rename-node-silent : ∀ side n i p′ → localT n i ≡ just p′
  → Σ O.Index (λ j → O.viewT (rename-force side n) j ≡ just (Rename side p′))
rename-node-silent side (L.ret tt) i p′ ()
rename-node-silent side (L.sil r) O.silence .r refl = O.silence , refl
rename-node-silent side (L.sil r) (O.raw _) p′ ()
rename-node-silent side (L.sil r) (O.left _) p′ ()
rename-node-silent side (L.sil r) (O.right _) p′ ()
rename-node-silent side (L.sil r) (O.commitment _) p′ ()
rename-node-silent side (L.sil r) (O.concealed _) p′ ()
rename-node-silent side (L.react v b) i p′ offered = i , cong (rename-map side) offered

rename-silent : ∀ side {p p′} → L._─[_]→_ p L.τ p′ → G._─[_]→_ (Rename side p) G.τ (Rename side p′)
rename-silent side {p} {p′} step = lift (local-silent-view step)
  where
  lift : Σ O.Index (λ i → localT (local-force p) i ≡ just p′)
    → G._─[_]→_ (Rename side p) G.τ (Rename side p′)
  lift (i , offered) = P.view-silent-exists (rename-node-silent side (local-force p) i p′ offered)

rename-visible-offer : ∀ side v x {p′} → v (tt , x) ≡ just p′
  → rename-visible side v (side , x) ≡ just (Rename side p′)
rename-visible-offer false v x offered = cong (rename-map false) offered
rename-visible-offer true v x offered = cong (rename-map true) offered

rename-event : ∀ side {p p′} x → L._─[_]→_ p (L.visible (L.event (tt , x))) p′
  → G._─[_]→_ (Rename side p) (G.visible (G.event (side , x))) (Rename side p′)
rename-event side x (L.sVis eq offered) = G.sVis (cong (rename-force side) eq) (rename-visible-offer side _ x offered)

data RenamedSilent (side : Bool) (n : L.Node) : G.Tree → Set where
  renamed-silent : ∀ {i p′} → localT n i ≡ just p′ → RenamedSilent side n (Rename side p′)

rename-map-silent-invert : ∀ side n i m {t} → localT n i ≡ m → rename-map side m ≡ just t → RenamedSilent side n t
rename-map-silent-invert side n i nothing offered ()
rename-map-silent-invert side n i (just p′) offered refl = renamed-silent offered

rename-node-silent-invert : ∀ side n i {t} → O.viewT (rename-force side n) i ≡ just t → RenamedSilent side n t
rename-node-silent-invert side (L.ret tt) i ()
rename-node-silent-invert side (L.sil p′) O.silence refl = renamed-silent {i = O.silence} refl
rename-node-silent-invert side (L.sil p′) (O.raw _) ()
rename-node-silent-invert side (L.sil p′) (O.left _) ()
rename-node-silent-invert side (L.sil p′) (O.right _) ()
rename-node-silent-invert side (L.sil p′) (O.commitment _) ()
rename-node-silent-invert side (L.sil p′) (O.concealed _) ()
rename-node-silent-invert side (L.react v b) i = rename-map-silent-invert side (L.react v b) i (b i) refl

record RenameTau (side : Bool) (p : L.Tree) (t : G.Tree) : Set where
  field next : L.Tree; step : L._─[_]→_ p L.τ next; target : t ≡ Rename side next

rename-silent-invert : ∀ side p {t} → G._─[_]→_ (Rename side p) G.τ t → RenameTau side p t
rename-silent-invert side p step = indexed (P.silent-view step)
  where
  finish : ∀ {t} → RenamedSilent side (local-force p) t → RenameTau side p t
  finish (renamed-silent offered) = record { next = _ ; step = local-view-silent-node (local-force p) refl offered ; target = refl }
  indexed : ∀ {t} → Σ O.Index (λ i → O.viewT (force (Rename side p)) i ≡ just t) → RenameTau side p t
  indexed (i , offered) = finish (rename-node-silent-invert side (local-force p) i offered)

data RenamedEvent (side : Bool) (n : L.Node) : Bool × X → G.Tree → Set where
  renamed-event : ∀ {x p′} → localV n (tt , x) ≡ just p′ → RenamedEvent side n (side , x) (Rename side p′)

rename-map-event-invert : ∀ side n x m {t} → localV n (tt , x) ≡ m → rename-map side m ≡ just t
  → RenamedEvent side n (side , x) t
rename-map-event-invert side n x nothing offered ()
rename-map-event-invert side n x (just p′) offered refl = renamed-event offered

rename-node-event-invert : ∀ side n e {t} → O.viewV (rename-force side n) e ≡ just t → RenamedEvent side n e t
rename-node-event-invert side (L.ret tt) e ()
rename-node-event-invert side (L.sil _) e ()
rename-node-event-invert false (L.react v b) (false , x) = rename-map-event-invert false (L.react v b) x (v (tt , x)) refl
rename-node-event-invert false (L.react v b) (true , x) ()
rename-node-event-invert true (L.react v b) (false , x) ()
rename-node-event-invert true (L.react v b) (true , x) = rename-map-event-invert true (L.react v b) x (v (tt , x)) refl

record RenameVis (side : Bool) (p : L.Tree) (e : Bool × X) (t : G.Tree) : Set where
  field value : X; next : L.Tree; step : L._─[_]→_ p (L.visible (L.event (tt , value))) next
        event-name : e ≡ (side , value); target : t ≡ Rename side next

rename-event-invert : ∀ side p e {t} → G._─[_]→_ (Rename side p) (G.visible (G.event e)) t → RenameVis side p e t
rename-event-invert side p e step = finish (rename-node-event-invert side (local-force p) e (P.visible-view step))
  where
  local-visible : ∀ n {x p′} → local-force p ≡ n → localV n (tt , x) ≡ just p′
    → L._─[_]→_ p (L.visible (L.event (tt , x))) p′
  local-visible (L.ret tt) eq ()
  local-visible (L.sil _) eq ()
  local-visible (L.react v b) eq offered = L.sVis eq offered
  finish : ∀ {e t} → RenamedEvent side (local-force p) e t → RenameVis side p e t
  finish (renamed-event offered) = record
    { value = _ ; next = _ ; step = local-visible (local-force p) refl offered ; event-name = refl ; target = refl }

rename-return-node : ∀ side n → rename-force side n ≡ G.ret tt → n ≡ L.ret tt
rename-return-node side (L.ret tt) eq = refl
rename-return-node side (L.sil _) ()
rename-return-node side (L.react _ _) ()

rename-return : ∀ side p → local-force p ≡ L.ret tt → force (Rename side p) ≡ G.ret tt
rename-return side p ready = cong (rename-force side) ready

confined : ∀ side p → C.OffersOnly (λ e → proj₁ e ≡ side) (Rename side p)
C.OffersOnly.now (confined side p) {e} step = cong proj₁ (RenameVis.event-name (rename-event-invert side p e step))
C.OffersOnly.after (confined side p) {l = G.τ} step = continue (rename-silent-invert side p step)
  where
  continue : ∀ {t} → RenameTau side p t → C.OffersOnly (λ e → proj₁ e ≡ side) t
  continue record { next = p′ ; target = refl } = confined side p′
C.OffersOnly.after (confined side p) {l = G.visible (G.event e)} step = continue (rename-event-invert side p e step)
  where
  continue : ∀ {t} → RenameVis side p e t → C.OffersOnly (λ e → proj₁ e ≡ side) t
  continue record { next = p′ ; target = refl } = confined side p′
C.OffersOnly.after (confined side p) {l = G.visible (G.√ tt)} (G.sRet _) = C.confined-stop _

namespace-disjoint : C.Disjoint (λ e → proj₁ e ≡ false) (λ e → proj₁ e ≡ true)
namespace-disjoint e a b = impossible (trans (sym a) b)
  where impossible : false ≡ true → ⊥
        impossible ()

separated : ∀ p q → C.Sep (λ _ → false) (Rename false p) (Rename true q)
separated p q = C.disjoint-interleaving-separation (confined false p) (confined true q) namespace-disjoint

out : Interface
out = interface singleton (λ _ → port tt output)

module TensorPair (initial-left initial-right : L.Tree) where
  module S = Single ⊤ (λ _ → X)
  left-network = S.Embed.network out O.Index initial-left
  right-network = S.Embed.network out O.Index initial-right
  network = left-network ⊗₁ right-network
  module K = Execution network
  module W = Wiring network
  module D = Disjoint left-network right-network

  first second : K.Box
  first = inj₁ tt
  second = inj₂ tt

  native : W.State → G.Tree
  native q = O.Par (Rename false (q first)) (Rename true (q second))

  data Related : G.Tree → K.Configuration → Set where
    live : ∀ q → Related (native q) (K.running q)
    settled : Related G.stop K.completed

  no-cross : ∀ {n x q r} (g : K.Gather n x q r) → K.Gather.selected g first ≡ just tt
    → K.Gather.selected g second ≡ just tt → ⊥
  no-cross = D.no-cross-participants

  connected-equality : ∀ {u v} → W.Connected u v → u ≡ v
  connected-equality W.same = refl
  connected-equality (W.alias ())
  connected-equality (W.reverse p) = sym (connected-equality p)
  connected-equality (W.join p q) = trans (connected-equality p) (connected-equality q)

  left-name right-name : W.Name
  left-name = K.external-name (inj₂ (inj₁ tt))
  right-name = K.external-name (inj₂ (inj₂ tt))

  module UIP = Decidable⇒UIP U.unit-equality

  payload-eq : ∀ {a b : ⊤} (eq : a ≡ b) x → subst (λ _ → X) eq x ≡ x
  payload-eq eq x = cong (λ z → subst (λ _ → X) z x) (UIP.≡-irrelevant eq refl)

  gather-left : ∀ {q : W.State} x {p′} → L._─[_]→_ (q first) (L.visible (L.event (tt , x))) p′
    → K.Gather left-name x q (K.update first p′ q)
  gather-left {q} x {p′} sp = record
    { selected = λ { (inj₁ tt) → just tt ; (inj₂ tt) → nothing }
    ; incident = λ
        { {inj₁ tt} tt conn → tt , refl
        ; {inj₂ tt} tt conn → ⊥-elim (impossible (connected-equality conn)) }
    ; on-wire = λ { {inj₁ tt} {tt} refl → W.same ; {inj₂ tt} () }
    ; advances = λ { {inj₁ tt} {tt} refl → subst
        (λ y → L._─[_]→_ (q first) (L.visible (L.event (tt , y))) p′)
        (sym (payload-eq (sym (K.class-payload {kp = first , tt} W.same)) x)) sp
      ; {inj₂ tt} () }
    ; absent = λ { {inj₁ tt} () ; {inj₂ tt} _ → refl }
    ; inhabited = first , tt , refl }
    where
    impossible : right-name ≡ left-name → ⊥
    impossible ()

  gather-right : ∀ {q : W.State} x {p′} → L._─[_]→_ (q second) (L.visible (L.event (tt , x))) p′
    → K.Gather right-name x q (K.update second p′ q)
  gather-right {q} x {p′} sp = record
    { selected = λ { (inj₁ tt) → nothing ; (inj₂ tt) → just tt }
    ; incident = λ
        { {inj₁ tt} tt conn → ⊥-elim (impossible (connected-equality conn))
        ; {inj₂ tt} tt conn → tt , refl }
    ; on-wire = λ { {inj₁ tt} () ; {inj₂ tt} {tt} refl → W.same }
    ; advances = λ { {inj₁ tt} () ; {inj₂ tt} {tt} refl → subst
        (λ y → L._─[_]→_ (q second) (L.visible (L.event (tt , y))) p′)
        (sym (payload-eq (sym (K.class-payload {kp = second , tt} W.same)) x)) sp }
    ; absent = λ { {inj₁ tt} _ → refl ; {inj₂ tt} () }
    ; inhabited = second , tt , refl }
    where
    impossible : left-name ≡ right-name → ⊥
    impossible ()

  left-compatible : ∀ {q x p′ sp} → K.BoundaryCompatible (gather-left {q} x {p′} sp)
  left-compatible = K.output-boundary refl record
    { provider = first , tt , refl , refl
    ; unique-output = λ { {inj₁ tt} _ _ → refl ; {inj₂ tt} () } }

  right-compatible : ∀ {q x p′ sp} → K.BoundaryCompatible (gather-right {q} x {p′} sp)
  right-compatible = K.output-boundary refl record
    { provider = second , tt , refl , refl
    ; unique-output = λ { {inj₁ tt} () ; {inj₂ tt} _ _ → refl } }

  step-label : G.Label → K.Label
  step-label G.τ = K.τ
  step-label (G.visible (G.√ tt)) = K.visible K.√
  step-label (G.visible (G.event (false , x))) = K.visible (K.event (inj₂ (inj₁ tt) , x))
  step-label (G.visible (G.event (true , x))) = K.visible (K.event (inj₂ (inj₂ tt) , x))

  kernel-label : K.Label → G.Label
  kernel-label K.τ = G.τ
  kernel-label (K.visible K.√) = G.visible (G.√ tt)
  kernel-label (K.visible (K.event (inj₁ (inj₁ ()) , _)))
  kernel-label (K.visible (K.event (inj₁ (inj₂ ()) , _)))
  kernel-label (K.visible (K.event (inj₂ (inj₁ tt) , x))) = G.visible (G.event (false , x))
  kernel-label (K.visible (K.event (inj₂ (inj₂ tt) , x))) = G.visible (G.event (true , x))

  native-silent-step : ∀ {q t} → G._─[_]→_ (native q) G.τ t
    → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) K.τ c × Related t c)
  native-silent-step {q} step = invert (P.par-silent-invert step)
    where
    from-left : ∀ {t} → RenameTau false (q first) t
      → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) K.τ c × Related (O.Par t (Rename true (q second))) c)
    from-left record { next = p′ ; step = sp ; target = refl } =
      K.running (K.update first p′ q) , K.internal sp , live (K.update first p′ q)
    from-right : ∀ {t} → RenameTau true (q second) t
      → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) K.τ c × Related (O.Par (Rename false (q first)) t) c)
    from-right record { next = p′ ; step = sp ; target = refl } =
      K.running (K.update second p′ q) , K.internal sp , live (K.update second p′ q)
    invert : ∀ {t} → P.SilentMove (Rename false (q first)) (Rename true (q second)) t
      → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) K.τ c × Related t c)
    invert (P.left-silent sp) = from-left (rename-silent-invert false (q first) sp)
    invert (P.right-silent sp) = from-right (rename-silent-invert true (q second) sp)

  native-event-step : ∀ {q e t} → G._─[_]→_ (native q) (G.visible (G.event e)) t
    → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) (step-label (G.visible (G.event e))) c × Related t c)
  native-event-step {q} {e} step = invert (P.par-visible-invert (separated (q first) (q second)) step)
    where
    from-left : ∀ {e t} → RenameVis false (q first) e t → Σ K.Configuration
      (λ c → K._─[_]→_ (K.running q) (step-label (G.visible (G.event e))) c × Related (O.Par t (Rename true (q second))) c)
    from-left record { value = x ; next = p′ ; step = sp ; event-name = refl ; target = refl } =
      K.running (K.update first p′ q) , K.exterior x (gather-left x sp) left-compatible , live (K.update first p′ q)
    from-right : ∀ {e t} → RenameVis true (q second) e t → Σ K.Configuration
      (λ c → K._─[_]→_ (K.running q) (step-label (G.visible (G.event e))) c × Related (O.Par (Rename false (q first)) t) c)
    from-right record { value = x ; next = p′ ; step = sp ; event-name = refl ; target = refl } =
      K.running (K.update second p′ q) , K.exterior x (gather-right x sp) right-compatible , live (K.update second p′ q)
    invert : ∀ {t} → P.VisibleMove (Rename false (q first)) (Rename true (q second)) e t
      → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) (step-label (G.visible (G.event e))) c × Related t c)
    invert (P.together () _ _)
    invert (P.only-left _ sp) = from-left (rename-event-invert false (q first) e sp)
    invert (P.only-right _ sp) = from-right (rename-event-invert true (q second) e sp)

  native-return-step : ∀ {q t} → G._─[_]→_ (native q) (G.visible (G.√ tt)) t
    → K._─[_]→_ (K.running q) (K.visible K.√) K.completed × Related t K.completed
  native-return-step {q} step = K.finish first ready ,
    subst (λ t → Related t K.completed) (sym (proj₂ (proj₂ result))) settled
    where
    result = P.par-return-invert step
    ready : K.AllRet q
    ready (inj₁ tt) = rename-return-node false (local-force (q first)) (proj₁ result)
    ready (inj₂ tt) = rename-return-node true (local-force (q second)) (proj₁ (proj₂ result))

  native-step : ∀ {q l t} → G._─[_]→_ (native q) l t
    → Σ K.Configuration (λ c → K._─[_]→_ (K.running q) (step-label l) c × Related t c)
  native-step {l = G.τ} = native-silent-step
  native-step {l = G.visible (G.event e)} = native-event-step
  native-step {l = G.visible (G.√ tt)} step = K.completed , native-return-step step

  gather-left-reflect : ∀ {q r x} (g : K.Gather left-name x q r)
    → L._─[_]→_ (q first) (L.visible (L.event (tt , x))) (r first) × r second ≡ q second
  gather-left-reflect {q} {r} {x} g = chosen (K.Gather.incident g {k = first} tt W.same)
    where
    chosen : Σ ⊤ (λ p → K.Gather.selected g first ≡ just p)
      → L._─[_]→_ (q first) (L.visible (L.event (tt , x))) (r first) × r second ≡ q second
    chosen (tt , eq) = subst (λ y → L._─[_]→_ (q first) (L.visible (L.event (tt , y))) (r first))
      (payload-eq (sym (K.class-payload {kp = first , tt} (K.Gather.on-wire g {k = first} {p = tt} eq))) x)
      (K.Gather.advances g {k = first} {p = tt} eq) , absent (K.Gather.selected g second) refl
      where
      absent : (selected : Maybe ⊤) → K.Gather.selected g second ≡ selected → r second ≡ q second
      absent nothing unselected = K.Gather.absent g unselected
      absent (just tt) selected = ⊥-elim (no-cross g eq selected)

  gather-right-reflect : ∀ {q r x} (g : K.Gather right-name x q r)
    → L._─[_]→_ (q second) (L.visible (L.event (tt , x))) (r second) × r first ≡ q first
  gather-right-reflect {q} {r} {x} g = chosen (K.Gather.incident g {k = second} tt W.same)
    where
    chosen : Σ ⊤ (λ p → K.Gather.selected g second ≡ just p)
      → L._─[_]→_ (q second) (L.visible (L.event (tt , x))) (r second) × r first ≡ q first
    chosen (tt , eq) = subst (λ y → L._─[_]→_ (q second) (L.visible (L.event (tt , y))) (r second))
      (payload-eq (sym (K.class-payload {kp = second , tt} (K.Gather.on-wire g {k = second} {p = tt} eq))) x)
      (K.Gather.advances g {k = second} {p = tt} eq) , absent (K.Gather.selected g first) refl
      where
      absent : (selected : Maybe ⊤) → K.Gather.selected g first ≡ selected → r first ≡ q first
      absent nothing unselected = K.Gather.absent g unselected
      absent (just tt) selected = ⊥-elim (no-cross g selected eq)

  right-absent : ∀ p x → O.viewV (force (Rename true p)) (false , x) ≡ nothing
  right-absent p x = node (local-force p)
    where
    node : ∀ n → O.viewV (rename-force true n) (false , x) ≡ nothing
    node (L.ret tt) = refl
    node (L.sil _) = refl
    node (L.react _ _) = refl

  left-absent : ∀ p x → O.viewV (force (Rename false p)) (true , x) ≡ nothing
  left-absent p x = node (local-force p)
    where
    node : ∀ n → O.viewV (rename-force false n) (true , x) ≡ nothing
    node (L.ret tt) = refl
    node (L.sil _) = refl
    node (L.react _ _) = refl

  network-step : ∀ {q kl c} → K._─[_]→_ (K.running q) kl c
    → Σ G.Tree (λ t → G._─[_]→_ (native q) (kernel-label kl) t × Related t c)
  network-step {q} (K.internal {k = inj₁ tt} {t = p′} step) =
    native (K.update first p′ q) , P.par-left-silent (rename-silent false step) , live (K.update first p′ q)
  network-step {q} (K.internal {k = inj₂ tt} {t = p′} step) =
    native (K.update second p′ q) , P.par-right-silent (rename-silent true step) , live (K.update second p′ q)
  network-step (K.exterior {e = inj₁ (inj₁ ())} _ _ _)
  network-step (K.exterior {e = inj₁ (inj₂ ())} _ _ _)
  network-step {q} (K.exterior {q′ = r} {e = inj₂ (inj₁ tt)} x g compatible) =
    native r , subst (λ t → G._─[_]→_ (native q) (G.visible (G.event (false , x))) t)
      (cong (λ z → O.Par (Rename false (r first)) (Rename true z)) (sym (proj₂ reflected)))
      (P.par-left-visible refl (rename-event false x (proj₁ reflected)) (right-absent (q second) x)) , live r
    where reflected = gather-left-reflect g
  network-step {q} (K.exterior {q′ = r} {e = inj₂ (inj₂ tt)} x g compatible) =
    native r , subst (λ t → G._─[_]→_ (native q) (G.visible (G.event (true , x))) t)
      (cong (λ z → O.Par (Rename false z) (Rename true (r second))) (sym (proj₂ reflected)))
      (P.par-right-visible refl (left-absent (q first) x) (rename-event true x (proj₁ reflected))) , live r
    where reflected = gather-right-reflect g
  network-step (K.hidden {n = inj₁ (inj₁ ())} _ _ _ _)
  network-step (K.hidden {n = inj₁ (inj₂ ())} _ _ _ _)
  network-step (K.hidden {n = inj₂ e} x g confined-class handshake) = ⊥-elim (confined-class e W.same)
  network-step {q} (K.finish _ ready) = G.stop ,
    P.par-return (rename-return false (q first) (ready first)) (rename-return true (q second) (ready second)) , settled

  related-native-step : ∀ {p c l t} → Related p c → G._─[_]→_ p l t
    → Σ K.Configuration (λ c′ → K._─[_]→_ c (step-label l) c′ × Related t c′)
  related-native-step (live q) = native-step
  related-native-step settled step = ⊥-elim (G.stop-no-step step)

  related-network-step : ∀ {p c kl c′} → Related p c → K._─[_]→_ c kl c′
    → Σ G.Tree (λ t → G._─[_]→_ p (kernel-label kl) t × Related t c′)
  related-network-step (live q) = network-step
  related-network-step settled step = ⊥-elim (K.completed-no-step step)

  record Bisim (p : G.Tree) (c : K.Configuration) : Set where
    coinductive
    field
      forward : ∀ {l t} → G._─[_]→_ p l t → Σ K.Configuration
        (λ c′ → K._─[_]→_ c (step-label l) c′ × Bisim t c′)
      backward : ∀ {kl c′} → K._─[_]→_ c kl c′ → Σ G.Tree
        (λ t → G._─[_]→_ p (kernel-label kl) t × Bisim t c′)

  correspondence : ∀ {p c} → Related p c → Bisim p c
  Bisim.forward (correspondence related) step = continue (related-native-step related step)
    where
    continue : ∀ {c l t} → Σ K.Configuration (λ c′ → K._─[_]→_ c (step-label l) c′ × Related t c′)
      → Σ K.Configuration (λ c′ → K._─[_]→_ c (step-label l) c′ × Bisim t c′)
    continue (c′ , sp , next) = c′ , sp , correspondence next
  Bisim.backward (correspondence related) step = continue (related-network-step related step)
    where
    continue : ∀ {p kl c′} → Σ G.Tree (λ t → G._─[_]→_ p (kernel-label kl) t × Related t c′)
      → Σ G.Tree (λ t → G._─[_]→_ p (kernel-label kl) t × Bisim t c′)
    continue (t , sp , next) = t , sp , correspondence next

  initial-correspondence : Bisim (native W.initial-state) K.initial-configuration
  initial-correspondence = correspondence (live W.initial-state)

  mutual
    native-divergence : ∀ {p c} → Related p c → G.Diverges p → K.Diverges c
    native-divergence related d = native-tail
      (related-native-step related (G.Diverges.step d)) (G.Diverges.rest d)

    native-tail : ∀ {c t} → Σ K.Configuration
      (λ c′ → K._─[_]→_ c K.τ c′ × Related t c′) → G.Diverges t → K.Diverges c
    K.Diverges.next (native-tail (c′ , sp , next) d) = c′
    K.Diverges.step (native-tail (c′ , sp , next) d) = sp
    K.Diverges.rest (native-tail (c′ , sp , next) d) = native-divergence next d

  mutual
    network-divergence : ∀ {p c} → Related p c → K.Diverges c → G.Diverges p
    network-divergence related d = network-tail
      (related-network-step related (K.Diverges.step d)) (K.Diverges.rest d)

    network-tail : ∀ {p c′} → Σ G.Tree
      (λ t → G._─[_]→_ p G.τ t × Related t c′) → K.Diverges c′ → G.Diverges p
    G.Diverges.next (network-tail (t , sp , next) d) = t
    G.Diverges.step (network-tail (t , sp , next) d) = sp
    G.Diverges.rest (network-tail (t , sp , next) d) = network-divergence next d
