{-# OPTIONS --safe --without-K --guardedness #-}

-- What a closed role circuit observes (docs/uc-setup-symbolic.md §3.5).  A role
-- runs as a `Proc` at the tensor of its atoms' interfaces, and every generator
-- occurrence draws its fresh names from a supply of its own
-- (`Categories.FreeMonoidal.Decorated`), so names are globally fresh exactly
-- when the supplies are injective.  `eval c b`: some injective supply makes the
-- closed run answer `b`.  `treeᵒ` is a transport along the seal's `⊗ᵒ`; at a
-- single atom it is `refl`, so a role on atoms is its `procᵒ` on the nose.

open import CategoricalCrypto.Symbolic.Term

module CategoricalCrypto.Symbolic.Semantics (𝔖 : Signature) (E : EqTheory 𝔖) where

open import Categories.Category.Monoidal
open import Categories.FreeMonoidal
open import Data.Bool.Base
open import Data.Fin.Base
open import Data.List.Base
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.Any
open import Data.Nat.Base
open import Data.Product
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit
open import Function.Base using (_∘′_)
open import Function.Bundles
open import Function.Definitions
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality

open import ProbabilisticLogic.Dp
open import ProbabilisticLogic.Dp.Reasoning

open import CategoricalCrypto.Iface
open import CategoricalCrypto.Machines.Base
open import CategoricalCrypto.Strategy
open import CategoricalCrypto.Symbolic.Fine 𝔖
open import CategoricalCrypto.Symbolic.Role 𝔖
open import CategoricalCrypto.UC.Machine
open import CategoricalCrypto.UC.Machine.Run
open import CategoricalCrypto.UC.Model.Observation
open import CategoricalCrypto.UC.Model.Seal

import Categories.FreeMonoidal.Decorated as Decorated
import CategoricalCrypto.Machines.Core as Core
import CategoricalCrypto.Machines.Sim as Sim
import CategoricalCrypto.UC.Seam.Plug as Plug

private
  module G = MonoidalCategory 𝔾ᵒ
  module MC = Core (𝒱ₚ 0ℓ)
  module S = Sim (𝒱ₚ 0ℓ) (𝒫ₚ 0ℓ)

  variable x y : ObjTerm

open Run E
open Terms 𝔖

------------------------------------------------------------------------
-- Roles as processes

atomᴵ : Atom → Iface
atomᴵ a = alphabet pos a ⇿ alphabet neg a

⟦_⟧ᴵ : ObjTerm → Iface
⟦ x ⟧ᴵ = Alphabet pos x ⇿ Alphabet neg x

⟦v⟧ᵒ : ⟦ Mon ⟧ᵥ
⟦v⟧ᵒ = fromMC 𝔾ᵒ noSymmetric

open FreeObjInterp Mon Atom ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ)

tree≡ : (x : ObjTerm) → UnitFree x → ⟦ x ⟧₀ ≡ ifaceᵒ ⟦ x ⟧ᴵ
tree≡ (x ⊗₀ y) (ux , uy) = trans (cong₂ G._⊗₀_ (tree≡ x ux) (tree≡ y uy)) (⊗ᵒ ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ)
tree≡ (Var _)  _         = refl
tree≡ unit     ()

treeᵒ : UnitFree x → UnitFree y → ifaceᵒ ⟦ x ⟧ᴵ G.⇒ ifaceᵒ ⟦ y ⟧ᴵ → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
treeᵒ {x = x} {y = y} ux uy = subst₂ G._⇒_ (sym (tree≡ x ux)) (sym (tree≡ y uy))

treeᵒ-resp : (ux : UnitFree x) (uy : UnitFree y) {f g : ifaceᵒ ⟦ x ⟧ᴵ G.⇒ ifaceᵒ ⟦ y ⟧ᴵ}
           → f G.≈ g → treeᵒ ux uy f G.≈ treeᵒ ux uy g
treeᵒ-resp {x = x} {y = y} ux uy = go (sym (tree≡ x ux)) (sym (tree≡ y uy))
  where
  go : ∀ {X X′ Y Y′} (p : X ≡ X′) (q : Y ≡ Y′) {f g : X G.⇒ Y}
     → f G.≈ g → subst₂ G._⇒_ p q f G.≈ subst₂ G._⇒_ p q g
  go refl refl e = e

-- Occurrence `κ` names its `j`-th fresh name `(κ , j)` (`Role.Run.exec`).
runᴿ : ℕ → Role x y → Proc ⟦ x ⟧ᴵ ⟦ y ⟧ᴵ
runᴿ {x = x} {y = y} κ p = MC.mk (initˢ (Config (Role.n p) (Role.Γ p)) (init p))
  λ (cfg , m) → returnₚ (map₂ (encode x y) (step κ p cfg (decode x y m)))

-- Programs equal modulo E run as one machine.
runᴿ-≈E : ∀ κ (p : Role x y) {r : Reactions p}
        → (∀ c {k} (i : k ∈ Ins x y) b → ReactE (Role.react p c i b) (r c i b))
        → procᵒ (runᴿ κ p) G.≈ procᵒ (runᴿ κ (record p { react = r }))
runᴿ-≈E {x = x} {y = y} κ p e = ≈ᴹ⇒≈ᵒ (S.≲⇒≈ᴹ (S.mk-cong λ (cfg , m) →
  ≡⇒≈ₚ (cong (returnₚ ∘′ map₂ (encode x y)) (step-≈E κ p e cfg (decode x y m)))))

leafᵒ : UnitFree x × UnitFree y × Role x y → ℕ → ⟦ x ⟧₀ G.⇒ ⟦ y ⟧₀
leafᵒ (ux , uy , p) κ = treeᵒ ux uy (procᵒ (runᴿ κ p))

open Decorated symData ⟦v⟧ᵒ (ifaceᵒ ∘′ atomᴵ) ℕ leafᵒ public

------------------------------------------------------------------------
-- The observation

-- A record, not a `Σ`: unification then compares circuits, where a definition
-- would unfold into `_≈ₚ_`'s rationals at every meta (Setup's presheaf ran out
-- of a 3 GiB heap that way).
record eval (c : HomTerm (Var void) (Var verdict)) (b : Bool) : Set where
  constructor named
  field
    naming : Occ c → ℕ
    fresh  : Injective _≡_ _≡_ naming
    answer : Obs ⟦ c ⟧[ naming ] ≈ₚ returnₚ b

-- A naming of `c′` reads back along the occurrence bijection on the nose; a
-- naming of `c` only up to `from ∘ to` pointwise, which `⟦⟧[]-cong` absorbs.
eval-cong : {c c′ : HomTerm (Var void) (Var verdict)} → c ≈Term c′ → ∀ b → eval c b ⇔ eval c′ b
eval-cong {c} {c′} e b = mk⇔ forth back
  where
  π = proj₁ (⟦⟧[]-resp-≈ e)
  open Inverse π

  forth : eval c b → eval c′ b
  forth (named ι inj o) = named (ι ∘′ from)
    (λ eq → trans (sym (strictlyInverseˡ _)) (trans (cong to (inj eq)) (strictlyInverseˡ _)))
    (obs-resp (G.Equiv.sym (proj₂ (⟦⟧[]-resp-≈ e) (ι ∘′ from)))
     ⟨≈⟩ ≡⇒≈ₚ (cong Obs (⟦⟧[]-cong c λ x → cong ι (strictlyInverseʳ x))) ⟨≈⟩ o)

  back : eval c′ b → eval c b
  back (named ι inj o) = named (ι ∘′ to)
    (λ eq → trans (sym (strictlyInverseʳ _)) (trans (cong from (inj eq)) (strictlyInverseʳ _)))
    (obs-resp (proj₂ (⟦⟧[]-resp-≈ e) ι) ⟨≈⟩ o)

------------------------------------------------------------------------
-- Two roles: a tester draws a fresh name, sends it, and answers `true` once
-- an echo returns it.

private
  module Example (s : Signature.Sort 𝔖) where
    wire : ObjTerm
    wire = Var (port s s)

    echo : Role (Var void) wire
    echo = record
      { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
      ; react = λ where
          zero (here refl) _ → emit zero [] (here refl) (var (here refl))
          zero (there ())  _
      }

    tester : Role wire (Var verdict)
    tester = record
      { n = 1 ; Γ = λ _ → [] ; start = zero ; fresh = refl
      ; react = λ where
          zero (here refl)         _ → emit zero [] (there (here refl)) true
          zero (there (here refl)) _ → new s (emit zero [] (here refl) (var (here refl)))
          zero (there (there ()))  _
      }

    circuit : HomTerm (Var void) (Var verdict)
    circuit = var (tt , tt , tester) ∘ var (tt , tt , echo)

    ι : Occ circuit → ℕ
    ι (inj₁ _) = 0
    ι (inj₂ _) = 1

    ι-injective : Injective _≡_ _≡_ ι
    ι-injective {inj₁ _} {inj₁ _} _ = refl
    ι-injective {inj₂ _} {inj₂ _} _ = refl
    ι-injective {inj₁ _} {inj₂ _} ()
    ι-injective {inj₂ _} {inj₁ _} ()

    K : Proc ⟦ wire ⟧ᴵ Ωᴵ
    K = runᴿ 0 tester

    u : Proc unitᴵ ⟦ wire ⟧ᴵ
    u = runᴿ 1 echo

    module P = Plug.Plugged ⟦ wire ⟧ᴵ K u

    -- After the tick: the tester has sent its first name, canonical; the echo
    -- is untouched.
    sent : MC.obj P.Sᴷ
    sent = config zero [] 1 , config zero [] 0

    query : Tm s
    query = EqTheory.canon E (name (0 , 0))

    _ : eval circuit true
    _ = named ι ι-injective
        ( runᴹ-resp-≈ᴹ {Ωᴵ} (unprocᵒ-∘ {unitᴵ} {⟦ wire ⟧ᴵ} {Ωᴵ} K u) (ask tt out)
        ⟨≈⟩ P.collapse ⟨≈⟩ P.observe
        ⟨≈⟩ bindˣ (P.point-red ⟨≈⟩ >>=ₚ-identityˡ _ _ ⟨≈⟩ >>=ₚ-identityˡ _ _)
        ⟨≈⟩ >>=ₚ-identityˡ _ _
        ⟨≈⟩ bindˣ (>>=ₚ-identityˡ _ _)
        ⟨≈⟩ >>=ₚ-identityˡ _ _
        ⟨≈⟩ bindˣ ( P.loop-pass sent (inj₁ query) _ _ (>>=ₚ-identityˡ _ _)
                  ⟨≈⟩ P.loop-pass sent (inj₂ (EqTheory.canon E query)) _ _ (>>=ₚ-identityˡ _ _))
        ⟨≈⟩ >>=ₚ-identityˡ _ _ )
