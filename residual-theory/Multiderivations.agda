
module Multiderivations where

import Data.List as L
open import Data.Empty
      using (⊥; ⊥-elim)
open import Data.Unit
      using (⊤; tt)
--open import Data.Bool
open import Data.Product
      using (_,_; proj₁; Σ-syntax)
open import Data.Sum
      using (_⊎_)
open import Data.Sum
open import Relation.Nullary
      using (¬_; Dec; yes; no)
open import Relation.Binary.Core
      using (_≡_; refl)

import Relation.Binary.PropositionalEquality as Eq
open Eq
       using (cong)
open Eq.≡-Reasoning
       using (_≡⟨_⟩_; _∎)

open import AxiomaticRewriteSystem
open import SetOfSteps
      using (set-of-steps; ss-ε; ss-∷; ss∈; ss∈?; ss-ε-+/*; _+/*_;
             finitely-branching; finitely-branching-proof)
open import Developments
      using (self-erasure; self-erasure-proof; complete-development-derivation)
open import BoundedDevelopments
      using (bounded-developments; ss-target; complete-development-exists; _/+_;
             set-of-steps-induction)

---- Canonical representation for subsets of a given set of steps

data subset-of-steps {A} {x} : set-of-steps {A} x → Set where
  sub-ε : subset-of-steps ss-ε
  sub-∘ : ∀ {R} {X} → subset-of-steps X → subset-of-steps (ss-∷ R X)
  sub-∙ : ∀ {R} {X} → subset-of-steps X → subset-of-steps (ss-∷ R X)
  
subset-inhabited : ∀ {A} {x} {𝕊 : set-of-steps {A} x}
                 → subset-of-steps 𝕊
                 → Set
subset-inhabited sub-ε     = ⊥
subset-inhabited (sub-∘ s) = subset-inhabited s
subset-inhabited (sub-∙ s) = ⊤

subset-inhabited? : ∀ {A} {x} {𝕊 : set-of-steps {A} x}
                  → (X : subset-of-steps 𝕊)
                  → Dec (subset-inhabited X)
subset-inhabited? sub-ε     = no (λ x → x)
subset-inhabited? (sub-∘ s) = subset-inhabited? s
subset-inhabited? (sub-∙ s) = yes tt

subset-inhabited-is-prop : ∀ {A} {x} {𝕊 : set-of-steps {A} x}
                         → {M : subset-of-steps 𝕊}
                         → {p q : subset-inhabited M}
                         → p ≡ q
subset-inhabited-is-prop {M = sub-∘ M} = subset-inhabited-is-prop {M = M}
subset-inhabited-is-prop {M = sub-∙ M} {tt} {tt} = refl

subset-to-set : ∀ {A} {x} {𝕊 : set-of-steps {A} x} → subset-of-steps 𝕊 → set-of-steps {A} x
subset-to-set sub-ε           = ss-ε
subset-to-set (sub-∘ sub)     = subset-to-set sub
subset-to-set (sub-∙ {R} sub) = ss-∷ R (subset-to-set sub)

set-to-subset : ∀ {A} {x} {𝕊 : set-of-steps {A} x} → set-of-steps {A} x → subset-of-steps 𝕊
set-to-subset {𝕊 = ss-ε}     _ = sub-ε
set-to-subset {𝕊 = ss-∷ R 𝕊} X
  with ss∈? R X
...  | no  _ = sub-∘ (set-to-subset {𝕊 = 𝕊} X)
...  | yes _ = sub-∙ (set-to-subset {𝕊 = 𝕊} X)

deceq-subset : ∀ {A} {x} {𝕊 : set-of-steps {A} x} (X Y : subset-of-steps 𝕊) → Dec (X ≡ Y)
deceq-subset sub-ε     sub-ε     = yes refl
deceq-subset (sub-∘ X) (sub-∘ Y)
  with deceq-subset X Y
...  | yes refl = yes refl
...  | no  X≢Y  = no (λ { refl → X≢Y refl })
deceq-subset (sub-∘ X) (sub-∙ Y) = no (λ {()})
deceq-subset (sub-∙ X) (sub-∘ Y) = no (λ {()})
deceq-subset (sub-∙ X) (sub-∙ Y)
  with deceq-subset X Y
...  | yes refl = yes refl
...  | no  X≢Y  = no (λ { refl → X≢Y refl })

----

all-steps : ∀ {A} {{FB : finitely-branching A}} {x}
          → set-of-steps {A} x
all-steps {{FB}} = proj₁ (finitely-branching.axiom FB)

data multistep {A} {{FB : finitely-branching A}}
                   {{_  : bounded-developments A}}
                     : (x y : Ob A) → Set where
  ms : ∀ {x}
         → (M : subset-of-steps {A} {x} all-steps)
         → subset-inhabited M
         → multistep x (ss-target (subset-to-set M))

ms-steps :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x y}
        → multistep {A} x y
        → set-of-steps {A} x
ms-steps (ms M _) = subset-to-set M

multistep-is-residual :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x₁ x₂ y₁ y₂}
    → multistep {A} x₁ y₁
    → multistep {A} x₁ x₂
    → multistep {A} x₂ y₂
    → Set
multistep-is-residual (ms M _) (ms N _) (ms P _) =
  set-to-subset (subset-to-set M /+ subset-to-set N) ≡ P

deceq-multistep : ∀ {A} {{_ : finitely-branching A}}
                        {{_ : bounded-developments A}}
                    (M N : Σ[ x ∈ Ob A ] Σ[ y ∈ Ob A ] multistep {A} x y)
                → Dec (M ≡ N)
deceq-multistep {A} (x₁ , y₁ , ms M _) (x₂ , y₂ , ms N _)
  with RS.deceqOb A x₁ x₂
...  | no x₁≢x₂ = no (λ { refl → x₁≢x₂ refl })
...  | yes refl
     with deceq-subset M N
...     | no  M≢N  = no (λ { refl → M≢N refl })
...     | yes refl = yes (cong (λ x → (_ , _ , ms N x))
                               (subset-inhabited-is-prop {M = N}))

-- Given an orthogonal axiomatic rewrite system A,
-- we may build an axiomatic rewrite system
-- whose steps are the multisteps of A.
𝕄 : (A : RS)
     → {{_ : finitely-branching A}}
     → {{_ : bounded-developments A}}
     → RS
𝕄 A = mkRS
        (Ob A)
        (multistep {A})
        multistep-is-residual
        (RS.deceqOb A)
        deceq-multistep

set-full-subset :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x}
    → (𝕊 : set-of-steps {A} x)
    → subset-of-steps 𝕊
set-full-subset ss-ε       = sub-ε
set-full-subset (ss-∷ _ 𝕊) = sub-∙ (set-full-subset 𝕊)

subset-powerset :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x}
    → {𝕊 : set-of-steps {A} x}
    → subset-of-steps 𝕊
    → L.List (subset-of-steps 𝕊)
subset-powerset sub-ε     = sub-ε L.∷ L.[]
subset-powerset (sub-∘ M) = L.map sub-∘ (subset-powerset M)
subset-powerset (sub-∙ M) = L.map sub-∘ (subset-powerset M)
                       L.++ L.map sub-∙ (subset-powerset M)

list∈ : {A : Set} (x : A) (ys : L.List A) → Set
list∈ x L.[]       = ⊥
list∈ x (y L.∷ ys) = (x ≡ y) ⊎ list∈ x ys

list∈-map : {A B : Set} {f : A → B} {x : A} {ys : L.List A}
          → list∈ x ys
          → list∈ (f x) (L.map f ys)
list∈-map {ys = y L.∷ ys} (inj₁ refl) = inj₁ refl
list∈-map {ys = y L.∷ ys} (inj₂ x∈ys) = inj₂ (list∈-map {ys = ys} x∈ys)

list∈++l : {A : Set} {x : A} {ys zs : L.List A}
         → list∈ x ys
         → list∈ x (ys L.++ zs)
list∈++l {ys = x L.∷ ys} (inj₁ refl) = inj₁ refl
list∈++l {ys = x L.∷ ys} (inj₂ x∈ys) = inj₂ (list∈++l {ys = ys} x∈ys)

list∈++r : {A : Set} {x : A} {ys zs : L.List A}
         → list∈ x zs
         → list∈ x (ys L.++ zs)
list∈++r {ys = L.[]}     x∈zs = x∈zs
list∈++r {ys = _ L.∷ ys} x∈zs = inj₂ (list∈++r {ys = ys} x∈zs)

subset-powerset-correct :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x}
    → {𝕊 : set-of-steps {A} x}
    → (M : subset-of-steps 𝕊)
    → list∈ M (subset-powerset (set-full-subset 𝕊))
subset-powerset-correct sub-ε     = inj₁ refl
subset-powerset-correct (sub-∘ M) =
  list∈++l (list∈-map (subset-powerset-correct M))
subset-powerset-correct (sub-∙ M) =
  list∈++r (list∈-map (subset-powerset-correct M))

select-multisteps :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x}
    → L.List (subset-of-steps {A} {x} all-steps)
    → set-of-steps {𝕄 A} x
select-multisteps L.[]       = ss-ε
select-multisteps (M L.∷ Ms)
  with subset-inhabited? M
...  | no  _  = select-multisteps Ms
...  | yes Mp = ss-∷ (_ , ms M Mp)
                     (select-multisteps Ms)

select-multisteps-correct :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x}
    → (N  : subset-of-steps {A} {x} all-steps) 
    → (Np : subset-inhabited N)
    → (Ms : L.List (subset-of-steps {A} {x} all-steps))
    → list∈ N Ms
    → ss∈ (_ , ms N Np) (select-multisteps Ms)
select-multisteps-correct N Np (M L.∷ Ms) (inj₁ refl)
  with subset-inhabited? N
...  | yes _   = inj₁ (cong (λ x → (_ , ms N x))
                      (subset-inhabited-is-prop {M = N}))
...  | no  ¬Np = ⊥-elim (¬Np Np)
select-multisteps-correct N Np (M L.∷ Ms) (inj₂ N∈Ms)
  with subset-inhabited? M
...  | yes _   = inj₂ (select-multisteps-correct N Np Ms N∈Ms)
...  | no  ¬Np = select-multisteps-correct N Np Ms N∈Ms
 
𝕄-finitely-branching :
   ∀ {A} {{_ : finitely-branching A}}
         {{_ : bounded-developments A}}
     → finitely-branching (𝕄 A)
𝕄-finitely-branching =
  finitely-branching-proof (
    select-multisteps (subset-powerset (set-full-subset all-steps)),
    (λ { _ (ms M Mp) →
         select-multisteps-correct M Mp 
           (subset-powerset (set-full-subset all-steps))
           (subset-powerset-correct _)
       }))

-- TODO : prove self erasure

multistep-self-erasure :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
        {x}
    → {𝕊 : set-of-steps {A} x}
    → (M : subset-of-steps 𝕊)
    → {𝕋 : set-of-steps {A} (ss-target (subset-to-set M))}
    → {N : subset-of-steps 𝕋}
    → set-to-subset (subset-to-set M /+ subset-to-set M) ≡ N
    → ¬ subset-inhabited N
multistep-self-erasure sub-ε         refl inh = {!!}
multistep-self-erasure (sub-∘ M) {𝕋} refl inh = multistep-self-erasure M {𝕋 = 𝕋} refl inh
multistep-self-erasure (sub-∙ M) {𝕋} refl inh = {!!}

𝕄-self-erasure :
  ∀ {A} {{_ : finitely-branching A}}
        {{_ : bounded-developments A}}
    → self-erasure (𝕄 A)
𝕄-self-erasure =
  self-erasure-proof (λ {
    (ms M _) (ms _ Np) res → multistep-self-erasure M res Np
  })

-- TODO : prove remaining axioms
