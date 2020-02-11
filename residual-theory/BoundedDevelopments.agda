
module BoundedDevelopments where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning
import Data.List as L

open import Utils
open import AxiomaticRewriteSystem
open import SetOfSteps
open import Developments

-- Strong version of Finite Developments:
-- there exists a bound for the length of a development.
record bounded-developments (A : RS)
         {{_ : finitely-branching A}} : Set where
  constructor bounded-developments-proof
  field
    axiom : ∀ {x} → (M : set-of-steps {A} x)
                  → Σ[ bound ∈ ℕ ]
                    ∀ {y} → (d : derivation {A} x y)
                          → is-development M d
                          → derivation-length d ≤ bound
open bounded-developments {{...}} public

-- Key results:
--
--   set-of-steps-depth
--     The depth of a set-of-steps.
--   set-of-steps-depth-correct
--     The length of any development of M is at most `set-of-steps-depth M`.
--   set-of-steps-depth-complete
--     There exists a development of M whose length is `set-of-steps-depth M`.
--   set-of-steps-depth-decreasing
--     The depth of M is greater than the depth of M/R.
--   set-of-steps-induction
--     Prove a property for set-of-stepss showing that
--     P(M/R) -> P(M)
--   complete-development-exists
--     If M is a set-of-steps, there exists a complete development of M.
--   complete-development-cofinal
--     Any two complete developments of a set-of-steps are cofinal.

developments-up-to-length : ∀ {A} {x}
                    → {{_ : finitely-branching A}}
                    → (M : set-of-steps {A} x)
                    → ℕ
                    → L.List (development M)
developments-up-to-length {A} {x} _ ℕ.zero = L.[ x , ε , dev-ε ]
developments-up-to-length {A} {x} M (ℕ.suc n) =
  (x , ε , dev-ε) L.∷
  ss-concat-map M (λ { (_ , R ) w →
    L.map (λ { (y , d , dev-d) →
            y , R ∷ d , dev-∷ w dev-d
          })
          (developments-up-to-length (M +/¹ R) n)
  })

developments-up-to-length-nonempty :
  ∀ {A} {x}
    → {{_ : finitely-branching A}}
    → (M : set-of-steps {A} x)
    → (n : ℕ)
    → ¬(developments-up-to-length M n ≡ L.[])
developments-up-to-length-nonempty _ ℕ.zero    ()
developments-up-to-length-nonempty _ (ℕ.suc _) ()

development-length : ∀ {A} {x}
                       → {{_ : finitely-branching A}}
                       → {M : set-of-steps {A} x}
                       → (d : development M)
                       → ℕ
development-length (_ , d , _) = derivation-length d
  
max-development-length : ∀ {A} {x} 
                           → {{_ : finitely-branching A}}
                           → (M : set-of-steps {A} x)
                           → L.List (development M)
                           → ℕ
max-development-length M L.[] = 0
max-development-length M (d L.∷ xs) =
  development-length d Data.Nat.⊔ max-development-length M xs
                       
max-development-length-correct :
    ∀ {A} {x}
       → {{_ : finitely-branching A}}
       → (M : set-of-steps {A} x)
       → (d : development M)
       → (xs : L.List (development M))
       → list∈ d xs
       → development-length d ≤ max-development-length M xs
max-development-length-correct M d L.[]       p = 𝟘-elim p
max-development-length-correct M d (e L.∷ xs) p
  with development-length d ≤? development-length e
... | Dec.yes d≤e = ≤-trans d≤e (m≤m⊔n _ _)
... | Dec.no  ¬d≤e with p 
...     | inj₁ refl = ⊥-elim (¬d≤e ≤-refl)
...     | inj₂ p'   = ≤-trans
                        (max-development-length-correct M d xs p')
                        (n≤m⊔n _ _)

max-development-length-complete :
    ∀ {A} {x}
       → {{_ : finitely-branching A}}
       → (M : set-of-steps {A} x)
       → (xs : L.List (development M))
       → ¬(xs ≡ L.[])
       → Σ[ d ∈ development M ]
         development-length d ≡ max-development-length M xs
max-development-length-complete M L.[]          nonempty = ⊥-elim (nonempty refl)
max-development-length-complete M (d₁ L.∷ L.[])      _ =  d₁ , sym (⊔-identityʳ _)
max-development-length-complete M (d₁ L.∷ d₂ L.∷ ds) _
  with development-length d₁ ≤? max-development-length M (d₂ L.∷ ds)
... | Dec.no  |d₁|≰rest = d₁ , sym (m≤n⇒n⊔m≡n (≰⇒≥ |d₁|≰rest))
... | Dec.yes |d₁|≤rest
    with max-development-length-complete M (d₂ L.∷ ds) (cons-nonempty _ _)
...   | d , d-max = d , trans d-max (sym (m≤n⇒m⊔n≡n |d₁|≤rest))

set-of-steps-depth-bound : ∀ {A} {x}
                          → {{_ : finitely-branching A}}
                          → {{_ : bounded-developments A}}
                          → set-of-steps {A} x
                          → ℕ
set-of-steps-depth-bound {_} {{_}} {{BD}} M =
  Σ.proj₁ (bounded-developments.axiom BD M)

development-list-complete-n :
  ∀ {A} {x}
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → (M : set-of-steps {A} x)
    → (d : development M)
    → (n : ℕ)
    → development-length d ≤ n
    → list∈ d (developments-up-to-length M n)
development-list-complete-n _ ( _ , ε     , dev-ε)           ℕ.zero    _         = inj₁ refl
development-list-complete-n _ ( _ , _ ∷ _ , _)               ℕ.zero    |R∷d|≤0   = ⊥-elim (1+n≰0 |R∷d|≤0)
development-list-complete-n M ( _ , ε     , dev-ε)           (ℕ.suc n) _         = inj₁ refl
development-list-complete-n M ( _ , R ∷ d , dev-∷ R∈M dev-d) (ℕ.suc n) |R∷d|≤1+n =
  inj₂ (ss-concat-map-correct M _ (_ , R) _ R∈M
         (list-map-correct _ (_ , d , dev-d) _
           (development-list-complete-n _ _ n (1+n≤1+m⇒n≤m |R∷d|≤1+n))))

development-list-complete :
  ∀ {A} {x}
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → (M : set-of-steps {A} x)
    → (d : development M)
    → list∈ d (developments-up-to-length M (set-of-steps-depth-bound M))
development-list-complete {{_}} {{BD}} M (y , d , d-dev) =
  development-list-complete-n M (y , d , d-dev)
    (set-of-steps-depth-bound M)
    (Σ.proj₂ (bounded-developments.axiom BD M) d d-dev)

set-of-steps-depth : ∀ {A} {x}
                    → {{_ : finitely-branching A}}
                    → {{_ : bounded-developments A}}
                    → set-of-steps {A} x
                    → ℕ
set-of-steps-depth M = max-development-length M
                        (developments-up-to-length M
                          (set-of-steps-depth-bound M))

set-of-steps-depth-correct : ∀ {A} {x}
                            → {{_ : finitely-branching A}}
                            → {{_ : bounded-developments A}}
                            → (M : set-of-steps {A} x)
                            → (d : development {A} M)
                            → development-length d ≤ set-of-steps-depth M
set-of-steps-depth-correct M d =
  max-development-length-correct M d 
    (developments-up-to-length M (set-of-steps-depth-bound M))
    (development-list-complete _ _)

set-of-steps-depth-complete : ∀ {A} {x}
                            → {{_ : finitely-branching A}}
                            → {{_ : bounded-developments A}}
                            → (M : set-of-steps {A} x)
                            → Σ[ d ∈ development {A} M ]
                                development-length d ≡ set-of-steps-depth M
set-of-steps-depth-complete M = max-development-length-complete M
                               (developments-up-to-length M (set-of-steps-depth-bound M))
                               (developments-up-to-length-nonempty _ _)

-- The depth of a set-of-steps M decreases after projection (M/R).

set-of-steps-depth-decreasing :
  ∀ {A} {x y}
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → (M : set-of-steps {A} x)
    → (R : Step A x y)
    → ss∈ (_ , R) M
    → set-of-steps-depth M ≥ 1 + set-of-steps-depth (M +/¹ R) 
set-of-steps-depth-decreasing M R R∈M
  with set-of-steps-depth-complete (M +/¹ R)
... | (_ , d , d-dev) , eq =
      ≡∘≤ (cong ℕ.suc (sym eq))
          (set-of-steps-depth-correct M (_ , R ∷ d , dev-∷ R∈M d-dev))
          
empty-set-of-steps-zero-depth :
  ∀ {A}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → ∀ {x}
  → set-of-steps-depth (ss-ε {A} {x}) ≡ 0
empty-set-of-steps-zero-depth {A} {x}
  with set-of-steps-depth-complete (ss-ε {A} {x})
... | (_ , ε , _)       , eq = trans (sym eq) refl
... | (_ , R ∷ d , dev) , eq = ⊥-elim (cons-not-development-of-empty _ _ dev)

nonempty-set-of-steps-nonzero-depth :
  ∀ {A}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → ∀ {x}
  → (R : out-step {A} x)
  → (M : set-of-steps {A} x)
  → ¬(set-of-steps-depth (ss-∷ R M) ≡ 0)
nonempty-set-of-steps-nonzero-depth (_ , R) M = λ h →
  ⊥-elim
    (1+n≰0
      (≤∘≡
        (set-of-steps-depth-correct
          (ss-∷ (_ , R) M)
          (_ , R ∷ ε , dev-∷ (inj₁ refl) dev-ε))
        h))

nonempty-set-of-steps-suc-depth :
  ∀ {A}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → ∀ {x}
  → (R : out-step {A} x)
  → (M : set-of-steps {A} x)
  → {n : ℕ}
  → set-of-steps-depth (ss-∷ R M) ≡ n
  → Σ[ m ∈ ℕ ] n ≡ suc m
nonempty-set-of-steps-suc-depth R M {n} p
  with n
...  | zero  = ⊥-elim (nonempty-set-of-steps-nonzero-depth R M p)
...  | suc m = m , refl

-- SetOfSteps induction principle.
--
-- To show that a property holds for any set-of-steps M,
-- it suffices to prove it for the empty set-of-steps,
-- and that if P(M/R) for some R ∈ M
-- then P(M).

-- Auxiliary recursive function
set-of-steps-induction-rec : ∀ {A} {ℓ}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → (P : ∀ {x} → set-of-steps {A} x → Set ℓ)
  → (∀ {x} → (M : set-of-steps {A} x)
           → (∀ {y}
                → (R : Step A x y)
                → ss∈ (_ , R) M
                → P (M +/¹ R))
           → P M)
  → ∀ {x} → (M : set-of-steps {A} x)
  → (n : ℕ) → set-of-steps-depth M ≤ n 
  → P M
set-of-steps-induction-rec P ps
    ss-ε              ℕ.zero    _  = ps ss-ε (λ S S∈M → ⊥-elim S∈M)
set-of-steps-induction-rec P ps
    (ss-∷ R M')       ℕ.zero    le =
      ⊥-elim
        (1+n≰0
          (≡∘≤
            (sym (proj₂ (n≢0⇒n=1+m (nonempty-set-of-steps-nonzero-depth R M'))))
            le))
set-of-steps-induction-rec P ps
    ss-ε              (ℕ.suc n) le = ps ss-ε (λ S S∈M → ⊥-elim S∈M)
set-of-steps-induction-rec P ps
    (ss-∷ (_ , R) M') (ℕ.suc n) le =
      ps (ss-∷ (_ , R) M')
         (λ S S∈M →
           set-of-steps-induction-rec P ps _ n
            (cancel-+-left-≤ 1
              (≤-trans (set-of-steps-depth-decreasing (ss-∷ (_ , R) M') S S∈M)
                       le)))

inductive-step-type : ∀ {A} {ℓ}
                    → {{_ : finitely-branching A}}
                    → {{_ : bounded-developments A}}
                    → (P : ∀ {x} → set-of-steps {A} x → Set ℓ)
                    → Set ℓ
inductive-step-type {A} P = 
    ∀ {x} → (M : set-of-steps {A} x)
              → (∀ {y}
                   → (R : Step A x y)
                   → ss∈ (_ , R) M
                   → P (M +/¹ R))
              → P M

set-of-steps-induction : ∀ {A} {ℓ}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → (P : ∀ {x} → set-of-steps {A} x → Set ℓ)
  → inductive-step-type P
  → ∀ {x} → (M : set-of-steps {A} x)
          → P M
set-of-steps-induction {A} P ps {x} M =
  set-of-steps-induction-rec P ps M (set-of-steps-depth M) ≤-refl

set-of-steps-induction-bound-irrelevant : ∀ {A} {ℓ}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → (P : ∀ {x} → set-of-steps {A} x → Set ℓ)
  → (ps : inductive-step-type P) 
  → ∀ {x} → (M : set-of-steps {A} x)
  → (n : ℕ) (Bn : set-of-steps-depth M ≤ n)
  → (m : ℕ) (Bm : set-of-steps-depth M ≤ m)
  → set-of-steps-induction-rec P ps M n Bn ≡
    set-of-steps-induction-rec P ps M m Bm
set-of-steps-induction-bound-irrelevant P ps ss-ε       zero    Bn zero    Bm = refl
set-of-steps-induction-bound-irrelevant P ps ss-ε       zero    Bn (suc m) Bm = refl
set-of-steps-induction-bound-irrelevant P ps ss-ε       (suc n) Bn zero    Bm = refl
set-of-steps-induction-bound-irrelevant P ps ss-ε       (suc n) Bn (suc m) Bm = refl
set-of-steps-induction-bound-irrelevant P ps (ss-∷ x M) zero    Bn _       Bm =
    ⊥-elim (1+n≰0 (≡∘≤ (sym (proj₂ (n≢0⇒n=1+m (nonempty-set-of-steps-nonzero-depth x M)))) Bn))
set-of-steps-induction-bound-irrelevant P ps (ss-∷ x M) (suc n) Bn zero    Bm =
    ⊥-elim (1+n≰0 (≡∘≤ (sym (proj₂ (n≢0⇒n=1+m (nonempty-set-of-steps-nonzero-depth x M)))) Bm))
set-of-steps-induction-bound-irrelevant P ps (ss-∷ x M) (suc n) Bn (suc m) Bm =
  cong (ps _) (funext* λ y → funext λ S → funext λ S∈M →
                 set-of-steps-induction-bound-irrelevant P ps _ n _ m _)

set-of-steps-induction-computation-rule : ∀ {A} {ℓ}
  → {{_ : finitely-branching A}}
  → {{_ : bounded-developments A}}
  → (P : ∀ {x} → set-of-steps {A} x → Set ℓ)
  → (ps : inductive-step-type P) 
  → ∀ {x} → (M : set-of-steps {A} x)
          → ∀ {y} {R₀ : Step A x y} → ss∈ (_ , R₀) M
          → set-of-steps-induction P ps M ≡
            ps M (λ R _ → set-of-steps-induction P ps (M +/¹ R))
set-of-steps-induction-computation-rule {A} P ps M R₀∈M = rec M (set-of-steps-depth M) R₀∈M ≤-refl
  where
    rec : ∀ {x} → (M : set-of-steps {A} x) → (n : ℕ)
                → ∀ {y} {R₀ : Step A x y} → ss∈ (_ , R₀) M
                → set-of-steps-depth M ≤ n
                → set-of-steps-induction P ps M ≡
                  ps M (λ R _ → set-of-steps-induction P ps (M +/¹ R))
    rec ss-ε        _       ()
    rec (ss-∷ R M') zero    R₀∈M le =
      ⊥-elim
        (1+n≰0
          (≡∘≤
            (sym (proj₂ (n≢0⇒n=1+m (nonempty-set-of-steps-nonzero-depth R M'))))
            le))
    rec (ss-∷ (_ , R) M') (suc n) R₀∈M le =
      let (m , depth≡Sm) = nonempty-set-of-steps-suc-depth (_ , R) M' refl
       in
          set-of-steps-induction-rec
            P ps (ss-∷ (_ , R) M')
            (set-of-steps-depth (ss-∷ (_ , R) M')) ≤-refl
        ≡⟨ set-of-steps-induction-bound-irrelevant P ps (ss-∷ (_ , R) M')
             (set-of-steps-depth (ss-∷ (_ , R) M')) ≤-refl
             (suc m) (≡∘≤ depth≡Sm ≤-refl) ⟩
          set-of-steps-induction-rec
            P ps (ss-∷ (_ , R) M') (suc m) (≡∘≤ depth≡Sm ≤-refl)
        ≡⟨ cong (ps _)
                (funext* λ y → funext λ S → funext λ S∈M →
                  set-of-steps-induction-bound-irrelevant P ps _ _ _ _ _) ⟩ _ ∎

-- Existence of complete developments

complete-development-inductive-step :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → inductive-step-type complete-development
complete-development-inductive-step ss-ε             IH =
  ((_ , ε , dev-ε), λ R → (cons-not-development-of-empty R ε))
complete-development-inductive-step (ss-∷ (_ , R) M) IH =
  let R∈M = inj₁ refl
      ((_ , d , d-development) , d-complete) = IH R R∈M
   in
    ((_ , R ∷ d , dev-∷ R∈M d-development),
     λ S hyp → d-complete S (dev-∷-inversion R∈M hyp))

complete-development-exists :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → ∀ {x} → (M : set-of-steps {A} x)
    → complete-development M
complete-development-exists =
  set-of-steps-induction _ complete-development-inductive-step

ss-target : ∀ {A} {{_ : finitely-branching A}}
                  {{_ : bounded-developments A}} {x}
              → set-of-steps {A} x
              → Ob A
ss-target M = complete-development-target (complete-development-exists M)

∂ : ∀ {A} {{_ : finitely-branching A}}
          {{_ : bounded-developments A}} {x}
      → (M : set-of-steps {A} x)
      → derivation {A} x (ss-target M)
∂ M = complete-development-derivation (complete-development-exists M)

infixl 4 _/+_

-- set-of-steps / set-of-steps = set-of-steps.
_/+_ : ∀ {A} {{_ : finitely-branching A}}
             {{_ : bounded-developments A}} {x}
          → set-of-steps {A} x
          → (N : set-of-steps {A} x)
          → set-of-steps {A} (ss-target N)
M /+ N = M +/* complete-development-derivation (complete-development-exists N)

