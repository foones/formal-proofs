
module Developments where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Relation.Nullary
open import Relation.Binary.Core

open import Utils
open import AxiomaticRewriteSystem
open import SetOfSteps

data is-development {A} {{_ : finitely-branching A}} :
        ∀ {x y} → set-of-steps {A} x
                → derivation {A} x y
                → Set
  where
    dev-ε : ∀ {x} {M : set-of-steps {A} x} → is-development M ε
    dev-∷ : ∀ {x y z R} → {M : set-of-steps {A} x}
                        → ss∈ (y , R) M
                        → {d : derivation y z}
                        → is-development (M +/¹ R) d
                        → is-development M (R ∷ d)
                        
dev-∷-inversion : ∀ {A} {{_ : finitely-branching A}} {x y z R}
                    → {M : set-of-steps {A} x}
                    → ss∈ (y , R) M
                    → {d : derivation y z}
                    → is-development M (R ∷ d)
                    → is-development (M +/¹ R) d
dev-∷-inversion _ (dev-∷ _ x) = x

dev-∷-∈ : ∀ {A} {{_ : finitely-branching A}} {x y z}
                    → {M : set-of-steps {A} x}
                    → {R : Step A x y}
                    → {d : derivation {A} y z}
                    → is-development M (R ∷ d)
                    → ss∈ (_ , R) M
dev-∷-∈ (dev-∷ R∈M x) = R∈M

dev-++-inversion :
  ∀ {A x y z} {{_ : finitely-branching A}}
    → {M : set-of-steps {A} x}
    → (d : derivation {A} x y)
    → (e : derivation {A} y z)
    → is-development M (d ++ e)
    → is-development M d × is-development (M +/* d) e
dev-++-inversion ε       e x             = dev-ε , x
dev-++-inversion (R ∷ d) e (dev-∷ R∈M x) =
  let (dev-d , dev-e) = dev-++-inversion d e x in
    dev-∷ R∈M dev-d , dev-e

development : ∀ {A} {{_ : finitely-branching A}} {x}
                → set-of-steps {A} x
                → Set
development {A} {x} M =
  Σ[ y ∈ Ob A ] Σ[ d ∈ derivation {A} x y ]
    is-development M d

development-target :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → ∀ {x} → {M : set-of-steps {A} x}
    → development M
    → Ob A
development-target (y , _ , _) = y

development-derivation :
  ∀ {A} {{_ : finitely-branching A}} {x} {M}
    → (dev : development {A} {x} M)
    → derivation {A} x (development-target dev)
development-derivation ( _ , d , _) = d
    
is-empty-development :
  ∀ {A} {{_ : finitely-branching A}} {x}
        → (d : development {A} {x} ss-ε)
        → Set
is-empty-development (_ , ε , _)     = ⊤
is-empty-development (_ , _ ∷ _ , _) = ⊥
    
development-of-empty :
  ∀ {A} {{_ : finitely-branching A}} {x}
        → (d : development {A} {x} ss-ε)
        → is-empty-development d
development-of-empty (_ , _ , dev-ε)     = tt
development-of-empty (_ , _ , dev-∷ w _) = w

cons-not-development-of-empty :
  ∀ {A} {{_ : finitely-branching A}} {x y z}
        → (R : Step A x y)
        → (d : derivation {A} y z)
        → ¬(is-development ss-ε (R ∷ d))
cons-not-development-of-empty R d = λ dev →
  ⊥-elim (development-of-empty (_ , R ∷ d , dev))

dev-++ : ∀ {A x y z} {{_ : finitely-branching A}}
           → {M : set-of-steps {A} x}
           → {d : derivation {A} x y}
           → {e : derivation {A} y z}
           → is-development M d
           → is-development (M +/* d) e
           → is-development M (d ++ e)
dev-++ dev-ε       q = q
dev-++ (dev-∷ x p) q = dev-∷ x (dev-++ p q)

dev-++-subset : ∀ {A x y z} {{_ : finitely-branching A}}
           → {M N : set-of-steps {A} x}
           → {d : derivation {A} x y}
           → {e : derivation {A} y z}
           → ss-subset M N
           → is-development M d
           → is-development (N +/* d) e
           → is-development N (d ++ e)
dev-++-subset subset dev-ε                 q = q
dev-++-subset subset (dev-∷ {R = R} R∈M p) q =
  dev-∷ (ss-subset-correct subset R∈M)
        (dev-++-subset (ss-subset-+/¹ _ _ R subset) p q)

development-++ : ∀ {A x} {{_ : finitely-branching A}}
           → {M : set-of-steps {A} x}
           → (dev : development M)
           → development (M +/* development-derivation dev)
           → development M
development-++ (_ , d , dev-d) (_ , e , dev-e) = (_ , d ++ e , dev-++ dev-d dev-e)

development-++-subset : ∀ {A x} {{_ : finitely-branching A}}
           → {M N : set-of-steps {A} x}
           → (subset : ss-subset M N)
           → (dev : development M)
           → development (N +/* development-derivation dev)
           → development N
development-++-subset subset (_ , d , dev-d) (_ , e , dev-e) = (_ , d ++ e , dev-++-subset subset dev-d dev-e)

is-complete : ∀ {A} {x} {{_ : finitely-branching A}}
                → {M : set-of-steps {A} x}
                → development M
                → Set
is-complete {A} {x} {M} (y , d , _) =
  ∀ {z} → (R : Step A y z)
        → ¬ is-development M (d ++ (R ∷ ε))

is-complete-development : ∀ {A} {x y} {{_ : finitely-branching A}}
                            → set-of-steps {A} x
                            → derivation {A} x y
                            → Set
is-complete-development M d =
  Σ[ dev ∈ is-development M d ] is-complete (_ , d , dev)

complete-development :
  ∀ {A} {{_ : finitely-branching A}} {x}
    → set-of-steps {A} x
    → Set
complete-development {A} {x} M =
  Σ[ d ∈ development M ] is-complete d

record self-erasure (A : RS) : Set where
  constructor self-erasure-proof
  field
    axiom : ∀ {x y z} → (R : Step A x y)
                      → (S : Step A y z)
                      → ¬ (isResidual A R R S)
open self-erasure {{...}} public

derivation-length : ∀ {A x y} → derivation {A} x y → ℕ
derivation-length ε       = ℕ.zero
derivation-length (_ ∷ d) = ℕ.suc (derivation-length d)

complete-development-development :
  ∀ {A} {{_ : finitely-branching A}} {x} {M}
    → complete-development {A} {x} M
    → development M
complete-development-development (dev , _) = dev

complete-development-target :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → ∀ {x} → {M : set-of-steps {A} x}
    → complete-development M
    → Ob A
complete-development-target (dev , _) = development-target dev

complete-development-derivation :
  ∀ {A} {{_ : finitely-branching A}} {x} {M}
    → (c : complete-development {A} {x} M)
    → derivation {A} x (complete-development-target c)
complete-development-derivation ( d , _) = development-derivation d

-- If d is a development of M/R and
-- R∷d is a *complete* development of M
-- then d is also a *complete* development of M/R.
--
is-complete-tail :
  ∀ {A} {{_ : finitely-branching A}} {x y}
    → {R : Step A x y}
    → {M : set-of-steps {A} x}
    → (R∈M : ss∈ (_ , R) M)
    → (dev : development (M +/¹ R))
    → let _ , d , d-dev = dev in
          is-complete (_ , R ∷ d , dev-∷ R∈M d-dev)
        → is-complete dev
is-complete-tail R∈M (_ , d , d-dev) R∷d-cpl =
  λ S d∷S-dev → ⊥-elim (R∷d-cpl S (dev-∷ R∈M d∷S-dev))

complete-development-head :
  ∀ {A} {{_ : finitely-branching A}} {x y}
    → {R : Step A x y}
    → {M : set-of-steps {A} x}
    → ss∈ (_ , R) M
    → complete-development M
    → out-step {A} x
complete-development-head {A} {x} {y} {R} R∈M ((_ , ε , _) , cpl)   =
  ⊥-elim (cpl R (dev-∷ R∈M dev-ε))
complete-development-head R∈M ((_ , S ∷ d , _) , _) = _ , S

complete-development-tail :
  ∀ {A} {{_ : finitely-branching A}} {x y}
    → {R : Step A x y}
    → {M : set-of-steps {A} x}
    → (R∈M : ss∈ (_ , R) M)
    → (c : complete-development M)
    → complete-development (M +/¹ proj₂ (complete-development-head R∈M c))
complete-development-tail {A} {x} {y} {R} R∈M ((_ , ε , _) , cpl) =
  ⊥-elim (cpl R (dev-∷ R∈M dev-ε))
complete-development-tail R∈M ((_ , S ∷ d , dev-∷ S∈M d-dev) , S∷d-cpl) =
  (_ , d , d-dev) ,
  is-complete-tail S∈M (_ , d , d-dev) S∷d-cpl

is-complete-++-subset : ∀ {A x} {{_ : finitely-branching A}}
           → {M N : set-of-steps {A} x}
           → (dev₁ : development M)
           → (dev₂ : development (N +/* development-derivation dev₁))
           → (subset : ss-subset M N)
           → is-complete dev₂
           → is-complete (development-++-subset subset dev₁ dev₂)
is-complete-++-subset (_ , d , d-dev) (_ , e , e-dev) subset cpl =
  λ R d++e∷R-dev →
    ⊥-elim
      (cpl R
        (dev-++ e-dev
          (dev-∷ (let (_ , R∷ε-dev) = dev-++-inversion (d ++ e) (R ∷ ε) d++e∷R-dev in
                  let R∈X = dev-∷-∈ R∷ε-dev in
                    transport (λ x → ss∈ (_ , R) x)
                              (ss-+/*-++ d e _)
                              R∈X)
                 dev-ε)))

complete-development-++-subset :
  ∀ {A x} {{_ : finitely-branching A}}
    → {M N : set-of-steps {A} x}
    → (subset : ss-subset M N)
    → (dev : development M)
    → complete-development (N +/* development-derivation dev)
    → complete-development N
complete-development-++-subset subset dev₁ (dev₂ , cpl₂) =
  development-++-subset subset dev₁ dev₂ ,
  is-complete-++-subset dev₁ dev₂ subset cpl₂
