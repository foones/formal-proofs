
module SetOfSteps where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
import Data.List as L

open import Utils
open import AxiomaticRewriteSystem

-- Finite set of coinitial steps.

data set-of-steps {A} (x : Ob A) : Set where
  ss-ε : set-of-steps x
  ss-∷ : out-step {A} x → set-of-steps {A} x → set-of-steps x
  
ss-++ : ∀ {A} {x} → set-of-steps {A} x → set-of-steps {A} x → set-of-steps {A} x
ss-++ ss-ε        M₂ = M₂
ss-++ (ss-∷ R M₁) M₂ = ss-∷ R (ss-++ M₁ M₂)

ss∈ : ∀ {A x} → out-step {A} x → set-of-steps {A} x → Set
ss∈ _ ss-ε        = ⊥
ss∈ x (ss-∷ y ys) = x ≡ y ⊎ ss∈ x ys

ss∉ : ∀ {A x} → out-step {A} x → set-of-steps {A} x → Set
ss∉ x M = ¬ (ss∈ x M)

ss∈? : ∀ {A x} → (R : out-step {A} x) → (X : set-of-steps {A} x) → Dec (ss∈ R X)
ss∈?     _       ss-ε       = no (λ x → x)
ss∈? {A} (_ , R) (ss-∷ (_ , S) X)
  with RS.deceqStep A (_ , _ , R) (_ , _ , S)
...  | yes refl = yes (inj₁ refl)
...  | no  R≢S
     with ss∈? (_ , R) X
...     | yes R∈X = yes (inj₂ R∈X)
...     | no  R∉X = no λ {
                      (inj₁ refl) → R≢S refl
                    ; (inj₂ R∈X)  → R∉X R∈X
                    }

ss∈++l : ∀ {A x}
           → {R : out-step {A} x}
           → {M N : set-of-steps {A} x}
           → ss∈ R M
           → ss∈ R (ss-++ M N)
ss∈++l {M = ss-ε}      R∈M    = ⊥-elim R∈M
ss∈++l {M = ss-∷ S M'} R∈S∷M' with R∈S∷M'
... | inj₁ refl = inj₁ refl
... | inj₂ R∈M' = inj₂ (ss∈++l R∈M')

ss∈++r : ∀ {A x}
           → {R : out-step {A} x}
           → {M N : set-of-steps {A} x}
           → ss∈ R N
           → ss∈ R (ss-++ M N)
ss∈++r {M = ss-ε}      R∈N = R∈N
ss∈++r {M = ss-∷ S M'} R∈N = inj₂ (ss∈++r R∈N)

ss-subset : ∀ {A x} → set-of-steps {A} x → set-of-steps {A} x → Set
ss-subset ss-ε       N = ⊤
ss-subset (ss-∷ R M) N = ss∈ R N × ss-subset M N

ss⊆ = ss-subset

ss-subset-ε-empty : ∀ {A x}
                      → {M : set-of-steps {A} x}
                      → ss-subset M ss-ε
                      → M ≡ ss-ε
ss-subset-ε-empty {M = ss-ε}      _         = refl
ss-subset-ε-empty {M = ss-∷ R M'} (R∈ε , _) = ⊥-elim R∈ε

ss-subset-correct : ∀ {A x}
                      → {M N : set-of-steps {A} x}
                      → ss-subset M N
                      → ∀ {y} → {R : Step A x y}
                      → ss∈ (_ , R) M
                      → ss∈ (_ , R) N
ss-subset-correct {M = ss-ε}      _                 R∈M = ⊥-elim R∈M
ss-subset-correct {M = ss-∷ S M'} (S∈N , M'-subset) R∈M with R∈M
... | inj₁ refl = S∈N
... | inj₂ R∈M' = ss-subset-correct M'-subset R∈M'

ss-subset-≡r : ∀ {A x}
                   → {M N₁ N₂ : set-of-steps {A} x}
                   → N₁ ≡ N₂
                   → ss-subset M N₁
                   → ss-subset M N₂
ss-subset-≡r refl subset = subset

ss-++-subset : ∀ {A x}
                 → {M₁ M₂ N : set-of-steps {A} x}
                 → ss-subset M₁ N
                 → ss-subset M₂ N
                 → ss-subset (ss-++ M₁ M₂) N
ss-++-subset {M₁ = ss-ε}      _               subset₂ = subset₂
ss-++-subset {M₁ = ss-∷ S M'} (S∈N , subset₁) subset₂ =
  S∈N , ss-++-subset subset₁ subset₂

ss-++-assoc : ∀ {A} {x₁}
              → (M N O : set-of-steps {A} x₁)
              → ss-++ M (ss-++ N O) ≡ ss-++ (ss-++ M N) O
ss-++-assoc ss-ε       _ _ = refl
ss-++-assoc (ss-∷ R M) N O = cong (ss-∷ R) (ss-++-assoc M N O)

ss-subset-extend : ∀ {A x}
                   → (M : set-of-steps {A} x)
                   → (N : set-of-steps {A} x)
                   → ss-subset M (ss-++ N M)
ss-subset-extend ss-ε _ = tt
ss-subset-extend (ss-∷ R M') N =
  ss∈++r (inj₁ refl) ,
  ss-subset-≡r
    (sym (ss-++-assoc N (ss-∷ R ss-ε) M'))
    (ss-subset-extend M' (ss-++ N (ss-∷ R ss-ε)))

ss-subset-refl : ∀ {A x}
                   → (M : set-of-steps {A} x)
                   → ss-subset M M
ss-subset-refl M = ss-subset-extend M ss-ε

ss-subset-trans : ∀ {A x}
                   → {M₁ M₂ M₃ : set-of-steps {A} x}
                   → ss-subset M₁ M₂
                   → ss-subset M₂ M₃
                   → ss-subset M₁ M₃
ss-subset-trans {_} {_} {ss-ε} _ _ = tt
ss-subset-trans {_} {_} {ss-∷ R M'₁} {M₂} {M₃} (R∈M₂ , s'₁₂) s₂₃ =
  ss-subset-correct s₂₃ R∈M₂ , ss-subset-trans {M₁ = M'₁} s'₁₂ s₂₃

ss-++-εr : ∀ {A x}
            → (M : set-of-steps {A} x)
            → ss-++ M ss-ε ≡ M
ss-++-εr ss-ε        = refl
ss-++-εr (ss-∷ R M') = cong (λ x → ss-∷ R x) (ss-++-εr M')

ss-subset-++l : ∀ {A x}
                 → {M N₁ N₂ : set-of-steps {A} x}
                 → ss-subset M N₁
                 → ss-subset M (ss-++ N₁ N₂)
ss-subset-++l {M = ss-ε}      _                = tt
ss-subset-++l {M = ss-∷ R M'} (R∈N₁ , subset') = ss∈++l R∈N₁ , ss-subset-++l subset'

ss-subset-++r : ∀ {A x}
                 → {M N₁ N₂ : set-of-steps {A} x}
                 → ss-subset M N₂
                 → ss-subset M (ss-++ N₁ N₂)
ss-subset-++r {M = ss-ε}      _                = tt
ss-subset-++r {M = ss-∷ R M'} (R∈N₂ , subset') = ss∈++r R∈N₂ , ss-subset-++r subset'

ss-concat-map : ∀ {ℓ} {A x} {T : Set ℓ}
                  → (M : set-of-steps {A} x)
                  → ((R : out-step {A} x) → ss∈ R M → L.List T)
                  → L.List T
ss-concat-map ss-ε        _ = L.[]
ss-concat-map (ss-∷ R M') f =
  f R (inj₁ refl)
  L.++
  ss-concat-map M' (λ S w → f S (inj₂ w))

ss-concat-map-correct : ∀ {ℓ} {A x} {T : Set ℓ}
                          → (M : set-of-steps {A} x)
                          → (f : (R : out-step {A} x) → ss∈ R M → L.List T)
                          → (S : out-step {A} x)
                          → (t : T)
                          → (S∈M : ss∈ S M)
                          → list∈ t (f S S∈M)
                          → list∈ t (ss-concat-map M f)
ss-concat-map-correct ss-ε        f S t S∈M t∈fS = ⊥-elim S∈M
ss-concat-map-correct (ss-∷ R M') f S t S∈M t∈fS
  with S∈M
... | inj₁ refl = list∈-++L t∈fS
... | inj₂ S∈M' = list∈-++R (ss-concat-map-correct M' _ _ t S∈M' t∈fS)

record finitely-branching (A : RS) : Set where
  constructor finitely-branching-proof
  field
    axiom : ∀ {x} → Σ[ M ∈ set-of-steps {A} x ]
                     ∀ (y : Ob A)
                     → (R : Step A x y)
                     → ss∈ (y , R) M
open finitely-branching {{...}} public

infixl 4 _/¹_
infixl 4 _+/¹_
infixl 4 _+/*_
infixl 4 _¹/*_
  
-- Step / step = set-of-steps.
_/¹_ :  ∀ {A} {x₁ x₂ y₁} {{_ : finitely-branching A}}
          → Step A x₁ y₁
          → Step A x₁ x₂
          → set-of-steps {A} x₂
_/¹_ {A} {{FB}} R₁ S =
  Σ.proj₁ (finitely-branching.axiom FB)

-- set-of-steps / step = set-of-steps.
_+/¹_ : ∀ {A} {x₁ x₂} {{_ : finitely-branching A}}
          → set-of-steps {A} x₁
          → Step A x₁ x₂
          → set-of-steps {A} x₂
ss-ε             +/¹  _ = ss-ε
(ss-∷ (_ , R) M) +/¹  S = ss-++ (R /¹ S) (M +/¹ S)

-- set-of-steps / derivation = set-of-steps.
_+/*_ : ∀ {A} {x₁ x₂} {{_ : finitely-branching A}}
          → set-of-steps {A} x₁
          → derivation {A} x₁ x₂
          → set-of-steps {A} x₂
M +/* ε       = M
M +/* (R ∷ d) = (M +/¹ R) +/* d

-- step / derivation = set-of-steps.
_¹/*_ : ∀ {A} {x₁ y₁ x₂} {{_ : finitely-branching A}}
          → Step A x₁ y₁
          → derivation {A} x₁ x₂
          → set-of-steps {A} x₂
R ¹/* d = (ss-∷ (_ , R) ss-ε) +/* d

---- Properties

ss-ε-+/* : ∀ {A} {{_ : finitely-branching A}} {x y}
                    → (d : derivation {A} x y)
                    → (ss-ε +/* d) ≡ ss-ε
ss-ε-+/* ε       = refl
ss-ε-+/* (_ ∷ d) = ss-ε-+/* d

ss-++-+/¹ : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂}
              → (R : Step A x₁ x₂)
              → (M N : set-of-steps {A} x₁)
              → (ss-++ M N +/¹ R) ≡ ss-++ (M +/¹ R) (N +/¹ R)
ss-++-+/¹ R ss-ε       N = refl
ss-++-+/¹ {{FB}} R (ss-∷ (_ , S) M) N =
   trans
     (cong (ss-++ (proj₁ (finitely-branching.axiom FB)))
           (ss-++-+/¹ R M N))
     (ss-++-assoc _ (M +/¹ R) (N +/¹ R))

ss-++-+/* : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂}
              → (d : derivation {A} x₁ x₂)
              → (M N : set-of-steps {A} x₁)
              → (ss-++ M N +/* d) ≡ ss-++ (M +/* d) (N +/* d)
ss-++-+/* ε       _ _ = refl
ss-++-+/* (R ∷ d) M N =
  trans (cong (λ x → x +/* d) (ss-++-+/¹ R M N))
        (ss-++-+/* d (M +/¹ R) (N +/¹ R))

ss-∷-+/* : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ x₃}
             → (d : derivation {A} x₁ x₂)
             → (R : Step A x₁ x₃)
             → (M : set-of-steps {A} x₁)
             → (ss-∷ (_ , R) M +/* d) ≡ ss-++ (R ¹/* d) (M +/* d)
ss-∷-+/* d R M = ss-++-+/* d (ss-∷ (_ , R) ss-ε) M

ss-+/*-++ : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ x₃}
             → (d : derivation {A} x₁ x₂)
             → (e : derivation {A} x₂ x₃)
             → (M : set-of-steps {A} x₁)
             → (M +/* (d ++ e)) ≡ ((M +/* d) +/* e)
ss-+/*-++ ε       e M = refl
ss-+/*-++ (R ∷ d) e M = ss-+/*-++ d e (M +/¹ R)

ss-subset-¹/ : ∀ {A} {{_ : finitely-branching A}} {x y z}
                 → {M : set-of-steps {A} x}
                 → {R : Step A x y}
                 → {S : Step A x z}
                 → ss∈ (_ , S) M
                 → ss-subset (S /¹ R) (M +/¹ R)
ss-subset-¹/ {M = ss-ε}          S∈M    = ⊥-elim S∈M
ss-subset-¹/ {M = ss-∷ T M'} {R} S∈T∷M' with S∈T∷M'
... | inj₁ refl = ss-subset-++l (ss-subset-refl _)
... | inj₂ S∈M' = ss-subset-++r (ss-subset-¹/ {R = R} S∈M')

ss-subset-+/¹ : ∀ {A} {{_ : finitely-branching A}} {x y}
                  → (M : set-of-steps {A} x)
                  → (N : set-of-steps {A} x)
                  → (R : Step A x y)
                  → ss-subset M N
                  → ss-subset (M +/¹ R) (N +/¹ R)
ss-subset-+/¹ ss-ε       _ _ _                = tt
ss-subset-+/¹ (ss-∷ (_ , S) M) N R (S∈N , M-subset) =
  ss-++-subset (ss-subset-¹/ {R = R} S∈N) (ss-subset-+/¹ M N R M-subset)

-- Inhabitation

ss-inhabited : ∀ {A} {x : Ob A} (M : set-of-steps {A} x) → Set
ss-inhabited ss-ε       = ⊥
ss-inhabited (ss-∷ _ _) = ⊤

ss-ε-not-inhabited : ∀ {A} {x : Ob A} {M : set-of-steps {A} x}
                       → M ≡ ss-ε
                       → ¬ ss-inhabited M
ss-ε-not-inhabited refl = ⊥-elim

ss-inhabited-is-prop : ∀ {A x}
                         → {M : set-of-steps {A} x}
                         → {p q : ss-inhabited M}
                         → p ≡ q
ss-inhabited-is-prop {M = ss-ε}     {p}       = ⊥-elim p
ss-inhabited-is-prop {M = ss-∷ _ _} {tt} {tt} = refl

-- No repeats

ss-no-repeats : ∀ {A} {x : Ob A} (M : set-of-steps {A} x) → Set
ss-no-repeats ss-ε       = ⊤
ss-no-repeats (ss-∷ R M) = ss∉ R M × ss-no-repeats M

-- Same elements

ss≡ : ∀ {A} {x : Ob A} → set-of-steps {A} x → set-of-steps {A} x → Set
ss≡ M N = ss⊆ M N × ss⊆ N M

ss≡-refl : 
  ∀ {A} {x : Ob A}
    → {M : set-of-steps {A} x}
    → ss≡ M M
ss≡-refl {_} {_} {M} = ss-subset-refl M , ss-subset-refl M

ss≡-refl' : 
  ∀ {A} {x : Ob A}
    → {M N : set-of-steps {A} x}
    → M ≡ N
    → ss≡ M N
ss≡-refl' refl = ss≡-refl

ss≡-sym : 
  ∀ {A} {x : Ob A}
    → {M₁ M₂ : set-of-steps {A} x}
    → ss≡ M₁ M₂
    → ss≡ M₂ M₁
ss≡-sym (s₁₂ , s₂₁) = s₂₁ , s₁₂

ss≡-trans : 
  ∀ {A} {x : Ob A}
    → {M₁ M₂ M₃ : set-of-steps {A} x}
    → ss≡ M₁ M₂
    → ss≡ M₂ M₃
    → ss≡ M₁ M₃
ss≡-trans (s₁₂ , s₂₁) (s₂₃ , s₃₂) =
  ss-subset-trans s₁₂ s₂₃ , ss-subset-trans s₃₂ s₂₁

ss-equivalence-relation :
  ∀ {A} {x : Ob A}
    → equivalence-relation (set-of-steps {A} x)
ss-equivalence-relation =
  ss≡ , is-equivalence-relation-proof
          ss≡-refl
          ss≡-sym
          ss≡-trans
