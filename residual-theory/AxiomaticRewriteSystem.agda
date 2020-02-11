
module AxiomaticRewriteSystem where

open import Relation.Nullary
      using (Dec)
open import Data.Product
      using (_×_; _,_; Σ; Σ-syntax)
open import Relation.Binary.PropositionalEquality
      using (_≡_; refl; cong)

-- Axiomatic Rewrite System

record RS : Set₁ where
  constructor mkRS
  field
    Ob         : Set
    Step       : (x y : Ob) → Set
    isResidual : {x₁ x₂ y₁ y₂ : Ob}
                   → Step x₁ y₁
                   → Step x₁ x₂
                   → Step x₂ y₂
                   → Set
    deceqOb    : (x y : Ob) → Dec (x ≡ y) 
    deceqStep  : (R S : Σ[ x ∈ Ob ] Σ[ y ∈ Ob ] Step x y)
                   → Dec (R ≡ S) 
open RS public

-- There are various kinds of computations.
-- Each has a symbol:
--
--     ¹  Step.
--     *  Derivation.
--     ⁺  SetOfSteps.
--     ** Multiderivation.
--
-- There are various kinds of residual notions:
--
-- (1) Ternary relation.
--     Written as follows, with an annotation :
--       x ⟨y⟩a z
--
-- x and z are always steps.
--
-- The annotation is of the form "a", where:
--   "a" is the symbol for the kind of computation of y.
--
-- E.g.:
--   R₁ ⟨S⟩¹  R₁   "step step step"
--   R₁ ⟨d⟩*  R₂   "step <derivation> step"
--   R₁ ⟨M⟩+  R₂   "step <set-of-steps> step"
--   R₁ ⟨D⟩** R₂   "step <multiderivation> step"
-- etc.
--
-- (2) Function.
--     Written as follows, with an annotation:
--       x a/bc z
--
-- The annotation is of the form "abc", where:
--   "a" is the symbol for the kind of computation of x,
--   "b" is the symbol for the kind of computation of y,
--   "c" is the symbol for the kind of computation of z.
--
-- We will omit "c" except in a few cases with multiderivations.
-- If a = b we write just "b".
--
-- E.g.:
--   R  /¹  S   "step / step          = set-of-steps"
--   R ¹/+  M   "step / set-of-steps  = set-of-steps"
--   R ¹/*  d   "step / derivation    = set-of-steps"
--
--   M +/¹ S   "set-of-steps / step          = set-of-steps"
--   M  /+ M'  "set-of-steps / set-of-steps  = set-of-steps"
--   M +/* d   "set-of-steps / derivation    = set-of-steps"
--
--   d */¹ S  "derivation / step          = derivation"
--   d */+ M  "derivation / set-of-steps  = derivation"
--   d  /* d' "derivation / derivation    = derivation"
-- etc.

-- Residual of a step after a step.
_⟨_⟩¹_ : ∀ {A} → {x₁ x₂ y₁ y₂ : Ob A}
               → Step A x₁ y₁
               → Step A x₁ x₂
               → Step A x₂ y₂
               → Set
_⟨_⟩¹_ {A} R₁ S R₂ = isResidual A R₁ S R₂ 

data derivation : ∀ {A} → Ob A → Ob A → Set where
  ε   : ∀ {A} → {x : Ob A} → derivation {A} x x
  _∷_ : ∀ {A} → {x₁ x₂ x₃ : Ob A}
              → Step A x₁ x₂
              → derivation {A} x₂ x₃
              → derivation {A} x₁ x₃

derivation-source : ∀ {A} {x y} → derivation {A} x y → Ob A
derivation-source {_} {x} {_} _ = x

derivation-target : ∀ {A} {x y} → derivation {A} x y → Ob A
derivation-target {_} {_} {y} _ = y

-- Concatenation of derivations.
infixr 5 _++_

_++_ : ∀ {A} → {x₁ x₂ x₃ : Ob A}
             → derivation {A} x₁ x₂
             → derivation {A} x₂ x₃
             → derivation {A} x₁ x₃
ε       ++ e = e
(R ∷ d) ++ e = R ∷ (d ++ e)

++-ε : ∀ {A} → {x₁ x₂ : Ob A}
             → (d : derivation {A} x₁ x₂)
             → d ++ ε ≡ d
++-ε ε       = refl
++-ε (R ∷ d) = cong (λ x → R ∷ x) (++-ε d)

++-assoc : ∀ {A} → {x₁ x₂ x₃ x₄ : Ob A}
             → (d : derivation {A} x₁ x₂)
             → (e : derivation {A} x₂ x₃)
             → (f : derivation {A} x₃ x₄)
             → d ++ (e ++ f) ≡ (d ++ e) ++ f
++-assoc ε       e f = refl
++-assoc (R ∷ d) e f = cong (λ x → R ∷ x) (++-assoc d e f)
 
-- Residual of a step after a derivation.
_⟨_⟩*_ : ∀ {A} → {x₁ x₂ y₁ y₂ : Ob A}
               → Step A x₁ y₁
               → derivation {A} x₁ x₂ 
               → Step A x₂ y₂
               → Set
_⟨_⟩*_ {A} {x₁} {x₂} {y₁} {y₂} R₁ ε R₂ =
  Σ (y₁ ≡ y₂) (λ { refl → R₁ ≡ R₂})
_⟨_⟩*_ {A} R₁ (_∷_ {A} {x₁} {x₂} {x₃} S d) R₃ =
  Σ[ y₂ ∈ Ob A ] Σ[ R₂ ∈ Step A x₂ y₂ ]
    _⟨_⟩¹_ {A} R₁ S R₂ × R₂ ⟨ d ⟩* R₃
         
-- Functorial lifting of derivations to residual relations.

⟨ε⟩ : ∀ {A} → {x y : Ob A}
             → {R : Step A x y}
             → R ⟨ ε{A} ⟩* R
⟨ε⟩ {A} {x} {y} {R} = refl , refl

_⟨∷⟩_ : ∀ {A} → {x₁ x₂ x₃ : Ob A}
              → {S : Step A x₁ x₂}
              → {d : derivation {A} x₂ x₃}
              → {y₁ y₂ y₃ : Ob A}
              → {R₁ : Step A x₁ y₁}
              → {R₂ : Step A x₂ y₂}
              → {R₃ : Step A x₃ y₃}
              → isResidual A R₁ S R₂
              → R₂ ⟨ d ⟩* R₃
              → R₁ ⟨ S ∷ d ⟩* R₃
_⟨∷⟩_ {A} {x₁} {x₂} {x₃} {R} {d} {y₁} {y₂} {y₃} {R₁} {R₂} p q =
  y₂ , R₂ , p , q

-- Residual after a concatenation

++-residual-right :
   ∀ {A} → {x₁ x₂ x₃ : Ob A}
         → (d₁ : derivation {A} x₁ x₂)
         → (d₂ : derivation {A} x₂ x₃)
         → {y₁ y₃ : Ob A}
         → (R₁ : Step A x₁ y₁)
         → (R₃ : Step A x₃ y₃)
         → R₁ ⟨ (d₁ ++ d₂) ⟩* R₃
         → Σ[ y₂ ∈ Ob A ]
           Σ[ R₂ ∈ Step A x₂ y₂ ]
             R₁ ⟨ d₁ ⟩* R₂ × R₂ ⟨ d₂ ⟩* R₃
++-residual-right ε d₂ {y₁} R₁ R₂ p =
  y₁ , R₁ , ⟨ε⟩ , p
++-residual-right (S ∷ d₁) d₂ R₁ R₃ (y₄ , R₄ , p , q) =
 let y₂ , R₂ , q₁ , q₂ = ++-residual-right d₁ d₂ R₄ R₃ q in
   y₂ , R₂ , p ⟨∷⟩ q₁ , q₂
   
-- Outgoing steps from a term.

out-step : ∀ {A} → Ob A → Set
out-step {A} x = Σ[ y ∈ Ob A ] Step A x y

transport-derivation-source :
  ∀ {A x y z}
    → x ≡ y
    → derivation {A} x z
    → derivation {A} y z
transport-derivation-source refl d = d

