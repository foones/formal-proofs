
module LL where

-- A formalization of one-sided Multiplicative Linear Logic.

open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl; sym; trans; cong)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Nat     using (ℕ)
open import Data.Bool    using (Bool; true; false)

infix   50 ⊢_ _~_
infixl  70 _++_
infixl  80 _,,_
infixl  90 _⊗_ _⅋_

---- Auxiliary functions

cong₂ : ∀ {A B C : Set}
        → (f : A → B → C) → {a₁ a₂ : A} {b₁ b₂ : B}
        → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ _ refl refl = refl

---- Formulae

data Form : Set where
  b+    : ℕ → Form            -- Base type (positive)
  b-    : ℕ → Form            -- Base type (negative)
  _⊗_   : Form → Form → Form  -- Tensor
  _⅋_   : Form → Form → Form  -- Par

variable A A⊥ B B⊥ C C⊥ : Form

---- Duality

-- `dual A B` is an inductive predicate meaning that
-- the formulae A and B are dual to each other.

data dual : Form → Form → Set where
  dual-b+ : ∀ {x} → dual (b+ x) (b- x)
  dual-b- : ∀ {x} → dual (b- x) (b+ x)
  dual-⊗  : dual A A⊥ → dual B B⊥ → dual (A ⊗ B) (A⊥ ⅋ B⊥)
  dual-⅋  : dual A A⊥ → dual B B⊥ → dual (A ⅋ B) (A⊥ ⊗ B⊥)
  
dual-dual : dual A B → dual B C → A ≡ C
dual-dual dual-b+        dual-b-        = refl
dual-dual dual-b-        dual-b+        = refl
dual-dual (dual-⊗ p₁ p₂) (dual-⅋ q₁ q₂) = cong₂ _⊗_ (dual-dual p₁ q₁) (dual-dual p₂ q₂)
dual-dual (dual-⅋ p₁ p₂) (dual-⊗ q₁ q₂) = cong₂ _⅋_ (dual-dual p₁ q₁) (dual-dual p₂ q₂)

dual-sym : dual A B → dual B A
dual-sym dual-b+        = dual-b-
dual-sym dual-b-        = dual-b+
dual-sym (dual-⊗ dA dB) = dual-⅋ (dual-sym dA) (dual-sym dB)
dual-sym (dual-⅋ dA dB) = dual-⊗ (dual-sym dA) (dual-sym dB)

---- Sequents

-- A sequent is a snoc-list of formulae.
data Seq : Set where
  ∅    : Seq
  _,,_ : Seq → Form → Seq

variable Γ Γ' Γ₁ Γ₁' Γ₂ Γ₂' Γ₃ Δ Δ' Δ₁ Δ₂ Δ₃ Σ : Seq

-- Concatenation of sequents

_++_ : Seq → Seq → Seq
Γ₁ ++ ∅       = Γ₁
Γ₁ ++ Γ₂ ,, A = (Γ₁ ++ Γ₂) ,, A

++-∅-neutl : ∅ ++ Γ ≡ Γ
++-∅-neutl {∅}      = refl
++-∅-neutl {Γ ,, _} = cong (_,, _) ++-∅-neutl

++-assoc : Γ₁ ++ (Γ₂ ++ Γ₃) ≡ (Γ₁ ++ Γ₂) ++ Γ₃ 
++-assoc {Γ₃ = ∅}       = refl
++-assoc {Γ₃ = Γ₃ ,, _} = cong (_,, _) (++-assoc {Γ₃ = Γ₃})

---- Equivalence of sequents up to exchange

-- `Γ ~ Δ` is an equivalence relation meaning that
-- Γ is a permutation of Δ.
data _~_ : Seq → Seq → Set where
  ~-refl  : Γ ~ Γ                         -- Reflexivity.
  ~-sym   : Γ₁ ~ Γ₂ → Γ₂ ~ Γ₁             -- Symmetry.
  ~-trans : Γ₁ ~ Γ₂ → Γ₂ ~ Γ₃ → Γ₁ ~ Γ₃   -- Transitivity.
  ~-swap  : Γ ,, A ,, B ~ Γ ,, B ,, A     -- Swapping (at the root).
  ~-dip   : Γ₁ ~ Γ₂ → Γ₁ ,, A ~ Γ₂ ,, A   -- Congruence below snoc.

-- Properties of _~_

~-eq : Γ₁ ≡ Γ₂ → Γ₁ ~ Γ₂
~-eq refl = ~-refl

~-eq-empty : Γ ~ ∅ → Γ ≡ ∅
~-eq-empty p = ~-eq-empty' true p
  where
    T : Bool → Seq → Set
    T true  Γ = Γ ~ ∅
    T false Γ = ∅ ~ Γ
    ~-eq-empty' : (b : Bool) → T b Γ → Γ ≡ ∅
    ~-eq-empty' true  ~-refl          = refl
    ~-eq-empty' true  (~-sym p)       = ~-eq-empty' false p
    ~-eq-empty' true  (~-trans p₁ p₂)
      with ~-eq-empty' true p₂
    ... | refl = ~-eq-empty' true p₁
    ~-eq-empty' false ~-refl          = refl
    ~-eq-empty' false (~-sym p)       = ~-eq-empty' true p
    ~-eq-empty' false (~-trans p₁ p₂)
      with ~-eq-empty' false p₁
    ... | refl = ~-eq-empty' false p₂

~-rotate¹r : Γ ,, A ++ Δ ~ Γ ++ Δ ,, A
~-rotate¹r {Δ = ∅}      = ~-refl
~-rotate¹r {Δ = _ ,, _} = ~-trans (~-dip ~-rotate¹r) ~-swap

~-rotate¹l : Γ ++ Δ ,, A ~ Γ ,, A ++ Δ
~-rotate¹l = ~-sym ~-rotate¹r

~-++-congl : Γ₁ ~ Γ₁' → Γ₁ ++ Γ₂ ~ Γ₁' ++ Γ₂
~-++-congl {Γ₂ = ∅}       p = p
~-++-congl {Γ₂ = Γ₂ ,, _} p = ~-dip (~-++-congl {Γ₂ = Γ₂} p)

~-++-congr : Γ₂ ~ Γ₂' → Γ₁ ++ Γ₂ ~ Γ₁ ++ Γ₂'
~-++-congr ~-refl         = ~-refl
~-++-congr (~-sym p)      = ~-sym (~-++-congr p)
~-++-congr (~-trans p q)  = ~-trans (~-++-congr p) (~-++-congr q)
~-++-congr ~-swap         = ~-swap
~-++-congr (~-dip p)      = ~-dip (~-++-congr p)

~-++-cong : Γ₁ ~ Γ₁' → Γ₂ ~ Γ₂' → Γ₁ ++ Γ₂ ~ Γ₁' ++ Γ₂'
~-++-cong p q = ~-trans (~-++-congl p) (~-++-congr q)

~-++-assoc : Γ₁ ++ (Γ₂ ++ Γ₃) ~ Γ₁ ++ Γ₂ ++ Γ₃
~-++-assoc {Γ₃ = Γ₃} = ~-eq (++-assoc {Γ₃ = Γ₃})

~-++-comm : Γ₁ ++ Γ₂ ~ Γ₂ ++ Γ₁
~-++-comm {Γ₂ = ∅}       = ~-eq (sym ++-∅-neutl)
~-++-comm {Γ₂ = Γ₂ ,, _} = ~-trans (~-dip (~-++-comm {Γ₂ = Γ₂})) ~-rotate¹l

~-rotate132 : Γ₁ ++ Γ₂ ++ Γ₃ ~ Γ₁ ++ Γ₃ ++ Γ₂
~-rotate132 {Γ₁} {Γ₂} {Γ₃} =
  ~-trans
    (~-sym (~-++-assoc {Γ₂ = Γ₂} {Γ₃ = Γ₃}))
    (~-trans (~-++-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂ ++ Γ₃} ~-refl (~-++-comm {Γ₁ = Γ₂}))
             (~-++-assoc {Γ₂ = Γ₃} {Γ₃ = Γ₂}))

~-rotate312 : Γ₁ ++ Γ₂ ++ Γ₃ ~ Γ₃ ++ Γ₁ ++ Γ₂
~-rotate312 {Γ₁} {Γ₂} {Γ₃} =
  ~-trans
    (~-++-comm {Γ₁ = Γ₁ ++ Γ₂} {Γ₂ = Γ₃})
    (~-++-assoc {Γ₃ = Γ₂})

~-rotate213 : Γ₁ ++ Γ₂ ++ Γ₃ ~ Γ₂ ++ Γ₁ ++ Γ₃
~-rotate213 {Γ₁} {Γ₂} {Γ₃} =
  ~-++-congl {Γ₂ = Γ₃} (~-++-comm {Γ₁ = Γ₁} {Γ₂ = Γ₂})

~-cons-snoc : Γ ,, A ~ ∅ ,, A ++ Γ
~-cons-snoc {Γ = ∅}      = ~-refl
~-cons-snoc {Γ = _ ,, _} = ~-trans ~-swap (~-dip ~-cons-snoc)

---- Multiplicative Linear Logic

-- `⊢ Γ` is a predicate meaning that Γ is provable in
-- the multiplicative fragment of linear logic.
-- The exchange rule allows arbitrary permutations of
-- the sequent, using the binary relation _~_ defined above.
data ⊢_ : Seq → Set where
  ax : dual A A⊥
     → ⊢ ∅ ,, A ,, A⊥
  i⊗ : ⊢ Γ₁ ,, A
     → ⊢ Γ₂ ,, B
     → ⊢ Γ₁ ++ Γ₂ ,, A ⊗ B
  i⅋ : ⊢ Γ ,, A ,, B
     → ⊢ Γ ,, A ⅋ B
  ex : ⊢ Γ₁
     → Γ₁ ~ Γ₂
     → ⊢ Γ₂
  cut : dual A A⊥
      → ⊢ Γ₁ ,, A
      → ⊢ Γ₂ ,, A⊥
      → ⊢ Γ₁ ++ Γ₂
      
