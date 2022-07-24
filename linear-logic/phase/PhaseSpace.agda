
module PhaseSpace where

-- A phase space is a commutative monoid with a distinguished set called the "pole".
-- In this formalization, the carrier set is a setoid (i.e. we work up to -- an
-- explicit equivalence relation "=="). This is why we need to postulate
-- reflexivity, symmetry, transitivity, and two forms of congruence.
--
-- We use a setoid specifically in order to be able to (eventually) prove
-- completeness of MELL with respect to phase semantics, as in this
-- construction one builds a model whose carrier set is a quotient of the set
-- of all sequents.

open import Relation.Binary.PropositionalEquality
                         using (_≡_)
open import Data.Product using (Σ-syntax; _,_)

open import Subset using (
                     subset; _∈_; _⊆_; _≃_; subset-comprehension-syntax;
                     ⊆-trans
                   )

infix   60 _⊥
infix   60 _==_
infixl  70 _∙_

record PhaseSpace : Set₁ where
  infix   60 _==_
  infixl  70 _∙_
  field
    ---- Structure
    M         : Set
    pole      : subset M
    _==_      : M → M → Set
    e         : M
    _∙_       : M → M → M
    ---- Properties
    ==-refl      : ∀ {x} → x == x
    ==-sym       : ∀ {x y} → x == y → y == x
    ==-trans     : ∀ {x y z} → x == y → y == z → x == z
    ==-cong-∙    : ∀ {x x' y y'} → x == x' → y == y' → x ∙ y == x' ∙ y'
    ==-cong-pole : ∀ {x y} → x == y → x ∈ pole → y ∈ pole
    e-neut-l     : ∀ {x} → e ∙ x == x
    e-neut-r     : ∀ {x} → x ∙ e == x
    ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z == x ∙ (y ∙ z)
    ∙-comm       : ∀ {x y} → x ∙ y == y ∙ x
    
---- Phase spaces with typeclasses

-- Structure
    
M : ∀ ⦃ _ ⦄ → Set
M ⦃ PS ⦄ = PhaseSpace.M PS 

pole : ∀ ⦃ _ ⦄ → subset M
pole ⦃ PS ⦄ = PhaseSpace.pole PS

_==_ : ∀ ⦃ _ ⦄ → M → M → Set
_==_ ⦃ PS ⦄ x y = PhaseSpace._==_ PS x y

e : ∀ ⦃ _ ⦄ → M
e ⦃ PS ⦄ = PhaseSpace.e PS

_∙_ : ∀ ⦃ _ ⦄ → M → M → M
_∙_ ⦃ PS ⦄ x y = PhaseSpace._∙_ PS x y

-- Properties

==-refl : ∀ ⦃ _ ⦄ {x : M} → x == x
==-refl ⦃ PS ⦄ = PhaseSpace.==-refl PS

==-sym : ∀ ⦃ _ ⦄ {x y : M} → x == y → y == x
==-sym ⦃ PS ⦄ x==y = PhaseSpace.==-sym PS x==y

==-trans : ∀ ⦃ _ ⦄ {x y z : M} → x == y → y == z → x == z
==-trans ⦃ PS ⦄ x==y y==z = PhaseSpace.==-trans PS x==y y==z

==-cong-∙ : ∀ ⦃ _ ⦄ {x x' y y' : M} → x == x' → y == y' → x ∙ y == x' ∙ y'
==-cong-∙ ⦃ PS ⦄ x==x' y==y' = PhaseSpace.==-cong-∙ PS x==x' y==y'

==-cong-pole : ∀ ⦃ _ ⦄ {x y : M} → x == y → x ∈ pole → y ∈ pole
==-cong-pole ⦃ PS ⦄ x==y x∈pole = PhaseSpace.==-cong-pole PS x==y x∈pole

e-neut-l : ∀ ⦃ _ ⦄ {x : M} → e ∙ x == x
e-neut-l ⦃ PS ⦄ = PhaseSpace.e-neut-l PS

e-neut-r : ∀ ⦃ _ ⦄ {x : M} → x ∙ e == x
e-neut-r ⦃ PS ⦄ = PhaseSpace.e-neut-r PS

∙-assoc : ∀ ⦃ _ ⦄ {x y z : M} → (x ∙ y) ∙ z == x ∙ (y ∙ z)
∙-assoc ⦃ PS ⦄ = PhaseSpace.∙-assoc PS

∙-comm : ∀ ⦃ _ ⦄ {x y : M} → x ∙ y == y ∙ x
∙-comm ⦃ PS ⦄ = PhaseSpace.∙-comm PS

---- Definition of the "perp" operator
    
_⊥ : ⦃ PS : PhaseSpace ⦄ → subset M → subset M
A ⊥ = [ x ∷ (∀ {y} → y ∈ A → (x ∙ y) ∈ pole) ]

---- Basic lemmas regarding the "perp" operator

⊥-contravariant : ⦃ _ : PhaseSpace ⦄ {A B : subset M}
                → A ⊆ B
                → B ⊥ ⊆ A ⊥
⊥-contravariant A⊆B x∈B⊥ y∈A = x∈B⊥ (A⊆B y∈A)

A⊆A⊥⊥ : ⦃ _ : PhaseSpace ⦄ {A : subset M}
      → A ⊆ A ⊥ ⊥
A⊆A⊥⊥ x∈A y∈A⊥ = ==-cong-pole ∙-comm (y∈A⊥ x∈A)

A⊥⊥⊥⊆A⊥ : ⦃ _ : PhaseSpace ⦄ {A : subset M}
        → A ⊥ ⊥ ⊥ ⊆ A ⊥
A⊥⊥⊥⊆A⊥ = ⊥-contravariant A⊆A⊥⊥

-- A fact is a subset A of the monoid that can
-- be written as of the form A ≃ B ⊥.
-- Note that, to avoid assuming functional extensionality,
-- we use mutual inclusion ("≃") rather than equality.
is-fact : ⦃ _ : PhaseSpace ⦄ → subset M → Set₁
is-fact A = Σ[ B ∈ subset M ] (A ≃ B ⊥)

-- Equivalently, A is a fact iff A ≃ A ⊥ ⊥.

fact-A⊥⊥⊆A : ⦃ _ : PhaseSpace ⦄ {A : subset M}
           → is-fact A
           → A ⊥ ⊥ ⊆ A
fact-A⊥⊥⊆A (B , A⊆B⊥ , B⊥⊆A) =
  λ x∈A⊥⊥ → B⊥⊆A (A⊥⊥⊥⊆A⊥ (⊥-contravariant (⊥-contravariant A⊆B⊥) x∈A⊥⊥))

fact-A≃A⊥⊥ : ⦃ _ : PhaseSpace ⦄ {A : subset M}
           → is-fact A
           → A ≃ A ⊥ ⊥
fact-A≃A⊥⊥ A-fact = A⊆A⊥⊥ , fact-A⊥⊥⊆A A-fact

