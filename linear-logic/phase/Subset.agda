
module Subset where

-- We define the type of "subsets" of a type X as the type of
-- predicates X → Set.
-- This definition is naive in that we do not require the predicates to
-- be propositional.

open import Data.Product using (_×_; _,_)

infix 50 _∈_ _⊆_

subset : Set → Set₁
subset X = X → Set

_∈_ : ∀ {X} → X → subset X → Set
x ∈ A = A x

_⊆_ : ∀ {X} → subset X → subset X → Set
A ⊆ B = ∀ {x} → x ∈ A → x ∈ B

_≃_ : ∀ {X} → subset X → subset X → Set
A ≃ B = (A ⊆ B) × (B ⊆ A)

subset-comprehension-syntax : ∀ {X} → (X → Set) → subset X
subset-comprehension-syntax f = f

syntax subset-comprehension-syntax (λ x → e) = [ x ∷ e ]

⊆-refl : ∀ {X} {A : subset X} → A ⊆ A
⊆-refl x∈A = x∈A

⊆-trans : ∀ {X} {A B C : subset X}
          → A ⊆ B
          → B ⊆ C
          → A ⊆ C
⊆-trans A⊆B B⊆C x∈A = B⊆C (A⊆B x∈A)

≃-refl : ∀ {X} {A : subset X} → A ≃ A
≃-refl {A = A} = ⊆-refl {A = A} , ⊆-refl {A = A}

