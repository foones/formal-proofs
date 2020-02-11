module Utils where

import Data.List as L
open import Level
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Data.Nat
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Function

open import Data.Bool.Properties using (not-¬; ¬-not; T-≡; T-∧; T-∨)
import Function.Equivalence as Equiv
open import Function.Equality using (_⟨$⟩_)

---- Empty type

data 𝟘 {ℓ} : Set ℓ where

𝟘-elim : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → 𝟘 {ℓ₂} → A
𝟘-elim ()

---- Type equivalence

isLinv : ∀ {ℓ} {A B : Set ℓ} → (g : B → A) → (f : A → B) → Set ℓ
isLinv g f = ∀ x → g (f x) ≡ x

_≃_ : ∀ {ℓ} → Set ℓ → Set ℓ → Set ℓ
A ≃ B = Σ[ f ∈ (A → B) ] (
          (Σ[ g ∈ (B → A) ] isLinv g f)
          ×
          (Σ[ h ∈ (B → A) ] isLinv f h)
        )

---- Bool

true≢false : ¬(true ≡ false)
true≢false p = not-¬ p refl

false≢true : ¬(false ≡ true)
false≢true p = not-¬ p refl

∧-×-true : ∀ {x y} → x ∧ y ≡ true → (x ≡ true) × (y ≡ true)
∧-×-true p =
  let (p₁ , p₂) = Equiv.Equivalence.to T-∧ ⟨$⟩ (Equiv.Equivalence.from T-≡ ⟨$⟩ p)
    in Equiv.Equivalence.to T-≡ ⟨$⟩ p₁ , Equiv.Equivalence.to T-≡ ⟨$⟩ p₂

×-∧-true : ∀ {x y} → (x ≡ true) × (y ≡ true) → x ∧ y ≡ true
×-∧-true (p₁ , p₂) =
  let p = Equiv.Equivalence.from T-∧ ⟨$⟩ (Equiv.Equivalence.from T-≡ ⟨$⟩ p₁ ,
                                          Equiv.Equivalence.from T-≡ ⟨$⟩ p₂)
    in Equiv.Equivalence.to T-≡ ⟨$⟩ p

false⇒not-true : ∀ {x} → x ≡ false → not x ≡ true
false⇒not-true p = cong not p

not-not-id : ∀ {x} → not (not x) ≡ x
not-not-id {x = true}  = refl
not-not-id {x = false} = refl

not-true⇒false : ∀ {x} → not x ≡ true → x ≡ false
not-true⇒false p = trans (sym not-not-id) (cong not p)

¬-true⇒false : ∀ {x} → ¬ (x ≡ true) → x ≡ false
¬-true⇒false {x = true}  p = ⊥-elim (p refl)
¬-true⇒false {x = false} p = refl

bool-is-set : ∀ {x y : Bool} → {p q : x ≡ y} → p ≡ q
bool-is-set {true}  {true}  {refl} {refl} = refl
bool-is-set {true}  {false} {p}           = ⊥-elim (true≢false p)
bool-is-set {false} {true}  {p}           = ⊥-elim (false≢true p)
bool-is-set {false} {false} {refl} {refl} = refl

---- "inspect" idiom
---- (cf. https://agda.readthedocs.io/en/latest/language/with-abstraction.html#nested-with-abstractions)

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

analyze : ∀ {a} {A : Set a} (x : A) → Singleton x
analyze x = x with≡ refl

---- Lists

list∈ : ∀ {ℓ} {A} → A → L.List {ℓ} A → Set ℓ
list∈ _ L.[]       = 𝟘
list∈ x (y L.∷ ys) = x ≡ y ⊎ list∈ x ys

list∈-++ : {A : Set} → {a : A} → {xs ys : L.List A}
                     → list∈ a (xs L.++ ys)
                     → list∈ a xs ⊎ list∈ a ys
list∈-++ {xs = L.[]}      p        = inj₂ p
list∈-++ {xs = x L.∷ xs'} (inj₁ p) = inj₁ (inj₁ p)
list∈-++ {xs = x L.∷ xs'} (inj₂ p) with list∈-++ {xs = xs'} p
... | inj₁ q = inj₁ (inj₂ q)
... | inj₂ q = inj₂ q

list∈-++L : ∀ {ℓ} {A}
                  → {z : A}
                  → {xs ys : L.List {ℓ} A}
                  → list∈ z xs
                  → list∈ z (xs L.++ ys)
list∈-++L {xs = L.[]}    z∈[] = 𝟘-elim z∈[]
list∈-++L {xs = _ L.∷ _} z∈x∷xs'
  with z∈x∷xs'
... | inj₁ z≡x   = inj₁ z≡x
... | inj₂ z∈xs' = inj₂ (list∈-++L z∈xs')

list∈-++R : ∀ {ℓ} {A}
                  → {z : A}
                  → {xs ys : L.List {ℓ} A}
                  → list∈ z ys
                  → list∈ z (xs L.++ ys)
list∈-++R {xs = L.[]}    z∈ys = z∈ys
list∈-++R {xs = _ L.∷ _} z∈ys = inj₂ (list∈-++R z∈ys)


list-map-correct : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
                     → (f : A → B)
                     → (a : A)
                     → (xs : L.List A)
                     → (a∈xs : list∈ a xs)
                     → list∈ (f a) (L.map f xs)
list-map-correct _ _ L.[]       a∈[]   = 𝟘-elim a∈[]
list-map-correct f a (x L.∷ xs) a∈x∷xs
  with a∈x∷xs
... | inj₁ refl = inj₁ refl
... | inj₂ a∈xs = inj₂ (list-map-correct f a xs a∈xs)

cons-nonempty : ∀ {ℓ} {A : Set ℓ} (x : A) (xs : L.List A) → ¬ x L.∷ xs ≡ L.[]
cons-nonempty _ _ ()

---- Numbers
  
1+n≰0 : {n : ℕ} → ¬(1 + n ≤ 0)
1+n≰0 ()

1+n≢0 : {n : ℕ} → ¬(1 + n ≡ 0)
1+n≢0 ()

n≢0⇒n=1+m : {n : ℕ} → ¬(n ≡ 0) → Σ[ m ∈ ℕ ] n ≡ 1 + m
n≢0⇒n=1+m {ℕ.zero}  e = ⊥-elim (e refl)
n≢0⇒n=1+m {ℕ.suc n} _ = n , refl

1+n≤1+m⇒n≤m : {n m : ℕ} → 1 + n ≤ 1 + m → n ≤ m
1+n≤1+m⇒n≤m (s≤s n≤m) = n≤m

≡∘≤ : ∀ {a b c : ℕ} → a ≡ b → b ≤ c → a ≤ c
≡∘≤ refl p = p

≤∘≡ : ∀ {a b c : ℕ} → a ≤ b → b ≡ c → a ≤ c
≤∘≡ p refl = p

---- Equivalence relation

record is-equivalence-relation {ℓ} {A : Set ℓ} (R : A → A → Set ℓ) : Set ℓ
  where
    constructor is-equivalence-relation-proof
    field
      eqv-refl  : ∀ {a} → R a a
      eqv-sym   : ∀ {a b} → R a b → R b a
      eqv-trans : ∀ {a b c} → R a b → R b c → R a c

equivalence-relation : ∀ {ℓ} → Set ℓ → Set (Level.suc ℓ)
equivalence-relation {ℓ} A =
  Σ[ R ∈ (A → A → Set ℓ) ]
    is-equivalence-relation R

---- Transport

transport : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) {a b : A} (p : a ≡ b) → P a → P b
transport _ refl x = x

-- Equality for other levels

data _≡'_ {ℓ} : ∀ {A : Set ℓ} (a b : A) → Set ℓ where
  refl' : ∀ {A : Set ℓ} {a : A} → a ≡' a
  
infixr 10 _≡'⟨_⟩_
infixr 15 _∎'

_∎' : ∀ {ℓ} {A : Set ℓ} (a : A) → a ≡' a
_ ∎' = refl'

_≡'⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} (a : A)
            → {b : A} → a ≡' b
            → {c : A} → b ≡' c
            → a ≡' c
_ ≡'⟨ refl' ⟩ refl' = refl'

-- Heterogeneous equality

_≡[_]_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} {a b : A}
           → (x : P a) → (p : a ≡ b) → (y : P b)
           → Set ℓ₂
_≡[_]_ x p y = transport _ p x ≡ y

cong² : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Set ℓ₁} {B : A → Set ℓ₂} {C : Set ℓ₃}
        → (f : (a : A) → B a → C)
        → {a₁ a₂ : A}
        → (p : a₁ ≡ a₂)
        → {b₁ : B a₁} {b₂ : B a₂}
        → (q : b₁ ≡[ p ] b₂)
        → f a₁ b₁ ≡ f a₂ b₂
cong² _ refl refl = refl

postulate
    funext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
               {f g : (a : A) → B a}
           → (∀ x → f x ≡ g x)
           → f ≡ g

    funext* : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : A → Set ℓ₂}
                {f g : (a : A) → B a}
            → (∀ x → f x ≡ g x)
            → (λ {x} → f x) ≡ (λ {x} → g x)
