
--
-- A straightforward backtracking-based SAT solver, together with
-- a proof of correctness/completeness.
--

open import Data.Empty using (⊥-elim)
open import Data.Nat   using (ℕ; zero; suc)
open import Data.Bool  using (Bool; true; false)
open import Data.List  using (List; []; _∷_; _++_; map)

open import Relation.Nullary     using (¬_)
open import Relation.Binary.Core using (_≡_; refl)

-- Booleanos

_and_ : Bool → Bool → Bool
true  and x = x
false and x = false

-- Maybe

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

-- Para el "inspect idiom"
--   https://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html#the-inspect-idiom

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

-- Conjuntos finitos

data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (suc n)
  fs : {n : ℕ} → Fin n → Fin (suc n)

-- Fórmulas

data Formula (n : ℕ) : Set where
  const : Bool → Formula n
  var   : Fin n → Formula n
  _∧_   : Formula n → Formula n → Formula n
  
-- Valuación de una fórmula

data Interpretation : ℕ → Set where
  ⟨⟩  : Interpretation zero
  _∙_ : {n : ℕ} → Bool → Interpretation n → Interpretation (suc n)

_⟨_⟩ : {n : ℕ} → Interpretation n → Fin n → Bool
(b ∙ _) ⟨ fz ⟩   = b
(_ ∙ i) ⟨ fs x ⟩ = i ⟨ x ⟩
  
eval : {n : ℕ} → Interpretation n → Formula n → Bool
eval i (const b) = b
eval i (var x)   = i ⟨ x ⟩
eval i (f₁ ∧ f₂) = eval i f₁ and eval i f₂
  
-- SAT solver

all : {n : ℕ} → List (Interpretation n)
all {zero}  = ⟨⟩ ∷ []
all {suc n} = map (false  ∙_) all ++ map (true ∙_) all

lookup-model : {n : ℕ}
             → Formula n
             → List (Interpretation n)
             → Maybe (Interpretation n)
lookup-model f []       = nothing
lookup-model f (i ∷ is) with eval i f
... | true  = just i
... | false = lookup-model f is

solve : {n : ℕ} → Formula n → Maybe (Interpretation n)
solve f = lookup-model f all

-- Correctitud

lookup-model-correct :
  {n : ℕ} {f : Formula n} (is : List (Interpretation n)) {i : Interpretation n}
  → lookup-model f is ≡ just i
  → eval i f ≡ true
lookup-model-correct {_} {f} (i₁ ∷ is) {i₂} p with inspect (eval i₁ f)
... | false with≡ q rewrite q = lookup-model-correct is p
... | true  with≡ q rewrite q with p
...    | refl = q

solve-correct : {n : ℕ} {f : Formula n} {i : Interpretation n}
              → solve f ≡ just i
              → eval i f ≡ true
solve-correct = lookup-model-correct all

-- Completitud

data _∈_ {A : Set} : A → List A → Set where
  ∈-zero : {x y : A} {ys : List A} → x ≡ y  → x ∈ (y ∷ ys)
  ∈-suc  : {x y : A} {ys : List A} → x ∈ ys → x ∈ (y ∷ ys)
  
just≢nothing : {A : Set} {a : A} → ¬(just a ≡ nothing)
just≢nothing ()

lookup-model-complete :
  {n : ℕ} {f : Formula n} (is : List (Interpretation n)) {i : Interpretation n}
  → i ∈ is
  → lookup-model f is ≡ nothing
  → eval i f ≡ false
lookup-model-complete {_} {f} (i₁ ∷ is) (∈-zero refl) p
  with inspect (eval i₁ f)
... | true  with≡ q rewrite q = ⊥-elim (just≢nothing p)
... | false with≡ q rewrite q = refl
lookup-model-complete {_} {f} (i₁ ∷ is) {i₂} (∈-suc i₂∈is) p
  with inspect (eval i₁ f)
... | true  with≡ q rewrite q = ⊥-elim (just≢nothing p)
... | false with≡ q rewrite q = lookup-model-complete is i₂∈is p

∈-map : {A B : Set} {f : A → B} {xs : List A} {a : A}
      → a ∈ xs
      → f a ∈ map f xs
∈-map {xs = []}    ()
∈-map {xs = _ ∷ _} (∈-zero refl) = ∈-zero refl
∈-map {xs = _ ∷ _} (∈-suc a∈xs)  = ∈-suc (∈-map a∈xs)

∈-++-left : {A : Set} {xs ys : List A} {a : A}
          → a ∈ xs
          → a ∈ (xs ++ ys)
∈-++-left {_} {[]}     ()
∈-++-left {_} {_ ∷ _} (∈-zero refl) = ∈-zero refl
∈-++-left {_} {_ ∷ _} (∈-suc p)     = ∈-suc (∈-++-left p)

∈-++-right : {A : Set} {xs ys : List A} {a : A}
           → a ∈ ys
           → a ∈ (xs ++ ys)
∈-++-right {_} {[]}    a∈ys = a∈ys
∈-++-right {_} {_ ∷ _} a∈ys = ∈-suc (∈-++-right a∈ys)

∈-all : {n : ℕ} {i : Interpretation n} → i ∈ all
∈-all {zero}  {⟨⟩}        = ∈-zero refl
∈-all {suc n} {false ∙ i} = ∈-++-left  {_} {map (_∙_ false) all} {_} (∈-map ∈-all)
∈-all {suc n} {true  ∙ i} = ∈-++-right {_} {map (_∙_ false) all} {_} (∈-map ∈-all)

solve-complete : {n : ℕ} {f : Formula n} {i : Interpretation n}
               → solve f ≡ nothing
               → eval i f ≡ false
solve-complete p = lookup-model-complete all ∈-all p

