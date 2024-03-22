
---- Equivalence between:
---- - structural recursion (foldr)
---- - iterative recursion  (foldl)
---- - primitive recursion  (recr)

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List    using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

----

FunctionalExtensionality : Set₁
FunctionalExtensionality = {A : Set} {B : A → Set} {f g : (x : A) → B x}
                         → (∀ x → f x ≡ g x)
                         → f ≡ g
                         
postulate funext : FunctionalExtensionality

proj₁-≡ : ∀ {A B : Set} {p q : A × B}
        → p ≡ q → proj₁ p ≡ proj₁ q 
proj₁-≡ refl = refl

proj₂-≡ : ∀ {A B : Set} {p q : A × B}
        → p ≡ q → proj₂ p ≡ proj₂ q 
proj₂-≡ refl = refl

----

foldr : ∀ {a b : Set} → (a → b → b) → b → List a → b
foldr _ z []       = z
foldr f z (x ∷ xs) = f x (foldr f z xs)

foldl : ∀ {a b : Set} → (b → a → b) → b → List a → b
foldl _ z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

recr : ∀ {a b : Set} → (a → List a → b → b) → b → List a → b
recr _ z []       = z
recr f z (x ∷ xs) = f x xs (recr f z xs)

---- Structural vs. iterative recursion ----

-- foldl in terms of foldr
foldl2 : ∀ {a b : Set} → (b → a → b) → b → List a → b
foldl2 {a} {b} f z xs = foldr {a} {b → b}
                              (λ x rec ac → rec (f ac x))
                              (λ x → x)
                              xs
                              z

-- foldl ≡ foldl2 (immediate)
foldl≡foldl2 : ∀ {a b : Set} (f : b → a → b) (z : b) (xs : List a)
               → foldl f z xs ≡ foldl2 f z xs
foldl≡foldl2 f z []       = refl
foldl≡foldl2 f z (x ∷ xs) = foldl≡foldl2 f (f z x) xs

-- foldr in terms of foldl
foldri : ∀ {a b : Set} → (a → b → b) → b → List a → b
foldri {a} {b} f z xs = foldl {a} {b → b}
                              (λ rec x ac → rec (f x ac))
                              (λ x → x)
                              xs
                              z

-- Auxiliary property
foldr-last : ∀ {a b : Set} (f : a → b → b) (z : b) (xs : List a) (y : a)
             → foldr f z (xs ++ y ∷ []) ≡ foldr f (f y z) xs
foldr-last f z []       y = refl
foldr-last f z (x ∷ xs) y = cong (f x) (foldr-last f z xs y)

-- foldr ≡ foldri, generalized to be able to reason inductively
foldr≡foldri* : ∀ {a b : Set} (f : a → b → b) (z : b) (xs ys : List a)
                → foldr f (foldr f z ys) xs ≡
                  foldl (λ rec x ac → rec (f x ac))
                        (λ ac → foldr f ac xs)
                        ys
                        z
foldr≡foldri* f z xs []       = refl
foldr≡foldri* f z xs (y ∷ ys) =
  begin
    foldr f (f y (foldr f z ys)) xs
  ≡⟨ sym (foldr-last f (foldr f z ys) xs y) ⟩
    foldr f (foldr f z ys) (xs ++ y ∷ []) 
  ≡⟨ foldr≡foldri* f z (xs ++ y ∷ []) ys ⟩
    foldl (λ z z₁ x → z (f z₁ x)) (λ x → foldr f x (xs ++ y ∷ [])) ys z
  ≡⟨ cong (λ □ → foldl (λ rec x ac → rec (f x ac)) □ ys z)
          (funext λ x → foldr-last f x xs y) ⟩
    foldl (λ z z₁ x → z (f z₁ x)) (λ x → foldr f (f y x) xs) ys z 
  ∎

-- foldr ≡ foldri, instantiating the preceding lemma
foldr≡foldri : ∀ {a b : Set} (f : a → b → b) (z : b) (xs : List a)
               → foldr f z xs ≡ foldri f z xs
foldr≡foldri f z xs = foldr≡foldri* f z [] xs

---- Structural vs. primitive recursion ----

-- foldr in terms of recr
foldrr : ∀ {a b : Set} → (a → b → b) → b → List a → b
foldrr f z = recr (λ x xs rec → f x rec) z

-- foldr ≡ foldrr (immediate)
foldr≡foldrr : ∀ {a b : Set} (f : a → b → b) (z : b) (xs : List a)
               → foldr f z xs ≡ foldrr f z xs
foldr≡foldrr f z []       = refl
foldr≡foldrr f z (x ∷ xs) = cong (f x) (foldr≡foldrr f z xs)

-- recr in terms of foldr
recr2 : ∀ {a b : Set} → (a → List a → b → b) → b → List a → b
recr2 {a} {b} f z xs = proj₂ (foldr {a} {List a × b}
                               (λ { x (xs , rec) → x ∷ xs , f x xs rec })
                               ([] , z)
                               xs)

-- recr ≡ recr2, generalized to be able to reason inductively
recr≡recr2* : ∀ {a b : Set} (f : a → List a → b → b) (z : b) (xs : List a)
               → (xs , recr f z xs) ≡
                 foldr {a} {List a × b}
                   (λ { x (xs , rec) → x ∷ xs , f x xs rec })
                   ([] , z)
                   xs
recr≡recr2* f z []       = refl
recr≡recr2* f z (x ∷ xs) =
  let xs-rec   = foldr (λ { x (xs , rec) → x ∷ xs , f x xs rec }) ([] , z) xs
      xs'      = proj₁ xs-rec
      rec'     = proj₂ xs-rec
      xs≡xs'   = proj₁-≡ (recr≡recr2* f z xs)
      rec≡rec' = proj₂-≡ (recr≡recr2* f z xs)
    in begin
         (x ∷ xs , f x xs (recr f z xs))
       ≡⟨ cong (λ □ → (x ∷ □ , f x xs (recr f z xs))) xs≡xs' ⟩
          x ∷ xs' , f x xs (recr f z xs)
       ≡⟨ cong (λ □ → (x ∷ xs' , f x □ (recr f z xs))) xs≡xs' ⟩
          x ∷ xs' , f x xs' (recr f z xs)
       ≡⟨ cong (λ □ → (x ∷ xs' , f x xs' □)) rec≡rec' ⟩
          x ∷ xs' , f x xs' rec'
       ≡⟨ refl ⟩
         foldr
           (λ { x (xs , rec) → x ∷ xs , f x xs rec })
           ([] , z)
           (x ∷ xs)
       ∎

-- recr ≡ recr2, instantiating the preceding lemma
recr≡recr2 : ∀ {a b : Set} (f : a → List a → b → b) (z : b) (xs : List a)
             → recr f z xs ≡ recr2 f z xs
recr≡recr2 f z xs = proj₂-≡ (recr≡recr2* f z xs)

