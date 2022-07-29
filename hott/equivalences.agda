
---- Logical equivalence between four notions of type equivalence:
----   bi-invertible maps,
----   quasi-invertible maps,
----   half-adjoint equivalences,
----   contractible maps,
---- following Chapter 4 of the HoTT book
---- and Pierre-Louis Curien's ECI 2021 course.

open import Data.Unit
  using (⊤)
open import Data.Product
  using (_×_; _,_; Σ-syntax)
  renaming (proj₁ to π₁; proj₂ to π₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

----

infixr 30 _∙_
infixr 35 _⁻¹
infix  30 _~_
infixr 40 _∘_

----

_⁻¹ = sym
_∙_ = trans

id : ∀ {ℓ} {A : Set ℓ} → A → A
id a = a

_∘_ : ∀ {ℓ} {A B C : Set ℓ} → (B → C) → (A → B) → A → C
(f ∘ g) a = f (g a)

tr : ∀ {ℓ} {A : Set ℓ} (B : A → Set ℓ) {a₁ a₂ : A} (p : a₁ ≡ a₂)
     → B a₁ → B a₂
tr _ refl x = x
 
congd : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} (f : (a : A) → B a) {a₁ a₂ : A} (p : a₁ ≡ a₂)
        → tr B p (f a₁) ≡ f a₂
congd _ refl = refl

----

ap : ∀ {ℓ} {A B : Set ℓ} (f : A → B) {a b : A} → a ≡ b → f a ≡ f b
ap _ refl = refl

apd : ∀ {ℓ} {A : Set ℓ} {B : (a : A) → Set ℓ} (f : (a : A) → B a) {a b : A}
      → (p : a ≡ b) → f a ≡ tr B (sym p) (f b)
apd _ refl = refl

ap-id : ∀ {ℓ} {A : Set ℓ} {a b : A} {p : a ≡ b}
        → ap id p ≡ p
ap-id {p = refl} = refl

ap-∘ : ∀ {ℓ} {A B C : Set ℓ} {f : A → B} {g : B → C} {a b : A} {p : a ≡ b}
       → ap (g ∘ f) p ≡ ap g (ap f p)
ap-∘ {p = refl} = refl

ap-∙ : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {a b c : A} {p : a ≡ b} {q : b ≡ c}
       → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-∙ {p = refl} = refl

ap-⁻¹ : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {a b : A} {p : a ≡ b}
        → (ap f p) ⁻¹ ≡ ap f (p ⁻¹)
ap-⁻¹ {p = refl} = refl

---- Groupoid structure

∙-assoc : ∀ {ℓ} {A : Set ℓ} {a b c d : A}
            (p : a ≡ b) (q : b ≡ c) (r : c ≡ d)
          → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
∙-assoc refl refl refl = refl

∙-neut-l : ∀ {ℓ} {A : Set ℓ} {a b : A}
           → (p : a ≡ b)
           → refl ∙ p ≡ p
∙-neut-l refl = refl

∙-neut-r : ∀ {ℓ} {A : Set ℓ} {a b : A}
           → (p : a ≡ b)
           → p ∙ refl ≡ p
∙-neut-r refl = refl

∙-inv : ∀ {ℓ} {A : Set ℓ} {a b c : A} {p : a ≡ b} {q : b ≡ c}
        → (p ∙ q)⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
∙-inv {p = refl} {q = refl} = refl

∙-inv-l : ∀ {ℓ} {A : Set ℓ} {a b : A}
          → (p : a ≡ b)
          → (p ⁻¹) ∙ p ≡ refl
∙-inv-l refl = refl

∙-cancel-r : ∀ {ℓ} {A : Set ℓ} {a b c : A} {p q : a ≡ b} (r : b ≡ c)
             → p ∙ r ≡ q ∙ r → p ≡ q
∙-cancel-r {p = p} {q = q} refl e =
  begin
    p
  ≡⟨ (∙-neut-r p)⁻¹ ⟩
    p ∙ refl
  ≡⟨ e ⟩
    q ∙ refl
  ≡⟨ ∙-neut-r q ⟩
    q
  ∎
  
⁻¹-involutive : ∀ {ℓ} {A : Set ℓ} {a b : A} {p : a ≡ b}
                → (p ⁻¹) ⁻¹ ≡ p
⁻¹-involutive {p = refl} = refl

----

tr-ap-l : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {x y : A} {z : B}
            {p : x ≡ y} {q : f x ≡ z}
          → tr (λ ◇ → f ◇ ≡ z) p q ≡ tr (λ ◇ → ◇ ≡ z) (ap f p) q
tr-ap-l {p = refl} = refl

tr-refl-l : ∀ {ℓ} {A : Set ℓ} {x y : A} {p : x ≡ y}
            → tr (λ ◇ → ◇ ≡ x) p refl ≡ sym p
tr-refl-l {p = refl} = refl

---- Logical equivalence

record _↔_ {ℓ} (A B : Set ℓ) : Set ℓ where
  field
    ↔-to   : A → B
    ↔-from : B → A
open _↔_

---- Homotopy

_~_ : ∀ {ℓ} {A B : Set ℓ} (f g : A → B) → Set ℓ
f ~ g = ∀ a → f a ≡ g a

H-comm : ∀ {ℓ} {A B : Set ℓ} {f g : A → B} {a₁ a₂ : A}
         → (H : f ~ g)
         → (p : a₁ ≡ a₂)
         → ap f p ∙ H a₂ ≡ H a₁ ∙ ap g p
H-comm H refl = trans (∙-neut-l _) ((∙-neut-r _)⁻¹)

H-nest : ∀ {ℓ} {A : Set ℓ} {f : A → A} {a : A}
         → (H : f ~ id)
         → H (f a) ≡ ap f (H a)
H-nest {f = f} {a = a} H =
  ∙-cancel-r (H a) 
    (begin
      H (f a) ∙ H a
    ≡⟨ cong (_∙_ (H (f a))) (ap-id ⁻¹) ⟩
      H (f a) ∙ ap id (H a)
    ≡⟨ (H-comm H (H a))⁻¹ ⟩
      ap f (H a) ∙ H a
    ∎)

---- Equivalence

biinv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → Set ℓ
biinv {_} {A} {B} f = (Σ[ g ∈ (B → A) ] f ∘ g ~ id)
                    × (Σ[ h ∈ (B → A) ] h ∘ f ~ id)

record _≃_ {ℓ} (A B : Set ℓ) : Set ℓ where
  field
    eq     : A → B
    eq-inv : biinv eq
open _≃_

---- Characterization of identity types

≡-Σ : ∀ {ℓ} {A : Set ℓ} {B : A → Set ℓ} {x y : Σ[ a ∈ A ] B a}
      → (x ≡ y) ≃ (Σ[ p ∈ π₁ x ≡ π₁ y ] tr B p (π₂ x) ≡ π₂ y)
eq     ≡-Σ refl = refl , refl
eq-inv ≡-Σ      =
  ((λ { (refl , refl) → refl }) , λ { (refl , refl) → refl }),
  ((λ { (refl , refl) → refl }) , λ { refl → refl })

---- n-types

isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = Σ[ a ∈ A ] ∀ (b : A) → a ≡ b

---- Fiber

fib : ∀ {ℓ} {A B : Set ℓ} (f : A → B) (b : B) → Set ℓ
fib {A = A} f b = Σ[ a ∈ A ] f a ≡ b

≡-fib : ∀ {ℓ} {A B : Set ℓ} {f : A → B} {b : B}
        → {a₁ : A} {p₁ : f a₁ ≡ b}
        → {a₂ : A} {p₂ : f a₂ ≡ b}
        → ((a₁ , p₁) ≡ (a₂ , p₂)) ≃
          (Σ[ q ∈ a₁ ≡ a₂ ] (ap f q ⁻¹) ∙ p₁ ≡ p₂)
eq     ≡-fib refl = refl , refl
eq-inv ≡-fib = ((λ { (refl , refl) → refl }) , (λ { (refl , refl) → refl })) ,
               ((λ { (refl , refl) → refl }) , (λ { refl → refl }))

---- Four notions of equivalence

qinv : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → Set ℓ
qinv {_} {A} {B} f = Σ[ g ∈ (B → A) ] (f ∘ g ~ id) × (g ∘ f ~ id)

ishae : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → Set ℓ
ishae {_} {A} {B} f = Σ[ g ∈ (B → A) ]
                      Σ[ ε ∈ (f ∘ g ~ id) ]
                      Σ[ η ∈ (g ∘ f ~ id) ]
                      ∀ a → ε (f a) ≡ ap f (η a)

contrmap : ∀ {ℓ} {A B : Set ℓ} (f : A → B) → Set ℓ
contrmap f = ∀ b → isContr (fib f b)

biinv↔qinv : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → biinv f ↔ qinv f
↔-to   (biinv↔qinv {f = f}) ((g , fg) , (h , hf)) =
  h ∘ f ∘ g ,
    (λ a → cong f (hf (g a)) ∙ fg a),
    (λ a → cong h (fg (f a)) ∙ hf a)
↔-from biinv↔qinv (g , fg , gf) = (g , fg) , (g , gf)

qinv↔ishae : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → qinv f ↔ ishae f
↔-to   (qinv↔ishae {f = f}) (g , ε , η) =
    g , ε' , η , λ a →
      begin
        (ε (f (g (f a))))⁻¹ ∙ ap f (η (g (f a))) ∙ ε (f a)
      ≡⟨ cong (λ z → ((ε (f (g (f a))))⁻¹) ∙ ap f z ∙ ε  (f a)) (H-nest η) ⟩
        (ε (f (g (f a))))⁻¹ ∙ ap f (ap (g ∘ f) (η a)) ∙ ε (f a)
      ≡⟨ cong (λ z → ((ε (f (g (f a))))⁻¹) ∙ ap f z ∙ ε  (f a)) ap-∘ ⟩
        (ε (f (g (f a))))⁻¹ ∙ ap f (ap g (ap f (η a))) ∙ ε (f a)
      ≡⟨ cong (λ z → ((ε (f (g (f a))))⁻¹) ∙ z ∙ ε  (f a)) (ap-∘)⁻¹ ⟩
        (ε (f (g (f a))))⁻¹ ∙ ap (f ∘ g) (ap f (η a)) ∙ ε (f a)
      ≡⟨ cong (λ z → (ε (f (g (f a))))⁻¹ ∙ z) (H-comm ε (ap f (η a))) ⟩
        (ε (f (g (f a))))⁻¹ ∙ ε (f (g (f a))) ∙ ap id (ap f (η a))
      ≡⟨ ∙-assoc ((ε (f (g (f a))))⁻¹) (ε (f (g (f a)))) (ap id (ap f (η a))) ⟩
        ((ε (f (g (f a))))⁻¹ ∙ ε (f (g (f a)))) ∙ ap id (ap f (η a))
      ≡⟨ cong (_∙ (ap id (ap f (η a)))) (∙-inv-l (ε (f (g (f a))))) ⟩
        refl ∙ ap id (ap f (η a))
      ≡⟨ ∙-neut-l _ ⟩
        ap id (ap f (η a))
      ≡⟨ ap-id ⟩
        ap f (η a)
      ∎
  where
    ε' : f ∘ g ~ id
    ε' b = sym (ε (f (g b))) ∙ ap f (η (g b)) ∙ ε b
↔-from qinv↔ishae (g , ε , η , _) = g , ε , η

ishae↔contrmap : ∀ {ℓ} {A B : Set ℓ} {f : A → B} → ishae f ↔ contrmap f
↔-to   (ishae↔contrmap {f = f}) (g , ε , η , coh) b =
  (g b , ε b) ,
  λ { (a , p) → π₁ (π₁ (eq-inv ≡-fib))
    ((ap g p)⁻¹ ∙ η a ,
     (begin
        (ap f (ap g p ⁻¹ ∙ η a)) ⁻¹ ∙ ε b
      ≡⟨ cong (λ z → z ⁻¹ ∙ ε b) (ap-∙ {p = ap g p ⁻¹}) ⟩
        (ap f (ap g p ⁻¹) ∙ ap f (η a)) ⁻¹ ∙ ε b
      ≡⟨ cong (λ z → z ∙ ε b) (∙-inv {p = ap f (ap g p ⁻¹)}) ⟩
        (ap f (η a) ⁻¹ ∙ ap f (ap g p ⁻¹) ⁻¹) ∙ ε b
      ≡⟨ cong (λ z → (z ⁻¹ ∙ ap f (ap g p ⁻¹) ⁻¹) ∙ ε b) (coh a ⁻¹) ⟩
        (ε (f a) ⁻¹ ∙ ap f (ap g p ⁻¹) ⁻¹) ∙ ε b
      ≡⟨ ∙-assoc (ε (f a) ⁻¹) (ap f (ap g p ⁻¹) ⁻¹) (ε b) ⁻¹ ⟩
        ε (f a) ⁻¹ ∙ (ap f (ap g p ⁻¹) ⁻¹ ∙ ε b)
      ≡⟨ cong (λ z → ε (f a) ⁻¹ ∙ (z ∙ ε b)) ap-⁻¹ ⟩
        ε (f a) ⁻¹ ∙ (ap f ((ap g p ⁻¹) ⁻¹) ∙ ε b)
      ≡⟨ cong (λ z → ε (f a) ⁻¹ ∙ (ap f (z ⁻¹) ∙ ε b)) ap-⁻¹ ⟩
        ε (f a) ⁻¹ ∙ (ap f ((ap g (p ⁻¹)) ⁻¹) ∙ ε b)
      ≡⟨ cong (λ z → ε (f a) ⁻¹ ∙ (ap f z ∙ ε b)) ap-⁻¹ ⟩
        ε (f a) ⁻¹ ∙ (ap f (ap g ((p ⁻¹) ⁻¹)) ∙ ε b)
      ≡⟨ cong (λ z → ε (f a) ⁻¹ ∙ z ∙ ε b) (ap-∘ ⁻¹) ⟩
        ε (f a) ⁻¹ ∙ (ap (f ∘ g) ((p ⁻¹) ⁻¹) ∙ ε b)
      ≡⟨ cong (λ z → ε (f a) ⁻¹ ∙ z) (H-comm ε ((p ⁻¹) ⁻¹)) ⟩
        ε (f a) ⁻¹ ∙ (ε (f a) ∙ ap id ((p ⁻¹) ⁻¹))
      ≡⟨ ∙-assoc (ε (f a) ⁻¹ ) (ε (f a)) (ap id ((p ⁻¹) ⁻¹)) ⟩
        (ε (f a) ⁻¹ ∙ ε (f a)) ∙ ap id ((p ⁻¹) ⁻¹)
      ≡⟨ cong (λ z → z ∙ ap id ((p ⁻¹) ⁻¹)) (∙-inv-l (ε (f a))) ⟩
        refl ∙ ap id ((p ⁻¹) ⁻¹)
      ≡⟨ ∙-neut-l _ ⟩
        ap id ((p ⁻¹) ⁻¹)
      ≡⟨ ap-id ⟩
        (p ⁻¹) ⁻¹
      ≡⟨ ⁻¹-involutive ⟩
        p
      ∎))
  }
↔-from (ishae↔contrmap {A = A} {B = B} {f = f}) c =
    g , ε , η , coh
  where
    g : B → A
    g b = π₁ (π₁ (c b))
    ε : f ∘ g ~ id
    ε b = π₂ (π₁ (c b)) 
    η : g ∘ f ~ id
    η a = ap π₁ (π₂ (c (f a)) (a , refl))
    coh : (a : A) → ε (f a) ≡ ap f (η a)
    coh a =
      begin
        π₂ (π₁ (c (f a))) 
      ≡⟨ apd π₂ (π₂ (c (f a)) (a , refl)) ⟩
        tr (λ ◇ → f (π₁ ◇) ≡ f a) (sym (π₂ (c (f a)) (a , refl))) refl
      ≡⟨ tr-ap-l {q = refl}⟩
        tr (λ ◇ → ◇ ≡ f a) (ap (f ∘ π₁) (sym (π₂ (c (f a)) (a , refl)))) refl
      ≡⟨ tr-refl-l ⟩
        sym (ap (f ∘ π₁) (sym (π₂ (c (f a)) (a , refl))))
      ≡⟨ ap-⁻¹ ⟩
        ap (f ∘ π₁) (sym (sym (π₂ (c (f a)) (a , refl))))
      ≡⟨ ap-∘ ⟩
        ap f (ap π₁ (sym (sym (π₂ (c (f a)) (a , refl)))))
      ≡⟨ cong (λ ◇ → ap f (ap π₁ ◇)) ⁻¹-involutive ⟩
        ap f (ap π₁ (π₂ (c (f a)) (a , refl)))
      ∎

