
--
-- Proof of strong normalization for the simply typed
-- lambda-calculus with weak/call-by-value evaluation.
--
-- The proof is based on a proof by de Vrijer using the
-- notion of "increasing functional"; see Term Rewriting
-- Systems (TeReSe), Section 10.5.
--
-- Terms are intrinsically typed and represented with a
-- straightforward named representation. It is not necessary
-- to avoid capture as we work in a weak setting.
--

open import Relation.Nullary      using (¬_; Dec; yes; no)
open import Relation.Binary.Core  using (_≡_; _≢_; refl)
open import Data.Empty            using (⊥; ⊥-elim)
open import Data.Unit             using (⊤; tt)
open import Data.Nat              using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _<_)
                               renaming (_≟_ to _≟Nat_)
open import Data.Nat.Properties   using (+-identityʳ; +-monoˡ-<; +-monoʳ-<; <-trans; ≤+≢⇒<)
open import Data.Product          using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum              using (_⊎_; inj₁; inj₂)
open import Data.String           using (String)
                               renaming (_≟_ to _≟String_)
open import Function              using (case_of_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym; trans; cong)
open Eq.≡-Reasoning

---- Precedence and associativity declarations

infix  30 _~~_
infixl 40 _⊏_
infixl 50 _⊕_
infix  60 _*
infix  70 ⟦_⟧_
infixl 80 _[_:=_]
infixl 80 _⟪_⟫

---- Functional extensionality

postulate
  funext  : {A : Set} {B : A → Set}
          → {f g : ∀ (a : A) → B a}
          → (∀ (a : A) → f a ≡ g a)
          → f ≡ g
          
  -- Variant for implicit functions
  funext* : {A : Set} {B : A → Set}
          → {f g : ∀ {a : A} → B a}
          → (∀ (a : A) → f {a} ≡ g {a})          
          → (λ {x} → f {x}) ≡ (λ {x} → g {x})

----- Propositions

isProp : Set → Set
isProp A = ∀ (a b : A) → a ≡ b

≤-prop : ∀ {n m : ℕ} → isProp (n ≤ m)
≤-prop _≤_.z≤n _≤_.z≤n = refl
≤-prop (s≤s p) (s≤s q) = cong s≤s (≤-prop p q)

<-prop : ∀ {n m : ℕ} → isProp (n < m)
<-prop p q = ≤-prop p q

∀-prop : ∀ {A : Set} {B : A → Set}
       → (∀ (a : A) → isProp (B a))
       → isProp (∀ (a : A) → B a)
∀-prop f p q = funext (λ a → f a (p a) (q a))

∀-prop* : ∀ {A : Set} {B : A → Set}
        → (∀ (a : A) → isProp (B a))
        → isProp (∀ {a : A} → B a)
∀-prop* f p q = funext* (λ a → f a (p {a}) (q {a}))

----- Grammar of types

data Ty : Set where
  O   : Ty
  _⟶_ : Ty → Ty → Ty

_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
O         ≟Ty O         = yes refl
O         ≟Ty (_ ⟶ _)   = no (λ{()})
(_ ⟶ _)   ≟Ty O         = no (λ{()})
(A₁ ⟶ A₂) ≟Ty (B₁ ⟶ B₂) with A₁ ≟Ty B₁ | A₂ ≟Ty B₂
... | yes refl | yes refl = yes refl
... | yes refl | no  q    = no (λ { refl → q refl })
... | no  p    | _        = no (λ { refl → p refl })

----- Theory of "increasing functionals"
  
-- Definition of the posets of increasing functionals.

IF           : Ty → Set
_⊏_          : {A : Ty} → IF A → IF A → Set
isIncreasing : {A B : Ty} → (IF A → IF B) → Set

IF O       = ℕ
IF (A ⟶ B) = Σ[ f ∈ (IF A → IF B) ]
                 isIncreasing f

_⊏_ {O}     n       m       = n < m
_⊏_ {A ⟶ B} (f , _) (g , _) = ∀ {x : IF A} → f x ⊏ g x

isIncreasing {A} f = ∀ {x y : IF A} → x ⊏ y → f x ⊏ f y

-- Being increasing is a proposition

⊏-prop : {A : Ty} {f g : IF A} → isProp (f ⊏ g)
⊏-prop {O}     = <-prop
⊏-prop {A ⟶ B} = ∀-prop* (λ _ → ⊏-prop)

isIncreasing-prop : {A B : Ty} {f : IF A → IF B}
                  → isProp (isIncreasing f)
isIncreasing-prop = ∀-prop* λ _ →
                    ∀-prop* λ _ →
                    ∀-prop  λ _ → ⊏-prop

IF-extensionality : {A B : Ty} {f g : IF (A ⟶ B)}
                  → proj₁ f ≡ proj₁ g
                  → f ≡ g
IF-extensionality {_} {_} {f , _} {_ , _} refl =
  cong (_,_ f) (isIncreasing-prop _ _)

-- Transitivity of ⊏

⊏-trans : {A : Ty} {f g h : IF A} → f ⊏ g → g ⊏ h → f ⊏ h
⊏-trans {O}     f⊏g g⊏h = <-trans f⊏g g⊏h
⊏-trans {A ⟶ B} f⊏g g⊏h = ⊏-trans f⊏g g⊏h

⊏-≡-cong : {A : Ty} {f f' g g' : IF A} → f ≡ f' → g ≡ g' → f ⊏ g → f' ⊏ g'
⊏-≡-cong refl refl f⊏g = f⊏g

-- Definition of ⊕ together with the proof that it is
-- left-monotonic.

_⊕_ : {A : Ty} → IF A → ℕ → IF A
⊕-monot-l : {A : Ty} {f g : IF A} {n : ℕ}
          → f ⊏ g → (f ⊕ n) ⊏ (g ⊕ n)

_⊕_ {O}     f          n = f + n
_⊕_ {A ⟶ B} (f , fInc) n = (λ x   → f x ⊕ n),
                           (λ x⊏y → ⊕-monot-l (fInc x⊏y))

⊕-monot-l {O}     f<g = +-monoˡ-< _ f<g
⊕-monot-l {A ⟶ B} f⊏g = ⊕-monot-l f⊏g

-- ⊕ is right-monotonic

⊕-monot-r : {A : Ty} {f : IF A} {n m : ℕ}
          → n < m → f ⊕ n ⊏ f ⊕ m
⊕-monot-r {O}     {f = f} n<m = +-monoʳ-< f n<m
  -- NB. first argument to +-monoʳ-< is implicit in more recent versions of Agda's stdlib
⊕-monot-r {A ⟶ B}         n<m = ⊕-monot-r n<m

-- ⊕ is right-monotonic (variant)

-- {This should be in Data.Nat.Properties}
m<m+n : ∀ m {n} → 0 < n → m < m + n
m<m+n zero    n>0 = n>0
m<m+n (suc m) n>0 = s≤s (m<m+n m n>0)
-- {end}

⊕-monot-r0 : {A : Ty} {f : IF A} {m : ℕ}
           → 0 < m → f ⊏ f ⊕ m
⊕-monot-r0 {O}     0<m = m<m+n _ 0<m
⊕-monot-r0 {A ⟶ B} 0<m = ⊕-monot-r0 0<m

--

⊏-⊕-monot-r : {A : Ty} {f f' : IF A} {n m : ℕ} → f ≡ f' → n < m → (f ⊕ n) ⊏ (f' ⊕ m)
⊏-⊕-monot-r refl n<m = ⊕-monot-r n<m

--

⊕-neut-r : {A : Ty} {f : IF A} {n : ℕ} → n ≡ 0 → f ⊕ n ≡ f
⊕-neut-r {O}     refl = +-identityʳ _
⊕-neut-r {A ⟶ B} refl = IF-extensionality (funext λ x → ⊕-neut-r refl)

-- Definition of the 𝟘 and _* operators together with
-- the proof that * is monotonic.

𝟘       : {A : Ty} → IF A
_*      : {A : Ty} → IF A → ℕ
*-monot : {A : Ty} {f g : IF A} → f ⊏ g → f * ⊏ g *

𝟘 {O}     = zero
𝟘 {A ⟶ B} = (λ f   → 𝟘 ⊕ f *) ,
            (λ f⊏g → ⊕-monot-r (*-monot f⊏g))

_* {O}     f       = f
_* {A ⟶ B} (f , _) = f 𝟘 *

*-monot {O}     f⊏g = f⊏g
*-monot {A ⟶ B} f⊏g = *-monot f⊏g

----- Simply typed lambda-calculus with weak call-by-value evaluation

-- Syntax

data Name : Ty → Set where
  name : {A : Ty} → String → Name A

data _≡Name_ : {A B : Ty} → Name A → Name B → Set where
  reflN : {A : Ty} {x : Name A} → x ≡Name x

symN : {A B : Ty} {x : Name A} {y : Name B} → x ≡Name y → y ≡Name x
symN reflN = reflN

transN : {A B C : Ty} {x : Name A} {y : Name B} {z : Name C}
       → x ≡Name y → y ≡Name z → x ≡Name z
transN reflN reflN = reflN

_≢Name_ : {A B : Ty} → Name A → Name B → Set
x ≢Name y = ¬(x ≡Name y)

_≟Name_ : {A B : Ty} (x : Name A) (y : Name B) → Dec (x ≡Name y)
_≟Name_ {A} {B} (name x) (name y) with A ≟Ty B
... | no  p    = no (λ { reflN → p refl })
... | yes refl with x ≟String y
...               | no  p    = no  (λ { reflN → p refl })
...               | yes refl = yes reflN

data Term : Ty → Set where
  var : {A : Ty}   → Name A → Term A
  lam : {A B : Ty} → Name A → Term B → Term (A ⟶ B)
  app : {A B : Ty} → Term (A ⟶ B) → Term A → Term B

data Value : {A : Ty} → Term A → Set where
  vlam : ∀ {A B x t} → Value {A ⟶ B} (lam {A} x t)
  
free : {A B : Ty} → Name A → Term B → Set
free x (var y)   = x ≡Name y
free x (lam y t) = ¬(x ≡Name y) × free x t
free x (app t s) = free x t ⊎ free x s

isFree : {A B : Ty} (x : Name A) (t : Term B) → Dec (free x t)
isFree x (var y)   = x ≟Name y
isFree x (lam y t)
  with x ≟Name y
...  | yes p = no (λ { (q , _) → q p })
...  | no  p
     with isFree x t
...     | no  q = no  (λ { (_ , r) → q r })
...     | yes q = yes (p , q)
isFree x (app t s)
  with isFree x t
...  | yes x∈t = yes (inj₁ x∈t)
...  | no  x∉t
     with isFree x s
...     | yes x∈s = yes (inj₂ x∈s)
...     | no  x∉s = no (λ {
                      (inj₁ x∈t) → x∉t x∈t
                    ; (inj₂ x∈s) → x∉s x∈s
                    })

-- Substitution

sub : {A B : Ty} → Term A → Name B → Term B → Term A
sub (var x) y v with x ≟Name y
... | no  _     = var x
... | yes reflN = v
sub (lam x t)  y v with x ≟Name y
... | no  _     = lam x (sub t y v)
... | yes reflN = lam x t
sub (app t s) y v = app (sub t y v) (sub s y v)

-- Free variables of a substitution

fv-sub : ∀ {A} {t : Term A} {B} {x : Name B} {s : Term B} {C} {y : Name C}
       → free y (sub t x s)
       → (¬(y ≡Name x) × free y t) ⊎ free y s
fv-sub {t = var z}   {x = x} {y = y} y∈fv
  with z ≟Name x
...  | no  z≢x   = inj₁ ((λ x≡y → z≢x (transN (symN y∈fv) x≡y)) , y∈fv)
...  | yes reflN = inj₂ y∈fv
fv-sub {t = lam z t} {x = x} {s = s} {y = y}   y∈fv
  with z ≟Name x
...  | yes reflN = inj₁ ((λ z≡y → proj₁ y∈fv z≡y), y∈fv)
...  | no  z≢x
     with fv-sub {t = t} (proj₂ y∈fv)
...     | inj₂ y∈s = inj₂ y∈s
...     | inj₁ y∈t
        with x ≟Name y
...        | no  x≢y   = inj₁ ((λ y≡x → x≢y (symN y≡x)) , proj₁ y∈fv , proj₂ y∈t)
...        | yes reflN = ⊥-elim (proj₁ y∈t reflN)
fv-sub {t = app t₁ t₂} {x = x} {s = s} {y = y} (inj₁ y∈t)
  with fv-sub {t = t₁} y∈t
...  | inj₁ y∈t₁ = inj₁ (proj₁ y∈t₁ , inj₁ (proj₂ y∈t₁))
...  | inj₂ y∈s  = inj₂ y∈s
fv-sub {t = app t₁ t₂} {x = x} {s = s} {y = y} (inj₂ y∈t)
  with fv-sub {t = t₂} y∈t
...  | inj₁ y∈t₂ = inj₁ (proj₁ y∈t₂ , inj₂ (proj₂ y∈t₂))
...  | inj₂ y∈s  = inj₂ y∈s

-- Small-step weak call-by-value evaluation

data _↦_ : {A : Ty} → Term A → Term A → Set where
  e-appl : ∀ {A B} {t t' : Term (A ⟶ B)} {s : Term A}
         → t ↦ t'
         → app t s ↦ app t' s
  e-appr : ∀ {A B} {t : Term (A ⟶ B)} {s s' : Term A}
         → s ↦ s'
         → app t s ↦ app t s'
  e-beta : ∀ {A B} {x : Name A} {t : Term B} {s : Term A}
         → Value s
         → app (lam x t) s ↦ sub t x s

-- Definition of closed terms (with no free variables)

closed : ∀ {A} → (t : Term A) → Set
closed t = ∀ {B} (x : Name B) → ¬ free x t

closed-appl : ∀ {A B} {t : Term (A ⟶ B)} {s : Term A} → closed (app t s) → closed t
closed-appl clts x x∈t = clts x (inj₁ x∈t)

closed-appr : ∀ {A B} {t : Term (A ⟶ B)} {s : Term A} → closed (app t s) → closed s
closed-appr clts x x∈s = clts x (inj₂ x∈s)

-- Reduction preserves closed terms

closed-reduce : ∀ {A} {t t' : Term A} → t ↦ t' → closed t → closed t'
closed-reduce (e-appl step) clts x (inj₁ x∈t) =
  closed-reduce step (closed-appl clts) x x∈t
closed-reduce (e-appl step) clts x (inj₂ x∈s) =
  closed-appr clts x x∈s
closed-reduce (e-appr step) clts x (inj₁ x∈t) =
  closed-appl clts x x∈t
closed-reduce (e-appr step) clts x (inj₂ x∈s) =
  closed-reduce step (closed-appr clts) x x∈s
closed-reduce {t = app (lam {B} y t) s}
              (e-beta val) clts {A} x x∈fv =
    clts {A} x (fv-sub {_} {t} {B} {y} {s} {A} {x} x∈fv)

---- Proof of termination

-- Definition of assignment

Assignment : Set
Assignment = {A : Ty} → Name A → IF A

:=𝟘 : Assignment
:=𝟘 _ = 𝟘

-- Extension of an assignment

_[_:=_] : ∀ {A} → Assignment → Name A → IF A → Assignment
(υ [ x := f ]) y with x ≟Name y
... | no  _     = υ y
... | yes reflN = f

data Extension : Set where 
  ext-[] : Extension
  ext-∷  : Extension → {A : Ty} → Name A → IF A → Extension

_⟪_⟫ : Assignment → Extension → Assignment
υ ⟪ ext-[] ⟫      = υ
υ ⟪ ext-∷ e x f ⟫ = υ ⟪ e ⟫ [ x := f ] 

extend-≢Name : ∀ {A B : Ty} {υ : Assignment} {e} {x : Name A} {y : Name B} {f}
             → x ≢Name y
             → (υ ⟪ e ⟫) y ≡ (υ [ x := f ] ⟪ e ⟫) y
extend-≢Name {e = ext-[]}      {x} {y} x≢y with x ≟Name y
... | no  _     = refl
... | yes reflN = ⊥-elim (x≢y reflN)
extend-≢Name {e = ext-∷ e z f} {x} {y} x≢y with z ≟Name y
... | no  _     = extend-≢Name {e = e} x≢y
... | yes reflN = refl

_~~_ : Assignment → Assignment → Set
υ₁ ~~ υ₂ = ∀ {A} {x : Name A} → υ₁ x ≡ υ₂ x

~~-refl : ∀ {υ : Assignment} → υ ~~ υ
~~-refl = refl

~~-trans : ∀ {υ₁ υ₂ υ₃ : Assignment} → υ₁ ~~ υ₂ → υ₂ ~~ υ₃ → υ₁ ~~ υ₃
~~-trans f g = trans f g

~~-extend : ∀ {υ₁ υ₂ : Assignment}
            → υ₁ ~~ υ₂
            → {A : Ty} {x : Name A} {f : IF A}
            → (υ₁ [ x := f ]) ~~ (υ₂ [ x := f ])
~~-extend eq {A} {x} {f} {B} {y} with x ≟Name y
... | no  _     = eq
... | yes reflN = refl

~~-swap-≢Name : ∀ {υ : Assignment} {A B : Ty} {x : Name A} {y : Name B} {f : IF A} {g : IF B}
              → x ≢Name y
              → (υ [ x := f ] [ y := g ]) ~~ (υ [ y := g ] [ x := f ] )
~~-swap-≢Name {υ} {A} {B} {x} {y} {f} {g} x≢y {C} {z}
  with y ≟Name z
...  | no  y≢z
     with x ≟Name z
...     | yes reflN = refl
...     | no  _
        with y ≟Name z
...        | no  _     = refl
...        | yes reflN = ⊥-elim (y≢z reflN)
~~-swap-≢Name {υ} {A} {B} {x} {y} {f} {g} x≢y {C} {z}
     | yes reflN
     with x ≟Name y
...     | yes reflN = ⊥-elim (x≢y reflN)
...     | no  _
        with y ≟Name y
...        | no  y≢y   = ⊥-elim (y≢y reflN)
...        | yes reflN = refl

~~-elim : ∀ {υ : Assignment} {A : Ty} {x : Name A} {f g : IF A}
            → (υ [ x := f ] [ x := g ]) ~~ (υ [ x := g ])
~~-elim {υ} {A} {x} {f} {g} {C} {z}
  with x ≟Name z
...  | yes reflN = refl
...  | no  x≢z
     with x ≟Name z
...     | yes reflN = ⊥-elim (x≢z reflN)
...     | no  _     = refl

~~-elim* : ∀ {υ : Assignment} {e : Extension}
            {A : Ty} {x : Name A} {f g : IF A}
          → υ ⟪ e ⟫ [ x := g ] ~~ υ [ x := f ] ⟪ e ⟫ [ x := g ]
~~-elim* {υ} {ext-[]}                 {A} {x} {f} {g} {C} {z} =
  sym (~~-elim {υ} {A} {x} {f} {g} {C} {z})
~~-elim* {υ} {ext-∷ e {B} (y) h} {A} {x} {f} {g} {C} {z}
  with y ≟Name x
...  | no  y≢x =
        (υ ⟪ e ⟫ [ y := h ] [ x := g ]) z
      ≡⟨ ~~-swap-≢Name {υ ⟪ e ⟫} {B} {A} {y} {x} y≢x {C} {z} ⟩
        (υ ⟪ e ⟫ [ x := g ] [ y := h ]) z
      ≡⟨ ~~-extend (λ {C} {z} → ~~-elim* {υ} {e} {A} {x} {f} {g} {C} {z})
                   {x = y} {h} {C} {z} ⟩
        (υ [ x := f ] ⟪ e ⟫ [ x := g ] [ y := h ]) z
      ≡⟨ ~~-swap-≢Name {υ [ x := f ] ⟪ e ⟫} {A} {B} {x} {y}
                       (λ x≡y → y≢x (symN x≡y)) {C} {z} ⟩
        (υ [ x := f ] ⟪ e ⟫ [ y := h ] [ x := g ]) z
      ∎
... | yes reflN =
        (υ ⟪ e ⟫ [ y := h ] [ y := g ]) z
      ≡⟨ ~~-elim {υ ⟪ e ⟫} {A} {y} {h} {g} {C} {z} ⟩
        (υ ⟪ e ⟫ [ y := g ]) z
      ≡⟨ ~~-elim* {υ} {e} {A} {y} {f} {g} {C} {z} ⟩
        (υ [ y := f ] ⟪ e ⟫ [ y := g ]) z
      ≡⟨ sym (~~-elim {υ [ y := f ] ⟪ e ⟫} {A} {y} {h} {g} {C} {z}) ⟩
        (υ [ y := f ] ⟪ e ⟫ [ y := h ] [ y := g ]) z
      ∎

-- Definition of valuation, including the proof that the
-- resulting functional is increasing.

⟦_⟧_      : ∀ {A} → Term A → Assignment → IF A

⟦⟧-extend : ∀ {A} {t : Term A} {υ : Assignment} {B} {x : Name B} {f : IF B}
          → ¬ free x t
          → ⟦ t ⟧ υ ≡ ⟦ t ⟧ υ [ x := f ]

⟦⟧-extend* : ∀ {A} {t : Term A} {υ : Assignment} {B} {x : Name B} {f : IF B} {e : Extension}
           → ¬ free x t
           → ⟦ t ⟧ (υ ⟪ e ⟫) ≡ ⟦ t ⟧ (υ [ x := f ] ⟪ e ⟫)

⟦⟧-cong-assignment
           : ∀ {υ₁ υ₂ : Assignment}
           → υ₁ ~~ υ₂
           → (∀ {A} {t : Term A} → ⟦ t ⟧ υ₁ ≡ ⟦ t ⟧ υ₂)
           
⟦⟧-monot-assignment
           : ∀ {A} {t : Term A} {υ : Assignment} {B} {x : Name B}
               {f g : IF B}
           → f ⊏ g
           → free x t
           → ⟦ t ⟧ υ [ x := f ] ⊏ ⟦ t ⟧ υ [ x := g ]

⟦ var x ⟧    υ = υ x
⟦ lam x t ⟧  υ =
  (λ f → ⟦ t ⟧ υ [ x := f ] ⊕ f * ⊕ 1) ,
  (λ f⊏g →
    ⊕-monot-l
      (case isFree x t of λ {
        (yes x∈fv) →
             ⊏-trans
               (⊕-monot-l (⟦⟧-monot-assignment {_} {t} {υ} {_} {x} f⊏g x∈fv))
               (⊕-monot-r (*-monot f⊏g))
      ; (no  x∉fv) →
              ⊏-⊕-monot-r
                (trans
                  (sym (⟦⟧-extend {_} {t} {υ} {_} {x} x∉fv))
                  (⟦⟧-extend {_} {t} {υ} {_} {x} x∉fv))
                (⊕-monot-r (*-monot f⊏g))
      }))
⟦ app t s ⟧  υ = proj₁ (⟦ t ⟧ υ) (⟦ s ⟧ υ)

⟦⟧-extend {x = x} x∉fv = ⟦⟧-extend* {x = x} {e = ext-[]} x∉fv

⟦⟧-extend* {A}       {var y}       {_} {B} {x} {f} {e} x∉fv
  with x ≟Name y
...  | no  x≢y   = extend-≢Name {e = e} x≢y
...  | yes reflN = ⊥-elim (x∉fv reflN)
⟦⟧-extend* {A₁ ⟶ A₂} {lam y t} {υ} {B} {x} {f} {e} x∉fv
  with x ≟Name y
...  | no  x≢y   = IF-extensionality (funext λ g → cong (_⊕ 1) (cong (_⊕ g *) (
                     ⟦⟧-extend* {t = t} {x = x} {e = ext-∷ e y g} (λ x∈t → x∉fv (x≢y , x∈t)))))
...  | yes reflN = IF-extensionality (funext λ g → cong (_⊕ 1) (cong (_⊕ g *) (
                     --- We use that if two assignments match on variables,
                     --- the valuation of any term also matches.
                     (⟦⟧-cong-assignment
                        {υ ⟪ e ⟫ [ y := g ]}
                        {υ [ y := f ] ⟪ e ⟫ [ y := g ]}
                        (λ {C} {z} → ~~-elim* {υ} {e} {A₁} {y} {f} {g} {C} {z})
                        {t = t}))))
⟦⟧-extend* {A₂}      {app {A₁} {.A₂} t s} {υ} {B} {x} {f} {e} x∉fv =
    proj₁ (⟦ t ⟧ υ ⟪ e ⟫) (⟦ s ⟧ υ ⟪ e ⟫)
  ≡⟨ cong (λ X → proj₁ X (⟦ s ⟧ υ ⟪ e ⟫))
          (⟦⟧-extend* {t = t} {x = x} {e = e}
            (λ x∈fv → x∉fv (inj₁ x∈fv))) ⟩
    proj₁ (⟦ t ⟧ υ [ x := f ] ⟪ e ⟫) (⟦ s ⟧ υ ⟪ e ⟫)
  ≡⟨ cong (proj₁ (⟦ t ⟧ υ [ x := f ] ⟪ e ⟫))
         (⟦⟧-extend* {t = s} {x = x} {e = e}
             (λ x∈fv → x∉fv (inj₂ x∈fv))) ⟩
    proj₁ (⟦ t ⟧ υ [ x := f ] ⟪ e ⟫) (⟦ s ⟧ υ [ x := f ] ⟪ e ⟫)
  ∎

⟦⟧-cong-assignment {υ₁} {υ₂} eq {A}        {var x}   = eq
⟦⟧-cong-assignment {υ₁} {υ₂} eq {_ ⟶ _}    {lam x t} =
  IF-extensionality (funext λ f →
    cong (λ X → X ⊕ f * ⊕ 1)
         (⟦⟧-cong-assignment
           {υ₁ [ x := f ]}
           {υ₂ [ x := f ]}
           (~~-extend eq {x = x})
           {t = t}))
⟦⟧-cong-assignment {υ₁} {υ₂} eq {A}        {app t s} =
    proj₁ (⟦ t ⟧ υ₁) (⟦ s ⟧ υ₁)
  ≡⟨ cong (λ X → proj₁ X (⟦ s ⟧ υ₁)) (⟦⟧-cong-assignment {υ₁} {υ₂} eq {t = t}) ⟩
    proj₁ (⟦ t ⟧ υ₂) (⟦ s ⟧ υ₁)
  ≡⟨ cong (proj₁ (⟦ t ⟧ υ₂)) (⟦⟧-cong-assignment {υ₁} {υ₂} eq {t = s}) ⟩
    proj₁ (⟦ t ⟧ υ₂) (⟦ s ⟧ υ₂)
  ∎

⟦⟧-monot-assignment {A}       {var y}   {υ} {B} {x} {f} {g} f⊏g x∈fv
  with x ≟Name y
...  | no  x≢y   = ⊥-elim (x≢y x∈fv)
...  | yes reflN = f⊏g
⟦⟧-monot-assignment {A₁ ⟶ A₂} {lam y t} {υ} {B} {x} {f} {g} f⊏g x∈fv {h}
  with x ≟Name y
...  | no  x≢y =
  let y≢x = λ y≡x → x≢y (symN y≡x) in
   ⊕-monot-l (⊕-monot-l (⊏-≡-cong {_}
     {⟦ t ⟧ υ [ y := h ] [ x := f ] }
     {⟦ t ⟧ υ [ x := f ] [ y := h ]}
     {⟦ t ⟧ υ [ y := h ] [ x := g ]}
     {⟦ t ⟧ υ [ x := g ] [ y := h ]}
     (⟦⟧-cong-assignment (λ {C} {z} → ~~-swap-≢Name {υ} {_} {_} {y} {x} {h} {f} y≢x {C} {z}) {_} {t})
     (⟦⟧-cong-assignment (λ {C} {z} → ~~-swap-≢Name {υ} {_} {_} {y} {x} {h} {g} y≢x {C} {z}) {_} {t})
     (⟦⟧-monot-assignment {_} {t} {υ [ y := h ]} {_} {x} {f} {g} f⊏g (proj₂ x∈fv))
   ))
...  | yes reflN = ⊕-monot-l (⊕-monot-l (⊥-elim (proj₁ x∈fv reflN)))
⟦⟧-monot-assignment {A} {app t s} {υ} {B} {x} {f} {g} f⊏g x∈fv
  with isFree x t
... | yes x∈t
    with isFree x s
...    | yes x∈s =
  let hi₁ = ⟦⟧-monot-assignment {_} {t} {υ} {B} {x} {f} {g} f⊏g x∈t
      hi₂ = ⟦⟧-monot-assignment {_} {s} {υ} {B} {x} {f} {g} f⊏g x∈s
    in
     ⊏-trans {_} {_} {proj₁ (⟦ t ⟧ υ [ x := g ]) (⟦ s ⟧ υ [ x := f ])}
             hi₁
             (proj₂ (⟦ t ⟧ υ [ x := g ]) hi₂)
...    | no  x∉s =
  let hi₁ = ⟦⟧-monot-assignment {_} {t} {υ} {B} {x} {f} {g} f⊏g x∈t
    in
      ⊏-≡-cong {_}
        {proj₁ (⟦ t ⟧ υ [ x := f ]) (⟦ s ⟧ υ)}
        {proj₁ (⟦ t ⟧ υ [ x := f ]) (⟦ s ⟧ υ [ x := f ])}
        {proj₁ (⟦ t ⟧ υ [ x := g ]) (⟦ s ⟧ υ)}
        {proj₁ (⟦ t ⟧ υ [ x := g ]) (⟦ s ⟧ υ [ x := g ])}
        (cong (proj₁ (⟦ t ⟧ υ [ x := f ])) (⟦⟧-extend {_} {s} {υ} {_} {x} {f} x∉s))
        (cong (proj₁ (⟦ t ⟧ υ [ x := g ])) (⟦⟧-extend {_} {s} {υ} {_} {x} {g} x∉s))
        hi₁
⟦⟧-monot-assignment {A} {app t s} {υ} {B} {x} {f} {g} f⊏g x∈fv
    | no  x∉t
    with isFree x s
...    | yes x∈s =
  let hi₂ = ⟦⟧-monot-assignment {_} {s} {υ} {B} {x} {f} {g} f⊏g x∈s
    in
      ⊏-≡-cong {_}
        {proj₁ (⟦ t ⟧ υ)            (⟦ s ⟧ υ [ x := f ])}
        {proj₁ (⟦ t ⟧ υ [ x := f ]) (⟦ s ⟧ υ [ x := f ])}
        {proj₁ (⟦ t ⟧ υ)            (⟦ s ⟧ υ [ x := g ])}
        {proj₁ (⟦ t ⟧ υ [ x := g ]) (⟦ s ⟧ υ [ x := g ])}
        (cong (λ X → proj₁ X (⟦ s ⟧ υ [ x := f ])) (⟦⟧-extend {_} {t} {υ} {_} {x} {f} x∉t))
        (cong (λ X → proj₁ X (⟦ s ⟧ υ [ x := g ])) (⟦⟧-extend {_} {t} {υ} {_} {x} {g} x∉t))
        (proj₂ (⟦ t ⟧ υ) hi₂)
...    | no  x∉s = case x∈fv of λ {
                     (inj₁ x∈t) → ⊥-elim (x∉t x∈t)
                   ; (inj₂ x∈s) → ⊥-elim (x∉s x∈s)
                   }

----

⟦⟧-sub : ∀ {A} {t : Term A} {B} {x : Name B} {s : Term B} {υ : Assignment}
       → closed s
       → ⟦ sub t x s ⟧ υ ≡ ⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ]
⟦⟧-sub {A}       {var x}   {B} {y} {s} {υ} cls
  with x ≟Name y
...  | no  x≢y
     with y ≟Name x
...     | yes reflN = ⊥-elim (x≢y reflN)
...     | no _      = refl
⟦⟧-sub {A}       {var x}   {B} {y} {s} {υ} cls
    | yes reflN
    with x ≟Name x
...    | no  x≢x   = ⊥-elim (x≢x reflN)
...    | yes reflN = refl
⟦⟧-sub {A₁ ⟶ A₂} {lam x t} {B} {y} {s} {υ} cls
  with x ≟Name y
...  | no  x≢y    =
       IF-extensionality (funext λ f →
         cong (λ X → X ⊕ f * ⊕ 1)
           (begin
              ⟦ sub t (y) s ⟧ υ [ x := f ]
            ≡⟨ ⟦⟧-sub {_} {t} {_} {y} {s} {υ [ x := f ]} cls ⟩
              ⟦ t ⟧ υ [ x := f ] [ y := ⟦ s ⟧ υ [ x := f ] ]
            ≡⟨ cong (λ X → ⟦ t ⟧ υ [ x := f ] [ y := X ])
                    (sym (⟦⟧-extend {_} {s} {υ} {_} {x} {f} (cls (x)))) ⟩
              ⟦ t ⟧ υ [ x := f ] [ y := ⟦ s ⟧ υ ]
            ≡⟨ ⟦⟧-cong-assignment
                 (λ {C} {z} →
                   ~~-swap-≢Name {_} {A₁} {B} {x} {y} {f} {⟦ s ⟧ υ} x≢y {C} {z}) {_} {t} ⟩
              ⟦ t ⟧ υ [ y := ⟦ s ⟧ υ ] [ x := f ]
            ∎))
...  | yes reflN =
       IF-extensionality (funext λ f →
         cong (λ X → X ⊕ f * ⊕ 1)
              (⟦⟧-cong-assignment
                (λ {C} {z} → sym (~~-elim {υ} {_} {x} {⟦ s ⟧ υ} {f} {C} {z}))
                {_} {t}))
⟦⟧-sub {A}       {app t₁ t₂}      {B} {y} {s} {υ} cls =
    proj₁ (⟦ sub t₁ (y) s ⟧ υ) (⟦ sub t₂ (y) s ⟧ υ)
  ≡⟨ cong (λ X → proj₁ X (⟦ sub t₂ (y) s ⟧ υ))
          (⟦⟧-sub {_} {t₁} {_} {y} {s} {υ} cls) ⟩
    proj₁ (⟦ t₁ ⟧ υ [ y := ⟦ s ⟧ υ ]) (⟦ sub t₂ (y) s ⟧ υ)
  ≡⟨ cong (λ X → proj₁ (⟦ t₁ ⟧ υ [ y := ⟦ s ⟧ υ ]) X)
          (⟦⟧-sub {_} {t₂} {_} {y} {s} {υ} cls) ⟩
    proj₁ (⟦ t₁ ⟧ υ [ y := ⟦ s ⟧ υ ]) (⟦ t₂ ⟧ υ [ y := ⟦ s ⟧ υ ])
  ∎

---- Beta reduction decreases the measure of closed terms

beta-decreasing : ∀ {A} {t t' : Term A} {υ : Assignment}
                → closed t
                → t ↦ t'
                → ⟦ t' ⟧ υ ⊏ ⟦ t ⟧ υ
beta-decreasing {_} {app t₁ t₂} {_} {υ}       clt (e-appl step) =
  beta-decreasing (closed-appl clt) step
beta-decreasing {_} {app t₁ t₂} {_} {υ = υ}   clt (e-appr step) =
  proj₂ (⟦ t₁ ⟧ υ) (beta-decreasing (closed-appr clt) step)
beta-decreasing {_} {app (lam x t) s} {_} {υ} clt (e-beta isVal) =
  ⊏-≡-cong {_}
    {⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ]}
    {⟦ sub t x s ⟧ υ}
    {_}
    {⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ] ⊕ ⟦ s ⟧ υ * ⊕ 1}
    (sym (⟦⟧-sub {_} {t} {_} {x} {s} {υ} (closed-appr clt)))
    refl
    (case ((⟦ s ⟧ (λ {A} → υ) *) ≟Nat 0) of λ {
      (no  S≢0) → ⊏-trans
                    (⊕-monot-r0 (≤+≢⇒< z≤n (λ 0≡S → S≢0 (sym 0≡S))))
                    (⊕-monot-r0 (s≤s z≤n))
    ; (yes S≡0) → ⊏-≡-cong {_}
                   {⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ] ⊕ ⟦ s ⟧ υ *}
                   {⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ]}
                   {⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ] ⊕ ⟦ s ⟧ υ * ⊕ 1}
                   {⟦ t ⟧ υ [ x := ⟦ s ⟧ υ ] ⊕ ⟦ s ⟧ υ * ⊕ 1}
                   (⊕-neut-r S≡0)
                   refl
                   (⊕-monot-r0 (s≤s z≤n))
    })

---- Definition of strong normalization

-- The strong normalization predicate follows the definition by Altenkirch
-- (A Formalization of the Strong Normalization Proof for System F in LEGO).

data SN {A : Ty} : Term A → Set where
  SNi : ∀ {t : Term A}
        → (∀ {t' : Term A} → (t ↦ t') → SN t')
        → SN t

---- Strong induction principle for natural numbers

m≢n∧m≤n→1+m≤n : ∀ {n m} → n ≢ m → m ≤ n → suc m ≤ n
m≢n∧m≤n→1+m≤n {zero}  {.0} n≢m z≤n = ⊥-elim (n≢m refl)
m≢n∧m≤n→1+m≤n {suc n} {.0} n≢m z≤n = s≤s z≤n
m≢n∧m≤n→1+m≤n {.(suc _)} {.(suc _)} n≢m (s≤s de) =
  s≤s (m≢n∧m≤n→1+m≤n (λ n≡m → n≢m (cong suc n≡m)) de)

iter : (P : ℕ → Set) → ℕ → Set
iter P zero    = ⊤
iter P (suc n) = P n × iter P n

iter-correct : ∀ P n k → iter P n → k < n → P k
iter-correct P (suc n) k Pns k<n
  with n ≟Nat k
...  | yes refl  = proj₁ Pns
...  | no  n≢1+k =
       iter-correct P n k (proj₂ Pns)
         (case k<n of λ { (s≤s k≤n) → m≢n∧m≤n→1+m≤n n≢1+k k≤n })

strong-ind* : (P : ℕ → Set)
            → (∀ n → (∀ k → k < n → P k) → P n)
            → (∀ n → iter P n)
strong-ind* P Pind zero    = tt
strong-ind* P Pind (suc n) =
  let Pns = strong-ind* P Pind n in
    Pind n (λ { k k<n → iter-correct P n k Pns k<n }),
    Pns

strong-ind : (P : ℕ → Set)
           → (∀ n → (∀ k → k < n → P k) → P n)
           → (∀ n → P n)
strong-ind P Pind n = proj₁ (strong-ind* P Pind (suc n))

---- Proof that every term is strongly normalizing

strong-normalization : {A : Ty} (t : Term A) → closed t → SN t
strong-normalization t clt =
  let bounded-strong-normalization =
        strong-ind (λ N → (∀ {A : Ty} {t : Term A} (clt : closed t) → (⟦ t ⟧ :=𝟘) * ≡ N → SN t))
                   (λ { N HI clt refl →
                     SNi (λ {t'} step →
                       HI ((⟦ t' ⟧ :=𝟘) *)
                          (*-monot (beta-decreasing clt step))
                          (closed-reduce step clt)
                          refl
                     )
                   })
   in bounded-strong-normalization ((⟦ t ⟧ :=𝟘) *) clt refl

