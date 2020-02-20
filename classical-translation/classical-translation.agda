
---- A translation from classical to intuitionistic logic
---- not based on the equivalence A <-> ¬¬A
---- but rather on the equivalence A <-> (¬A -> A).

open import Relation.Nullary using (¬_)
open import Data.Empty       using (⊥; ⊥-elim)
open import Data.Unit        using (⊤; tt)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Product     using (_×_; _,_; proj₁; proj₂)
open import Function         using (case_of_)

---- Formulae

infixr 20 _⇒_

data Form : Set₁ where
  prop : Set → Form
  FF   : Form
  TT   : Form
  _∧_  : Form → Form → Form
  _∨_  : Form → Form → Form
  _⇒_  : Form → Form → Form
  ~_   : Form → Form
  
---- Translation

_+ : Form → Set
_- : Form → Set

prop X +  = ¬ X → X
FF +      = ⊥
TT +      = ⊤
(A ∧ B) + = (A - ⊎ B -) → (A + × B +)
(A ∨ B) + = (A - × B -) → (A + ⊎ B +)
(A ⇒ B) + = (A + × B -) → (A + → B +)
(~ A) +   = A -

prop X -  = X → ¬ X
FF -      = ⊤
TT -      = ⊥
(A ∧ B) - = (A + × B +) → (A - ⊎ B -) 
(A ∨ B) - = (A + ⊎ B +) → (A - × B -)
(A ⇒ B) - = (A + → B +) → (A + × B -)
(~ A) -   = A +

----

-- Classical strengthening:
--   to prove A+ it suffices to prove A- → A+
CS+ : {A : Form} → (A - → A +) → A +
CS- : {A : Form} → (A + → A -) → A -

CS+ {prop X} f = λ p → f (λ _ → p) p
CS+ {FF}     f = f tt
CS+ {TT}     f = tt
CS+ {A ∧ B}  f = λ p → f (λ _ → p) p
CS+ {A ∨ B}  f = λ p → f (λ _ → p) p
CS+ {A ⇒ B}  f = λ p → f (λ _ → p) p
CS+ {~ A}    f = CS- {A} f

CS- {prop X} f = λ p → f (λ _ → p) p
CS- {FF}     f = tt
CS- {TT}     f = f tt
CS- {A ∧ B}  f = λ p → f (λ _ → p) p
CS- {A ∨ B}  f = λ p → f (λ _ → p) p
CS- {A ⇒ B}  f = λ p → f (λ _ → p) p
CS- {~ A}    f = CS+ {A} f

-- Law of excluded middle / explosion principle
--
--   (A ∨ ~A)+   holds
--   (A ∧ ~A)-   holds
--
-- Note that these statements are dual to each other.

lem : {A : Form} → (A ∨ (~ A))+    
lem (a , b) = inj₁ b            ---alt: inj₂ a

non-contradiction : {A : Form} → (A ∧ (~ A))-
non-contradiction (a , b) = inj₁ b      ---alt: inj₂ a

-- "External" non-contradiction principle

non-contradiction' : {A : Form} → A + → A - → ⊥
non-contradiction' {prop X} = λ f g → g (f (λ x → g x (f (g x))))
                                (f (λ x → g x (f (g x))))
non-contradiction' {FF}     = λ x _ → x
non-contradiction' {TT}     = λ _ x → x
non-contradiction' {A ∧ B}  =
  λ f g → non-contradiction' {A}
            (CS+ {A} (λ na → proj₁ (f (inj₁ na))))
            (CS- {A} (λ a →
              ⊥-elim (non-contradiction' {B}
                (CS+ {B} (λ nb → proj₂ (f (inj₂ nb))))
                (CS- {B} (λ b →
                         (case g (a , b) of λ {
                           (inj₁ na) → ⊥-elim (non-contradiction' {A} a na)
                         ; (inj₂ nb) → nb}))))))
non-contradiction' {A ∨ B}  =
  λ f g → non-contradiction' {A}
            (CS+ {A} (λ na →
              ⊥-elim (non-contradiction' {B}
                (CS+ {B} (λ nb →
                   case f (na , nb) of λ {
                     (inj₁ a) → ⊥-elim (non-contradiction' {A} a na)
                   ; (inj₂ b) → b
                   }
                ))
                (CS- {B} (λ b → proj₂ (g (inj₂ b)))))))
            (CS- {A} (λ a → proj₁ (g (inj₁ a))))
non-contradiction' {A ⇒ B}  =
  λ f g →
    non-contradiction' {A}
      (CS+ {A} (λ na → proj₁ (g (λ a → ⊥-elim (non-contradiction' {A} a na)))))
      (CS- {A} (λ a →
        ⊥-elim (non-contradiction' {B}
          (CS+ {B} (λ nb → (f (a , nb) a)))
          (CS- {B} (λ b → (proj₂ (g (λ _ → b))))))))
non-contradiction' {~ A}    = λ x y → non-contradiction' {A} y x

-- Law of contraposition

contrapos : {A B : Form}
          → (A + → B +)
          → (B - → A -)
contrapos {A} {B} f nb = CS- {A} (λ a → ⊥-elim (non-contradiction' {B} (f a) nb))

-- Properties of implication
--
-- (A ⇒ B)+  <--->  A+ → B+

⇒I : {A B : Form}
   → (A + → B +)
   → (A ⇒ B)+
⇒I f _ = f

⇒E : {A B : Form}
   → (A ⇒ B)+
   → A + → B +
⇒E {A} {B} f a = CS+ {B} (λ nb → f (a , nb) a)

-- Properties of conjunction
--
-- (A ∧ B)+  <--->  A+ ∧ B+

∧I : {A B : Form}
   → A + → B + → (A ∧ B) +
∧I a b _ = a , b

∧E₁ : {A B : Form}
    → (A ∧ B) + → A +
∧E₁ {A} p = CS+ {A} (λ na → proj₁ (p (inj₁ na)))

∧E₂ : {A B : Form}
    → (A ∧ B) + → B +
∧E₂ {_} {B} p = CS+ {B} (λ nb → proj₂ (p (inj₂ nb)))

-- Properties of disjunction

∨I₁ : {A B : Form}
   → A + → (A ∨ B) +
∨I₁ a _ = inj₁ a

∨I₂ : {A B : Form}
   → B + → (A ∨ B) +
∨I₂ b _ = inj₂ b

∨E : {A B C : Form}
   → (A ∨ B) +
   → (A + → C +)
   → (B + → C +)
   → C +
∨E {A} {B} {C} p f g =
  CS+ {C} (λ nc → 
    case p (contrapos {A} {C} f nc , contrapos {B} {C} g nc) of λ {
      (inj₁ a) → f a
    ; (inj₂ b) → g b
    })

-- Properties of negation

¬I : {A : Form}
   → (A + → FF +)
   → (~ A)+
¬I {A} f = CS- {A} (λ a → ⊥-elim (f a))

¬E : {A : Form}
   → (~ A)+ → A +
   → FF +
¬E {A} f g = non-contradiction' {A} g f
