
---- A construction of the natural numbers without using the
---- induction principle. 

open import Agda.Primitive using (lzero; lsuc)

------------------------------------------------------------

-- Empty

data ⊥ {ℓ} : Set ℓ where

⊥-elim : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₂} → ⊥ {ℓ₁} → A
⊥-elim ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬_ {ℓ} A = A → ⊥ {ℓ}

-- Unit

data ⊤ {ℓ} : Set ℓ where
  tt : ⊤ {ℓ}
  
-- Product

data Σ {ℓ} (A : Set ℓ) (B : A → Set ℓ) : Set ℓ where
  _,_ : (a : A) → B a → Σ A B

-- Sum

data _⊎_ {ℓ} (A B : Set ℓ) : Set ℓ where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Lift

record Lift {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  constructor lift
  field
    unlift : A
open Lift
  
-- Decidable

data Dec {ℓ} (A : Set ℓ) : Set ℓ where
  yes : A → Dec A
  no  : ¬ A → Dec A

-- Propositional equality

data _≡_ {ℓ} : {A : Set ℓ} → A → A → Set ℓ where
  refl : {A : Set ℓ} {a : A} → a ≡ a

sym : ∀ {ℓ} {A : Set ℓ} {a₁ a₂ : A}
      → a₁ ≡ a₂
      → a₂ ≡ a₁
sym refl = refl

trans : ∀ {ℓ} {A : Set ℓ} {a₁ a₂ a₃ : A}
        → a₁ ≡ a₂
        → a₂ ≡ a₃
        → a₁ ≡ a₃
trans refl refl = refl

cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {a₁ a₂ : A}
       → a₁ ≡ a₂
       → f a₁ ≡ f a₂
cong _ refl = refl

_≢_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
a₁ ≢ a₂ = ¬(a₁ ≡ a₂)

-- (Not used currently)
-- transport : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} (B : A → Set ℓ₂) {a₁ a₂ : A} → (a₁ ≡ a₂) → B a₁ → B a₂
-- transport _ refl x = x

transport* : ∀ {ℓ} {A B : Set ℓ} → (A ≡ B) → A → B
transport* refl x = x

-- Equational reasoning

infixr 10 begin_
infixr 20 _≡⟨_⟩_
infix  21 _∎

begin_ : ∀ {ℓ} {A : Set ℓ} {a b : A} → a ≡ b → a ≡ b
begin p = p

_∎ : ∀ {ℓ} {A : Set ℓ} → (a : A) → a ≡ a
_ ∎ = refl

_≡⟨_⟩_ : ∀ {ℓ} {A : Set ℓ} → (a : A) {b : A} → a ≡ b → {c : A} → b ≡ c → a ≡ c
_ ≡⟨ p ⟩ q = trans p q

------------------------------------------------------------

-- NUM is the type of numerals.

postulate NUM : Set

-- Weak variant of the peano axioms:
--   No induction/recursion principle,
--   Allows pattern matching.
--
-- A typical numeral N is encoded as numS (numS ... (numS num0)),
-- but we have no guarantee that these are the only numerals.
--
postulate num0     : NUM
postulate numS     : NUM → NUM
postulate zero≢suc : {a : NUM} → num0 ≢ numS a
postulate suc-inj  : {a b : NUM} → numS a ≡ numS b → a ≡ b
postulate match    : (a : NUM) → (a ≡ num0) ⊎ Σ NUM (λ b → a ≡ numS b)

------------------------------------------------------------

-- SMALL is the type of smallness predicates
--
-- smallN is a predicate that holds for numerals up to N
--
-- Informally:
--     smallN a <=> ((a = 0) ⊎ (a = 1) ⊎ ... ⊎ (a = N))
--
-- Practically, smallN may be defined by iterating
-- smallS N times:
--     smallN = smallS (... (smallS small0))
--
-- But there is no general rule to build smallN.

SMALL : Set₁
SMALL = NUM → Set

small0 : SMALL
small0 n = n ≡ num0

smallS : SMALL → SMALL
smallS small n with match n
... | inj₁ refl     = ⊤
... | inj₂ (n' , _) = small n'

-- E.g.:
-- small3 : SMALL
-- small3 = smallS (smallS (smallS small0))

num-small-0 : small0 num0
num-small-0 = refl

-- If n is small, (numS n) is (smallS small).
num-small-S : {small : SMALL} {n : NUM}
            → small n
            → smallS small (numS n)
num-small-S {small} {n} num-small with match (numS n)
... | inj₁ p        = ⊥-elim (zero≢suc (sym p))
... | inj₂ (n' , p)
    with suc-inj p
...    | refl = num-small

------------------------------------------------------------

-- (REC small) is the type of recursion principles
-- for small numbers.
--
-- recN is the induction principle for numerals up to N
--
-- Informally:
--   If:
--     cz : C
--     cs : C → C
--   then:
--     recN C cz cs
--   constructs an inhabitant of C for all small numerals,
--   by iterating cs N times.
--
-- Practically, recN may be defined by iterating
-- recS N times:
--     recN = recS (... (recS rec0))
--
-- But there is no general rule to build recN.

REC : ∀ {ℓ} → SMALL → Set (lsuc ℓ)
REC {ℓ} small = (X : Set ℓ)
              → X
              → (X → X)
              → (n : NUM)
              → small n
              → X

rec0 : ∀ {ℓ} → REC {ℓ} small0
rec0 X cz cs .num0 refl = cz

recS : ∀ {ℓ} {small : SMALL} → REC {ℓ} small → REC {ℓ} (smallS small)
recS rec X cz cs n ns with match n
... | inj₁ refl     = cz
... | inj₂ (n' , _) = cs (rec X cz cs n' ns)

------------------------------------------------------------

-- (IND small rec) is the type of induction principles
-- for small numbers with a given recursion principle.
--
-- Informally:
--   If:
--     cz : P CZ
--     cs : P x → P (CS x)
--   then:
--     indN P CZ CS cz cs
--   constructs an inhabitant of P(CS(CS...(CS CZ)...))
--   for all small numerals, by iterating
--   cs(cs(...(cs cz)...)).
--
-- indN is the induction principle for numerals up to N
--
-- Practically, indN may be defined by iterating
-- indS N times:
--     indN = indS (... (indS ind0))

IND : ∀ {ℓ} (small : SMALL) → REC small → Set (lsuc ℓ)
IND {ℓ} small rec = (X : Set ℓ) (P : X → Set ℓ)
                  → (CZ : X) (CS : X → X) 
                  → P CZ
                  → (∀ x → P x → P (CS x))
                  → (n : NUM)
                  → (ns : small n)
                  → P (rec X CZ CS n ns)
                  
ind0 : ∀ {ℓ} → IND {ℓ} small0 rec0
ind0 X P CZ CS cz cs .num0 refl = cz

indS : ∀ {ℓ} {small : SMALL} {rec : REC small}
       → IND {ℓ} small rec
       → IND {ℓ} (smallS small) (recS rec)
indS ind X P CZ CS cz cs n ns with match n
... | inj₁ refl     = cz
... | inj₂ (n' , _) = cs _ (ind X P CZ CS cz cs n' ns)

------------------------------------------------------------

-- ℕ is the type of "natural numbers".
--
-- Informally, it is given by:
--   A numeral.
--   A smallness predicate.
--   A recursion principle.
--   An induction principle.
--   Evidence that the numeral is small.
record ℕ ℓ : Set (lsuc ℓ) where
  field
    num       : NUM
    small     : SMALL
    rec       : REC {ℓ} small
    ind       : IND {ℓ} small rec
    num-small : small num

zero : ∀ {ℓ} → ℕ ℓ
zero = record { num       = num0
              ; small     = small0
              ; rec       = rec0
              ; ind       = ind0
              ; num-small = num-small-0
              }

suc : ∀ {ℓ} → ℕ ℓ → ℕ ℓ
suc n = record { num       = numS (ℕ.num n)
               ; small     = smallS (ℕ.small n)
               ; rec       = recS (ℕ.rec n)
               ; ind       = indS (ℕ.ind n)
               ; num-small = num-small-S (ℕ.num-small n)
               }

---- Recursion principle

recℕ : ∀ {ℓ}
       → (X : Set ℓ)
       → X
       → (X → X)
       → ∀ (n : ℕ ℓ)
       → X
recℕ X cz cs n = ℕ.rec n X cz cs (ℕ.num n) (ℕ.num-small n)

recℕ-zero : ∀ {ℓ X cz cs} → recℕ {ℓ} X cz cs zero ≡ cz
recℕ-zero = refl

recℕ-suc : ∀ {ℓ X cz cs} {n : ℕ ℓ}
           → recℕ {ℓ} X cz cs (suc n) ≡ cs (recℕ {ℓ} X cz cs n)
recℕ-suc {n = n} with match (ℕ.num (suc n))
... | inj₁ p        = ⊥-elim (zero≢suc (sym p))
... | inj₂ (n' , p)
    with suc-inj p
...    | refl = refl

---- Induction principle

sink : ∀ {ℓ} → ℕ (lsuc ℓ) → ℕ ℓ
sink = recℕ _ zero suc

sink-zero : ∀ {ℓ}
           → sink (zero {lsuc ℓ}) ≡ zero {ℓ}
sink-zero {ℓ} = recℕ-zero {cs = suc}

sink-suc : ∀ {ℓ} {n : ℕ (lsuc ℓ)}
           → sink (suc n) ≡ suc (sink n)
sink-suc {ℓ} {n} =
  recℕ-suc {lsuc ℓ} {_} {zero} {suc} {n}

indℕ : ∀ {ℓ}
       → (P : ℕ ℓ → Set ℓ)
       → P zero
       → (∀ n → P n → P (suc n))
       → ∀ (n : ℕ (lsuc ℓ)) → P (sink n)
indℕ {ℓ} P cz cs n =
  unlift
   (ℕ.ind n
          (ℕ ℓ) (λ x → Lift (P x)) zero suc
          (lift cz)
          (λ { _ (lift p) → lift (cs _ p) })
          (ℕ.num n)
          (ℕ.num-small n))
          
indℕ-zero : ∀ {ℓ P cz cs}
            → indℕ {ℓ} P cz cs zero ≡ cz
indℕ-zero = refl

indℕ-suc : ∀ {ℓ P cz cs} {n : ℕ (lsuc ℓ)}
           → indℕ {ℓ} P cz cs (suc n) ≡
             transport* (cong P (sym (sink-suc {ℓ} {n})))
                        (cs _ (indℕ {ℓ} P cz cs n))
indℕ-suc {n = n} with match (ℕ.num (suc n))
... | inj₁ p        = ⊥-elim (zero≢suc (sym p))
... | inj₂ (n' , p)
    with suc-inj p
...    | refl = refl

------------------------------------------------------------

---- isZero

isZero : ∀ {ℓ} → ℕ (lsuc ℓ) → Set ℓ
isZero = recℕ _ ⊤ (λ _ → ⊥)

isZero-zero : ∀ {ℓ} → isZero {ℓ} zero
isZero-zero = tt

¬isZero-suc : ∀ {ℓ} {n : ℕ (lsuc ℓ)}
              → ¬ isZero (suc n)
¬isZero-suc {ℓ} {n} x = transport* (recℕ-suc {n = n}) x

isZero-dec : ∀ {ℓ} {n : ℕ (lsuc (lsuc ℓ))}
             → Dec {ℓ} (isZero {ℓ} (sink n))
isZero-dec {ℓ} {n} = 
  let z = Dec {ℓ} (isZero {ℓ} (sink n)) in 
      unlift
        (indℕ (λ n → Lift (Dec {ℓ} (isZero {ℓ} n)))
              (lift (yes isZero-zero))
              (λ { n _ → lift (no (¬isZero-suc {n = n}))})
              n)

---- Addition

sink² : ∀ {ℓ} → ℕ (lsuc (lsuc ℓ)) → ℕ ℓ
sink² n = sink (sink n)

infixl 30 _+_

_+_ : ∀ {ℓ} → ℕ (lsuc ℓ) → ℕ ℓ → ℕ ℓ
n + m = recℕ _ m suc n

sink-+ : ∀ {ℓ} {n : ℕ (lsuc (lsuc (lsuc ℓ)))} {m : ℕ (lsuc ℓ)}
         → sink (sink n + m) ≡ sink² n + sink m
sink-+ {ℓ} {n} {m} =
  unlift
    (indℕ (λ n → Lift (sink (n + m) ≡ sink n + sink m))
      (lift refl)
      (λ { n' (lift IH) → lift (
        begin
        sink (suc n' + m)
          ≡⟨ cong sink (recℕ-suc {n = n'}) ⟩
        sink (suc (n' + m))
          ≡⟨ sink-suc {n = n' + m} ⟩
        suc (sink (n' + m))
          ≡⟨ cong suc IH ⟩
        suc (sink n' + sink m)
          ≡⟨ sym (recℕ-suc {n = sink n'}) ⟩
        suc (sink n') + sink m
          ≡⟨ cong (_+ (sink m)) (sym (sink-suc {n = n'})) ⟩
        sink (suc n') + sink m
          ∎
      )})
      n)

+-neut-l : ∀ {ℓ} {n : ℕ ℓ}
           → zero + n ≡ n
+-neut-l = refl

+-neut-r : ∀ {ℓ} {n : ℕ (lsuc ℓ)}
           → n + zero ≡ sink n
+-neut-r = refl

+-assoc : ∀ {ℓ}
            {n : ℕ (lsuc (lsuc (lsuc ℓ)))}
            {m : ℕ (lsuc ℓ)}
            {p : ℕ ℓ}
          → sink² n + (m + p) ≡ (sink n + m) + p
+-assoc {ℓ} {n} {m} {p} =
  unlift
    (indℕ (λ n → Lift (sink n + (m + p) ≡ (n + m) + p))
      (lift refl)
      (λ { n' (lift IH) → lift (
        begin
        sink (suc n') + (m + p)
          ≡⟨ cong (_+ _) (sink-suc {n = n'}) ⟩
        suc (sink n') + (m + p)
          ≡⟨ recℕ-suc {n = sink n'} ⟩
        suc (sink n' + (m + p))
          ≡⟨ cong suc IH ⟩
        suc ((n' + m) + p)
          ≡⟨ sym (recℕ-suc {n = n' + m}) ⟩
        suc (n' + m) + p
          ≡⟨ cong (_+ p) (sym (recℕ-suc {n = n'})) ⟩
        (suc n' + m) + p
          ∎
        )})
      n)
      
+-suc-right : ∀ {ℓ} {n : ℕ (lsuc (lsuc ℓ))} {m : ℕ ℓ}
              → suc (sink n + m) ≡ sink n + suc m
+-suc-right {ℓ} {n} {m} =
  indℕ (λ n → suc (n + m) ≡ n + suc m)
       refl
       (λ n' IH →
          begin
          suc (suc n' + m)
            ≡⟨ cong suc (recℕ-suc {n = n'}) ⟩
          suc (suc (n' + m))
            ≡⟨ cong suc IH ⟩
          suc (n' + suc m)
            ≡⟨ sym (recℕ-suc {n = n'}) ⟩
          suc n' + suc m
            ∎)
       n

+-comm : ∀ {ℓ} {n m : ℕ (lsuc (lsuc ℓ))}
         → sink n + sink² m ≡ sink m + sink² n
+-comm {ℓ} {n} {m} =
  indℕ (λ n → n + sink² m ≡ sink m + sink n)
       refl
       (λ n' IH →
        begin
        suc n' + sink² m
          ≡⟨ recℕ-suc {n = n'} ⟩
        suc (n' + sink² m)
          ≡⟨ cong suc IH ⟩
        suc (sink m + sink n')
          ≡⟨ +-suc-right {n = m} ⟩
        sink m + suc (sink n')
          ≡⟨ cong (_+_ (sink m)) (sym (sink-suc {n = n'})) ⟩
        sink m + sink (suc n')
          ∎)
       n

---- Product

infixl 40 _*_

_*_ : ∀ {ℓ} → ℕ (lsuc ℓ) → ℕ (lsuc ℓ) → ℕ ℓ
n * m = recℕ _ zero (_+_ m) n

*-neut-l : ∀ {ℓ} {n : ℕ (lsuc ℓ)}
           → suc zero * n ≡ sink n
*-neut-l {ℓ} {n} =
    begin
    suc zero * n
      ≡⟨ recℕ-suc {n = zero} ⟩
    n + zero
      ≡⟨ +-neut-r {n = n} ⟩
    sink n
      ∎

*-neut-r : ∀ {ℓ} {n : ℕ (lsuc (lsuc ℓ))}
           → sink n * suc zero ≡ sink² n
*-neut-r {ℓ} {n} =
  indℕ (λ n → n * suc zero ≡ sink n)
    refl
    (λ n' IH →
      begin
      suc n' * suc zero
        ≡⟨ recℕ-suc {n = n'} ⟩
      suc zero + n' * suc zero
        ≡⟨ recℕ-suc {n = zero} ⟩
      suc (n' * suc zero)
        ≡⟨ cong suc IH ⟩
      suc (sink n')
        ≡⟨ sym (sink-suc {n = n'}) ⟩
      sink (suc n')
        ∎)
    n

---- Relation with the usual natural numbers

data Nat : Set where
  zeroN : Nat
  sucN  : Nat → Nat

Nat⇒ℕ : Nat → ℕ lzero
Nat⇒ℕ zeroN    = zero
Nat⇒ℕ (sucN n) = suc (Nat⇒ℕ n)

ℕ⇒Nat : ℕ lzero → Nat
ℕ⇒Nat = recℕ Nat zeroN sucN

ℕ⇒Nat⇒ℕ : ∀ {n : Nat}
          → ℕ⇒Nat (Nat⇒ℕ n) ≡ n
ℕ⇒Nat⇒ℕ {zeroN}  = refl
ℕ⇒Nat⇒ℕ {sucN n} = begin
                     ℕ⇒Nat (suc (Nat⇒ℕ n))
                   ≡⟨ recℕ-suc {n = Nat⇒ℕ n} ⟩
                     sucN (ℕ⇒Nat (Nat⇒ℕ n))
                   ≡⟨ cong sucN ℕ⇒Nat⇒ℕ ⟩
                     sucN n
                   ∎

Nat⇒ℕ⇒Nat : ∀ {n : ℕ (lsuc (lsuc lzero))}
            → Nat⇒ℕ (ℕ⇒Nat (sink² n)) ≡ sink² n
Nat⇒ℕ⇒Nat {n} = indℕ (λ n → Nat⇒ℕ (ℕ⇒Nat (sink n)) ≡ sink n)
                     refl
                     (λ n IH →
                       begin
                         Nat⇒ℕ (ℕ⇒Nat (sink (suc n)))
                       ≡⟨ cong Nat⇒ℕ (cong ℕ⇒Nat (sink-suc {n = n})) ⟩
                         Nat⇒ℕ (ℕ⇒Nat (suc (sink n)))
                       ≡⟨ cong Nat⇒ℕ (recℕ-suc {n = sink n}) ⟩
                         Nat⇒ℕ (sucN (ℕ⇒Nat (sink n)))
                       ≡⟨ refl ⟩
                         suc (Nat⇒ℕ (ℕ⇒Nat (sink n)))
                       ≡⟨ cong suc IH ⟩
                         suc (sink n)
                       ≡⟨ sym (sink-suc {n = n}) ⟩
                         sink (suc n)
                       ∎)
                     n

