
-- Encoding of the full lambda-PRK calculus,
-- including:
--   disjunction, implication, co-implication,
--   and second-order existential quantification
-- in terms of a restricted fragment of lambda-PRK
-- including only:
--   conjunction, negation,
--   and second-order universal quantification.
--
-- Terms and types are represented using higher-order
-- abstract syntax (HOAS), using positive recursion, which
-- requires to side-step Agda's positivity checker.
-- We postulate propositional equalities corresponding
-- to rewriting rules of the lambda-PRK calculus, and
-- we use Agda's builtin rewrite mechanism to
-- strengthen these postulates to definitional equalities.
--
-- Note that we do not use Agda to actually *prove*
-- properties about the system, rather we use it as a
-- convenient tool to be able to type-check and
-- rewrite terms.

{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

infix  50  _+ _- _⊕ _⊝
infix  60 _><_
infixr 60  Π
infixr 60  Σ
infixr 70  _!_
infixr 70  _⇒_
infixl 80  _∨_
infixl 90  _∧_
infix  100 ¬_

{-# NO_POSITIVITY_CHECK #-}
data Pure : Set where
  _∧_  : Pure → Pure → Pure
  ¬_   : Pure → Pure
  Π    : (Pure → Pure) → Pure

syntax Π (λ A → B) = Π A ∙ B
syntax Σ (λ A → B) = Σ A ∙ B

variable A B C : Pure
variable A[_] B[_] : Pure → Pure

---- Types
data Type : Set where
  _+ : Pure → Type
  _- : Pure → Type
  _⊕ : Pure → Type
  _⊝ : Pure → Type

variable P Q R P₁ P₂ : Type

---- Terms
{-# NO_POSITIVITY_CHECK #-}
data T : Type → Set where
  ---- Absurdity
  _><_  : T (A +) → T (A -) → T P
  ---- Positive half
  I∧+   : T (A ⊕) → T (B ⊕) → T (A ∧ B +)
  E∧+₁  : T (A ∧ B +) → T (A ⊕)
  E∧+₂  : T (A ∧ B +) → T (B ⊕)
  IΠ+   : (∀ B → T (A[ B ] ⊕)) → T (Π α ∙ A[ α ] +)
  EΠ+   : T (Π α ∙ A[ α ] +) → ∀ B → T (A[ B ] ⊕)
  I¬+   : T (A ⊝) → T (¬ A +)
  E¬+   : T (¬ A +) → T (A ⊝)
  I⊕    : (T (A ⊝) → T (A +)) → T (A ⊕)
  E⊕    : T (A ⊕) → T (A ⊝) → T (A +)
  ---- Negative half
  I∧-₁  : T (A ⊝) → T (A ∧ B -)
  I∧-₂  : T (B ⊝) → T (A ∧ B -)
  E∧-   : T (A ∧ B -) → (T(A ⊝) → T P) → (T (B ⊝) → T P) → T P 
  IΠ-   : ∀ B → T (A[ B ] ⊝) → T (Π α ∙ A[ α ] -)
  EΠ-   : T (Π α ∙ A[ α ] -) → (∀ α → T (A[ α ] ⊝) → T P) → T P
  I¬-   : T (A ⊕) → T (¬ A -)
  E¬-   : T (¬ A -) → T (A ⊕)
  I⊝    : (T (A ⊕) → T (A -)) → T (A ⊝)
  E⊝    : T (A ⊝) → T (A ⊕) → T (A -)

variable t s u t' s' u' : T P

variable t[_] s[_] u[_] t'[_] s'[_] u'[_] : T P → T Q

variable t<_> s<_> u<_> t'<_> s'<_> u'<_> : Pure → T P

_~ : Type → Type
(A +) ~ = A -
(A -) ~ = A +
(A ⊕) ~ = A ⊝
(A ⊝) ~ = A ⊕

abs : ∀ Q {P} → T P → T (P ~) → T Q
abs _ {x +}  t s = t >< s
abs _ {x - } t s = s >< t
abs _ {x ⊕}  t s = E⊕ t s >< E⊝ s t
abs _ {x ⊝}  t s = E⊕ s t >< E⊝ t s

contrapos+ : (T (A ⊕) → T (B ⊕)) → T (B ⊝) → T (A ⊝)
contrapos+ f b = I⊝ (λ a → abs _ (f a) b)

contrapos- : (T (A ⊝) → T (B ⊝)) → T (B ⊕) → T (A ⊕)
contrapos- f b = I⊕ (λ a → abs _ (f a) b)

---- Reduction rules

-- Absurdity computation rules
postulate ><∧₁  : I∧+ t s  >< I∧-₁ u     ≡ abs P t u
postulate ><∧₂  : I∧+ t s  >< I∧-₂ u     ≡ abs P s u
postulate ><¬   : I¬+ t    >< I¬- s      ≡ abs P t s
postulate ><Π   : ∀ {t<_> : ∀ β → T (A[ β ] ⊕)}
                  → IΠ+ t<_> >< IΠ- B s  ≡ abs P t< B > s
-- Positive computation rules
postulate β∧+₁ : E∧+₁ (I∧+ t s)          ≡ t
postulate β∧+₂ : E∧+₂ (I∧+ t s)          ≡ s
postulate β¬+  : E¬+ (I¬+ t)             ≡ t
postulate βΠ+  : ∀ {t<_> : ∀ β → T (A[ β ] ⊕)}
                 → EΠ+ (IΠ+ t<_>) B      ≡ t< B >
postulate β⊕   : E⊕ (I⊕ t[_]) s          ≡ t[ s ]
-- Negative computation rules
postulate β∧-₁ : E∧- (I∧-₁ t) s[_] u[_]  ≡ s[ t ]
postulate β∧-₂ : E∧- (I∧-₂ t) s[_] u[_]  ≡ u[ t ]
postulate β¬-  : E¬- (I¬- t)             ≡ t
postulate βΠ-  : ∀ {t : T (A[ B ] ⊝)}
                   {s<_>[_] : ∀ β → T (A[ β ] ⊝) → T P}
                 → EΠ- (IΠ- B t) s<_>[_] ≡ s< B >[ t ]
postulate β⊝   : E⊝ (I⊝ t[_]) s          ≡ t[ s ]
-- Eta rules
postulate η⊕   : I⊕ (λ x → E⊕ t x)       ≡ t
postulate η⊝   : I⊝ (λ x → E⊝ t x)       ≡ t

{-# REWRITE ><∧₁ ><∧₂ ><¬ ><Π #-}
{-# REWRITE β∧+₁ β∧+₂ β¬+ βΠ+ β⊕ #-}
{-# REWRITE β∧-₁ β∧-₂ β¬- βΠ- β⊝ #-}
{-# REWRITE η⊕ η⊝ #-}

-- Weak rules of negation

I¬⊕ : T (A ⊝) → T (¬ A ⊕)
I¬⊕ t = I⊕ λ _ → I¬+ t

I¬⊝ : T (A ⊕) → T (¬ A ⊝)
I¬⊝ t = I⊝ λ _ → I¬- t

E¬⊕ : T (¬ A ⊕) → T (A ⊝)
E¬⊕ t = I⊝ λ a → E⊝ (E¬+ (E⊕ t (I¬⊝ a))) a

E¬⊝ : T (¬ A ⊝) → T (A ⊕)
E¬⊝ t = I⊕ λ a → E⊕ (E¬- (E⊝ t (I¬⊕ a))) a

><¬∘ : abs P (I¬⊕ t) (I¬⊝ s) ≡ abs P t s
><¬∘ = refl

β¬⊕ : E¬⊕ (I¬⊕ t) ≡ t
β¬⊕ = refl

β¬⊝ : E¬⊝ (I¬⊝ t) ≡ t
β¬⊝ = refl

---------------- Encodings ---------------- 

-------- Encoding of disjunction --------

_∨_ : Pure → Pure → Pure
A ∨ B = ¬(¬ A ∧ ¬ B)

---- [Weak] positive disjunction

I∨+₁ : T (A ⊕) → T (A ∨ B +)
I∨+₁ t = I¬+ (I⊝ λ _ → I∧-₁ (I⊝ λ _ → I¬- t))

I∨+₂ : T (B ⊕) → T (A ∨ B +)
I∨+₂ t = I¬+ (I⊝ λ _ → I∧-₂ (I⊝ λ _ → I¬- t))

E∨+ : T (A ∨ B +) → (T (A ⊕) → T (C ⊕)) → (T (B ⊕) → T (C ⊕)) → T (C ⊕)
E∨+ t s[_] u[_] =
  I⊕ λ c →
    E⊕ (E∧- (E⊝ (E¬+ t) (I⊕ λ _ → I∧+ (I⊕ λ _ → I¬+ (contrapos+ s[_] c))
                                      (I⊕ λ _ → I¬+ (contrapos+ u[_] c))))
          (λ a → s[ I⊕ (λ x → E⊕ (E¬- (E⊝ a (I⊕ λ _ → I¬+ x))) x) ])
          (λ b → u[ I⊕ (λ x → E⊕ (E¬- (E⊝ b (I⊕ λ _ → I¬+ x))) x) ]))
       c

-- Negative disjunction

I∨- : T (A ⊝) → T (B ⊝) → T (A ∨ B -)
I∨- t s = I¬- (I⊕ λ _ → I∧+ (I⊕ λ _ → I¬+ t) (I⊕ λ _ → I¬+ s))

E∨-₁ : T (A ∨ B -) → T (A ⊝)
E∨-₁ t = I⊝ λ x →
           let a = I⊝ λ _ → I¬- x in
             E⊝ (E¬+ (E⊕ (E∧+₁ (E⊕ (E¬- t) (I⊝ λ _ → I∧-₁ a))) a)) x

E∨-₂ : T (A ∨ B -) → T (B ⊝)
E∨-₂ t = I⊝ λ x →
           let b = I⊝ λ _ → I¬- x in
             E⊝ (E¬+ (E⊕ (E∧+₂ (E⊕ (E¬- t) (I⊝ λ _ → I∧-₂ b))) b)) x

-- (Trivial) proof that computation rules for disjunction hold

><∨+₁ : I∨+₁ t >< I∨- s u ≡ abs P t s
><∨+₁ = refl

><∨+₂ : I∨+₂ t >< I∨- s u ≡ abs P t u
><∨+₂ = refl

β∨+₁ : E∨+ (I∨+₁ t) s[_] u[_] ≡ s[ t ] 
β∨+₁ = refl

β∨+₂ : E∨+ (I∨+₂ t) s[_] u[_] ≡ u[ t ] 
β∨+₂ = refl

β∨-₁ : E∨-₁ (I∨- t s) ≡ t
β∨-₁ = refl

β∨-₂ : E∨-₂ (I∨- t s) ≡ s
β∨-₂ = refl

-------- Encoding of implication --------

_⇒_ : Pure → Pure → Pure
A ⇒ B = ¬(A ∧ ¬ B)

-- Positive implication

I⇒+ : (T (A ⊕) → T (B ⊕)) → T (A ⇒ B +)
I⇒+ t[_] =
  I¬+ (I⊝ λ x → I∧-₂ (I⊝ λ y → I¬- t[
    E∧+₁ (E⊕ x (I⊝ λ _ → I∧-₁ (I⊝ λ a → E⊝ (abs _ y (I⊝ λ _ → I¬- t[ a ])) a)))
  ]))

E⇒+ : T (A ⇒ B +) → T (A ⊕) → T (B ⊕)
E⇒+ t s = I⊕ λ b →
            E⊕ (E¬- (E⊝ (E∧- (E⊝ (E¬+ t)
                                 (I⊕ λ _ → I∧+ s
                                               (I⊕ λ _ → I¬+ b)))
                             (λ a → abs _ s a)
                             (λ x → x))
                        (I⊕ λ _ → I¬+ b)))
               b

-- Negative implication

I⇒- : T (A ⊕) → T (B ⊝) → T (A ⇒ B -)
I⇒- t s = I¬- (I⊕ λ x → I∧+ t (I⊕ λ _ → I¬+ s))

E⇒-₁ : T (A ⇒ B -) → T (A ⊕)
E⇒-₁ t = I⊕ λ a → E⊕ (E∧+₁ (E⊕ (E¬- t) (I⊝ λ _ → I∧-₁ a))) a

E⇒-₂ : T (A ⇒ B -) → T (B ⊝)
E⇒-₂ t = I⊝ λ b →
           E⊝ (E¬+ (E⊕
             (E∧+₂ (E⊕ (E¬- t) (I⊝ λ _ → I∧-₂ (I⊝ λ _ → I¬- b))))
             (I⊝ λ _ → I¬- b))) b

-- (Trivial) proof that computation rules for implication hold

><⇒ : I⇒+ t[_] >< I⇒- s u ≡ abs P t[ s ] u
><⇒ = refl

β⇒+ : E⇒+ (I⇒+ t[_]) s ≡ t[ s ]
β⇒+ = refl

β⇒-₁ : E⇒-₁ (I⇒- t s) ≡ t
β⇒-₁ = refl

β⇒-₂ : E⇒-₂ (I⇒- t s) ≡ s
β⇒-₂ = refl

-------- Encoding of co-implication --------

_!_ : Pure → Pure → Pure
A ! B = ¬ ¬ (¬ A ∧ B)

-- Positive co-implication

I!+ : T (A ⊝) → T (B ⊕) → T (A ! B +)
I!+ t s = I¬+ (I¬⊝ (I⊕ λ _ → I∧+ (I⊕ λ _ → I¬+ t) s))

E!+₁ : T (A ! B +) → T (A ⊝)
E!+₁ t = I⊝ λ a → E⊝ (E¬+ (E⊕ (E∧+₁ (E⊕ (E¬⊝ (E¬+ t))
                                        (I⊝ λ _ → I∧-₁ (I¬⊝ a))))
                              (I⊝ λ _ → I¬- a))) a

E!+₂ : T (A ! B +) → T (B ⊕)
E!+₂ t = I⊕ λ b → E⊕ (E∧+₂ (E⊕ (E¬⊝ (E¬+ t)) (I⊝ λ _ → I∧-₂ b))) b

-- Negative co-implication

I!- : (T (A ⊝) → T (B ⊝)) → T (A ! B -)
I!- t[_] = I¬- (I¬⊕ (I⊝ λ x →
             I∧-₂ (I⊝ λ y →
              E⊝ (t[
                    (E¬⊕ (E∧+₁ (E⊕ x (I⊝ λ _ → I∧-₁
                       (I⊝ λ a → E⊝ (abs _ y (t[ E¬⊕ a ])) a)
                    ))))
                  ])
                 y)))

E!- : T (A ! B -) → T (A ⊝) → T (B ⊝)  
E!- t s =
  I⊝ λ b →
    E⊝ (E¬+ (E⊕ (E∧- (E⊝ (E¬⊕ (E¬- t))
                         (I⊕ λ _ → I∧+ (I¬⊕ s) b))
                     (λ a → abs _ s (E¬⊝ a))
                     (λ x → I¬⊕ x))
                (I¬⊝ b)))
       b

-- (Trivial) proof that computation rules for co-implication hold

><! : I!+ t s >< I!- u[_] ≡ abs P s u[ t ]
><! = refl

β!+₁ : E!+₁ (I!+ t s) ≡ t
β!+₁ = refl

β!+₂ : E!+₂ (I!+ t s) ≡ s
β!+₂ = refl

β!- : E!- (I!- t[_]) s ≡ t[ s ]
β!- = refl

-------- Encoding of existential --------

Σ : (Pure → Pure) → Pure
Σ A[_] = ¬ (Π α ∙ ¬ A[ α ])

-- [Weak] positive existential

IΣ+ : (B : Pure) → T (A[ B ] ⊕) → T (Σ A[_] +)
IΣ+ B t = I¬+ (I⊝ λ _ → IΠ- B (I⊝ λ _ → I¬- t))

EΣ+ : T (Σ A[_] +) → (∀ α → T (A[ α ] ⊕) → T (B ⊕)) → T (B ⊕)
EΣ+ t f = I⊕ λ b →
  let z α = I⊕ λ x → abs _ b (f α (I⊕ λ a → E⊕ (E¬- (E⊝ x (I¬⊕ a))) a))
   in E⊕ (EΠ- (E⊝ (E¬+ t) (I⊕ λ _ → IΠ+ z)) (λ α s → f α (E¬- (E⊝ s (z α))))) b

-- Negative existential

IΣ- : (∀ β → T (A[ β ] ⊝)) → T (Σ A[_] -)
IΣ- t<_> = I¬- (I⊕ λ _ → IΠ+ (λ β → I⊕ λ _ → I¬+ t< β >))

EΣ- : T (Σ A[_] -) → ∀ B → T (A[ B ] ⊝)
EΣ- t B = I⊝ λ a →
            E⊝ (E¬+ (E⊕ (EΠ+ (E⊕ (E¬- t)
                                 (I⊝ λ _ → IΠ- B (I⊝ λ _ → I¬- a)))
                             B)
                        (I⊝ λ _ → I¬- a)))
               a

-- (Trivial) proof that computation rules for existential hold

><Σ : ∀ {s<_> : ∀ β → T (A[ β ] ⊝)}
      → IΣ+ B t >< IΣ- s<_> ≡ abs P t s< B >
><Σ = refl

βΣ+ : ∀ {t : T (A[ B ] ⊕)}
        {s<_>[_] : ∀ β → T (A[ β ] ⊕) → T (B ⊕)}
      → EΣ+ (IΣ+ B t) s<_>[_] ≡ s< B >[ t ]
βΣ+ = refl

βΣ- : ∀ {t<_> : ∀ β → T (A[ β ] ⊝)}
      → EΣ- (IΣ- t<_>) B ≡ t< B >
βΣ- = refl
