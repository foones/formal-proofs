
----
---- Soundness and completeness of classical propositional logic
----
---- The idea of the completness proof is as follows.
----
---- - If Γ is a context and v a valuation,
----   we say that (Γ, v) is specified for a propositional variable P
----      if v(P) = 1 implies that P occurs in Γ
----     and v(P) = 0 implies that ¬P occurs in Γ.
---- - We say that (Γ, v) is specified for a formula A
----     if v ⊨ A  implies Γ ⊢ A
----    and v ⊨ ¬A implies Γ ⊢ ¬A.
---- - Prove the "Main Semantic Lemma" ("sem" below), saying that
----     if (Γ, v) is specified for all the propositional variables in A
----   then (Γ, v) is specified for A.
---- - To prove that all tautologies are provable, suppose that ⊨ A
----   and using the law of excluded middle reduce proving ⊢ A
----   to proving Γ ⊢ A for all 2^n combinations in which the propositional
----   variables of A can be affirmed/denied.
----   Each combination determines a context Γ and a valuation v
----   such that (Γ, v) is specified for all the propositional variables in A,
----   hence (Γ, v) is specified for A,
----   and since v ⊨ A (because A is a tautology)
----   we have Γ ⊢ A.
----

open import Data.Nat using (ℕ; suc; zero; _⊔_; _+_; _≤_; _<_; _≟_)
open import Data.Nat.Properties using (
                                  ≤-refl; ≤-trans; ≤-step; +-identityʳ; +-suc; 1+n≰n;
                                  m≤m⊔n; n≤m⊔n; ≤+≢⇒<
                                )
open import Data.Bool using (Bool; true; false)
open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
                             renaming (¬_ to not)
open import Function using (case_of_)

infix 50 _∋_ _⊢_ _⊨Form_ _⊨Ctx_ _⊨_
infixl 60 _,,_
infixr 70 _⇒_ _∧_ _∨_
infixr 80 ¬_

---- Natural deduction

PropVar : Set 
PropVar = ℕ

variable P Q R : PropVar

data Form : Set where
  propVar : PropVar → Form
  ⊥       : Form
  _⇒_     : Form → Form → Form
  
variable A B C : Form

data occurs : PropVar → Form → Set where
  occurs-root : occurs P (propVar P)
  occurs-⇒L   : occurs P A → occurs P (A ⇒ B)
  occurs-⇒R   : occurs P B → occurs P (A ⇒ B)

data Ctx : Set where
  ∅    : Ctx
  _,,_ : Ctx → Form → Ctx
  
variable Γ Δ : Ctx

_⇒*_ : Ctx → Form → Form
∅        ⇒* A = A
(Γ ,, A) ⇒* B = Γ ⇒* (A ⇒ B)

data _∋_ : Ctx → Form → Set where
  zero : (Γ ,, A) ∋ A
  suc  : Γ ∋ A → (Γ ,, B) ∋ A

-- Classical natural deduction

data _⊢_ : Ctx → Form → Set where
  ax   : Γ ∋ A → Γ ⊢ A
  ⊥E   : Γ ⊢ ⊥ → Γ ⊢ A
  ⇒I   : Γ ,, A ⊢ B → Γ ⊢ A ⇒ B
  ⇒E   : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  dneg : Γ ⊢ (A ⇒ ⊥) ⇒ ⊥ → Γ ⊢ A
  
-- Admissible rules

Renaming : Ctx → Ctx → Set
Renaming Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

shift : Renaming Γ Δ → Renaming (Γ ,, A) (Δ ,, A)
shift ρ zero    = zero
shift ρ (suc x) = suc (ρ x)

swap : Renaming (Γ ,, A ,, B) (Γ ,, B ,, A)
swap zero          = suc zero
swap (suc zero)    = zero
swap (suc (suc x)) = suc (suc x)

rename : Renaming Γ Δ → Γ ⊢ A → Δ ⊢ A
rename ρ (ax x)   = ax (ρ x)
rename ρ (⊥E p)   = ⊥E (rename ρ p)
rename ρ (⇒I p)   = ⇒I (rename (shift ρ) p)
rename ρ (⇒E p q) = ⇒E (rename ρ p) (rename ρ q)
rename ρ (dneg p) = dneg (rename ρ p)

-- Weakening
wk : Γ ⊢ B → Γ ,, A ⊢ B
wk (ax x)     = ax (suc x)
wk (⊥E p)     = ⊥E (wk p)
wk (⇒I p)     = ⇒I (rename swap (wk p))
wk (⇒E p q)   = ⇒E (wk p) (wk q)
wk (dneg p)   = dneg (wk p)

syn-pull : ∅ ⊢ (Γ ⇒* A) → Γ ⊢ A
syn-pull {Γ = ∅}      p = p
syn-pull {Γ = Γ ,, A} p = ⇒E (wk (syn-pull {Γ = Γ} p)) (ax zero)

---- Derived operators

-- Negation

¬_ : Form → Form
¬ A = A ⇒ ⊥

¬I : Γ ,, A ⊢ ⊥ → Γ ⊢ ¬ A
¬I = ⇒I

¬E : Γ ⊢ ¬ A → Γ ⊢ A → Γ ⊢ ⊥
¬E = ⇒E

-- Conjunction

_∧_ : Form → Form → Form
A ∧ B = ¬(A ⇒ ¬ B)

∧I : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ∧ B
∧I p q = ¬I (¬E (⇒E (ax zero) (wk p)) (wk q))

∧E₁ : Γ ⊢ A ∧ B → Γ ⊢ A
∧E₁ p = dneg (¬I (¬E (wk p)
                     (⇒I (¬I (¬E (ax (suc (suc zero)))
                                 (ax (suc zero)))))))

∧E₂ : Γ ⊢ A ∧ B → Γ ⊢ B
∧E₂ p = dneg (¬I (¬E (wk p)
                     (⇒I (¬I (¬E (ax (suc (suc zero)))
                                 (ax zero))))))

-- Disjunction

_∨_ : Form → Form → Form
A ∨ B = ¬ A ⇒ B

∨I₁ : Γ ⊢ A → Γ ⊢ A ∨ B
∨I₁ p = ⇒I (⊥E (¬E (ax zero) (wk p)))

∨I₂ : Γ ⊢ B → Γ ⊢ A ∨ B
∨I₂ p = ⇒I (wk p)

contra : Γ ,, A ⊢ B → Γ ,, ¬ B ⊢ ¬ A
contra p = ¬I (¬E (ax (suc zero)) (rename swap (wk p)))

∨E : Γ ⊢ A ∨ B → Γ ,, A ⊢ C → Γ ,, B ⊢ C → Γ ⊢ C
∨E p q r = dneg (⇒I (¬E (contra r) (⇒E (wk p) (contra q))))

LEM : ∀ A → Γ ⊢ A ∨ ¬ A
LEM A = dneg (¬I (¬E (ax zero) (∨I₂ (¬I (¬E (ax (suc zero)) (∨I₁ (ax zero)))))))

---- Semantics

case-bool : ∀ b → b ≡ true ⊎ b ≡ false
case-bool true  = inj₁ refl
case-bool false = inj₂ refl

Valuation : Set
Valuation = PropVar → Bool

variable v : Valuation

value : Valuation → Form → Bool
value v (propVar x) = v x
value v ⊥           = false
value v (A ⇒ B)
  with value v A
... | false = true
... | true  = value v B

_⊨Form_ : Valuation → Form → Set
v ⊨Form A = value v A ≡ true

sem⊥E : not (v ⊨Form ⊥)
sem⊥E ()

sem⇒I : (v ⊨Form A → v ⊨Form B) → v ⊨Form A ⇒ B
sem⇒I {v = v} {A = A} φ
  with case-bool (value v A)
...  | inj₁ e rewrite e = φ refl
...  | inj₂ e rewrite e = refl

sem⇒E : v ⊨Form (A ⇒ B) → v ⊨Form A → v ⊨Form B
sem⇒E {v = v} {A = A} p q
  with case-bool (value v A)
...  | inj₁ e rewrite e = p
...  | inj₂ e rewrite e = case q of λ {()}

sem-dneg : v ⊨Form (¬ ¬ A) → v ⊨Form A
sem-dneg {v = v} {A = A} p
  with case-bool (value v A)
...  | inj₁ e rewrite e = refl
...  | inj₂ e rewrite e = case p of λ {()}

_⊨Ctx_ : Valuation → Ctx → Set
v ⊨Ctx Γ = ∀ {A} → Γ ∋ A → v ⊨Form A

_sem,,_ : v ⊨Ctx Γ → v ⊨Form A → v ⊨Ctx Γ ,, A
(v⊨Γ sem,, v⊨A) zero    = v⊨A
(v⊨Γ sem,, v⊨A) (suc x) = v⊨Γ x

_⊨_ : Ctx → Form → Set
Γ ⊨ A = ∀ {v} → v ⊨Ctx Γ → v ⊨Form A

sem-push : Γ ⊨ A → ∅ ⊨ (Γ ⇒* A)
sem-push Γ⊨A _ = force-push Γ⊨A
  where
    force-push : (v ⊨Ctx Γ → v ⊨Form A) → v ⊨Form (Γ ⇒* A)
    force-push         {Γ = ∅}              φ = φ (λ {()})
    force-push {v = v} {Γ = Γ ,, A} {A = B} φ =
      force-push {Γ = Γ} λ v⊨Γ →
        sem⇒I {A = A} {B = B} λ v⊨A → φ (v⊨Γ sem,, v⊨A)

neg-true₁ : ∀ {b} → not (b ≡ true) → b ≡ false
neg-true₁ {true}  p = ⊥-elim (p refl)
neg-true₁ {false} _ = refl

neg-true₂ : ∀ {b} → b ≡ false → not (b ≡ true)
neg-true₂ {true}  ()
neg-true₂ {false} _ ()

---- Soundness

soundness : ∀ {Γ A} → Γ ⊢ A → Γ ⊨ A
soundness (ax x)       v⊨Γ = v⊨Γ x
soundness (⊥E p)   {v} v⊨Γ = ⊥-elim (sem⊥E {v = v} (soundness p v⊨Γ))
soundness {A = A ⇒ B}
          (⇒I p)   {v} v⊨Γ = sem⇒I {A = A} {B = B} λ v⊨A → soundness p (v⊨Γ sem,, v⊨A)
soundness (⇒E {A = A} {B = B} p q)
                   {v} v⊨Γ = sem⇒E {A = A} {B = B} (soundness p v⊨Γ) (soundness q v⊨Γ)
soundness (dneg {A = A} p)
                   {v} v⊨Γ = sem-dneg {A = A} (soundness p v⊨Γ)

---- Completeness

specifiesVar : Ctx → Valuation → PropVar → Set
specifiesVar Γ v P = 
    (v P ≡ true  → Γ ∋ propVar P)
  × (v P ≡ false → Γ ∋ ¬ propVar P)

specifiesForm : Ctx → Valuation → Form → Set
specifiesForm Γ v A = 
    (v ⊨Form A → Γ ⊢ A)
  × (not (v ⊨Form A) → Γ ⊢ ¬ A)

goL : (∀ P → occurs P (A ⇒ B) → specifiesVar Γ v P)
       → (∀ P → occurs P A → specifiesVar Γ v P)
goL S P o = S P (occurs-⇒L o)

goR : (∀ P → occurs P (A ⇒ B) → specifiesVar Γ v P)
       → (∀ P → occurs P B → specifiesVar Γ v P)
goR S P o = S P (occurs-⇒R o)

-- Main Semantic Lemma

sem : ∀ A v → (∀ P → occurs P A → specifiesVar Γ v P)
            → specifiesForm Γ v A
sem (propVar P) v S =
  let (sl , sr) = S P occurs-root in
    (λ x → ax (sl x)) , (λ x → ax (sr (neg-true₁ x)))
sem ⊥       v S =
    (λ { () })
  , λ _ → ¬I (ax zero)
sem (A ⇒ B) v S
  with case-bool (value v A)
...  | inj₁ v⊨A rewrite v⊨A =
           (λ v⊨B → let ⊢B = proj₁ (sem B v (goR S)) v⊨B
                      in ⇒I (wk ⊢B))
         , (λ v⊭B → let ⊢A = proj₁ (sem A v (goL S)) v⊨A
                        ⊢¬B = proj₂ (sem B v (goR S)) v⊭B
                     in ⇒I (¬E (wk ⊢¬B) (⇒E (ax zero) (wk ⊢A))))
...  | inj₂ v⊭A rewrite v⊭A =
           (λ _ → let ⊢¬A = proj₂ (sem A v (goL S)) (neg-true₂ v⊭A)
                   in ⇒I (⊥E (¬E (wk ⊢¬A) (ax zero))))
         , (λ p → ⊥-elim (p refl))
         
degree : Form → ℕ
degree (propVar P) = suc P
degree ⊥           = zero
degree (A ⇒ B)     = degree A ⊔ degree B

degree-bound : ∀ {D} → D ≡ degree A → occurs P A → P < D
degree-bound refl occurs-root   = ≤-refl
degree-bound refl (occurs-⇒L o) = ≤-trans (degree-bound refl o) (m≤m⊔n _ _)
degree-bound refl (occurs-⇒R o) = ≤-trans (degree-bound refl o) (n≤m⊔n _ _)

data isPropCtx : ℕ → Ctx → Set where
  isPropCtx-empty : isPropCtx 0 ∅
  isPropCtx-pos   : ∀ {n}
                    → isPropCtx n Γ
                    → isPropCtx (suc n) (Γ ,, propVar n)
  isPropCtx-neg   : ∀ {n}
                    → isPropCtx n Γ
                    → isPropCtx (suc n) (Γ ,, ¬ propVar n)
                    
dec-=-Form : (A B : Form) → Dec (A ≡ B)
dec-=-Form (propVar P) (propVar Q)
  with P ≟ Q
...  | yes refl = yes refl
...  | no  p    = no (λ { refl → p refl })
dec-=-Form (propVar P) ⊥           = no (λ { () })
dec-=-Form (propVar P) (_ ⇒ _)     = no (λ { () })
dec-=-Form ⊥           (propVar Q) = no (λ { () })
dec-=-Form ⊥           ⊥           = yes refl
dec-=-Form ⊥           (_ ⇒ _)     = no (λ { () })
dec-=-Form (A₁ ⇒ A₂) (propVar x)   = no (λ { () })
dec-=-Form (A₁ ⇒ A₂) ⊥             = no (λ { () })
dec-=-Form (A₁ ⇒ A₂) (B₁ ⇒ B₂)
  with dec-=-Form A₁ B₁
...  | no p     = no (λ { refl → p refl })
...  | yes refl
     with dec-=-Form A₂ B₂
...     | no p     = no (λ { refl → p refl })
...     | yes refl = yes refl

dec-∋ : (Γ : Ctx) (A : Form) → Dec (Γ ∋ A)
dec-∋ ∅        _ = no (λ {()})
dec-∋ (Γ ,, A) B
    with dec-=-Form A B
...    | yes refl = yes zero
...    | no  p
       with dec-∋ Γ B
...       | yes r = yes (suc r)
...       | no  r = no (λ {
                         zero    → p refl
                       ; (suc x) → r x
                       })

ctxVal : Ctx → Valuation
ctxVal Γ P with dec-∋ Γ (propVar P)
... | yes _ = true
... | no  _ = false

propCtxVarShape : ∀ {n} → isPropCtx n Γ → Γ ∋ A
                → Σ[ k ∈ ℕ ] (k < n) × ((A ≡ propVar k) ⊎ (A ≡ ¬ propVar k))
propCtxVarShape (isPropCtx-pos pCtx) zero = _ , ≤-refl , inj₁ refl
propCtxVarShape (isPropCtx-pos pCtx) (suc x)
  with propCtxVarShape pCtx x
...  | (k , k<n , p) = k , ≤-step k<n , p
propCtxVarShape (isPropCtx-neg pCtx) zero = _ , ≤-refl , inj₂ refl
propCtxVarShape (isPropCtx-neg pCtx) (suc x)
  with propCtxVarShape pCtx x
...  | (k , k<n , p) = k , ≤-step k<n , p

ctxValUniq₁ : ∀ {n} → (pCtx : isPropCtx n Γ)
             → ∀ {k} → Γ ∋ propVar k → not (Γ ∋ ¬ propVar k)
ctxValUniq₁ (isPropCtx-pos pCtx) zero     (suc x)
  with propCtxVarShape pCtx x
...  | (_ , _ , inj₁ ())
...  | (_ , 1+n≤n , inj₂ refl) = 1+n≰n 1+n≤n
ctxValUniq₁ (isPropCtx-pos pCtx) (suc x)  (suc y)
  with propCtxVarShape pCtx x
...  | (_ , _ , inj₁ refl) = ctxValUniq₁ pCtx x y
...  | (_ , _ , inj₂ ())
ctxValUniq₁ (isPropCtx-neg pCtx) (suc x) zero
  with propCtxVarShape pCtx x
...  | (_ , 1+n≤n , inj₁ refl) = 1+n≰n 1+n≤n
...  | (_ , _ , inj₂ ())
ctxValUniq₁ (isPropCtx-neg pCtx) (suc x) (suc y)
  with propCtxVarShape pCtx x
...  | (_ , _ , inj₁ p)  = ctxValUniq₁ pCtx x y
...  | (_ , _ , inj₂ ())

s≤s-inv : ∀ {m n} → suc m ≤ suc n → m ≤ n
s≤s-inv (_≤_.s≤s p) = p

ctxValUniq₂ : ∀ {n} → (pCtx : isPropCtx n Γ)
             → ∀ {k} → k < n → not (Γ ∋ propVar k) → Γ ∋ ¬ propVar k
ctxValUniq₂ {n = suc n} (isPropCtx-pos pCtx) {k} k<n ¬ΓA∋k
  with k ≟ n
... | yes refl = ⊥-elim (¬ΓA∋k zero)
... | no  p    = suc (ctxValUniq₂ {n = n} pCtx {k = k}
                                  (≤+≢⇒< (s≤s-inv k<n) p)
                                  (λ Γ∋k → ¬ΓA∋k (suc Γ∋k)))
ctxValUniq₂ {n = suc n} (isPropCtx-neg pCtx) {k} k<n ¬ΓA∋k
  with k ≟ n
... | yes refl = zero
... | no  p    = suc (ctxValUniq₂ {n = n} pCtx {k = k}
                                  (≤+≢⇒< (s≤s-inv k<n) p)
                                  (λ Γ∋k → ¬ΓA∋k (suc Γ∋k)))

ctxValSat : ∀ {n} → (pCtx : isPropCtx n Γ) → ctxVal Γ ⊨Ctx Γ
ctxValSat {Γ = Γ} pCtx {A} Γ∋A
  with propCtxVarShape pCtx Γ∋A
... | (k , k<n , inj₁ refl)
    with dec-∋ Γ (propVar k)
...    | yes p = refl
...    | no  p = ⊥-elim (p Γ∋A)
ctxValSat {Γ = Γ} pCtx {A} Γ∋A
    | (k , k<n , inj₂ refl)
    with dec-∋ Γ (propVar k)
...    | yes p = ⊥-elim (ctxValUniq₁ pCtx p Γ∋A)
...    | no  p = refl

ctxValSpec : ∀ {n i} → i < n → (pCtx : isPropCtx n Γ) → specifiesVar Γ (ctxVal Γ) i
ctxValSpec {Γ = Γ} {n} {i} i<n pCtx
    with dec-∋ Γ (propVar i)
...    | yes p = (λ _ → p) , (λ {()})
...    | no  p = (λ {()}) , (λ _ → ctxValUniq₂ pCtx i<n p)

taut-completeness* :
  ∀ i j
  → i + j ≡ degree A
  → isPropCtx j Γ
  → Γ ⊨ A → Γ ⊢ A 
taut-completeness* {Γ = Γ} zero    j i+j=d pCtx Γ⊨A =
  let v = ctxVal Γ
   in proj₁ (sem _ _ (λ P o → ctxValSpec (degree-bound i+j=d o) pCtx))
            (Γ⊨A (ctxValSat pCtx))
taut-completeness* (suc i) j i+j=d pCtx Γ⊨A =
  ∨E (LEM (propVar j))
     (taut-completeness*
       i (suc j) (trans (+-suc i j) i+j=d)
       (isPropCtx-pos pCtx)
       (λ v⊨ΓA → Γ⊨A (λ x → v⊨ΓA (suc x))))
     (taut-completeness*
       i (suc j) (trans (+-suc i j) i+j=d)
       (isPropCtx-neg pCtx)
       (λ v⊨ΓA → Γ⊨A (λ x → v⊨ΓA (suc x))))

taut-completeness : ∀ {A} → ∅ ⊨ A → ∅ ⊢ A
taut-completeness {A} =
  taut-completeness* (degree A) 0 (+-identityʳ _) isPropCtx-empty

completeness : ∀ {Γ A} → Γ ⊨ A → Γ ⊢ A
completeness Γ⊨A = syn-pull (taut-completeness (sem-push Γ⊨A))

