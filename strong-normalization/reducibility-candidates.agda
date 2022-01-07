{-# OPTIONS --injective-type-constructors #-}

-- Proof of strong normalization for the simply typed
-- lambda-calculus with beta-reduction.
--
-- The proof is based on Girard's technique of reducibility
-- candidates.
--
-- Terms are intrinsically typed, and binding is encoded with de
-- Bruijn indices.

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; Σ-syntax)
                      renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
      using (_≡_; refl; sym; trans; cong)
   renaming (subst to transport)
import Relation.Binary.PropositionalEquality as Eq 
open Eq.≡-Reasoning
open import Relation.Binary.HeterogeneousEquality
      using (_≅_; refl; ≡-to-≅)
open import Function     using (case_of_)

--

cong₂ : {A B C : Set} {a a' : A} {b b' : B}
      → (f : A → B → C) → a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ _ refl refl = refl

-- Type system

infixl 40 _∋_
infixl 40 _⊢_
infixl 50 _∷_
infixl 60 _,_ _,*_
infixr 70 _⇒_ _⇒*_

data Typ : Set where
  *   : Typ
  _⇒_ : Typ → Typ → Typ
  
variable A A' B C : Typ

data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Typ → Ctx

variable Γ Γ' Δ Σ : Ctx

data _∋_ : Ctx → Typ → Set where
  Z : Γ , A ∋ A
  S : Γ ∋ A → Γ , B ∋ A

data _⊢_ : Ctx → Typ → Set where
  atom : ∀ A → Γ ⊢ A
  var  : Γ ∋ A → Γ ⊢ A
  lam  : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  app  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B

variable t t' s s' u : Γ ⊢ A

----------------------------------------

-- Rewriting

Renaming : Ctx → Ctx → Set
Renaming Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A 

shift-renaming : Renaming Γ Δ → Renaming (Γ , A) (Δ , A)
shift-renaming ρ Z     = Z
shift-renaming ρ (S x) = S (ρ x)

rename : Renaming Γ Δ → Γ ⊢ A → Δ ⊢ A
rename _ (atom A)  = atom A
rename ρ (var x)   = var (ρ x)
rename ρ (lam t)   = lam (rename (shift-renaming ρ) t)
rename ρ (app t s) = app (rename ρ t) (rename ρ s)

weaken : Γ ⊢ A → Γ , B ⊢ A
weaken = rename S

Substitution : Ctx → Ctx → Set
Substitution Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

variable σ σ' : Substitution Γ Δ

_,[Z:=_] : Substitution Γ Δ → Δ ⊢ A → Substitution (Γ , A) Δ
(σ ,[Z:= t ]) Z     = t
(σ ,[Z:= _ ]) (S x) = σ x

id : Substitution Γ Γ
id x = var x

[Z:=_] : Γ ⊢ A → Substitution (Γ , A) Γ
[Z:= t ] = id ,[Z:= t ]

shift-substitution : Substitution Γ Δ → Substitution (Γ , A) (Δ , A)
shift-substitution σ Z     = var Z
shift-substitution σ (S x) = weaken (σ x)

substitute : Substitution Γ Δ → Γ ⊢ A → Δ ⊢ A
substitute _ (atom A)  = atom A
substitute σ (var x)   = σ x
substitute σ (lam t)   = lam (substitute (shift-substitution σ) t)
substitute σ (app t s) = app (substitute σ t) (substitute σ s)

data _⟶_ : Γ ⊢ A → Γ ⊢ A → Set where
  ⟶beta≡ : {t : Γ ⊢ B}
           {s : Γ , A ⊢ B}
           {u : Γ ⊢ A}
           → t ≡ app (lam s) u
           → t ⟶ substitute [Z:= u ] s
  ⟶c-lam : {t t' : Γ , A ⊢ B}
           → t ⟶ t'
           → lam t ⟶ lam t'
  ⟶c-appL : {t t' : Γ ⊢ A ⇒ B} {s : Γ ⊢ A}
            → t ⟶ t'
            → app t s ⟶ app t' s
  ⟶c-appR : {t : Γ ⊢ A ⇒ B} {s s' : Γ ⊢ A}
            → s ⟶ s'
            → app t s ⟶ app t s'
            
⟶beta : {t : Γ , A ⊢ B}
        {s : Γ ⊢ A}
        → app (lam t) s ⟶ substitute [Z:= s ] t
⟶beta = ⟶beta≡ refl

----------------------------------------

-- Strongly normalizing terms

data SN : Γ ⊢ A → Set where
  mkSN : (∀ {s} → (t ⟶ s) → SN s) → SN t

----------------------------------------

-- Generalized application

data Typ* : Set where
  []  : Typ*
  _∷_ : Typ* → Typ → Typ*

_⇒*_ : Typ* → Typ → Typ
[]       ⇒* A = A
(A* ∷ B) ⇒* C = A* ⇒* (B ⇒ C)

variable A* B* : Typ*

_⊢*_ : Ctx → Typ* → Set
Γ ⊢* []       = ⊤
Γ ⊢* (A* ∷ B) = (Γ ⊢* A*) × (Γ ⊢ B)

variable t* s* : Γ ⊢* A*

app* : Γ ⊢ A* ⇒* B → Γ ⊢* A* → Γ ⊢ B
app* {A* = []}    t tt         = t
app* {A* = _ ∷ _} t ⟨ s* , r ⟩ = app (app* t s*) r

SN* : Γ ⊢* A* → Set
SN* {A* = []}    tt         = ⊤
SN* {A* = _ ∷ _} ⟨ t* , s ⟩ = SN* t* × SN s

----------------------------------------

-- Strong normalization - congruence lemmas

SN-lam-body : SN (lam t) → SN t
SN-lam-body (mkSN p) = mkSN (λ t⟶t' →
  SN-lam-body (p (⟶c-lam t⟶t')))

SN-app-head : SN (app t s) → SN t
SN-app-head (mkSN p) = mkSN (λ t⟶t' →
  SN-app-head (p (⟶c-appL t⟶t')))

SN-app-arg : SN (app t s) → SN s
SN-app-arg (mkSN p) = mkSN (λ s⟶s' →
  SN-app-arg (p (⟶c-appR s⟶s')))

----
  
data _⟶⟶_ : Γ ⊢* A* → Γ ⊢* A* → Set where
  ⟶⟶last : {t* : Γ ⊢* A*} {s s' : Γ ⊢ A}
         → s ⟶ s' → ⟨ t* , s ⟩ ⟶⟶ ⟨ t* , s' ⟩
  ⟶⟶init : {t* t'* : Γ ⊢* A*} {s : Γ ⊢ A}
         → t* ⟶⟶ t'* → ⟨ t* , s ⟩ ⟶⟶ ⟨ t'* , s ⟩
         
data SN⟶⟶ (t* : Γ ⊢* A*) : Set where
  mkSN⟶⟶ : (∀ {s*} → (t* ⟶⟶ s*) → SN⟶⟶ s*) → SN⟶⟶ t*

SN⟶⟶-pair : {t* : Γ ⊢* A*} → SN⟶⟶ t* → SN s → SN⟶⟶ ⟨ t* , s ⟩
SN⟶⟶-pair α β = aux α α β β
  where
    -- Workaround for the termination checker. 
    aux : {t* : Γ ⊢* A*} → SN⟶⟶ t* → SN⟶⟶ t* → SN s → SN s → SN⟶⟶ ⟨ t* , s ⟩
    aux α (mkSN⟶⟶ SN⟶⟶-t*) β (mkSN SN-s) = mkSN⟶⟶ λ {
        (⟶⟶last p) → SN⟶⟶-pair α (SN-s p)
      ; (⟶⟶init p) → SN⟶⟶-pair (SN⟶⟶-t* p) β
      }

SN*⇒SN⟶⟶ : {t* : Γ ⊢* A*} → SN* t* → SN⟶⟶ t*
SN*⇒SN⟶⟶ {A* = []}    {t* = tt}        tt               = mkSN⟶⟶ λ ()
SN*⇒SN⟶⟶ {A* = _ ∷ _} {t* = ⟨ _ , _ ⟩} ⟨ SN-t* , SN-s ⟩ =
  SN⟶⟶-pair (SN*⇒SN⟶⟶ SN-t*) SN-s

app-eq-left : {t : Γ ⊢ A ⇒ B} {s : Γ ⊢ A}
              {t' : Γ ⊢ A' ⇒ B} {s' : Γ ⊢ A'}
            → app t s ≡ app t' s'
            → t ≅ t'
app-eq-left refl = refl

atom-app*-not-lambda : ∀ {A*} -- (Workaround).
                         {t* : Γ ⊢* A*}
                     → ¬(app* (atom (A* ⇒* B ⇒ C)) t* ≅ lam s)
atom-app*-not-lambda {A* = []}     {t* = tt}        ()
atom-app*-not-lambda {A* = _ ∷ _ } {t* = ⟨ _ , _ ⟩} ()

atom-app*-not-redex : {t* : Γ ⊢* A*}
                    → ¬(app* (atom (A* ⇒* B)) t* ≡ app (lam s) u)
atom-app*-not-redex {A* = []}    ()
atom-app*-not-redex {A* = _ ∷ _} {s = s} {u = u} p =
  atom-app*-not-lambda (app-eq-left p)

atom-app*-red : {t* : Γ ⊢* A*}
              → app* (atom (A* ⇒* B)) t* ⟶ s
              → Σ[ t'* ∈ Γ ⊢* A* ]
                  t* ⟶⟶ t'*
                × s ≡ app* (atom (A* ⇒* B)) t'*
atom-app*-red {A* = []}                      (⟶beta≡ ())
atom-app*-red {A* = _ ∷ _}                   (⟶beta≡ p)  =
  ⊥-elim (atom-app*-not-redex p)
atom-app*-red {A* = _ ∷ _} {t* = ⟨ s* , t ⟩} (⟶c-appL p) =
  case atom-app*-red p of λ {
    ⟨ _ , ⟨ q , refl ⟩ ⟩ → ⟨ _ , ⟨ ⟶⟶init q , refl ⟩ ⟩
  }
atom-app*-red {A* = _ ∷ _} {t* = ⟨ s* , t ⟩ } (⟶c-appR p) =
  ⟨ _ , ⟨ ⟶⟶last p , refl ⟩ ⟩

SN-atom-app⟶⟶ : {t* : ∅ ⊢* A*}
             → SN⟶⟶ t* → SN (app* (atom (A* ⇒* B)) t*)
SN-atom-app⟶⟶ (mkSN⟶⟶ SN⟶⟶-t*) = mkSN λ p → 
  case atom-app*-red p of λ {
    ⟨ _ , ⟨ p' , refl ⟩ ⟩ → SN-atom-app⟶⟶ (SN⟶⟶-t* p')
  }

SN-atom-app* : {t* : ∅ ⊢* A*}
             → SN* t* → SN (app* (atom (A* ⇒* B)) t*)
SN-atom-app* SN-t* = SN-atom-app⟶⟶ (SN*⇒SN⟶⟶ SN-t*)

----------------------------------------

---- Substitution lemma

_,*_ : Ctx → Ctx → Ctx
Γ ,* ∅       = Γ
Γ ,* (Δ , A) = (Γ ,* Δ) , A

shift-renaming* : Renaming Γ Δ → Renaming (Γ ,* Σ) (Δ ,* Σ)
shift-renaming* {Σ = ∅}     ρ = ρ
shift-renaming* {Σ = _ , _} ρ = shift-renaming (shift-renaming* ρ)

shift-substitution* : Substitution Γ Δ → Substitution (Γ ,* Σ) (Δ ,* Σ)
shift-substitution* {Σ = ∅}     σ = σ
shift-substitution* {Σ = _ , _} σ = shift-substitution (shift-substitution* σ)

-- 1) rename-shift-weaken

rename-shift-weaken*-var :
  ∀ {Γ Δ Σ}
    {x : Γ ,* Σ ∋ B}
    {ρ : Renaming Γ Δ}
  → shift-renaming* {Σ = Σ} (shift-renaming {A = A} ρ) (shift-renaming* {Σ = Σ} S x)
  ≡ shift-renaming* {Σ = Σ} S (shift-renaming* {Σ = Σ} ρ x)
rename-shift-weaken*-var {Σ = ∅}           = refl
rename-shift-weaken*-var {Σ = _ , _} {Z}   = refl
rename-shift-weaken*-var {Σ = _ , _} {S x} = cong S rename-shift-weaken*-var

rename-shift-weaken* :
  ∀ {Γ Δ Σ}
    {t : Γ ,* Σ ⊢ B}
    {ρ : Renaming Γ Δ}
  → rename (shift-renaming* {Σ = Σ} (shift-renaming {A = A} ρ))
           (rename (shift-renaming* {Σ = Σ} S) t)
  ≡ rename (shift-renaming* {Σ = Σ} S)
           (rename (shift-renaming* {Σ = Σ} ρ) t)
rename-shift-weaken* {t = atom _}        = refl
rename-shift-weaken* {t = var x}         = cong var rename-shift-weaken*-var
rename-shift-weaken* {Σ = Σ} {t = lam t} =
  cong lam (rename-shift-weaken* {Σ = Σ , _} {t = t})
rename-shift-weaken* {t = app t s}       =
  cong₂ app rename-shift-weaken* rename-shift-weaken*

rename-shift-weaken : ∀ {ρ : Renaming Γ Δ}
                      → rename (shift-renaming {A = A} ρ) (weaken t)
                      ≡ weaken (rename ρ t)
rename-shift-weaken {t = t} {ρ = ρ} = rename-shift-weaken* {t = t} {ρ = ρ}

-- 2) subst-weaken

subst-weaken*-var :
  ∀ {Γ Σ}
    {x : Γ ,* Σ ∋ A}
    {s : Γ ⊢ B}
  → shift-substitution* {Σ = Σ} [Z:= s ]
      (shift-renaming* {Σ = Σ} S x) ≡ var x
subst-weaken*-var {Σ = ∅}           = refl
subst-weaken*-var {Σ = _ , _} {Z}   = refl
subst-weaken*-var {Σ = Σ , _} {S x} = cong weaken
                                           (subst-weaken*-var {Σ = Σ} {x = x})

subst-weaken* :
  ∀ {Γ Σ}
    {t : Γ ,* Σ ⊢ A}
    {s : Γ ⊢ B}
  → substitute (shift-substitution* {Σ = Σ} [Z:= s ])
               (rename (shift-renaming* {Σ = Σ} S) t) ≡ t
subst-weaken* {t = atom _}        = refl
subst-weaken* {Σ = Σ} {t = var x} = subst-weaken*-var {Σ = Σ} {x = x}
subst-weaken* {Σ = Σ} {t = lam t} = cong lam (subst-weaken* {Σ = Σ , _} {t = t})
subst-weaken* {t = app _ _}       = cong₂ app subst-weaken* subst-weaken*

subst-weaken : substitute [Z:= s ] (weaken t) ≡ t
subst-weaken {s = s} {t = t} = subst-weaken* {t = t} {s = s}

-- 3) subst-shift-weaken

subst-shift-weaken*-var :
  ∀ {Γ Δ Σ}
     {x : Γ ,* Σ ∋ B}
     {σ : Substitution Γ Δ}
  → shift-substitution* {Σ = Σ} (shift-substitution {A = A} σ)
      (shift-renaming* {Σ = Σ} S x)
  ≡ rename (shift-renaming* {Σ = Σ} S) (shift-substitution* {Σ = Σ} σ x)
subst-shift-weaken*-var {Σ = ∅}           = refl
subst-shift-weaken*-var {Σ = Σ , _} {Z}   = refl
subst-shift-weaken*-var {Σ = Σ , _} {S x} =
  trans (cong weaken subst-shift-weaken*-var)
        (sym rename-shift-weaken)

subst-shift-weaken* :
  ∀ {Γ Δ Σ}
     {t : Γ ,* Σ ⊢ B}
     {σ : Substitution Γ Δ}
  → substitute (shift-substitution* {Σ = Σ} (shift-substitution {A = A} σ))
               (rename (shift-renaming* {Σ = Σ} S) t)
  ≡ rename (shift-renaming* {Σ = Σ} S)
           (substitute (shift-substitution* {Σ = Σ} σ) t)
subst-shift-weaken* {t = atom _}        = refl
subst-shift-weaken* {Σ = Σ} {t = var x} = subst-shift-weaken*-var {Σ = Σ} {x = x}
subst-shift-weaken* {Σ = Σ} {t = lam t} =
  cong lam (subst-shift-weaken* {Σ = Σ , _} {t = t})
subst-shift-weaken* {t = app t₁ t₂}     =
  cong₂ app (subst-shift-weaken* {t = t₁})
            (subst-shift-weaken* {t = t₂})

subst-shift-weaken : ∀ {σ : Substitution Γ Δ}
                     → substitute (shift-substitution {A = A} σ) (weaken t)
                     ≡ weaken (substitute σ t)
subst-shift-weaken {t = t} {σ = σ} = subst-shift-weaken* {t = t} {σ = σ}

-- 4) substitution-lemma

substitution-lemma*-var :
  ∀ {Γ Δ Σ : Ctx}
    {x : Γ , A ,* Σ ∋ B}
    {s : Γ ⊢ A}
    {σ : Substitution Γ Δ}
  → substitute (shift-substitution* {Σ = Σ} σ)
               (shift-substitution* {Σ = Σ} [Z:= s ] x)
  ≡ substitute (shift-substitution* {Σ = Σ} [Z:= substitute σ s ])
               (shift-substitution* {Σ = Σ} (shift-substitution σ) x)
substitution-lemma*-var {Σ = ∅}     {Z}   = refl
substitution-lemma*-var {Σ = ∅}     {S x} = sym subst-weaken
substitution-lemma*-var {Σ = Σ , _} {Z}   = refl
substitution-lemma*-var {Σ = Σ , _} {S x} {s} {σ} =
  begin
  _ ≡⟨ subst-shift-weaken {t = shift-substitution* [Z:= s ] x} ⟩
  _ ≡⟨ cong weaken (substitution-lemma*-var {x = x}) ⟩
  _ ≡⟨ sym (subst-shift-weaken {t = shift-substitution* (shift-substitution σ) x}) ⟩
  _ ∎

substitution-lemma* :
  ∀ {Γ Δ Σ : Ctx}
    {t : Γ , A ,* Σ ⊢ B}
    {s : Γ ⊢ A}
    {σ : Substitution Γ Δ}
  → substitute (shift-substitution* {Σ = Σ} σ)
               (substitute (shift-substitution* {Σ = Σ} [Z:= s ]) t)
  ≡ substitute (shift-substitution* {Σ = Σ} [Z:= substitute σ s ])
               (substitute (shift-substitution* {Σ = Σ} (shift-substitution σ)) t)
substitution-lemma* {t = atom _}        = refl
substitution-lemma* {t = var x}         = substitution-lemma*-var {x = x}
substitution-lemma* {t = lam t} {σ = σ} =
  cong lam (substitution-lemma* {t = t} {σ = σ})
substitution-lemma* {t = app t₁ t₂}     =
  cong₂ app (substitution-lemma* {t = t₁})
            (substitution-lemma* {t = t₂})

-- Non-generalized version:
substitution-lemma : substitute σ (substitute [Z:= s ] t)
                   ≡ substitute [Z:= substitute σ s ] (substitute (shift-substitution σ) t)
substitution-lemma {σ = σ} {s = s} {t = t} = substitution-lemma* {t = t} {s = s} {σ = σ}

----

step-eq-endpoints : t ≡ t' → s' ≡ s → t ⟶ s → t' ⟶ s'
step-eq-endpoints refl refl p = p

reduction-substitute : (t ⟶ s) → (substitute σ t ⟶ substitute σ s)
reduction-substitute {t = app (lam t) s} (⟶beta≡ refl) =
  step-eq-endpoints refl (substitution-lemma {s = s} {t = t}) (⟶beta≡ refl)
reduction-substitute (⟶c-lam p)    = ⟶c-lam (reduction-substitute p)
reduction-substitute (⟶c-appL p)   = ⟶c-appL (reduction-substitute p)
reduction-substitute (⟶c-appR p)   = ⟶c-appR (reduction-substitute p)

SN-substitute : SN (substitute σ t) → SN t
SN-substitute (mkSN SN-tσ) = mkSN λ p →
    SN-substitute (SN-tσ (reduction-substitute p))

----------------------------------------

-- Reducible terms of type A.

⟦_⟧ : ∀ A → ∅ ⊢ A → Set
⟦ * ⟧     t = SN t
⟦ A ⇒ B ⟧ t = ∀ s → ⟦ A ⟧ s → ⟦ B ⟧ (app t s)

-- Reducible terms are SN & adequacy of atoms

mutual
  adequacy-atom* : {t* : ∅ ⊢* B*} → SN* t* → ⟦ A ⟧ (app* (atom (B* ⇒* A)) t*)
  adequacy-atom* {A = *}               SN-t*         = SN-atom-app* SN-t*
  adequacy-atom* {A = C ⇒ D} {t* = t*} SN-t* s red-s =
    adequacy-atom* {A = D} {t* = ⟨ t* , s ⟩} ⟨ SN-t* , reducible-SN red-s ⟩

  reducible-SN : ⟦ A ⟧ t → SN t
  reducible-SN {*}         p = p
  reducible-SN {A ⇒ B} {t} p =
    SN-app-head (reducible-SN {B} {app t (atom A)}
                              (p (atom A) (adequacy-atom* tt)))

adequacy-atom : ⟦ A ⟧ (atom A)
adequacy-atom = adequacy-atom* tt

-- Forward closure for reducible terms.

reducible-forward : ⟦ A ⟧ t → (t ⟶ s) → ⟦ A ⟧ s
reducible-forward {*}     (mkSN SN-t) p         = SN-t p
reducible-forward {A ⇒ B} red-t       p s red-s =
  reducible-forward {B} (red-t s red-s) (⟶c-appL p)
  
-- Backward closure (~ well-founded induction) for reducible term.

data neutral : ∅ ⊢ A → Set where
  neu-atom : neutral (atom A)
  neu-app  : neutral (app t s)
  
neutral-neq-lam : neutral t → ¬(t ≅ lam s)
neutral-neq-lam neu-atom ()
neutral-neq-lam neu-app  ()

reducible-backward : neutral t → (∀ t' → (t ⟶ t') → ⟦ A ⟧ t') → ⟦ A ⟧ t
reducible-backward {A = *}             neut f = mkSN (λ {s} → f s)
reducible-backward {A = B ⇒ C} {t = t} neut f s red-s = rec red-s (reducible-SN red-s)
  where
    rec : ∀ {s} → ⟦ B ⟧ s → SN s → ⟦ C ⟧ (app t s)
    rec red-s (mkSN SN-s) =
      reducible-backward neu-app λ {
        _ (⟶beta≡ p)  → ⊥-elim (neutral-neq-lam neut (app-eq-left p))
      ; _ (⟶c-appL p) → f _ p _ red-s
      ; _ (⟶c-appR p) → rec (reducible-forward red-s p) (SN-s p)
      }

-- Adequacy of abstraction

adequacy-abstraction : (∀ {s} → ⟦ A ⟧ s → ⟦ B ⟧ (substitute [Z:= s ] t))
                     → ⟦ A ⇒ B ⟧ (lam t)
adequacy-abstraction {A = A} {B = B} {t = t} f _ red-s =
    rec (reducible-SN red-s) red-s SN-t f
  where
    SN-t : SN t
    SN-t = SN-substitute {t = t} (reducible-SN (f adequacy-atom)) 
    --
    rec : ∀ {t s}
          → SN s
          → ⟦ A ⟧ s 
          → SN t
          → (∀ {s} → ⟦ A ⟧ s → ⟦ B ⟧ (substitute [Z:= s ] t))
          → ⟦ B ⟧ (app (lam t) s)
    -- rec calls rec-aux, which takes an extra argument,
    -- as a workaround for the termination checker to
    -- accept this recursive definition.
    rec-aux : ∀ {t s}
            → SN s
            → SN s
            → ⟦ A ⟧ s 
            → SN t
            → (∀ {s} → ⟦ A ⟧ s → ⟦ B ⟧ (substitute [Z:= s ] t))
            → ⟦ B ⟧ (app (lam t) s)
    rec SN-s red-s SN-t f =
      rec-aux SN-s SN-s red-s SN-t f
    rec-aux SN-s0 (mkSN SN-s) red-s (mkSN SN-t) f =
      reducible-backward neu-app (λ {
        _ (⟶beta≡ refl)        → f red-s
      ; _ (⟶c-appL (⟶c-lam p)) →
          rec SN-s0 red-s (SN-t p)
              (λ red-s' → reducible-forward (f red-s') (reduction-substitute p))
      ; _ (⟶c-appR p) →
          rec (SN-s p) (reducible-forward red-s p) (mkSN SN-t) f
      })

-- Adequacy of application

adequacy-application : ⟦ A ⇒ B ⟧ t → ⟦ A ⟧ s → ⟦ B ⟧ (app t s)
adequacy-application red-t red-s = red-t _ red-s

-- Adequacy

split-substitution*-var :
  ∀ {Γ Δ Σ}
    {x : Γ , A ,* Σ ∋ B}
    {s : Δ ⊢ A}
    {σ : Substitution Γ Δ}
  → shift-substitution* (σ ,[Z:= s ]) x ≡
    substitute (shift-substitution* [Z:= s ])
      (shift-substitution* (shift-substitution σ) x)
split-substitution*-var {Σ = ∅}     {Z}   = refl
split-substitution*-var {Σ = ∅}     {S x} = sym subst-weaken
split-substitution*-var {Σ = _ , _} {Z}   = refl
split-substitution*-var {Σ = _ , _} {S x} {σ = σ} =
  trans
    (cong weaken (split-substitution*-var {x = x}))
    (sym (subst-shift-weaken {t = shift-substitution* (shift-substitution σ) x}))

split-substitution* :
  ∀ {Γ Δ Σ}
    {t : Γ , A ,* Σ ⊢ B}
    {s : Δ ⊢ A}
    {σ : Substitution Γ Δ}
  → substitute (shift-substitution* (σ ,[Z:= s ])) t ≡
    substitute (shift-substitution* [Z:= s ])
      (substitute (shift-substitution* (shift-substitution σ)) t)
split-substitution*         {t = atom _}  = refl
split-substitution*         {t = var x}   =
  split-substitution*-var {x = x}
split-substitution* {Σ = Σ} {t = lam t}   =
  cong lam (split-substitution* {Σ = Σ , _} {t = t})
split-substitution*         {t = app t s} =
  cong₂ app (split-substitution* {t = t})
            (split-substitution* {t = s})

split-substitution :
  substitute (σ ,[Z:= s ]) t ≡
  substitute [Z:= s ] (substitute (shift-substitution σ) t)
split-substitution {σ = σ} {t = t} = split-substitution* {t = t} {σ = σ}

_⊨_ : (Γ : Ctx) → Substitution Γ ∅ → Set
Γ ⊨ σ = ∀ {A} (x : Γ ∋ A) → ⟦ A ⟧ (σ x)

adequacy : (t : Γ ⊢ A) → Γ ⊨ σ → ⟦ A ⟧ (substitute σ t)
adequacy (atom A)  _ = adequacy-atom
adequacy (var x)   a = a x
adequacy {A = A ⇒ B} {σ = σ} (lam t)   a =
  adequacy-abstraction (λ {s} red-s →
    transport ⟦ B ⟧
       (split-substitution {σ = σ} {t = t})
       (let σ' = σ ,[Z:= s ]
         in adequacy {σ = σ'} t (λ { Z → red-s ; (S x) → a x })))
adequacy (app t s) a =
  adequacy-application (adequacy t a) (adequacy s a)

----------------------------------------

---- Main theorem

asubst : ∀ Γ → Substitution Γ ∅
asubst Γ {A = A} _ = atom A

adequacy-asubst : Γ ⊨ asubst Γ
adequacy-asubst _ = adequacy-atom

strong-normalization : (t : Γ ⊢ A) → SN t
strong-normalization t = SN-substitute (reducible-SN (adequacy t adequacy-asubst))
