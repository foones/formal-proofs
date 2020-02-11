
module Permutation where

open import Level
open import Function
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Relation.Binary.Core
import Relation.Binary.PropositionalEquality as Eq
open Eq
open Eq.≡-Reasoning

open import Utils
open import AxiomaticRewriteSystem
open import SetOfSteps
open import Developments
open import BoundedDevelopments
open import WeakEquivalence

record semantic-orthogonality (A : RS)
                              {{_ : finitely-branching A}} : Set where
  constructor semantic-orthogonality-proof
  field
    axiom :
      ∀ {x₁ x₂ x₃ : Ob A}
        → (R : Step A x₁ x₂)
        → (S : Step A x₁ x₃)
        → Σ[ d ∈ complete-development {A} (S /¹ R) ]
          Σ[ e ∈ complete-development {A} (R /¹ S) ]
          R ∷ complete-development-derivation d ≈ S ∷ complete-development-derivation e
open semantic-orthogonality {{...}} public

-- Permutation equivalence

infixl 3 _~_

data _~_ {A} {{_ : finitely-branching A}} :
    ∀ {x₁ x₂ y₁ y₂}
      → derivation {A} x₁ x₂
      → derivation {A} y₁ y₂
      → Set where
  ~-refl : ∀ {x y}
             → {d : derivation x y}
             → d ~ d
  ~-perm : ∀ {x y₁ y₂}
             → (R : Step A x y₁)
             → (S : Step A x y₂)
             → (d : complete-development {A} (S /¹ R))
             → (e : complete-development {A} (R /¹ S))
             → R ∷ complete-development-derivation d ≈
               S ∷ complete-development-derivation e
             → R ∷ complete-development-derivation d ~
               S ∷ complete-development-derivation e
  ~-trans : ∀ {x₁ x₂ y₁ y₂ z₁ z₂}
              → {d : derivation x₁ x₂}
              → {e : derivation y₁ y₂}
              → {f : derivation z₁ z₂}
              → d ~ e
              → e ~ f
              → d ~ f
  ~-cong : ∀ {x₁ x₂ x₃ y₁ y₂ y₃}
             → {d₁ : derivation {A} x₁ x₂}
             → {d₂ : derivation {A} x₂ x₃}
             → {e₁ : derivation {A} y₁ y₂}
             → {e₂ : derivation {A} y₂ y₃}
             → (p : d₁ ~ e₁)
             → (q : d₂ ~ e₂)
             → d₁ ++ d₂ ~ e₁ ++ e₂

~-cofinal : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂}
             → {d : derivation {A} x₁ x₂}
             → {e : derivation {A} y₁ y₂}
             → d ~ e
             → x₂ ≡ y₂
~-cofinal ~-refl              = refl
~-cofinal (~-perm R S d e w)  = ≈-cofinal w
~-cofinal (~-trans p q)       = trans (~-cofinal p) (~-cofinal q)
~-cofinal (~-cong p q)        = ~-cofinal q

~-sym : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂}
          → {d : derivation {A} x₁ x₂}
          → {e : derivation {A} y₁ y₂}
          → d ~ e
          → e ~ d
~-sym ~-refl             = ~-refl
~-sym (~-perm R S d e w) = ~-perm S R e d (≈-sym w)
~-sym (~-trans p q)      = ~-trans (~-sym q) (~-sym p)
~-sym (~-cong p q)       = ~-cong (~-sym p) (~-sym q)

~-cong-left : ∀ {A} {{_ : finitely-branching A}} {x y z₁ z₂}
                → (f : derivation {A} x y)
                → {d : derivation {A} y z₁}
                → {e : derivation {A} y z₂}
                → (p : d ~ e)
                → f ++ d ~ f ++ e
~-cong-left f p = ~-cong ~-refl p

~-cong-right : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y z}
                → {d  : derivation {A} x₁ y}
                → {e  : derivation {A} x₂ y}
                → (f : derivation {A} y z)
                → (p : d ~ e)
                → d ++ f ~ e ++ f
~-cong-right f p = ~-cong p ~-refl

~-perm-complete-development-type :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → ∀ {x y₁ y₂}
    → (M : set-of-steps {A} x)
    → (d : derivation {A} x y₁)
    → (e : derivation {A} x y₂)
    → Set
~-perm-complete-development-type M d e = ∂ (M +/* d) ~ ∂ (M +/* e)

~-perm-complete-development :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → ∀ {x y₁ y₂}
    → (M : set-of-steps {A} x)
    → (d : derivation {A} x y₁)
    → (e : derivation {A} x y₂)
    → (d≈e : d ≈ e)
    → ~-perm-complete-development-type M d e
~-perm-complete-development M d e (≈-con u)
  rewrite ss-≈ M d e (≈-con u) = ~-refl

complete-development-equivalent :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → {{_ : bounded-developments A}}
    → {{_ : semantic-orthogonality A}}
    → ∀ {x} → (M : set-of-steps {A} x)
    → (d₁ d₂ : complete-development M)
    → complete-development-derivation d₁ ~ complete-development-derivation d₂
complete-development-equivalent {{FR}} {{BD}} {{SO}} M d₁ d₂ =
  set-of-steps-induction
    (λ M → ∀ (d₁ d₂ : complete-development M) →
      complete-development-derivation d₁ ~ complete-development-derivation d₂)
    (λ {
      ss-ε _ ((_ , _ , dev-∷ R∈M _), _) _                    → ⊥-elim R∈M
    ; ss-ε _ ((_ , _ , dev-ε), _) ((_ , _ , dev-∷ R∈M _), _) → ⊥-elim R∈M
    ; ss-ε _ ((_ , _ , dev-ε), _) ((_ , _ , dev-ε), comp₂)   → ~-refl
    ; (ss-∷ (_ , R) _) IH ((_ , _ , dev-ε), c₁) →
        ⊥-elim (c₁ R (dev-∷ (inj₁ refl) dev-ε))
    ; (ss-∷ (_ , R) _) IH ((_ , _ , dev-∷ _ _), _)  ((_ , _ , dev-ε), c₂) →
        ⊥-elim (c₂ R (dev-∷ (inj₁ refl) dev-ε))
    ; M@(ss-∷ (_ , R) _) IH S∷d₁@((_ , S ∷ _ , dev-∷ S∈M _) , _) T∷d₂@((_ , T ∷ _ , dev-∷ T∈M _) , _) →
        let e₁ , e₂ , S∷e₁≈T∷e₂ = semantic-orthogonality.axiom SO S T in
        let f₁ = complete-development-exists (M +/* (S ∷ complete-development-derivation e₁)) in
        let f₂ = complete-development-exists (M +/* (T ∷ complete-development-derivation e₂)) in
          ~-trans {e = S ∷ complete-development-derivation e₁ ++ complete-development-derivation f₁}
            (~-cong-left (S ∷ ε)
              (IH S S∈M (complete-development-tail S∈M S∷d₁)
                        (complete-development-++-subset (ss-subset-¹/ {R = S} T∈M)
                          (complete-development-development e₁)
                          f₁)))
            (~-trans {e = T ∷ complete-development-derivation e₂ ++ complete-development-derivation f₂}
              (~-cong
                (~-perm S T e₁ e₂ S∷e₁≈T∷e₂)
                (~-perm-complete-development M
                  (S ∷ complete-development-derivation e₁)
                  (T ∷ complete-development-derivation e₂) S∷e₁≈T∷e₂))
              (~-sym
                (~-cong-left (T ∷ ε)
                  (IH T T∈M
                       (complete-development-tail T∈M T∷d₂)
                       (complete-development-++-subset (ss-subset-¹/ {R = T} S∈M)
                              (complete-development-development e₂)
                              f₂)))))
    })
    M d₁ d₂

