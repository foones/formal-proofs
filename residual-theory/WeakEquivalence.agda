module WeakEquivalence where

open import Function
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Utils
open import AxiomaticRewriteSystem
open import SetOfSteps

-- Weak equivalence of derivations:
-- Two coinitial derivations are weakly equivalent if
-- they induce the same residual relation for individual steps.

infixl 3 _≈_
 
data _≈_ {A} {{_ : finitely-branching A}} :
      ∀ {x₁ x₂ y₁ y₂}
        → derivation {A} x₁ x₂
        → derivation {A} y₁ y₂
        → Set where
  ≈-con : ∀ {x y} {d e : derivation x y} →
            (∀ {z} → (T : Step A x z) → (T ¹/* d) ≡ (T ¹/* e)) →
            d ≈ e

≈-refl : ∀ {A} {{_ : finitely-branching A}} {x y}
          → {d : derivation {A} x y}
          → d ≈ d
≈-refl = ≈-con (λ _ → refl)

≈-sym : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂}
          → {d : derivation {A} x₁ x₂}
          → {e : derivation {A} y₁ y₂}
          → d ≈ e
          → e ≈ d
≈-sym (≈-con u) = ≈-con (λ x → sym (u x))

≈-trans : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂ z₁ z₂}
            → {d : derivation {A} x₁ x₂}
            → {e : derivation {A} y₁ y₂}
            → {f : derivation {A} z₁ z₂}
            → d ≈ e
            → e ≈ f
            → d ≈ f
≈-trans (≈-con u) (≈-con v) = ≈-con (λ x → trans (u x) (v x))

≈-coinitial : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂}
          → {d : derivation {A} x₁ x₂}
          → {e : derivation {A} y₁ y₂}
          → d ≈ e
          → x₁ ≡ y₁
≈-coinitial (≈-con _) = refl

≈-cofinal : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂}
          → {d : derivation {A} x₁ x₂}
          → {e : derivation {A} y₁ y₂}
          → d ≈ e
          → x₂ ≡ y₂
≈-cofinal (≈-con _) = refl

≈-transport : ∀ {A} {{_ : finitely-branching A}} {x₁ x₂ y₁ y₂}
          → {d : derivation {A} x₁ x₂}
          → (e : derivation {A} y₁ y₂)
          → d ≈ e
          → derivation {A} x₁ x₂
≈-transport e (≈-con _) = e

ss-≈-type :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → ∀ {x₁ x₂ y₁ y₂}
    → (M : set-of-steps {A} x₁)
    → (d : derivation {A} x₁ x₂) 
    → (e : derivation {A} y₁ y₂) 
    → d ≈ e
    → Set
ss-≈-type M d e (≈-con _) =
  (M +/* d) ≡ (M +/* e)

ss-≈ :
  ∀ {A} 
    → {{_ : finitely-branching A}}
    → ∀ {x₁ x₂ y₁ y₂}
    → (M : set-of-steps {A} x₁)
    → (d : derivation {A} x₁ x₂) 
    → (e : derivation {A} y₁ y₂) 
    → (w : d ≈ e)
    → ss-≈-type M d e w
ss-≈ ss-ε             d e (≈-con _) =
  trans (ss-ε-+/* d) (sym (ss-ε-+/* e))
ss-≈ (ss-∷ (_ , R) M) d e (≈-con u) =
  trans
    (ss-∷-+/* d R M)
    (trans
      (cong (λ x → ss-++ x (M +/* d))
            (u R))
      (trans
        (cong (λ x → ss-++ (R ¹/* e) x)
              (ss-≈ M d e (≈-con u)))
        (sym (ss-∷-+/* e R M))))

