
---- A proof of the Cantor-Schroeder-Bernstein theorem.

---- Idea of the proof:
----
---- Let f : A → B and g : B → A be injective functions.
----
---- An element b : B is a root if b ∉ im(f).
----
---- An element b : B descends from a root if it can be
---- written as b = (f ∘ g)^k(b₀) where b₀ is a root.
----
---- An element a : A descends from a root if a = g(b),
---- where in turn b : B descends from a root.
----
---- To define a bijection h : A → B, set:
----     h(a) := b     if a = g(b) descends from a root,
----     h(a) := f(a)  otherwise
----
---- The theorem depends on a witness the law of excluded middle, as
---- checking whether an element descends from a root cannot be done
---- constructively.

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
                             using (_≡_; refl; sym; trans; cong)
open import Data.Empty       using (⊥-elim)
open import Data.Product     using (_×_; _,_; Σ-syntax)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Nat         using (ℕ; zero; suc)
open import Function         using (case_of_)

DEC : Set → Set
DEC A = A ⊎ ¬ A

LEM : Set₁
LEM = ∀ (A : Set) → DEC A

isInjective : ∀ {A B} → (A → B) → Set
isInjective f = ∀ {a a'} → f a ≡ f a' → a ≡ a'

isSurjective : ∀ {A B} → (A → B) → Set
isSurjective f = ∀ {b} → Σ[ a ∈ _ ] b ≡ f a

isBijective : ∀ {A B} → (A → B) → Set
isBijective f = isInjective f × isSurjective f
    
iterate : ∀ {A : Set} → ℕ → (A → A) → A → A
iterate zero    _ x = x
iterate (suc n) f x = f (iterate n f x)

cantor-schroeder-bernstein :
  ∀ {A B} {f : A → B} {g : B → A}
  → LEM
  → isInjective f
  → isInjective g
  → Σ[ h ∈ (A → B) ] isBijective h
cantor-schroeder-bernstein {A} {B} {f} {g} lem fInj gInj =
    (λ a → h a (decDFR¹ a)) ,
    (λ {a a'} p → hInj (decDFR¹ a) (decDFR¹ a') p) ,
    (λ {b} → hSurj (decDFR b))
  where
    f∘g : B → B
    f∘g x = f (g x)

    isRoot : B → Set
    isRoot b = ¬ (Σ[ a ∈ A ] b ≡ f a)

    descendsFromRoot : B → Set
    descendsFromRoot b = Σ[ b₀ ∈ B ] Σ[ k ∈ ℕ ] isRoot b₀ × b ≡ iterate k f∘g b₀
    
    decDFR : (b : B) → DEC (descendsFromRoot b)
    decDFR b = lem (descendsFromRoot b)

    descendsFromRoot¹ : A → Set
    descendsFromRoot¹ a = Σ[ b ∈ B ] descendsFromRoot b × a ≡ g b

    decDFR¹ : (a : A) → DEC (descendsFromRoot¹ a)
    decDFR¹ a = lem (descendsFromRoot¹ a)

    h : (a : A) → DEC (descendsFromRoot¹ a) → B 
    h _ (inj₁ (b , _)) = b
    h a (inj₂ _)       = f a

    hInj : ∀ {a a'} (da : DEC (descendsFromRoot¹ a)) (da' : DEC (descendsFromRoot¹ a'))
         → h a da ≡ h a' da' → a ≡ a'
    hInj (inj₁ (_ , (_ , a≡gb))) (inj₁ (_ , (_ , a'≡gb'))) b≡b' =
      trans a≡gb (trans (cong g b≡b') (sym a'≡gb'))
    hInj {a' = a'} (inj₁ (b , (_ , zero , (b₀r , b≡b₀)) , _))  (inj₂ _) b≡fa' =
      ⊥-elim (b₀r (a' , trans (sym b≡b₀) b≡fa'))
    hInj (inj₁ (b , (b₀ , suc k , (b₀r , b≡fg[fg]*b₀)) , a≡gb)) (inj₂ ¬DFR¹a') b≡fa' =
      ⊥-elim (¬DFR¹a' (iterate k f∘g b₀ ,
                       (b₀ , k , b₀r , refl) ,
                       fInj (trans (sym b≡fa') b≡fg[fg]*b₀)))
    hInj {a = a} (inj₂ _) (inj₁ (_ , (_ , zero , b₀'r , b'≡b₀') , _)) fa≡b' =
      ⊥-elim (b₀'r (a , trans (sym b'≡b₀') (sym fa≡b')))
    hInj (inj₂ ¬DFR¹a) (inj₁ (b' , (b₀' , suc k , b₀'r , b'≡fg[fg]*b₀') , a'≡gb')) fa≡b' =
      ⊥-elim (¬DFR¹a (iterate k f∘g b₀' ,
                      (b₀' , k , b₀'r , refl) ,
                      fInj (trans fa≡b' b'≡fg[fg]*b₀')))
    hInj (inj₂ _) (inj₂ _) fa≡fa' = fInj fa≡fa'

    hSurj : ∀ {b} → DEC (descendsFromRoot b) → Σ[ a ∈ A ] b ≡ h a (decDFR¹ a)
    hSurj {b} (inj₁ db) = g b , α (decDFR¹ (g b))
      where
        α : (dgb : DEC (descendsFromRoot¹ (g b))) → b ≡ h (g b) dgb
        α (inj₁ (_ , _ , gb₁≡gb₀')) = gInj gb₁≡gb₀'
        α (inj₂ ¬dgb) = ⊥-elim (¬dgb (b , db , refl))
    hSurj {b} (inj₂ ¬db) =
      case lem (Σ[ a ∈ A ] b ≡ f a) of λ {
        (inj₁ (a , b≡fa)) → a , β (decDFR¹ a) b≡fa
      ; (inj₂ br)         → ⊥-elim (¬db (b , zero , br , refl))
      }
      where
        β : ∀ {a} → (da : DEC (descendsFromRoot¹ a)) → b ≡ f a → b ≡ h a da
        β (inj₁ (b' , (b₀ , k , b₀r , b'≡[fg]*b₀) , a≡gb')) b≡fa =
          ⊥-elim (¬db (b₀ , suc k , b₀r ,
                  trans b≡fa (trans (cong f a≡gb') (cong f∘g b'≡[fg]*b₀))))
        β (inj₂ _) b≡fa = b≡fa
    
