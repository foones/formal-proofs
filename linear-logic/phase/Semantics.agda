
module Semantics where

-- Phase semantics for Multiplicative Linear Logic, with a proof of soundness.

open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Bool    using (Bool; true; false)
open import Data.Nat     using (ℕ)

open import LL           using (Form; Seq; _++_; ⊢_; dual; dual-sym)
open Seq
open Form
open ⊢_
open dual
open import Subset       using (subset; _∈_; _⊆_; subset-comprehension-syntax; _≃_; ≃-refl)
open import PhaseSpace   using (
    PhaseSpace; M; pole; e; _∙_;
    ==-refl; ==-sym; ==-trans; ==-cong-∙; ==-cong-pole; e-neut-l; e-neut-r;
    ∙-comm; ∙-assoc;
    _⊥; is-fact;
    A⊥⊥⊥⊆A⊥; fact-A⊥⊥⊆A
  )

-- We explicitly define the type of facts.
Fact : ⦃ _ : PhaseSpace ⦄ → Set₁
Fact = Σ[ A ∈ subset M ] is-fact A

-- Operations on facts.

_f∈_ : ⦃ _ : PhaseSpace ⦄ → M → Fact → Set
x f∈ (A , _) = x ∈ A

fpole : ⦃ _ : PhaseSpace ⦄ → Fact
fpole = pole
      , [ x ∷ x ≡ e ]
      , (λ { x∈pole refl → ==-cong-pole (==-sym e-neut-r) x∈pole })
      , (λ x∈e⊥ → ==-cong-pole e-neut-r (x∈e⊥ refl))

_f⊥ : ⦃ _ : PhaseSpace ⦄ → Fact → Fact
(A , A-fact) f⊥ = (A ⊥ , A , ≃-refl)

_f⊗'_ : ⦃ _ : PhaseSpace ⦄ → Fact → Fact → subset M
(A , _) f⊗' (B , _) = [ x ∷ Σ[ a ∈ M ] Σ[ b ∈ M ] (a ∈ A × b ∈ B × x ≡ a ∙ b) ]

_f⊗_ : ⦃ _ : PhaseSpace ⦄ → Fact → Fact → Fact
A f⊗ B = let C = A f⊗' B in
           C ⊥ ⊥ , C ⊥ , ≃-refl

_f⅋_ : ⦃ _ : PhaseSpace ⦄ → Fact → Fact → Fact
A f⅋ B = ((A f⊥) f⊗ (B f⊥)) f⊥

-- An environment ρ maps each propositional variable (aka type
-- variable) to a fact.
Env : ⦃ _ : PhaseSpace ⦄ → Set₁
Env = ℕ → Fact

-- The interpretation of an MLL formula under an environment
-- is given recursively.
form⟦_⟧ : ⦃ _ : PhaseSpace ⦄ → Form → Env → Fact
form⟦ b+ x ⟧   ρ = ρ x
form⟦ b- x ⟧   ρ = (ρ x) f⊥
form⟦ A ⊗ B ⟧  ρ = form⟦ A ⟧ ρ f⊗ form⟦ B ⟧ ρ 
form⟦ A ⅋ B ⟧  ρ = form⟦ A ⟧ ρ f⅋ form⟦ B ⟧ ρ

-- The lemmas below relate the interpreations of
-- formulae A and A⊥ when they are dual.

dual-perp : ∀ ⦃ _ : PhaseSpace ⦄ {A A⊥} {ρ : Env} {a b : M}
            → dual A A⊥
            → a f∈ form⟦ A ⟧ ρ
            → b f∈ form⟦ A⊥ ⟧ ρ
            → a ∙ b ∈ pole
dual-perp dual-b+            a∈α   b∈α⊥    = ==-cong-pole ∙-comm (b∈α⊥ a∈α)
dual-perp dual-b-            a∈α⊥  b∈α     = a∈α⊥ b∈α
dual-perp (dual-⊗ AdA⊥ BdB⊥) a∈A⊗B b∈A⊥⅋B⊥ =
   a∈A⊗B λ {
     (_ , _ , u∈A , v∈B , refl) →
       b∈A⊥⅋B⊥ λ d∈[A⊥⊗'B⊥]⊥ →
         ==-cong-pole ∙-comm
           (d∈[A⊥⊗'B⊥]⊥
             (_ , _
             , dual-perp AdA⊥ u∈A
             , dual-perp BdB⊥ v∈B
             , refl))
   }
dual-perp (dual-⅋ AdA⊥ BdB⊥) a∈A⅋B b∈A⊥⊗B⊥ =
  ==-cong-pole ∙-comm
    (b∈A⊥⊗B⊥ λ {
      (_ , _ , u∈A⊥ , v∈B⊥ , refl) →
        a∈A⅋B λ w∈[A⊥⊗'B⊥]⊥ →
          ==-cong-pole ∙-comm
            (w∈[A⊥⊗'B⊥]⊥ (_ , _
                         , dual-perp (dual-sym AdA⊥) u∈A⊥
                         , dual-perp (dual-sym BdB⊥) v∈B⊥
                         , refl))
    })

dual-[A]⊆[A⊥]⊥ :
  ∀ ⦃ _ : PhaseSpace ⦄ {A A⊥} {ρ : Env} {a : M}
  → dual A A⊥
  → a f∈ (form⟦ A ⟧ ρ)
  → a f∈ ((form⟦ A⊥ ⟧ ρ) f⊥)
dual-[A]⊆[A⊥]⊥ AdA⊥ a∈A b∈[A⊥] = dual-perp AdA⊥ a∈A b∈[A⊥]

dual-[A]⊥⊆[A⊥] :
  ∀ ⦃ _ : PhaseSpace ⦄ {A A⊥} {ρ : Env} {a : M}
  → dual A A⊥
  → a f∈ ((form⟦ A ⟧ ρ) f⊥)
  → a f∈ (form⟦ A⊥ ⟧ ρ)
dual-[A]⊥⊆[A⊥] dual-b+ a∈[x]⊥ b∈ρx = a∈[x]⊥ b∈ρx
dual-[A]⊥⊆[A⊥] {ρ = ρ} (dual-b- {x = x}) a∈[x]⊥ = fact-A⊥⊥⊆A (proj₂ (ρ x)) a∈[x]⊥
dual-[A]⊥⊆[A⊥] (dual-⊗ AdA⊥ BdB⊥) a∈[A⊗B]⊥ b∈[A⊥⊗B⊥] =
  a∈[A⊗B]⊥ λ a'∈[A⊗'B]⊥ → b∈[A⊥⊗B⊥] λ {
    (_ , _ , u∈[A⊥]⊥ , v∈[B⊥]⊥ , refl) →
      a'∈[A⊗'B]⊥
       (_ , _
       , dual-[A]⊥⊆[A⊥] (dual-sym AdA⊥) u∈[A⊥]⊥
       , dual-[A]⊥⊆[A⊥] (dual-sym BdB⊥) v∈[B⊥]⊥
       , refl)
  }
dual-[A]⊥⊆[A⊥] (dual-⅋ AdA⊥ BdB⊥) a∈[A⅋B]⊥ b∈[A⊥⅋B⊥] =
  a∈[A⅋B]⊥ λ a'∈[A⅋B] →
    ==-cong-pole ∙-comm (a'∈[A⅋B] λ {
      (_ , _ , u∈[A] , v∈[B] , refl) →
        b∈[A⊥⅋B⊥]
          (_ , _
          , dual-[A]⊥⊆[A⊥] AdA⊥ u∈[A]
          , dual-[A]⊥⊆[A⊥] BdB⊥ v∈[B]
          , refl)
    })

-- The interpretation of a sequent
--   A1 , ... , An
-- is defined by identifying it with
--   A1 ⅋ ... ⅋ An
seq⟦_⟧ : ⦃ _ : PhaseSpace ⦄ → Seq → Env → Fact
seq⟦ ∅ ⟧      ρ = fpole
seq⟦ Γ ,, A ⟧ ρ = seq⟦ Γ ⟧ ρ f⅋ form⟦ A ⟧ ρ

-- The following lemma relates the interpretations
-- of Γ₁ and Γ₂ with the interpretation of (Γ₁ ++ Γ₂).
seq-++-⊆ : ∀ ⦃ _ : PhaseSpace ⦄ {Γ₁ Γ₂} {ρ : Env}
       → proj₁ (seq⟦ Γ₁ ⟧ ρ f⅋ seq⟦ Γ₂ ⟧ ρ) ⊆
         proj₁ (seq⟦ (Γ₁ ++ Γ₂) ⟧ ρ)
seq-++-⊆ {Γ₁ = Γ₁} {Γ₂ = ∅} {ρ = ρ} x∈[Γ₁]⅋p =
  fact-A⊥⊥⊆A (proj₂ (seq⟦ Γ₁ ⟧ ρ)) λ y∈[Γ₁]⊥ →
    ==-cong-pole (==-cong-∙ ==-refl e-neut-r)
      (x∈[Γ₁]⅋p (λ z∈[[Γ₁]⊥⊗'p⊥]⊥ →
        ==-cong-pole ∙-comm
          (z∈[[Γ₁]⊥⊗'p⊥]⊥
            (_ , _
            , y∈[Γ₁]⊥
            , (λ u∈p → ==-cong-pole (==-sym e-neut-l) u∈p)
            , refl))))
seq-++-⊆ {Γ₁ = Γ₁} {Γ₂ = Γ₂ ,, A} x∈[Γ₁]⅋[[Γ₂]⅋[A]] y∈[Γ₁++Γ₂]⊥⊗[A]⊥ =
  x∈[Γ₁]⅋[[Γ₂]⅋[A]] λ x'∈[[Γ₁]⊗'[[Γ₂]⅋[A]]]⊥ →
    y∈[Γ₁++Γ₂]⊥⊗[A]⊥ λ {
      (_ , _ , u∈[Γ₁++Γ₂]⊥ , v∈[A]⊥ , refl) →
        ==-cong-pole (==-trans (==-sym ∙-assoc) ∙-comm)
          (u∈[Γ₁++Γ₂]⊥ (seq-++-⊆ {Γ₂ = Γ₂} λ z∈[Γ₁]⊥⊗[Γ₂]⊥ →
            ==-cong-pole ∙-comm
              (z∈[Γ₁]⊥⊗[Γ₂]⊥ λ {
                (_ , _ , g₁∈[Γ₁]⊥ , g₂∈[Γ₂]⊥ , refl) →
                  ==-cong-pole (==-trans
                                 (==-cong-∙ ==-refl (==-trans (==-sym ∙-assoc) ∙-comm))
                                 (==-trans
                                   (==-sym ∙-assoc)
                                   (==-cong-∙ ∙-comm ==-refl)))
                    (x'∈[[Γ₁]⊗'[[Γ₂]⅋[A]]]⊥
                      (_ , _
                      , g₁∈[Γ₁]⊥
                      , (λ w∈[Γ₂]⅋[A] →
                          ==-cong-pole ∙-comm
                            (w∈[Γ₂]⅋[A] λ w'∈[[Γ₂]⊥⊗'[A]⊥]⊥ →
                              ==-cong-pole ∙-comm
                                (w'∈[[Γ₂]⊥⊗'[A]⊥]⊥
                                  (_ , _
                                  , g₂∈[Γ₂]⊥
                                  , v∈[A]⊥
                                  , refl)))
                        )
                      , refl))
              })))
    }
    
---- Soundness ----

soundness-swap : ∀ ⦃ _ : PhaseSpace ⦄ {Γ : Seq} {A B : Form} {ρ : Env}
               → proj₁ (seq⟦ Γ ,, A ,, B ⟧ ρ) ⊆
                 proj₁ (seq⟦ Γ ,, B ,, A ⟧ ρ)
soundness-swap m∈[Γ,A,B] =
  λ x∈[[Γ]⅋[B]]⊥⊗[A]⊥ →
    m∈[Γ,A,B] λ y∈[[[Γ]⅋[A]]⊥⊗'[B]⊥]⊥ →
      x∈[[Γ]⅋[B]]⊥⊗[A]⊥ λ {
        (u , a , u∈[Γ⅋B]⊥ , a∈[A]⊥ , refl) →
          ==-cong-pole (==-trans (==-sym ∙-assoc) ∙-comm)
            (u∈[Γ⅋B]⊥ λ u'∈[[Γ]⊥⊗[B]⊥]⊥ →
              ==-cong-pole ∙-comm
                (u'∈[[Γ]⊥⊗[B]⊥]⊥ λ {
                  (g , b , g∈[Γ]⊥ , b∈[B]⊥ , refl) →
                    ==-cong-pole
                      (==-trans
                        (==-cong-∙
                          ==-refl
                          ∙-assoc)
                        (==-trans
                          (==-sym ∙-assoc)
                          (==-cong-∙ ∙-comm ==-refl)))
                      (y∈[[[Γ]⅋[A]]⊥⊗'[B]⊥]⊥
                        (_ , _
                        , (λ w∈[Γ]⅋[A] →
                             ==-cong-pole ∙-comm
                               (w∈[Γ]⅋[A] λ w'∈[[Γ]⊥⊗'[A]⊥]⊥ →
                                 ==-cong-pole (==-trans
                                                (==-cong-∙ ==-refl ∙-comm)
                                                ∙-comm)
                                   (w'∈[[Γ]⊥⊗'[A]⊥]⊥
                                     (_ , _
                                     , g∈[Γ]⊥
                                     , a∈[A]⊥
                                     , refl))
                               ))
                        , b∈[B]⊥
                        , refl))
                })
            )
      }

soundness-dip : ∀ ⦃ _ : PhaseSpace ⦄ {Γ Γ' : Seq} {A : Form} {ρ : Env}
               → proj₁ (seq⟦ Γ ⟧ ρ) ⊆ proj₁ (seq⟦ Γ' ⟧ ρ) 
               → proj₁ (seq⟦ Γ ,, A ⟧ ρ) ⊆ proj₁ (seq⟦ Γ' ,, A ⟧ ρ)
soundness-dip [Γ]⊆[Γ'] m∈[Γ]⅋[A] =
  λ x∈[Γ]⊥⊗[A]⊥ →
    m∈[Γ]⅋[A] λ y∈[[Γ]⊥⊗'[A]⊥]⊥ →
      x∈[Γ]⊥⊗[A]⊥ λ {
        (g , a , g∈[Γ']⊥ , a∈[A]⊥ , refl) →
          y∈[[Γ]⊥⊗'[A]⊥]⊥
            (g , a
            , (λ z∈[Γ] →
                g∈[Γ']⊥ ([Γ]⊆[Γ'] z∈[Γ])
              )
            , a∈[A]⊥
            , refl)
      }

soundness-exchange : ∀ ⦃ _ : PhaseSpace ⦄ {Γ Γ' : Seq} {ρ : Env}
                   → Γ LL.~ Γ'
                   → proj₁ (seq⟦ Γ ⟧ ρ) ⊆ proj₁ (seq⟦ Γ' ⟧ ρ)
soundness-exchange x = rec true x
  where
    T~ : Bool → Seq → Seq → Set
    T~ true  Γ Γ' = Γ LL.~ Γ'
    T~ false Γ Γ' = Γ' LL.~ Γ
    rec : ∀ {Γ Γ' : Seq} {ρ : Env}
        → (b : Bool)
        → T~ b Γ Γ'
        → proj₁ (seq⟦ Γ ⟧ ρ) ⊆ proj₁ (seq⟦ Γ' ⟧ ρ)
    rec true LL.~-refl        m∈[Γ] = m∈[Γ]
    rec true (LL.~-sym x)     m∈[Γ] = rec false x m∈[Γ]
    rec true (LL.~-trans x y) m∈[Γ] = rec true y (rec true x m∈[Γ])
    rec true (LL.~-swap {Γ = Γ} {A = A} {B = B}) m∈[Γ,A,B] =
      soundness-swap {Γ = Γ} {A = A} {B = B} m∈[Γ,A,B]
    rec true (LL.~-dip {Γ₁ = Γ} {Γ₂ = Γ'} {A = A} x) =
      soundness-dip  {Γ = Γ} {Γ' = Γ'} {A = A} (rec true x)
    rec false LL.~-refl        m∈[Γ] = m∈[Γ]
    rec false (LL.~-sym x)     m∈[Γ] = rec true x m∈[Γ] 
    rec false (LL.~-trans x y) m∈[Γ] = rec false x (rec false y m∈[Γ])
    rec false (LL.~-swap {Γ = Γ} {A = A} {B = B}) m∈[Γ,B,A] =
      soundness-swap {Γ = Γ} {A = B} {B = A} m∈[Γ,B,A]
    rec false (LL.~-dip {Γ₁ = Γ} {Γ₂ = Γ'} {A = A} x) =
      soundness-dip  {Γ = Γ'} {Γ' = Γ} {A = A} (rec false x)

-- Main soundness theorem
soundness : ∀ ⦃ _ : PhaseSpace ⦄ {Γ : Seq} {ρ : Env}
            → ⊢ Γ → e f∈ seq⟦ Γ ⟧ ρ
soundness (ax AdA⊥) =
  λ x∈[p⅋[A]⊥]⊗[A⊥]⊥ →
    ==-cong-pole ∙-comm
      (x∈[p⅋[A]⊥]⊗[A⊥]⊥ λ {
        (_ , _ , u∈[p⅋[A]⊥] , v∈[A⊥]⊥ , refl) →
          ==-cong-pole (==-sym e-neut-l)
            (u∈[p⅋[A]⊥] λ u'∈[p⊗[A]⊥] →
              ==-cong-pole ∙-comm
                (u'∈[p⊗[A]⊥] λ {
                  (_ , _ , a∈p⊥ , b∈A⊥ , refl) →
                    v∈[A⊥]⊥ (dual-[A]⊥⊆[A⊥] AdA⊥ λ w∈[A]⊥ →
                      ==-cong-pole (==-sym ∙-assoc)
                        (a∈p⊥ (b∈A⊥ w∈[A]⊥)))
                }))
      })
soundness {ρ = ρ} (i⊗ {Γ₁ = Γ₁} {A = A} {Γ₂ = Γ₂} {B = B} d₁ d₂) =
  λ x∈[Γ₁++Γ₂]⊥⊗[[A]⊗[B]]⊥ →
    ==-cong-pole ∙-comm
      (x∈[Γ₁++Γ₂]⊥⊗[[A]⊗[B]]⊥ λ {
        (u , v , u∈[Γ₁++Γ₂]⊥ , v∈[[A]⊗[B]]⊥ , refl) →
          soundness {ρ = ρ} d₁ λ ga∈[[Γ₁]⊥⊗[A]⊥]⊥ →
            ==-cong-pole e-neut-l
              (soundness {ρ = ρ} d₂ λ gb∈[[Γ₂]⊥⊗[B]⊥]⊥ →
                ==-cong-pole
                  (==-trans (==-sym ∙-assoc)
                            (==-cong-∙ (==-sym ∙-assoc) ==-refl))
                  (u∈[Γ₁++Γ₂]⊥ (seq-++-⊆ {Γ₁ = Γ₁} {Γ₂ = Γ₂} λ u'∈[Γ₁]⊥⊗[Γ₂]⊥ →
                    ==-cong-pole ∙-comm
                      (u'∈[Γ₁]⊥⊗[Γ₂]⊥ λ {
                        (g₁ , g₂ , g₁∈[Γ₁]⊥ , g₂∈[Γ₂]⊥ , refl) →
                          ==-cong-pole (==-trans (==-sym ∙-assoc)
                                                 (==-cong-∙ (==-sym ∙-assoc) ==-refl))
                            (v∈[[A]⊗[B]]⊥ λ v'∈[[A]⊗'[B]]⊥ →
                              ==-cong-pole
                                (==-trans
                                  (==-cong-∙ ==-refl
                                             (==-trans
                                               ∙-assoc
                                               (==-trans
                                                 (==-cong-∙ ==-refl ∙-comm)
                                                 (==-trans
                                                   (==-sym ∙-assoc)
                                                   (==-trans
                                                     (==-cong-∙ (==-sym ∙-assoc) ==-refl)
                                                     (==-trans
                                                       ∙-assoc
                                                       (==-cong-∙ ==-refl ∙-comm)))))))
                                  ∙-comm)
                                (v'∈[[A]⊗'[B]]⊥
                                  (_ , _
                                  , fact-A⊥⊥⊆A (proj₂ (form⟦ A ⟧ ρ))
                                      (λ a∈[A]⊥ →
                                        ==-cong-pole (==-sym ∙-assoc)
                                          (ga∈[[Γ₁]⊥⊗[A]⊥]⊥ (_ , _ , g₁∈[Γ₁]⊥ , a∈[A]⊥ , refl)))
                                  , fact-A⊥⊥⊆A (proj₂ (form⟦ B ⟧ ρ))
                                      (λ b∈[B]⊥ →
                                        ==-cong-pole (==-sym ∙-assoc)
                                          (gb∈[[Γ₂]⊥⊗[B]⊥]⊥ (_ , _ , g₂∈[Γ₂]⊥ , b∈[B]⊥ , refl)))
                                  , refl)))
                      })
                  )))
      })
soundness {ρ = ρ} (i⅋ d) x∈[Γ]⊥⊗[[A]⅋[B]]⊥ =
  ==-cong-pole ∙-comm
    (x∈[Γ]⊥⊗[[A]⅋[B]]⊥ λ {
      (u , v , u∈[Γ]⊥ , v∈[[A]⅋[B]]⊥ , refl) →
        ==-cong-pole (==-trans ∙-comm (==-sym e-neut-l))
          (v∈[[A]⅋[B]]⊥ λ v'∈[A]⊥⊗[B]⊥ →
            ==-cong-pole ∙-comm
              (v'∈[A]⊥⊗[B]⊥ λ {
                 (a , b , a∈[A]⊥ , b∈[B]⊥ , refl) →
                   ==-cong-pole e-neut-l
                     (soundness {ρ = ρ} d λ p∈[[[Γ]⅋[A]]⊥⊗'[B]⊥]⊥ →
                       ==-cong-pole (==-trans (==-cong-∙ ==-refl ∙-assoc)
                                              ∙-comm)
                         (p∈[[[Γ]⅋[A]]⊥⊗'[B]⊥]⊥
                           (_ , _
                           , (λ z∈[Γ]⅋[A] →
                               ==-cong-pole ∙-comm
                                 (z∈[Γ]⅋[A] λ z'∈[[Γ]⊥⊗'[A]⊥]⊥ →
                                   ==-cong-pole ∙-comm
                                     (z'∈[[Γ]⊥⊗'[A]⊥]⊥
                                       (_ , _
                                       , u∈[Γ]⊥
                                       , a∈[A]⊥
                                       , refl)
                                     )))
                           , b∈[B]⊥
                           , refl)))
              }))
    })
soundness {ρ = ρ} (ex d x) = soundness-exchange x (soundness {ρ = ρ} d)
soundness {ρ = ρ} (cut {Γ₁ = Γ₁} {Γ₂ = Γ₂} AdA⊥ d₁ d₂) =
  seq-++-⊆ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {ρ = ρ} λ x∈[Γ₁]⊥⊗[Γ₂]⊥ →
    ==-cong-pole ∙-comm
      (x∈[Γ₁]⊥⊗[Γ₂]⊥ λ {
        (_ , _ , u∈[Γ₁]⊥ , v∈[Γ₂]⊥ , refl) →
          soundness {ρ = ρ} d₁ λ y₁∈[[Γ₁]⊥⊗'[A]⊥]⊥ →
            ==-cong-pole ∙-comm
              (y₁∈[[Γ₁]⊥⊗'[A]⊥]⊥
                (_ , _
                , u∈[Γ₁]⊥
                , (λ a∈[A] →
                    (==-cong-pole e-neut-l
                      (soundness {ρ = ρ} d₂ λ y₂∈[[Γ₂]⊥⊗'[B]⊥]⊥ →
                        ==-cong-pole ∙-comm
                          (y₂∈[[Γ₂]⊥⊗'[B]⊥]⊥
                            (_ , _
                            , v∈[Γ₂]⊥
                            , dual-[A]⊆[A⊥]⊥ AdA⊥ a∈[A]
                            , refl)))))
                , refl))
      })
