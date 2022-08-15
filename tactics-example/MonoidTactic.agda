
-- An example of a tactic, as an exercise to understand
-- how tactics work in Agda.
--
-- The tactic solves equalities in a monoid, as long as they
-- hold up to associativity.
--
-- For example, it can prove that:
--   (x ∙ y) ∙ (z ∙ w) ≡ x ∙ ((y ∙ z) ∙ w)
--
-- The neutral element ("e") is not dealt with, e.g. the tactic cannot
-- prove that e ∙ x ≡ x holds.
--
-- The strategy to build the proof is based on an auxiliary
-- lemma to prove that each expression is equivalent to
-- a canonical representative of its associativity
-- equivalence class, of the form ((e ∙ x₁) ∙ x₂) ... ∙ xn
-- For example:
--
--     (x ∙ y) ∙ (z ∙ w)
--   ≡ ...
--   ≡ (((e ∙ x) ∙ y) ∙ z) ∙ w
--   ≡ ...
--   ≡ x ∙ ((y ∙ z) ∙ w)
--

open import Agda.Builtin.Reflection
  using (
    primQNameEquality;
    Term;
      var; con; def; lam;
      unknown;
    Relevance; relevant; irrelevant;
    Visibility; hidden; visible;
    ArgInfo; arg-info;
    Arg; arg;
    Abs; abs;
    Type;
    ErrorPart; strErr; termErr; nameErr;
    TC; bindTC; returnTC; catchTC; freshName;
    getContext; normalise; inferType; unify; typeError
  )
open import Function     using (case_of_)
open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl; sym; trans; cong)
open import Data.Unit    using (⊤)
open import Data.Product using (_×_; _,_)
open import Data.Bool    using (if_then_else_)
open import Data.Nat     using (zero)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.List    using (List; []; _∷_; length)

record Monoid : Set₁ where
  field
    M       : Set
    e       : M
    _∙_     : M → M → M
    ∙-neutl : ∀ {x} → e ∙ x ≡ x
    ∙-neutr : ∀ {x} → x ∙ e ≡ x
    ∙-assoc : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
open Monoid ⦃ ... ⦄

flip-∙ : ⦃ _ :  Monoid ⦄ → M → M → M
flip-∙ x y = y ∙ x

infixl 1 _>>=_
_>>=_ : {A B : Set} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

getArgList² : List (Arg Term) → Maybe (Term × Term)
getArgList² ( arg (arg-info visible relevant) x
            ∷ arg (arg-info visible relevant) y
            ∷ [])
                     = just (x , y)
getArgList² (_ ∷ xs) = getArgList² xs
getArgList² []       = nothing

getArgs² : Term → Maybe (Term × Term)
getArgs² (def _ args) = getArgList² args
getArgs² _            = nothing

#vArg : Term → Arg Term
#vArg = arg (arg-info visible relevant)

#refl : Term
#refl = con (quote refl) []

#sym : Term → Term
#sym p = def (quote sym) (#vArg p ∷ [])

#trans : Term → Term → Term
#trans p q = def (quote trans) (#vArg p ∷ #vArg q ∷ [])

#cong : Term → Term → Term
#cong p q = def (quote cong) (#vArg p ∷ #vArg q ∷ [])

#e : Term
#e = def (quote e) []

#∙-neutl : Term
#∙-neutl = def (quote ∙-neutl) []

#∙-assoc : Term
#∙-assoc = def (quote ∙-assoc) []

#∙ : Term → Term → Term
#∙ x y = def (quote Monoid._∙_) (#vArg x ∷ #vArg y ∷ [])

#flip-∙ : Term → Term
#flip-∙ x = def (quote flip-∙) (#vArg x ∷ [])

{-# TERMINATING #-}
--
-- Explanation:
--
-- The kinds of terms that we are interested in
-- are either "atomic" or "compound" i.e. of the
-- form (t #∙ s).
--
-- If t is a term, we write ⟦t⟧ for the value it denotes.
--
-- #∙ is the term constructor such that ⟦t #∙ s⟧ = ⟦t⟧ ∙ ⟦s⟧.
--
-- If t and s are terms, we define (t L∙ s) as an operation
-- returning a term:
--   t L∙ s          ≡ t #∙ s           if s is atomic
--   t L∙ (s₁ #∙ s₂) ≡ (t L∙ s₁) L∙ s₂  if s = (s₁ #∙ s₂) is compound
--
-- The following lemma is such that
--   prove-comb-left t
-- Builds a proof of:
--   ⟦s #∙ t⟧ ≡ ⟦s L∙ t⟧
-- For an arbitrary term s.
--
-- The interesting case is when t is compound; then:
--
--     ⟦s #∙ (t₁ #∙ t₂)⟧
--   ≡ ⟦s⟧ ∙ (⟦t₁⟧ ∙ ⟦t₂⟧)   by definition
--   ≡ (⟦s⟧ ∙ ⟦t₁⟧) ∙ ⟦t₂⟧   by associativity
--   ≡ (⟦s #∙ t₁⟧) ∙ ⟦t₂⟧    by definition
--   ≡ ⟦s L∙ t₁⟧ ∙ ⟦t₂⟧      by IH
--   ≡ ⟦(s L∙ t₁) #∙ t₂⟧     by definition
--   ≡ ⟦(s L∙ t₁) L∙ t₂⟧     by IH
--   ≡ ⟦s L∙ (t₁ #∙ t₂)⟧     by definition
--
prove-comb-left : Term → Term
prove-comb-left (def op args) =
  if primQNameEquality op (quote Monoid._∙_)
    then (case getArgList² args of λ {
            nothing → #refl
          ; (just (x , y)) →
              #trans (#sym #∙-assoc)
                (#trans (#cong (#flip-∙ y) (prove-comb-left x))
                        (prove-comb-left y))
          })
    else #refl
prove-comb-left _ = #refl

macro
  solve : Term → TC ⊤
  solve hole = do
    holeType ← inferType hole >>= normalise
    case getArgs² holeType of λ {
        nothing →
          typeError (strErr "Did not found arguments to solve" ∷ [])
      ; (just (x , y)) →
          unify hole
            (#trans
              (#trans (#sym #∙-neutl) (prove-comb-left x))
              (#trans (#sym (prove-comb-left y)) #∙-neutl))
      }

example : ∀ ⦃ _ :  Monoid ⦄ {a b c d e f : M} →
            (a ∙ b) ∙ (c ∙ (d ∙ (e ∙ f)))
          ≡ (a ∙ ((b ∙ c) ∙ (d ∙ e))) ∙ f
example = solve
