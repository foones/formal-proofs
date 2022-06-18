
--
-- Proof of cut elimination for MLL (the multiplicative fragment
-- of linear logic).
--
-- The proof is an adaptation of the proof of cut elimination 
-- of classical sequent calculus, as found for instance in
-- Sørensen and Urzyczyn, Lectures on the Curry Howard Isomorphism,
-- Section 7.
--

open import Relation.Nullary
                         using (¬_)
open import Relation.Binary.PropositionalEquality
                         using (_≡_; refl; sym; trans; cong)
open import Data.Product using (_×_; Σ-syntax; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Nat     using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
                         using (≤-reflexive; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; m≤m+n; n≤m+n)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infix   50 ⊢_ _~_
infixl  60 _⊝_⇒_
infixl  70 _++_
infixl  80 _,,_
infixl  90 _⊗_ _⅋_

---- Auxiliary functions

n≤0⇒n≡0 : ∀ {n} → n ≤ 0 → n ≡ 0
n≤0⇒n≡0 z≤n = refl

cong₂ : ∀ {A B C : Set}
        → (f : A → B → C) → {a₁ a₂ : A} {b₁ b₂ : B}
        → a₁ ≡ a₂ → b₁ ≡ b₂ → f a₁ b₁ ≡ f a₂ b₂
cong₂ _ refl refl = refl

-- Universal property of _⊔_

⊔-bound₁ : ∀ {n m p} → n ⊔ m ≤ p → n ≤ p
⊔-bound₁ a = ≤-trans (m≤m⊔n _ _) a

⊔-bound₂ : ∀ {n m p} → n ⊔ m ≤ p → m ≤ p
⊔-bound₂ a = ≤-trans (n≤m⊔n _ _) a

⊔-univ : ∀ {n m p} → n ≤ p → m ≤ p → n ⊔ m ≤ p
⊔-univ z≤n     b       = b
⊔-univ (s≤s a) z≤n     = s≤s a
⊔-univ (s≤s a) (s≤s b) = s≤s (⊔-univ a b)

{-------- One-sided MLL --------}

---- Formulae

data Form : Set where
  b+    : ℕ → Form            -- Base type (positive)
  b-    : ℕ → Form            -- Base type (negative)
  _⊗_   : Form → Form → Form  -- Tensor
  _⅋_   : Form → Form → Form  -- Par

variable A A⊥ B B⊥ C C⊥ : Form

---- Duality

-- `dual A B` is an inductive predicate meaning that
-- the formulae A and B are dual to each other.

data dual : Form → Form → Set where
  dual-b+ : ∀ {x} → dual (b+ x) (b- x)
  dual-b- : ∀ {x} → dual (b- x) (b+ x)
  dual-⊗  : dual A A⊥ → dual B B⊥ → dual (A ⊗ B) (A⊥ ⅋ B⊥)
  dual-⅋  : dual A A⊥ → dual B B⊥ → dual (A ⅋ B) (A⊥ ⊗ B⊥)
  
dual-dual : dual A B → dual B C → A ≡ C
dual-dual dual-b+        dual-b-        = refl
dual-dual dual-b-        dual-b+        = refl
dual-dual (dual-⊗ p₁ p₂) (dual-⅋ q₁ q₂) = cong₂ _⊗_ (dual-dual p₁ q₁) (dual-dual p₂ q₂)
dual-dual (dual-⅋ p₁ p₂) (dual-⊗ q₁ q₂) = cong₂ _⅋_ (dual-dual p₁ q₁) (dual-dual p₂ q₂)

dual-sym : dual A B → dual B A
dual-sym dual-b+        = dual-b-
dual-sym dual-b-        = dual-b+
dual-sym (dual-⊗ dA dB) = dual-⅋ (dual-sym dA) (dual-sym dB)
dual-sym (dual-⅋ dA dB) = dual-⊗ (dual-sym dA) (dual-sym dB)

---- Sequents

-- A sequent is a snoc-list of formulae.
data Seq : Set where
  ∅    : Seq
  _,,_ : Seq → Form → Seq

variable Γ Γ' Γ₁ Γ₁' Γ₂ Γ₂' Γ₃ Δ Δ' Δ₁ Δ₂ Δ₃ Σ : Seq

-- Concatenation of sequents

_++_ : Seq → Seq → Seq
Γ₁ ++ ∅       = Γ₁
Γ₁ ++ Γ₂ ,, A = (Γ₁ ++ Γ₂) ,, A

++-∅-neutl : ∅ ++ Γ ≡ Γ
++-∅-neutl {∅}      = refl
++-∅-neutl {Γ ,, _} = cong (_,, _) ++-∅-neutl

++-assoc : Γ₁ ++ (Γ₂ ++ Γ₃) ≡ (Γ₁ ++ Γ₂) ++ Γ₃ 
++-assoc {Γ₃ = ∅}       = refl
++-assoc {Γ₃ = Γ₃ ,, _} = cong (_,, _) (++-assoc {Γ₃ = Γ₃})

---- Equivalence of sequents up to exchange

-- `Γ ~ Δ` is an equivalence relation meaning that
-- Γ is a permutation of Δ.
data _~_ : Seq → Seq → Set where
  ~-refl  : Γ ~ Γ                         -- Reflexivity.
  ~-sym   : Γ₁ ~ Γ₂ → Γ₂ ~ Γ₁             -- Symmetry.
  ~-trans : Γ₁ ~ Γ₂ → Γ₂ ~ Γ₃ → Γ₁ ~ Γ₃   -- Transitivity.
  ~-swap  : Γ ,, A ,, B ~ Γ ,, B ,, A     -- Swapping (at the root).
  ~-dip   : Γ₁ ~ Γ₂ → Γ₁ ,, A ~ Γ₂ ,, A   -- Congruence below snoc.

-- Properties of _~_

~-eq : Γ₁ ≡ Γ₂ → Γ₁ ~ Γ₂
~-eq refl = ~-refl

~-eq-empty : Γ ~ ∅ → Γ ≡ ∅
~-eq-empty p = ~-eq-empty' (inj₁ p)
  where
    -- The lemma must be generalized for symmetry.
    ~-eq-empty' : (Γ ~ ∅) ⊎ (∅ ~ Γ) → Γ ≡ ∅
    ~-eq-empty' (inj₁ ~-refl)          = refl
    ~-eq-empty' (inj₁ (~-sym p))       = ~-eq-empty' (inj₂ p)
    ~-eq-empty' (inj₁ (~-trans p₁ p₂))
      with ~-eq-empty' (inj₁ p₂)
    ... | refl = ~-eq-empty' (inj₁ p₁)
    ~-eq-empty' (inj₂ ~-refl)          = refl
    ~-eq-empty' (inj₂ (~-sym p))       = ~-eq-empty' (inj₁ p)
    ~-eq-empty' (inj₂ (~-trans p₁ p₂))
      with ~-eq-empty' (inj₂ p₁)
    ... | refl = ~-eq-empty' (inj₂ p₂)

~-rotate¹r : Γ ,, A ++ Δ ~ Γ ++ Δ ,, A
~-rotate¹r {Δ = ∅}      = ~-refl
~-rotate¹r {Δ = _ ,, _} = ~-trans (~-dip ~-rotate¹r) ~-swap

~-rotate¹l : Γ ++ Δ ,, A ~ Γ ,, A ++ Δ
~-rotate¹l = ~-sym ~-rotate¹r

~-++-congl : Γ₁ ~ Γ₁' → Γ₁ ++ Γ₂ ~ Γ₁' ++ Γ₂
~-++-congl {Γ₂ = ∅}       p = p
~-++-congl {Γ₂ = Γ₂ ,, _} p = ~-dip (~-++-congl {Γ₂ = Γ₂} p)

~-++-congr : Γ₂ ~ Γ₂' → Γ₁ ++ Γ₂ ~ Γ₁ ++ Γ₂'
~-++-congr ~-refl         = ~-refl
~-++-congr (~-sym p)      = ~-sym (~-++-congr p)
~-++-congr (~-trans p q)  = ~-trans (~-++-congr p) (~-++-congr q)
~-++-congr ~-swap         = ~-swap
~-++-congr (~-dip p)      = ~-dip (~-++-congr p)

~-++-cong : Γ₁ ~ Γ₁' → Γ₂ ~ Γ₂' → Γ₁ ++ Γ₂ ~ Γ₁' ++ Γ₂'
~-++-cong p q = ~-trans (~-++-congl p) (~-++-congr q)

~-++-assoc : Γ₁ ++ (Γ₂ ++ Γ₃) ~ Γ₁ ++ Γ₂ ++ Γ₃
~-++-assoc {Γ₃ = Γ₃} = ~-eq (++-assoc {Γ₃ = Γ₃})

~-++-comm : Γ₁ ++ Γ₂ ~ Γ₂ ++ Γ₁
~-++-comm {Γ₂ = ∅}       = ~-eq (sym ++-∅-neutl)
~-++-comm {Γ₂ = Γ₂ ,, _} = ~-trans (~-dip (~-++-comm {Γ₂ = Γ₂})) ~-rotate¹l

~-rotate132 : Γ₁ ++ Γ₂ ++ Γ₃ ~ Γ₁ ++ Γ₃ ++ Γ₂
~-rotate132 {Γ₁} {Γ₂} {Γ₃} =
  ~-trans
    (~-sym (~-++-assoc {Γ₂ = Γ₂} {Γ₃ = Γ₃}))
    (~-trans (~-++-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂ ++ Γ₃} ~-refl (~-++-comm {Γ₁ = Γ₂}))
             (~-++-assoc {Γ₂ = Γ₃} {Γ₃ = Γ₂}))

~-rotate312 : Γ₁ ++ Γ₂ ++ Γ₃ ~ Γ₃ ++ Γ₁ ++ Γ₂
~-rotate312 {Γ₁} {Γ₂} {Γ₃} =
  ~-trans
    (~-++-comm {Γ₁ = Γ₁ ++ Γ₂} {Γ₂ = Γ₃})
    (~-++-assoc {Γ₃ = Γ₂})

~-rotate213 : Γ₁ ++ Γ₂ ++ Γ₃ ~ Γ₂ ++ Γ₁ ++ Γ₃
~-rotate213 {Γ₁} {Γ₂} {Γ₃} =
  ~-++-congl {Γ₂ = Γ₃} (~-++-comm {Γ₁ = Γ₁} {Γ₂ = Γ₂})

~-cons-snoc : Γ ,, A ~ ∅ ,, A ++ Γ
~-cons-snoc {Γ = ∅}      = ~-refl
~-cons-snoc {Γ = _ ,, _} = ~-trans ~-swap (~-dip ~-cons-snoc)

---- Multiplicative Linear Logic

-- `⊢ Γ` is a predicate meaning that Γ is provable in
-- the multiplicative fragment of linear logic.
-- The exchange rule allows arbitrary permutations of
-- the sequent, using the binary relation _~_ defined above.
data ⊢_ : Seq → Set where
  ax : dual A A⊥
     → ⊢ ∅ ,, A ,, A⊥
  i⊗ : ⊢ Γ₁ ,, A
     → ⊢ Γ₂ ,, B
     → ⊢ Γ₁ ++ Γ₂ ,, A ⊗ B
  i⅋ : ⊢ Γ ,, A ,, B
     → ⊢ Γ ,, A ⅋ B
  ex : ⊢ Γ₁
     → Γ₁ ~ Γ₂
     → ⊢ Γ₂
  cut : dual A A⊥
      → ⊢ Γ₁ ,, A
      → ⊢ Γ₂ ,, A⊥
      → ⊢ Γ₁ ++ Γ₂
      
      
{-------- Cut elimination --------}

-- The remainder of this module contains a proof of cut elimination.

-- The size of a formula is defined as usual. 
size : Form → ℕ
size (b+ _)  = 1
size (b- _)  = 1
size (A ⊗ B) = 1 + size A + size B
size (A ⅋ B) = 1 + size A + size B

-- The size of any formula is non-zero
size≢0 : ¬(size A ≡ zero)
size≢0 {b+ _}  ()
size≢0 {b- _}  ()
size≢0 {_ ⊗ _} ()
size≢0 {_ ⅋ _} ()

-- The depth of a derivation of ⊢ Γ is defined as the size
-- of the biggest formula which is cut somewhere in the
-- derivation.
depth : ⊢ Γ → ℕ
depth (ax _)              = 0
depth (i⊗ p q)            = depth p ⊔ depth q
depth (i⅋ p)              = depth p
depth (ex p _)            = depth p
depth (cut {A = A} _ p q) = size A ⊔ depth p ⊔ depth q

-- We define a ternary predicate Γ ⊝ A ⇒ Γ' meaning that
-- Γ' is a sequent which results from erasing exactly one
-- occurrence of A from Γ.
-- Note that it is not deterministic, e.g. both
--   (∅ ,, A ,, B ,, A) ⊝ A ⇒ (∅ ,, A ,, B)
-- and
--   (∅ ,, A ,, B ,, A) ⊝ A ⇒ (∅ ,, B ,, A)
-- hold.
data _⊝_⇒_ : Seq → Form → Seq → Set where
  ⊝-zero : (Γ ,, A) ⊝ A ⇒ Γ
  ⊝-suc  : Γ ⊝ A ⇒ Γ'
         → Γ ,, B ⊝ A ⇒ Γ' ,, B

-- Erasing A from Γ₁ ++ Γ₂ is either erasing it from Γ₁ or from Γ₂.
⊝-concat-cases : Γ₁ ++ Γ₂ ⊝ A ⇒ Γ
               → (Σ[ Γ₁' ∈ Seq ] ((Γ₁ ⊝ A ⇒ Γ₁') × (Γ ≡ Γ₁' ++ Γ₂)))
                 ⊎
                 (Σ[ Γ₂' ∈ Seq ] ((Γ₂ ⊝ A ⇒ Γ₂') × (Γ ≡ Γ₁ ++ Γ₂')))
⊝-concat-cases {Γ₂ = ∅}       m         = inj₁ (_ , (m , refl))
⊝-concat-cases {Γ₂ = Γ₂ ,, _} ⊝-zero    = inj₂ (_ , (⊝-zero , refl))
⊝-concat-cases {Γ₂ = Γ₂ ,, _} (⊝-suc m)
  with ⊝-concat-cases {Γ₂ = Γ₂} m
... | inj₁ (_ , (m' , refl)) = inj₁ (_ , (m' , refl))
... | inj₂ (_ , (m' , refl)) = inj₂ (_ , (⊝-suc m' , refl))

~-⊝-rev : Γ ⊝ A ⇒ Γ'
        → Γ ~ Γ' ,, A
~-⊝-rev ⊝-zero    = ~-refl
~-⊝-rev (⊝-suc m) = ~-trans (~-dip (~-⊝-rev m)) ~-swap

-- The following lemma is slightly tricky.
--
-- Our goal is to prove a "strong bisimulation"-like result,
-- namely that
--   if Γ₁ ~ Γ₂ and Γ₁ ⊝ A ⇒ Γ₁'
--   then there exists a sequent Γ₂
--   such that Γ₁' ~ Γ₂' and Γ₂ ⊝ A ⇒ Γ₂'.
--
-- If one tries to prove this by structural induction on
-- the proof of Γ₁ ~ Γ₂, the symmetry case becomes stuck
-- (as we cannot apply the IH).
--
-- We strengthen the inductive hypothesis by weakening
-- the condition (Γ₁ ~ Γ₂) to (Γ₁ ~ Γ₂) ⊎ (Γ₂ ~ Γ₁).
--
-- This works, but the lemma ends up having two symmetric halves.

⊝-~-commute : Γ₁ ~ Γ₂ → Γ₁ ⊝ A ⇒ Γ₁' → Σ[ Γ₂' ∈ Seq ] (Γ₁' ~ Γ₂' × Γ₂ ⊝ A ⇒ Γ₂')
⊝-~-commute p m = ⊝-~-commute² (inj₁ p) m
  where
    ⊝-~-commute² : (Γ₁ ~ Γ₂) ⊎ (Γ₂ ~ Γ₁) → Γ₁ ⊝ A ⇒ Γ₁'
                 → Σ[ Γ₂' ∈ Seq ] (Γ₁' ~ Γ₂' × Γ₂ ⊝ A ⇒ Γ₂')
    ⊝-~-commute² (inj₁ ~-refl)            m  = _ , (~-refl , m)
    ⊝-~-commute² (inj₁ (~-sym p))         m  = ⊝-~-commute² (inj₂ p) m
    ⊝-~-commute² (inj₁ (~-trans p₁₂ p₂₃)) m₁ =
      let (_ , (q₁₂ , m₂)) = ⊝-~-commute² (inj₁ p₁₂) m₁ in
      let (_ , (q₂₃ , m₃)) = ⊝-~-commute² (inj₁ p₂₃) m₂ in
        (_ , (~-trans q₁₂ q₂₃ , m₃))
    ⊝-~-commute² (inj₁ ~-swap)    ⊝-zero            = _ , (~-refl , ⊝-suc ⊝-zero)
    ⊝-~-commute² (inj₁ ~-swap)    (⊝-suc ⊝-zero)    = _ , (~-refl , ⊝-zero)
    ⊝-~-commute² (inj₁ ~-swap)    (⊝-suc (⊝-suc m)) = _ , (~-swap , ⊝-suc (⊝-suc m))
    ⊝-~-commute² (inj₁ (~-dip p)) ⊝-zero            = _ , (p , ⊝-zero)
    ⊝-~-commute² (inj₁ (~-dip p)) (⊝-suc m)         =
      let (_ , (q , m')) = ⊝-~-commute² (inj₁ p) m in
        (_ , (~-dip q , ⊝-suc m'))
    ⊝-~-commute² (inj₂ ~-refl)            m  = _ , (~-refl , m)
    ⊝-~-commute² (inj₂ (~-sym p))         m  = ⊝-~-commute² (inj₁ p) m
    ⊝-~-commute² (inj₂ (~-trans p₃₂ p₂₁)) m₁ =
      let (_ , (q₁₂ , m₂)) = ⊝-~-commute² (inj₂ p₂₁) m₁ in
      let (_ , (q₂₃ , m₃)) = ⊝-~-commute² (inj₂ p₃₂) m₂ in
        _ , (~-trans q₁₂ q₂₃ , m₃)
    ⊝-~-commute² (inj₂ ~-swap)    ⊝-zero            = _ , (~-refl , ⊝-suc ⊝-zero)
    ⊝-~-commute² (inj₂ ~-swap)    (⊝-suc ⊝-zero)    = _ , (~-refl , ⊝-zero)
    ⊝-~-commute² (inj₂ ~-swap)    (⊝-suc (⊝-suc m)) = _ , (~-swap , ⊝-suc (⊝-suc m))
    ⊝-~-commute² (inj₂ (~-dip p)) ⊝-zero            = _ , (~-sym p , ⊝-zero)
    ⊝-~-commute² (inj₂ (~-dip p)) (⊝-suc m)         =
      let (_ , (q , m')) = ⊝-~-commute² (inj₂ p) m in
        _ , (~-dip q , ⊝-suc m')

---- Main technical lemma for cut elimination ----

-- This lemma is an analog of Lemma 7.3.3 in Sørensen and Urzyczyn's book.
-- One important difference is that, rather than erasing *all* occurrences
-- of a formula in a sequent, Γ ⊝ C ⇒ Γ' erases exactly one occurrence of C.
--
-- Another difference is that we weaken the requirement "size C ≡ 1 + d"
-- to the requirement "size C ≤ 1 + d". This simplifies the proof of
-- this lemma as well as the proof of the `cut-decrease-depth` lemma.

cut-lemma : ∀ {d}
          → (p : ⊢ Γ) → depth p ≤ d
          → (q : ⊢ Δ) → depth q ≤ d
          → Γ ⊝ C ⇒ Γ'
          → Δ ⊝ C⊥ ⇒ Δ'
          → dual C C⊥
          → size C ≤ 1 + d
          → Σ[ r ∈ ⊢ Γ' ++ Δ' ] depth r ≤ d
---- Axiom ----
cut-lemma (ax AdA⊥) dp q dq ⊝-zero mq CdC⊥ sa =
    ex q (~-trans (~-⊝-rev mq)
           (~-trans (~-eq (cong (_ ,,_) (sym (dual-dual AdA⊥ CdC⊥))))
                    ~-cons-snoc))
  , dq
cut-lemma (ax AdA⊥) dp q dq (⊝-suc ⊝-zero) mq CdC⊥ sa =
    ex q (~-trans (~-⊝-rev mq)
           (~-trans (~-eq (cong (_ ,,_) (sym (dual-dual (dual-sym AdA⊥) CdC⊥))))
                    ~-cons-snoc))
  , dq
cut-lemma p dp (ax AdA⊥) dq mp ⊝-zero CdC⊥ sa =
    ex p (~-trans (~-⊝-rev mp)
                  (~-eq (cong (_ ,,_) (dual-dual CdC⊥ (dual-sym AdA⊥)))))
  , dp
cut-lemma p dp (ax AdA⊥) dq mp (⊝-suc ⊝-zero) CdC⊥ sa =
    ex p (~-trans (~-⊝-rev mp)
                  (~-eq (cong (_ ,,_) (dual-dual CdC⊥ AdA⊥))))
  , dp
---- Exchange (commutative cases) ----
cut-lemma (ex {Γ₁ = Γ₁} {Γ₂ = Γ₂} p ep) dp q dq mp mq CdC⊥ sa =
  let (Γ₁' , (ep' , mp')) = ⊝-~-commute (~-sym ep) mp
      (r , dr) = cut-lemma p dp q dq mp' mq CdC⊥ sa
   in ex r (~-++-congl (~-sym ep'))
    , dr
cut-lemma p dp (ex {Γ₁ = Δ₁} {Γ₂ = Δ₂} q eq) dq mp mq CdC⊥ sa =
  let (Δ₁' , (eq' , mq')) = ⊝-~-commute (~-sym eq) mq
      (r , dr) = cut-lemma p dp q dq mp mq' CdC⊥ sa
   in ex r (~-++-congr (~-sym eq'))
    , dr
---- Cut (commutative cases) ----
cut-lemma {Δ' = Δ'} (cut {A = A} {Γ₁ = Γ₁} {Γ₂ = Γ₂} AdA⊥ p₁ p₂) dp q dq mp mq CdC⊥ sa
  with ⊝-concat-cases {Γ₂ = Γ₂} mp
... | inj₁ (_ , (mp₁ , refl)) =
  let dA = ⊔-bound₁ {n = size A} {m = depth p₁} (⊔-bound₁ dp)
      dp₁ = ⊔-bound₂ {n = size A} {m = depth p₁} (⊔-bound₁ dp)
      (r , dr) = cut-lemma p₁ dp₁ q dq (⊝-suc mp₁) mq CdC⊥ sa
   in ex (cut AdA⊥ (ex r ~-rotate¹r) p₂)
         (~-rotate132 {Γ₂ = Δ'} {Γ₃ = Γ₂})
    , ⊔-univ (⊔-univ dA dr) (⊔-bound₂ dp)
... | inj₂ (_ , (mp₂ , refl)) =
  let dA = ⊔-bound₁ {n = size A} {m = depth p₁} (⊔-bound₁ dp)
      dp₁ = ⊔-bound₂ {n = size A} {m = depth p₁} (⊔-bound₁ dp)
      (r , dr) = cut-lemma p₂ (⊔-bound₂ dp) q dq (⊝-suc mp₂) mq CdC⊥ sa
   in ex (cut AdA⊥ p₁ (ex r ~-rotate¹r))
         (~-++-assoc {Γ₃ = Δ'})
    , ⊔-univ (⊔-univ dA dp₁) dr
cut-lemma {Γ' = Γ'} p dp (cut {A = A} {Γ₁ = Δ₁} {Γ₂ = Δ₂} AdA⊥ q₁ q₂) dq mp mq CdC⊥ sa
  with ⊝-concat-cases {Γ₂ = Δ₂} mq
... | inj₁ (_ , (mq₁ , refl)) =
  let dA = ⊔-bound₁ {n = size A} {m = depth q₁} (⊔-bound₁ dq)
      dq₁ = ⊔-bound₂ {n = size A} {m = depth q₁} (⊔-bound₁ dq)
      (r , dr) = cut-lemma p dp q₁ dq₁ mp (⊝-suc mq₁) CdC⊥ sa
   in ex (cut AdA⊥ r q₂) (~-sym (~-++-assoc {Γ₃ = Δ₂}))
    , ⊔-univ (⊔-univ dA dr) (⊔-bound₂ dq)    
... | inj₂ (Γ₄' , (mq₂ , refl)) =
  let dA = ⊔-bound₁ {n = size A} {m = depth q₁} (⊔-bound₁ dq)
      dq₁ = ⊔-bound₂ {n = size A} {m = depth q₁} (⊔-bound₁ dq)
      (r , dr) = cut-lemma p dp q₂ (⊔-bound₂ dq) mp (⊝-suc mq₂) CdC⊥ sa
   in ex (cut AdA⊥ q₁ r)
         (~-trans (~-++-assoc {Γ₁ = Δ₁} {Γ₂ = Γ'})
                  (~-trans (~-rotate213 {Γ₁ = Δ₁} {Γ₂ = Γ'} {Γ₃ = Γ₄'})
                           (~-sym (~-++-assoc {Γ₁ = Γ'} {Γ₂ = Δ₁}))))
    , ⊔-univ (⊔-univ dA dq₁) dr
---- Tensor / Par (principal case) ----
cut-lemma (i⊗ {A = A} {B = B} p₁ p₂) dp (i⅋ {Γ = Δ} q) dq ⊝-zero ⊝-zero (dual-⊗ AdA⊥ BdB⊥) (s≤s sa) =
    ex (cut AdA⊥ p₁ (cut BdB⊥ p₂ q))
       (~-++-assoc {Γ₃ = Δ})
  , ⊔-univ (⊔-univ {n = size A}
                   (≤-trans (m≤m+n _ _) sa)
                   (⊔-bound₁ dp))
           (⊔-univ (⊔-univ {n = size B}
                           (≤-trans (n≤m+n _ _) sa)
                           (⊔-bound₂ dp))
                   dq)
---- Par / Tensor (principal case) ----
cut-lemma (i⅋ {Γ = Γ} {A = A} {B = B} p) dp (i⊗ {Γ₁ = Δ₁} {Γ₂ = Δ₂} q₁ q₂) dq ⊝-zero ⊝-zero (dual-⅋ AdA⊥ BdB⊥) (s≤s sa) =
    ex (cut AdA⊥ (ex (cut BdB⊥ p q₂) ~-rotate¹r) q₁)
       (~-trans (~-rotate132 {Γ₁ = Γ} {Γ₂ = Δ₂} {Γ₃ = Δ₁})
                (~-sym (~-++-assoc {Γ₁ = Γ} {Γ₂ = Δ₁} {Γ₃ = Δ₂})))
  , ⊔-univ (⊔-univ {n = size A}
                   (≤-trans (m≤m+n _ _) sa)
                   (⊔-univ
                     (⊔-univ {n = size B}
                       (≤-trans (n≤m+n _ _) sa)
                       dp)
                     (⊔-bound₂ dq)))
           (⊔-bound₁ dq)
---- Tensor on the left (commutative cases) ----
cut-lemma {Δ' = Δ'} (i⊗ {Γ₂ = Γ₂} p₁ p₂) dp (i⅋ {Γ = Δ} q) dq ⊝-zero (⊝-suc mq) CdC⊥ sa =
  let (r , dr) = cut-lemma (i⊗ p₁ p₂) dp q dq ⊝-zero (⊝-suc (⊝-suc mq)) CdC⊥ sa
   in i⅋ r
    , dr
cut-lemma {Δ' = Δ'} (i⊗ {Γ₂ = Γ₂} p₁ p₂) dp (i⅋ {Γ = Δ} q) dq (⊝-suc mp) mq CdC⊥ sa
  with ⊝-concat-cases {Γ₂ = Γ₂} mp
... | inj₁ (_ , (mp₁ , refl)) =
        let (r , dr) = cut-lemma p₁ (⊔-bound₁ dp) (i⅋ q) dq (⊝-suc mp₁) mq CdC⊥ sa in
          ex (i⊗ (ex r ~-rotate¹r) p₂)
             (~-trans (~-dip (~-rotate132 {Γ₂ = Δ'} {Γ₃ = Γ₂})) ~-rotate¹l)
        , ⊔-univ dr (⊔-bound₂ dp)
... | inj₂ (_ , (mp₂ , refl)) =
        let (r , dr) = cut-lemma p₂ (⊔-bound₂ dp) (i⅋ q) dq (⊝-suc mp₂) mq CdC⊥ sa in
          ex (i⊗ p₁ (ex r ~-rotate¹r))
             (~-trans (~-dip (~-++-assoc {Γ₃ = Δ'})) ~-rotate¹l)
        , ⊔-univ (⊔-bound₁ dp) dr
cut-lemma (i⊗ {Γ₁ = Γ₁} {Γ₂ = Γ₂} p₁ p₂) dp (i⊗ {Γ₁ = Δ₁} {Γ₂ = Δ₂} q₁ q₂) dq ⊝-zero (⊝-suc mq) CdC⊥ sa
  with ⊝-concat-cases {Γ₂ = Δ₂} mq
... | inj₁ (_ , (mq₁ , refl)) =
  let (r , dr) = cut-lemma (i⊗ p₁ p₂) dp q₁ (⊔-bound₁ dq) ⊝-zero (⊝-suc mq₁) CdC⊥ sa
   in ex (i⊗ r q₂)
         (~-dip (~-eq (sym (++-assoc {Γ₃ = Δ₂}))))
    , ⊔-univ dr (⊔-bound₂ dq)
... | inj₂ (Γ₄' , (mq₂ , refl)) =
  let (r , dr) = cut-lemma (i⊗ p₁ p₂) dp q₂ (⊔-bound₂ dq) ⊝-zero (⊝-suc mq₂) CdC⊥ sa
   in ex (i⊗ q₁ r)
         (~-dip (~-trans (~-eq (++-assoc {Γ₃ = Γ₄'}))
                  (~-trans (~-++-congl {Γ₁ = Δ₁ ++ (Γ₁ ++ Γ₂)} {Γ₂ = Γ₄'} (~-++-comm {Γ₂ = Γ₁ ++ Γ₂}))
                           (~-sym (~-++-assoc {Γ₂ = Δ₁} {Γ₃ = Γ₄'})))))
    , ⊔-univ (⊔-bound₁ dq) dr
cut-lemma (i⊗ {Γ₁ = Γ₁} {Γ₂ = Γ₂} p₁ p₂) dp (i⊗ q₁ q₂) dq (⊝-suc mp) mq CdC⊥ sa
  with ⊝-concat-cases {Γ₂ = Γ₂} mp
... | inj₁ (Γ₁' , (mp₁ , refl)) =
  let (r , dr) = cut-lemma p₁ (⊔-bound₁ dp) (i⊗ q₁ q₂) dq (⊝-suc mp₁) mq CdC⊥ sa in
    ex (i⊗ (ex r ~-rotate¹r) p₂)
       (~-trans
          (~-dip (~-rotate132 {Γ₁ = Γ₁'} {Γ₃ = Γ₂}))
          ~-rotate¹l)
  , ⊔-univ dr (⊔-bound₂ dp)
... | inj₂ (Γ₂' , (mp₂ , refl)) =
  let (r , dr) = cut-lemma p₂ (⊔-bound₂ dp) (i⊗ q₁ q₂) dq (⊝-suc mp₂) mq CdC⊥ sa in
    ex (i⊗ p₁ (ex r ~-rotate¹r))
       (~-trans
          (~-dip (~-++-assoc {Γ₁ = Γ₁} {Γ₂ = Γ₂'}))
          ~-rotate¹l)
  , ⊔-univ (⊔-bound₁ dp) dr
---- Par on the left (commutative cases)
cut-lemma (i⅋ {Γ = Γ} p) dp (i⊗ {Γ₁ = Δ₁} {Γ₂ = Δ₂} q₁ q₂) dq ⊝-zero (⊝-suc mq) CdC⊥ sa
  with ⊝-concat-cases {Γ₁ = Δ₁} {Γ₂ = Δ₂} mq
... | inj₁ (Δ₁' , (mq₁ , refl)) =
  let (r , dr) = cut-lemma (i⅋ p) dp q₁ (⊔-bound₁ dq) ⊝-zero (⊝-suc mq₁) CdC⊥ sa in
    ex (i⊗ r q₂)
       (~-dip (~-sym (~-++-assoc {Γ₁ = Γ} {Γ₂ = Δ₁'} {Γ₃ = Δ₂})))
  , ⊔-univ dr (⊔-bound₂ dq)
... | inj₂ (Δ₂' , (mq₂ , refl)) =
  let (r , dr) = cut-lemma (i⅋ p) dp q₂ (⊔-bound₂ dq) ⊝-zero (⊝-suc mq₂) CdC⊥ sa in
    ex (i⊗ q₁ r)
       (~-dip (~-trans (~-++-assoc {Γ₁ = Δ₁} {Γ₂ = Γ} {Γ₃ = Δ₂'})
                       (~-trans (~-rotate213 {Γ₁ = Δ₁} {Γ₂ = Γ} {Γ₃ = Δ₂'})
                                (~-sym (~-++-assoc {Γ₁ = Γ} {Γ₂ = Δ₁} {Γ₃ = Δ₂'})))))
  , ⊔-univ (⊔-bound₁ dq) dr
cut-lemma (i⅋ p) dp (i⊗ q₁ q₂) dq (⊝-suc mp) mq CdC⊥ sa =
  let (r , dr) = cut-lemma p dp (i⊗ q₁ q₂) dq (⊝-suc (⊝-suc mp)) mq CdC⊥ sa in 
    ex (i⅋ (ex r (~-trans ~-rotate¹r (~-dip ~-rotate¹r))))
       ~-rotate¹l
  , dr
cut-lemma (i⅋ p) dp (i⅋ q) dq ⊝-zero (⊝-suc mq) CdC⊥ sa =
  let (r , dr) = cut-lemma (i⅋ p) dp q dq ⊝-zero (⊝-suc (⊝-suc mq)) CdC⊥ sa in
    i⅋ r
  , dr
cut-lemma (i⅋ p) dp (i⅋ q) dq (⊝-suc mp) mq CdC⊥ sa =
  let (r , dr) = cut-lemma p dp (i⅋ q) dq (⊝-suc (⊝-suc mp)) mq CdC⊥ sa in
    ex (i⅋ (ex r (~-trans ~-rotate¹r (~-dip ~-rotate¹r))))
       ~-rotate¹l
  , dr

---- Cut elimination ----

-- A derivation of depth at most 1 + d
-- can always be transformed into a derivation of depth at most d.
-- The proof of this lemma is easy by structural induction
-- on the derivation, resorting to the main technical lemma
-- in the case of cut.
cut-decrease-depth : ∀ {d}
                   → (p : ⊢ Γ)
                   → depth p ≤ 1 + d
                   → Σ[ q ∈ ⊢ Γ ] depth q ≤ d
cut-decrease-depth (ax x)        _  = ax x , z≤n
cut-decrease-depth (i⊗ p₁ p₂)    dp =
  let (q₁ , dq₁) = cut-decrease-depth p₁ (⊔-bound₁ dp)
      (q₂ , dq₂) = cut-decrease-depth p₂ (⊔-bound₂ dp)
   in i⊗ q₁ q₂ , ⊔-univ dq₁ dq₂
cut-decrease-depth (i⅋ p)        dp =
  let (q , dq) = cut-decrease-depth p dp
   in i⅋ q , dq
cut-decrease-depth (ex p ep)      dp =
  let (q , dq) = cut-decrease-depth p dp
   in ex q ep , dq
cut-decrease-depth (cut {A = A} AdA⊥ p₁ p₂) dp =
  let dA  = ⊔-bound₁ {n = size A} {m = depth p₁} (⊔-bound₁ dp)
      dp₁ = ⊔-bound₂ {n = size A} {m = depth p₁} (⊔-bound₁ dp)
      dp₂ = ⊔-bound₂ dp
      (q₁ , dq₁) = cut-decrease-depth p₁ dp₁
      (q₂ , dq₂) = cut-decrease-depth p₂ dp₂
   in cut-lemma q₁ dq₁ q₂ dq₂ ⊝-zero ⊝-zero AdA⊥ dA

-- A derivation of depth at most d can always be transformed
-- into a cut-free proof (i.e. a derivation of depth zero).
-- This is by induction on d, by repeatedly applying the
-- previous lemma.
cut-elimination' : ∀ {d}
                 → (p : ⊢ Γ) → depth p ≤ d
                 → Σ[ q ∈ ⊢ Γ ] depth q ≡ zero
cut-elimination' {d = zero}  p dp = p , n≤0⇒n≡0 dp
cut-elimination' {d = suc d} p dp =
  let (p' , dp') = cut-decrease-depth p dp in
    cut-elimination' p' dp'

-- Any derivation can be transformed into a cut-free derivation.
-- An immediate consequence of the previous lemma.
cut-elimination : ⊢ Γ → Σ[ q ∈ ⊢ Γ ] depth q ≡ zero
cut-elimination p = cut-elimination' {d = depth p} p ≤-refl

-- An easy corollary of cut elimination is consistency
-- (the empty sequent is not derivable).
consistency : ¬ (⊢ ∅)
consistency p = let (q , dq) = cut-elimination p in
                  rec q dq refl
  where
    -- A cut-free proof does not prove the empty sequent.
    rec : (p : ⊢ Γ) → depth p ≡ zero → ¬(Γ ≡ ∅)
    rec (ax _)    _  ()
    rec (i⊗ _ _)  _  ()
    rec (i⅋ _)    _  ()
    rec (ex p ep) dp refl =
      rec p dp (~-eq-empty ep)
    rec (cut {A = A} AdA⊥ p₁ p₂) dp q =
      size≢0 {A = A}
        (n≤0⇒n≡0 (⊔-bound₁ {n = size A} {m = depth p₁} (⊔-bound₁ (≤-reflexive dp))))
