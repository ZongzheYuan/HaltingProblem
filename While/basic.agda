module While.basic where

open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)

-- tuple
data _×_ (A B : Set) : Set where
  <_,_> : A → B → A × B

fst : {A B : Set} → A × B → A
fst < x , y > = x

snd : {A B : Set} → A × B → B
snd < x , y > = y

-- triple
data _×_×_ (A B C : Set) : Set where
  <_,_,_> : A → B → C → A × B × C

ini : {A B C : Set} → A × B × C → A
ini < x , y , z > = x

mid : {A B C : Set} → A × B × C → B
mid < x , y , z > = y

lst : {A B C : Set} → A × B × C → C
lst < x , y , z > = z

{-
-- the tree structure of calling
data CallTree : Set where
  leaf : CallTree
  node : CallTree → CallTree → CallTree
-}

-- inspect of data
data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

-- data structure of evaluation tree
infix 20 _∙_
data D : Set where
  dnil : D 
  _∙_  : D → D → D

-- first element of the tree
dfst : D → D
dfst dnil = dnil
dfst (d₁ ∙ d₂) = d₁

-- second element of the tree
dsnd : D → D
dsnd dnil = dnil
dsnd (d₁ ∙ d₂) = d₂

-- reflectiviety
≡ok : {A : Set}{a b : A} → a ≡ b → b ≡ a
≡ok refl = refl

-- neq of tree
data _≢_ : D → D → Set where
  n≢t  : {m n : D} → dnil ≢ (m ∙ n)
  t≢n  : {m n : D} → (m ∙ n) ≢ dnil
  t≢trs : {m n p : D} → m ≢ n → (m ∙ p) ≢ (n ∙ p)
  t≢trd : {m n p q : D} → m ≢ n → (m ∙ p) ≢ (n ∙ q)
  t≢tls : {m n p : D} → m ≢ n → (p ∙ m) ≢ (p ∙ n)
  t≢tld : {m n p q : D} → m ≢ n → (p ∙ m) ≢ (q ∙ n)

-- neq = eq → False
≢≡⊥ : {d₁ d₂ : D} → d₁ ≢ d₂ → d₁ ≡ d₂ → ⊥
≢≡⊥ (t≢trs q) refl = ≢≡⊥ q refl
≢≡⊥ (t≢trd q) refl = ≢≡⊥ q refl
≢≡⊥ (t≢tls q) refl = ≢≡⊥ q refl
≢≡⊥ (t≢tld q) refl = ≢≡⊥ q refl

-- relationship of two trees, equal or not
data EqualD? (m n : D) : Set where
  eq  : m ≡ n → EqualD? m n
  neq : m ≢ n → EqualD? m n

EqualD?-case : {A : Set} {m n : D} → A → A → EqualD? m n → A
EqualD?-case a b (eq x) = a
EqualD?-case a b (neq x) = b

-- false in D
dfalse : D
dfalse = dnil

-- standard true in D
dtrue : D
dtrue = dnil ∙ dnil

-- true can't be false
true-false : dtrue ≡ dfalse → ⊥
true-false ()

-- check the equality of two trees
equalD? : (m n : D) → EqualD? m n
equalD? dnil dnil = eq refl
equalD? dnil (n ∙ n₁) = neq n≢t
equalD? (m ∙ m₁) dnil = neq t≢n
equalD? (m ∙ m₁) (n ∙ n₁) with equalD? m n
equalD? (m ∙ m₁) (.m ∙ n₁)  | eq refl with equalD? m₁ n₁
equalD? (m ∙ m₁) (.m ∙ .m₁) | eq refl | eq refl = eq refl
equalD? (m ∙ m₁) (.m ∙ n₁)  | eq refl | neq q = neq (t≢tls q)
equalD? (m ∙ m₁) (n ∙ n₁)   | neq x with equalD? m₁ n₁
equalD? (m ∙ m₁) (n ∙ .m₁)  | neq p   | eq refl = neq (t≢trs p)
equalD? (m ∙ m₁) (n ∙ n₁)   | neq p   | neq q = neq (t≢trd p)

-- reflectivity of equalD
equalD-refl : (m : D) → equalD? m m ≡ eq refl
equalD-refl m with equalD? m m
equalD-refl m | eq refl = refl
equalD-refl m | neq x with ≢≡⊥ x refl
equalD-refl m | neq x | ()

-- equality of D
dequal : D → D → D
dequal d₁ d₂ with equalD? d₁ d₂
dequal d₁ d₂ | eq x = dtrue
dequal d₁ d₂ | neq x = dfalse

-- property of equality
dequal-true : (d₁ d₂ : D) → d₁ ≡ d₂ → dequal d₁ d₂ ≡ dtrue
dequal-true d₁ .d₁ refl with equalD? d₁ d₁
dequal-true d₁ .d₁ refl | eq refl = refl
dequal-true d₁ .d₁ refl | neq x with ≢≡⊥ x refl
dequal-true d₁ .d₁ refl | neq x | ()

dequal-false : (d₁ d₂ : D) → d₁ ≢ d₂ → dequal d₁ d₂ ≡ dfalse
dequal-false d₁ d₂ p with equalD? d₁ d₂
dequal-false d₁ d₂ p | eq x with ≢≡⊥ p x
dequal-false d₁ d₂ p | eq x | ()
dequal-false d₁ d₂ p | neq x = refl

-- split the tree
splitD : (d : D) → d ≢ dnil → D × D
splitD dnil p with ≢≡⊥ p refl
splitD dnil p | ()
splitD (d₁ ∙ d₂) p = < d₁ , d₂ >

-- the property of split
splitD-ok : (d : D) → (p : d ≢ dnil) → d ≡ ( fst (splitD d p) ∙ snd (splitD d p))
splitD-ok dnil p with ≢≡⊥ p refl
splitD-ok dnil p | ()
splitD-ok (d ∙ d₁) p = refl

-- translate natural number to D
const : (n : ℕ) → D
const zero = dnil
const (suc n) = (dnil ∙ dnil) ∙ const n

-- translate n to tree D
ntoD : ℕ → D
ntoD zero = dnil
ntoD (suc n) = const 1 ∙ ntoD n

-- translate fin to d
dftod : {n : ℕ} → Fin n → D
dftod zero = dnil
dftod (suc n) = (dnil ∙ dnil)  ∙ dftod n

-- euqation chains
infix  15 _∎
infixr 10 _=⟨_⟩_

_=⟨_⟩_ : {A : Set} (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
_ =⟨ refl ⟩ refl = refl

_∎ : {A : Set} (x : A) → x ≡ x
_ ∎ = refl

-- function application
general-ap : {A B : Set} → (f : A → B) → {a₁ a₂ : A} → (p : a₁ ≡ a₂) → f a₁ ≡ f a₂
general-ap f refl = refl
