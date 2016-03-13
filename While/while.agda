module While.while where

open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Vec
open import Data.Maybe
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic

-- data structure of expression
data E (n : ℕ) : Set where
  var  : Fin n → E n
  nil  : E n
  cons : E n → E n → E n
  hd   : E n → E n
  tl   : E n → E n
  _=?_ : E n → E n → E n

-- translate D into expression
dtoE : {n : ℕ} → D → E n
dtoE dnil = nil
dtoE (d₁ ∙ d₂) = cons (dtoE d₁) (dtoE d₂)

infixr 20 _→→_
-- data structure of command
data C (n : ℕ) : Set where
  _:=_  : Fin n  → E n → C n
  _→→_  : C n → C n → C n
  while : E n → C n → C n

-- data structure of program
data P (n : ℕ) : Set where
  prog : Fin n → C n → Fin n → P n

-- find correspondence value of the variable
dlookup : {n : ℕ} → Fin n → Vec D n → D
dlookup zero (x ∷ v) = x
dlookup (suc n) (x ∷ v) = dlookup n v

-- evaluate the expression
eval : {n : ℕ} → E n → Vec D n → D
eval (var x) v = dlookup x v
eval nil v = dnil
eval (cons e₁ e₂) v = eval e₁ v ∙ eval e₂ v
eval (hd e) v = dfst (eval e v)
eval (tl e) v = dsnd (eval e v)
eval (e₁ =? e₂) v = EqualD?-case dtrue dfalse (equalD? (eval e₁ v) (eval e₂ v))

-- property of equal and eval =?
eq-ok : {n : ℕ} → (e₁ e₂ : E n) → (env : Vec D n) → eval (e₁ =? e₂) env ≡ dequal (eval e₁ env) (eval e₂ env)
eq-ok e₁ e₂ env with equalD? (eval e₁ env) (eval e₂ env)
eq-ok e₁ e₂ env | eq x = refl
eq-ok e₁ e₂ env | neq x = refl

-- the set that have element
record ⊤ : Set where

tt : ⊤
tt = record {}

-- check the data D is nil or not
isNil : D → Set
isNil dnil = ⊤
isNil _ = ⊥

-- check the data D is tree (not nil) or not
isTree : D → Set
isTree dnil = ⊥
isTree _ = ⊤

-- property of isNil
isNil-ok : (d : D) → isNil d → d ≡ dfalse
isNil-ok dnil q = refl
isNil-ok (d₁ ∙ d₂) () 

-- property of isTree
isTree-ok : (d : D) → isTree d → d ≢ dnil
isTree-ok dnil ()
isTree-ok (d ∙ d₁) p = t≢n

-- property of isNil and is Tree
nilIsnil : {d : D} → d ≡ dnil → isNil d
nilIsnil refl = _

treeIstree : {d d₁ d₂ : D} → d ≡ (d₁ ∙ d₂) → isTree d
treeIstree refl = _

-- update the value to the environment (vector)
updateE : {n : ℕ} → Fin n → D →  Vec D n  → Vec D n
updateE zero d (x ∷ v) = d ∷ v
updateE (suc n) d (x ∷ v) = x ∷ updateE n d v

-- the relationship between the input environment and output environment with the given command
data _⊢_⇒_ {n : ℕ} : C n → Vec D n  → Vec D n → Set where
  whilef : {e : E n}{c : C n}{env : Vec D n}
         → isNil (eval e env)
         → (while e c) ⊢ env ⇒ env
  whilet : {e : E n}{c : C n}{env₁ env₂ env₃ : Vec D n}
         → isTree (eval e env₁)
         → c ⊢ env₁ ⇒ env₂
         → (while e c) ⊢ env₂ ⇒ env₃
         → (while e c) ⊢ env₁ ⇒ env₃
  assign : {v : Fin n}{e : E n}{env : Vec D n}
         → (v := e) ⊢ env ⇒ (updateE v (eval e env) env)
  seq    : {c₁ c₂ : C n}{env₁ env₂ env₃ : Vec D n}
         → c₁ ⊢ env₁ ⇒ env₂
         → c₂ ⊢ env₂ ⇒ env₃
         → (c₁ →→ c₂) ⊢ env₁ ⇒ env₃

-- get the intermidiem environment
getInterim : {n : ℕ}{c : C n}{env₁ env₂ : Vec D n} → c ⊢ env₁ ⇒ env₂ → Vec D n
getInterim (whilef {e}{c}{env} f) = env
getInterim (whilet {e}{c}{env₁}{env₂}{env₃} t c₁ c₂) = env₂
getInterim (assign {v}{e}{env}) = env
getInterim (seq {c₁}{c₂}{env₁}{env₂}{env₃} cr₁ cr₂) = env₂

-- get the result environment
getResult : {n : ℕ}{c : C n}{env₁ env₂ : Vec D n} → c ⊢ env₁ ⇒ env₂ → Vec D n
getResult (whilef {e}{c}{env} f) = env
getResult (whilet {e}{c}{env₁}{env₂}{env₃} t c₁ c₂) = env₃
getResult (assign {v}{e}{env}) = (updateE v (eval e env) env)
getResult (seq {c₁}{c₂}{env₁}{env₂}{env₃} cr₁ cr₂) = env₃

-- get the command
getCommand : {n : ℕ}{c : C n}{env₁ env₂ : Vec D n} → c ⊢ env₁ ⇒ env₂ → C n
getCommand (whilef {e}{c} x) = while e c
getCommand (whilet {e}{c} x c₁ c₂) = while e c
getCommand (assign {v}{e}) = v := e
getCommand (seq {x}{y} c c₃) = x →→ y

-- property of getResult
getResult-ok : {n : ℕ}{c : C n}{env₁ env₂ : Vec D n} → (p : c ⊢ env₁ ⇒ env₂) → env₂ ≡ getResult p
getResult-ok (whilef x) = refl
getResult-ok (whilet x p p₁) = refl
getResult-ok assign = refl
getResult-ok (seq p p₁) = refl

-- proof the consistency of the tree
consist : (d : D) → isTree d → isNil d → ⊥
consist dnil () t
consist (d₁ ∙ d₂) t ()

-- calculate the loops inside the execution of command
loop-ct : {n : ℕ}{c : C n}{env₁ env₂ : Vec D n} → c ⊢ env₁ ⇒ env₂ → D
loop-ct (whilef x) = dnil
loop-ct (whilet x p p₁) = (loop-ct p) ∙ (loop-ct p₁)
loop-ct assign = dnil
loop-ct (seq p p₁) = (loop-ct p) ∙ (loop-ct p₁)

-- proof that exec the same command with same input environment will result same output environment
⊢ok : {n : ℕ}{c : C n}{env₁ env₂ env₃ : Vec D n} → c ⊢ env₁ ⇒ env₂ → c  ⊢ env₁ ⇒ env₃ → env₂ ≡ env₃
⊢ok (whilef x) (whilef x₁) = refl
⊢ok (whilef {e}{c}{env₁} f)
         (whilet {.e}{.c}{.env₁} t exec₁ exec₂) with eval e env₁
... | d with consist d t f
⊢ok (whilef f) (whilet t exec₁ exec₂) | h | ()
⊢ok (whilet {e}{c}{env₁} t exec₁ exec₂)
         (whilef {.e}{.c}{.env₁} f) with eval e env₁
... | d with consist d t f
⊢ok (whilet t exec₁ exec₂) (whilef f) | h | ()
⊢ok (whilet t₁ exec₁ exec₂) (whilet t₂ exec₃ exec₄) with ⊢ok exec₁ exec₃
... | refl = ⊢ok exec₂ exec₄
⊢ok assign assign = refl
⊢ok (seq exec₁ exec₂) (seq exec₃ exec₄) with ⊢ok exec₁ exec₃
⊢ok (seq exec₁ exec₂) (seq exec₃ exec₄) | refl = ⊢ok exec₂ exec₄

-- generate initial environment
dNil : {n : ℕ} → Fin n → D
dNil _ = dnil

initialVec : {n : ℕ} → Vec D n
initialVec = tabulate dNil

-- relation ship with a given program, the input and the output
data ExecP {n : ℕ} : P n → D → D → Set where
  terminate : (x y : Fin n){c : C n}{env : Vec D n}{d : D}
            → c ⊢ (updateE x d initialVec) ⇒ env
            → ExecP (prog x c y) d (dlookup y env)

-- get command from a program
getCommandP : {n : ℕ} → P n → C n
getCommandP (prog x c y) = c

-- proof that exec the same program with same input will result same output
execP-ok : {n : ℕ}{p : P n}{d₁ d₂ d₃ : D} → ExecP p d₁ d₂ → ExecP p d₁ d₃ → d₂ ≡ d₃
execP-ok (terminate i j exec₁) (terminate .i .j exec₂) with ⊢ok exec₁ exec₂
execP-ok (terminate i j exec₁) (terminate .i .j exec₂) | refl = refl



