module HaltingProblem.finalproof where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec
open import Data.Empty
open import While.basic
open import While.while
open import Universal.interpret
open import Haltingproblem.u
open import Haltingproblem.proof6
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import Data.Product renaming (_,_ to _,'_; _×_ to _×'_; <_,_> to <_,'_> )

-- transform the environment with multi-variables to the environment that has only one variable
env-multi-one : {n : ℕ} → Vec D n → Vec D 1
env-multi-one [] = dnil ∷ []
env-multi-one (x ∷ v) = x ∙ head (env-multi-one v) ∷ []

-- generate an expression to find the value to the variable in teh one-variable envionment
e-var : {n : ℕ} → Fin n → E 1 → E 1
e-var zero e = e
e-var (suc n₁) e = tl (e-var n₁ e)

-- transform the expression under multi-variables to the expression that only use one varaible
e-multi-one : {n : ℕ} → E n → E 1
e-multi-one (var x) = hd (e-var x (var zero))
e-multi-one nil = nil
e-multi-one (cons e e₁) = cons (e-multi-one e) (e-multi-one e₁)
e-multi-one (hd e) = hd (e-multi-one e)
e-multi-one (tl e) = tl (e-multi-one e)
e-multi-one (e =? e₁) = (e-multi-one e) =? (e-multi-one e₁)

-- equality of the combination of the binary tree
d-cons-ok : {d₁ d₂ d₃ d₄ : D}
            → d₁ ≡ d₃
            → d₂ ≡ d₄
            → d₁ ∙ d₂ ≡ d₃ ∙ d₄
d-cons-ok refl refl = refl

-- proof the equality of finding value under the original environment and the transformed environment
lemma-e : {n : ℕ} → {x : Fin n} → {env : Vec D n}
        → dlookup x env ≡ dfst (eval (e-var x (var zero)) (env-multi-one env))
lemma-e {x = zero} {d ∷ env} = refl
lemma-e {x = suc x} {d ∷ env} with inspect (env-multi-one env)
lemma-e {._} {suc x₁} {d ∷ env} | it (x ∷ []) p = dlookup x₁ env
                                                  =⟨ lemma-e {_} {x₁} {env} ⟩
                                                  dfst (eval (e-var x₁ (var zero)) (env-multi-one env))
                                                  =⟨ cong dfst (eval (e-var x₁ (var zero)) (env-multi-one env)
                                                               =⟨ cong (λ v → eval (e-var x₁ (var zero)) v) p ⟩
                                                               eval (e-var x₁ (var zero)) (x ∷ [])
                                                               =⟨ sym (lemma₂ {_} {x₁} {x} {d}) ⟩
                                                               eval (e-var x₁ (tl (var zero))) (d ∙ x ∷ [])
                                                               =⟨ sym (lemma₁ {_} {x₁} {d ∙ x ∷ []}) ⟩
                                                               dsnd (eval (e-var x₁ (var zero)) (d ∙ x ∷ []))
                                                               =⟨ sym
                                                                    (cong (λ v → dsnd (eval (e-var x₁ (var zero)) (d ∙ head v ∷ [])))
                                                                     p) ⟩
                                                               dsnd (eval (e-var x₁ (var zero)) (d ∙ head (env-multi-one env) ∷ []))
                                                               ∎) ⟩
                                                  dfst (dsnd (eval (e-var x₁ (var zero)) (d ∙ head (env-multi-one env) ∷ [])))
                                                  ∎

  where lemma₁ : {n : ℕ} → {x : Fin n} → {env : Vec D 1} →
                   dsnd (eval (e-var x (var zero)) env) ≡ eval (e-var x (tl (var zero))) env
        lemma₁ {x = zero} = refl
        lemma₁ {x = suc x₁} = cong dsnd (lemma₁ {x = x₁})
        
        lemma₂ : {n : ℕ} → {x : Fin n} → {d y : D} →
                   eval (e-var x (tl (var zero))) (y ∙ d ∷ []) ≡ eval (e-var x (var zero)) (d ∷ [])
        lemma₂ {x = zero} = refl
        lemma₂ {x = suc x₁} = cong dsnd (lemma₂ {x = x₁})

-- evaluate the original expression under some environment
-- will have the same result compare to
-- evaluste the transformed expression under the transformed environment
e-multi-one-ok : {n : ℕ} → (e : E n) → {env : Vec D n}
                 → eval e env ≡ eval (e-multi-one e) (env-multi-one env)
e-multi-one-ok {n} (var x) {env} = lemma-e {n} {x} {env}
e-multi-one-ok nil = refl
e-multi-one-ok (cons e e₁) = d-cons-ok (e-multi-one-ok e) (e-multi-one-ok e₁)
e-multi-one-ok (hd e) = cong dfst (e-multi-one-ok e)
e-multi-one-ok (tl e) = cong dsnd (e-multi-one-ok e)
e-multi-one-ok (e =? e₁) {env} with equalD? (eval e env) (eval e₁ env)
e-multi-one-ok (e =? e₁) {env} | eq x with equalD? (eval (e-multi-one e) (env-multi-one env)) (eval (e-multi-one e₁) (env-multi-one env))
e-multi-one-ok (e =? e₁) | eq x₁ | eq x = refl
e-multi-one-ok (e =? e₁) {env} | eq x₁ | neq x with ≢≡⊥ (subst (λ d₁ → d₁ ≢ eval e₁ env) (sym (e-multi-one-ok e {env}))
                                                           (subst (λ d₂ → eval (e-multi-one e) (env-multi-one env) ≢ d₂) (sym (e-multi-one-ok e₁ {env})) x)) x₁
e-multi-one-ok (e =? e₁) | eq x₁ | neq x | ()
e-multi-one-ok (e =? e₁) {env} | neq x with equalD? (eval (e-multi-one e) (env-multi-one env)) (eval (e-multi-one e₁) (env-multi-one env))
e-multi-one-ok (e =? e₁) {env} | neq x₁ | eq x with ≢≡⊥ (subst (λ d₁ → d₁ ≢ eval (e-multi-one e₁) (env-multi-one env))
                                                           (e-multi-one-ok e {env})
                                                           (subst (λ d₂ → eval e env ≢ d₂) (e-multi-one-ok e₁ {env}) x₁)) x
e-multi-one-ok (e =? e₁) | neq x₁ | eq x | ()
e-multi-one-ok (e =? e₁) | neq x₁ | neq x = refl

-- zip the vector into a tuple of two vectors
zipVec :  {m n : ℕ} → Vec D (m + n) → Vec D m × Vec D n
zipVec {m = zero} x = < [] , x >
zipVec {m = (suc m)} (x ∷ res) with zipVec {m = m} res
zipVec {m = (suc m)} (x ∷ res) | < l , r > = < x ∷ l , r >

-- append an element into the end of one vector
appendVec : {m : ℕ} → Vec D m → D → Vec D (suc m)
appendVec {zero} [] y = y ∷ []
appendVec {suc m} (x ∷ xs) y with appendVec xs y
... | h = x ∷ h

-- concat a tuple of two vectors into one vector
unzipVec : {m n : ℕ} → Vec D m × Vec D n → Vec D (m + n)
unzipVec < [] , r > = r
unzipVec < x ∷ l , r > with unzipVec < l , r >
... | h = x ∷ h

-- helping lemma
suc-ok : {a b : ℕ} → a + suc b ≡ suc (a + b)
suc-ok {zero} = refl
suc-ok {suc a} = cong suc (suc-ok {a})

-- using subst twice equals to the original one
subst-subst : ∀ {i j} {A : Set i} {B : A → Set j} {a a' : A} (p : a ≡ a') (b : B a) →
              subst B (sym p) (subst B p b) ≡ b
subst-subst refl b = refl

-- apply subst to the vector
append-subst : {n m : ℕ}{vn : Vec D n}{x : D}{p : n ≡ m}
               → (x ∷ subst (Vec D) p vn) ≡ subst (Vec D) (cong suc p) (x ∷ vn)
append-subst {vn = vn} {p = refl} = refl

-- unzip with two vector, a ++ [b] ++ c ≡ a ++ (b ∷ c)
append-h : {m n : ℕ}{vm : Vec D m}{vn : Vec D n}{d : D}
           → (unzipVec < appendVec vm d , vn >) ≡ subst (Vec D) (suc-ok {m} {n}) (unzipVec < vm , d ∷ vn >)
append-h {vm = []} = refl
append-h {suc m}{n}{vm = x ∷ vm} {vn = vn} {d} = 
                 unzipVec < x ∷ appendVec vm d , vn >
                 =⟨ refl ⟩
                 (x ∷ unzipVec < appendVec vm d , vn >)
                 =⟨ cong (λ y → x ∷ y) (append-h {m}{n}{vm}{vn}{d}) ⟩
                 (x ∷  subst (Vec D) (suc-ok {m}{n}) (unzipVec < vm , d ∷ vn >))
                 =⟨ append-subst {vn = unzipVec < vm , d ∷ vn >} {x = x} {p = suc-ok {m}{n}}  ⟩
                 subst (Vec D) (cong suc (suc-ok {m}{n})) (x ∷ unzipVec < vm , d ∷ vn >)
                 =⟨ refl ⟩ 
                 subst (Vec D) (cong suc (suc-ok {m}{n})) (unzipVec < x ∷ vm , d ∷ vn >)
                 ∎ 
append-Ok : {m n : ℕ}{vm : Vec D m}{vn : Vec D n}{d : D}
          → subst (Vec D) (sym (suc-ok {m} {n})) (unzipVec < appendVec vm d , vn >) ≡ (unzipVec < vm , d ∷ vn >)
append-Ok {m}{n}{vm}{vn}{d} = subst (Vec D) (sym (suc-ok {m} {n}))
                                (unzipVec < appendVec vm d , vn >)
                              =⟨ cong (subst (Vec D) (sym (suc-ok {m} {n}))) (append-h {m}{n}{vm}{vn}{d}) ⟩
                              subst (Vec D) (sym (suc-ok {m} {n}))
                                (subst (Vec D) (suc-ok {m} {n}) (unzipVec < vm , d ∷ vn >))
                              =⟨ subst-subst (suc-ok {m} {n}) (unzipVec < vm , d ∷ vn >) ⟩ 
                              unzipVec < vm , d ∷ vn > ∎

-- find the value of the variable, construct new expression to assign it
c-var : {n : ℕ} → Fin n → ℕ → E 1 → E 1
c-var zero y e = cons e (e-var (fromℕ (suc y)) (var zero))
c-var (suc x) y e = cons (hd (e-var (fromℕ y) (var zero))) (c-var x (suc y) e)

-- transform the command under multi-variables to the expression that only use one varaible
c-multi-one : {n : ℕ} → C n → C 1
c-multi-one (x := e) = zero := c-var x zero (e-multi-one e)
c-multi-one (c →→ c₁) = c-multi-one c →→ c-multi-one c₁
c-multi-one (while x c) = while (e-multi-one x) (c-multi-one c)

-- helping lemma used in the proof of the correctness of the command transformation
-- prove the first element doesn't influence the result
lemma-dsnd : {d₁ d₂ : D}{m : ℕ}{n : Fin m} → dsnd (eval (e-var n (var zero)) (d₁ ∙ d₂ ∷ [])) ≡ eval (e-var n (var zero)) (d₂ ∷ [])
lemma-dsnd {n = zero} = refl
lemma-dsnd {n = suc n₂} = cong dsnd (lemma-dsnd {n = n₂})

-- prove the one variable environment only has one variable
lemma-env-multi-one : {n : ℕ}{env : Vec D n} → env-multi-one env ≡ head (env-multi-one env) ∷ []
lemma-env-multi-one {env = []} = refl
lemma-env-multi-one {env = x ∷ env₁} = refl

-- prove the property of zipper and e-var
lemma-x : {m n : ℕ}{x : D}{env₁ : Vec D m}{env₂ : Vec D n} →
          x ≡  dfst (eval (e-var (fromℕ m) (var zero))(env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
lemma-x {zero} {env₁ = []} = refl
lemma-x {suc m}{x = x}{env₁ = x₁ ∷ env₁}{env₂ = env₂} = x
                                                        =⟨ lemma-x {m} {x = x} {env₁} {env₂} ⟩
                                                        dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                        =⟨ cong (λ a → dfst (eval (e-var (fromℕ m) (var zero)) a)) (lemma-env-multi-one {env = unzipVec < env₁ , x ∷ env₂ >}) ⟩
                                                        dfst (eval (e-var (fromℕ m) (var zero)) (head (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∷ []))
                                                        =⟨ cong dfst (sym (lemma-dsnd {x₁} {head (env-multi-one (unzipVec < env₁ , x ∷ env₂ >))} {_}{fromℕ m})) ⟩
                                                        dfst (dsnd (eval (e-var (fromℕ m) (var zero))  (x₁ ∙ head (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∷ [])))
                                                        ∎

-- prove the property of dsnd and e-var
lemma-e-var : {m n : ℕ}{env₁ : Vec D m}{env₂ : Vec D n}{x : D}
              → head (env-multi-one env₂) ≡ dsnd (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
lemma-e-var {zero} {env₁ = []} = refl
lemma-e-var {suc m}{env₁ = a ∷ env₁}{env₂ = env₂}{x = x} = head (env-multi-one env₂)
                                                           =⟨ lemma-e-var {m} {_} {env₁} {env₂} {x} ⟩
                                                           dsnd (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                           =⟨ cong (λ b → dsnd (eval (e-var (fromℕ m) (var zero)) b)) (lemma-env-multi-one {_} {unzipVec < env₁ , x ∷ env₂ >}) ⟩
                                                           dsnd (eval (e-var (fromℕ m) (var zero)) (head (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∷ []))
                                                           =⟨ cong (λ b → dsnd b) (sym (lemma-dsnd {a}{head (env-multi-one (unzipVec < env₁ , x ∷ env₂ >))} {suc m}{fromℕ m})) ⟩
                                                           dsnd (dsnd (eval (e-var (fromℕ m) (var zero)) (a ∙ head (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∷ [])))
                                                           ∎

-- apply subst on eval
subst-lemma₁ : {m n : ℕ}{e : E m}{env : Vec D n}{p : m ≡ n}
             → eval e (subst (Vec D) (sym p) env) ≡ eval (subst E p e) env
subst-lemma₁ {p = refl} = refl
subst-lemma₂ : {m n : ℕ}{a b : ℕ}{y : Fin b}{e : E m}{env : Vec D n}{p : m ≡ n}
             → eval (c-var y (suc a) (e-multi-one (subst E p e))) (env-multi-one env) ≡
               eval (c-var y (suc a) (e-multi-one e)) (env-multi-one (subst (Vec D) (sym p) env))
subst-lemma₂ {p = refl} = refl

-- lemma to prove the property of eval
lemma-eval : {m n : ℕ}{y : Fin n}{e : E (m + n)}{env₁ : Vec D m}{env₂ : Vec D n} →
        head (env-multi-one (updateE y (eval e (unzipVec < env₁ , env₂ >)) env₂))
        ≡ eval (c-var y m (e-multi-one e)) (env-multi-one (unzipVec < env₁ , env₂ >))
lemma-eval {m = m}{y = zero}{e = e}{env₁ = env₁}{env₂ = x ∷ env₂} = eval e (unzipVec < env₁ , x ∷ env₂ >) ∙ head (env-multi-one env₂)
                                                               =⟨ cong (λ x₁ → x₁ ∙ head (env-multi-one env₂)) (e-multi-one-ok e {unzipVec < env₁ , x ∷ env₂ >}) ⟩
                                                               eval (e-multi-one e) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∙ head (env-multi-one env₂)
                                                               =⟨ cong (λ a → eval (e-multi-one e) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∙ a) (lemma-e-var {m} {_} {env₁} {env₂} {x}) ⟩
                                                               eval (e-multi-one e) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)) ∙
                                                               dsnd (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                               ∎
lemma-eval {m = m}{y = suc y}{e = e}{env₁ = env₁}{env₂ = x ∷ env₂} = x ∙ head (env-multi-one (updateE y (eval e (unzipVec < env₁ , x ∷ env₂ >)) env₂))
                                                                =⟨ cong (λ a → a ∙ head (env-multi-one (updateE y (eval e (unzipVec < env₁ , x ∷ env₂ >)) env₂)))
                                                                        (lemma-x {x = x} {env₁ = env₁} {env₂ = env₂}) ⟩
                                                                dfst(eval (e-var (fromℕ m) (var zero))(env-multi-one (unzipVec < env₁ , x ∷ env₂ >))) ∙
                                                                head (env-multi-one (updateE y (eval e (unzipVec < env₁ , x ∷ env₂ >)) env₂))
                                                                =⟨ cong (λ a → dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                               ∙ head (env-multi-one (updateE y (eval e a) env₂))) (sym (append-Ok {_} {_} {env₁} {env₂} {x})) ⟩
                                                                dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                ∙ head (env-multi-one (updateE y (eval e (subst (Vec D) (sym (suc-ok {m} {_})) (unzipVec < appendVec env₁ x , env₂ >))) env₂))                                                                                                             =⟨ cong (λ a → dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                              ∙ head (env-multi-one (updateE y a env₂))) (subst-lemma₁ {e = e} {env = unzipVec < appendVec env₁ x , env₂ >}{p = suc-ok {m}}) ⟩
                                                                dfst (eval (e-var (fromℕ m) (var zero))(env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                ∙ head (env-multi-one (updateE y (eval (subst E (suc-ok {m}) e) (unzipVec < appendVec env₁ x , env₂ >)) env₂))
                                                                =⟨ cong (λ a → dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >))) ∙ a)
                                                                       (lemma-eval {_} {_} {y} {subst E (suc-ok {m}) e} {appendVec env₁ x} {env₂}) ⟩
                                                                dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                ∙ eval (c-var y (suc m) (e-multi-one (subst E (suc-ok {m}) e))) (env-multi-one (unzipVec < appendVec env₁ x , env₂ >))
                                                                =⟨ cong (λ a → dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                              ∙ a) (subst-lemma₂ {a = m} {y = y} {e = e} {env = unzipVec < appendVec env₁ x , env₂ >} {p = suc-ok {m}}) ⟩
                                                                dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                ∙ eval (c-var y (suc m) (e-multi-one e)) (env-multi-one (subst (Vec D) (sym (suc-ok {m} {_})) (unzipVec < appendVec env₁ x , env₂ >)))
                                                                =⟨ cong (λ a → dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                              ∙ eval (c-var y (suc m) (e-multi-one e)) (env-multi-one a)) (append-Ok {_} {_} {env₁} {env₂} {x}) ⟩
                                                                dfst (eval (e-var (fromℕ m) (var zero)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >)))
                                                                ∙ eval (c-var y (suc m) (e-multi-one e)) (env-multi-one (unzipVec < env₁ , x ∷ env₂ >))
                                                                ∎


-- the property of updateE with one-variable environment
lemma-env : {x : ℕ}{env : Vec D x}{d : D} → updateE zero d (env-multi-one env) ≡ d ∷ []
lemma-env {env = env}{d} with inspect (env-multi-one env)
lemma-env {env = env}{d}| it (x ∷ []) p = updateE zero d (env-multi-one env)
                                          =⟨ cong (λ x₁ → updateE zero d x₁) p ⟩
                                          updateE zero d (x ∷ [])
                                          =⟨ refl ⟩
                                          (d ∷ [])
                                          ∎
-- prove the relationship between transfer-first and transfer-last on one command
lemma-c : {x : ℕ}{y : Fin x}{e : E x}{env : Vec D x}
        → env-multi-one (updateE y (eval e env) env) ≡ updateE zero
                                                               (eval (c-var y zero (e-multi-one e)) (env-multi-one env))
                                                               (env-multi-one env)
lemma-c {y = zero}{e}{env = x ∷ env₁} = cong (λ a → a ∙ head (env-multi-one env₁) ∷ [])
                                             (e-multi-one-ok e {x ∷ env₁})
lemma-c {y = suc z}{e}{env = env} = env-multi-one (updateE (suc z) (eval e env) env)
                                    =⟨ lemma-env-multi-one {_} {updateE (suc z) (eval e env) env} ⟩
                                    (head (env-multi-one (updateE (suc z) (eval e env) env)) ∷ [])
                                    =⟨ cong (λ x → x ∷ []) (lemma-eval {zero} {_} {suc z} {e} {[]} {env}) ⟩
                                    (dfst (dlookup zero (env-multi-one env)) ∙ eval (c-var z (suc zero) (e-multi-one e)) (env-multi-one env) ∷ [])
                                    =⟨ sym (lemma-env {_} {env} {dfst (dlookup zero (env-multi-one env)) ∙ eval (c-var z (suc zero) (e-multi-one e)) (env-multi-one env)}) ⟩
                                    updateE zero (dfst (dlookup zero (env-multi-one env)) ∙ eval (c-var z (suc zero) (e-multi-one e)) (env-multi-one env)) (env-multi-one env)
                                    ∎
-- prove the correctness of the command transformation
c-multi-one-ok : {n : ℕ} → {c : C n} → {env₁ env₂ : Vec D n}
                 → c ⊢ env₁ ⇒ env₂
                 → c-multi-one c ⊢ (env-multi-one {n} env₁) ⇒ (env-multi-one {n} env₂)
c-multi-one-ok (whilef {e} x) = whilef (subst (λ d → isNil d) (e-multi-one-ok e) x)
c-multi-one-ok (whilet {e} x p p₁) = whilet (subst (λ d → isTree d) (e-multi-one-ok e) x) (c-multi-one-ok p) (c-multi-one-ok p₁)
c-multi-one-ok (assign {n}{e}{env}) = subst
                                        (λ x →
                                           (zero := c-var n zero (e-multi-one e)) ⊢ env-multi-one env ⇒ x)
                                        (sym (lemma-c {_} {n} {e} {env}))
                                        (assign {1} {zero} {c-var n zero (e-multi-one e)}
                                         {env-multi-one env})
c-multi-one-ok (seq p p₁) = seq (c-multi-one-ok p) (c-multi-one-ok p₁)

-- helper function, construct the accumulate environment from one variable
p-multi-one-h : {m : ℕ}(ini : E 1) → (inp : E 1) → (pos : Fin m) → ℕ → E 1
p-multi-one-h ini inp zero n = cons inp (e-var (fromℕ n) ini)
p-multi-one-h ini inp (suc pos) n = cons nil (p-multi-one-h ini inp pos (suc n))

-- transform the program under multi-variables to the expression that only use one varaible
p-multi-one : {n : ℕ} → P n → P 1
p-multi-one {n}(prog x c y) = prog zero ((zero := p-multi-one-h (dtoE {1} (head (env-multi-one (initialVec {n})))) (var zero) x (suc zero))
                                        →→ c-multi-one c
                                        →→ (zero := e-multi-one (var y)))
                                   zero
                                   
-- prove the accumulated one-variable environment contruction is correct
p-lemma₁ : {n : ℕ}{x : Fin n}{d : D}
         → ((zero := p-multi-one-h (dtoE {1} (head (env-multi-one (initialVec {n}))))(var zero) x (suc zero))
            ⊢ d ∷ [] ⇒  env-multi-one (updateE x d (initialVec {n})))
p-lemma₁ {n}{x}{d} with inspect (initialVec {n})
p-lemma₁ | it xs p with inspect (env-multi-one xs)
p-lemma₁ {n}{x}{d}| it .(tabulate (λ _ → dnil)) refl | it (a ∷ []) q = subst (λ b → (zero := p-multi-one-h (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))) (var zero) x 1)
                                                                                    ⊢ d ∷ [] ⇒ b)
                                                                             (lemma {n} {x} {d})
                                                                             (assign {v = zero} {e = p-multi-one-h (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))) (var zero) x 1} {env = d ∷ []})
         where -- the correctness of dtoE
               lemma-dtoE-ok : {n : ℕ}{x : D}{env : Vec D n} →  eval (dtoE x) env ≡ x
               lemma-dtoE-ok {x = dnil} = refl
               lemma-dtoE-ok {x = d₁ ∙ d₂}{env = env} = eval (dtoE d₁) env ∙ eval (dtoE d₂) env
                                                        =⟨ cong (λ a₁ → a₁ ∙ eval (dtoE d₂) env) (lemma-dtoE-ok {_} {d₁} {env}) ⟩
                                                        d₁ ∙ eval (dtoE d₂) env
                                                        =⟨ cong (λ a₁ → d₁ ∙ a₁) (lemma-dtoE-ok {_} {d₂} {env}) ⟩
                                                        d₁ ∙ d₂
                                                        ∎
               -- the property of dtoE
               lemma-dtoE : {n : ℕ}{env : Vec D n}{d : D} → eval (dtoE (head (env-multi-one env)))(d ∷ []) ≡ head (env-multi-one env)
               lemma-dtoE {env = []} = refl
               lemma-dtoE {env = x ∷ env}{d} = eval (dtoE x) (d ∷ []) ∙
                                               eval (dtoE (head (env-multi-one env))) (d ∷ [])
                                               =⟨ cong (λ a₁ → a₁ ∙ eval (dtoE (head (env-multi-one env))) (d ∷ []))
                                                      (lemma-dtoE-ok {_} {x} {d ∷ []}) ⟩
                                               x ∙ eval (dtoE (head (env-multi-one env))) (d ∷ [])
                                               =⟨ cong (λ a₁ → x ∙ a₁) (lemma-dtoE {_} {env} {d}) ⟩
                                               x ∙ head (env-multi-one env)
                                               ∎
               -- the property of env-multi-one
               lemma-env-one : {n : ℕ}{env : Vec D n}{d : D} → d ∷ [] ≡ env-multi-one env → d ≡ head (env-multi-one env)
               lemma-env-one {env = []} refl = refl
               lemma-env-one {env = d₁ ∷ env} refl = refl

               -- property of dsnd
               lemma-dsnd₂ : {y : ℕ}{e : E 1}{env : Vec D 1} → dsnd (eval (e-var (fromℕ y) (cons nil e)) env) ≡ eval (e-var (fromℕ y) e) env
               lemma-dsnd₂ {zero} = refl
               lemma-dsnd₂ {suc y}{e}{env} = cong dsnd (lemma-dsnd₂ {y} {e} {env})

               -- the property of eval and p-multi-one
               lemma-h : {n : ℕ}{e₁ e₂ : E 1}{x : Fin n}{y : ℕ}{d : D}
                        → eval (p-multi-one-h (cons nil e₁) e₂ x (suc y)) (d ∷ [])
                        ≡ eval (p-multi-one-h e₁ e₂ x y) (d ∷ [])
               lemma-h {e₁ = e₁}{e₂}{x = zero}{y}{d} = cong (λ a₁ → eval e₂ (d ∷ []) ∙ a₁) (lemma-dsnd₂ {y} {e₁} {d ∷ []})
               lemma-h {e₁ = e₁}{e₂}{x = suc x}{y}{d} = cong (λ a₁ → dnil ∙ a₁) (lemma-h {e₁ = e₁} {e₂} {x} {suc y} {d})

               -- the correctness of the construction
               lemma : {n : ℕ}{x : Fin n}{d : D}
                       → eval (p-multi-one-h (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))) (var zero) x 1) (d ∷ []) ∷ []
                       ≡ env-multi-one (updateE x d (tabulate (λ _ → dnil)))
               lemma {zero} {()}
               lemma {suc n}{x = zero}{d} = cong (λ a₁ → d ∙ a₁ ∷ []) (eval (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))) (d ∷ [])
                                                                      =⟨ lemma-dtoE {n} {tabulate (λ _ → dnil)} {d} ⟩
                                                                      head (env-multi-one {n} (tabulate (λ _ → dnil))) ∎)
               lemma {suc n}{x = suc x}{d} = cong (λ a → dnil ∙ a ∷ []) (eval (p-multi-one-h (cons nil (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))))
                                                                                             (var zero) x (suc 1))
                                                                              (d ∷ [])
                                                                         =⟨ lemma-h {n} {dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))} {var zero} {x} {1} {d} ⟩
                                                                         eval (p-multi-one-h (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))) (var zero) x 1)
                                                                              (d ∷ [])
                                                                         =⟨ lemma-env-one {n} {updateE x d (tabulate (λ _ → dnil))}
                                                                                          {eval (p-multi-one-h (dtoE (head (env-multi-one {n} (tabulate (λ _ → dnil))))) (var zero) x 1)
                                                                                                (d ∷ [])}
                                                                                          (lemma {n} {x} {d}) ⟩
                                                                         head (env-multi-one (updateE x d (tabulate (λ _ → dnil)))) ∎)

-- prove the correctness of the exaction
p-lemma₂ : {n : ℕ}{y : Fin n}{env : Vec D n}
         → ((zero := e-multi-one (var y)) ⊢ env-multi-one env ⇒ (dlookup y env ∷ []))
p-lemma₂ {y = y}{env = env} with inspect (env-multi-one env)
p-lemma₂ {n}{y = y}{env = env}| it (x ∷ []) p  = subst
                                                (λ a → (zero := hd (e-var y (var zero))) ⊢ env-multi-one env ⇒ a)
                                                (updateE zero (eval (hd (e-var y (var zero))) (env-multi-one env)) (env-multi-one env)
                                                =⟨ lemma₁ {n}{d = eval (hd (e-var y (var zero))) (env-multi-one env)}{env = env-multi-one env} ⟩
                                                (eval (hd (e-var y (var zero))) (env-multi-one env) ∷ [])
                                                =⟨ cong (λ a → a ∷ []) (lemma₂ {n} {y} {env}) ⟩
                                                (dlookup y env ∷ []) ∎)
                                                (assign {v = zero} {hd (e-var y (var zero))} {env-multi-one env})
         where lemma₁ : {n : ℕ}{d : D}{env : Vec D 1} → updateE zero d env ≡ d ∷ []
               lemma₁ {env = x ∷ []} = refl
               lemma-dsnd₂ : {d₁ d₂ : D}{m : ℕ}{n : Fin m} → dsnd (eval (e-var n (var zero)) (d₁ ∙ d₂ ∷ [])) ≡ eval (e-var n (var zero)) (d₂ ∷ [])
               lemma-dsnd₂ {n = zero} = refl
               lemma-dsnd₂ {n = suc n₂} = cong dsnd (lemma-dsnd₂ {n = n₂})
               lemma₂ : {n : ℕ}{y : Fin n}{env : Vec D n} → dfst (eval (e-var y (var zero)) (env-multi-one env)) ≡ dlookup y env
               lemma₂ {y = zero} {d ∷ env} = refl
               lemma₂ {y = suc y} {d ∷ env} = dfst
                                                (dsnd
                                                 (eval (e-var y (var zero)) (d ∙ head (env-multi-one env) ∷ [])))
                                                =⟨ cong dfst (lemma-dsnd₂ {d} {head (env-multi-one env)} {n = y}) ⟩
                                                dfst (eval (e-var y (var zero)) (head (env-multi-one env) ∷ []))
                                                =⟨ cong (λ a → dfst (eval (e-var y (var zero)) a)) (sym (lemma-env-multi-one {env = env})) ⟩
                                                dfst (eval (e-var y (var zero)) (env-multi-one env))
                                                =⟨ lemma₂ {y = y} {env} ⟩
                                                dlookup y env ∎

-- prove that the same program has the same command
prog-same : {n : ℕ}{c₁ c₂ : C n}{x y : Fin n} → (prog x c₁ y) ≡ (prog x c₂ y) → c₁ ≡ c₂
prog-same refl = refl

-- prove the correctness of the transformation of the program
p-multi-one-ok : {n : ℕ} → {p : P n} → {d₁ d₂ : D}
                 → ExecP p d₁ d₂
                 → ExecP (p-multi-one p) d₁ d₂
p-multi-one-ok {p = prog .x c .y} (terminate x y exec) with inspect (p-multi-one (prog x c y))
p-multi-one-ok {n} {prog .x c .y}{d₁} (terminate x y {env = env} exec) | it (prog zero c₁ zero) p = subst (λ p₁ → ExecP p₁ d₁ (dlookup y env)) (sym p)
                                                                                                          (terminate zero zero {c = c₁} {env = dlookup y env ∷ []}
                                                                                                                     (subst (λ c₂ → c₂ ⊢ d₁ ∷ [] ⇒ (dlookup y env ∷ []))
                                                                                                                            (prog-same {1}{(zero := p-multi-one-h (dtoE (head (env-multi-one {n} initialVec))) (var zero) x (suc zero))
                                                                                                                                           →→ c-multi-one c →→ (zero := hd (e-var y (var zero)))}{c₁} {zero} {zero} p)
                                                                                                                                           (seq (p-lemma₁ {x = x})(seq (c-multi-one-ok exec) (p-lemma₂ {y = y} {env = env})))))
p-multi-one-ok {n} {prog .x c .y} (terminate x y exec) | it (prog zero c₂ (suc ())) p
p-multi-one-ok {n} {prog .x c .y} (terminate x y exec) | it (prog (suc ()) c₂ b) p

-- final proof to the undecidability of the halting problem
halt-contradiction-arb : ∀ {m} {h : P m}
                   → (∀ {n : ℕ} → ∀ {p : P n} → ∀ {inp : D}
                      → (Σ D (ExecP p inp) → ExecP h (dsnd (codeP p) ∙ inp) dtrue)
                      ×' ((∀ {out : D} → ExecP p inp out → ⊥) → ExecP h (dsnd (codeP p) ∙ inp) dfalse))
                   → ⊥
halt-contradiction-arb {m} {h} p = halt-contradiction {p-multi-one {m} h}
                                   (λ {n : ℕ} {p₁ : P n} {inp : D}
                                   → (λ x → p-multi-one-ok {m} {h} {dsnd (codeP p₁) ∙ inp} {dtrue} (proj₁ (p {n} {p₁} {inp}) x))
                                   ,'(λ x → p-multi-one-ok {m} {h} {dsnd (codeP p₁) ∙ inp} {dfalse} (proj₂ (p {n} {p₁} {inp}) (λ y → x y))))
