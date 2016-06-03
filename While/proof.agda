module While.proof where

open import Data.Nat
open import Data.Fin
open import Data.Empty
open import Data.Maybe
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import Data.Product renaming (_,_ to _,'_; _×_ to _×'_)
open import While.basic
open import While.while
open import Universal.interpret
open import Haltingproblem.u
open import Haltingproblem.proof6

env-multi-one : {n : ℕ} → Vec D n → Vec D 1
env-multi-one [] = dnil ∷ []
env-multi-one (x ∷ v) = x ∙ head (env-multi-one v) ∷ []

e-var : {n : ℕ} → Fin n → E 1 → E 1
e-var zero e = e
e-var (suc n₁) e = tl (e-var n₁ e)

e-multi-one : {n : ℕ} → E n → E 1
e-multi-one (var x) = hd (e-var x (var zero))
e-multi-one nil = nil
e-multi-one (cons e e₁) = cons (e-multi-one e) (e-multi-one e₁)
e-multi-one (hd e) = hd (e-multi-one e)
e-multi-one (tl e) = tl (e-multi-one e)
e-multi-one (e =? e₁) = (e-multi-one e) =? (e-multi-one e₁)

d-cons-ok : {d₁ d₂ d₃ d₄ : D}
            → d₁ ≡ d₃
            → d₂ ≡ d₄
            → d₁ ∙ d₂ ≡ d₃ ∙ d₄
d-cons-ok refl refl = refl

lemma-e : {n : ℕ} → {x : Fin n} → {env : Vec D n}
        → dlookup x env ≡ dfst (eval (e-var x (var zero)) (env-multi-one env))
lemma-e {x = zero} {d ∷ env} = refl
lemma-e {x = suc x} {d ∷ env} with inspect (env-multi-one env)
lemma-e {._} {suc x₁} {d₁ ∷ env} | it (x ∷ []) p = dlookup x₁ env
                                                   =⟨ lemma-e {_} {x₁} {env} ⟩
                                                   dfst (eval (e-var x₁ (var zero)) (env-multi-one env))
                                                   =⟨ cong (λ v → dfst (eval (e-var x₁ (var zero)) v)) p ⟩
                                                   dfst (eval (e-var x₁ (var zero)) (x ∷ []))
                                                   =⟨ cong dfst (sym (lemma-e₂ {_} {x₁} {x} {d₁})) ⟩
                                                   dfst (eval (e-var x₁ (tl (var zero))) (d₁ ∙ x ∷ []))
                                                   =⟨ cong dfst (sym (lemma-e₁ {_} {x₁} {d₁ ∙ x ∷ []})) ⟩
                                                   dfst (dsnd (eval (e-var x₁ (var zero)) (d₁ ∙ x ∷ [])))
                                                   =⟨ sym
                                                        (cong
                                                         (λ v → dfst (dsnd (eval (e-var x₁ (var zero)) (d₁ ∙ head v ∷ []))))
                                                         p) ⟩
                                                   dfst
                                                     (dsnd
                                                      (eval (e-var x₁ (var zero)) (d₁ ∙ head (env-multi-one env) ∷ [])))
                                                     ∎                                                 
  where lemma-e₁ : {n : ℕ} → {x : Fin n} → {env : Vec D 1} →
                   dsnd (eval (e-var x (var zero)) env) ≡ eval (e-var x (tl (var zero))) env
        lemma-e₁ {x = zero} = refl
        lemma-e₁ {x = suc x₁} = cong dsnd (lemma-e₁ {x = x₁})
        
        lemma-e₂ : {n : ℕ} → {x : Fin n} → {d y : D} →
                   eval (e-var x (tl (var zero))) (y ∙ d ∷ []) ≡ eval (e-var x (var zero)) (d ∷ [])
        lemma-e₂ {x = zero} = refl
        lemma-e₂ {x = suc x₁} = cong dsnd (lemma-e₂ {x = x₁})

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

c-var : {n : ℕ} → Fin n → ℕ → E 1 → E 1
c-var zero y e = cons e (e-var (fromℕ (suc y)) (var zero))
c-var (suc x) y e = cons (hd (e-var (fromℕ y) (var zero))) (c-var x (suc y) e)

c-multi-one : {n : ℕ} → C n → C 1
c-multi-one (x := e) = zero := c-var x zero (e-multi-one e)
c-multi-one (c →→ c₁) = c-multi-one c →→ c-multi-one c₁
c-multi-one (while x c) = while (e-multi-one x) (c-multi-one c)

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
  where lemma-c : {x : ℕ}{y : Fin x}{e : E x}{env : Vec D x}
              → env-multi-one (updateE y (eval e env) env) ≡ updateE zero
                                                                     (eval (c-var y zero (e-multi-one e)) (env-multi-one env))
                                                                     (env-multi-one env)
        lemma-c {y = zero}{e}{env = x ∷ env₁} = cong (λ a → a ∙ head (env-multi-one env₁) ∷ [])
                                                  (e-multi-one-ok e {x ∷ env₁})
        lemma-c {y = suc z}{e}{env = x ∷ env₁} = cong (λ a → x ∙ a ∷ []) {!!}

        -- the same proof as the above one, just do a little abstract
        lemma-var : {x : ℕ}{y : Fin x}{e : E x}{env : Vec D x} →
                    head (env-multi-one (updateE y (eval e env) env))
                    ≡ eval (c-var y zero (e-multi-one e)) (env-multi-one env)
        lemma-var {y = zero}{e}{env = x ∷ env₁} = cong (λ a → a ∙ head (env-multi-one env₁))
                                                    (e-multi-one-ok e {x ∷ env₁})
        lemma-var {y = suc y}{e}{env = x ∷ env₁} = cong (λ a → x ∙ a) {!!}

        lemma-env₁ : {x : ℕ}{env : Vec D x}{d : D} → updateE zero d (env-multi-one env) ≡ d ∷ []
        lemma-env₁ {env = env}{d} with inspect (env-multi-one env)
        lemma-env₁ {env = env}{d}| it (x ∷ []) p = updateE zero d (env-multi-one env)
                                                  =⟨ cong (λ x₁ → updateE zero d x₁) p ⟩
                                                  updateE zero d (x ∷ [])
                                                  =⟨ refl ⟩
                                                  (d ∷ []) ∎
        
c-multi-one-ok (seq p p₁) = seq (c-multi-one-ok p) (c-multi-one-ok p₁)

p-multi-one : {n : ℕ} → P n → P 1
p-multi-one {n} (prog x c y) with env-multi-one {n} (initialVec {n})
p-multi-one {n} (prog x c y) | d ∷ [] = prog zero ((zero := c-var x zero (dtoE {1} d))
                                                  →→ c-multi-one c
                                                  →→ (zero := e-multi-one (var y)))
                                             zero

p-multi-one-ok : {n : ℕ} → {p : P n} → {d₁ d₂ : D}
                 → ExecP p d₁ d₂
                 → ExecP (p-multi-one p) d₁ d₂
p-multi-one-ok (terminate x y c) = {!!}



halt-contradiction-arb : {m : ℕ} {h : P m}
                   → (∀ {n : ℕ} → ∀ {p : P n} → ∀ {inp : D}
                      → (Σ D (ExecP p inp) → ExecP h (dsnd (codeP p) ∙ inp) dtrue)
                      ×' ((∀ {out : D} → ExecP p inp out → ⊥) → ExecP h (dsnd (codeP p) ∙ inp) dfalse))
                   → ⊥
halt-contradiction-arb {m} {h} p = halt-contradiction {p-multi-one {m} h} (λ {n : ℕ} {p₁ : P n} {inp : D}
                                   → (λ x → p-multi-one-ok {m} {h} {dsnd (codeP p₁) ∙ inp} {dtrue}  (proj₁ (p {n} {p₁} {inp}) x))
                                   ,'(λ x → p-multi-one-ok {m} {h} {dsnd (codeP p₁) ∙ inp} {dfalse} (proj₂ (p {n} {p₁} {inp}) (λ y → x y))))

