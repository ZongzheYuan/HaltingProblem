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

seq-assoc+ : {n : ℕ} → {env₁ env₂ : Vec D n}
            → {c₁ c₂ c₃ : C n}
            → (c₁ →→ (c₂ →→ c₃) ⊢ env₁ ⇒ env₂)
            → ((c₁ →→ c₂) →→ c₃ ⊢ env₁ ⇒ env₂)
seq-assoc+ (seq p (seq p₁ p₂)) = seq (seq p p₁) p₂

seq-assoc- : {n : ℕ} → {env₁ env₂ : Vec D n}
            → {c₁ c₂ c₃ : C n}
            → ((c₁ →→ c₂) →→ c₃ ⊢ env₁ ⇒ env₂)
            → (c₁ →→ (c₂ →→ c₃) ⊢ env₁ ⇒ env₂)
seq-assoc- (seq (seq p p₁) p₂) = seq p (seq p₁ p₂)

env-multi-one : {n : ℕ} → Vec D n → Vec D 1
env-multi-one [] = dnil ∷ []
env-multi-one (x ∷ v) = x ∙ head (env-multi-one v) ∷ []

env-one-multi : Vec D 1 → Σ ℕ (Vec D)
env-one-multi (dnil ∷ []) = zero ,' []
env-one-multi (x ∙ x₁ ∷ []) with env-one-multi (x₁ ∷ [])
env-one-multi (x ∙ x₁ ∷ []) | proj₁ ,' proj₂ = (suc proj₁) ,' (x ∷ proj₂)

env-one-n : Vec D 1 → (n : ℕ) → Maybe (Vec D n)
env-one-n (dnil ∷ []) zero = just []
env-one-n (dnil ∷ []) (suc n) = nothing
env-one-n (x ∙ x₁ ∷ []) zero = nothing
env-one-n (x ∙ x₁ ∷ []) (suc n) with env-one-n (x₁ ∷ []) n
env-one-n (x₂ ∙ x₁ ∷ []) (suc n) | just x = just (x₂ ∷ x)
env-one-n (x ∙ x₁ ∷ []) (suc n) | nothing = nothing

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

look-up-ok : {n : ℕ} → {x : Fin n} → {env : Vec D n} →
             dlookup x env ≡
             dfst (eval (e-var x (var zero)) (env-multi-one env))
look-up-ok {zero} {()}
look-up-ok {suc n}{x} = {!!}

e-multi-one-ok : {n : ℕ} → (e : E n) → {env : Vec D n}
                 → eval e env ≡ eval (e-multi-one e) (env-multi-one env)
e-multi-one-ok (var x) = {!!}
e-multi-one-ok nil = refl
e-multi-one-ok (cons e e₁) = d-cons-ok (e-multi-one-ok e) (e-multi-one-ok e₁)
e-multi-one-ok (hd e) = cong dfst (e-multi-one-ok e)
e-multi-one-ok (tl e) = cong dsnd (e-multi-one-ok e)
e-multi-one-ok (e =? e₁) {env} = {!!}

c-multi-one : {n : ℕ} → C n → C 1
c-multi-one (x := e) = zero := {!!}
c-multi-one (c →→ c₁) = c-multi-one c →→ c-multi-one c₁
c-multi-one (while x c) = while (e-multi-one x) (c-multi-one c)

c-multi-one-ok : {n : ℕ} → {c : C n} → {env₁ env₂ : Vec D n}
                 → c ⊢ env₁ ⇒ env₂
                 → c-multi-one c ⊢ (env-multi-one {n} env₁) ⇒ (env-multi-one {n} env₂)
c-multi-one-ok (whilef {e} x) = whilef (subst (λ d → isNil d) (e-multi-one-ok e) x)
c-multi-one-ok (whilet {e} x p p₁) = whilet (subst (λ d → isTree d) (e-multi-one-ok e) x) (c-multi-one-ok p) (c-multi-one-ok p₁)
c-multi-one-ok (assign {n}{e}{env}) = {!assign {zero} {}!}
c-multi-one-ok (seq p p₁) = seq (c-multi-one-ok p) (c-multi-one-ok p₁)

p-multi-one : {n : ℕ} → P n → P 1
p-multi-one (prog x c y) = prog zero (c-multi-one c) zero

p-multi-one-ok : {n : ℕ} → {p : P n} → {d₁ d₂ : D}
                 → ExecP p d₁ d₂
                 → ExecP (p-multi-one p) d₁ d₂
p-multi-one-ok (terminate x y p) = {!!}

