module Haltingproblem.proof1 where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Nat.Properties.Simple
open import Data.Empty
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.proof3
open import Universal.Proof.proof5
open import Universal.Proof.proof6

-- while true loop
wt : {n : ℕ} → C n → C n
wt c = while (cons nil nil) c

-- the relationship between the program and the simulating universal command
relation :  (c : C 1) → (d₁ d₂ : D)
            → ExecP (prog zero c zero) (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) d₂
            → while (var Cd) STEP-I ⊢ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil  ∷ dnil ∷ d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) ∷ dnil ∷ dnil ∷ [])
                                    ⇒ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ [])
relation c d₁ ._ (terminate .zero .zero x) = c-h* (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) _ (codeC {1} c ∙ dnil) dnil dnil (⇒*ok c (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) _ dnil dnil (getResult x) (subst
                                                                                                                                                                                                                   (λ env →
                                                                                                                                                                                                                      c ⊢ d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) ∷ [] ⇒ env)
                                                                                                                                                                                                                   (getResult-ok x) x) (execP-c-ok c (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) _ (getResult x) (terminate zero zero x) (subst
                                                                                                                                                                                                                                                                                                                                               (λ env →
                                                                                                                                                                                                                                                                                                                                                  c ⊢ d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) ∷ [] ⇒ env)
                                                                                                                                                                                                                                                                                                                                               (getResult-ok x) x)))

-- while true command can't stop under any environment
loop-c : {t : CallTree}{n : ℕ}{c : C n}{env₁ env₂ : Vec D n} → (p : wt c ⊢ env₁ ⇒ env₂) → loop-ct p ≡ t → ⊥
loop-c (whilef ()) x₁
loop-c {leaf} (whilet x p p₁) ()
loop-c {node .(loop-ct p) .(loop-ct p₁)} (whilet x p p₁) refl = loop-c {loop-ct p₁} p₁ refl
