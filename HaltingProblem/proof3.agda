module Haltingproblem.proof3 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Haltingproblem.u
open import Haltingproblem.proof4
open import Haltingproblem.proof5
open import Universal.Proof.proof3
open import Universal.Proof.proof6

-- the property 2 of program U
-- the execution of the command in U will halt
-- if the result of the program h under the input is nil
execP-U-halt :  {h : P 1} → (d₁ d₂ : D)
             → ExecP h (d₁ ∙ (dsnd (codeP h) ∙ d₁)) d₂
             → d₂ ≡ dnil
             → ExecP U (dsnd (codeP h) ∙ d₁) d₂
execP-U-halt {(prog zero c zero)} d₁ ._ (terminate .zero .zero p) q = step-U-halt c d₁ _ dnil dnil (step-U-ok c d₁ _ (⇒*ok c (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) _ dnil dnil (getResult p) (subst
                                                                                                                                                                                                       (λ env →
                                                                                                                                                                                                          c ⊢ d₁ ∙ (((dvar ∙ dnil) ∙ (codeC c ∙ (dvar ∙ dnil))) ∙ d₁) ∷ [] ⇒
                                                                                                                                                                                                          env)
                                                                                                                                                                                                       (getResult-ok p) p) (execP-c-ok c (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) _ (getResult p) (terminate zero zero p) (subst
                                                                                                                                                                                                                                                                                                                                   (λ env →
                                                                                                                                                                                                                                                                                                                                      c ⊢ d₁ ∙ (((dvar ∙ dnil) ∙ (codeC c ∙ (dvar ∙ dnil))) ∙ d₁) ∷ [] ⇒
                                                                                                                                                                                                                                                                                                                                      env)
                                                                                                                                                                                                                                                                                                                                   (getResult-ok p) p)))) q
execP-U-halt {(prog zero x₁ (suc ()))} d₁ ._ (terminate .zero ._ x₃) x₄
execP-U-halt {(prog (suc ()) x₁ x₂)} d₁ ._ (terminate ._ .x₂ x₃) x₄


