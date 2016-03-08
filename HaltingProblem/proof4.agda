module Haltingproblem.proof4 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Haltingproblem.u

-- the relationship between the universal simulation command and the program U
step-U-halt : (c : C 1) → (d₁ d₂ Cr St : D)
             → while (var Cd) STEP-I ⊢ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) ∷ dnil ∷ dnil ∷ [])
                                     ⇒ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ [])
             → d₂ ≡ dnil
             → ExecP U (dsnd (codeP (prog zero c zero)) ∙ d₁) d₂
step-U-halt c d₁ d₂ Cr St (whilet x p p₁) q = terminate PD V1 (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ dnil ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq
                                                             (whilet x p p₁)
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             (subst
                                                                (λ d →
                                                                   (Z := var V1) ⊢
                                                                   ((dvar ∙ dnil) ∙ (codeC c ∙ (dvar ∙ dnil))) ∙ d₁ ∷
                                                                   (dvar ∙ dnil) ∙ (codeC c ∙ (dvar ∙ dnil)) ∷
                                                                   codeC c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []
                                                                   ⇒
                                                                   (((dvar ∙ dnil) ∙ (codeC c ∙ (dvar ∙ dnil))) ∙ d₁ ∷
                                                                    (dvar ∙ dnil) ∙ (codeC c ∙ (dvar ∙ dnil)) ∷
                                                                    codeC c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ d ∷ []))
                                                                q assign)
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             (whilef tt)
                                                             (whilet {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                     {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                                     {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             tt
                                                             (seq {env₁ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                  {env₂ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                                  {env₃ = dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             assign)
                                                             (whilef tt)))))))))))
