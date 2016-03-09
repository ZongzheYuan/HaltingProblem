module Universal.Proof.Intermediate.case17 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case17 : {Pd P C d₁ St : D} →   STEP-I ⊢ Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                         ⇒ (Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case17 {Pd} {P} {C} {d₁} {St} = seq {env₁ = result}
                                      {env₂ = result}
                                      {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₃ = result}
                                  (whilef tt)
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  (seq {env₁ = result}
                                       {env₂ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                       {env₃ = result}
                                  assign
                                  (whilet {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                  tt
                                  (seq {env₁ = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                       {env₂ = result}
                                       {env₃ = result}
                                  assign
                                  assign)
                                  (whilef tt))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))))
                                  (whilef tt))))
                                  where
                                    result : Vec D 8
                                    result = Pd ∷ P ∷ C ∷ dnil ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
