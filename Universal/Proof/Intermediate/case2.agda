module Universal.Proof.Intermediate.case2 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case2 : {St Cr d₁ C P Pd : D} → STEP-I ⊢ Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ d₁ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case2 {St} {Cr} {d₁} {C} {P} {Pd}= seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                         {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                         {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     (whilef tt)
                                     (whilet {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                             {env₂ = result}
                                             {env₃ = result}
                                     tt
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₂ = result}
                                          {env₃ = result}
                                     (whilet {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                             {env₂ = result}
                                             {env₃ = result}
                                     tt
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (whilet {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                             {env₂ = result}
                                             {env₃ = result}
                                             tt
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dvar ∙ dnil) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          {env₃ = result}
                                     assign
                                     assign))
                                     (whilef tt)))))
                                     (whilef tt))
                                     (whilef tt)))))
                                     (whilef tt))))
                                     where
                                          result : Vec D 8
                                          result = Pd ∷ P ∷ C ∷ Cr ∷ d₁ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []


        
