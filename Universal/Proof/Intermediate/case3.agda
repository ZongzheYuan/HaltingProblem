module Universal.Proof.Intermediate.case3 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case3 : {Cr E St d₁ C P Pd : D} → STEP-I ⊢ Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒ (Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case3 {Cr} {E} {St} {d₁} {C} {P} {Pd}= seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                             {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                             {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         (whilef tt)
                                         (whilet {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = result}
                                                 {env₃ = result}
                                         tt
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         (whilef tt)
                                         (whilet {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = result}
                                                 {env₃ = result}
                                         tt
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                              {env₂ = result}
                                              {env₃ = result}
                                         (whilet {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = result}
                                                 {env₃ = result}
                                         tt
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = result}
                                         assign
                                         assign))
                                         (whilef tt))
                                         (whilef tt)))))
                                         (whilef tt))))))
                                         (whilef tt))))
                                         where
                                              result : Vec D 8
                                              result = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
