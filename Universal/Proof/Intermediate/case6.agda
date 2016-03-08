module Universal.Proof.Intermediate.case6 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case6 : {St T Cr d₁ C P Pd : D} → STEP-I ⊢ Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case6 {St} {T} {Cr} {d₁} {C} {P} {Pd} = seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dotl ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dsnd T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          assign)))
                                          (whilef tt))
                                          (whilef tt)))))
                                          (whilef tt))))))
                                          (whilef tt))))))
                                          (whilef tt))))))
                                          (whilef tt))))))
                                          (whilef tt))))
