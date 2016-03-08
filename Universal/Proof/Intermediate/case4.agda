module Universal.Proof.Intermediate.case4 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case4 : {St T Cr d₁ C P Pd : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case4 {St} {T} {Cr} {d₁} {C} {P} {Pd} = seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilef tt)
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          (whilet {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          tt
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ dohd ∙ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ dfst T ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          assign)))
                                          (whilef tt))
                                          (whilef tt)))))
                                          (whilef tt))))))
                                          (whilef tt))))))
                                          (whilef tt))))
{-
  case4 = seq assign (seq assign (seq (whilef tt) (whilet tt (seq assign
          (seq assign (seq assign (seq (whilef tt) (whilet tt (seq assign
          (seq assign (seq assign (seq (whilef tt) (whilet tt (seq assign
          (seq assign (seq assign (seq (whilet tt (seq assign (seq assign (seq assign assign))) (whilef tt)) (whilef tt))))) (whilef tt)))))) (whilef tt)))))) (whilef tt))))
-}
