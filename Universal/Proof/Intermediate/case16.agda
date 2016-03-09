module Universal.Proof.Intermediate.case16 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case16 : {Pd P C E C₁ Cr X Y d₁ St : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                                ⇒ (Pd ∷ P ∷ C ∷ C₁ ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case16 {Pd} {P} {C} {E} {C₁} {Cr} {X} {Y} {d₁} {St} = seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                            {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₂ = result}
                                                             {env₃ = result}
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (whilet
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        (whilef tt)
                                                        (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                {env₂ = result}
                                                                {env₃ = result}
                                                        tt
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₂ = Pd ∷ P ∷ C ∷ C₁ ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ (X ∙ Y) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             {env₃ = result}
                                                        assign
                                                        assign))
                                                        (whilef tt))))))
                                                        (whilef tt)))))
                                                        (whilef tt))
                                                        (whilef tt)))))
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
                                                          result = Pd ∷ P ∷ C ∷ C₁ ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
