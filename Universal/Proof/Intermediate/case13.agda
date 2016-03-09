module Universal.Proof.Intermediate.case13 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case13 : {Pd P C Cr d₁ d₂ St : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                               ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ [])
  case13 {Pd} {P} {C} {Cr} {d₁} {d₂} {St} = seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = result}
                                                 {env₃ = result}
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ d₂ ∙ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = result}
                                            assign
                                            assign))))
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
                                            (whilef tt))))
                                            where
                                              result : Vec D 8
                                              result = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []
