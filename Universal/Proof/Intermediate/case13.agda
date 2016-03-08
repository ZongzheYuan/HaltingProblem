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
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilef tt)
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            (whilet {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            tt
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ doasgn ∙ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ Cr ∷ d₂ ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ d₂ ∙ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₂ ∷ dnil ∷ dnil ∷ []}
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
