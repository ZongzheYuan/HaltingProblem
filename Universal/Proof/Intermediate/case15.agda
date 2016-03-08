module Universal.Proof.Intermediate.case15 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case15 : {Pd P C E C₁ Cr d₁ St : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                      ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case15 {Pd} {P} {C} {E} {C₁} {Cr} {d₁} {St} = seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr) ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ dnil ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                assign)))
                                                (whilef tt))
                                                (whilef tt)))))
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
