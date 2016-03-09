module Universal.Proof.Intermediate.case10 where

open import Relation.Binary.PropositionalEquality.Core
open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.Intermediate.case10_helper

abstract
  case10 : {Cr U T ST d₁ C P Pd : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                             ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ dequal T U ∙ ST ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case10 {Cr} {U} {T} {ST} {d₁} {C} {P} {Pd} = seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               (whilef tt)
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₂ = result}
                                                    {env₃ = result}
                                               (whilet {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                       {env₂ = result}
                                                       {env₃ = result}
                                               tt
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (seq {env₁ = Pd ∷ P ∷ C ∷ do=? ∙ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                               assign
                                               (subst
                                                  (λ x →
                                                     (St := cons (hd (tl (var St)) =? hd (var St)) (tl (tl (var St)))) ⊢
                                                     Pd ∷ P ∷ C ∷ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒
                                                     (Pd ∷ P ∷ C ∷ Cr ∷ x ∙ ST ∷ d₁ ∷ dnil ∷ dnil ∷ []))
                                                  (lemma {Pd}{P}{C}{Cr}{U}{T}{ST}{d₁})assign))))
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
                                               (whilef tt))))
                                               where
                                                 result : Vec D 8
                                                 result = Pd ∷ P ∷ C ∷ Cr ∷ dequal T U ∙ ST ∷ d₁ ∷ dnil ∷ dnil ∷ []
