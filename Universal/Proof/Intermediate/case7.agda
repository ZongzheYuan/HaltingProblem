module Universal.Proof.Intermediate.case7 where

open import Relation.Binary.PropositionalEquality.Core
open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.Intermediate.case7_helper

abstract
  case7 : {Cr E₁ E₂ St d₁ C P Pd : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                                ⇒ (Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (docons ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case7 {Cr} {E₁} {E₂} {St} {d₁} {C} {P} {Pd} = seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (subst
                                                   (λ x →
                                                      (Z := (hd (var Cd) =? dohdE)) ⊢
                                                      Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                                      ⇒
                                                      (Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ x ∷ []))
                                                   (lemma1 {Pd} {P} {C} {E₁} {E₂} {Cr} {St} {d₁}) assign)
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (subst
                                                   (λ x →
                                                      (Z := (hd (var Cd) =? dotlE)) ⊢
                                                      Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                                      ⇒
                                                      (Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ x ∷ []))
                                                   (lemma2 {Pd} {P} {C} {E₁} {E₂} {Cr} {St} {d₁}) assign)
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil  ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil  ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = result}
                                                     {env₃ = result}
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                        {env₂ = result}
                                                        {env₃ = result}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = result}
                                                assign
                                                assign))
                                                (whilef tt))
                                                (whilef tt)))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))
                                                where
                                                  result : Vec D 8
                                                  result = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (docons ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
