module Universal.Proof.Intermediate.case9 where

open import Relation.Binary.PropositionalEquality.Core
open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.Intermediate.case9_helper

abstract
  case9 : {Cr E₁ E₂ St d₁ C P Pd : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                              ⇒(Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case9 {Cr} {E₁} {E₂} {St} {d₁} {C} {P} {Pd} = seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}                                                   
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}                                                   
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}                                                   
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (subst
                                                   (λ x →
                                                      (Z := (hd (var Cd) =? dohdE)) ⊢
                                                      Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒
                                                      (Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ x ∷ []))
                                                   (lemma1 {Pd} {P} {C} {E₁} {E₂} {Cr} {St} {d₁}) assign)
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (subst
                                                   (λ x →
                                                      (Z := (hd (var Cd) =? dotlE)) ⊢
                                                      Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒
                                                      (Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ x ∷ []))
                                                   (lemma2 {Pd} {P} {C} {E₁} {E₂} {Cr} {St} {d₁}) assign)
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (subst
                                                   (λ x →
                                                      (Z := (hd (var Cd) =? doconsE)) ⊢
                                                      Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒
                                                      (Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ x ∷ []))
                                                   (lemma3 {Pd} {P} {C} {E₁} {E₂} {Cr} {St} {d₁}) assign)
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilef tt)
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                (whilet {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                        {env₂ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                        {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (d=? ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                assign
                                                assign))
                                                (whilef tt))
                                                (whilef tt)))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))))
                                                (whilef tt))))
