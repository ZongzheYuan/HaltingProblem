module Universal.Proof.Intermediate.case8 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case8 : {Cr T U St d₁ C P Pd : D} →  STEP-I ⊢ Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []
                                              ⇒ (Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case8 {Cr} {T} {U} {St} {d₁} {C} {P} {Pd} = seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              tt
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              (seq {env₁ = Pd ∷ P ∷ C ∷ docons ∙ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₂ = Pd ∷ P ∷ C ∷ Cr ∷ U ∙ (T ∙ St) ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                   {env₃ = Pd ∷ P ∷ C ∷ Cr ∷ (T ∙ U) ∙ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              assign
                                              assign)))
                                              (whilef tt))
                                              (whilef tt)))))
                                              (whilef tt))))))
                                              (whilef tt))))))
                                              (whilef tt))))))
                                              (whilef tt))))))
                                              (whilef tt))))))
                                              (whilef tt))))))
                                              (whilef tt)))) 
