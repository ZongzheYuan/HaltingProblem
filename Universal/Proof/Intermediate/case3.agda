module Universal.Proof.Intermediate.case3 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

abstract
  case3 : {Cr E St d₁ C P Pd : D} → STEP-I ⊢ Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒ (Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])
  case3 {Cr} {E} {St} {d₁} {C} {P} {Pd}= seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                             {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                             {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                          assign
                                          (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                               {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                               {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                            assign
                                            (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                 {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                              (whilef tt)
                                              (whilet {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                      {env₂ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                tt
                                                (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                     {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                     {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                  assign
                                                  (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                       {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                       {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                    assign
                                                    (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                         {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                         {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                      assign
                                                      (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                           {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                           {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                       (whilef tt)
                                                       (whilet {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                               {env₂ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                               {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                         tt
                                                         (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                              {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                              {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                           assign
                                                           (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                                {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                             assign
                                                             (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∙ dnil ∷ []}
                                                                  {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                                  {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                               assign
                                                               (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                                    {env₂ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                    {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                 (whilet {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                                         {env₂ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                         {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                   tt
                                                                   (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∙ dnil ∷ []}
                                                                        {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                        {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                     assign
                                                                     (seq {env₁ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∙ dnil ∷ dnil ∷ []}
                                                                          {env₂ = Pd ∷ P ∷ C ∷ (dhd ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                          {env₃ = Pd ∷ P ∷ C ∷ E ∙ (dohd ∙ Cr) ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []}
                                                                       assign
                                                                       assign))
                                                                   (whilef tt))
                                                                 (whilef tt)))))
                                                         (whilef tt))))))
                                                (whilef tt))))

{-
  case3 = seq assign (seq assign (seq (whilef tt) (whilet tt (seq assign
          (seq assign (seq assign (seq (whilef tt) (whilet tt (seq assign
          (seq assign (seq assign (seq (whilet tt (seq assign (seq assign assign)) (whilef tt)) (whilef tt))))) (whilef tt)))))) (whilef tt))))
-}
