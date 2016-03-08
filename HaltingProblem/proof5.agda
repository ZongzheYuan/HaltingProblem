module Haltingproblem.proof5 where

open import Data.Fin
open import Data.Vec
open import While.while
open import While.basic
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.proof5

-- the many steps relationship between the simulation of the command and the universal simulation command
step-U-ok : (c : C 1) → (d₁ d₂ : D) 
            → < codeC c ∙ dnil , dnil , d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) > ⇒* < dnil , dnil , d₂ >
            → while (var Cd) STEP-I ⊢ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil  ∷ dnil ∷ d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁) ∷ dnil ∷ dnil ∷ [])
                                    ⇒ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ [])
step-U-ok c d₁ d₂ p = c-h* (d₁ ∙ (dsnd (codeP (prog zero c zero)) ∙ d₁)) d₂ (codeC c ∙ dnil) dnil dnil p

