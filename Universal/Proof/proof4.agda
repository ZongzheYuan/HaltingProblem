module Universal.Proof.proof4 where

open import Data.Vec
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.Intermediate.case1
open import Universal.Proof.Intermediate.case2
open import Universal.Proof.Intermediate.case3
open import Universal.Proof.Intermediate.case4
open import Universal.Proof.Intermediate.case5
open import Universal.Proof.Intermediate.case6
open import Universal.Proof.Intermediate.case7
open import Universal.Proof.Intermediate.case8
open import Universal.Proof.Intermediate.case9
open import Universal.Proof.Intermediate.case10
open import Universal.Proof.Intermediate.case11
open import Universal.Proof.Intermediate.case12
open import Universal.Proof.Intermediate.case13
open import Universal.Proof.Intermediate.case14
open import Universal.Proof.Intermediate.case15
open import Universal.Proof.Intermediate.case16
open import Universal.Proof.Intermediate.case17

abstract
  -- one step corresponding from simulate program using agda to simulate program using the universal simulation command
  c-h : {Pd P C : D}(d₁ d₂ Cr₁ Cr₂ St₁ St₂ : D) 
        → < Cr₁ , St₁ , d₁ > ⇒ < Cr₂ , St₂ , d₂ >
        → STEP-I ⊢ (Pd ∷ P ∷ C ∷ Cr₁ ∷ St₁ ∷ d₁ ∷ dnil ∷ dnil ∷ [])
                 ⇒ (Pd ∷ P ∷ C ∷ Cr₂ ∷ St₂ ∷ d₂ ∷ dnil ∷ dnil ∷ [])

  c-h d₁ .d₁ .((dquote ∙ d) ∙ Cr) Cr St .(d ∙ St) (equote d .Cr .St .d₁) = case1
  c-h d₁ .d₁ .((dvar ∙ dnil) ∙ Cr) Cr St .(d₁ ∙ St) (evar1 .Cr .St .d₁) = case2
  c-h d₁ .d₁ .((dhd ∙ E) ∙ Cr) .(E ∙ (dohd ∙ Cr)) St .St (ehd E Cr .St .d₁) = case3
  c-h d₁ .d₁ .(dohd ∙ Cr) Cr .(T ∙ St) .(dfst T ∙ St) (edohd T .Cr St .d₁) = case4
  c-h d₁ .d₁ .((dtl ∙ E) ∙ Cr) .(E ∙ (dotl ∙ Cr)) St .St (etl E Cr .St .d₁) = case5
  c-h d₁ .d₁ .(dotl ∙ Cr) Cr .(T ∙ St) .(dsnd T ∙ St) (edotl T .Cr St .d₁) = case6
  c-h d₁ .d₁ .((dcons ∙ (E₁ ∙ E₂)) ∙ Cr) .(E₁ ∙ (E₂ ∙ (docons ∙ Cr))) St .St (econs E₁ E₂ Cr .St .d₁) = case7
  c-h d₁ .d₁ .(docons ∙ Cr) Cr .(U ∙ (T ∙ St)) .((T ∙ U) ∙ St) (edocons U T .Cr St .d₁) = case8
  c-h d₁ .d₁ .((d=? ∙ (E₁ ∙ E₂)) ∙ Cr) .(E₁ ∙ (E₂ ∙ (do=? ∙ Cr))) St .St (e=? E₁ E₂ Cr .St .d₁) = case9
  c-h d₁ .d₁ .(do=? ∙ Cr) Cr .(U ∙ (T ∙ St)) .(_ ∙ St) (edo=? U T .Cr St .d₁) = case10
  c-h d₁ .d₁ .((d→→ ∙ (C₁ ∙ C₂)) ∙ Cr) .(C₁ ∙ (C₂ ∙ Cr)) St .St (e→→ C₁ C₂ Cr .St .d₁) = case11
  c-h d₁ .d₁ .((d:= ∙ ((dvar ∙ dnil) ∙ E)) ∙ Cr) .(E ∙ (doasgn ∙ Cr)) St .St (e:= E Cr .St .d₁) = case12
  c-h d₁ d₂ .(doasgn ∙ Cr) Cr .(d₂ ∙ St) St (edoasgn .d₂ .Cr .St .d₁) = case13
  c-h d₁ .d₁ .((dwhile ∙ (E ∙ C₁)) ∙ Cr) .(E ∙ (dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr))) St .St (ewhile E C₁ Cr .St .d₁) = case14
  c-h d₁ .d₁ .(dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr)) Cr .(dnil ∙ St) St (edowhf E C₁ .Cr .St .d₁) = case15
  c-h d₁ .d₁ .(dowh ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr)) .(C₁ ∙ ((dwhile ∙ (E ∙ C₁)) ∙ Cr)) .((X ∙ Y) ∙ St) St (edowht E C₁ X Y Cr .St .d₁) = case16
  c-h d₁ .d₁ .dnil .dnil St .St (enil .St .d₁) = case17

