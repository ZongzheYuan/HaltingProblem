module Universal.Proof.Intermediate.case10_helper where

open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

env : {Pd P C Cr U T ST d₁ : D} → Vec D 8
env {Pd}{P}{C}{Cr}{U}{T}{ST}{d₁} = Pd ∷ P ∷ C ∷ Cr ∷ U ∙ (T ∙ ST) ∷ d₁ ∷ dnil ∷ dnil ∷ []

lemma : {Pd P C Cr U T ST d₁ : D} → eval (hd (tl (var St)) =? hd (var St)) (env {Pd}{P}{C}{Cr}{U}{T}{ST}{d₁}) ≡ dequal T U
lemma {Pd}{P}{C}{Cr}{U}{T}{ST}{d₁} with equalD? (eval (hd (tl (var St))) (env {Pd}{P}{C}{Cr}{U}{T}{ST}{d₁})) (eval (hd (var St)) (env {Pd}{P}{C}{Cr}{U}{T}{ST}{d₁}))
lemma | eq x = refl
lemma | neq x = refl
