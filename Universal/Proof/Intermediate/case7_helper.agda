module Universal.Proof.Intermediate.case7_helper where

open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

env : {Pd P C E₁ E₂ Cr St d₁ : D} → Vec D 8
env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁} = Pd ∷ P ∷ C ∷ (dcons ∙ (E₁ ∙ E₂)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []

lemma1 : {Pd P C E₁ E₂ Cr St d₁ : D} → eval ((hd (var Cd)) =? dohdE) (env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁}) ≡ dnil
lemma1 {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁})) (eval dohdE (env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁}))
lemma1 | eq ()
lemma1 | neq x = refl

lemma2 : {Pd P C E₁ E₂ Cr St d₁ : D} → eval ((hd (var Cd)) =? dotlE) (env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁}) ≡ dnil
lemma2 {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁})) (eval dotlE (env {Pd}{P}{C}{E₁}{E₂}{Cr}{St}{d₁}))
lemma2 | eq ()
lemma2 | neq x = refl
