module Universal.Proof.Intermediate.case5_helper where

open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

env : {Pd P C E Cr St d₁ : D} → Vec D 8
env {Pd}{P}{C}{E}{Cr}{St}{d₁} = (Pd ∷ P ∷ C ∷ (dtl ∙ E) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ [])

lemma : {Pd P C E Cr St d₁ : D} → eval ((hd (var Cd)) =? dohdE) (env {Pd}{P}{C}{E}{Cr}{St}{d₁}) ≡ dnil
lemma {Pd}{P}{C}{E}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E}{Cr}{St}{d₁})) (eval dohdE (env {Pd}{P}{C}{E}{Cr}{St}{d₁}))
lemma | eq ()
lemma | neq x = refl
