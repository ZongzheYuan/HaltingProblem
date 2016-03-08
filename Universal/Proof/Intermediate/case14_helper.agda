module Universal.Proof.Intermediate.case14_helper where

open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal

env : {Pd P C E C₁ Cr St d₁ : D} → Vec D 8
env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁} = Pd ∷ P ∷ C ∷ (dwhile ∙ (E ∙ C₁)) ∙ Cr ∷ St ∷ d₁ ∷ dnil ∷ dnil ∷ []

lemma1 : {Pd P C E C₁ Cr St d₁ : D} → eval ((hd (var Cd)) =? dohdE) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}) ≡ dnil
lemma1 {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁})) (eval dohdE (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}))
lemma1 | eq ()
lemma1 | neq x = refl

lemma2 : {Pd P C E C₁ Cr St d₁ : D} → eval ((hd (var Cd)) =? dotlE) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}) ≡ dnil
lemma2 {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁})) (eval dotlE (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}))
lemma2 | eq ()
lemma2 | neq x = refl

lemma3 : {Pd P C E C₁ Cr St d₁ : D} → eval ((hd (var Cd)) =? doconsE) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}) ≡ dnil
lemma3 {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁})) (eval doconsE (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}))
lemma3 | eq ()
lemma3 | neq x = refl

lemma4 : {Pd P C E C₁ Cr St d₁ : D} → eval ((hd (var Cd)) =? do=?E) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}) ≡ dnil
lemma4 {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁})) (eval do=?E (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}))
lemma4 | eq ()
lemma4 | neq x = refl

lemma5 : {Pd P C E C₁ Cr St d₁ : D} → eval ((hd (var Cd)) =? doasgnE) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}) ≡ dnil
lemma5 {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁} with equalD? (eval (hd (var Cd)) (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁})) (eval doasgnE (env {Pd}{P}{C}{E}{C₁}{Cr}{St}{d₁}))
lemma5 | eq ()
lemma5 | neq x = refl
