module Universal.Proof.proof1 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.universal

abstract
  -- transitivity of the ⇒* relation
  ⇒*-m : (Cr₁ Cr₂ Cr₃ St₁ St₂ St₃ V1₁ V1₂ V1₃ : D)
              → < Cr₁ , St₁ , V1₁ > ⇒* < Cr₂ , St₂ , V1₂ >
              → < Cr₂ , St₂ , V1₂ > ⇒* < Cr₃ , St₃ , V1₃ >
              → < Cr₁ , St₁ , V1₁ > ⇒* < Cr₃ , St₃ , V1₃ >
  ⇒*-m Cr₁ .Cr₁ Cr₃ St₁ .St₁ St₃ V1₁ .V1₁ V1₃ (id .Cr₁ .St₁ .V1₁) q = q
  ⇒*-m Cr₁ Cr₂ Cr₃ St₁ St₂ St₃ V1₁ V1₂ V1₃ (seq .Cr₁ Cr₄ .Cr₂ .St₁ St₄ .St₂ .V1₁ V1₄ .V1₂ x p) q = seq Cr₁ Cr₄ Cr₃
                                                                                                       St₁ St₄ St₃
                                                                                                       V1₁ V1₄ V1₃
                                                                                                       x
                                                                                                       (⇒*-m Cr₄ Cr₂ Cr₃
                                                                                                             St₄ St₂ St₃
                                                                                                             V1₄ V1₂ V1₃
                                                                                                             p
                                                                                                             q)
  
abstract
  ⇒*-b : (Cr₁ Cr₂ Cr₃ St₁ St₂ St₃ V1₁ V1₂ V1₃ : D)
              → < Cr₁ , St₁ , V1₁ > ⇒* < Cr₂ , St₂ , V1₂ >
              → < Cr₂ , St₂ , V1₂ > ⇒  < Cr₃ , St₃ , V1₃ >
              → < Cr₁ , St₁ , V1₁ > ⇒* < Cr₃ , St₃ , V1₃ >
  ⇒*-b Cr₁ .Cr₁ Cr₃ St₁ .St₁ St₃ V1₁ .V1₁ V1₃ (id .Cr₁ .St₁ .V1₁) x = seq Cr₁ Cr₃ Cr₃
                                                                          St₁ St₃ St₃
                                                                          V1₁ V1₃ V1₃
                                                                          x
                                                                          (id Cr₃ St₃ V1₃)
  ⇒*-b Cr₁ Cr₂ Cr₃ St₁ St₂ St₃ V1₁ V1₂ V1₃ (seq .Cr₁ Cr₄ .Cr₂ .St₁ St₄ .St₂ .V1₁ V1₄ .V1₂ x p) x₁ = seq Cr₁ Cr₄ Cr₃
                                                                                                        St₁ St₄ St₃
                                                                                                        V1₁ V1₄ V1₃
                                                                                                        x
                                                                                                        (⇒*-b Cr₄ Cr₂ Cr₃
                                                                                                              St₄ St₂ St₃
                                                                                                              V1₄ V1₂ V1₃
                                                                                                              p
                                                                                                              x₁)
abstract
  -- property of the environment that have only one variable       
  one-ok : {env : Vec D 1} → env ≡ (dlookup zero env ∷ [])
  one-ok {x ∷ []} = refl
