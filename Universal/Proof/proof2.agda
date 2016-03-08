module Universal.Proof.proof2 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.proof1

-- relationship with execution an expression
-- [(E.Cd), St, d] ⇒* [Cd, (e.St), d] iff eval [E][X ↦ d] = e
⇒*e : (e : E 1) → (d₁ d₂ Cr St : D)
       → eval e (updateE zero d₁ initialVec) ≡ d₂
       → < codeE e ∙ Cr , St , d₁ > ⇒* < Cr , d₂ ∙ St , d₁ >
⇒*e (var zero) d₁ .d₁ Cr St refl = seq (codeE (var {1} zero) ∙ Cr) Cr        Cr
                                                St                   (d₁ ∙ St) (d₁ ∙ St)
                                                d₁                   d₁        d₁
                                                (evar1 Cr St d₁)
                                                (id Cr (d₁ ∙ St) d₁)
⇒*e (var (suc ())) d₁ d₂ Cr St equality 
⇒*e nil d₁ .dnil Cr St refl = seq ((dquote ∙ dnil) ∙ Cr) Cr          Cr
                                    St                     (dnil ∙ St) (dnil ∙ St)
                                    d₁                     d₁          d₁
                                    (equote dnil Cr St d₁)
                                    (id Cr (dnil ∙ St) d₁)
⇒*e (cons e₁ e₂) d₁ .(eval e₁ (d₁ ∷ []) ∙ eval e₂ (d₁ ∷ [])) Cr St refl = seq (codeE (cons e₁ e₂) ∙ Cr) (codeE e₁ ∙ (codeE e₂ ∙ (docons ∙ Cr))) Cr
                                                                               St                        St                                      ((eval e₁ (d₁ ∷ []) ∙ eval e₂ (d₁ ∷ [])) ∙ St)
                                                                               d₁                        d₁                                      d₁
                                                                               (econs (codeE e₁) (codeE e₂) Cr St d₁)
                                                                               (⇒*-b (codeE e₁ ∙ (codeE e₂ ∙ (docons ∙ Cr))) (docons ∙ Cr)                                  Cr
                                                                                     St                                      (eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St)) ((eval e₁ (d₁ ∷ []) ∙ eval e₂ (d₁ ∷ [])) ∙ St)
                                                                                     d₁                                      d₁                                             d₁
                                                                                     (⇒*-m (codeE e₁ ∙ (codeE e₂ ∙ (docons ∙ Cr))) (codeE e₂ ∙ (docons ∙ Cr)) (docons ∙ Cr)
                                                                                           St                                      (eval e₁ (d₁ ∷ []) ∙ St)   (eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St))
                                                                                           d₁                                      d₁                         d₁
                                                                                           (⇒*e e₁ d₁ (eval e₁ (d₁ ∷ [])) (codeE e₂ ∙ (docons ∙ Cr)) St refl)
                                                                                           (⇒*e e₂ d₁ (eval e₂ (d₁ ∷ [])) (docons ∙ Cr) (eval e₁ (d₁ ∷ []) ∙ St) refl))
                                                                                     (edocons (eval e₂ (d₁ ∷ [])) (eval e₁ (d₁ ∷ [])) Cr St d₁))
⇒*e (hd e) d₁ .(dfst (eval e (d₁ ∷ []))) Cr St refl = seq (codeE (hd e) ∙ Cr) (codeE e ∙ (dohd ∙ Cr)) Cr
                                                            St                  St                      (dfst (eval e (d₁ ∷ [])) ∙ St)
                                                            d₁                  d₁                      d₁
                                                            (ehd (codeE e) Cr St d₁)
                                                            (⇒*-b (codeE e ∙ (dohd ∙ Cr)) (dohd ∙ Cr)             Cr
                                                                  St                      (eval e (d₁ ∷ []) ∙ St) (dfst (eval e (d₁ ∷ [])) ∙ St)
                                                                  d₁                      d₁                      d₁
                                                                  (⇒*e e d₁ (eval e (d₁ ∷ [])) (dohd ∙ Cr) St refl)
                                                                  (edohd (eval e (d₁ ∷ [])) Cr St d₁))
⇒*e (tl e) d₁ .(dsnd (eval e (d₁ ∷ []))) Cr St refl = seq (codeE (tl e) ∙ Cr) (codeE e ∙ (dotl ∙ Cr)) Cr
                                                            St                  St                      (dsnd (eval e (d₁ ∷ [])) ∙ St)
                                                            d₁                  d₁                      d₁
                                                            (etl (codeE e) Cr St d₁)
                                                            (⇒*-b (codeE e ∙ (dotl ∙ Cr)) (dotl ∙ Cr)             Cr
                                                                  St                      (eval e (d₁ ∷ []) ∙ St) (dsnd (eval e (d₁ ∷ [])) ∙ St)
                                                                  d₁                      d₁                      d₁
                                                                  (⇒*e e d₁ (eval e (d₁ ∷ [])) (dotl ∙ Cr) St refl)
                                                                  (edotl (eval e (d₁ ∷ [])) Cr St d₁))
⇒*e (e₁ =? e₂) d₁ d₂ Cr St equality with equalD? (eval (e₁) (updateE zero d₁ initialVec)) (eval (e₂) (updateE zero d₁ initialVec))
⇒*e (e₁ =? e₂) d₁ .dtrue Cr St refl | eq x = seq (codeE (e₁ =? e₂) ∙ Cr) (codeE e₁ ∙ (codeE e₂ ∙ (do=? ∙ Cr))) Cr
                                                  St                      St                                    (dtrue ∙ St)
                                                  d₁                      d₁                                    d₁
                                                  (e=? (codeE e₁) (codeE e₂) Cr St d₁)
                                                  (⇒*-b (codeE e₁ ∙ (codeE e₂ ∙ (do=? ∙ Cr))) (do=? ∙ Cr)                                    Cr
                                                        St                                    (eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St)) (dtrue ∙ St)
                                                        d₁                                    d₁                                             d₁
                                                        (⇒*-m (codeE e₁ ∙ (codeE e₂ ∙ (do=? ∙ Cr))) (codeE e₂ ∙ (do=? ∙ Cr)) (do=? ∙ Cr)
                                                              St                                    (eval e₁ (d₁ ∷ []) ∙ St) (eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St))
                                                              d₁                                    d₁                       d₁
                                                              (⇒*e e₁ d₁ (eval e₁ (d₁ ∷ [])) (codeE e₂ ∙ (do=? ∙ Cr)) St refl)
                                                              (⇒*e e₂ d₁ (eval e₂ (d₁ ∷ [])) (do=? ∙ Cr) (eval e₁ (d₁ ∷ []) ∙ St) refl))
                                                              (subst (λ x → < do=? ∙ Cr , eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St) , d₁ > ⇒ x) aux (edo=? (eval e₂ (d₁ ∷ []))  (eval e₁ (d₁ ∷ [])) Cr St d₁)))
                                                              where aux = < Cr , dequal (eval e₁ (d₁ ∷ [])) (eval e₂ (d₁ ∷ [])) ∙ St , d₁ >
                                                                            =⟨ general-ap (λ e → < Cr , dequal e (eval e₂ (d₁ ∷ [])) ∙ St , d₁ >) x ⟩
                                                                          < Cr , dequal (eval e₂ (d₁ ∷ [])) (eval e₂ (d₁ ∷ [])) ∙ St , d₁ >
                                                                            =⟨ general-ap (λ e → < Cr , e ∙ St , d₁ >) (dequal-true _ _ refl)  ⟩
                                                                          < Cr , dtrue ∙ St , d₁ >
                                                                             ∎                                                                                                                       
⇒*e (e₁ =? e₂) d₁ .dfalse Cr St refl | neq x = seq (codeE (e₁ =? e₂) ∙ Cr) (codeE e₁ ∙ (codeE e₂ ∙ (do=? ∙ Cr))) Cr
                                                    St                      St                                    (dfalse ∙ St)
                                                    d₁                      d₁                                    d₁
                                                    (e=? (codeE e₁) (codeE e₂) Cr St d₁)
                                                    (⇒*-b (codeE e₁ ∙ (codeE e₂ ∙ (do=? ∙ Cr))) (do=? ∙ Cr)                                    Cr
                                                          St                                    (eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St)) (dfalse ∙ St)
                                                          d₁                                    d₁                                             d₁
                                                          (⇒*-m (codeE e₁ ∙ (codeE e₂ ∙ (do=? ∙ Cr))) (codeE e₂ ∙ (do=? ∙ Cr)) (do=? ∙ Cr)
                                                                St                                    (eval e₁ (d₁ ∷ []) ∙ St) (eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St))
                                                                d₁                                    d₁                       d₁
                                                                (⇒*e e₁ d₁ (eval e₁ (d₁ ∷ [])) (codeE e₂ ∙ (do=? ∙ Cr)) St refl)
                                                                (⇒*e e₂ d₁ (eval e₂ (d₁ ∷ [])) (do=? ∙ Cr) (eval e₁ (d₁ ∷ []) ∙ St) refl))
                                                          (subst (λ x₁ → < do=? ∙ Cr , eval e₂ (d₁ ∷ []) ∙ (eval e₁ (d₁ ∷ []) ∙ St) , d₁ > ⇒ x₁) aux (edo=? (eval e₂ (d₁ ∷ [])) (eval e₁ (d₁ ∷ [])) Cr St d₁)))
                                                          where aux = < Cr , dequal (eval e₁ (d₁ ∷ [])) (eval e₂ (d₁ ∷ [])) ∙ St , d₁ >
                                                                      =⟨ general-ap (λ e → < Cr , e ∙ St , d₁ >) (dequal-false _ _ x) ⟩
                                                                      < Cr , dfalse ∙ St , d₁ >
                                                                      ∎
                        
