module Universal.Proof.proof3 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.proof1
open import Universal.Proof.proof2

-- relationship with execution on command
-- c ⊢ env₁ ⇒ env2
-- Cr
-- St
-- V1
-- [c ∙ Cr, St, V1] → [Cr, St, out]
-- [(C.Cd), St, d] ⇒* [Cd, St, e] iff C ⊢ [X ↦ d] → [X ↦ e]

⇒*proof : {t : D} → (c : C 1) → (d₁ d₂ Cr St : D) → (out : Vec D 1)
       → (p : c ⊢ updateE zero d₁ initialVec ⇒ out)
       → dlookup zero out ≡ d₂
       → loop-ct p ≡ t
       → < codeC c ∙ Cr , St , d₁ > ⇒* < Cr , St , d₂ >
⇒*proof (zero := e) d₁ .(eval e (d₁ ∷ [])) Cr St .(eval e (d₁ ∷ []) ∷ []) assign refl r = ⇒*-b (codeC (zero := e) ∙ Cr) (doasgn ∙ Cr)                                   Cr
                                                                                          St                       ((dlookup zero ((eval e (d₁ ∷ []) ∷ []))) ∙ St) St
                                                                                          d₁                       d₁                                              (dlookup zero (eval e (d₁ ∷ []) ∷ []))
                                                                                          (seq (codeC (zero := e) ∙ Cr) (codeE e ∙ (doasgn ∙ Cr)) (doasgn ∙ Cr)
                                                                                                St                       St                        ((dlookup zero (eval e (d₁ ∷ []) ∷ [])) ∙ St)
                                                                                                d₁                       d₁                        d₁
                                                                                                (e:= (codeE e) Cr St d₁)
                                                                                                (⇒*e e d₁ (dlookup zero (eval e (d₁ ∷ []) ∷ [])) (doasgn ∙ Cr) St refl))
                                                                                          (edoasgn (dlookup zero (eval e (d₁ ∷ []) ∷ [])) Cr St d₁)
⇒*proof (suc () := x₁) d₁ d₂ Cr St out p q r
⇒*proof (c₁ →→ c₂) d₁ .(dlookup zero out) Cr St out (seq cr₁ cr₂) refl r = seq (codeC (c₁ →→ c₂) ∙ Cr) (codeC c₁ ∙ (codeC c₂ ∙ Cr)) Cr
                                                                           St                      St                           St
                                                                           d₁                      d₁                           (dlookup zero out)
                                                                           (e→→ (codeC c₁) (codeC c₂) Cr St d₁)
                                                                           (⇒*-m (codeC c₁ ∙ (codeC c₂ ∙ Cr)) (codeC c₂ ∙ Cr)                           Cr
                                                                                 St                           St                                        St
                                                                                 d₁                           (dlookup zero (getInterim (seq cr₁ cr₂))) (dlookup zero out)
                                                                                 (⇒*proof c₁ d₁ (dlookup zero (getInterim (seq cr₁ cr₂))) (codeC c₂ ∙ Cr) St (getInterim (seq cr₁ cr₂)) cr₁ refl refl)
                                                                                 (⇒*proof c₂ (dlookup zero (getInterim (seq cr₁ cr₂))) (dlookup zero out) Cr St out (subst (λ x₁ → c₂ ⊢ x₁ ⇒ out) one-ok cr₂) refl refl))
⇒*proof (while e c) d₁ .d₁ Cr St .(d₁ ∷ []) (whilef x) refl r = seq (codeC (while e c) ∙ Cr) (codeE e ∙ (dowh ∙ (codeC (while e c) ∙ Cr))) Cr
                                                                St                       St                                            St
                                                                d₁                       d₁                                            d₁
                                                                (ewhile (codeE e) (codeC c) Cr St d₁)
                                                                (⇒*-b (codeE e ∙ (dowh ∙ (codeC (while e c) ∙ Cr))) (dowh ∙ (codeC (while e c) ∙ Cr)) Cr
                                                                      St                                            (dfalse ∙ St)                     St
                                                                      d₁                                            d₁                                d₁
                                                                      (⇒*e e d₁ dnil (dowh ∙ (codeC (while e c) ∙ Cr)) St (isNil-ok (eval e (d₁ ∷ [])) x))
                                                                      (edowhf (codeE e) (codeC c) Cr St d₁))

⇒*proof {dnil} (while e c) d₁ .(dlookup zero out) Cr St out (whilet x cr₁ cr₂) refl ()
⇒*proof {.(loop-ct cr₁) ∙ .(loop-ct cr₂)} (while e c) d₁ .(dlookup zero out) Cr St out (whilet x cr₁ cr₂) refl refl = seq (codeC (while e c) ∙ Cr) (codeE e ∙ (dowh ∙ (codeC (while e c) ∙ Cr))) Cr
                                                                                 St                       St                                            St
                                                                                 d₁                       d₁                                            (dlookup zero out)
                                                                                 (ewhile (codeE e) (codeC c) Cr St d₁)
                                                                                 (⇒*-m (codeE e ∙ (dowh ∙ (codeC (while e c) ∙ Cr))) (dowh ∙ (codeC (while e c) ∙ Cr)) Cr
                                                                                       St                                            ((f ∙ l) ∙ St)                    St
                                                                                       d₁                                            d₁                                (dlookup zero out)
                                                                                       (⇒*e e d₁ (_ ∙ _) (dowh ∙ (codeC (while e c) ∙ Cr)) St (splitD-ok (eval e (d₁ ∷ [])) (isTree-ok (eval e (d₁ ∷ [])) x)))                                                                              
                                                                                       (seq (dowh ∙ (codeC (while e c) ∙ Cr)) (codeC c ∙ (codeC (while e c) ∙ Cr)) Cr
                                                                                             ((_ ∙ _) ∙ St)                      St                                   St
                                                                                             d₁                                d₁                                   (dlookup zero out)
                                                                                             (edowht (codeE e) (codeC c) _ _ Cr St d₁)
                                                                                             (⇒*-m (codeC c ∙ (codeC (while e c) ∙ Cr)) (codeC (while e c) ∙ Cr)                       Cr
                                                                                                   St                                   St                                             St
                                                                                                   d₁                                   (dlookup zero (getInterim (whilet x cr₁ cr₂))) (dlookup zero out)
                                                                                                   (⇒*proof {(loop-ct cr₁)} c d₁ (dlookup zero (getInterim (whilet x cr₁ cr₂))) (codeC (while e c) ∙ Cr) St (getInterim (whilet x cr₁ cr₂)) cr₁ refl refl)
                                                                                                   (⇒*proof {(loop-ct cr₂)} (while e c) (dlookup zero (getInterim (whilet x cr₁ cr₂))) (dlookup zero out) Cr St out (subst (λ x₁ → while e c ⊢ x₁ ⇒ out) one-ok cr₂) refl (lemma one-ok)))))
                                                                                                   where tuple = splitD (eval e (d₁ ∷ [])) (isTree-ok (eval e (d₁ ∷ [])) x)
                                                                                                         f = fst tuple
                                                                                                         l = snd tuple
                                                                                                         
                                                                                                         lemma : ∀{a b d}(p : a ≡ b) → loop-ct (subst (λ x₁ → while e c ⊢ x₁ ⇒ out) p d) ≡ loop-ct d
                                                                                                         lemma refl = refl


⇒*ok : (c : C 1) → (d₁ d₂ Cr St : D) → (out : Vec D 1)
       → c ⊢ updateE zero d₁ initialVec ⇒ out
       → dlookup zero out ≡ d₂
       → < codeC c ∙ Cr , St , d₁ > ⇒* < Cr , St , d₂ >
⇒*ok c d₁ d₂ Cr St out p q = ⇒*proof {loop-ct p} c d₁ d₂ Cr St out p q refl
