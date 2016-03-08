module Haltingproblem.proof2 where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Empty
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Haltingproblem.u
open import Haltingproblem.proof1

-- the property 1 of program U
-- the execution of the command in U will loop forever
-- if the result of the program h under the input is not nil
execC-U-loop : {m : ℕ}{h : P 1} → (d₁ d₂ : D)
             → ExecP h (d₁ ∙ (dsnd (codeP h) ∙ d₁)) d₂
             → (d₂ ≡ dnil → ⊥)
             → ∀ {env : Vec D 8}
             → (p : (getCommandP U) ⊢ updateE PD (dsnd (codeP h) ∙ d₁) initialVec ⇒ env)
             → loop-n p ≡ m
             → ⊥
execC-U-loop {h = prog zero c zero} d₁ ._ (terminate .zero .zero x) q₁ (seq assign (seq assign (seq assign (seq assign (seq assign (seq p₇ (seq p₈ (seq p₉ (seq (whilef x₁) p₁₁))))))))) q₂ with ⊢ok p₇ (relation c d₁ _ (terminate zero zero x))
execC-U-loop {m} {prog zero c zero} d₁ ._ (terminate .zero .zero {.c}{env} x) q₁ (seq assign (seq assign (seq assign (seq assign (seq assign (seq p₇ (seq assign (seq assign (seq (whilef x₁) p₁₁))))))))) q₂ | refl with (dlookup zero env)
execC-U-loop {m} {prog zero c zero} d₁ ._ (terminate .zero .zero x) q₁ (seq assign (seq assign (seq assign (seq assign (seq assign (seq p₇ (seq assign (seq assign (seq (whilef x₁) p₁₁))))))))) q₂ | refl | dnil = q₁ refl
execC-U-loop {m} {prog zero c zero} d₁ ._ (terminate .zero .zero x) q₁ (seq assign (seq assign (seq assign (seq assign (seq assign (seq p₇ (seq assign (seq assign (seq (whilef x₁) p₁₁))))))))) q₂ | refl | h ∙ h₁ = x₁
execC-U-loop {zero} {prog zero c zero} d₁ ._ (terminate .zero .zero x) q₁ (seq p₂ (seq p₃ (seq p₄ (seq p₅ (seq p₆ (seq p₇ (seq p₈ (seq p₉ (seq (whilet x₁ p₁₀ p₁₁) p₁₂))))))))) q₂ = lemma1
                                                                                                                                                                                       (loop-n p₂ + loop-n p₃ + loop-n p₄ + loop-n p₅ + loop-n p₆ +
                                                                                                                                                                                        loop-n p₇
                                                                                                                                                                                        + loop-n p₈
                                                                                                                                                                                        + loop-n p₉)
                                                                                                                                                                                       (loop-n p₁₀ + loop-n p₁₁ + loop-n p₁₂) (subst (λ x₂ → x₂ ≡ zero) (lemma2 (loop-n p₂) (loop-n p₃) (loop-n p₄) (loop-n p₅) (loop-n p₆) (loop-n p₇) (loop-n p₈) (loop-n p₉) (loop-n p₁₀ + loop-n p₁₁ + loop-n p₁₂)) q₂)
execC-U-loop {suc m} {prog zero c zero} d₁ ._ (terminate .zero .zero x) q₁ (seq p₂ (seq p₃ (seq p₄ (seq p₅ (seq p₆ (seq p₇ (seq p₈ (seq p₉ (seq (whilet x₁ (seq p₁₀ (seq p₁₁ (whilef ()))) p₁₃) p₁₄))))))))) q₂
execC-U-loop {suc m} {prog zero c zero} d₁ ._ (terminate .zero .zero x) q₁ (seq p₂ (seq p₃ (seq p₄ (seq p₅ (seq p₆ (seq p₇ (seq p₈ (seq p₉ (seq (whilet x₁ (seq p₁₀ (seq p₁₁ p₁₂)) p₁₄) p₁₅))))))))) q₂ = loop-c p₁₂ refl
execC-U-loop {h = prog zero c (suc ())} d₁ d₂ p₁ q₁ p₂ q₂
execC-U-loop {h = prog (suc ()) x₁ x₂} d₁ d₂ p₁ q₁ p₂ q₂

-- the execution of the program U will loop forever
-- if the result of the program h under the input is not nil
execP-U-loop :  {h : P 1} → (d₁ d₂ : D)
             → ExecP h (d₁ ∙ (dsnd (codeP h) ∙ d₁)) d₂
             → (d₂ ≡ dnil → ⊥)
             → (∀ {d₃ : D} → ExecP U (dsnd (codeP h) ∙ d₁) d₃ → ⊥)
execP-U-loop d₁ d₂ p₁ q (terminate .zero .(suc (suc (suc (suc (suc zero))))) x) = execC-U-loop d₁ d₂ p₁ q x refl
