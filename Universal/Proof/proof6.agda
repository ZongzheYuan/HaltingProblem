module Universal.Proof.proof6 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.proof3
open import Universal.Proof.proof5

-- the completeness of the exec program and command
execP-c-ok : (c : C 1) → (d₁ d₂ : D) → (out : Vec D 1)
                 → ExecP (prog zero c zero) d₁ d₂
                 → c ⊢ updateE zero d₁ initialVec ⇒ out
                 → dlookup zero out ≡ d₂
execP-c-ok c d₁ ._ out (terminate .zero .zero x) q with ⊢ok x q
execP-c-ok c d₁ .(dlookup zero env) env (terminate .zero .zero x) q | refl = refl

-- the relation of the universal command and the universal program
step-I-uni : (c : C 1) → (d₁ d₂ Cr St : D)
             → while (var Cd) STEP-I ⊢ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil ∷ dnil ∷ d₁ ∷ dnil ∷ dnil ∷ [])
                                     ⇒ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ [])
             → ExecP universalI (dsnd (codeP ((prog zero c zero))) ∙ d₁) d₂
step-I-uni c d₁ d₂ Cr St (whilet _ p₁ p₂) = terminate PD V1 (seq assign (seq assign (seq assign (seq assign (seq assign (whilet tt p₁ p₂))))))

-- ∀ p : P 1, exec p inp out
--            exec universal (p' ∙ inp) out
execP-uni :  (c : C 1) → (d₁ d₂ : D)
             → ExecP (prog zero c zero) d₁ d₂
             → ExecP universalI (dsnd (codeP ((prog zero c zero))) ∙ d₁) d₂
execP-uni c d₁ ._ (terminate .zero .zero x) = step-I-uni c d₁ _ dnil dnil (step-I-ok c d₁ _ (⇒*ok c d₁ _ dnil dnil (getResult x) (subst (λ env → c ⊢ d₁ ∷ [] ⇒ env) (getResult-ok x) x) (execP-c-ok c d₁ _ (getResult x) (terminate zero zero x) (subst (λ env → c ⊢ d₁ ∷ [] ⇒ env) (getResult-ok x) x))))
