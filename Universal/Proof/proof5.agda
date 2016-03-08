module Universal.Proof.proof5 where

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import Data.Product renaming (_,_ to _,'_; _×_ to _×'_)
open import While.basic
open import While.while
open import Universal.interpret
open import Universal.universal
open import Universal.Proof.proof4

-- proof the base case of the ⇒* relation
⇒*base : {d₁ d₂ St₁ St₂ : D}  → < dnil , St₁ , d₁ > ⇒* < dnil , St₂ , d₂ > → (St₁ ≡ St₂) ×' (d₁ ≡ d₂)
⇒*base (id .dnil St V1) = refl ,' refl
⇒*base (seq .dnil .dnil .dnil St₁ .St₁ St₃ V1₁ .V1₁ V1₃ (enil .St₁ .V1₁) p) = ⇒*base p

-- convert the tuple of equality to the equality of tuple
convert,' : ∀{A B : Set}{a a' : A}{b b' : B} → (a ≡ a') ×' (b ≡ b') → (a ,' b) ≡ (a' ,' b')
convert,' (refl ,' refl) = refl

-- many steps corresponding from simulate program using agda to simulate program using the universal simulation command
c-h* : {Pd P C : D}(d₁ d₂ Cr St₁ St₂ : D) 
       → < Cr , St₁ , d₁ > ⇒* < dnil , St₂ , d₂ >
       → while (var Cd) STEP-I ⊢ (Pd ∷ P ∷ C ∷ Cr ∷ St₁ ∷ d₁ ∷ dnil ∷ dnil ∷ [])
                               ⇒ (Pd ∷ P ∷ C ∷ dnil ∷ St₂ ∷ d₂ ∷ dnil ∷ dnil ∷ [])
c-h* d₁ .d₁ .dnil St .St (id .dnil .St .d₁) = whilef tt
c-h* d₁ d₂ dnil St₁ St₃ (seq .dnil .dnil .dnil .St₁ .St₁ .St₃ .d₁ .d₁ .d₂ (enil .St₁ .d₁) p)
     = subst (λ { (St ,' d) → while (var Cd) STEP-I ⊢ _ ∷ _ ∷ _ ∷ dnil ∷ St₁ ∷ d₁ ∷ dnil ∷ dnil ∷ [] ⇒ (_ ∷ _ ∷ _ ∷ dnil ∷ St ∷ d ∷ dnil ∷ dnil ∷ []) })
                (convert,' (⇒*base p))
                (whilef tt)
c-h* d₁ d₂ (Cr₁ ∙ Cr₂) St₁ St₃ (seq .(Cr₁ ∙ Cr₂) Cr₃ .dnil .St₁ St₂ .St₃ .d₁ V1₂ .d₂ x p) = whilet tt (c-h d₁ V1₂ (Cr₁ ∙ Cr₂) Cr₃ St₁ St₂ x)
                                                                                                      (c-h* V1₂ d₂ Cr₃ St₂ St₃ p)

-- many steps corresponding from simulate program using agda to simulate program using the universal program
step-I-ok : (c : C 1) → (d₁ d₂ : D) 
            → < codeC c ∙ dnil , dnil , d₁ > ⇒* < dnil , dnil , d₂ >
            → while (var Cd) STEP-I ⊢ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ codeC {1} c ∙ dnil  ∷ dnil ∷ d₁ ∷ dnil ∷ dnil ∷ [])
                                    ⇒ (dsnd (codeP (prog zero c zero)) ∙ d₁ ∷ dsnd (codeP (prog zero c zero)) ∷ codeC {1} c ∷ dnil ∷ dnil ∷ d₂ ∷ dnil ∷ dnil ∷ [])
step-I-ok c d₁ d₂ p = c-h* d₁ d₂ (codeC c ∙ dnil) dnil dnil p


