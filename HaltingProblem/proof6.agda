module Haltingproblem.proof6 where

open import Data.Empty
open import Data.Nat
open import Data.Product renaming (_,_ to _,'_; _×_ to _×'_)
open import Relation.Binary.PropositionalEquality hiding (_≢_; inspect)
open import While.basic
open import While.while
open import Universal.interpret
open import Haltingproblem.u
open import Haltingproblem.proof3
open import Haltingproblem.proof2

-- the propositional logic proof
postulate
  -- Σ D (ExecP U (dsnd (codeP h) ∙ dsnd (codeP U)))
  X : Set
  -- ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dtrue 
  Y : Set
  -- ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dfalse
  Z : Set
  -- u-halt : Σ D (ExecP U (dsnd (codeP h) ∙ dsnd (codeP U))) → ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dtrue
  xy  : X → Y
  -- u-loop : (∀ {out : D} → ExecP U (dsnd (codeP h) ∙ dsnd (codeP U)) out → ⊥) → ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dfalse
  nxz : (X → ⊥) → Z
  -- execP-U-loop
  ynx : Y → X → ⊥
  -- execP-U-halt'
  zx  : Z → X

-- exec-U-⊥
a⊥ : X → ⊥
a⊥ a = ynx (xy a) a

-- final proof
bot : ⊥
bot = a⊥ (zx (nxz a⊥))

{-
final proof
if there exists a program h that would decide the halting problem
  which means for each program p and input d, 
    the program h will return false if p loop forever on d
    the program h will return true  if p halt on d
then we feed h to our predefine program U
then if the program U run on the input of (h' ∙ U') (in which ' is the notation of the code of the program)
  which means inside U, it will simulate h run on (U' ∙ (h' ∙ U'))
    which means h is deciding U will halt on (h' ∙ U') or not
However if there exist some output d such that exec U on (h' ∙ U') will yield d which means U halt on (h' ∙ U')
  then the output of h run on (U' ∙ (h' ∙ U')) will return true by definition
    which will let U loop forever on (h' ∙ U') which causes contradiction
Otherwise if U will loop forever on (h' ∙ U')
  then the out put of h run on (U' ∙ (h' ∙ U')) will return false by definition
    which will let U halt on (h' ∙ U') immediately and case contradiction
By conclusion, the assumption that there exists a program h that would decide the halting problem is fallacy
Which means the halting problem is undecidable
QED
-}

halt-contradiction : {h : P 1}
                   → (∀ {n : ℕ} → ∀ {p : P n} → ∀ {inp : D}
                      → (Σ D (ExecP p inp) → ExecP h (dsnd (codeP p) ∙ inp) dtrue)
                      ×' ((∀ {out : D} → ExecP p inp out → ⊥) → ExecP h (dsnd (codeP p) ∙ inp) dfalse))
                   → ⊥
halt-contradiction {h} p = exec-U-⊥ (execP-U-halt' (u-loop (λ {out} q → exec-U-⊥ (out ,' q))))
  where
    prop = p {8}{U}{(dsnd (codeP h) ∙ dsnd (codeP U))}
    
    u-halt : Σ D (ExecP U (dsnd (codeP h) ∙ dsnd (codeP U))) → ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dtrue
    u-halt = proj₁ prop

    u-loop : (∀ {out : D} → ExecP U (dsnd (codeP h) ∙ dsnd (codeP U)) out → ⊥) → ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dfalse
    u-loop = proj₂ prop

    exec-U-⊥ : Σ D (ExecP U (dsnd (codeP h) ∙ dsnd (codeP U))) → ⊥
    exec-U-⊥ (d ,' p) = execP-U-loop (dsnd (codeP U)) dtrue (u-halt (d ,' p)) (λ { () }) p

    execP-U-halt' : ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dfalse → Σ D (ExecP U (dsnd (codeP h) ∙ dsnd (codeP U)))
    execP-U-halt' p = dnil ,' execP-U-halt {h} (dsnd (codeP U)) dnil p refl


{- false proof

contradiction-halt : {h : P 1} → Σ D (ExecP U (dsnd (codeP h) ∙ dsnd (codeP U))) → ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dtrue → ⊥
contradiction-halt (proj₁ ,' proj₂) q = execP-U-loop (dsnd (codeP U)) dtrue q true-false proj₂

contradiction-loop : {h : P 1} → (∀ {d : D} → ExecP U (dsnd (codeP h) ∙ dsnd (codeP U)) d → ⊥) → ExecP h (dsnd (codeP U) ∙ (dsnd (codeP h) ∙ dsnd (codeP U))) dfalse → ⊥
contradiction-loop p q = p (execP-U-halt (dsnd (codeP U)) dnil q refl)

-}
