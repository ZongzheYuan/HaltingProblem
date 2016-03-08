module While.kStep where

open import Data.Nat
open import Data.Vec
open import Data.Maybe
open import While.basic
open import While.while

-- result command with some output environment in t times
record ResultCT {n : ℕ}(c : C n)(inp : Vec D n) : Set where
  field
    out : Vec D n
    exe : c ⊢ inp ⇒ out
    time : ℕ

-- result program with some output data D
record ResultP {n : ℕ}(p : P n)(inp : D) : Set where
  field
    out : D
    exe : ExecP p inp out

-- substraction on nat
_sub_ : ℕ → ℕ → Maybe ℕ
zero sub zero = just zero
zero sub suc n = nothing
suc m sub zero = just (suc m)
suc m sub suc n = m sub n

-- run command in k steps
{-# NO_TERMINATION_CHECK #-}
kStepC : {n : ℕ} → (time : ℕ) → (c : C n) → (inp : Vec D n) → (Maybe (ResultCT c inp))
kStepC zero c inp = nothing
kStepC (suc time) (v := e) inp = just (record {out = updateE v (eval e inp) inp; exe = assign; time = 1})
kStepC (suc time) (c₁ →→ c₂) inp with kStepC (suc time) c₁ inp
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ with (suc time) sub (ResultCT.time res₁)
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ | just n₁ with kStepC n₁ c₂ (ResultCT.out res₁)
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ | just n₁ | just res₂ with n₁ sub (ResultCT.time res₂)
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ | just n₁ | just res₂ | just n₂ = just (record {out = ResultCT.out res₂ ; exe = seq (ResultCT.exe res₁) (ResultCT.exe res₂) ; time = n₁ Data.Nat.+ n₂ })
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ | just n₁ | just res₂ | nothing = nothing
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ | just n₁ | nothing = nothing
kStepC (suc time) (c₁ →→ c₂) inp | just res₁ | nothing = nothing
kStepC (suc time) (c₁ →→ c₂) inp | nothing = nothing
kStepC (suc time) (while e c) inp with inspect (eval e inp)
kStepC (suc time) (while e c) inp | it dnil p = just (record { out = inp ; exe = whilef (nilIsnil p) ; time = 1 })
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p with kStepC (suc time) c inp
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ with (suc time) sub (ResultCT.time res₁)
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ | just n₁ with kStepC n₁ (while e c) (ResultCT.out res₁)
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ | just n₁ | just res₂ with n₁ sub (ResultCT.time res₂)
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ | just n₁ | just res₂ | just n₂ = just (record {out = ResultCT.out res₂ ; exe = whilet (treeIstree p) (ResultCT.exe res₁) (ResultCT.exe res₂) ; time = n₁ Data.Nat.+ n₂ })
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ | just n₁ | just res₂ | nothing = nothing
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ | just n₁ | nothing = nothing
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | just res₁ | nothing = nothing
kStepC (suc time) (while e c) inp | it (d₁ ∙ d₂) p | nothing = nothing

-- run program in k steps
kStepP : {n : ℕ} → (time : ℕ) → (p : P n) → (inp : D) → (Maybe (ResultP p inp))
kStepP time (prog x c y) inp with kStepC time c (updateE x inp initialVec)
kStepP time (prog x c y) inp | just rc = just (record {out = dlookup y (ResultCT.out rc) ; exe = terminate x y (ResultCT.exe rc)})
kStepP time (prog x c y) inp | nothing = nothing
