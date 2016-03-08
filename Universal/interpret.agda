module Universal.interpret where

open import Data.Nat
open import Data.Fin
open import Data.Maybe
open import Data.Product
open import While.basic
open import While.while

--ten basic key word represented in D
dquote : D
dquote = const 1

d:= : D
d:= = const 2

d→→ : D
d→→ = const 3

dwhile : D
dwhile = const 4

dvar : D
dvar =  const 5

ddnil : D
ddnil = const 6

dcons : D
dcons = const 7

dhd : D
dhd = const 8

dtl : D
dtl = const 9

d=? : D
d=? = const 10

-- code the expression to data
codeE : {n : ℕ} → E n → D
codeE (var x) = dvar ∙ dftod x
codeE nil = dquote ∙ dnil
codeE (cons e₁ e₂) = dcons ∙ (codeE e₁ ∙ codeE e₂)
codeE (hd e) = dhd ∙ codeE e
codeE (tl e) = dtl ∙ codeE e
codeE (e₁ =? e₂) = d=? ∙ (codeE e₁ ∙ codeE e₂)

-- code the command to data
codeC : {n : ℕ} → C n → D
codeC (x := e) = d:= ∙ ((dvar ∙ dftod x) ∙ codeE e)
codeC (c₁ →→ c₂) = d→→ ∙ (codeC c₁ ∙ codeC c₂)
codeC (while e c) = dwhile ∙ (codeE e ∙ codeC c)

-- code the program to data
codeP : {n : ℕ} → P n → D
codeP {n} (prog x c y) = const n ∙ ((dvar ∙ dftod x) ∙ (codeC c ∙ (dvar ∙ dftod y)))

-- view the tree D in format of D
data ViewD : D → Set where
  zero : ViewD dnil
  suc : (d : D) → ViewD d → ViewD ((dnil ∙ dnil) ∙ d)

viewD : (d : D) → Maybe (ViewD d)
viewD dnil = just zero
viewD ((dnil ∙ dnil) ∙ d) with viewD d
viewD ((dnil ∙ dnil) ∙ d) | just x = just (suc d x)
viewD ((dnil ∙ dnil) ∙ d) | nothing = nothing
viewD _ = nothing

-- translate ViewD D to ℕ
vtoℕ : {d : D} → ViewD d → ℕ
vtoℕ zero = zero
vtoℕ (suc d h) = suc (vtoℕ h)

-- view the tree D in format of var
data ViewV : ℕ → D → Set where
  vvar  : (n : ℕ) → (f : Fin n) → ViewV n (dftod f)

viewV : {n : ℕ} → (d : D) → Maybe (ViewV n d)
viewV {zero} d = nothing
viewV {suc n} dnil = just (vvar (suc n) zero)
viewV {suc n} ((dnil ∙ dnil) ∙ d) with viewV {n} d
viewV {suc .n} ((dnil ∙ dnil) ∙ .(dftod f)) | just (vvar n f) = just (vvar (suc n) (suc f))
viewV {suc n} ((dnil ∙ dnil) ∙ d) | nothing = nothing
viewV {suc n} _ = nothing

-- translate ViewV D to Fin n
vtoF : {n : ℕ} → {d : D} → ViewV n d → Fin n
vtoF (vvar n f) = f

-- view the tree D in format of expression
data ViewE : ℕ → D → Set where
  vdvar  : {n : ℕ} → (d : D) → ViewV n d → ViewE n (dvar ∙ d)
  vquote : {n : ℕ} → (d : D) → ViewE n (dquote ∙ d)
  vdcons : {n : ℕ} → (dl dr : D) → ViewE n dl → ViewE n dr → ViewE n (dcons ∙ (dl ∙ dr))
  vdhd   : {n : ℕ} → (d : D) → ViewE n d → ViewE n (dhd ∙ d)
  vdtl   : {n : ℕ} → (d : D) → ViewE n d → ViewE n (dtl ∙ d)
  vd=?   : {n : ℕ} → (dl dr : D) → ViewE n dl → ViewE n dr → ViewE n (d=? ∙ (dl ∙ dr))

viewE : {n : ℕ} → (d : D) → Maybe (ViewE n d)
viewE {zero} d = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d) with viewV {suc n} d
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d) | just v = just (vdvar d v)
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d) | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))) ∙ (d₁ ∙ d₂)) with viewE {suc n} d₁
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))) ∙ (d₁ ∙ d₂)) | just e₁ with viewE {suc n} d₂
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))) ∙ (d₁ ∙ d₂)) | just e₁ | just e₂ = just (vdcons d₁ d₂ e₁ e₂)
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))) ∙ (d₁ ∙ d₂)) | just e₁ | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))) ∙ (d₁ ∙ d₂)) | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))) ∙ d) with viewE {suc n} d
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))) ∙ d) | just e = just (vdhd d e)
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))) ∙ d) | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))))) ∙ d) with viewE {suc n} d
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))))) ∙ d) | just e = just (vdtl d e)
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))))) ∙ d) | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))) ∙ (d₁ ∙ d₂)) with viewE {suc n} d₁
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))) ∙ (d₁ ∙ d₂)) | just e₁ with viewE {suc n} d₂
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))) ∙ (d₁ ∙ d₂)) | just e₁ | just e₂ = just (vd=? d₁ d₂ e₁ e₂)
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))) ∙ (d₁ ∙ d₂)) | just e₁ | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))) ∙ (d₁ ∙ d₂)) | nothing = nothing
viewE {suc n} (((dnil ∙ dnil) ∙ dnil) ∙ d) = just (vquote d)
viewE {suc n} _ = nothing

-- view three D in format of command
data ViewC : ℕ → D → Set where
  v:= : {n : ℕ} → (d₁ d₂ : D) → ViewV n d₁ → ViewE n d₂ → ViewC n (d:= ∙ ((dvar ∙ d₁) ∙ d₂))
  v→→ : {n : ℕ} → (d₁ d₂ : D) → ViewC n d₁ → ViewC n d₂ → ViewC n (d→→ ∙ (d₁ ∙ d₂))
  vwhile : {n : ℕ} → (d₁ d₂ : D) → ViewE n d₁ → ViewC n d₂ → ViewC n (dwhile ∙ (d₁ ∙ d₂))

viewC : {n : ℕ} → (d : D) → Maybe (ViewC n d)
viewC {zero} d = nothing
viewC {suc n} dnil = nothing
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)) ∙ ((((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d₁) ∙ d₂)) with viewV {suc n} d₁
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)) ∙ ((((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d₁) ∙ d₂)) | just v with viewE {suc n} d₂
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)) ∙ ((((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d₁) ∙ d₂)) | just v | just e = just (v:= d₁ d₂ v e)
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)) ∙ ((((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d₁) ∙ d₂)) | just v | nothing = nothing
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)) ∙ ((((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))) ∙ d₁) ∙ d₂)) | nothing = nothing
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))) ∙ (d₁ ∙ d₂)) with viewC {suc n} d₁
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))) ∙ (d₁ ∙ d₂)) | just c₁ with viewC {suc n} d₂
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))) ∙ (d₁ ∙ d₂)) | just c₁ | just c₂ = just (v→→ d₁ d₂ c₁ c₂)
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))) ∙ (d₁ ∙ d₂)) | just c₁ | nothing = nothing
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))) ∙ (d₁ ∙ d₂)) | nothing = nothing
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))) ∙  (d₁ ∙ d₂)) with viewE {suc n} d₁
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))) ∙ (d₁ ∙ d₂)) | just e with viewC {suc n} d₂
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))) ∙ (d₁ ∙ d₂)) | just e | just c = just (vwhile d₁ d₂ e c)
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))) ∙ (d₁ ∙ d₂)) | just e | nothing = nothing
viewC {suc n} (((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))) ∙ (d₁ ∙ d₂)) | nothing = nothing
viewC {suc n} _ = nothing

-- decode the expression
decodeE : {n : ℕ} → D → Maybe (E n)
decodeE {n} d with viewE {n} d
decodeE .(dvar ∙ dftod f) | just (vdvar .(dftod f) (vvar n f)) = just (var f)
decodeE {n} .(dcons ∙ (dl ∙ dr)) | just (vdcons dl dr x x₁) with decodeE {n} dl
decodeE {n} .(dcons ∙ (dl ∙ dr)) | just (vdcons dl dr x₁ x₂) | just e₁ with decodeE {n} dr
decodeE .(dcons ∙ (dl ∙ dr)) | just (vdcons dl dr x₁ x₂) | just e₁ | just e₂ = just (cons e₁ e₂)
decodeE .(dcons ∙ (dl ∙ dr)) | just (vdcons dl dr x₁ x₂) | just e₁ | nothing = nothing
decodeE .(dcons ∙ (dl ∙ dr)) | just (vdcons dl dr x x₁) | nothing = nothing
decodeE {n} .(dhd ∙ d) | just (vdhd d x) with decodeE {n} d
decodeE .(dhd ∙ d) | just (vdhd d x₁) | just e = just (hd e)
decodeE .(dhd ∙ d) | just (vdhd d x) | nothing = nothing
decodeE {n} .(dtl ∙ d) | just (vdtl d x) with decodeE {n} d
decodeE .(dtl ∙ d) | just (vdtl d x₁) | just e = just (tl e)
decodeE .(dtl ∙ d) | just (vdtl d x) | nothing = nothing
decodeE {n} .(d=? ∙ (dl ∙ dr)) | just (vd=? dl dr x x₁) with decodeE {n} dl
decodeE {n} .(d=? ∙ (dl ∙ dr)) | just (vd=? dl dr x₁ x₂) | just e₁ with decodeE {n} dr
decodeE .(d=? ∙ (dl ∙ dr)) | just (vd=? dl dr x₁ x₂) | just e₁ | just e₂ = just (e₁ =? e₂)
decodeE .(d=? ∙ (dl ∙ dr)) | just (vd=? dl dr x₁ x₂) | just e₁ | nothing = nothing
decodeE .(d=? ∙ (dl ∙ dr)) | just (vd=? dl dr x x₁) | nothing = nothing
decodeE .(dquote ∙ d) | just (vquote d) = just (dtoE d)
decodeE d | nothing = nothing

-- decode the command
decodeC : {n : ℕ} → D → Maybe (C n)
decodeC {n} d with viewC {n} d
decodeC .(d:= ∙ ((dvar ∙ dftod f) ∙ d₂)) | just (v:= .(dftod f) d₂ (vvar n f) x₁) with decodeE {n} d₂
decodeC .(d:= ∙ ((dvar ∙ dftod f) ∙ d₂)) | just (v:= .(dftod f) d₂ (vvar n f) x₁) | just e = just (f := e)
decodeC .(d:= ∙ ((dvar ∙ dftod f) ∙ d₂)) | just (v:= .(dftod f) d₂ (vvar n f) x₁) | nothing = nothing
decodeC {n} .(d→→ ∙ (d₁ ∙ d₂)) | just (v→→ d₁ d₂ x x₁) with decodeC {n} d₁
decodeC {n} .(d→→ ∙ (d₁ ∙ d₂)) | just (v→→ d₁ d₂ x₁ x₂) | just c₁ with decodeC {n} d₂
decodeC .(d→→ ∙ (d₁ ∙ d₂)) | just (v→→ d₁ d₂ x₁ x₂) | just c₁ | just c₂ = just (c₁ →→ c₂)
decodeC .(d→→ ∙ (d₁ ∙ d₂)) | just (v→→ d₁ d₂ x₁ x₂) | just c₁ | nothing = nothing
decodeC .(d→→ ∙ (d₁ ∙ d₂)) | just (v→→ d₁ d₂ x x₁) | nothing = nothing
decodeC {n} .(dwhile ∙ (d₁ ∙ d₂)) | just (vwhile d₁ d₂ x x₁) with decodeE {n} d₁
decodeC {n} .(dwhile ∙ (d₁ ∙ d₂)) | just (vwhile d₁ d₂ x₁ x₂) | just e with decodeC {n} d₂
decodeC .(dwhile ∙ (d₁ ∙ d₂)) | just (vwhile d₁ d₂ x₁ x₂) | just e | just c = just (while e c)
decodeC .(dwhile ∙ (d₁ ∙ d₂)) | just (vwhile d₁ d₂ x₁ x₂) | just e | nothing = nothing
decodeC .(dwhile ∙ (d₁ ∙ d₂)) | just (vwhile d₁ d₂ x x₁) | nothing = nothing
decodeC d | nothing = nothing

-- decode the program
decodeP : D → Maybe (Σ ℕ P)
decodeP (dn ∙ (dx ∙ (dc ∙ dy))) with viewD dn
decodeP (dn ∙ (dx ∙ (dc ∙ dy))) | just n with viewE {vtoℕ n} dx
decodeP (dn ∙ (.(dvar ∙ d) ∙ (dc ∙ dy))) | just n | just (vdvar d x) with viewE {vtoℕ n} dy
decodeP (dn ∙ (.(dvar ∙ dx) ∙ (dc ∙ .(dvar ∙ dy)))) | just n | just (vdvar dx x) | just (vdvar dy y) with decodeC {vtoℕ n} dc
decodeP (dn ∙ (.(dvar ∙ dx) ∙ (dc ∙ .(dvar ∙ dy)))) | just n | just (vdvar dx x) | just (vdvar dy y) | just c = just (record { proj₁ = vtoℕ n ; proj₂ = prog (vtoF x) c (vtoF y) })
decodeP (dn ∙ (.(dvar ∙ dx) ∙ (dc ∙ .(dvar ∙ dy)))) | just n | just (vdvar dx x) | just (vdvar dy y) | nothing = nothing
decodeP (dn ∙ (.(dvar ∙ d) ∙ (dc ∙ dy))) | just n | just (vdvar d x) | _ = nothing
decodeP (dn ∙ (dx ∙ (dc ∙ dy))) | just n | _ = nothing
decodeP (dn ∙ (dx ∙ (dc ∙ dy))) | nothing = nothing
decodeP _ = nothing

-- extra 6 key words in D
dohd : D
dohd = const 11

dotl : D
dotl = const 12

docons : D
docons = const 13

doasgn : D
doasgn = const 14

dowh : D
dowh = const 15

do=? : D
do=? = const 16

-- view tree D in format of the six new key words.
data ViewDO : D → Set where
  vdohd   : ViewDO dohd
  vdotl   : ViewDO dotl
  vdocons : ViewDO docons
  vdoasgn : ViewDO doasgn
  vdowh   : ViewDO dowh
  vdo=?   : ViewDO do=?

viewDO : (d : D) → Maybe (ViewDO d)
viewDO dnil = nothing
viewDO ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))))))) = just vdohd
viewDO ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))))) = just vdotl
viewDO ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))))))))) = just vdocons
viewDO ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))))))) = just vdoasgn
viewDO ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil))))))))))))))) = just vdowh
viewDO ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ ((dnil ∙ dnil) ∙ dnil)))))))))))))))) = just vdo=?
viewDO _ = nothing
