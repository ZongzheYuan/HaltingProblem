module Universal.universal where

open import Data.Nat
open import Data.Fin
open import While.basic
open import While.while
open import Universal.interpret

-- new one-step relationship [Cr, St, V1] → [Cr', St', V1']
data _⇒_ : D × D × D → D × D × D → Set where
  equote  : (d Cr St V1 : D) → < (dquote ∙ d) ∙ Cr , St , V1 > ⇒ < Cr , d ∙ St , V1 >
  evar1   : (Cr St V1 : D) → < (dvar ∙ dftod {1} zero) ∙ Cr , St , V1 > ⇒ < Cr , V1 ∙ St , V1 >
  ehd     : (E Cr St V1 : D) → < (dhd ∙ E) ∙ Cr , St , V1 > ⇒ < E ∙ (dohd ∙ Cr) , St , V1 >
  edohd   : (T Cr St V1 : D) → < dohd ∙ Cr , T ∙ St , V1 > ⇒ < Cr , (dfst T) ∙ St , V1 >
  etl     : (E Cr St V1 : D) → < (dtl ∙ E) ∙ Cr , St , V1 > ⇒ < E ∙ (dotl ∙ Cr) , St , V1 >
  edotl   : (T Cr St V1 : D) → < dotl ∙ Cr , T ∙ St , V1 > ⇒ < Cr , (dsnd T) ∙ St , V1 >
  econs   : (E₁ E₂ Cr St V1 : D) → < (dcons ∙ (E₁ ∙ E₂)) ∙ Cr , St , V1 > ⇒ < E₁ ∙ (E₂ ∙ (docons ∙ Cr)) , St , V1 >
  edocons : (U T Cr St V1 : D) → < docons ∙ Cr , U ∙ (T ∙ St) , V1 > ⇒ < Cr , (T ∙ U) ∙ St , V1 >
  e=?     : (E₁ E₂ Cr St V1 : D) → < (d=? ∙ (E₁ ∙ E₂)) ∙ Cr , St , V1 > ⇒ < E₁ ∙ (E₂ ∙ (do=? ∙ Cr)) , St , V1 >
  edo=?   : (U T Cr St V1 : D) → < do=? ∙ Cr , U ∙ (T ∙ St) , V1 > ⇒ < Cr , (dequal T U) ∙ St , V1 >
  e→→     : (C₁ C₂ Cr St V1 : D) → < (d→→ ∙ (C₁ ∙ C₂)) ∙ Cr , St , V1 > ⇒ < C₁ ∙ (C₂ ∙ Cr) , St , V1 >
  e:=     : (E Cr St V1 : D) → < (d:= ∙ ((dvar ∙ dftod {1} zero) ∙ E)) ∙ Cr , St , V1 > ⇒ < E ∙ (doasgn ∙ Cr) , St , V1 >
  edoasgn : (W Cr St V1 : D) → < doasgn ∙ Cr , W ∙ St , V1 > ⇒ < Cr , St , W >
  ewhile  : (E C Cr St V1 : D) → < (dwhile ∙ (E ∙ C)) ∙ Cr , St , V1 > ⇒ < E ∙ (dowh ∙ ((dwhile ∙ (E ∙ C)) ∙ Cr)) , St , V1 >
  edowhf  : (E C Cr St V1 : D) → < dowh ∙ ((dwhile ∙ (E ∙ C)) ∙ Cr) , dnil ∙ St , V1 > ⇒ < Cr , St , V1 >
  edowht  : (E C X Y Cr St V1 : D) → < dowh ∙ ((dwhile ∙ (E ∙ C)) ∙ Cr) , (X ∙ Y) ∙ St , V1 > ⇒ <  C ∙ ((dwhile ∙ (E ∙ C)) ∙ Cr)  , St , V1 >
  enil    : (St V1 : D) → < dnil , St , V1 > ⇒ < dnil , St , V1 >

-- several step relationship
data _⇒*_ : D × D × D → D × D × D → Set where
  id   : (Cr St V1 : D) → < Cr , St , V1 > ⇒* < Cr , St , V1 >
  seq  : (Cr₁ Cr₂ Cr₃ St₁ St₂ St₃ V1₁ V1₂ V1₃ : D)
         → < Cr₁ , St₁ , V1₁ > ⇒  < Cr₂ , St₂ , V1₂ >
         → < Cr₂ , St₂ , V1₂ > ⇒* < Cr₃ , St₃ , V1₃ >
         → < Cr₁ , St₁ , V1₁ > ⇒* < Cr₃ , St₃ , V1₃ >

-- eight variable in the universal program
PD : Fin 8
PD = zero

Pp : Fin 8
Pp = suc zero

Cc : Fin 8
Cc = suc (suc (zero))

Cd : Fin 8
Cd = suc (suc (suc (zero)))

St : Fin 8
St = suc (suc (suc (suc (zero))))

V1 : Fin 8
V1 = suc (suc (suc (suc (suc (zero)))))

W : Fin 8
W = suc (suc (suc (suc (suc (suc (zero))))))

Z : Fin 8
Z = suc (suc (suc (suc (suc (suc (suc (zero)))))))

-- if command in while language
if8 : E 8 → C 8 → C 8
if8 e c = (Z := e) →→ while (var Z) ((Z := nil) →→ c)

-- if-else command in while language
if-else8 : E 8 → C 8 → C 8 → C 8
if-else8 e c₁ c₂ = (Z := e) →→
                   (W := cons nil nil) →→
                   ((while (var Z)
                           ((Z := nil) →→
                           ((W := nil) →→
                           c₁))) →→
                   (while (var W)
                          ((W := nil) →→
                          c₂)))

-- key words in expression format
quoteE : {n : ℕ} → E n
quoteE = dtoE dquote

varE : {n : ℕ} → E n
varE = dtoE dvar

valueE : {n : ℕ} → (f : Fin n) → E n
valueE f = dtoE (dftod f)

hdE : {n : ℕ} → E n
hdE = dtoE dhd

dohdE : {n : ℕ} → E n
dohdE = dtoE dohd

tlE : {n : ℕ} → E n
tlE = dtoE dtl

dotlE : {n : ℕ} → E n
dotlE = dtoE dotl

consE : {n : ℕ} → E n
consE = dtoE dcons

doconsE : {n : ℕ} → E n
doconsE = dtoE docons

=?E : {n : ℕ} → E n
=?E = dtoE d=?

do=?E : {n : ℕ} → E n
do=?E = dtoE do=?

→→E : {n : ℕ} → E n
→→E = dtoE d→→

:=E : {n : ℕ} → E n
:=E = dtoE d:=

doasgnE : {n : ℕ} → E n
doasgnE = dtoE doasgn

whileE : {n : ℕ} → E n
whileE = dtoE dwhile

dowhE : {n : ℕ} → E n
dowhE = dtoE dowh

-- the command that simulate the program
STEP-I : C 8
STEP-I =  if-else8 ((hd (hd (var Cd))) =? quoteE) ((St := (cons (tl (hd (var Cd))) (var St))) →→ (Cd := tl (var Cd)))
         (if-else8 (hd (hd (var Cd)) =? varE)     (if8 (tl (hd (var Cd)) =? valueE zero) ((Cd := tl (var Cd)) →→ (St := cons (var V1) (var St))))
         (if-else8 (hd (hd (var Cd)) =? hdE)      (Cd := cons (tl (hd (var Cd))) (cons dohdE (tl (var Cd))))
         (if-else8 (hd (var Cd) =? dohdE)         ((Cd := tl (var Cd)) →→ (St := cons (hd (hd (var St))) (tl (var St))))
         (if-else8 (hd (hd (var Cd)) =? tlE)      (Cd := cons (tl (hd (var Cd))) (cons dotlE (tl (var Cd))))
         (if-else8 (hd (var Cd) =? dotlE)         ((Cd := tl (var Cd)) →→ (St := cons (tl (hd (var St))) (tl (var St))))
         (if-else8 (hd (hd (var Cd)) =? consE)    (Cd := cons (hd (tl (hd (var Cd)))) (cons (tl (tl (hd (var Cd)))) (cons doconsE (tl (var Cd)))))
         (if-else8 (hd (var Cd) =? doconsE)       ((Cd := tl (var Cd)) →→ (St := cons (cons (hd (tl (var St))) (hd (var St))) (tl (tl (var St)))))
         (if-else8 (hd (hd (var Cd)) =? =?E)      (Cd := cons (hd (tl (hd (var Cd)))) (cons (tl (tl (hd (var Cd)))) (cons do=?E (tl (var Cd)))))
         (if-else8 (hd (var Cd) =? do=?E)         ((Cd := tl (var Cd)) →→ (St := cons ((hd (tl (var St))) =? (hd (var St))) (tl (tl (var St)))))
         (if-else8 (hd (hd (var Cd)) =? →→E)      (Cd := cons (hd (tl (hd (var Cd)))) (cons (tl (tl (hd (var Cd)))) (tl (var Cd))))
         (if-else8 (hd (hd (var Cd)) =? :=E)      (if8 ((hd (hd (tl (hd (var Cd))))) =? varE) (if8 (tl (hd (tl (hd (var Cd)))) =? valueE zero) (Cd := cons (tl (tl (hd (var Cd)))) (cons doasgnE (tl (var Cd))))))
         (if-else8 (hd (var Cd) =? doasgnE)       ((Cd := tl (var Cd)) →→ ( (V1 := hd (var St)) →→ (St := tl (var St))))
         (if-else8 (hd (hd (var Cd)) =? whileE)   (Cd := cons (hd (tl (hd (var Cd)))) (cons dowhE (cons (cons whileE (cons (hd (tl (hd (var Cd)))) (tl (tl (hd (var Cd)))))) (tl (var Cd)))))
         (if-else8 (hd (var Cd) =? dowhE)         (if8 (hd (hd (tl (var Cd))) =? whileE) (if-else8 (hd (var St) =? nil) ((Cd := tl (tl (var Cd))) →→ (St := tl (var St)))
                                                                                                                        ((Cd := cons (tl (tl (hd (tl (var Cd))))) (cons (cons whileE (cons (hd (tl (hd (tl (var Cd))))) (tl (tl (hd (tl (var Cd))))))) (tl (tl (var Cd))))) →→ (St := tl (var St)))))
         (if8      (var Cd =? nil)                (Cd := nil))))))))))))))))

{- the universal while program that could simulate the program that have one variable

read PD;             (* Input (p.d) *)
  P := hd PD;        (* P = ((var 1) C (var 1)) *)
  C := hd (tl P)     (* C = hd tl p program code is C *)
  Cd := cons C nil;  (* Cd = (c.nil), Code to execute is c *)
  St := nil;         (* St = nil, Stack empty *)
  Vl := tl PD;       (* Vl = d Initial value of var.*)
  while Cd do STEP;  (* do while there is code to execute *)
write Vl;
-}

universalI : P 8
universalI = prog PD ((Pp := hd (var PD))
                     →→
                     (Cc := hd (tl (var Pp)))
                     →→
                     (Cd := cons (var Cc) nil)
                     →→
                     (St := nil)
                     →→
                     (V1 := tl (var PD))
                     →→
                     (while (var Cd) STEP-I))
                  V1
