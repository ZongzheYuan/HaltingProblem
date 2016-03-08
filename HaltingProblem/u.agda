module Haltingproblem.u where

open import While.while
open import Universal.universal

{-
U : P 8
U = prog PD ((Pp := hd (var PD))
            →→
            (Cc := hd (tl (var Pp)))
            →→
            (Cd := cons (var Cc) nil)
            →→
            (St := nil)
            →→
            (V1 := cons (tl (var PD)) (cons  (var Pp) (tl (var PD))))
            →→
            (while (var Cd) STEP-I)
            →→
            (Z := var V1) →→
            (W := cons nil nil) →→
            ((while (var Z)
                    ((Z := nil) →→
                    ((W := nil) →→
                    (while (cons nil nil) (V1 := var V1))))) →→
            (while (var W)
                   ((W := nil) →→
                   (V1 := var V1))))
            )
          V1
-}

-- the program, constructing to proof the contradiction of the halting problem
U : P 8
U = prog PD ((Pp := hd (var PD))
            →→
            (Cc := hd (tl (var Pp)))
            →→
            (Cd := cons (var Cc) nil)
            →→
            (St := nil)
            →→
            (V1 := cons (tl (var PD)) (cons  (var Pp) (tl (var PD))))
            →→
            (while (var Cd) STEP-I)
            →→
            if-else8 (var V1) (while (cons nil nil) (V1 := var V1)) (V1 := var V1)
            )
          V1

