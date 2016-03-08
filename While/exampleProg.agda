module While.exampleProg where

open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Data.List
open import While.basic
open import While.while


{-
read X; (* X is (d.e) *)
  A := hd X; (* A is d *)
  Y := tl X; (* Y is e *)
  B := nil; (* B becomes d reversed *)
  while A do
    B := cons (hd A) B;
    A := tl A;
  while B do
    Y := cons (hd B) Y;
    B := tl B;
write Y
-}

append : P 4
append = prog zero
             ((suc (suc zero) := hd (var zero)) →→
             (suc zero := tl (var zero)) →→
             (suc (suc (suc zero)) := nil) →→
             (while
               (var (suc (suc zero)))
               ((suc (suc (suc zero)) := cons (hd (var (suc (suc zero)))) (var (suc (suc (suc zero))))) →→
               ((suc (suc zero)) := tl (var (suc (suc zero)))))) →→
             (while
               (var (suc (suc (suc zero))))
               ((suc zero := cons (hd (var (suc (suc (suc zero))))) (var (suc zero))) →→
               (suc (suc (suc zero)) := tl (var (suc (suc (suc zero))))))))
             (suc zero)
             
-- translate a list of nat to d
ltod : List ℕ → D
ltod [] = dnil
ltod (x ∷ g) = const x ∙ ltod g

list1 : D
list1 = ltod (1 ∷ 2 ∷ 3 ∷ [])

list2 : D
list2 = ltod (4 ∷ 5 ∷ 6 ∷ [])

list3 : D
list3 = ltod (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [])

runAppend : ExecP append (list1 ∙ list2) list3
runAppend = terminate zero (suc zero) {env = list1 ∙ list2 ∷ list3 ∷ dnil ∷ dnil ∷ []}
            (seq {env₁ = list1 ∙ list2 ∷ dnil ∷ dnil ∷ dnil ∷ []}
              assign
              (seq {env₁ = list1 ∙ list2 ∷ dnil ∷ list1 ∷ dnil ∷ []}
                assign
                (seq {env₁ = list1 ∙ list2 ∷ list2 ∷ list1 ∷ dnil ∷ []}
                  assign
                  (seq {env₁ = list1 ∙ list2 ∷ list2 ∷ list1 ∷ dnil ∷ []}
                       {env₂ = list1 ∙ list2 ∷ list2 ∷ dnil ∷ ltod (3 ∷ 2 ∷ 1 ∷ []) ∷ []}
                       {env₃ =  list1 ∙ list2 ∷ list3 ∷ dnil ∷ dnil ∷ []}
                    (whilet {env₁ =  list1 ∙ list2 ∷ list2 ∷ list1 ∷ dnil ∷ []}
                            {env₂ = list1 ∙ list2 ∷ list2 ∷ dsnd list1 ∷ dfst list1 ∙ dnil ∷ []}
                            {env₃ = list1 ∙ list2 ∷ list2 ∷ dnil ∷ ltod (3 ∷ 2 ∷ 1 ∷ []) ∷ []}
                      _ 
                     (seq 
                       assign
                       assign)
                     (whilet {env₁ = list1 ∙ list2 ∷ list2 ∷ dsnd list1 ∷ dfst list1 ∙ dnil ∷ []}
                             {env₂ = list1 ∙ list2 ∷ list2 ∷ dsnd (dsnd list1) ∷ dfst (dsnd list1) ∙ (dfst list1 ∙ dnil) ∷ []}
                             {env₃ = list1 ∙ list2 ∷ list2 ∷ dnil ∷ ltod (3 ∷ 2 ∷ 1 ∷ []) ∷ []}
                       _
                       (seq
                         assign
                         assign)
                       (whilet {env₁ = list1 ∙ list2 ∷ list2 ∷ dsnd (dsnd list1) ∷ dfst (dsnd list1) ∙ (dfst list1 ∙ dnil) ∷ []}
                               {env₂ = list1 ∙ list2 ∷ list2 ∷ dnil ∷ ltod (3 ∷ 2 ∷ 1 ∷ []) ∷ []}
                               {env₃ = list1 ∙ list2 ∷ list2 ∷ dnil ∷ ltod (3 ∷ 2 ∷ 1 ∷ []) ∷ []}
                         _
                         (seq
                           assign
                           assign)
                         (whilef _))))
                    (whilet {env₁ = list1 ∙ list2 ∷ list2 ∷ dnil ∷ ltod (3 ∷ 2 ∷ 1 ∷ []) ∷ []}
                            {env₂ = list1 ∙ list2 ∷ const 3 ∙ list2 ∷ dnil ∷ ltod (2 ∷ 1 ∷ []) ∷ []}
                            {env₃ = list1 ∙ list2 ∷ list3 ∷ dnil ∷ dnil ∷ []}
                      _
                      (seq
                        assign
                        assign)
                      (whilet {env₁ = list1 ∙ list2 ∷ const 3 ∙ list2 ∷ dnil ∷ ltod (2 ∷ 1 ∷ []) ∷ []}
                              {env₂ = list1 ∙ list2 ∷ const 2 ∙ (const 3 ∙ list2) ∷ dnil ∷ ltod (1 ∷ []) ∷ []}
                              {env₃ = list1 ∙ list2 ∷ list3 ∷ dnil ∷ dnil ∷ []}
                        _
                        (seq
                          assign
                          assign)
                        (whilet {env₁ = list1 ∙ list2 ∷ const 2 ∙ (const 3 ∙ list2) ∷ dnil ∷ ltod (1 ∷ []) ∷ []}
                                {env₂ = list1 ∙ list2 ∷ list3 ∷ dnil ∷ dnil ∷ []}
                                {env₃ = list1 ∙ list2 ∷ list3 ∷ dnil ∷ dnil ∷ []}
                          _
                          (seq
                            assign
                            assign)
                          (whilef _))))))))
