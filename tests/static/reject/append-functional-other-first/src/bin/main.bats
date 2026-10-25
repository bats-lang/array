#include "share/atspre_staload.hats"
#use array as A

(* The lemma is about one first and one second: two appends of different firsts need not agree. *)
implement main0 () = let
  prval one = $A.APPEND_nil{$A.ccons(1, $A.cnil())}()
  prval two = $A.APPEND_cons{1}($A.APPEND_nil{$A.cnil()}())
  prval _ = $A.append_functional(one, two)
in () end
