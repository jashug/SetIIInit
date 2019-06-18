Require Import HoTT.

(* Test use of HoTT definitions *)
Definition test1 : IsEquiv idmap
  := isequiv_idmap nat.
