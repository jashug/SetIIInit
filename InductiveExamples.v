Require Import HoTT.Basics HoTT.Utf8.
Require Import InductiveTypes.

(*
Here we demonstrate that InductiveTypes allows for the construction of
various inductive types internally.
*)

Local Notation "'convertible' x y" := (idpath x : x = y)
  (at level 0, x, y at next level).

(* We can handle multiple constructors: *)
Module Example_N.

Definition N_spec : OpSpec@{Set} Unit
  := op_prod (el tt) (ind_arg (single_argument tt) (el tt)).

Definition N : Type0 := Initial.sorts N_spec tt.

Definition N_ops : N * (N → N) := Initial.operations N_spec.
Definition O : N := fst N_ops.
Definition S : N → N := snd N_ops.

Section eliminator.
Universe j.
Context (P : N → Type@{j}) (ISO : P O) (ISS : ∀ n, P n → P (S n)).

Definition N_rect@{} : ∀ n, P n
  := Initial.eliminators N_spec (λ 'tt, P) (ISO, ISS) tt.

Check convertible (N_rect O) ISO.
Check λ n, convertible (N_rect (S n)) (ISS n (N_rect n)).

End eliminator.
End Example_N.

(* And infinitary arguments: *)
Module Example_W.
Section W.
Universe i.
Context (A : Type@{i}) (B : A → Type@{i}).

Definition W_spec@{} : OpSpec@{i} Unit
  := nonind_arg A (λ a,
     ind_arg (infinitary_argument (B a) (λ b, tt))
     (el@{i} tt)).

Definition W@{} : Type@{i} := Initial.sorts W_spec tt.

Definition sup@{} : ∀ a, (B a → W) → W := Initial.operations W_spec.

Section eliminator.
Universe j.
Context (P : W → Type@{j}) (IS : ∀ a f, (∀ b, P (f b)) → P (sup a f)).

Definition W_rect@{} : ∀ x, P x
  := Initial.eliminators@{i j} W_spec (λ 'tt, P) IS tt.

Check λ a f, convertible (W_rect (sup a f)) (IS a f (λ b, W_rect (f b))).
End eliminator.
End W.
End Example_W.