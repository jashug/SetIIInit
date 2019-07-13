Require Import HoTT.Basics Coq.Unicode.Utf8.
Require Import HoTT.Types.Sum.
Require Import InductiveTypes.

(* Define semantics *)

Record Ctx@{i} : Type@{i+1} := {
  indices0 : Type@{i};
  indices1 : (indices0 → Type@{i}) → indices0 → Type@{i};
  (* indices_pr_10 : ∀ {Sorts0}, indices1 Sorts0 → indices0; *)
  operations0 : ∀ {indices0' : Type@{i}} (indices0_inc : indices0 → indices0'),
                OpSpec@{i} indices0;
  operations1 : ∀ {indices0' indices1' : Type@{i}} {Sorts0'},
    ∀ (indices0_inc : indices0 → indices0') (Sorts0 := Sorts0' o indices0_inc),
    Operations@{i} Sorts0' (operations0 indices0_inc) →
    (∀ (i0 : indices0) (i1 : indices1 Sorts0 i0), Sorts0 i0 → indices1') →
    OpSpec@{i} indices1';
  indices2 : ∀ {indices0' : Type@{i}} (indices0_inc : indices0 → indices0'),
    ∀ (Sorts0' : indices0' → Type@{i})
      (Sorts0 := Sorts0' o indices0_inc),
    Operations@{i} Sorts0' (operations0 indices0_inc) →
    (∀ (i0 : indices0) (i1 : indices1 Sorts0 i0), Sorts0 i0 → Type@{i}) →
    ∀ (i0 : indices0), indices1 Sorts0 i0 → Type@{i};
(*   indices_pr_21 : ∀ {indices0' indices0_inc Sorts0' Ops0 Sorts1},
                  @indices2 indices0' indices0_inc Sorts0' Ops0 Sorts1 →
                  indices1 (Sorts0' o indices0_inc); *)
(*   indices_pr_20 : ∀ {indices0' indices0_inc Sorts0' Ops0 Sorts1},
                  @indices2 indices0' indices0_inc Sorts0' Ops0 Sorts1 →
                  indices0
    := λ indices0' indices0_inc Sorts0' Ops0 Sorts1,
       indices_pr_10 o
       @indices_pr_21 indices0' indices0_inc Sorts0' Ops0 Sorts1; *)
  Indices : Type@{i} :=
    let pre_sorts := Initial.sorts (operations0 idmap) in
    let pre_ops := Initial.operations (operations0 idmap) in
    let good_sorts i0 i1 p := Initial.sorts
      (operations1 idmap pre_ops (λ i0 i1 p, (i0; (i1, p))))
      (i0; (i1, p)) in
    {i0 : indices0 &
    {i1 : indices1 pre_sorts i0 &
          indices2 idmap pre_sorts pre_ops good_sorts i0 i1
    }};
}.

Record TyOp@{i} (Γ : Ctx@{i}) : Type@{i+1} := {
  ops0 : ∀ {indices0' : Type@{i}} (indices0_inc : Γ.(indices0) → indices0'),
         OpSpec@{i} indices0';
  ops1 : ∀ {indices0' indices1' : Type@{i}} {Sorts0'},
    ∀ (indices0_inc : Γ.(indices0) → indices0')
      (Sorts0 := Sorts0' o indices0_inc)
      (indices1_inc : ∀ (i0 : Γ.(indices0)),
       Γ.(indices1) Sorts0 i0 → Sorts0 i0 → indices1'),
    Operations@{i} Sorts0' (ops0 indices0_inc) →
    Operations@{i} Sorts0' (Γ.(operations0) indices0_inc) →
    OpSpec@{i} indices1';
}.
Arguments ops0 {Γ} _ {indices0'} indices0_inc.
Arguments ops1 {Γ} _ {indices0' indices1' Sorts0'}
               indices0_inc indices1_inc ops0 Γ_ops0.

(* For now, ignore infinitary arguments/indices *)
Definition Data (Γ : Ctx) := Indices Γ.

Definition data_to_op {Γ : Ctx} (A : Data Γ) : TyOp Γ
  := {|
        ops0 _ ix0_inc := el (ix0_inc A.1);
        ops1 _ _ Sorts0' ix0_inc ix1_inc pt Γops := el (ix1_inc A.1 (* A.2.1 *)_ pt);
     |}.


(* Record IndSpec@{i} : Type@{i+1} := {
  Ix : Type@{i};
  opspec : ∀ {Ix' : Type@{i}}, (Ix → Ix') → OpSpec@{i} Ix';
}.
(* We include a delayed substitution, is this a good idea?
OpSpec is a functor, we expect there to be an object ops such that:
  opspec f = OpSpec f ops
Doing it this way may be more efficient?
*)
Definition IndOpSpec@{i} (S : IndSpec@{i}) : Type@{i+1}
  := ∀ (Ix' : Type@{i}), (S.(Ix) → Ix') → OpSpec@{i} Ix'.

Record IndAlg@{i} (S : IndSpec@{i}) : Type@{i+1} := {
  Ix' : Type@{i};
  Ix_inj : S.(Ix) → Ix';
  Sorts : Ix' → Type@{i}; (* Should this be Ix → Type instead? *)
  ops : Operations@{i} Sorts (S.(opspec) Ix_inj);
}.
Arguments Ix' {S} _.
Arguments Ix_inj {S} _ _.
Arguments Sorts {S} _ _.
Arguments ops {S} _.

Definition IndOpAlg@{i} {S : IndSpec@{i}} (O : IndOpSpec@{i} S)
  (A : IndAlg@{i} S) : Type@{i}
  := Operations@{i} A.(Sorts) (O _ A.(Ix_inj)).

Definition initial_alg@{i} (S : IndSpec@{i}) : IndAlg@{i} S
  := {|
        Ix_inj := idmap;
        Sorts := Initial.sorts (S.(opspec) idmap);
        ops := Initial.operations (S.(opspec) idmap);
     |}.
Arguments initial_alg S, {S}.

(* IndAlg (S + I) ≅ IndAlg S * (I → Type) *)
Definition add_sort (S : IndSpec@{i}) (I : Type@{i}) : IndSpec@{i}
  := {|
        Ix := S.(Ix) + I;
        opspec Ix' Ix_inj := S.(opspec) (Ix_inj o inl);
     |}.
Definition add_sort_pr1 {S I} (A : IndAlg (add_sort@{i} S I)) : IndAlg@{i} S
  := {|
        Ix_inj := A.(Ix_inj) o inl;
        Sorts := A.(Sorts);
        ops := A.(ops);
     |}.
Definition add_sort_pr2 {S I} (A : IndAlg (add_sort@{i} S I)) : I → Type@{i}
  := A.(Sorts) o A.(Ix_inj) o inr.

(* IndAlg (S + O) ≅ { A : IndAlg S & = IndOpAlg O A } *)
Definition add_op (S : IndSpec@{i}) (O : IndOpSpec@{i} S) : IndSpec@{i}
  := {|
        Ix := S.(Ix);
        opspec Ix' Ix_inj := op_prod (S.(opspec) Ix_inj) (O _ Ix_inj);
     |}.
Definition add_op_pr1 {S O} (A : IndAlg (add_op@{i} S O)) : IndAlg@{i} S
  := Build_IndAlg S _ A.(Ix_inj) A.(Sorts) (fst A.(ops)).
Definition add_op_pr2 {S O} (A : IndAlg (add_op@{i} S O))
  : IndOpAlg O (add_op_pr1 A)
  := snd A.(ops). *)


(* Record TySort@{i} (Γ : Ctx) : Type@{i+1} := {
  pre_ix : Type@{i};
  good_ix : IndAlg@{i} Γ.(pre_ind) → (pre_ix → Type@{i}) → Type@{i};
  sorts_ix : ∀ pre, IndAlg@{i} (Γ.(good_ind) pre) → Type@{i};
  (* Also projections sorts → good, good → pre *)
}.
Arguments pre_ix {Γ} _.
Arguments good_ix {Γ} _ _.
Arguments sorts_ix {Γ} _ _ _.

Record TyOp@{i} (Γ : Ctx) : Type@{i+1} := {
  pre_op : IndOpSpec@{i} Γ.(pre_ind);
  good_op : ∀ pre, IndOpAlg pre_op pre → IndOpSpec@{i} (Γ.(good_ind) pre);
}.
Arguments pre_op {Γ} _ [Ix'] Ix_inj.
Arguments good_op {Γ} _ pre _ [Ix'] Ix_inj.

(* For now, ignore infinitary arguments/indices *)
Definition Data (Γ : Ctx) := Indices Γ.

(* Definition data_to_op {Γ : Ctx} (A : Data Γ) : TyOp Γ
  := {|
        pre_op _ Ix_inc := el (Ix_inc _);
        good_op := _;
     |}. *)

Definition ext_sort (Γ : Ctx) (A : TySort Γ) : Ctx
  := {|
        pre_ind := add_sort Γ.(pre_ind) A.(pre_ix);
        good_ind pre' :=
          let pre := add_sort_pr1 pre' in
          let A_sorts := add_sort_pr2 pre' in
          add_sort (Γ.(good_ind) pre) (A.(good_ix) pre A_sorts);
        IISorts pre' good' :=
          let pre := add_sort_pr1 pre' in
          let good := add_sort_pr1 good' in
          Γ.(IISorts) pre good + A.(sorts_ix) pre good;
     |}.

Definition ext_op (Γ : Ctx) (A : TyOp Γ) : Ctx
  := {|
        pre_ind := add_op Γ.(pre_ind) A.(pre_op);
        good_ind pre' :=
          let pre := add_op_pr1 pre' in
          let A_ops := add_op_pr2 pre' in
          add_op (Γ.(good_ind) pre) (A.(good_op) pre A_ops);
        IISorts pre' good' :=
          Γ.(IISorts) (add_op_pr1 pre') (add_op_pr1 good');
     |}.

Definition u {Γ : Ctx} : TySort Γ
  := {|
        pre_ix := Unit;
        good_ix pre X := X tt; (* Index goodness by pre-syntax *)
        sorts_ix _ _ := Unit;
     |}.

(* Definition ind_ix {Γ : Ctx} (A : Data Γ) (B : TySort (ext_data Γ A)) : TySort Γ
  := _. *)
 *)