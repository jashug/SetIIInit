Require Import HoTT.Basics HoTT.Utf8.
Require InductiveTypes.
Require Import ForsbergSemantics.

Module TyCon_Example.

(* We will use the below II definition as our example:
Ty : Set
Con : Ty → Set
emp : Con
ext : ∀ (Γ : Con), Ty Γ → Con
u : ∀ (Γ : Con), Ty Γ
pi : ∀ (Γ : Con) (A : Ty Γ), Ty (ext Γ A) → Ty Γ

Note that it includes the use of ext in pi.

The construction of the specification is still quite messy, see below at
Section test_TyCon_spec for the results.
*)

Arguments ind_ix {Γ} & A B.
Arguments ind_arg {Γ} & A B.
Arguments el {Γ} & i.
Arguments inc {Γ} & i.
Arguments exist A P & _ _.

(* Notation for contexts *)
Local Infix ",O" := ext_op (at level 20).
Local Infix ",S" := ext_sort (at level 20).
Definition ε := emp.

Definition give_ix@{i} {Γ : Ctx@{i}}
  (i : ∀ Sorts0 Sorts1
   (preops : InductiveTypes.Operations Sorts0 Sorts0 Γ.(operations0)),
   (let Sorts1' i := Sorts1 i.1 (fst i.2) (snd i.2) in
    InductiveTypes.Operations Sorts1' Sorts1' (Γ.(operations1) preops)) →
   Γ.(@indices2) Sorts0 Sorts1 preops)
  : Indices@{i} Γ
  := i _ _
     (InductiveTypes.Initial.operations _)
     (InductiveTypes.Initial.operations _).
Arguments give_ix {Γ} & i.

(* Helper functions for variables *)
Definition popS {Γ A Sorts0 Sorts1 ops}
  : Γ.(@indices2) _ _ _ → (Γ ,S A).(@indices2) Sorts0 Sorts1 ops
  := inl.
Arguments popS {Γ A Sorts0 Sorts1 ops} & i.
Definition popO {Γ A Sorts0 Sorts1 ops}
  : Γ.(@indices2) _ _ _ → (Γ ,O A).(@indices2) Sorts0 Sorts1 ops
  := idmap.
Arguments popO {Γ A Sorts0 Sorts1 ops} & i.
(* Definition popD {Γ A Sorts0 Sorts1 ops}
  : Γ.(@indices2) _ _ _ → (ext_data Γ A).(@indices2) Sorts0 Sorts1 ops
  := idmap.
Arguments popD {Γ A Sorts0 Sorts1 ops} & i. *)
Definition top {Γ A Sorts0 Sorts1 ops}
  : A.(ix2) _ _  → (Γ ,S A).(@indices2) Sorts0 Sorts1 ops
  := inr.
Arguments top {Γ A Sorts0 Sorts1 ops} & i.

Definition spec_Con_Ty_emp : Ctx@{Set}
  := ε
     ,S u (* Con *)
     ,S ind_ix (inc (top tt)) u (* Ty *)
     ,O el (popS (top tt)).

Module Con_Ty_emp_Γ.
(* To specify the Ty Γ part of ext : ∀ Γ, Ty Γ → Con, we need to use the II def:
Con : Set
Ty : Con → Set
emp : Con
Γ : Con
*)
Definition spec : Ctx@{Set}
  := Eval compute in spec_Con_Ty_emp ,O el (popO (popS (top tt))).

Definition presorts
  : (Empty + Unit) + Unit → Set
  := InductiveTypes.Initial.sorts spec.(operations0).
Definition preCon : Set := presorts (inl (inr tt)).
Definition preTy : Set := presorts (inr tt).
Definition preops
  : (Unit * preCon) * preCon
  := InductiveTypes.Initial.operations spec.(operations0).
Definition preemp : preCon := snd (fst preops).
Definition preΓ : preCon := snd preops.

Definition goodCon
  : preCon → Set
  := λ preG, InductiveTypes.Initial.sorts (spec.(operations1) preops)
     (inl (inr tt); (tt, preG)).
Definition goodTy
  : preCon → preTy → Set
  := λ preG preA, InductiveTypes.Initial.sorts (spec.(operations1) preops)
     (inr tt; ((preG, tt), preA)).
Definition goodops
  : (Unit * goodCon preemp) * goodCon preΓ
  := InductiveTypes.Initial.operations (spec.(operations1) preops).
Definition goodemp : goodCon preemp := snd (fst goodops).
Definition goodΓ : goodCon preΓ := snd goodops.

Definition Γ : {preG : preCon & goodCon preG} := (preΓ; goodΓ).

Definition spec_Ty_of_Γ : Indices spec
  := give_ix (λ _ _ preops goodops, inr ((preops.(snd); goodops.(snd)); tt)).
Definition spec_plus_A : Ctx@{Set}
  := spec ,O el spec_Ty_of_Γ.
Definition spec_return_Ctx : TyOp@{Set} spec_plus_A
  := el (inl (inr tt)).
End Con_Ty_emp_Γ.

Definition spec_ext : TyOp@{Set} spec_Con_Ty_emp
  := ind_arg (inc (popO (popS (top tt))))
     (ind_arg (Γ := Con_Ty_emp_Γ.spec) (inc Con_Ty_emp_Γ.spec_Ty_of_Γ)
     Con_Ty_emp_Γ.spec_return_Ctx).

Definition spec_Con_Ty_emp_ext : Ctx@{Set} := Eval compute in spec_Con_Ty_emp ,O spec_ext.

Definition spec_Con_Ty_emp_ext_u : Ctx@{Set}
  := Eval compute in
     spec_Con_Ty_emp_ext
     ,O ind_arg (inc (inl (inr tt)))
        (let spec_Con_Ty_emp_ext_Γ
          := spec_Con_Ty_emp_ext ,O el (inl (inr tt)) in
         let preops
          := InductiveTypes.Initial.operations
             spec_Con_Ty_emp_ext_Γ.(operations0) in
         let goodops
          := InductiveTypes.Initial.operations
             (spec_Con_Ty_emp_ext_Γ.(operations1) preops) in
         let Γ := (snd preops; snd goodops) in
         el (Γ := spec_Con_Ty_emp_ext_Γ) (inr (Γ; tt))).

Module spec_pi.
Definition Ctx : Indices spec_Con_Ty_emp_ext_u
  := give_ix (λ _ _ preops goodops, inl (inr tt)).
Definition spec_Con_Ty_emp_ext_u_Γ := Eval compute in spec_Con_Ty_emp_ext_u ,O el Ctx.

Definition TyΓ : Indices spec_Con_Ty_emp_ext_u_Γ
  := give_ix (Γ := spec_Con_Ty_emp_ext_u_Γ)
     (λ _ _ preops goodops, inr ((snd preops; snd goodops); tt)).
Definition spec_Con_Ty_emp_ext_u_Γ_A := Eval compute in spec_Con_Ty_emp_ext_u_Γ ,O el TyΓ.
Definition TyΓA : Indices spec_Con_Ty_emp_ext_u_Γ_A
  := give_ix (λ _ _ preops goodops,
       inr ((preops.(fst).(fst).(fst).(snd) preops.(fst).(snd) preops.(snd);
             goodops.(fst).(fst).(fst).(snd)
             _ goodops.(fst).(snd) _ goodops.(snd)); tt)).
Definition return_TyΓ : Indices (spec_Con_Ty_emp_ext_u_Γ_A ,O el TyΓA)
  := give_ix (λ _ _ preops goodops,
       inr ((preops.(fst).(fst).(snd); goodops.(fst).(fst).(snd)); tt)).
Definition spec_pi : TyOp@{Set} spec_Con_Ty_emp_ext_u
  := ind_arg (Γ := spec_Con_Ty_emp_ext_u) (inc Ctx) (* Γ *)
     (ind_arg (Γ := spec_Con_Ty_emp_ext_u_Γ) (inc TyΓ) (* A *)
      (ind_arg (Γ := spec_Con_Ty_emp_ext_u_Γ_A) (inc TyΓA) (* B *)
       (el return_TyΓ))).
End spec_pi.

Definition TyCon_spec : Ctx@{Set}
  := Eval compute in spec_Con_Ty_emp_ext_u ,O spec_pi.spec_pi.

Local Notation convertible x y := (idpath x : x = y).

Section test_TyCon_spec.

(* indices0 gives a choice of tag_preCon vs tag_preTy *)
Check convertible TyCon_spec.(indices0) ((Empty + Unit) + Unit).
Definition tag_preCon : TyCon_spec.(indices0) := inl (inr tt).
Definition tag_preTy : TyCon_spec.(indices0) := inr tt.

(* The initial algebra then has sorts preCtx and preTy *)
Definition pre_sorts : (Empty + Unit) + Unit → Set
  := InductiveTypes.Initial.sorts TyCon_spec.(operations0).
Definition preCon := pre_sorts tag_preCon.
Definition preTy := pre_sorts tag_preTy.

(* operations0 gives the operations of the pre-syntax *)
Definition pre_ops
  : (((Unit *
    preCon) * (* pre_emp *)
    (preCon → preTy → preCon)) * (* pre_ext *)
    (preCon → preTy)) * (* pre_u *)
    (preCon → preTy → preTy → preTy) (* pre_pi *)
  := InductiveTypes.Initial.operations TyCon_spec.(operations0).
Definition pre_emp : preCon
  := pre_ops.(fst).(fst).(fst).(snd).
Definition pre_ext : preCon → preTy → preCon
  := pre_ops.(fst).(fst).(snd).
Definition pre_u : preCon → preTy
  := pre_ops.(fst).(snd).
Definition pre_pi : preCon → preTy → preTy → preTy
  := pre_ops.(snd).

(* indices1 collects the pre-syntax of the inductive indices. *)

(* goodCon is relative to nothing *)
Check convertible (TyCon_spec.(indices1) pre_sorts tag_preCon) Unit.
(* goodTy is relative to a preCon *)
Check convertible (TyCon_spec.(indices1) pre_sorts tag_preTy) (preCon * Unit).

(* How these are functorial over pre_sorts is functor_indices1 *)

(*
The goodness predicates are indexed by:
 * a choice of pre-judgement
 * the pre-syntax of the inductive indices
 * the pre-syntax we are judging good
*)
Definition indices_of_goodness_predicates
  := {i0 : TyCon_spec.(indices0) &
      TyCon_spec.(indices1) pre_sorts i0 *
      pre_sorts i0}.
Definition tag_goodCon (preΓ : preCon)
  : indices_of_goodness_predicates
  := (tag_preCon; (tt, preΓ)).
Definition tag_goodTy (preΓ : preCon) (preA : preTy)
  : indices_of_goodness_predicates
  := (tag_preTy; ((preΓ, tt), preA)).

Definition good_sorts : indices_of_goodness_predicates → Set
  := InductiveTypes.Initial.sorts (TyCon_spec.(operations1) pre_ops).
Definition goodCon : preCon → Set
  := λ preΓ, good_sorts (tag_goodCon preΓ).
Definition goodTy : preCon → preTy → Set
  := λ preΓ preA, good_sorts (tag_goodTy preΓ preA).

Definition good_ops
  : (((Unit *
    goodCon pre_emp) *
    (∀ preΓ, goodCon preΓ → ∀ preA, goodTy preΓ preA →
     goodCon (pre_ext preΓ preA))) *
    (∀ preΓ, goodCon preΓ → goodTy preΓ (pre_u preΓ))) *
    (∀ preΓ, goodCon preΓ → ∀ preA, goodTy preΓ preA →
     ∀ preB, goodTy (pre_ext preΓ preA) preB →
     goodTy preΓ (pre_pi preΓ preA preB))
  := InductiveTypes.Initial.operations (TyCon_spec.(operations1) pre_ops).

Definition Con : Set := {preΓ : preCon & goodCon preΓ}.
Definition Ty (Γ : Con) : Set := {preA : preTy & goodTy Γ.1 preA}.

(*
Indices offers a choice between
 * Con = inl (inr tt)
 * Ty Γ = inr (Γ; tt)
*)
Check convertible TyCon_spec.(Indices) ((Empty + Unit) + {_ : Con & Unit}).
