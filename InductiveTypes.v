Require Import HoTT.Basics HoTT.Utf8.

(* Indexed Inductive Definitions *)

(* Specify the operations of an inductive definition *)
Cumulative Inductive DataSpec@{i} (I : Type@{i}) : Type@{i+1} :=
  | single_argument (i : I)
  | infinitary_argument (A : Type@{i}) (B : A → I)
.

(* An [OpSpec I] is, informally, a list of constructors for an
[I]-indexed inductive definition.  The first three constructors [el],
[ind_arg], and [nonind_arg] generate inductively a single constructor:
[el] specifies the output index of the constructor, while the other
two add inductive and non-inductive arguments respectively.  The
"list" aspect (more precisely, a binary tree) is governed by [op_prod]
and [op_skip].  Putting these all in the same inductive definition
allows them to be all mixed up, but that doesn't materially affect the
generality. *)
Cumulative Inductive OpSpec@{i} (I : Type@{i}) : Type@{i+1} :=
  | el (i : I)
  | ind_arg (A : DataSpec@{i} I) (B : OpSpec I)
  | nonind_arg (A : Type@{i}) (B : A → OpSpec I)
  | op_prod (A B : OpSpec I)
  | op_skip
.
Arguments single_argument {I} i.
Arguments infinitary_argument {I} A B.
Arguments el {I} i.
Arguments ind_arg {I} A B.
Arguments nonind_arg {I} A B.
Arguments op_prod {I} A B.
Arguments op_skip {I}.

(* As an example that may make this more comprehensible to category
theorists, suppose we have a dependent polynomial, which semantically
is a triple of morphisms:

I <--p-- B --q--> A --r--> I.

We represent q by a dependent type B : A -> Type and the other two by
functions r : A -> I and p : ∀ a, B a -> I. *)
Section DependentPolynomial.
  Context (I : Type) (A : Type) (B : A -> Type) (r : A -> I) (p : ∀ a, B a -> I).
  (* The constructors of the corresponding indexed inductive type (the
     putative initial algebra for this dependent polynomial functor)
     are then, in the above syntax: *)
  Definition OpSpec_DepPoly : OpSpec I
    := nonind_arg A (λ a, ind_arg (infinitary_argument (B a) (p a)) (el (r a))).
End DependentPolynomial.

(* Conversely, we can turn an [OpSpec] into a dependent polynomial. *)
Section ToDepPoly.
  Context {I : Type}.
  Fixpoint constructors (op : OpSpec I) : Type
    := match op with
       | el i => Unit
       | ind_arg A B => constructors B
       | nonind_arg A B => { a : A & constructors (B a) }
       | op_prod A B => constructors A + constructors B
       | op_skip => Empty
       end.
  Fixpoint out_index (op : OpSpec I) : constructors op -> I
    := match op return constructors op -> I with
       | el i => λ _, i
       | ind_arg A B => out_index B
       | nonind_arg A B => λ ab, out_index (B ab.1) ab.2
       | op_prod A B => λ ab, match ab with
                              | inl a => out_index A a
                              | inr b => out_index B b
                              end
       | op_skip => Empty_rec I
       end.
  Definition argdata (dt : DataSpec I) : Type
    := match dt with
       | single_argument i => Unit
       | infinitary_argument A B => A
       end.
  Fixpoint arguments (op : OpSpec I) : constructors op -> Type
    := match op return constructors op -> Type with
       | el i => λ _, Empty
       | ind_arg A B => λ c, argdata A + arguments B c
       | nonind_arg A B => λ ab, arguments (B ab.1) ab.2
       | op_prod A B => λ ab, match ab with
                              | inl a => arguments A a
                              | inr b => arguments B b
                              end
       | op_skip => Empty_rec Type
       end.
  Definition arg_index (dt : DataSpec I) : argdata dt -> I
    := match dt return argdata dt -> I with
       | single_argument i => λ _, i
       | infinitary_argument A B => B
       end.
  Fixpoint in_index (op : OpSpec I) : ∀ c, arguments op c -> I
    := match op return ∀ c, arguments op c -> I with
       | el i => λ _, Empty_rec I
       | ind_arg A B => λ c xy, match xy with
                                | inl x => arg_index A x
                                | inr y => in_index B c y
                                end
       | nonind_arg A B => λ ab x, in_index (B ab.1) ab.2 x
       | op_prod A B => λ ab, match ab with
                                | inl a => in_index A a
                                | inr b => in_index B b
                                end
       | op_skip => Empty_ind (λ c, arguments op_skip c -> I)
       end.

  (* If we start from a dependent polynomial, then this recaptures it,
  up to trivialities like Σs over Unit or coproducts with Empty. *)
  Context (A : Type) (B : A -> Type) (r : A -> I) (p : ∀ a, B a -> I).
  Eval compute in (constructors (OpSpec_DepPoly I A B r p)).
  (* ==> ∃ _ : A, Unit *)
  Eval compute in (out_index (OpSpec_DepPoly I A B r p)).
  (* ==> λ ab, r ab.1 *)
  Eval compute in (arguments (OpSpec_DepPoly I A B r p)).
  (* ==> λ ab, B ab ₁ ⊔ Empty *)
  Eval compute in (in_index (OpSpec_DepPoly I A B r p)).
  (* ==> λ ab xy,
       match xy with
       | inl x => p ab.1 x
       | inr y => match y return I with end
       end
   *)
End ToDepPoly.

Definition functor_DataSpec@{i j} {I : Type@{i}} {J : Type@{j}} (f : I → J)
  : DataSpec@{i} I → DataSpec@{j} J
  := λ A, match A with
     | single_argument i => single_argument (f i)
     | infinitary_argument A B => infinitary_argument A (f o B)
     end.

Definition functor_OpSpec@{i j} {I : Type@{i}} {J : Type@{j}} (f : I → J)
  : OpSpec@{i} I → OpSpec@{j} J
  := fix F A := match A with
     | el i => el (f i)
     | ind_arg A B => ind_arg (functor_DataSpec f A) (F B)
     | nonind_arg A B => nonind_arg A (F o B)
     | op_prod A B => op_prod (F A) (F B)
     | op_skip => op_skip
     end.

(* Now we define the "algebra structure" corresponding to a given list
of constructors [A : OpSpec I].  Given [X : I -> Type], an element of
[Operations X A] is an "[A]-algebra structure" on [X], and the
intended indexed inductive definition should be the initial such
[A]-algebra. *)
Section el_op.
Universe i.
Context {I : Type@{i}} (Xin Xout : I → Type@{i}).
Definition ElDataSpec@{} (A : DataSpec@{i} I) : Type@{i}
  := match A with
     | single_argument i => Xin i
     | infinitary_argument A B => ∀ a, Xin (B a)
     end.
Fixpoint Operations@{} (A : OpSpec@{i} I) : Type@{i}
  := match A with
     | el i => Xout i
     | ind_arg A B => ElDataSpec A → Operations B
     | nonind_arg A B => ∀ a, Operations (B a)
     | op_prod A B => Operations A * Operations B
     | op_skip => Unit
     end.

(* We can check that this produces the correct result on a dependent
polynomial:

Eval compute in (λ A B r p, Operations (OpSpec_DepPoly I A B r p)).
 ==> λ A B r p, ∀ a : A, (∀ b : B a, Xin (p a b)) → Xout (r a) *)

(* Next we specify the notion of "dependent algebra structure", which
gives the hypotheses of the desired eliminator. *)
Universe j.
Constraint i <= j. (* Don't consider eliminating into smaller universes *)
Context (Pin : ∀ i, Xin i → Type@{j}) (Pout : ∀ i, Xout i → Type@{j}).
Definition InductiveHypothesis@{} (A : DataSpec@{i} I)
  : ElDataSpec A → Type@{j}
  := match A return ElDataSpec A → Type@{_} with
     | single_argument i => Pin i
     | infinitary_argument A B => λ f, ∀ a, Pin (B a) (f a)
     end.
Fixpoint Methods@{} (A : OpSpec@{i} I)
  : Operations A → Type@{j}
  := match A return Operations A → Type@{_} with
     | el i => Pout i
     | ind_arg A B => λ f, ∀ x, InductiveHypothesis A x → Methods B (f x)
     | nonind_arg A B => λ f, ∀ a, Methods (B a) (f a)
     | op_prod A B => λ x, Methods A (fst x) * Methods B (snd x)
     | op_skip => λ _, Unit
     end.

(*
Eval compute in (λ A B r p (op : Operations (OpSpec_DepPoly I A B r p)), Methods (OpSpec_DepPoly I A B r p) op).
==> λ A B r p op,
  ∀ (a : A) (x : ∀ b : B a, X (p a b)),
  (∀ b : B a, P (p a b) (x b)) → P (r a) (op a x)
*)

(* Finally, we specify the computation equations that a putative solution to the elimination rule ought to satisfy. *)
Context (Ein : ∀ i x, Pin i x) (Eout : ∀ i x, Pout i x).
Definition InductiveData@{} (A : DataSpec@{i} I)
  : ∀ x, InductiveHypothesis A x
  := match A return ∀ x, InductiveHypothesis A x with
     | single_argument i => Ein i
     | infinitary_argument A B => λ f a, Ein (B a) (f a)
     end.
Fixpoint Equations@{} (A : OpSpec@{i} I)
  : ∀ op, Methods A op → Type@{j}
  := match A return ∀ op, Methods A op → Type@{_} with
     | el i => λ x y, Eout i x = y
     | ind_arg A B => λ f f',
       ∀ x, Equations B (f x) (f' x (InductiveData A x))
     | nonind_arg A B => λ f f',
       ∀ a, Equations (B a) (f a) (f' a)
     | op_prod A B => λ x x',
       Equations A (fst x) (fst x') * Equations B (snd x) (snd x')
     | op_skip => λ _ _,
       Unit
     end.
(* Alternatively, have InductiveData be a relation, like in general II elim *)

(*
Eval compute in (λ A B r p (op : Operations (OpSpec_DepPoly I A B r p)) m, Equations (OpSpec_DepPoly I A B r p) op m).
==> λ A B r p op m, 
  ∀ (a : A) (x : ∀ b : B a, X (p a b)),
    E (r a) (op a x) = m a x (λ b : B a, E (p a b) (x b))
*)

End el_op.

Definition data_to_op@{i} {I : Type@{i}} : DataSpec@{i} I → OpSpec@{i} I
  := λ A, match A with
     | single_argument i => el i
     | infinitary_argument A B => nonind_arg A (el o B)
     end.

(* is an equivalence *)
Definition data_to_op_El@{i j} {I : Type@{i}} {El : I → Type@{j}}
  : ∀ {A : DataSpec@{i} I},
    ElDataSpec@{i} El A → Operations@{j} El El (data_to_op A)
  := λ {A}, match A with
     | single_argument i => idmap
     | infinitary_argument A B => idmap
     end.
Definition op_to_data_El@{i j} {I : Type@{i}} {El : I → Type@{j}}
  : ∀ {A : DataSpec@{i} I},
    Operations@{j} El El (data_to_op A) → ElDataSpec@{i} El A
  := λ {A}, match A with
     | single_argument i => idmap
     | infinitary_argument A B => idmap
     end.

(* is an equivalence *)
Definition ElDataSpec_compose@{i j k} {I : Type@{i}} {J : Type@{j}}
  {f : I → J} {El : J → Type@{k}}
  : ∀ {A : DataSpec@{i} I},
    ElDataSpec@{i} (El o f) A → ElDataSpec@{j} El (functor_DataSpec f A)
  := λ {A}, match A with
     | single_argument i => idmap
     | infinitary_argument A B => idmap
     end.

(* is an equivalence *)
Definition Operations_compose@{i j k} {I : Type@{i}} {J : Type@{j}}
  {f : I → J} {El : J → Type@{k}}
  : ∀ {A : OpSpec@{i} I},
    Operations@{j} El El (functor_OpSpec f A) →
    Operations@{j} (El o f) (El o f) A
  := fix comp {A} := match A with
     | el i => idmap
     | ind_arg A B => λ f, (λ a, comp (f (ElDataSpec_compose a)))
     | nonind_arg A B => λ f a, comp (f a)
     | op_prod A B => λ x, (comp (fst x), comp (snd x))
     | op_skip => λ _, tt
     end.

Definition functor_ElDataSpec {I : Type@{i}} {Elin1 Elin2 : I → Type@{i}}
  (Fin : ∀ i, Elin2 i → Elin1 i)
  : ∀ {A : DataSpec@{i} I},
    ElDataSpec@{i} Elin2 A → ElDataSpec@{i} Elin1 A
  := λ {A}, match A return ElDataSpec@{i} Elin2 A → ElDataSpec@{i} Elin1 A with
     | single_argument i => Fin i
     | infinitary_argument A B => λ f a, Fin _ (f a)
     end.
Definition functor_Operations {I : Type@{i}}
  {Elin1 Elin2 Elout1 Elout2 : I → Type@{i}}
  (Fin : ∀ i, Elin2 i → Elin1 i) (Fout : ∀ i, Elout1 i → Elout2 i)
  : ∀ {A : OpSpec@{i} I},
    Operations@{i} Elin1 Elout1 A →
    Operations@{i} Elin2 Elout2 A
  := fix func {A} := match A with
     | el i => Fout i
     | ind_arg A B => λ f a, func (f (functor_ElDataSpec Fin a))
     | nonind_arg A B => λ f a, func (f a)
     | op_prod A B => λ x, (func (fst x), func (snd x))
     | op_skip => λ _, tt
     end.
Definition functor_Operations1 {I : Type@{i}}
  {Elin Elout1 Elout2 : I → Type@{i}}
  (Fout : ∀ i, Elout1 i → Elout2 i)
  : ∀ {A : OpSpec@{i} I},
    Operations@{i} Elin Elout1 A →
    Operations@{i} Elin Elout2 A
  := fix func {A} := match A with
     | el i => Fout i
     | ind_arg A B => λ f a, func (f a)
     | nonind_arg A B => λ f a, func (f a)
     | op_prod A B => λ x, (func (fst x), func (snd x))
     | op_skip => λ _, tt
     end.
Definition functor_Methods1 {I : Type@{i}}
  {Elin Elout1 Elout2 : I → Type@{i}}
  (FElout : ∀ i, Elout1 i → Elout2 i)
  {Pin : ∀ i, Elin i → Type@{j}}
  {Pout1 : ∀ i, Elout1 i → Type@{j}} {Pout2 : ∀ i, Elout2 i → Type@{j}}
  (FPout : ∀ i x, Pout1 i x → Pout2 i (FElout i x))
  : ∀ {A : OpSpec@{i} I} {ops : Operations@{i} Elin Elout1 A},
    Methods@{i j} Elin Elout1 Pin Pout1 A ops →
    Methods@{i j} Elin Elout2 Pin Pout2 A (functor_Operations1 FElout ops)
  := fix func {A} := match A with
     | el i => FPout i
     | ind_arg A B => λ ops f a x, func (ops a) (f a x)
     | nonind_arg A B => λ ops f a, func (ops a) (f a)
     | op_prod A B => λ ops x, (func (fst ops) (fst x), func (snd ops) (snd x))
     | op_skip => λ _ _, tt
     end.
Definition functor_Methods1_rev {I : Type@{i}}
  {Elin Elout1 Elout2 : I → Type@{i}}
  (FElout : ∀ i, Elout1 i → Elout2 i)
  {Pin : ∀ i, Elin i → Type@{j}}
  {Pout1 : ∀ i, Elout1 i → Type@{j}} {Pout2 : ∀ i, Elout2 i → Type@{j}}
  (FPout : ∀ i x, Pout2 i (FElout i x) → Pout1 i x)
  : ∀ {A : OpSpec@{i} I} {ops : Operations@{i} Elin Elout1 A},
    Methods@{i j} Elin Elout2 Pin Pout2 A (functor_Operations1 FElout ops) →
    Methods@{i j} Elin Elout1 Pin Pout1 A ops
  := fix func {A} := match A with
     | el i => FPout i
     | ind_arg A B => λ ops f a x, func (ops a) (f a x)
     | nonind_arg A B => λ ops f a, func (ops a) (f a)
     | op_prod A B => λ ops x, (func (fst ops) (fst x), func (snd ops) (snd x))
     | op_skip => λ _ _, tt
     end.
Definition functor_Methods0_rev {I : Type@{i}}
  {Elin Elout1 Elout2 : I → Type@{i}}
  (Fout : ∀ i, Elout1 i → Elout2 i)
  {Pin : ∀ i, Elin i → Type@{j}}
  {Pout2 : ∀ i, Elout2 i → Type@{j}}
  (Pout1 : ∀ i, Elout1 i → Type@{j} := λ i, Pout2 i o Fout i)
  : ∀ {A : OpSpec@{i} I} {ops : Operations@{i} Elin Elout1 A},
    Methods@{i j} Elin Elout2 Pin Pout2 A (functor_Operations1 Fout ops) →
    Methods@{i j} Elin Elout1 Pin Pout1 A ops
  := fix func {A} : ∀ {ops}, _ → _ := match A with
     | el i => λ x, idmap
     | ind_arg A B => λ ops f a x, func (f a x)
     | nonind_arg A B => λ ops f a, func (f a)
     | op_prod A B => λ ops x, (func (fst x), func (snd x))
     | op_skip => λ _ _, tt
     end.
Definition functor_Methods0 {I : Type@{i}}
  {Elin Elout1 Elout2 : I → Type@{i}}
  (Fout : ∀ i, Elout1 i → Elout2 i)
  {Pin : ∀ i, Elin i → Type@{j}}
  {Pout2 : ∀ i, Elout2 i → Type@{j}}
  (Pout1 : ∀ i, Elout1 i → Type@{j} := λ i, Pout2 i o Fout i)
  : ∀ {A : OpSpec@{i} I} {ops : Operations@{i} Elin Elout1 A},
    Methods@{i j} Elin Elout1 Pin Pout1 A ops →
    Methods@{i j} Elin Elout2 Pin Pout2 A (functor_Operations1 Fout ops)
  := fix func {A} : ∀ {ops}, _ → _ := match A with
     | el i => λ x, idmap
     | ind_arg A B => λ ops f a x, func (f a x)
     | nonind_arg A B => λ ops f a, func (f a)
     | op_prod A B => λ ops x, (func (fst x), func (snd x))
     | op_skip => λ _ _, tt
     end.

Definition functor_Equations0_rev {I : Type@{i}}
  {Elin Elout1 Elout2 : I → Type@{i}}
  (Fout : ∀ i, Elout1 i → Elout2 i)
  {Pin : ∀ i, Elin i → Type@{j}}
  {Pout2 : ∀ i, Elout2 i → Type@{j}}
  (Pout1 : ∀ i, Elout1 i → Type@{j} := λ i, Pout2 i o Fout i)
  {Ein : ∀ i x, Pin i x}
  {Eout2 : ∀ i x, Pout2 i x}
  (Eout1 : ∀ i x, Pout1 i x := λ i x, Eout2 i (Fout i x))
  : ∀ {A : OpSpec@{i} I} {ops : Operations@{i} Elin Elout1 A}
      {M : Methods@{i j} Elin Elout2 Pin Pout2 A
           (functor_Operations1 Fout ops)},
    Equations@{i j} Elin Elout1 Pin Pout1 Ein Eout1 A ops
      (functor_Methods0_rev Fout M) →
    Equations@{i j} Elin Elout2 Pin Pout2 Ein Eout2 A
      (functor_Operations1 Fout ops) M
  := fix func {A} : ∀ {ops M}, _ → _ := match A with
     | el i => λ ops M, idmap
     | ind_arg A B => λ ops M f a, func (f a)
     | nonind_arg A B => λ ops M f a, func (f a)
     | op_prod A B => λ ops M x,
       (func (fst x),
        func (snd x))
     | op_skip => λ _ _ _, tt
     end.

Module Initial.
Section initial.

(* TODO: prove we have sorts and operations that satisfy the eliminator *)

Universe i.
Context {I : Type@{i}}.

(* Section test_constructors. *)
Context (A : OpSpec@{i} I).

Local Notation "( ? p )" := (λ A, match A with p => Unit | _ => Empty end)
  (p pattern).
Local Notation "( ' p => x )" :=
  (λ A, match A as A return ∀ H : (? p) A, _ with
   | p => λ _, x
   | _ => λ XX, match XX in Empty with end
   end)
  (p pattern).

Record infinitary_argument_data := {
  inf_arg_data_A : Type@{i};
  inf_arg_data_B : inf_arg_data_A → I
}.
Inductive init_Data@{} (El : I → Type@{i}) (A' : DataSpec@{i} I) : Type@{i} :=
  | init_inc (H : (? single_argument _) A')
    (_ : El (('single_argument i => i) A' H))
  | init_inf (H : (? infinitary_argument _ _) A')
    (_ : let '{|inf_arg_data_A:=A; inf_arg_data_B:=B|}
          := ('infinitary_argument A B =>
              {|inf_arg_data_A:=A; inf_arg_data_B:=B|}) A' H in
         ∀ a : A, El (B a))
.
Definition init_Data_inc_rect {El i} (P : init_Data El (single_argument i) → Type@{j})
  (IS : ∀ x, P (init_inc El (single_argument i) tt x)) : ∀ X, P X
  := λ X, match X with
     | init_inc tt x => IS x
     | init_inf XX _ => match XX with end
     end.
Definition init_Data_inf_rect {El A B} (P : init_Data El (infinitary_argument A B) → Type@{j})
  (IS : ∀ f, P (init_inf El (infinitary_argument A B) tt f)) : ∀ X, P X
  := λ X, match X with
     | init_inc XX _ => match XX with end
     | init_inf tt f => IS f
     end.
(* is an equivalence *)
Fixpoint init_Data_to_ElDataSpec {El} (A : DataSpec@{i} I)
  : init_Data El A → ElDataSpec El A
  := match A with
     | single_argument i => init_Data_inc_rect
       (λ _, ElDataSpec El (single_argument i))
       idmap
     | infinitary_argument A B => init_Data_inf_rect
       (λ _, ElDataSpec El (infinitary_argument A B))
       idmap
     end.
Fixpoint ElDataSpec_to_init_Data {El} (A : DataSpec@{i} I)
  : ElDataSpec El A → init_Data El A
  := match A with
     | single_argument i as A' => init_inc El A' tt
     | infinitary_argument A B as A' => init_inf El A' tt
     end.

Record infinitary_cons_data := {
  inf_cons_data_A : Type@{i};
  inf_cons_data_B : inf_cons_data_A → OpSpec@{i} I
}.
Inductive init@{} (A' : OpSpec@{i} I) (i : I) : Type@{i} :=
  | init_el (H : (? el _) A')
    (_ : ('el j => j) A' H = i)
  | init_ind_arg (H : (? ind_arg _ _) A')
    (_ : init_Data (init A) (('ind_arg A _ => A) A' H))
    (_ : init (('ind_arg _ B => B) A' H) i)
  | init_nonind_arg (H : (? nonind_arg _ _) A')
    (AB := ('nonind_arg A B =>
            {|inf_cons_data_A:=A; inf_cons_data_B:=B|}) A' H)
    (a : AB.(inf_cons_data_A))
    (_ : init (AB.(inf_cons_data_B) a) i)
  | init_op_prod_l (H : (? op_prod _ _) A')
    (_ : init (('op_prod A _ => A) A' H) i)
  | init_op_prod_r (H : (? op_prod _ _) A')
    (_ : init (('op_prod _ B => B) A' H) i)
.

(* End test_constructors. *)

(* Context  (A : OpSpec@{i} I). *)

Definition sorts : I → Type@{i} := init A.

Fixpoint operations_helper A'
  : Operations@{i} sorts (init A') A'
  := match A' return Operations@{i} sorts (init A') A' with
     | el i as A' => init_el A' _ tt 1
     | ind_arg A B as A' => λ a, functor_Operations1
       (λ i, init_ind_arg A' i tt (ElDataSpec_to_init_Data _ a))
       (operations_helper B)
     | nonind_arg A B as A' => λ a, functor_Operations1
       (λ i, init_nonind_arg A' i tt a)
       (operations_helper (B a))
     | op_prod A B as A' =>
       (functor_Operations1 (λ i, init_op_prod_l A' i tt) (operations_helper A),
        functor_Operations1 (λ i, init_op_prod_r A' i tt) (operations_helper B))
     | op_skip as A' => tt
     end.
Definition operations : Operations@{i} sorts sorts A
  := operations_helper A.

Section dependent_eliminator.
Universe j.
Constraint i <= j.
Context
  (P : ∀ i, sorts i → Type@{j})
  (M : Methods@{i j} sorts sorts P P A operations)
.

Local Notation "( @ p => IS & A H => P )"
  := (λ A', match A' as A return ∀ H : (? p) A, P with
      | p => λ 'tt, IS
      | _ => λ XX, match XX with end
      end)
     (p pattern, A ident, H ident).

Local Notation P' A' i x := (∀ (P2 : ∀ i, init A' i → Type@{j}),
         Methods@{i j} sorts (init A') P P2 A' (operations_helper A') →
         P2 i x).
Local Notation P2' A' B a := (∀ (P2 : ∀ i, init _ i → Type@{j}),
             Methods@{i j} sorts _ P P2 (ind_arg A' B)
               (operations_helper (ind_arg A' B)) →
             Methods@{i j} sorts _ P
             (λ i b, P2 i (init_ind_arg (ind_arg A' B) i tt a b))
             B (operations_helper B)).
Fixpoint eliminators_helper@{} A' i (x : init A' i) {struct x}
  : ∀ (P2 : ∀ i, init A' i → Type@{j}),
    Methods@{i j} sorts (init A') P P2 A' (operations_helper A') →
    P2 i x
  := match x return P' A' i x with
     | init_el H p as x =>
       (@ el i => λ p, match p with idpath => λ H, idmap end &
        A' H => ∀ p, P' A' i (init_el _ _ H p))
       A' H p
     | init_ind_arg H a b =>
       (@ ind_arg A B => λ a, λ b IH H M', IH _
          (match a return P2' A B a with
           | init_inc H2 x =>
             (@ single_argument i => λ x H (M' : ∀ a, _), functor_Methods0_rev _
                (M' _ (eliminators_helper _ _ x P M)) &
              A' H2 => ∀ x, P2' A' B (init_inc _ A' H2 x))
             A H2 x
           | init_inf H2 f =>
             (@ infinitary_argument A2 B2 => λ f H M', functor_Methods0_rev _
                (M' _ (λ a2, eliminators_helper _ _ (f a2) P M)) &
              A' H2 => ∀ f, P2' A' B (init_inf _ A' H2 f))
             A H2 f
           end H M') &
        A' H => ∀ a b, P' _ i b → P' A' i (init_ind_arg _ _ H a b))
       A' H a b (eliminators_helper _ i b)
     | init_nonind_arg H a b =>
       (@ nonind_arg A B => λ a b H M',
          eliminators_helper (B a) i b _
          (functor_Methods0_rev _ (M' a)) &
        A' H => ∀ a b, P' A' i (init_nonind_arg _ _ H a b))
       A' H a b
     | init_op_prod_l H a =>
       (@ op_prod A B => λ a H M',
          eliminators_helper A i a _
          (functor_Methods0_rev _ (fst M')) &
        A' H => ∀ a, P' A' i (init_op_prod_l _ _ H a))
       A' H a
     | init_op_prod_r H b =>
       (@ op_prod A B => λ b H M',
          eliminators_helper B i b _
          (functor_Methods0_rev _ (snd M')) &
        A' H => ∀ b, P' A' i (init_op_prod_r _ _ H b))
       A' H b
     end.

Definition eliminators@{} i x : P i x
  := eliminators_helper A i x P M.

Fixpoint equations_helper@{} A'
  : ∀ (P2 : ∀ i, init A' i → Type@{j}) M,
    Equations@{i j} sorts (init A') P P2
      eliminators (λ i x, eliminators_helper A' i x P2 M)
      A' (operations_helper A') M
  := match A' with
     | el i => λ P2 M, idpath
     | ind_arg (single_argument i) B => λ P2 M a,
       functor_Equations0_rev _ (equations_helper B _ _)
     | ind_arg (infinitary_argument A B2) B => λ P2 M a,
       functor_Equations0_rev _ (equations_helper _ _ _)
     | nonind_arg A B => λ P2 M a,
       functor_Equations0_rev _ (equations_helper _ _ _)
     | op_prod A B => λ P2 M,
       (functor_Equations0_rev _ (equations_helper _ _ _),
        functor_Equations0_rev _ (equations_helper _ _ _))
     | op_skip => λ P2 M, tt
     end.

Definition equations@{}
  : Equations@{i j} sorts sorts P P eliminators eliminators A operations M
  := equations_helper A P M.
End dependent_eliminator.

(* Derived from dependent eliminator *)
Section initiality.
Universe j.
Constraint i <= j.
Context
  {sorts' : I → Type@{j}}
  (operations' : Operations@{j} sorts' sorts' A)
.

Fixpoint nondependent_methods@{} {A : OpSpec@{i} I}
  : Operations@{j} sorts' sorts' A →
    Methods@{i j} sorts (init A) (λ i _, sorts' i) (λ i _, sorts' i) A (operations_helper A)
  := match A return Operations@{j} sorts' sorts' A →
    Methods@{i j} sorts (init A) (λ i _, sorts' i) (λ i _, sorts' i) A (operations_helper A) with
     | el i => idmap
     | ind_arg (single_argument i) B => λ f _ a, functor_Methods0 _
       (nondependent_methods (A := B) (f a))
     | ind_arg (infinitary_argument A B2) B => λ f _ a, functor_Methods0 _
       (nondependent_methods (A := B) (f a))
     | nonind_arg A B => λ f a, functor_Methods0 _
       (nondependent_methods (A := B a) (f a))
     | op_prod A B => λ x,
       (functor_Methods0 _ (nondependent_methods (fst x)),
        functor_Methods0 _ (nondependent_methods (snd x)))
     | op_skip => idmap
     end.

(* Should really define morphisms including equations,
   then prove that this one is unique. *)

Definition initial_morphism_sorts@{} : ∀ i, sorts i → sorts' i
  := eliminators (λ i _, sorts' i) (nondependent_methods operations').

End initiality.
End initial.
End Initial.

(* (* Specify the sorts of an inductive definition *)
Cumulative Inductive SortSpec@{i} : Type@{i+1} :=
  | u
  | nonind_ix (A : Type@{i}) (B : A → SortSpec)
  | sort_prod (A B : SortSpec)
.

(* The intended interpretation, as a bunch of families of types: *)
Fixpoint Sorts@{i ii | i < ii} (S : SortSpec@{i}) : Type@{ii}
  := match S with
     | u => Type@{i}
     | nonind_ix A B => ∀ a, Sorts (B a)
     | sort_prod A B => Sorts A * Sorts B
     end.
(* Could do an inductive version in Type@{i+1}, probably not worth it *)
(* Alternatively, just use Indices → Type@{i} *)

Fixpoint Indices (S : SortSpec@{i}) : Type@{i}
  := match S with
     | u => Unit
     | nonind_ix A B => { a : A & Indices (B a) }
     | sort_prod A B => Indices A + Indices B
     end.

Fixpoint get_sort@{i ii} {S : SortSpec@{i}}
  : Sorts@{i ii} S → Indices S → Type@{i}
  := match S return Sorts S → Indices S → Type@{i} with
     | u => λ X _, X
     | nonind_ix A B => λ X i, get_sort (X i.1) i.2
     | sort_prod A B => λ X i, match i with
       | inl a => get_sort (fst X) a
       | inr b => get_sort (snd X) b
       end
     end.
(*
Theorem isequiv_get_sort `{Funext} {S} : IsEquiv (get_sort@{i j k} (S := S)).
*)

Fixpoint Motives@{i j ii ijj} (S : SortSpec@{i})
  : Sorts@{i ii} S → Type@{ijj}
  := match S return Sorts S → Type@{ijj} with
     | u => λ X, X → Type@{j}
     | nonind_ix A B => λ f, ∀ a, Motives (B a) (f a)
     | sort_prod A B => λ x, Motives A (fst x) * Motives B (snd x)
     end.
Fixpoint Eliminators@{i j ii ijj ij} (S : SortSpec@{i})
  : ∀ A : Sorts@{i ii} S, Motives@{i j ii ijj} S A → Type@{ij}
  := match S return ∀ A : Sorts S, Motives S A → Type@{ij} with
     | u => λ X P,
       ∀ x, P x
     | nonind_ix A B => λ f f',
       ∀ a, Eliminators (B a) (f a) (f' a)
     | sort_prod A B => λ x x',
       Eliminators A (fst x) (fst x') * Eliminators B (snd x) (snd x')
     end. *)


(* Record IndSpec@{i} : Type@{i+1} := {
  IndSorts : SortSpec@{i};
  IndOps   : OpSpec@{i} (Indices IndSorts);
}.
Definition Algebra@{i ii | i < i} (S : IndSpec@{i}) : Type@{j}
  := { El : Sorts@{i ii} S.(IndSorts) & Operations (get_sort El) S.(IndOps) }. *)


