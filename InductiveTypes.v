Require Import HoTT.Basics HoTT.Utf8.

(* Indexed Inductive Definitions *)

(* Specify the operations of an inductive definition *)
Cumulative Inductive DataSpec@{i} (I : Type@{i}) : Type@{i+1} :=
  | inc (i : I)
  | inf (A : Type@{i}) (B : A → DataSpec I)
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
Arguments inc {I} i.
Arguments inf {I} A B.
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
    := nonind_arg A (λ a, ind_arg (inf (B a) (λ b, inc (p a b))) (el (r a))).
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
  Fixpoint argdata (dt : DataSpec I) : Type
    := match dt with
       | inc i => Unit
       | inf A B => { a : A & argdata (B a) }
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
  Fixpoint arg_index (dt : DataSpec I) : argdata dt -> I
    := match dt return argdata dt -> I with
       | inc i => λ _, i
       | inf A B => λ ab, arg_index (B ab.1) ab.2
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
  (* ==> λ ab, (∃ _ : B ab ₁, Unit) ⊔ Empty *)
  Eval compute in (in_index (OpSpec_DepPoly I A B r p)).
  (* ==> λ ab xy,
       match xy with
       | inl x => p ab.1 x.1
       | inr y => match y return I with end
       end
   *)
End ToDepPoly.

Definition functor_DataSpec@{i j} {I : Type@{i}} {J : Type@{j}} (f : I → J)
  : DataSpec@{i} I → DataSpec@{j} J
  := fix F A := match A with
     | inc i => inc (f i)
     | inf A B => inf A (F o B)
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
Context {I : Type@{i}} (X : I → Type@{i}).
Fixpoint ElDataSpec@{} (A : DataSpec@{i} I) : Type@{i}
  := match A with
     | inc i => X i
     | inf A B => ∀ a, ElDataSpec (B a)
     end.
Fixpoint Operations@{} (A : OpSpec@{i} I) : Type@{i}
  := match A with
     | el i => X i
     | ind_arg A B => ElDataSpec A → Operations B
     | nonind_arg A B => ∀ a, Operations (B a)
     | op_prod A B => Operations A * Operations B
     | op_skip => Unit
     end.

(* We can check that this produces the correct result on a dependent
polynomial:

Eval compute in (λ A B r p, Operations (OpSpec_DepPoly I A B r p)).
 ==> λ A B r p, ∀ a : A, (∀ b : B a, X (p a b)) → X (r a) *)

(* Next we specify the notion of "dependent algebra structure", which
gives the hypotheses of the desired eliminator. *)
Universe j.
Constraint i <= j. (* Don't consider eliminating into smaller universes *)
Context (P : ∀ i, X i → Type@{j}).
Fixpoint InductiveHypothesis@{} (A : DataSpec@{i} I)
  : ElDataSpec A → Type@{j}
  := match A return ElDataSpec A → Type@{_} with
     | inc i => P i
     | inf A B => λ f, ∀ a, InductiveHypothesis (B a) (f a)
     end.
Fixpoint Methods@{} (A : OpSpec@{i} I)
  : Operations A → Type@{j}
  := match A return Operations A → Type@{_} with
     | el i => P i
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
Context (E : ∀ i x, P i x).
Fixpoint InductiveData@{} (A : DataSpec@{i} I)
  : ∀ x, InductiveHypothesis A x
  := match A return ∀ x, InductiveHypothesis A x with
     | inc i => E i
     | inf A B => λ f a, InductiveData (B a) (f a)
     end.
Fixpoint Equations@{} (A : OpSpec@{i} I)
  : ∀ op, Methods A op → Type@{j}
  := match A return ∀ op, Methods A op → Type@{_} with
     | el i => λ x y, E i x = y
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
  := fix include A := match A with
     | inc i => el i
     | inf A B => nonind_arg A (include o B)
     end.

(* is an equivalence *)
Definition data_to_op_El@{i j} {I : Type@{i}} {El : I → Type@{j}}
  : ∀ {A : DataSpec@{i} I},
    ElDataSpec@{i} El A → Operations@{j} El (data_to_op A)
  := fix map {A} := match A with
     | inc i => idmap
     | inf A B => λ f a, map (f a)
     end.
Definition op_to_data_El@{i j} {I : Type@{i}} {El : I → Type@{j}}
  : ∀ {A : DataSpec@{i} I},
    Operations@{j} El (data_to_op A) → ElDataSpec@{i} El A
  := fix map {A} := match A with
     | inc i => idmap
     | inf A B => λ f a, map (f a)
     end.

(* is an equivalence *)
Definition ElDataSpec_compose@{i j k} {I : Type@{i}} {J : Type@{j}}
  {f : I → J} {El : J → Type@{k}}
  : ∀ {A : DataSpec@{i} I},
    ElDataSpec@{i} (El o f) A → ElDataSpec@{j} El (functor_DataSpec f A)
  := fix comp {A} := match A with
     | inc i => idmap
     | inf A B => λ f a, comp (f a)
     end.

(* is an equivalence *)
Definition Operations_compose@{i j k} {I : Type@{i}} {J : Type@{j}}
  {f : I → J} {El : J → Type@{k}}
  : ∀ {A : OpSpec@{i} I},
    Operations@{j} El (functor_OpSpec f A) → Operations@{j} (El o f) A
  := fix comp {A} := match A with
     | el i => idmap
     | ind_arg A B => λ f, (λ a, comp (f (ElDataSpec_compose a)))
     | nonind_arg A B => λ f a, comp (f a)
     | op_prod A B => λ x, (comp (fst x), comp (snd x))
     | op_skip => λ _, tt
     end.

Module Initial.
Section initial.

(* TODO: prove we have sorts and operations that satisfy the eliminator *)

Universe i.
Context {I : Type@{i}} (A : OpSpec@{i} I).

Definition sorts : I → Type@{i}.
Admitted.

Definition operations : Operations@{i} sorts A.
Admitted.

Section dependent_eliminator.
Universe j.
Constraint i <= j.
Context
  (P : ∀ i, sorts i → Type@{j})
  (M : Methods@{i j} sorts P A operations)
.

Definition eliminators : ∀ i x, P i x.
Admitted.

Definition equations : Equations@{i j} sorts P eliminators A operations M.
Admitted.
End dependent_eliminator.

(* Can be derived from dependent_eliminator *)
Section initiality.
Universe j.
Constraint i <= j.
Context
  {sorts' : I → Type@{j}}
  (operations' : Operations@{j} sorts' A)
.

(* Should really define morphisms including equations,
   then prove that this one is unique. *)

Definition initial_morphism_sorts : ∀ i, sorts i → sorts' i.
Admitted.

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


