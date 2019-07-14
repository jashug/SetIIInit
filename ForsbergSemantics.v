Require Import HoTT.Basics Coq.Unicode.Utf8.
Require Import HoTT.Types.Sum.
Require Import InductiveTypes.

(* Define semantics *)

Record Ctx@{i} : Type@{i+1} := {
  indices0 : Type@{i};
  indices1 : (indices0 → Type@{i}) → (indices0 → Type@{i});
  functor_indices1 : ∀ {Sorts0a Sorts0b : indices0 → Type@{i}},
    (∀ i0, Sorts0a i0 → Sorts0b i0) →
    (∀ i0, indices1 Sorts0a i0 → indices1 Sorts0b i0);
  operations0 : OpSpec@{i} indices0;
  operations1 : ∀ {Sorts0}, Operations@{i} Sorts0 operations0 →
                OpSpec@{i} {i0 : indices0 & indices1 Sorts0 i0 * Sorts0 i0};
  indices2 :
    ∀ {Sorts0},
    (∀ i0, indices1 Sorts0 i0 → Sorts0 i0 → Type@{i}) →
    Operations@{i} Sorts0 operations0 →
    ∀ i0, indices1 Sorts0 i0 → Type@{i};
  Indices : Type@{i} :=
    let pre_sorts := Initial.sorts operations0 in
    let pre_ops := Initial.operations operations0 in
    let good_sorts i0 i1 p
     := Initial.sorts (operations1 pre_ops) (i0; (i1, p)) in
    {i0 : indices0 &
    {i1 : indices1 pre_sorts i0 &
          indices2 good_sorts pre_ops i0 i1
    }};
}.
Arguments functor_indices1 _ {Sorts0a Sorts0b} H {i0} _.

Definition elim_Indices {Γ : Ctx} {Sorts0}
  (Γops : Operations Sorts0 Γ.(operations0)) (i : Γ.(Indices))
  : Γ.(indices1) Sorts0 i.1
  := Γ.(functor_indices1)
     (Initial.initial_morphism_sorts Γ.(operations0) Γops)
     i.2.1.

Record TySort@{i} (Γ : Ctx@{i}) : Type@{i+1} := {
  ix0 : Type@{i};
  ix1 : (Γ.(indices0) → Type@{i}) → (ix0 → Type@{i});
  functor_ix1 : ∀ {Sorts0a Sorts0b : Γ.(indices0) → Type@{i}},
    (∀ i0, Sorts0a i0 → Sorts0b i0) →
    (∀ i0, ix1 Sorts0a i0 → ix1 Sorts0b i0);
  ix2 : ∀ {Sorts0},
    (∀ i0, Γ.(indices1) Sorts0 i0 → Sorts0 i0 → Type@{i}) →
    Operations@{i} Sorts0 Γ.(operations0) →
    ∀ i0, ix1 Sorts0 i0 → Type@{i};
}.
Arguments ix0 {Γ} _.
Arguments ix1 {Γ} _ Sorts0 i0.
Arguments functor_ix1 {Γ} _ {Sorts0a Sorts0b} H {i0} _.
Arguments ix2 {Γ} _ {Sorts0} Sorts1 ops0 i0 i1.

Record TyOp@{i} (Γ : Ctx@{i}) : Type@{i+1} := {
  ops0 : OpSpec@{i} Γ.(indices0);
  ops1 : ∀ {Sorts0},
    Operations@{i} Sorts0 Γ.(operations0) →
    Operations@{i} Sorts0 ops0 →
    OpSpec@{i} {i0 : Γ.(indices0) & Γ.(indices1) Sorts0 i0 * Sorts0 i0};
}.
Arguments ops0 {Γ} _.
Arguments ops1 {Γ} _ {Sorts0} _ _.

(* For now, ignore infinitary arguments/indices *)
Definition Data (Γ : Ctx) := Indices Γ.

Definition data_to_op {Γ : Ctx} (A : Data Γ) : TyOp Γ
  := {|
        ops0 := el A.1;
        ops1 Sorts0 Γops pt := el (A.1; (elim_Indices Γops A, pt));
     |}.

Definition emp : Ctx
  := {|
        indices0 := Unit;
        indices1 Sorts0 i0 := Unit;
        functor_indices1 _ _ H i0 i1 := tt; (* maybe idmap instead? *)
        operations0 := op_skip;
        operations1 Sorts0 ops0 := op_skip;
        indices2 Sorts0 Sorts1 ops0 i0 i1 := Unit;
     |}.

Definition ext_sort (Γ : Ctx) (A : TySort Γ) : Ctx
  := {|
        indices0 := Γ.(indices0) + A.(ix0);
        indices1 Sorts0 i0 :=
          match i0 with
          | inl iΓ => Γ.(indices1) (Sorts0 o inl) iΓ
          | inr iA => A.(ix1) (Sorts0 o inl) iA
          end;
        functor_indices1 _ _ H i0 :=
          match i0 with
          | inl iΓ => Γ.(functor_indices1) (H o inl)
          | inr iA => A.(functor_ix1) (H o inl)
          end;
        operations0 := functor_OpSpec inl Γ.(operations0);
        operations1 Sorts0 ops0 := functor_OpSpec
          (λ i, (inl i.1; (fst i.2, snd i.2)))
          (Γ.(operations1) (Operations_compose ops0));
        indices2 Sorts0 Sorts1 ops0 i0 :=
          match i0 with
          | inl iΓ => Γ.(indices2) (Sorts1 o inl) (Operations_compose ops0) iΓ
          | inr iA => A.(ix2) (Sorts1 o inl) (Operations_compose ops0) iA
          end;
     |}.

Definition ext_op (Γ : Ctx) (A : TyOp Γ) : Ctx
  := {|
        indices0 := Γ.(indices0);
        indices1 := Γ.(indices1);
        functor_indices1 _ _ := Γ.(functor_indices1);
        operations0 := op_prod Γ.(operations0) A.(ops0);
        operations1 Sorts0 ops0 := op_prod
          (Γ.(operations1) (fst ops0))
          (A.(ops1) (fst ops0) (snd ops0));
        indices2 Sorts0 Sorts1 ops0 := Γ.(indices2) Sorts1 (fst ops0);
     |}.

Definition ext_data (Γ : Ctx) (A : Data Γ) : Ctx
  := ext_op Γ (data_to_op A).

Definition u {Γ} : TySort Γ
  := {|
        ix0 := Unit;
        ix1 _ i0 := Unit;
        functor_ix1 _ _ H i0 i1 := tt; (* maybe idmap instead? *)
        ix2 Sorts0 Sorts1 ops0 i0 i1 := Unit;
     |}.

Definition ind_ix {Γ} (A : Data Γ) (B : TySort (ext_data Γ A)) : TySort Γ
  := {|
        ix0 := B.(ix0);
        ix1 Sorts0 i0 := Sorts0 A.1 * B.(ix1) Sorts0 i0;
        functor_ix1 _ _ H i0 i1 := (H _ (fst i1), B.(functor_ix1) H (snd i1));
        ix2 Sorts0 Sorts1 ops0 i0 i1 :=
          {g : Sorts1 A.1 (elim_Indices ops0 A) (fst i1) &
           B.(ix2) Sorts1 (ops0, fst i1) i0 (snd i1)};
     |}.

Definition nonind_ix {Γ} (A : Type@{i}) (* `{IsTrunc 1 A} *) (B : A → TySort Γ)
  : TySort Γ
  := {|
        ix0 := {a : A & (B a).(ix0)};
        ix1 Sorts0 i0 := (B i0.1).(ix1) Sorts0 i0.2;
        functor_ix1 _ _ H i0 i1 := (B i0.1).(functor_ix1) H i1;
        ix2 Sorts0 Sorts1 ops0 i0 i1 := (B i0.1).(ix2) Sorts1 ops0 i0.2 i1;
     |}.

Definition el {Γ} (i : Indices Γ) : TyOp Γ
  := data_to_op i.

Definition ind_arg {Γ} (A : Data Γ) (B : TyOp (ext_data Γ A)) : TyOp Γ
  := {|
        ops0 := ind_arg (inc A.1) (B.(ops0) : OpSpec Γ.(indices0));
        ops1 Sorts0 Γops op :=
          nonind_arg (Sorts0 A.1) (λ p,
          ind_arg (inc (A.1; (elim_Indices Γops A, p)))
          (B.(ops1) (Γops, p) (op p)));
     |}.

Definition nonind_arg {Γ} (A : Type@{i}) (* `{IsHSet A} *) (B : A → TyOp Γ)
  : TyOp Γ
  := {|
        ops0 := nonind_arg A (λ a, (B a).(ops0));
        ops1 Sorts0 ops0Γ ops0 :=
          nonind_arg A (λ a, (B a).(ops1) ops0Γ (ops0 a));
     |}.
