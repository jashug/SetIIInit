Require Import HoTT.Basics Coq.Unicode.Utf8.

Module Import Par.
(* Partial elements *)
Definition Par@{i j | i < j} (Y : Type@{j}) : Type@{j}
  := sig@{j j} (λ X : Type@{i}, X → Y).
Definition Build_Par@{i j} {Y : Type@{j}}
  : ∀ X : Type@{i}, (X → Y) → Par@{i j} Y
  := fun X f => (X ; f).
Definition ret@{i j} {Y : Type@{j}} (y : Y) : Par@{i j} Y
  := (Unit : Type@{i} ; λ _, y).
Definition bind@{i j} {Y1 Y2 : Type@{j}}
    (x : Par@{i j} Y1) (f : Y1 → Par@{i j} Y2)
  : Par@{i j} Y2
  := Build_Par {x1 : x.1 & (f (x.2 x1)).1} (λ x12, (f (x.2 x12.1)).2 (x12 .2)).
Definition map@{i j} {Y1 Y2 : Type@{j}} (x : Par@{i j} Y1) (f : Y1 → Y2)
  : Par@{i j} Y2
  := Build_Par x.1 (f o x.2).
Definition bind_map@{i j} {Y1 Y3 : Type@{j}} {Y2 : Y1 → Type@{j}}
    (x : Par@{i j} Y1) (f : ∀ y1, Par@{i j} (Y2 y1)) (m : ∀ y1, Y2 y1 → Y3)
  : Par@{i j} Y3
  := bind x (λ y1, map (f y1) (m y1)).
Definition assume (Y : Type@{i}) : Par@{i j} Y := Build_Par Y idmap.
Definition prod {X : Type@{i}} {Y : X → Type@{j}} (f : ∀ x, Par@{i j} (Y x))
  : Par@{i j} (∀ x, Y x)
  := Build_Par@{i j} (∀ x, (f x).1) (λ fx x, (f x).2 (fx x)).
End Par.