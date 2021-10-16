Require Import List QArith.
Require Import BBSL.BB.
Import ListNotations.


Definition SetBB : Type := list BB.

Declare Scope SetBB.
Local Open Scope SetBB.

(* TODO: filter empty BB for efficiency *)
Fixpoint _BB_SBBintersection (p : BB) (ps accum : SetBB) : SetBB :=
  match ps with
  | nil => accum
  | cons q qs => _BB_SBBintersection p qs (cons (BBintersection p q) accum)
  end.

Fixpoint _SBBintersection (ps qs accum : SetBB) : SetBB :=
  match ps with
  | nil => accum
  | cons p ps' => _SBBintersection ps' qs (_BB_SBBintersection p qs nil ++ accum)
  end.

Definition SBBintersection (ps qs : SetBB) : SetBB :=
  _SBBintersection ps qs nil.

Definition SBBunion (ps qs : SetBB) : SetBB :=
  ps ++ qs.

Fixpoint _SetBBarea (ps accum : SetBB) (area : Q) : Q :=
  match ps with
  | nil => area
  | cons p qs =>
    let cs := _BB_SBBintersection p accum nil in
    let csarea := List.fold_right Qplus 0 (List.map BBarea cs) in
    _SetBBarea qs (cons p accum) (area + BBarea p - csarea)
  end.

Definition SetBBarea (ps : SetBB) : Q :=
  _SetBBarea ps nil 0.

Definition RAT (ps qs : SetBB) : Q :=
  SetBBarea ps / SetBBarea qs.
