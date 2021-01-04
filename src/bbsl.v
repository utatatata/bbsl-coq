Require Import Classical_Pred_Type Reals ROrderedType ConstructiveCauchyReals String Bool List FMapList OrderedTypeEx Ensembles Bool Ltac2.Option.
Import ListNotations.

Declare Scope Interval_scope.

Local Open Scope Interval_scope.
Local Open Scope bool_scope.
Local Open Scope R_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


Definition Interval : Type := R * R.


Definition lower (i : Interval) : R :=
  match i with
  | (l, _) => l
  end.

Definition upper (i : Interval) : R :=
  match i with
  | (_, u) => u
  end.

Definition IisEmpty (i : Interval) : Prop :=
  lower i > upper i.

Definition contains (v : R) (i : Interval) : Prop :=
  (lower i <= v /\ v <= upper i)%R.

Lemma contains_lower : forall i, ~IisEmpty i -> contains (lower i) i.
Proof.
  intros. unfold contains. unfold IisEmpty in H.
  split. r_order. r_order.
Qed.

Lemma contains_upper : forall i, ~IisEmpty i -> contains (upper i) i.
Proof.
  intros. unfold contains. unfold IisEmpty in H.
  split. r_order. r_order.
Qed.

Definition width (i : Interval) : R :=
  upper i - lower i.

Definition Ilt (i0 i1 : Interval) : Prop :=
  upper i0 < lower i1.

Definition Igt (i0 i1 : Interval) : Prop :=
  upper i1 < lower i0.

Lemma Ilt_gt_dual : forall i0 i1, Ilt i0 i1 <-> Igt i1 i0.
Proof.
  intros.
  unfold Ilt. unfold Igt. unfold iff.
  split. trivial. trivial.
Qed.

Definition Isubset (i0 i1 : Interval) : Prop :=
  lower i1 < lower i0 /\ upper i0 < upper i1.

Definition Isupset (i0 i1 : Interval) : Prop :=
  lower i0 < lower i1 /\ upper i1 < upper i0.

Lemma Isubset_supset_dual : forall i0 i1, Isubset i0 i1 <-> Isupset i1 i0.
Proof.
  intros.
  unfold Isubset. unfold Isupset. unfold iff.
  split. trivial. trivial.
Qed.

Definition Ieq (i0 i1 : Interval) : Prop :=
  lower i0 = lower i1 /\ upper i0 = upper i1.

Definition Ioverlap (i0 i1 : Interval) : Prop :=
  exists r : R, contains r i0 /\ contains r i1.

Lemma Ioverlap_comm : forall i0 i1, Ioverlap i0 i1 <-> Ioverlap i1 i0.
Proof.
  intros.
  unfold Ioverlap. unfold iff.
  split.
  - intros. destruct H.
    rewrite (and_comm (contains x i0) (contains x i1)) in H.
    eexists x. assumption.
  - intros. destruct H. 
    rewrite (and_comm (contains x i1) (contains x i0)) in H.
    eexists x. assumption.
Qed.

Lemma Ilt_not_overlap : forall i0 i1,
  Ilt i0 i1 -> ~Ioverlap i0 i1.
Proof.
  unfold Ilt. unfold Ioverlap. unfold contains. unfold not.
  intros.
  destruct H0. destruct H0. destruct H0. destruct H1. r_order.
Qed.

Lemma Igt_not_overlap : forall i0 i1,
  Igt i0 i1 -> ~Ioverlap i0 i1.
Proof.
  intros i0 i1.
  rewrite <- (Ilt_gt_dual i1 i0).
  rewrite (Ioverlap_comm i0 i1).
  apply (Ilt_not_overlap i1 i0).
Qed.

Lemma Ioverlap_not_lt : forall i0 i1, Ioverlap i0 i1 -> ~Ilt i0 i1.
Proof.
  unfold Ilt. unfold Ioverlap. unfold contains. unfold not.
  intros.
  destruct H. destruct H. destruct H. destruct H1.
  r_order.
Qed.

Lemma Ioverlap_not_gt : forall i0 i1, Ioverlap i0 i1 -> ~Igt i0 i1.
Proof.
  intros i0 i1.
  rewrite <- (Ilt_gt_dual i1 i0).
  rewrite (Ioverlap_comm i0 i1).
  apply (Ioverlap_not_lt i1 i0).
Qed.

Lemma Ilt_antisymm : forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Ilt i0 i1 -> ~Ilt i1 i0.
Proof.
  unfold Ilt. intros.
  unfold IisEmpty in H. destruct H.
  r_order.
Qed.

Lemma Igt_antisymm : forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Igt i0 i1 -> ~Igt i1 i0.
Proof.
  intros i0 i1.
  rewrite <- (Ilt_gt_dual i1 i0).
  rewrite (and_comm (~IisEmpty i0) (~IisEmpty i1)).
  apply (Ilt_antisymm i1 i0).
Qed.

Lemma Ilt_not_gt : forall i0 i1,
  ~IisEmpty i0 /\ ~IisEmpty i1 -> Ilt i0 i1 -> ~Igt i0 i1.
Proof.
  intros i0 i1.
  rewrite <- (Ilt_gt_dual i1 i0).
  apply (Ilt_antisymm i0 i1).
Qed.

Lemma Igt_not_lt : forall i0 i1,
  ~IisEmpty i0 /\ ~IisEmpty i1 -> Igt i0 i1 -> ~Ilt i0 i1.
Proof.
  intros i0 i1.
  rewrite (Ilt_gt_dual i0 i1).
  rewrite <- (Ilt_gt_dual i1 i0).
  rewrite (and_comm (~IisEmpty i0) (~IisEmpty i1)).
  apply (Ilt_not_gt i1 i0).
Qed.

Lemma Isubset_overlap :
  forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Isubset i0 i1 -> Ioverlap i0 i1.
Proof.
  unfold IisEmpty. unfold Isubset. unfold Ioverlap. unfold contains.
  intros. destruct H. destruct H0.
  eexists (lower i0). split.
  - split. r_order. r_order.
  - split. r_order. r_order.
Qed.

Lemma Isupset_overlap :
  forall i0 i1, ~IisEmpty i0 /\ ~IisEmpty i1 -> Isupset i0 i1 -> Ioverlap i0 i1.
Proof.
  intros i0 i1.
  rewrite <- (Isubset_supset_dual i1 i0).
  rewrite (Ioverlap_comm i0 i1).
  rewrite (and_comm (~IisEmpty i0) (~IisEmpty i1)).
  apply (Isubset_overlap i1 i0).
Qed.

(* TODO
Lemma not_lt_gt_overlap : forall i0 i1, ~Ilt i0 i1 /\ ~Igt i0 i1 -> Ioverlap i0 i1.
Proof.
  unfold Ilt. unfold Igt. unfold Ioverlap. unfold contains.
  intros.
  destruct H. eexists.
  split. split. 
  unfold Ioverlap.
*)

(* TODO
Lemma not_overlap_lgt_gt : forall i0 i1, ~Ioverlap i0 i1 -> Ilt i0 i1 \/ Igt i0 i1.
Proof.
   unfold Ioverlap. unfold contains. unfold Ilt. unfold Igt. intros.
   rewrite not_ex_all_not.
   left.
   destruct H.
  left.
  apply (Ioverlap_not_lt i0 i1 H).
  rewrite (Ioverlap_not_lt i0 i1) in H.
*)

(* TODO
Lemma exclusive_Ilt_Ioverlap : forall i0 i1, Ilt i0 i1 <-> ~Ioverlap i0 i1.
*)

Definition Iintersection (i0 i1 : Interval) : Interval :=
  (Rmax (lower i0) (lower i1), Rmin (upper i0) (upper i1)).

(* TODO
Lemma Iempty_intersection : forall i0 i1, IisEmpty i0 -> IisEmpty (Iintersection i0 i1).
Proof.
  unfold IisEmpty. unfold Iintersection. simpl. intros.
  apply (Rmax_Rle (lower i0) (lower i1) (Rmin (upper i0) (upper i1))).
*)

Definition BB : Type := Interval * Interval.

Definition projx (bb : BB) : Interval :=
  match bb with
  | (x, _) => x
  end.

Definition projy (bb : BB) : Interval :=
  match bb with
  | (_, y) => y
  end.

Definition projxl (bb : BB) : R :=
  lower (projx bb).

Definition projxu (bb : BB) : R :=
  upper (projx bb).

Definition projyl (bb : BB) : R :=
  lower (projy bb).

Definition projyu (bb : BB) : R :=
  upper (projy bb).

Definition BBisEmpty (bb : BB) : Prop :=
  IisEmpty (projx bb) \/ IisEmpty (projy bb).

Definition BBoverlap (bb0 bb1 : BB) : Prop :=
  Ioverlap (projx bb0) (projx bb1) /\ Ioverlap (projy bb0) (projy bb1).

Definition BBintersection (bb0 bb1 : BB) : BB :=
  (Iintersection (projx bb0) (projx bb1), Iintersection (projy bb0) (projy bb1)).

Definition BBarea (bb : BB) : R :=
  Rmax 0 (width (projx bb) * width (projy bb)).

Definition SetBB : Type := list BB.

(*Lemma foo : forall sbb, (exist bb, In bb sbb /\ isEmpty bb) -> isEmpty sbb. *) 

(* TODO: filter empty BB for efficiency *)
Fixpoint _BB_SBBintersection (bb : BB) (sbb accum : SetBB) : SetBB :=
  match sbb with
  | nil => accum
  | cons bb' sbb' => _BB_SBBintersection bb sbb' (cons (BBintersection bb bb') accum)
  end.

Fixpoint _SBBintersection (sbb0 sbb1 accum : SetBB) : SetBB :=
  match sbb0 with
  | nil => accum
  | cons bb sbb => _SBBintersection sbb sbb1 (_BB_SBBintersection bb sbb1 nil ++ accum)
  end.

Definition SBBintersection (sbb0 sbb1 : SetBB) : SetBB :=
  _SBBintersection sbb0 sbb1 nil.

Definition SBBunion (sbb0 sbb1 : SetBB) : SetBB :=
  sbb0 ++ sbb1.

Definition BB2area (bb0 bb1 : BB) : R :=
  BBarea bb0 + BBarea bb1 - BBarea (BBintersection bb0 bb1).

Fixpoint _SetBBarea (sbb accum : SetBB) (area : R) : R :=
  match sbb with
  | nil => area
  | cons bb sbb' =>
    let sbb'' := _BB_SBBintersection bb accum nil in
    let sbb''area := List.fold_right Rplus 0 (List.map BBarea sbb'') in
    _SetBBarea sbb' (cons bb accum) (area + BBarea bb - sbb''area)
  end.

(* TODO wrong algorithm *)
Definition SetBBarea (sbb : SetBB) : R :=
  _SetBBarea sbb nil 0.

(* TODO what happen at 0-divided ? *)
Definition RAT (sbb0 sbb1 : SetBB) : R :=
  SetBBarea sbb0 / SetBBarea sbb1.

Inductive SBBexp : Set :=
  | EXP_SBBvar (x : string)
  | EXP_SBBintersection (sbb0 sbb1 : SBBexp) | EXP_SBBunion (sbb0 sbb1 : SBBexp).

Inductive BBexp : Set :=
  | EXP_BBvar (x : string)
  (* 画像全体のBB *)
  | EXP_BBimg.

Inductive Iexp : Set :=
  | EXP_Ivar (x : string)
  | EXP_projx (bb : BBexp) | EXP_projy (bb : BBexp)
  | EXP_Iintersection (i0 i1 : Iexp).

Inductive Rexp : Set :=
  | EXP_Rvar (x : string)
  | EXP_width (i : Iexp) | EXP_RAT (sbb0 sbb1 : SBBexp)
  | EXP_projxl (bb : BBexp) | EXP_projxu (bb : BBexp)
  | EXP_projyl (bb : BBexp) | EXP_projyu (bb : BBexp).

Inductive Bexp : Set :=
  | EXP_Bvar (x : string)
  | EXP_not (b : Bexp) | EXP_and (b0 b1 : Bexp) | EXP_or (b0 b1 : Bexp)
  | EXP_BBoverlap (bb0 bb1 : BBexp)
  | EXP_Ilt (i0 i1 : Iexp) | EXP_Igt (i0 i1 : Iexp) | EXP_Ieq (i0 i1 : Iexp)
  | EXP_Ioverlap (i0 i1 : Iexp) | EXP_Isubset (i0 i1 : Iexp) | EXP_Isupset (i0 i1 : Iexp)
  | EXP_Rlt (r0 r1 : Rexp) | EXP_Rgt (r0 r1 : Rexp) | EXP_Req (r0 r1 : Rexp).

Definition Cond : Set := Bexp.

Inductive Def : Set :=
  | DEF_SBB (x : string) (sbb : SBBexp)
  | DEF_BB (x : string) (bb : BBexp)
  | DEF_I (x : string) (i : Iexp)
  | DEF_R (x : string) (r : Rexp)
  | DEF_B (x : string) (b : Bexp).

Definition LetBexp : Set := list Def * Bexp.

Definition Case : Set := string * LetBexp.

Definition Spec : Set := Cond * list Case.

Module Import M := FMapList.Make(String_as_OT).

Inductive Value : Type :=
  | Vb (x : Prop) | Vr (x : R) | Vi (x : Interval)
  | Vbb (x : BB) | Vsbb (x : SetBB).

Definition Env := M.t Value.

Fixpoint Asbb (expr : SBBexp) (env : Env) : option SetBB :=
  match expr with
  | EXP_SBBvar s =>
    match find s env with
    | Some (Vsbb sbb) => Some sbb
    | _ => None
    end
  | EXP_SBBintersection sbb_expr0 sbb_expr1 =>
    match Asbb sbb_expr0 env, Asbb sbb_expr1 env with
    | Some sbb0, Some sbb1 => Some (SBBintersection sbb0 sbb1)
    | _, _ => None
    end
  | EXP_SBBunion sbb_expr0 sbb_expr1 =>
    match Asbb sbb_expr0 env, Asbb sbb_expr1 env with
    | Some sbb0, Some sbb1 => Some (SBBunion sbb0 sbb1)
    | _, _ => None
    end
  end.

Definition Abb (expr : BBexp) (env : Env) : option BB :=
  match expr with
  | EXP_BBimg =>
    match find "IMG" env with
    | Some (Vbb bb) => Some bb
    | _ => None
    end
  | EXP_BBvar s =>
    match find s env with
    | Some (Vbb bb) => Some bb
    | _ => None
    end
  end.

Fixpoint Ai (expr : Iexp) (env : Env) : option Interval :=
  match expr with
  | EXP_Ivar s =>
    match find s env with
    | Some (Vi i) => Some i
    | _ => None
    end
  | EXP_projx bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projx bb)
    | None => None
    end
  | EXP_projy bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projy bb)
    | None => None
    end
  | EXP_Iintersection i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Iintersection i0 i1)
    | _, _ => None
    end
  end.

Definition Ar (expr : Rexp) (env : Env) : option R :=
  match expr with
  | EXP_Rvar s =>
    match find s env with
    | Some (Vr r) => Some r
    | _ => None
    end
  | EXP_width i_expr =>
    match Ai i_expr env with
    | Some i => Some (width i)
    | None => None
    end
  | EXP_RAT sbb_expr0 sbb_expr1 =>
    match Asbb sbb_expr0 env, Asbb sbb_expr1 env with
    | Some sbb0, Some sbb1 => Some (RAT sbb0 sbb1)
    | _, _ => None
    end
  | EXP_projxl bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projxl bb)
    | None => None
    end
  | EXP_projxu bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projxu bb)
    | None => None
    end
  | EXP_projyl bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projyl bb)
    | None => None
    end
  | EXP_projyu bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (projyu bb)
    | None => None
    end
  end.

Fixpoint B (expr : Bexp) (env : Env) : option Prop :=
  match expr with
  | EXP_Bvar s =>
    match find s env with
    | Some (Vb b) => Some b
    | _ => None
    end
  | EXP_not b_expr =>
    match B b_expr env with
    | Some b => Some (not b)
    | None => None
    end
  | EXP_and b_expr0 b_expr1 =>
    match B b_expr0 env, B b_expr1 env with
    | Some b0, Some b1 => Some (b0 /\ b1)
    | _, _ => None
    end
  | EXP_or b_expr0 b_expr1 =>
    match B b_expr0 env, B b_expr1 env with
    | Some b0, Some b1 => Some (b0 \/ b1)
    | _, _ => None
    end
  | EXP_BBoverlap bb_expr0 bb_expr1 =>
    match Abb bb_expr0 env, Abb bb_expr1 env with
    | Some bb0, Some bb1 => Some (BBoverlap bb0 bb1)
    | _, _ => None
    end
  | EXP_Ilt i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Ilt i0 i1)
    | _, _ => None
    end
  | EXP_Igt i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Igt i0 i1)
    | _, _ => None
    end
  | EXP_Ieq i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Ieq i0 i1)
    | _, _ => None
    end
  | EXP_Ioverlap i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Ioverlap i0 i1)
    | _, _ => None
    end
  | EXP_Isubset i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Isubset i0 i1)
    | _, _ => None
    end
  | EXP_Isupset i_expr0 i_expr1 =>
    match Ai i_expr0 env, Ai i_expr1 env with
    | Some i0, Some i1 => Some (Isupset i0 i1)
    | _, _ => None
    end
  | EXP_Rlt r_expr0 r_expr1 =>
    match Ar r_expr0 env, Ar r_expr1 env with
    | Some r0, Some r1 => Some (r0 < r1)%R
    | _, _ => None
    end
  | EXP_Rgt r_expr0 r_expr1 =>
    match Ar r_expr0 env, Ar r_expr1 env with
    | Some r0, Some r1 => Some (r0 < r1)%R
    | _, _ => None
    end
  | EXP_Req r_expr0 r_expr1 =>
    match Ar r_expr0 env, Ar r_expr1 env with
    | Some r0, Some r1 => Some (r0 = r1)
    | _, _ => None
    end
  end.

Definition Ccond : Cond -> Env -> option Prop := B.

Definition Cdef (def : Def) (env : Env) : option Env :=
  match def with
  | DEF_SBB s sbb_expr =>
    match Asbb sbb_expr env with
    | Some sbb => Some (add s (Vsbb sbb) env)
    | _ => None
    end
  | DEF_BB s bb_expr =>
    match Abb bb_expr env with
    | Some bb => Some (add s (Vbb bb) env)
    | _ => None
    end
  | DEF_I s i_expr =>
    match Ai i_expr env with
    | Some i => Some (add s (Vi i) env)
    | _ => None
    end
  | DEF_R s r_expr =>
    match Ar r_expr env with
    | Some r => Some (add s (Vr r) env)
    | _ => None
    end
  | DEF_B s b_expr =>
    match B b_expr env with
    | Some b => Some (add s (Vb b) env)
    | _ => None
    end
  end.

Fixpoint _Cdefs (defs : list Def) (env : Env) : option Env :=
  match defs with
  | nil => Some env
  | cons def defs' =>
    match Cdef def env with
    | Some env' => _Cdefs defs' env'
    | _ => None
    end
  end.

Definition CletBexp (_let : LetBexp) (env : Env) : option Prop :=
  match _let with
  | (defs, b_expr) =>
    match _Cdefs defs env with
    | Some env' => B b_expr env'
    | _ => None
    end
  end.

Definition Ccase (case : Case) (env : Env) : option (string * Prop) :=
  match case with
  | (l, letBexp) =>
    match CletBexp letBexp env with
    | Some b => Some (l, b)
    | _ => None
    end
  end.

Fixpoint _Ccases (cases : list Case) (env : Env) (accum : list (string * Prop)) : option (list (string * Prop)) :=
  match cases with
  | nil => Some accum
  | cons case cases' =>
    match Ccase case env with
    | Some lb => _Ccases cases' env (cons lb accum)
    | _ => None
    end
  end.

Definition Cspec (spec : Spec) (env : Env) : option (list (string * Prop)) :=
  match spec with
  | (cond, cases) =>
    match Ccond cond env, _Ccases cases env nil with
    | Some b, Some lbs => Some (List.map
          (fun lb => match lb with (l, b') => (l, b /\ b') end)
          lbs)
    | _, _ => None
    end
  end.

Definition testEnv := add "r1" (Vr 1) (add "r0" (Vr 0) (empty Value)).

Lemma foo : B (EXP_Rlt (EXP_Rvar "r0") (EXP_Rvar "r1")) testEnv
  = match Ar (EXP_Rvar "r0") testEnv, Ar (EXP_Rvar "r1") testEnv with
    | Some r0, Some r1 => Some (r0 < r1)
    | _, _ => None
  end.
Proof.
  simpl. trivial.
Qed.











Inductive interval : Type :=
  I (l u : R).

Inductive bb : Type :=
  BB (x y : interval).

Inductive setbbexpr :=
  | SBBcon (x : Ensemble bb) | SBBvar (s : string)
  | SBBintersection (x y : setbbexpr)
  | SBBunion (x y : setbbexpr).

Definition bb_intersection (a b : bb) :=
  match a, b with
  | BB ax ay, BB bx by_ =>
    if ~(ioverlap ax bx) \/ ~(ioverlap ay by_) then
      0
    else (Rabs (w ax) (w bx)) * (Rabs (w ay) (w by_))
  end.

Inductive bbexpr :=
  | BBcon (x : bb) | BBvar (s : string).

Inductive iexpr :=
  | Icon (x : interval) | Ivar (s : string)
  | Iintersection (i0 i1 : iexpr)
  | Proj_x (bb : bbexpr) | Proj_y (bb : bbexpr).

Inductive rexpr :=
  | Rcon (x : R) | Rvar (s : string)
  | W (i : iexpr)
  (*
  | RAT (sbb0 sbb1 : setbbexpr)
  *).

Inductive bexpr :=
  | Bcon (x : bool) | Bvar (s : string)
  | And (b0 b1 : bexpr) | Or (b0 b1 : bexpr)
  | Not (b : bexpr)
  (*
  | Req (r0 r1 : rexpr)
  | Ieq (i0 i1 : iexpr)
  *)
  | Rlt (r0 r1 : rexpr)
  | Ilt (i0 i1 : iexpr)
  | Ioverlap (i0 i1 : iexpr)
  (*
  | BBoverlap (bb0 bb1 : bbexpr)
  | Iincluded (i0 i1 : iexpr)
  *).

Inductive condexpr :=
  Cond (b : bexpr).

(*Inductive type : Type := Typreal | Typinterval | Typbb | Typbool.*)

Inductive atomexpr : Type :=
  | Atmreal (r : rexpr)
  | Atminterval (i : iexpr)
  | Atmbb (bb : bbexpr)
  | Atmbool (b : bexpr).

Inductive sbstexpr :=
  Sbst (s : string) (*(t : type)*) (a : atomexpr).

Inductive caseexpr :=
  Case (l : string) (sbsts : list sbstexpr) (b : bexpr).

Inductive imgexpr :=
  Img (cond : condexpr) (cases : list caseexpr).


Module Import M := FMapList.Make(String_as_OT).

Inductive value : Type := Vbool (x : Prop) | Vreal (x : R) | Vinterval (x : interval) | Vbb (x : bb).

Definition env := M.t value.

Definition Abb (expr : bbexpr) (e : env) : option bb :=
  match expr with
  | BBcon bb => Some bb
  | BBvar s =>
    match find s e with
    | Some (Vbb bb) => Some bb
    | _ => None
    end
  end.

Fixpoint Ainterval (expr : iexpr) (e : env) : option interval := match expr with | Icon i => Some i
  | Ivar s =>
    match find s e with
    | Some (Vinterval i) => Some i
    | _ => None
    end
  | Iintersection iexpr0 iexpr1 =>
    match Ainterval iexpr0 e, Ainterval iexpr1 e with
    | Some (I i0l i0u), Some (I i1l i1u) => Some (I (Rmax i0l i1l) (Rmin i0u i1u))
    | _,_ => None
    end
  | Proj_x bb =>
    match Abb bb e with
    | Some (BB x y) => Some x
    | _ => None
    end
  | Proj_y bb =>
    match Abb bb e with
    | Some (BB x y) => Some y
    | _ => None
    end
  end.

Definition Areal (expr : rexpr) (e : env) : option R :=
  match expr with
  | Rcon r => Some r
  | Rvar s => 
    match find s e with
    | Some (Vreal r) => Some r
    | _ => None
    end
  | W i =>
    match Ainterval i e with
    | Some (I l u) => Some (u - l)
    | _ => None
    end
  end.

Fixpoint B (expr : bexpr) (e : env) : option Prop :=
  match expr with
  | Bcon b => Some (Is_true b)
  | Bvar s =>
    match find s e with
    | Some (Vbool t) => Some t
    | _ => None
    end
  | And b0 b1 =>
    match B b0 e, B b1 e with
    | Some t1, Some t2 => Some (t1 /\ t2)
    | _, _ => None
    end
  | Or b0 b1 =>
    match B b0 e, B b1 e with
    | Some t1, Some t2 => Some (t1 \/ t2)
    | _, _ => None
    end
  | Not b =>
    match B b e with
    | Some t => Some (~t)
    | _ => None
    end
  | Rlt r0 r1 =>
    match Areal r0 e, Areal r1 e with
    | Some x, Some y => Some (x < y)
    | _, _ => None
    end
  | Ilt i0 i1 =>
    match Ainterval i0 e, Ainterval i1 e with
    | Some (I i0l i0u), Some (I i1l i1u) => Some (i0u < i1l)
    | _, _ => None
    end
  | Ioverlap i0 i1 =>
    match Ainterval i0 e, Ainterval i1 e with
    | Some (I i0l i0u), Some (I i1l i1u) => Some (~(i0u < i1l \/ i1u < i0l))
    | _, _ => None
    end
  end.

Definition Ccond (expr : condexpr) (e : env) : option Prop :=
    match expr with
    | Cond b => B b e
    end.

Definition Csbst (expr : sbstexpr) (e : env) : option env :=
    match expr with
    | Sbst s a =>
      match a with
      | Atmreal r =>
        match Areal r e with
        | Some r => Some (add s (Vreal r) e)
        | _ => None
        end
      | Atminterval i =>
        match Ainterval i e with
        | Some i => Some (add s (Vinterval i) e)
        | _ => None
        end
      | Atmbb bb =>
        match Abb bb e with
        | Some bb => Some (add s (Vbb bb) e)
        | _ => None
        end
      | Atmbool b =>
        match B b e with
        | Some t => Some (add s (Vbool t) e)
        | _ => None
        end
      end
    end.

Fixpoint Csbsts (sbsts : list sbstexpr) (e : env) : option env :=
    match sbsts with
    | nil => Some e
    | cons sbst sbsts =>
      match Csbst sbst e with
      | Some e' => Csbsts sbsts e'
      | None => None
      end
    end.

Definition Ccase (expr : caseexpr) (e : env) : option (string * Prop) :=
  match expr with
  | Case l sbsts b =>
    match Csbsts sbsts e with
    | Some e' =>
      match B b e' with
      | Some t => Some (l, t)
      | None => None
      end
    | _ => None
    end
  end.

Fixpoint Ccases (cases : list caseexpr) (e : env) (accum : list (string * Prop))
  : option (list (string * Prop)) :=
  match cases with
  | nil => Some accum
  | cons case cases =>
    match Ccase case e with
    | Some (l, t) =>
      Ccases cases e (cons (l, t) accum)
    | None => None
    end
  end.

Definition Cimg (expr : imgexpr) (e : env) : option (list (string * Prop)) :=
    match expr with
    | Img cond cases =>
      match Ccond cond e with
      | Some t =>
        match Ccases cases e nil with
        | Some lts => Some (List.map
          (fun lt => match lt with (l, t') => (l, t /\ t') end)
          lts)
        | None => None
        end
      | None => None
      end
    end.

Definition ImgSample :=
  Img
    (Cond (Bvar "exists_vehicle_in_front"))
    [ Case
        "stop"
        [ Sbst "vehicle_in_front" (Atmbb (BBvar "vehicle_in_front"))
        ; Sbst "deceleration_interval" (Atminterval (Ivar "deceleration_interval"))
        ]
        (Ioverlap (Proj_y (BBvar "vehicle_in_front")) (Ivar "deceleration_interval"))
    ; Case
        "not_stop"
        [ Sbst "vehicle_in_front" (Atmbb (BBvar "vehicle_in_front"))
        ; Sbst "deceleration_interval" (Atminterval (Ivar "deceleration_interval"))
        ]
        (Ilt (Ivar "deceleration_interval") (Proj_y (BBvar "vehicle_in_front")))
    ].

(*
Goal forall (exists_vehicle : Prop) (vehicle : bb) (dec : interval),
  let e := (add "deceleration_interval" (Vinterval dec)
             (add "vehicle_in_front" (Vbb vehicle)
               (add "exists_vehicle_in_front" (Vbool exists_vehicle) (empty value))))
  in
  map_default
    (fun cases => List.In True (List.map (fun case => match case with (l, b) => b end) cases))
    False
    (Cimg ImgSample e).
Proof.
  intros.
  simpl.
*)

(*
Lemma foo : forall (A : Type) (x : option A) (y : A), x <> None -> Ltac2.Option.get x = y.
*)

Goal forall (exists_vehicle : Prop) (vehicle : bb) (dec : interval),
  let e := (add "deceleration_interval" (Vinterval dec)
             (add "vehicle_in_front" (Vbb vehicle)
               (add "exists_vehicle_in_front" (Vbool exists_vehicle) (empty value))))
  in
  Cimg ImgSample e <> None ->
  exists s : string, map (Cimg ImgSample e)
  match Cimg ImgSample e with
  | None => False
  | Some cases => List.In True (List.map (fun case => match case with (l, b) => b end) cases)
  end.

Goal forall (exists_vehicle : Prop) (vehicle : bb) (dec : interval),
  let e := (add "deceleration_interval" (Vinterval dec)
             (add "vehicle_in_front" (Vbb vehicle)
               (add "exists_vehicle_in_front" (Vbool exists_vehicle) (empty value))))
  in
  Cimg ImgSample e <> None ->
  match Cimg ImgSample e with
  | None => False
  | Some cases => List.In True (List.map (fun case => match case with (l, b) => b end) cases)
  end.
Proof.
  intros.
  rewrite H.
  simpl Cimg.
  destruct vehicle.
  destruct dec.

















Inductive proj_ii := X | Y.

Inductive proj_ri := XL | XU | YL | YU.

Inductive bbexpr : Type :=
  | BBcon (x : bb) | BBvar (s : string).

Inductive iexpr : Type :=
  | Icon (x : interval) | Ivar (s : string) | Icap (x y : iexpr)
  | Iproj (i : proj_ii) (x : bb).

Inductive rexpr : Type :=
  | Rcon (x : R) | Rvar (s : string)
  | Rw (x : interval)
  | Rproj (i : proj_ri) (x : bb).

Inductive bexpr : Type :=
  | Bcon (x : bool) | Bvar (s : string)
  | Band (x y : bexpr) | Bor (x y : bexpr ) | Bnot (x : bexpr)
  | Brlt (x y : rexpr) | Brgt (x y : rexpr) | Breq (x y : rexpr)
  | Bilt (x y : iexpr) | Bigt (x y : iexpr) | Bieq (x y : iexpr)
  | Bioverlap (x y : iexpr)
  | Bisub (x y : iexpr) | Bisup (x y : iexpr) | Bisubeq (x y :iexpr) | Bisupeq (x y : iexpr)
  | Bbboverlap (x y : bb).

Inductive type : Type := Typreal | Typbool | Typinterval | Typbb | TypsetBB.

Inductive bind_value : Type :=
  | BVreal (n : R) | BVvar (s : string)
  | BVfcall (fname : string) (i : proj_i) (values : list bind_value).

Inductive bind : Type := Bind (name : string) (type : type) (value : bind_value).

Inductive fundef : Type := Fdef (name : string) (args : list type) (ret : type).

Inductive blkexpr : Type :=
  | exfun (fundefs : list fundef)
  | case (name : string) (binds : list bind).

Inductive value : Type := Vbool (x : bool) | Vreal (x : R) | Vinterval (x : interval) | Vbb (x : bb).

Definition env := M.t value.


(*
Inductive interval : Type :=
  I (l u : R) : interval.

Notation "[ l , u ]" := (I l u) : Interval_scope.

Inductive iexpr :=
  Icon (x : interval)
  | Iintersection (x y : interval).

Definition eval_i (i : interval) : Ensemble R :=
  match i with
  | [l, u] => fun x => l <= x <= u
  end.

Inductive ilt (x y : interval) : Prop :=
  Ilt (l u : interval).

Definition eval_ilt (x : ilt) : Prop :=
  match x with
  | Ilt x y =>

Inductive igt (x y : interval) : Prop :=
  Igt (l u : interval).

Definition eval_igt (x y : interval) : Prop :=
  match x, y with
  | [xl, xu], [yl, yu] => yu <= xl
  end.

Inductive ieq (x y : interval) : Prop :=
  Ieq (l u : interval).

Definition eval_ieq (x y : interval) : Prop :=
  match x, y with
  | [xl, xu], [yl, yu] => xl = yl /\ xu = yu
  end.


Goal forall x y : interval, eval_ilt (ilt x y) = (forall x, In (eval_i x) x -> forall y, In (eval_i y) y -> x < y).

Lemma foo : forall x y : interval, ilt x y /\ ieq x y -> igt x y.
Proof.
  intros x y.
  intros lt_and_eq.
  elim lt_and_eq. intros lt eq.
  elim lt. 



Definition Iintersection : forall xl xu yl yu, [xl, xu] -> [yl, yu] -> [Rmax xl xu, Rmin xu yu].
  intros xl xu yl yu X Y.
  case X.

Definition Ioverlap : forall xl xu yl yu, [xl, xu] -> [yl, yu] -> Prop.
  intros X Y.
  apply (Intersection X Y) <> Empty_set R.
Defined.





Lemma disjoint : forall xl xu yl yu, xu < yl \/ yu < xl -> Intersection [xl, xu] [yl, yu] = Empty_set R.


Definition eval_i (l u : R) (i : Interval l u) :=

Inductive Interval (l u : R) : Set :=
  I : l <= u -> Interval l u.


Inductive Ilt (xl xu yl yu : R) (x : Interval xl xu) (y : Interval yl yu) : Set :=
  Ilt_intro 

Inductive Intersection (xl xu yl yu : R) (x : Interval xl xu) (y : Interval yl yu) : Set :=
  Intersection_intro : Intersection xl xu -> Intersection yl yu -> Intersection (Rmax xl xu)
*)



Lemma foo : forall x y : interval, eval_bexpr (Ioverlap x y) 




Inductive type : Type := Typreal | Typbool | Typinterval | Typbb | TypsetBB.

Inductive proj_i : Type := X | XL | XU | Y | YL | YU.

Inductive value : Type :=
  | Vvar (var : string) | Vreal (n : R)
  | Vproj_call (i : proj_i) (x : value)
  | Vrat_call (x : value)
  | Vw_call (x : value)
  | Vfun_call (args : list value)
  | Vintersection (x y : value)
  | Vunion (x y : value).

Inductive bind : Type := Bind (name : string) (type : type) (value : value).

Inductive condition : Type :=
  | Cnot (x y : condition)
  | Cand (x y : condition) | Cor (x y : condition)
  | Cforall (a : string) (A : type) (cond : condition)
  | Cexist (a : string) (A : type) (cond : condition)
  | Ceq (x y : value) | Clt (x y : value) | Cgt (x y : value)
  | Csub (x y : value) | Csup (x y : value) | Csubeq (x y : value) | Csupeq (x y : value)
  | None.

Inductive case : Type :=
  Case (name : string) (binds : list bind) (cond : condition).

Inductive fun_def : Type :=
  Fdef (name : string) (args : list type) (ret : type).

Inductive exfun : Type :=
  Exfun (exfuns : list fun_def).

Inductive spec : Type :=
  Spec (exfuns : exfun) (cases : case).

Inductive interval : Set := I (l u : R).

Notation "[ l , u ]" := (I l u) : Interval_scope.

Inductive bb : Set := BB (x y : interval).

Inductive setBB : Type := SetBB (bbs : Ensemble bb).

Inductive fvalue : Type :=
  | FVreal (n : R) | FVbool (b : bool) | FVinterval (i : interval)
  | FVbb (bb : bb) | FVsetBB (bbs : setBB).

Definition fenv := M.t fvalue.

Definition env := M.t value.

Definition eval_i (i : interval) : Ensemble R :=
  match i with
  | [l, u] => fun x => l <= x <= u
  end.

Definition eval_i_intersection (x y : interval) : Ensemble R :=
    match x, y with
    | [xl, xu], [yl, yu] => fun x => Rmax xl yl <= x <= Rmin xu yu
    end.


Definition eval_i_overlap (x y : interval) : Ensemble R :=
    match x, y with
    | [xl, xu], [yl, yu] => 
    end.

Fixpoint eval_value (v : value) :=

Fixpoint eval_exfun (blk : exfun) :=
  match blk with
  | Exfun fs =>
  end.

Fixpoint eval_spec


Inductive interval : Set := I (l u : R).

Notation "[ l , u ]" := (I l u) : Interval_scope.

Inductive bb : Set := BB (ix iy : interval).

Inductive proj_ii := X | Y.

Inductive proj_ri := XL | XU | YL | YU.

Inductive bbexpr : Type :=
  | BBcon (x : bb) | BBvar (s : string).

Inductive iexpr : Type :=
  | Icon (x : interval) | Ivar (s : string) | Icap (x y : iexpr)
  | Iproj (i : proj_ii) (x : bb).

Inductive rexpr : Type :=
  | Rcon (x : R) | Rvar (s : string)
  | Rw (x : interval)
  | Rproj (i : proj_ri) (x : bb).

Inductive bexpr : Type :=
  | Bcon (x : bool) | Bvar (s : string)
  | Band (x y : bexpr) | Bor (x y : bexpr ) | Bnot (x : bexpr)
  | Brlt (x y : rexpr) | Brgt (x y : rexpr) | Breq (x y : rexpr)
  | Bilt (x y : iexpr) | Bigt (x y : iexpr) | Bieq (x y : iexpr)
  | Bioverlap (x y : iexpr)
  | Bisub (x y : iexpr) | Bisup (x y : iexpr) | Bisubeq (x y :iexpr) | Bisupeq (x y : iexpr)
  | Bbboverlap (x y : bb).

Inductive type : Type := Typreal | Typbool | Typinterval | Typbb | TypsetBB.

Inductive bind_value : Type :=
  | BVreal (n : R) | BVvar (s : string)
  | BVfcall (fname : string) (i : proj_i) (values : list bind_value).

Inductive bind : Type := Bind (name : string) (type : type) (value : bind_value).

Inductive fundef : Type := Fdef (name : string) (args : list type) (ret : type).

Inductive blkexpr : Type :=
  | exfun (fundefs : list fundef)
  | case (name : string) (binds : list bind).

Inductive value : Type := Vbool (x : bool) | Vreal (x : R) | Vinterval (x : interval) | Vbb (x : bb).

Definition env := M.t value.

Fixpoint eval_i (i : interval) : Ensemble R :=
  match i with
  | [l, u] => fun x => l <= u /\ l <= x <= u
  end.

Fixpoint eval_iexpr (e : iexpr) (env : env) : option (Ensemble R) :=
  match e with
  | Icon i => Some (eval_i i)
  | Ivar s =>
    match find s env with
    | Some (Vinterval i) => Some (eval_i i)
    | _ => None
    end
  | Icap x y =>
    match eval_iexpr x env, eval_iexpr y env with
    | Some x', Some y' => Some (Intersection R x' y')
    | _, _ => None
    end
  end.

Fixpoint eval_rexpr (e : rexpr) (env : env) : option R :=
    match e with
    | Rcon x => Some x
    | Rvar s =>
      match find s env with
      | Some (Vreal x) => Some x
      | _ => None
      end
    | Rw [l, u] => Some (u - l) (* TODO *)
    | Rproj i (BB [xl, xu] [yl, yu]) =>
      match i with
      | _ => None
      end
    end.





Inductive term : Type :=
  | TmInterval : interval -> term
  | TmIintersection : interval -> interval -> term.

Fixpoint eval (tm : term) : Set :=
  match tm with
  | TmInterval [l, u] => { x | l <= x <= u }
  | TmIintersection [xl, xu] [yl, yu] => { x | Rmax xl yl <= x <= Rmin xu yu }
  end.

Definition foo : forall n m, n >3 /\ m > 3 -> R.
  intros.
  elim H. intros.
  apply (Rplus n m).
Defined.

Goal forall n m, foo n m > 6.

Inductive term : Set :=
  | TmR : R -> term
  | TmInterval : interval -> term
  | TmIintersection : interval -> interval -> term.


Inductive form : Set :=
  | Ilt : interval -> interval -> form
  | Lgt : interval -> interval -> form.

Definition Ilt (x y : interval) : Prop.
  elim x. intros xl xu isx.
  elim y. intros yl yu isy.
  apply (Rlt xu yl).
Defined.


Inductive interval : Set := Between : forall l u : R, l <= u -> interval.

Notation "[ l , u ]" := (Between l u) : Interval_scope.

Notation "x < y" := (Ilt x y) : Interval_scope.

Definition Igt (x y : interval) : Prop.
  elim x. intros xl xu isx.
  elim y. intros yl yu isy.
  apply (Rgt xl yu).
Defined.

Notation "x > y" := (Igt x y) : Interval_scope.

Definition Iintersection (x y : interval) : interval.
  elim x. intros xl xu isx.
  elim y. intros yl yu isy.
  apply (Between (Rmax xl yl) (Rmin xu yu)).


Inductive term : Set :=
  | TmR : R -> term
  | TmInterval : Interval -> term.

Inductive form : Set :=
  | 



Definition Interval := { '(l, u)  | l <= u }.

Definition mk_interval l u = 

Lemma foo : forall l u, 

Inductive Interval : Set :=
  between : forall l u, l <= u -> Interval.

Inductive interval : R -> R -> R -> Prop :=
  | between : forall l u, l <= u -> fun x => l <= x <= u.

Inductive Interval : R -> R -> Set :=
  | between : forall l u x, l <= x <= u -> Interval l u.

Notation "[ l , u ]" := (Interval l u) : Interval_scope.

Goal forall (l u : R), [l, u] -> l <= u.
Proof.
  intros.
  elim H.
  intros.
  apply r.
Qed.

Definition less : forall (xl xu yl yu : R), [xl, xu] -> [yl, yu] -> xu <= yl -> True.
Proof.
  intros.
  elim H.
  elim H0.
  intros.
  revert H1.
  

 :=
  fun XL XU YL YU x y => match (x, y) with
  | (between xl xu xis, between yl yu yis) => xis /\ yis /\ xu < yl
  end.

Inductive Interval : R -> R -> Set :=
  | between : forall l u, l <= u -> Interval l u.

Notation "[ l , u ]" := (Interval l u) : Interval_scope.


Definition less : forall (xl xu yl yu : R), [xl, xu] -> [yl, yu] -> Prop.
Proof.
  intros.
  elim H. intros.

Definition less : forall (l1 u1 l2 u2: R), [l1, u1] -> [l2, u2] -> forall x, 

