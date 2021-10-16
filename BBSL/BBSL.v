Require Import ClassicalDescription QArith OrdersFacts QOrderedType Qminmax GenericMinMax String Bool List FMapList OrderedTypeEx Bool.
Require Import Extra.Init.Logic Extra.QArith.QArith Extra.QArith.Qminmax.
Require Import BBSL.Interval BBSL.BB BBSL.SetBB.
Import ListNotations.

Local Open Scope string_scope.

Declare Scope BBSL_scope.
Local Open Scope BBSL_scope.



(******************** Expressions ********************)

(* Set of bounding box *)
Inductive SBBexp : Set :=
  | EXP_SBBvar (s : string)
  | EXP_SBBintersection (ps qs : SBBexp) | EXP_SBBunion (ps qs : SBBexp)
  | EXP_makeSBB (ps : list BBexp)
(* Bouding box *)
with BBexp : Set :=
  | EXP_BBvar (s : string)
  | EXP_makeBB (i j : Iexp)
  (* 画像全体のBB *)
  | EXP_BBimg
(* Interval *)
with Iexp : Set :=
  | EXP_Ivar (s : string)
  | EXP_projx (p : BBexp) | EXP_projy (p : BBexp)
  | EXP_Iintersection (i j : Iexp)
  | EXP_makeI (x y : Qexp)
(* Rational number *)
with Qexp : Set :=
  | EXP_Q (x: Q)
  | EXP_Qvar (s : string)
  | EXP_width (i : Iexp) | EXP_RAT (ps qs : SBBexp)
  | EXP_projl (i : Iexp) | EXP_proju (i : Iexp)
  | EXP_projxl (p : BBexp) | EXP_projxu (p : BBexp)
  | EXP_projyl (p : BBexp) | EXP_projyu (p : BBexp).

(* Boolean *)
Inductive Bexp : Set :=
  | EXP_Bvar (s : string)
  | EXP_not (a : Bexp) | EXP_and (a b : Bexp) | EXP_or (a b : Bexp)
  | EXP_BBeq (p q : BBexp)
  | EXP_BBoverlap (p q : BBexp)
  | EXP_BBsubset (p q : BBexp) | EXP_BBsupset (p q : BBexp)
  | EXP_BBsubseteq (p q : BBexp) | EXP_BBsupseteq (p q : BBexp)
  | EXP_Ilt (i j : Iexp) | EXP_Igt (i j : Iexp) | EXP_Ieq (i j : Iexp)
  | EXP_Ioverlap (i j : Iexp)
  | EXP_Iin (x : Qexp) (i : Iexp) | EXP_Iinrev (i : Iexp) (x : Qexp)
  | EXP_Isubset (i j : Iexp) | EXP_Isupset (i j : Iexp)
  | EXP_Isubseteq (i j : Iexp) | EXP_Isupseteq (i j : Iexp)
  | EXP_Qlt (x y : Qexp) | EXP_Qgt (x y : Qexp) 
  | EXP_Qeq (x y : Qexp)
  | EXP_Qle (x y : Qexp) | EXP_Qge (x y : Qexp) 
  | EXP_forall (bound : string) (ps : SBBexp) (a : Bexp)
  | EXP_exists (bound : string) (ps : SBBexp) (a : Bexp).



(******************** Syntax ********************)

(* Condition block *)
Inductive Cond : Set :=
  | CND_None
  | CND (a : Bexp).

Inductive Def : Set :=
  | DEF_SBB (s : string) (ps : SBBexp)
  | DEF_BB (s : string) (p : BBexp)
  | DEF_I (s : string) (i : Iexp)
  | DEF_Q (s : string) (x : Qexp)
  | DEF_B (s : string) (a : Bexp).

(* Case block *)
Definition Case : Set := string * list Def * Bexp.

(* Whole of syntax *)
Definition Spec : Set := Cond * list Case.



(******************** Semantic functions ********************)

Module Import M := FMapList.Make(String_as_OT).

Inductive Value : Type :=
  | Vb (A : Prop) | Vq (x : Q) | Vi (i : Interval)
  | Vbb (p : BB) | Vsbb (ps : SetBB).

(* Environment: a set of string(a variable name) and value pairs  *)
Definition Env := M.t Value.

(* Set of bounding box *)
Fixpoint Asbb (expr : SBBexp) (env : Env) : option SetBB :=
  match expr with
  | EXP_SBBvar s =>
    match find s env with
    | Some (Vsbb ps) => Some ps
    | _ => None
    end
  | EXP_SBBintersection expr_ps expr_qs =>
    match Asbb expr_ps env, Asbb expr_qs env with
    | Some ps, Some qs => Some (SBBintersection ps qs)
    | _, _ => None
    end
  | EXP_SBBunion expr_ps expr_qs =>
    match Asbb expr_ps env, Asbb expr_qs env with
    | Some ps, Some qs => Some (SBBunion ps qs)
    | _, _ => None
    end
  | EXP_makeSBB expr_ps =>
    List.fold_left (fun option_ps option_p =>
      match option_ps, option_p with
      | Some ps, Some p => Some (cons p ps)
      | _, _ => None
      end
    ) (List.map (fun expr_p => Abb expr_p env) expr_ps) (Some nil)
  end
(* Bounding box *)
with Abb (expr : BBexp) (env : Env) : option BB :=
  match expr with
  | EXP_BBimg =>
    match find "IMG" env with
    | Some (Vbb p) => Some p
    | _ => None
    end
  | EXP_BBvar s =>
    match find s env with
    | Some (Vbb p) => Some p
    | _ => None
    end
  | EXP_makeBB expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (i, j)
    | _, _ => None
    end
  end
(* Interval *)
with Ai (expr : Iexp) (env : Env) : option Interval :=
  match expr with
  | EXP_Ivar s =>
    match find s env with
    | Some (Vi i) => Some i
    | _ => None
    end
  | EXP_projx expr_p =>
    match Abb expr_p env with
    | Some p => Some (projx p)
    | None => None
    end
  | EXP_projy expr_p =>
    match Abb expr_p env with
    | Some p => Some (projy p)
    | None => None
    end
  | EXP_Iintersection expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Iintersection i j)
    | _, _ => None
    end
  | EXP_makeI expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x, y)
    | _, _ => None
    end
  end
(* Rational number *)
with Aq (expr : Qexp) (env : Env) : option Q :=
  match expr with
  | EXP_Q x => Some x
  | EXP_Qvar s =>
    match find s env with
    | Some (Vq x) => Some x
    | _ => None
    end
  | EXP_width expr_i =>
    match Ai expr_i env with
    | Some i => Some (width i)
    | None => None
    end
  | EXP_RAT expr_ps expr_qs =>
    match Asbb expr_ps env, Asbb expr_qs env with
    | Some ps, Some qs => Some (RAT ps qs)
    | _, _ => None
    end
  | EXP_projl expr_i =>
    match Ai expr_i env with
    | Some i => Some (lower i)
    | _ => None
    end
  | EXP_proju expr_i =>
    match Ai expr_i env with
    | Some i => Some (upper i)
    | _ => None
    end
  | EXP_projxl expr_p =>
    match Abb expr_p env with
    | Some p => Some (projxl p)
    | None => None
    end
  | EXP_projxu expr_p =>
    match Abb expr_p env with
    | Some p => Some (projxu p)
    | None => None
    end
  | EXP_projyl expr_p =>
    match Abb expr_p env with
    | Some p => Some (projyl p)
    | None => None
    end
  | EXP_projyu expr_p =>
    match Abb expr_p env with
    | Some p => Some (projyu p)
    | None => None
    end
  end.
  
Definition option_and (a b : option Prop) : option Prop :=
    match a, b with
    | Some a, Some b => Some (a /\ b)
    | _, _ => None
    end.

Definition option_or (a b : option Prop) : option Prop :=
    match a, b with
    | Some a, Some b => Some (a \/ b)
    | _, _ => None
    end.

(* Boolean *)
Fixpoint B (expr : Bexp) (env : Env) : option Prop :=
  match expr with
  | EXP_Bvar s =>
    match find s env with
    | Some (Vb a) => Some a
    | _ => None
    end
  | EXP_not expr_a =>
    match B expr_a env with
    | Some b => Some (not b)
    | None => None
    end
  | EXP_and expr_a expr_b =>
    match B expr_a env, B expr_b env with
    | Some a, Some b => Some (a /\ b)
    | _, _ => None
    end
  | EXP_or expr_a expr_b =>
    match B expr_a env, B expr_b env with
    | Some a, Some b => Some (a \/ b)
    | _, _ => None
    end
  | EXP_BBeq expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (p == b)
    | _, _ => None
    end
  | EXP_BBoverlap expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBoverlap p b)
    | _, _ => None
    end
  | EXP_BBsubset expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsubset p b)
    | _, _ => None
    end
  | EXP_BBsupset expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsupset p b)
    | _, _ => None
    end
  | EXP_BBsubseteq expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsubseteq p b)
    | _, _ => None
    end
  | EXP_BBsupseteq expr_p expr_q =>
    match Abb expr_p env, Abb expr_q env with
    | Some p, Some b => Some (BBsupseteq p b)
    | _, _ => None
    end
  | EXP_Ilt expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (i < j)
    | _, _ => None
    end
  | EXP_Igt expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (i > j)
    | _, _ => None
    end
  | EXP_Ieq expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Ieq i j)
    | _, _ => None
    end
  | EXP_Ioverlap expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Ioverlap i j)
    | _, _ => None
    end
  | EXP_Iin expr_x expr_i =>
    match Aq expr_x env, Ai expr_i env with
    | Some x, Some i => Some (Iin x i)
    | _, _ => None
    end
  | EXP_Iinrev expr_i expr_x =>
    match Aq expr_x env, Ai expr_i env with
    | Some x, Some i => Some (Iin x i)
    | _, _ => None
    end
  | EXP_Isubset expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isubset i j)
    | _, _ => None
    end
  | EXP_Isupset expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isupset i j)
    | _, _ => None
    end
  | EXP_Isubseteq expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isubseteq i j)
    | _, _ => None
    end
  | EXP_Isupseteq expr_i expr_j =>
    match Ai expr_i env, Ai expr_j env with
    | Some i, Some j => Some (Isupseteq i j)
    | _, _ => None
    end
  | EXP_Qlt expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x < y)%Q
    | _, _ => None
    end
  | EXP_Qgt expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x < y)%Q
    | _, _ => None
    end
  | EXP_Qeq expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x = y)
    | _, _ => None
    end
  | EXP_Qle expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x <= y)%Q
    | _, _ => None
    end
  | EXP_Qge expr_x expr_y =>
    match Aq expr_x env, Aq expr_y env with
    | Some x, Some y => Some (x <= y)%Q
    | _, _ => None
    end
  | EXP_forall bound expr_ps expr_a =>
    match Asbb expr_ps env with
    | Some ps => List.fold_left option_and (List.map (fun p => B expr_a (add bound (Vbb p) env)) ps) (Some True)
    | _ => None
    end
  | EXP_exists bound expr_ps expr_a =>
    match Asbb expr_ps env with
    | Some ps => List.fold_left option_or (List.map (fun p => B expr_a (add bound (Vbb p) env)) ps) (Some False)
    | _ => None
    end
  end.

(* Condition block *)
Definition Ccond (cond : Cond) (env : Env) : option Prop :=
  match cond with
  | CND_None => Some True
  | CND a => B a env
  end.

Definition Cdef (def : Def) (env : Env) : option Env :=
  match def with
  | DEF_SBB s expr_ps =>
    match Asbb expr_ps env with
    | Some ps => Some (add s (Vsbb ps) env)
    | _ => None
    end
  | DEF_BB s expr_p =>
    match Abb expr_p env with
    | Some p => Some (add s (Vbb p) env)
    | _ => None
    end
  | DEF_I s expr_i =>
    match Ai expr_i env with
    | Some i => Some (add s (Vi i) env)
    | _ => None
    end
  | DEF_Q s expr_x =>
    match Aq expr_x env with
    | Some x => Some (add s (Vq x) env)
    | _ => None
    end
  | DEF_B s expr_a =>
    match B expr_a env with
    | Some a => Some (add s (Vb a) env)
    | _ => None
    end
  end.

Fixpoint Cdefs (defs : list Def) (env : Env) : option Env :=
  match defs with
  | nil => Some env
  | cons def defs' =>
    match Cdef def env with
    | Some env' => Cdefs defs' env'
    | _ => None
    end
  end.

Definition Ccase (case : Case) (env : Env) : option (string * Prop) :=
  match case with
  | (label, defs, expr_a) =>
    match Cdefs defs env with
    | Some env' =>
      match B expr_a env' with
      | Some a => Some (label, a)
      | _ => None
      end
    | _ => None
    end
  end.

(* Case block *)
Fixpoint Ccases (cases : list Case) (env : Env) (accum : list (string * Prop)) : option (list (string * Prop)) :=
  match cases with
  | nil => Some accum
  | cons case cases' =>
    match Ccase case env with
    | Some label_bool => Ccases cases' env (cons label_bool accum)
    | _ => None
    end
  end.

(* Whole of syntax *)
Definition Cspec (spec : Spec) (env : Env) : option (list (string * Prop)) :=
  match spec with
  | (cond, cases) =>
    match Ccond cond env, Ccases cases env nil with
    | Some a, Some label_bools => Some (List.map
          (fun label_bool => match label_bool with (label, b) => (label, a /\ b) end)
          label_bools)
    | _, _ => None
    end
  end.
