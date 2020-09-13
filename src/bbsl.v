Require Import Reals String List FMapList OrderedTypeEx Ensembles Bool.
Import ListNotations.

Declare Scope Interval_scope.

Local Open Scope Interval_scope.
Local Open Scope bool_scope.
Local Open Scope R_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.


Inductive interval : Type :=
  I (l u : R).

Inductive bb : Type :=
  BB (x y : interval).

Inductive bbexpr :=
  | BBcon (x : bb) | BBvar (s : string).

Inductive iexpr :=
  | Icon (x : interval) | Ivar (s : string)
  | Iintersection (i0 i1 : iexpr)
  | Proj_x (bb : bbexpr) | Proj_y (bb : bbexpr).

Inductive rexpr :=
  | Rcon (x : R) | Rvar (s : string)
  | W (i : iexpr).

Inductive bexpr :=
  | Bcon (x : bool) | Bvar (s : string)
  | And (b0 b1 : bexpr) | Or (b0 b1 : bexpr)
  | Not (b : bexpr)
  | Rlt (r0 r1 : rexpr)
  | Ilt (i0 i1 : iexpr)
  | Ioverlap (i0 i1 : iexpr).

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

