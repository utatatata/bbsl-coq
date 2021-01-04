Require Import Reals String List FMapList OrderedTypeEx Ensembles Bool.
Import ListNotations.

Declare Scope Interval_scope.

Local Open Scope Interval_scope.
Local Open Scope bool_scope.
Local Open Scope R_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Inductive interval := I (l u : R).

Inductive bb := BB (x y : interval).

Inductive exp_bb := BBvar (s : string).

Inductive exp_i := Ivar (s : string) | Proj_y (bb : exp_bb).

Inductive overlap : exp_i -> exp_i -> Prop :=
  

Example ImgSampleComprehensiveness
  : forall exists_vehicle : Prop vehicle : bb dec : interval, 
    exists_vehicle ->
       Proj_y vehicle ≈ dec
    \/ Proj_y vehicle > dec.
