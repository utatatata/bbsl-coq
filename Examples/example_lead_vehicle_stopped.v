Require Import QArith Qminmax String List.
Import ListNotations.


Local Open Scope string_scope.
Require Import BBSL.BBSL.
Local Open Scope BBSL_scope.

Module Export M := BBSL.M.

Definition example_lead_vehicle_stopped : Spec :=
  ( CND (EXP_Bvar "前方車両がある")
  , [ ( "減速"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Ioverlap
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ; ( "停止"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Ilt
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ; ( "レスポンスなし"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Igt
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ]
  ).

Proposition comprehensiveness_of_example_lead_vehicle_stopped :
  forall (exists_front : Prop) (front_bb dec : BB),
    let evaluated := 
      Cspec
        example_lead_vehicle_stopped
        (add "減速区間" (Vbb dec) (add "前方車両" (Vbb front_bb) (add "前方車両がある" (Vb exists_front) (empty Value))))
    in 
    BBnempty front_bb /\ BBnempty dec /\ exists_front ->
       match option_map (fun ev => List.fold_left or (List.map snd ev) False) evaluated with
       | Some b => b
       | _ => False
       end.
Proof.
  simpl. unfold BBnempty. unfold Inempty. unfold Ilt.
  unfold Ioverlap. unfold Iempty. unfold Iintersection. unfold not.
  intros. destruct dec as (dec_x, dec_y). destruct front_bb as (f_x, f_y).
  destruct dec_x as (dec_xl, dec_xu). destruct dec_y as (dec_yl, dec_yu).
  destruct f_x as (f_xl, f_xu). destruct f_y as (f_yl, f_yu).
  simpl. simpl in H. destruct H. destruct H. destruct H0. destruct H0.
  rewrite (Q.min_lt_iff f_yu dec_yu (Qmax f_yl dec_yl)).
  rewrite (Q.max_lt_iff f_yl dec_yl dec_yu).
  rewrite (Q.max_lt_iff f_yl dec_yl f_yu).
  destruct (Qlt_le_dec dec_yu f_yl).
  - left. left. right. apply (conj H2 q).
  - destruct (Qlt_le_dec f_yu dec_yl).
  -- left. right. apply (conj H2 q0).
  -- right. split. assumption. intros. destruct H4. destruct H4.
  --- apply (Qle_lteq f_yl f_yu) in H1. destruct H1.
  ---- apply (Qlt_asym f_yl f_yu (conj H1 H4)).
  ---- rewrite H1 in H4. apply (Qlt_irrefl f_yu H4).
  --- apply (Qle_lteq dec_yl f_yu) in q0. destruct q0.
  ---- apply (Qlt_asym dec_yl f_yu (conj H5 H4)).
  ---- rewrite H5 in H4. apply (Qlt_irrefl f_yu H4).
  --- destruct H4.
  ---- apply (Qle_lteq f_yl dec_yu) in q. destruct q.
  ----- apply (Qlt_asym f_yl dec_yu (conj H5 H4)).
  ----- rewrite H5 in H4. apply (Qlt_irrefl dec_yu H4).
  ---- apply (Qle_lteq dec_yl dec_yu) in H3. destruct H3.
  ----- apply (Qlt_asym dec_yl dec_yu (conj H3 H4)).
  ----- rewrite H3 in H4. apply (Qlt_irrefl dec_yu H4).
Qed.

Proposition exclusiveness_of_example_lead_vehicle_stopped :
  forall (exists_front : Prop) (front_bb dec : BB),
    let evaluated := 
      Cspec
        example_lead_vehicle_stopped
        (add "減速区間" (Vbb dec) (add "前方車両" (Vbb front_bb) (add "前方車両がある" (Vb exists_front) (empty Value))))
    in 
    BBnempty front_bb /\ BBnempty dec /\ exists_front ->
       match option_map (fun cases => List.fold_left and (List.map (fun case =>
           ~snd case \/ List.fold_left and (List.map (fun case' => ~snd case' \/ fst case = fst case') cases) True

         ) cases) True) evaluated with
       | Some b => b
       | _ => False
       end.
Proof.
  simpl. unfold BBnempty. unfold Ioverlap. unfold Iintersection.
  unfold Iempty. unfold Inempty. unfold not. unfold Ilt.
  intros. destruct dec as (dec_x, dec_y). destruct front_bb as (f_x, f_y).
  destruct dec_x as (dec_xl, dec_xu). destruct dec_y as (dec_yl, dec_yu).
  destruct f_x as (f_xl, f_xu). destruct f_y as (f_yl, f_yu).
  simpl. simpl in H. destruct H. destruct H. destruct H0. destruct H0.
  rewrite (Q.min_lt_iff f_yu dec_yu (Qmax f_yl dec_yl)).
  rewrite (Q.max_lt_iff f_yl dec_yl f_yu).
  rewrite (Q.max_lt_iff f_yl dec_yl dec_yu).
  destruct (Qlt_le_dec dec_yu f_yl).
  split. split. split. trivial. right. split. split. split. trivial. right. trivial.
  left. intros. destruct H4. apply (Qle_lt_trans dec_yl dec_yu f_yl H3) in q.
  -- destruct (Qlt_le_dec f_yu dec_yl).
     apply (Qle_lt_trans f_yl f_yu dec_yl H1) in q0. apply (Qlt_asym dec_yl f_yl (conj q q0)).
     apply (Qlt_le_trans dec_yl f_yl f_yu q) in H1. apply (Qlt_asym dec_yl f_yu (conj H1 H5)).
  -- left. intros. destruct H4. destruct H5. right. left. assumption.
  -- left. intros. destruct H4. apply (Qlt_le_trans dec_yu f_yl f_yu q) in H1.
     apply (Qle_lt_trans dec_yl dec_yu f_yu H3) in H1. apply (Qlt_asym dec_yl f_yu (conj H1 H5)).
  -- left. intros. destruct H4. destruct H5. right. left. assumption.
  -- destruct (Qlt_le_dec f_yu dec_yl).
     split. split. split. trivial. left. intros. destruct H4.
     apply (Qle_lt_trans f_yl dec_yu f_yl q) in H5. apply (Qlt_irrefl f_yl) in H5. assumption.
     right. split. split. split. trivial. left. intros. destruct H4.
     apply (Qle_lt_trans f_yl dec_yu f_yl q) in H5. apply (Qlt_irrefl f_yl) in H5. assumption.
     right. trivial. left. intros. destruct H4. destruct H5. left. right. assumption.
     left. intros. destruct H4. destruct H5. left. right. assumption.
     split. split. split. trivial. left. intros. destruct H4.
     apply (Qle_lt_trans f_yl dec_yu f_yl q) in H5. apply (Qlt_irrefl f_yl) in H5. assumption.
     left. intros. destruct H4. apply (Qle_lt_trans dec_yl f_yu dec_yl q0) in H5.
     apply (Qlt_irrefl dec_yl) in H5. assumption.
     right. split. split. split. trivial. left. intros. destruct H4.
     apply (Qle_lt_trans f_yl dec_yu f_yl q) in H5. apply (Qlt_irrefl f_yl) in H5. assumption.
     left. intros. destruct H4. apply (Qle_lt_trans dec_yl f_yu dec_yl q0) in H5. apply (Qlt_irrefl dec_yl). assumption.
     right. trivial.
Qed.
