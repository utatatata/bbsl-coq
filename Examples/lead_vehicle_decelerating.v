Require Import List String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.

Module Export M := BBSL.M.


(* lead vehicle decelerating
 *
 * exfunction
 *   // 前方車両の存在をチェック，あればtrueを返す
 *   前方車両がある():bool
 *   // 前方車両のbounding boxを返す
 *   前方車両():bb
 *   // 追従するだけで問題のない範囲のbounding boxを返す
 *   追従区間():bb
 *   // 減速する必要のある範囲のbounding boxを返す
 *   減速区間():bb
 * endexfunction
 * 
 * condition
 *   [前方車両がある()]
 * endcondition
 * 
 * case 追従
 *   let
 *     前方車両:bb = 前方車両()
 *   , 追従区間:bb = 追従区間()
 *   in
 *     PROJ_y(前方車両) ≈ PROJ_y(追従区間)
 * endcase
 * 
 * case 減速
 *   let
 *     前方車両:bb = 前方車両()
 *   , 減速区間:bb = 減速区間()
 *   in
 *     PROJ_y(前方車両) ≈ PROJ_y(減速区間)
 * endcase
 * 
 * case 停止
 *   let
 *     前方車両:bb = 前方車両()
 *   , 追従区間:bb = 追従区間()
 *   , 減速区間:bb = 減速区間()
 *   in
 *     PROJ_y(前方車両) < PROJ_y(追従区間) and
 *     PROJ_y(前方車両) < PROJ_y(減速区間)
 * endcase
 * 
 * case レスポンス無し
 *   let
 *     前方車両:bb = 前方車両()
 *   , 追従区間:bb = 追従区間()
 *   , 減速区間:bb = 減速区間()
 *   in
 *     PROJ_y(前方車両) > PROJ_y(追従区間) and
 *     PROJ_y(前方車両) > PROJ_y(減速区間)
 * endcase
 *)
Definition example_lead_vehicle_decelerating : Spec :=
  ( CND (EXP_Bvar "前方車両がある")
  , [ ("追従"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "追従区間" (EXP_BBvar "追従区間")
        ]
      , EXP_Ioverlap
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "追従区間"))
      )
    ; ( "減速"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_Ioverlap
          (EXP_projy (EXP_BBvar "前方車両"))
          (EXP_projy (EXP_BBvar "減速区間"))
      )
    ; ( "停止"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "追従区間" (EXP_BBvar "追従区間")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_and
          (EXP_Ilt
            (EXP_projy (EXP_BBvar "前方車両"))
            (EXP_projy (EXP_BBvar "追従区間")))
          (EXP_Ilt
            (EXP_projy (EXP_BBvar "前方車両"))
            (EXP_projy (EXP_BBvar "減速区間")))

      )
    ; ( "レスポンスなし"
      , [ DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ; DEF_BB "追従区間" (EXP_BBvar "追従区間")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_and
          (EXP_Igt
            (EXP_projy (EXP_BBvar "前方車両"))
            (EXP_projy (EXP_BBvar "追従区間")))
          (EXP_Igt
            (EXP_projy (EXP_BBvar "前方車両"))
            (EXP_projy (EXP_BBvar "減速区間")))
      )
    ]
  ).

Proposition comprehensiveness_of_example_lead_vehicle_decelerating :
  forall (exists_front : Prop) (front_bb dec follow : BB),
    let evaluated := 
      Cspec
        example_lead_vehicle_decelerating
        (add "減速区間" (Vbb dec) (add "追従区間" (Vbb follow) (add "前方車両" (Vbb front_bb) (add "前方車両がある" (Vb exists_front) (empty Value)))))
    in 
    BBnempty front_bb /\ BBnempty dec /\ BBnempty follow /\ exists_front ->
       match option_map (fun ev => List.fold_left or (List.map snd ev) False) evaluated with
       | Some b => b
       | _ => False
       end.
Proof.
  simpl. unfold BBnempty. intro exists_front.
  destruct front_bb as (frt_x, frt_y), dec as (dec_x, dec_y), follow as (flw_x, flw_y).
  simpl. intros H. destruct H as (H, H0), H as (H, H1), H0 as (H0, H2), H0 as (H0, H3), H2 as (H2, H4), H2 as (H2, H5).
  destruct (Ilt_overlap_gt_dec frt_y dec_y H1 H3). destruct s.
  - left. left. right. split. assumption. apply and_comm. split. assumption.
    destruct (Ilt_overlap_gt_dec dec_y flw_y H3 H5). destruct s.
  -- apply (Ilt_trans frt_y dec_y flw_y H3 i i0).
  -- destruct (Ilt_overlap_gt_dec )
  -- rewrite Ioverlap
  - 
  - 

  unfold BBnempty, not. intros exists_front front_bb dec follow H.
  destruct front_bb as (f_x, f_y). destruct dec as (dec_x, dec_y).
  destruct follow as (flw_x, flw_y).
  simpl in H. simpl. destruct H as (H, H0). destruct H as (H, H1), H0 as (H0, H2).
  destruct H0 as (H0, H3), H2 as (H2, H4). destruct H2 as (H2, H5).
  destruct (Ilt_overlap_gt_dec f_y dec_y H1 H3). destruct s.
  - left. left. right. split. assumption. apply and_comm. split. assumption.
    destruct (Ilt_overlap_gt_dec dec_y flw_y H3 H5). destruct s.
  -- apply (Ilt_trans f_y dec_y flw_y H3 i i0).
  -- destruct (Ilt_overlap_gt_dec f_y flw_y H1 H5). destruct s.
  --- assumption.
  --- 
  --- 
  -- 
  - 
  - 

  unfold Inempty. unfold Igt.
  unfold Ioverlap. unfold Iempty. unfold Iintersection. unfold not.
  intros. destruct dec as (dec_x, dec_y). destruct follow as (follow_x, follow_y).
  destruct front_bb as (f_x, f_y).
  destruct dec_x as (dec_xl, dec_xu). destruct dec_y as (dec_yl, dec_yu).
  destruct follow_x as (follow_xl, follow_xu). destruct follow_y as (follow_yl, follow_yu).
  destruct f_x as (f_xl, f_xu). destruct f_y as (f_yl, f_yu).
  simpl. simpl in H. destruct H. destruct H. destruct H0.
  destruct H0. destruct H2. destruct H2.
  rewrite (Q.min_lt_iff f_yu dec_yu (Qmax f_yl dec_yl)).
  rewrite (Q.max_lt_iff f_yl dec_yl f_yu).
  rewrite (Q.max_lt_iff f_yl dec_yl dec_yu).
  rewrite (Q.min_lt_iff f_yu follow_yu (Qmax f_yl follow_yl)).
  rewrite (Q.max_lt_iff f_yl follow_yl f_yu).
  rewrite (Q.max_lt_iff f_yl follow_yl follow_yu).
  destruct (Qlt_le_dec dec_yu f_yl).
  - left. right.
    apply (and_r exists_front (((f_yu < f_yl)%Q \/ (f_yu < dec_yl)%Q) \/ (dec_yu < f_yl)%Q \/ (dec_yu < dec_yl)%Q -> False) H4).
    intros. destruct H6. destruct H6.
  -- apply (Qlt_le_trans f_yu f_yl f_yu H6) in H1. apply (Qlt_irrefl f_yu H1).
  -- apply (Qlt_le_trans f_yu dec_yl dec_yu H6) in H3.
     apply (Qle_lt_trans f_yl f_yu dec_yu H1) in H3.
     apply (Qlt_trans dec_yu f_yl dec_yu q) in H3.
     apply (Qlt_irrefl dec_yu H3).
  -- destruct H6.
  --- destruct (Qlt_le_dec f_yu follow_yl).
  ---- destruct (Qlt_le_dec follow_yu dec_yl).
  ----- apply (Qlt_le_trans f_yu follow_yl follow_yu q0) in H5.
        apply (Qlt_trans f_yu follow_yu dec_yl H5) in q1.
        apply (Qlt_le_trans f_yu dec_yl dec_yu q1) in H3.
        apply (Qlt_le_trans dec_yu f_yl f_yu q) in H1.
        apply (Qlt_trans dec_yu f_yu dec_yu H1) in H3.
        apply (Qlt_irrefl dec_yu H3).
  ----- destruct (Qlt_le_dec follow_yu dec_yl).
  ------ apply (Qlt_le_trans follow_yu dec_yl follow_yu q2) in q1.
         apply (Qlt_irrefl follow_yu q1).
  ------ destruct (Qlt_le_dec follow_yu dec_yl).
  ------- apply (Qlt_le_trans f_yu follow_yl follow_yu q0) in H5.
          apply (Qlt_trans f_yu follow_yu dec_yl H5) in q3.
          apply (Qlt_le_trans f_yu dec_yl dec_yu q3) in H3.
          apply (Qlt_le_trans dec_yu f_yl f_yu q) in H1.
          apply (Qlt_trans dec_yu f_yu dec_yu H1) in H3.
          apply (Qlt_irrefl dec_yu H3).
  ------- 

apply (Qlt_le_trans dec_yu f_yl f_yu q) in H1.

        apply (Qlt_trans dec_yu f_yu follow_yl H1) in q0.
  

  - right. destruct (Qlt_le_dec follow_yl f_yu).
  -- destruct (Qlt_le_dec follow_yu f_yl).
  --- apply (and_r exists_front (((f_yu < f_yl)%Q \/ (f_yu < follow_yl)%Q) \/ (follow_yu < f_yl)%Q \/ (follow_yu < follow_yl)%Q -> False) H4).
      intros. destruct H6. destruct H6.
  ---- apply (Qle_lt_trans f_yl f_yu f_yl H1) in H6. apply (Qlt_irrefl f_yl H6).
  ---- apply (Qlt_le_trans f_yu follow_yl follow_yu H6) in H5.
       apply (Qlt_trans f_yu follow_yu f_yl H5) in q1.
       apply (Qlt_le_trans f_yu f_yl f_yu q1) in H1.
       apply (Qlt_irrefl f_yu H1).
  ---- destruct H6. destruct (Qlt_le_dec dec_yu follow_yl).
       
  ----- apply (Qlt_le_trans dec_yu follow_yl follow_yu q2) in H5.
  apply (Qlt_trans dec_yu follow_yl f_yu q2) in q0.
       

  - left. left. right. destruct (Qlt_le_dec f_yu follow_yl).
  -- 
*)
