Require Import List String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.


Definition example_debris_static_in_lane : Spec :=
  ( CND (EXP_Bvar "静的障害物がある")
  , [ ( "減速"
      , [ DEF_SBB "障害物集合" (EXP_SBBvar "障害物集合")
        ; DEF_SBB "進行区間集合" (EXP_SBBvar "進行区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "障害物集合")
          (EXP_exists "y" (EXP_SBBvar "進行区間集合")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
              (EXP_and
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ; ( "停止"
      , [ DEF_SBB "障害物集合" (EXP_SBBvar "障害物集合")
        ; DEF_SBB "進行区間集合" (EXP_SBBvar "進行区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "障害物集合")
          (EXP_exists "y" (EXP_SBBvar "進行区間集合")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
              (EXP_and
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))
                (EXP_Ilt (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ; ( "レスポンスなし"
      , [ DEF_SBB "障害物集合" (EXP_SBBvar "障害物集合")
        ; DEF_SBB "進行区間集合" (EXP_SBBvar "進行区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "障害物集合")
          (EXP_exists "y" (EXP_SBBvar "進行区間集合")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "x")) (EXP_projx (EXP_BBvar "y")))
              (EXP_and
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "y")))
                (EXP_Igt (EXP_projy (EXP_BBvar "x")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ]
  ).

(**
Proposition comprehensiveness_of_example_debris_static_in_lane :
  forall (exists_debris : Prop) (debrises : SetBB) (lane_bbs : SetBB) (dec : BB),
    let evaluated :=
      Cspec
        example_debris_static_in_lane
        (add "減速区間" (Vbb dec) (add "進行区間集合" (Vsbb lane_bbs) (add "障害物集合" (Vsbb debrises) (add "静的障害物がある" (Vb exists_debris) (empty Value)))))
    in
    BBnempty dec /\ exists_debris ->
      match option_map (fun ev => List.fold_left or (List.map snd ev) False) evaluated with
      | Some b => b
      | _ => False
      end.
Proof.
  simpl. unfold BBnempty. unfold Inempty. unfold Igt. unfold Ilt.
  unfold Ioverlap. unfold Iempty. unfold Iintersection. unfold not.
  intros. destruct dec as (dec_x, dec_y). 
  destruct dec_x as (dec_xl, dec_xu). destruct dec_y as (dec_yl, dec_yu).
  simpl. simpl in H. destruct H. destruct H. destruct H0. destruct H0.
  rewrite (Q.min_lt_iff f_yu dec_yu (Qmax f_yl dec_yl)).
  rewrite (Q.max_lt_iff f_yl dec_yl dec_yu).
  rewrite (Q.max_lt_iff f_yl dec_yl f_yu).
  destruct (Qlt_le_dec dec_yu f_yl).
*)
