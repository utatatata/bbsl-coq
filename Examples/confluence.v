Require Import List String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.


Definition example_confluence : Spec := 
  ( CND_None
  , [ ( "シーン１"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_forall "x" (EXP_SBBvar "他車集合")
          (EXP_not (EXP_Ieq (EXP_projy (EXP_BBvar "x")) (EXP_Ivar "合流領域")))
      )
    ; ( "シーン２"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_exists "x" (EXP_SBBvar "他車集合")
          (EXP_and
            (EXP_Qeq (EXP_projyl (EXP_BBvar "x")) (EXP_proju (EXP_Ivar "合流領域")))
            (EXP_forall "y" (EXP_SBBvar "他車集合")
              (EXP_or (EXP_not (EXP_Ieq (EXP_projy (EXP_BBvar "y")) (EXP_Ivar "合流領域")))
                      (EXP_BBeq (EXP_BBvar "x") (EXP_BBvar "y")))))
      )
    ; ( "シーン３"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_exists "x" (EXP_SBBvar "他車集合")
         (EXP_and
           (EXP_Qeq (EXP_projyl (EXP_BBvar "x")) (EXP_proju (EXP_Ivar "合流領域")))
           (EXP_and
             (EXP_exists "y" (EXP_SBBvar "他車集合")
               (EXP_and
                 (EXP_Qeq (EXP_projyu (EXP_BBvar "y")) (EXP_projl (EXP_Ivar "合流領域")))
                 (EXP_not (EXP_BBeq (EXP_BBvar "x") (EXP_BBvar "y")))))
             (EXP_forall "z" (EXP_SBBvar "他車領域")
                   (EXP_not (EXP_Isupseteq (EXP_Ivar "合流領域") (EXP_projy (EXP_BBvar "z")))))))
      )
    ; ( "シーン４"
      , [ DEF_I "合流領域" (EXP_Ivar "合流領域")
        ; DEF_SBB "他車集合" (EXP_SBBvar "他車集合")
        ]
      , EXP_exists "z" (EXP_SBBvar "他車集合")
          (EXP_Isupseteq (EXP_Ivar "合流領域") (EXP_projy (EXP_BBvar "z")))
      )
    ]
  ).

(*
Proposition comprehensiveness_of_example_confluence :
  forall (confluent_region : Interval) (set_of_cars : SetBB),
    let evaluated := 
      Cspec
        example_confluence
        (add "合流領域" (Vi confluent_region) (add "他車集合" (Vsbb set_of_cars) (empty Value)))
    in 
    Inempty confluent_region ->
       match option_map (fun ev => List.fold_left or (List.map snd ev) False) evaluated with
       | Some b => b
       | _ => False
       end.
Proof.
  simpl.
  intros confluent_region set_of_cars. destruct confluent_region as (region_l, region_u).
  destruct set_of_cars as [|car].
  -- simpl. rewrite (and_l True True).
     rewrite (or_truer (((False \/ True /\ False) \/ True /\ False) \/ True /\ False)).
     trivial.
     trivial.
  -- destruct car as (car_x, car_y).
     destruct car_x as (car_xl, car_xu).
     destruct car_y as (car_yl, car_yu).
     simpl. unfold Inempty. unfold Ieq. unfold Isubseteq. simpl.

     destruct (Qlt_le_dec )

  destruct dec as (dec_x, dec_y). destruct front_bb as (f_x, f_y).
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
*)