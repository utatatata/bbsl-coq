Require Import List String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.

Module Export M := BBSL.M.


(* lead vehicle stopped
 *
 * exfunction
 *   // 前方車両の存在をチェック，あればtrueを返す
 *   前方車両がある():bool
 *   // 前方車両のbounding boxを返す
 *   前方車両():bb
 *   // 減速しなければならない範囲のbounding boxを返す
 *   減速区間():bb
 * endexfunction
 * 
 * condition
 *   [前方車両がある()]
 * endcondition
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
 *   , 減速区間:bb = 減速区間()
 *   in
 *     PROJ_y(前方車両) < PROJ_y(減速区間)
 * endcase
 * 
 * case レスポンス無し
 *   let 前方車両:bb = 前方車両()
 *   ,   減速区間:bb = 減速区間()
 *   in
 *     PROJ_y(前方車両) > PROJ_y(減速区間)
 * endcase
 *)
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

(* ケースの網羅性
 *
 * ∀減速区間, 前方車両∈BB. (
 *     減速区間 ≠ ∅ ∧ 前方車両 ≠ ∅ ∧ 前方車両がある ⇒
 *         case 減速 ∨ case 停止 ∨ case レスポンス無し
 * )
 *)
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
  simpl. unfold BBnempty. intros exists_front front_bb dec H.
  destruct front_bb as (f_x, f_y). destruct dec as (dec_x, dec_y).
  simpl in H. simpl. destruct H as (H, H0). destruct H as (H, H1), H0 as (H0, H2). destruct H0.
  destruct (Ilt_overlap_gt_dec f_y dec_y H1 H3). destruct s.
  - left. right. apply (conj H2 i).
  - right. apply (conj H2 i).
  - left. left. right. apply (conj H2 i).
Qed.

(* ケースの排他性
 *
 * ∀減速区間, 前方車両∈BB. (
 *     減速区間 ≠ ∅ ∧ 前方車両 ≠ ∅ ∧ 前方車両がある ⇒
 *         case 減速 ⇒ ¬(case 停止 ∨ case レスポンス無し) ∧
 *         case 停止 ⇒ ¬(case 減速 ∨ case レスポンス無し) ∧
 *         case レスポンス無し ⇒ ¬(case 減速 ∨ case 停止)
 * )
 *)
Proposition exclusiveness_of_example_lead_vehicle_stopped :
  forall (exists_front : Prop) (front_bb dec : BB),
    let evaluated := 
      Cspec
        example_lead_vehicle_stopped
        (add "減速区間" (Vbb dec) (add "前方車両" (Vbb front_bb) (add "前方車両がある" (Vb exists_front) (empty Value))))
    in 
    BBnempty front_bb /\ BBnempty dec /\ exists_front ->
      match option_map (fun cases => List.fold_left and (List.map (fun case =>
        or (not (snd case)) (not (List.fold_left and (List.map (fun case' => snd case') (List.filter (fun case' => negb (fst case =? fst case')) cases)) True))) cases) True) evaluated with
      | Some b => b
      | _ => False
      end.
Proof.
  simpl. unfold BBnempty, not. intros exists_front front_bb dec H.
  destruct front_bb as (f_x, f_y). destruct dec as (dec_x, dec_y).
  simpl in H. simpl.
  destruct H as (H, H0). destruct H as (H, H1), H0 as (H0, H2).
  destruct H0 as (H0, H3).
  split. split.
  - split. trivial. right. intros. destruct H4 as (H4, H5).
    destruct H4 as (H4, H6). destruct H6 as (H6, H7). destruct H5 as (H5, H8).
    apply (Ilt_not_overlap f_y dec_y H7) in H8. assumption.
  - right. intros H4. destruct H4 as (H4, H5). destruct H4 as (H4, H6).
    destruct H6 as (H6, H7). destruct H5 as (H5, H8).
    apply (Igt_not_overlap f_y dec_y H7) in H8. assumption.
  - right. intros H4. destruct H4 as (H4, H5). destruct H4 as (H4, H6).
    destruct H6 as (H6, H7). destruct H5 as (H5, H8).
    apply (Ilt_trans f_y dec_y f_y H3 H8) in H7.
    apply (Ilt_irrefl f_y H1 H7).
Qed.
