Require Import List String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.


Definition example_vehicle_cutting_in : Spec :=
  ( CND (EXP_and (EXP_Bvar "前方車両がある") (EXP_Bvar "他車両がある"))
  , [ ( "停止"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_exists "x" (EXP_SBBvar "自車線区間集合")
          (EXP_and
            (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
            (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))
      )
    ; ( "減速"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_and
          (EXP_forall "x" (EXP_SBBvar "自車線区間集合")
            (EXP_and
              (EXP_not (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x"))))
              (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))))
          (EXP_exists "x" (EXP_SBBvar "自車線区間")
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
              (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))))
      )
    ; ( "前方車両に従う"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_BB "前方車両" (EXP_BBvar "前方車両")
        ]
      , EXP_Qlt (EXP_projyl (EXP_BBvar "前方車両")) (EXP_projyl (EXP_BBvar "割り込み車両"))
      )
    ; ( "割り込み車両に前方を譲る"
      , [ DEF_BB "割り込み車両" (EXP_BBvar "割り込み車両")
        ; DEF_SBB "自車線区間集合" (EXP_SBBvar "自車線区間集合")
        ; DEF_BB "減速区間" (EXP_BBvar "減速区間")
        ]
      , EXP_forall "x" (EXP_SBBvar "自車線区間集合")
          (EXP_not
            (EXP_and
              (EXP_Ioverlap (EXP_projx (EXP_BBvar "割り込み車両")) (EXP_projx (EXP_BBvar "x")))
              (EXP_or
                (EXP_Ilt (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間")))
                (EXP_Ioverlap (EXP_projy (EXP_BBvar "割り込み車両")) (EXP_projy (EXP_BBvar "減速区間"))))))
      )
    ]
  ).