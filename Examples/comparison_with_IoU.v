Require Import List QArith String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.


Definition example_ratio_relation1_2 : Spec :=
  ( CND_None
  , [ ( "割合の関係１(IoU=0.5の場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Qeq
          (EXP_RAT
            (EXP_SBBintersection
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_SBBunion
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ])))
          (EXP_Q 0.5)
      )
    ; ( "割合の関係１(IoU=0.15の場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Qeq
          (EXP_RAT
            (EXP_SBBintersection
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_SBBunion
              (EXP_makeSBB [ EXP_BBvar "A" ])
              (EXP_makeSBB [ EXP_BBvar "B" ])))
          (EXP_Q 0.15)
      )
    ]
  ).

Definition example_rational_relation3_4 : Spec :=
  ( CND_None
  , [ ( "割合の関係３(IoU=0.12かつAの右上の頂点とBの左下の頂点が重なっている場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_SBBunion
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ])))
            (EXP_Q 0.5))
          (EXP_and
            (EXP_Ioverlap (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
            (EXP_Ioverlap (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))))
      )
    ; ( "割合の関係３(IoU=0.12かつAの右下の頂点とBの左上の頂点が重なっている場合)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_SBBunion
                (EXP_makeSBB [ EXP_BBvar "A" ])
                (EXP_makeSBB [ EXP_BBvar "B" ])))
            (EXP_Q 0.5))
          (EXP_and
            (EXP_Ioverlap (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
            (EXP_Ioverlap (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))))
      )
    ]
  ).

Definition example_positional_relation1_2 : Spec :=
  ( CND_None
  , [ ( "位置関係１(AよりもBの方が上にある)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Ilt (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))
      )
    ; ( "位置関係１(AよりもBの方が右にある)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_Ilt (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B"))
      )
    ]
  ).

Definition example_positional_relation3_4 : Spec :=
  ( CND (EXP_Bvar "画像全体を取得可能")
  , [ ( "位置関係３(BがAの左上と上の領域どちらともに位置している)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Ilt (EXP_projy (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))
          (EXP_Ioverlap (EXP_projx (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
      )
    ; ( "位置関係４(B全体の0.3以上がAの左下に位置している)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ; DEF_BB "A左下" (EXP_makeBB
          (EXP_makeI (EXP_projxl EXP_BBimg) (EXP_projxl (EXP_BBvar "A")))
          (EXP_makeI (EXP_projyl EXP_BBimg) (EXP_projyl (EXP_BBvar "A"))))
        ]
      , EXP_Qge
          (EXP_RAT
            (EXP_SBBintersection
              (EXP_makeSBB [ EXP_BBvar "A左下" ])
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_makeSBB [ EXP_BBvar "B" ]))
          (EXP_Q 0.3)
      )
    ]
  ).

Definition example_inclusion_relation1_2 : Spec :=
  ( CND_None
  , [ ( "包含関係１(BがAに包含されている)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_BBsupseteq (EXP_BBvar "A") (EXP_BBvar "B")
      )
    ; ( "包含関係２(AがBに包含されている)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_BBsubseteq (EXP_BBvar "A") (EXP_BBvar "B")
      )
    ]
  ).

Definition example_comparison_relation1_2 : Spec :=
  ( CND_None
  , [ ( "大小関係１(AよりBが小さい)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_Qgt
          (EXP_RAT (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
          (EXP_Q 1.0)
      )
    ; ( "大小関係２(AよりBが大さい)"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
      ]
      , EXP_Qlt
          (EXP_RAT (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
          (EXP_Q 1.0)
      )
    ]
  ).
