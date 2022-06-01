Require Import List QArith String.
Require Import BBSL.BBSL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope BBSL_scope.


Definition example_contains : Spec :=
  ( CND_None
  , [ ( "A contains B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
         (EXP_BBsupseteq (EXP_BBvar "A") (EXP_BBvar "B"))
         (EXP_not (EXP_or
           (EXP_Qeq (EXP_projxl (EXP_BBvar "A")) (EXP_projxl (EXP_BBvar "B")))
           (EXP_or
             (EXP_Qeq (EXP_projxu (EXP_BBvar "A")) (EXP_projxu (EXP_BBvar "B")))
             (EXP_or
               (EXP_Qeq (EXP_projyl (EXP_BBvar "A")) (EXP_projyl (EXP_BBvar "B")))
               (EXP_Qeq (EXP_projyu (EXP_BBvar "A")) (EXP_projyu (EXP_BBvar "B")))))))
      )
    ; ( "A covers B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
         (EXP_BBsupseteq (EXP_BBvar "A") (EXP_BBvar "B"))
         (EXP_or
           (EXP_Qeq (EXP_projxl (EXP_BBvar "A")) (EXP_projxl (EXP_BBvar "B")))
           (EXP_or
             (EXP_Qeq (EXP_projxu (EXP_BBvar "A")) (EXP_projxu (EXP_BBvar "B")))
             (EXP_or
               (EXP_Qeq (EXP_projyu (EXP_BBvar "A")) (EXP_projyl (EXP_BBvar "B")))
               (EXP_Qeq (EXP_projyl (EXP_BBvar "A")) (EXP_projyu (EXP_BBvar "B"))))))
      )
    ; ( "A touch B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_SBBunion (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ])))
            (EXP_Q 0))
          (EXP_or
            (EXP_Qeq (EXP_projxl (EXP_BBvar "A")) (EXP_projxl (EXP_BBvar "B")))
            (EXP_or
              (EXP_Qeq (EXP_projxu (EXP_BBvar "A")) (EXP_projxu (EXP_BBvar "B")))
              (EXP_or
              (EXP_Qeq (EXP_projyl (EXP_BBvar "A")) (EXP_projyl (EXP_BBvar "B")))
              (EXP_Qeq (EXP_projyu (EXP_BBvar "A")) (EXP_projyu (EXP_BBvar "B"))))))
      )
    ; ( "A overlapbdyintersect B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_not (EXP_and
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_Q 1))
          (EXP_Qeq
            (EXP_RAT
              (EXP_SBBintersection (EXP_makeSBB [ EXP_BBvar "A" ]) (EXP_makeSBB [ EXP_BBvar "B" ]))
              (EXP_makeSBB [ EXP_BBvar "B" ]))
            (EXP_Q 0)))
      )
    ; ( "A equal B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_BBeq (EXP_BBvar "A") (EXP_BBvar "B")
      )
    ; ( "A disjoint B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_not (EXP_BBoverlap (EXP_BBvar "A") (EXP_BBvar "B"))
      )
    ; ( "A overlapbdydisjoint B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_or
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projy (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_and
                (EXP_Iin (EXP_projxl (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
                (EXP_Iin (EXP_projxu (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B"))))
              (EXP_and
                (EXP_Iin (EXP_projxu (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))
                (EXP_not (EXP_Iin (EXP_projxl (EXP_BBvar "A")) (EXP_projx (EXP_BBvar "B")))))))
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projx (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_and
                (EXP_Iin (EXP_projyl (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))
                (EXP_Iin (EXP_projyu (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B"))))
              (EXP_and
                (EXP_Iin (EXP_projyu (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))
                (EXP_not (EXP_Iin (EXP_projyl (EXP_BBvar "A")) (EXP_projy (EXP_BBvar "B")))))))
      )
    ; ( "A on B"
      , [ DEF_BB "A" (EXP_BBvar "Aを返す関数")
        ; DEF_BB "B" (EXP_BBvar "Bを返す関数")
        ]
      , EXP_or
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projy (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_Iinrev (EXP_projy (EXP_BBvar "B")) (EXP_projyu (EXP_BBvar "A")))
              (EXP_Iinrev (EXP_projy (EXP_BBvar "B")) (EXP_projyl (EXP_BBvar "A")))))
          (EXP_and
            (EXP_Qeq (EXP_width (EXP_projx (EXP_BBvar "B"))) (EXP_Q 0))
            (EXP_or
              (EXP_Iinrev (EXP_projx (EXP_BBvar "B")) (EXP_projxu (EXP_BBvar "A")))
              (EXP_Iinrev (EXP_projx (EXP_BBvar "B")) (EXP_projxl (EXP_BBvar "A")))))
      )
    ]
  ).