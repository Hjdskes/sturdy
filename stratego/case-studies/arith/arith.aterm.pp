Specification(
  [ Signature(
      [ Constructors(
          [ OpDecl("Zero", ConstType(SortNoArgs("Exp")))
          , OpDecl(
              "Succ"
            , FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "Mul"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Add"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl("Nil", ConstType(Sort("List", [SortVar("a")])))
          ]
        )
      ]
    )
  , Strategies(
      [ SDefT(
          "eval_0_0"
        , []
        , []
        , GuardedLChoice(
            Seq(
              Match(Anno(Op("Zero", []), Wld()))
            , Build(Anno(Op("Zero", []), Op("Nil", [])))
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["a_1", "b_1", "c_1"]
              , Seq(
                  Match(Anno(Op("Succ", [Var("a_1")]), Wld()))
                , Seq(
                    Match(Var("c_1"))
                  , Seq(
                      Build(Var("a_1"))
                    , Seq(
                        CallT(SVar("eval_0_0"), [], [])
                      , Seq(
                          Match(Var("b_1"))
                        , Seq(
                            Build(Var("c_1"))
                          , Build(
                              Anno(
                                Op("Succ", [Var("b_1")])
                              , Op("Nil", [])
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            , Id()
            , GuardedLChoice(
                Seq(
                  Match(
                    Anno(
                      Op(
                        "Mul"
                      , [Anno(Op("Zero", []), Wld()), Wld()]
                      )
                    , Wld()
                    )
                  )
                , Build(Anno(Op("Zero", []), Op("Nil", [])))
                )
              , Id()
              , GuardedLChoice(
                  Scope(
                    ["y_0", "z_0"]
                  , Seq(
                      Match(
                        Anno(
                          Op(
                            "Mul"
                          , [Anno(Op("Succ", [Var("y_0")]), Wld()), Var("z_0")]
                          )
                        , Wld()
                        )
                      )
                    , Seq(
                        Build(
                          Anno(
                            Op(
                              "Add"
                            , [ Anno(
                                  Op("Mul", [Var("y_0"), Var("z_0")])
                                , Op("Nil", [])
                                )
                              , Var("z_0")
                              ]
                            )
                          , Op("Nil", [])
                          )
                        )
                      , CallT(SVar("eval_0_0"), [], [])
                      )
                    )
                  )
                , Id()
                , GuardedLChoice(
                    Scope(
                      ["s_0", "t_0", "u_0", "w_0", "v_0", "x_0"]
                    , Seq(
                        Match(
                          Anno(
                            Op("Mul", [Var("s_0"), Var("t_0")])
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("w_0"))
                        , Seq(
                            Build(Var("s_0"))
                          , Seq(
                              CallT(SVar("eval_0_0"), [], [])
                            , Seq(
                                Match(Var("u_0"))
                              , Seq(
                                  Build(Var("w_0"))
                                , Seq(
                                    Match(Var("x_0"))
                                  , Seq(
                                      Build(Var("t_0"))
                                    , Seq(
                                        CallT(SVar("eval_0_0"), [], [])
                                      , Seq(
                                          Match(Var("v_0"))
                                        , Seq(
                                            Build(Var("x_0"))
                                          , Seq(
                                              Build(
                                                Anno(
                                                  Op("Mul", [Var("u_0"), Var("v_0")])
                                                , Op("Nil", [])
                                                )
                                              )
                                            , CallT(SVar("eval_0_0"), [], [])
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  , Id()
                  , GuardedLChoice(
                      Scope(
                        ["r_0"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                "Add"
                              , [Anno(Op("Zero", []), Wld()), Var("r_0")]
                              )
                            , Wld()
                            )
                          )
                        , Seq(
                            Build(Var("r_0"))
                          , CallT(SVar("eval_0_0"), [], [])
                          )
                        )
                      )
                    , Id()
                    , GuardedLChoice(
                        Scope(
                          ["p_0", "q_0"]
                        , Seq(
                            Match(
                              Anno(
                                Op(
                                  "Add"
                                , [Anno(Op("Succ", [Var("p_0")]), Wld()), Var("q_0")]
                                )
                              , Wld()
                              )
                            )
                          , Seq(
                              Build(
                                Anno(
                                  Op(
                                    "Succ"
                                  , [ Anno(
                                        Op("Add", [Var("p_0"), Var("q_0")])
                                      , Op("Nil", [])
                                      )
                                    ]
                                  )
                                , Op("Nil", [])
                                )
                              )
                            , CallT(SVar("eval_0_0"), [], [])
                            )
                          )
                        )
                      , Id()
                      , Scope(
                          ["n_0", "o_0"]
                        , Seq(
                            Match(
                              Anno(
                                Op("Add", [Var("n_0"), Var("o_0")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Build(
                                Anno(
                                  Op("Add", [Var("n_0"), Var("o_0")])
                                , Op("Nil", [])
                                )
                              )
                            , CallT(SVar("eval_0_0"), [], [])
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Anno__Cong_____2_0"
        , [ VarDec(
              "h_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_1", "e_1", "f_1", "g_1"]
          , Seq(
              Match(Anno(Var("d_1"), Var("e_1")))
            , Seq(
                Build(Var("d_1"))
              , Seq(
                  CallT(SVar("h_1"), [], [])
                , Seq(
                    Match(Var("f_1"))
                  , Seq(
                      Build(Var("e_1"))
                    , Seq(
                        CallT(SVar("i_1"), [], [])
                      , Seq(
                          Match(Var("g_1"))
                        , Build(Anno(Var("f_1"), Var("g_1")))
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Zero_0_0"
        , []
        , []
        , Match(Anno(Op("Zero", []), Wld()))
        )
      , SDefT(
          "Succ_1_0"
        , [ VarDec(
              "j_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_1", "p_1", "r_1"]
          , Seq(
              Match(
                Anno(Op("Succ", [Var("p_1")]), Var("q_1"))
              )
            , Seq(
                Build(Var("p_1"))
              , Seq(
                  CallT(SVar("j_1"), [], [])
                , Seq(
                    Match(Var("r_1"))
                  , Build(
                      Anno(Op("Succ", [Var("r_1")]), Var("q_1"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Mul_2_0"
        , [ VarDec(
              "k_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_1", "s_1", "t_1", "v_1", "w_1"]
          , Seq(
              Match(
                Anno(
                  Op("Mul", [Var("s_1"), Var("t_1")])
                , Var("u_1")
                )
              )
            , Seq(
                Build(Var("s_1"))
              , Seq(
                  CallT(SVar("k_1"), [], [])
                , Seq(
                    Match(Var("v_1"))
                  , Seq(
                      Build(Var("t_1"))
                    , Seq(
                        CallT(SVar("l_1"), [], [])
                      , Seq(
                          Match(Var("w_1"))
                        , Build(
                            Anno(
                              Op("Mul", [Var("v_1"), Var("w_1")])
                            , Var("u_1")
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Add_2_0"
        , [ VarDec(
              "m_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_1", "x_1", "y_1", "a_2", "b_2"]
          , Seq(
              Match(
                Anno(
                  Op("Add", [Var("x_1"), Var("y_1")])
                , Var("z_1")
                )
              )
            , Seq(
                Build(Var("x_1"))
              , Seq(
                  CallT(SVar("m_1"), [], [])
                , Seq(
                    Match(Var("a_2"))
                  , Seq(
                      Build(Var("y_1"))
                    , Seq(
                        CallT(SVar("n_1"), [], [])
                      , Seq(
                          Match(Var("b_2"))
                        , Build(
                            Anno(
                              Op("Add", [Var("a_2"), Var("b_2")])
                            , Var("z_1")
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Nil_0_0"
        , []
        , []
        , Match(Anno(Op("Nil", []), Wld()))
        )
      , SDefT(
          "DR__UNDEFINE_1_0"
        , [ VarDec(
              "o_1"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_2", "c_2", "e_2"]
          , Seq(
              Match(
                Anno(Op("DR_UNDEFINE", [Var("c_2")]), Var("d_2"))
              )
            , Seq(
                Build(Var("c_2"))
              , Seq(
                  CallT(SVar("o_1"), [], [])
                , Seq(
                    Match(Var("e_2"))
                  , Build(
                      Anno(Op("DR_UNDEFINE", [Var("e_2")]), Var("d_2"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "DR__DUMMY_0_0"
        , []
        , []
        , Match(Anno(Op("DR_DUMMY", []), Wld()))
        )
      ]
    )
  ]
)
