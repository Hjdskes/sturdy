Specification(
  [ Signature(
      [ Constructors(
          [ OpDecl(
              "Var"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "App"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Abs"
            , FunType(
                [ConstType(SortNoArgs("String")), ConstType(SortNoArgs("Type")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl("Zero", ConstType(SortNoArgs("Exp")))
          , OpDecl(
              "Succ"
            , FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "Pred"
            , FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "Ifz"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl("Num", ConstType(SortNoArgs("Type")))
          , OpDecl(
              "Fun"
            , FunType(
                [ConstType(SortNoArgs("Type")), ConstType(SortNoArgs("Type"))]
              , ConstType(SortNoArgs("Type"))
              )
            )
          , OpDecl("Nil", ConstType(Sort("List", [SortVar("a")])))
          , OpDecl(
              "Cons"
            , FunType(
                [ConstType(SortVar("a")), ConstType(Sort("List", [SortVar("a")]))]
              , ConstType(Sort("List", [SortVar("a")]))
              )
            )
          , OpDeclInj(
              FunType(
                [ConstType(SortVar("a")), ConstType(SortVar("b"))]
              , ConstType(SortTuple([SortVar("a"), SortVar("b")]))
              )
            )
          , OpDecl("Builtin", ConstType(SortNoArgs("String")))
          ]
        )
      ]
    )
  , Strategies(
      [ SDefT(
          "check_0_0"
        , []
        , []
        , GuardedLChoice(
            Scope(
              ["v_1", "w_1"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [Var("w_1"), Anno(Op("Var", [Var("v_1")]), Wld())]
                    )
                  , Wld()
                  )
                )
              , Seq(
                  Build(
                    Anno(
                      Op("", [Var("v_1"), Var("w_1")])
                    , Op("Nil", [])
                    )
                  )
                , CallT(SVar("lookup_0_0"), [], [])
                )
              )
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["r_1", "s_1", "t_1", "u_1"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        ""
                      , [ Var("t_1")
                        , Anno(
                            Op(
                              "Abs"
                            , [Var("r_1"), Var("s_1"), Var("u_1")]
                            )
                          , Wld()
                          )
                        ]
                      )
                    , Wld()
                    )
                  )
                , Seq(
                    Build(
                      Anno(
                        Op(
                          ""
                        , [ Anno(
                              Op(
                                "Cons"
                              , [ Anno(
                                    Op("", [Var("r_1"), Var("s_1")])
                                  , Op("Nil", [])
                                  )
                                , Var("t_1")
                                ]
                              )
                            , Op("Nil", [])
                            )
                          , Var("u_1")
                          ]
                        )
                      , Op("Nil", [])
                      )
                    )
                  , CallT(SVar("check_0_0"), [], [])
                  )
                )
              )
            , Id()
            , GuardedLChoice(
                Scope(
                  ["l_1", "m_1", "n_1", "o_1", "p_1", "q_1"]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          ""
                        , [ Var("n_1")
                          , Anno(
                              Op("App", [Var("l_1"), Var("o_1")])
                            , Wld()
                            )
                          ]
                        )
                      , Wld()
                      )
                    )
                  , Seq(
                      Match(Var("q_1"))
                    , Seq(
                        Build(
                          Anno(
                            Op("", [Var("n_1"), Var("l_1")])
                          , Op("Nil", [])
                          )
                        )
                      , Seq(
                          CallT(SVar("check_0_0"), [], [])
                        , Seq(
                            Match(
                              Anno(
                                Op("Fun", [Var("p_1"), Var("m_1")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("n_1"), Var("o_1")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("check_0_0"), [], [])
                              , Seq(
                                  Match(Var("p_1"))
                                , Seq(Build(Var("q_1")), Build(Var("m_1")))
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
                          ""
                        , [Wld(), Anno(Op("Zero", []), Wld())]
                        )
                      , Wld()
                      )
                    )
                  , Build(Anno(Op("Num", []), Op("Nil", [])))
                  )
                , Id()
                , GuardedLChoice(
                    Scope(
                      ["i_1", "j_1", "k_1"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              ""
                            , [Var("i_1"), Anno(Op("Succ", [Var("j_1")]), Wld())]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("k_1"))
                        , Seq(
                            Build(
                              Anno(
                                Op("", [Var("i_1"), Var("j_1")])
                              , Op("Nil", [])
                              )
                            )
                          , Seq(
                              CallT(SVar("check_0_0"), [], [])
                            , Seq(
                                Match(Anno(Op("Num", []), Wld()))
                              , Seq(
                                  Build(Var("k_1"))
                                , Build(Anno(Op("Num", []), Op("Nil", [])))
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
                        ["f_1", "g_1", "h_1"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                ""
                              , [Var("f_1"), Anno(Op("Pred", [Var("g_1")]), Wld())]
                              )
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("h_1"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("f_1"), Var("g_1")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("check_0_0"), [], [])
                              , Seq(
                                  Match(Anno(Op("Num", []), Wld()))
                                , Seq(
                                    Build(Var("h_1"))
                                  , Build(Anno(Op("Num", []), Op("Nil", [])))
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    , Id()
                    , Scope(
                        ["z_0", "a_1", "b_1", "c_1", "d_1", "e_1"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                ""
                              , [ Var("b_1")
                                , Anno(
                                    Op(
                                      "Ifz"
                                    , [Var("a_1"), Var("c_1"), Var("z_0")]
                                    )
                                  , Wld()
                                  )
                                ]
                              )
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("e_1"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("b_1"), Var("a_1")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("check_0_0"), [], [])
                              , Seq(
                                  Match(Anno(Op("Num", []), Wld()))
                                , Seq(
                                    Build(
                                      Anno(
                                        Op("", [Var("b_1"), Var("c_1")])
                                      , Op("Nil", [])
                                      )
                                    )
                                  , Seq(
                                      CallT(SVar("check_0_0"), [], [])
                                    , Seq(
                                        Match(Var("d_1"))
                                      , Seq(
                                          Build(
                                            Anno(
                                              Op("", [Var("b_1"), Var("c_1")])
                                            , Op("Nil", [])
                                            )
                                          )
                                        , Seq(
                                            CallT(SVar("check_0_0"), [], [])
                                          , Seq(
                                              Match(Var("d_1"))
                                            , Seq(Build(Var("e_1")), Build(Var("d_1")))
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
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "eval_0_0"
        , []
        , []
        , GuardedLChoice(
            Scope(
              ["a_3", "b_3"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [Var("b_3"), Anno(Op("Var", [Var("a_3")]), Wld())]
                    )
                  , Wld()
                  )
                )
              , Seq(
                  Build(
                    Anno(
                      Op("", [Var("a_3"), Var("b_3")])
                    , Op("Nil", [])
                    )
                  )
                , CallT(SVar("lookup_0_0"), [], [])
                )
              )
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["w_2", "x_2", "y_2", "z_2"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        ""
                      , [ Var("w_2")
                        , Anno(
                            Op(
                              "Abs"
                            , [Var("x_2"), Var("y_2"), Var("z_2")]
                            )
                          , Wld()
                          )
                        ]
                      )
                    , Wld()
                    )
                  )
                , Build(
                    Anno(
                      Op(
                        "Abs"
                      , [Var("x_2"), Var("y_2"), Var("z_2")]
                      )
                    , Op("Nil", [])
                    )
                  )
                )
              )
            , Id()
            , GuardedLChoice(
                Scope(
                  ["p_2", "q_2", "r_2", "s_2", "t_2", "u_2", "v_2"]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          ""
                        , [ Var("s_2")
                          , Anno(
                              Op("App", [Var("p_2"), Var("t_2")])
                            , Wld()
                            )
                          ]
                        )
                      , Wld()
                      )
                    )
                  , Seq(
                      Match(Var("v_2"))
                    , Seq(
                        Build(
                          Anno(
                            Op("", [Var("s_2"), Var("p_2")])
                          , Op("Nil", [])
                          )
                        )
                      , Seq(
                          CallT(SVar("eval_0_0"), [], [])
                        , Seq(
                            Match(
                              Anno(
                                Op("Abs", [Var("q_2"), Wld(), Var("r_2")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("s_2"), Var("t_2")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("eval_0_0"), [], [])
                              , Seq(
                                  Match(Var("u_2"))
                                , Seq(
                                    Build(Var("v_2"))
                                  , Seq(
                                      Build(
                                        Anno(
                                          Op(
                                            ""
                                          , [ Anno(
                                                Op(
                                                  "Cons"
                                                , [ Anno(
                                                      Op("", [Var("q_2"), Var("u_2")])
                                                    , Op("Nil", [])
                                                    )
                                                  , Var("s_2")
                                                  ]
                                                )
                                              , Op("Nil", [])
                                              )
                                            , Var("r_2")
                                            ]
                                          )
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
              , Id()
              , GuardedLChoice(
                  Seq(
                    Match(
                      Anno(
                        Op(
                          ""
                        , [Wld(), Anno(Op("Zero", []), Wld())]
                        )
                      , Wld()
                      )
                    )
                  , Build(Anno(Op("Zero", []), Op("Nil", [])))
                  )
                , Id()
                , GuardedLChoice(
                    Scope(
                      ["l_2", "m_2", "n_2", "o_2"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              ""
                            , [Var("l_2"), Anno(Op("Succ", [Var("m_2")]), Wld())]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("o_2"))
                        , Seq(
                            Build(
                              Anno(
                                Op("", [Var("l_2"), Var("m_2")])
                              , Op("Nil", [])
                              )
                            )
                          , Seq(
                              CallT(SVar("eval_0_0"), [], [])
                            , Seq(
                                Match(Var("n_2"))
                              , Seq(
                                  Build(Var("o_2"))
                                , Build(
                                    Anno(
                                      Op("Succ", [Var("n_2")])
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
                      Scope(
                        ["h_2", "i_2", "j_2", "k_2"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                ""
                              , [Var("h_2"), Anno(Op("Pred", [Var("i_2")]), Wld())]
                              )
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("k_2"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("h_2"), Var("i_2")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("eval_0_0"), [], [])
                              , Seq(
                                  Match(Var("j_2"))
                                , Seq(
                                    Build(Var("k_2"))
                                  , Build(
                                      Anno(
                                        Op("Pred", [Var("j_2")])
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
                        Scope(
                          ["c_2", "d_2", "e_2", "f_2", "g_2"]
                        , Seq(
                            Match(
                              Anno(
                                Op(
                                  ""
                                , [ Var("e_2")
                                  , Anno(
                                      Op(
                                        "Ifz"
                                      , [Var("f_2"), Var("d_2"), Var("c_2")]
                                      )
                                    , Wld()
                                    )
                                  ]
                                )
                              , Wld()
                              )
                            )
                          , Seq(
                              Match(Var("g_2"))
                            , Seq(
                                Build(
                                  Anno(
                                    Op("", [Var("e_2"), Var("f_2")])
                                  , Op("Nil", [])
                                  )
                                )
                              , Seq(
                                  CallT(SVar("eval_0_0"), [], [])
                                , Seq(
                                    Match(Anno(Op("Zero", []), Wld()))
                                  , Seq(
                                      Build(Var("g_2"))
                                    , Seq(
                                        Build(
                                          Anno(
                                            Op("", [Var("e_2"), Var("d_2")])
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
                      , Id()
                      , Scope(
                          ["x_1", "y_1", "z_1", "a_2", "b_2"]
                        , Seq(
                            Match(
                              Anno(
                                Op(
                                  ""
                                , [ Var("z_1")
                                  , Anno(
                                      Op(
                                        "Ifz"
                                      , [Var("x_1"), Var("a_2"), Var("y_1")]
                                      )
                                    , Wld()
                                    )
                                  ]
                                )
                              , Wld()
                              )
                            )
                          , Seq(
                              Match(Var("b_2"))
                            , Seq(
                                Build(
                                  Anno(
                                    Op("", [Var("z_1"), Var("a_2")])
                                  , Op("Nil", [])
                                  )
                                )
                              , Seq(
                                  CallT(SVar("eval_0_0"), [], [])
                                , Seq(
                                    Match(Anno(Op("Succ", [Wld()]), Wld()))
                                  , Seq(
                                      Build(Var("b_2"))
                                    , Seq(
                                        Build(
                                          Anno(
                                            Op("", [Var("z_1"), Var("y_1")])
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
            )
          )
        )
      , SDefT(
          "check_eval_0_0"
        , []
        , []
        , Scope(
            ["c_3", "d_3"]
          , Seq(
              Match(Var("c_3"))
            , Seq(
                Match(Var("d_3"))
              , Seq(
                  Build(
                    Anno(
                      Op(
                        ""
                      , [Anno(Op("Nil", []), Op("Nil", [])), Var("c_3")]
                      )
                    , Op("Nil", [])
                    )
                  )
                , Seq(
                    CallT(SVar("check_0_0"), [], [])
                  , Seq(
                      Build(Var("d_3"))
                    , Seq(
                        Build(
                          Anno(
                            Op(
                              ""
                            , [Anno(Op("Nil", []), Op("Nil", [])), Var("c_3")]
                            )
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
      , SDefT(
          "lookup_0_0"
        , []
        , []
        , Scope(
            ["e_3", "f_3", "g_3"]
          , GuardedLChoice(
              Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [ Var("f_3")
                      , Anno(
                          Op(
                            "Cons"
                          , [ Anno(
                                Op("", [Var("f_3"), Var("e_3")])
                              , Wld()
                              )
                            , Wld()
                            ]
                          )
                        , Wld()
                        )
                      ]
                    )
                  , Wld()
                  )
                )
              , Build(Var("e_3"))
              )
            , Id()
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [ Var("f_3")
                      , Anno(Op("Cons", [Wld(), Var("g_3")]), Wld())
                      ]
                    )
                  , Wld()
                  )
                )
              , Seq(
                  Build(
                    Anno(
                      Op("", [Var("f_3"), Var("g_3")])
                    , Op("Nil", [])
                    )
                  )
                , CallT(SVar("lookup_0_0"), [], [])
                )
              )
            )
          )
        )
      , SDefT(
          "Anno__Cong_____2_0"
        , [ VarDec(
              "l_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "m_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_3", "i_3", "j_3", "k_3"]
          , Seq(
              Match(Anno(Var("h_3"), Var("i_3")))
            , Seq(
                Build(Var("h_3"))
              , Seq(
                  CallT(SVar("l_3"), [], [])
                , Seq(
                    Match(Var("j_3"))
                  , Seq(
                      Build(Var("i_3"))
                    , Seq(
                        CallT(SVar("m_3"), [], [])
                      , Seq(
                          Match(Var("k_3"))
                        , Build(Anno(Var("j_3"), Var("k_3")))
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
          "Var_1_0"
        , [ VarDec(
              "n_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_4", "f_4", "h_4"]
          , Seq(
              Match(
                Anno(Op("Var", [Var("f_4")]), Var("g_4"))
              )
            , Seq(
                Build(Var("f_4"))
              , Seq(
                  CallT(SVar("n_3"), [], [])
                , Seq(
                    Match(Var("h_4"))
                  , Build(
                      Anno(Op("Var", [Var("h_4")]), Var("g_4"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "App_2_0"
        , [ VarDec(
              "o_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "p_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_4", "i_4", "j_4", "l_4", "m_4"]
          , Seq(
              Match(
                Anno(
                  Op("App", [Var("i_4"), Var("j_4")])
                , Var("k_4")
                )
              )
            , Seq(
                Build(Var("i_4"))
              , Seq(
                  CallT(SVar("o_3"), [], [])
                , Seq(
                    Match(Var("l_4"))
                  , Seq(
                      Build(Var("j_4"))
                    , Seq(
                        CallT(SVar("p_3"), [], [])
                      , Seq(
                          Match(Var("m_4"))
                        , Build(
                            Anno(
                              Op("App", [Var("l_4"), Var("m_4")])
                            , Var("k_4")
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
          "Abs_3_0"
        , [ VarDec(
              "q_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "r_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_4", "n_4", "o_4", "p_4", "r_4", "s_4", "t_4"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Abs"
                  , [Var("n_4"), Var("o_4"), Var("p_4")]
                  )
                , Var("q_4")
                )
              )
            , Seq(
                Build(Var("n_4"))
              , Seq(
                  CallT(SVar("q_3"), [], [])
                , Seq(
                    Match(Var("r_4"))
                  , Seq(
                      Build(Var("o_4"))
                    , Seq(
                        CallT(SVar("r_3"), [], [])
                      , Seq(
                          Match(Var("s_4"))
                        , Seq(
                            Build(Var("p_4"))
                          , Seq(
                              CallT(SVar("s_3"), [], [])
                            , Seq(
                                Match(Var("t_4"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Abs"
                                    , [Var("r_4"), Var("s_4"), Var("t_4")]
                                    )
                                  , Var("q_4")
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
              "t_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_4", "u_4", "w_4"]
          , Seq(
              Match(
                Anno(Op("Succ", [Var("u_4")]), Var("v_4"))
              )
            , Seq(
                Build(Var("u_4"))
              , Seq(
                  CallT(SVar("t_3"), [], [])
                , Seq(
                    Match(Var("w_4"))
                  , Build(
                      Anno(Op("Succ", [Var("w_4")]), Var("v_4"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Pred_1_0"
        , [ VarDec(
              "u_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_4", "x_4", "z_4"]
          , Seq(
              Match(
                Anno(Op("Pred", [Var("x_4")]), Var("y_4"))
              )
            , Seq(
                Build(Var("x_4"))
              , Seq(
                  CallT(SVar("u_3"), [], [])
                , Seq(
                    Match(Var("z_4"))
                  , Build(
                      Anno(Op("Pred", [Var("z_4")]), Var("y_4"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Ifz_3_0"
        , [ VarDec(
              "v_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "w_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_5", "a_5", "b_5", "c_5", "e_5", "f_5", "g_5"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Ifz"
                  , [Var("a_5"), Var("b_5"), Var("c_5")]
                  )
                , Var("d_5")
                )
              )
            , Seq(
                Build(Var("a_5"))
              , Seq(
                  CallT(SVar("v_3"), [], [])
                , Seq(
                    Match(Var("e_5"))
                  , Seq(
                      Build(Var("b_5"))
                    , Seq(
                        CallT(SVar("w_3"), [], [])
                      , Seq(
                          Match(Var("f_5"))
                        , Seq(
                            Build(Var("c_5"))
                          , Seq(
                              CallT(SVar("x_3"), [], [])
                            , Seq(
                                Match(Var("g_5"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Ifz"
                                    , [Var("e_5"), Var("f_5"), Var("g_5")]
                                    )
                                  , Var("d_5")
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
        )
      , SDefT(
          "Num_0_0"
        , []
        , []
        , Match(Anno(Op("Num", []), Wld()))
        )
      , SDefT(
          "Fun_2_0"
        , [ VarDec(
              "y_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "z_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_5", "h_5", "i_5", "k_5", "l_5"]
          , Seq(
              Match(
                Anno(
                  Op("Fun", [Var("h_5"), Var("i_5")])
                , Var("j_5")
                )
              )
            , Seq(
                Build(Var("h_5"))
              , Seq(
                  CallT(SVar("y_3"), [], [])
                , Seq(
                    Match(Var("k_5"))
                  , Seq(
                      Build(Var("i_5"))
                    , Seq(
                        CallT(SVar("z_3"), [], [])
                      , Seq(
                          Match(Var("l_5"))
                        , Build(
                            Anno(
                              Op("Fun", [Var("k_5"), Var("l_5")])
                            , Var("j_5")
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
          "Cons_2_0"
        , [ VarDec(
              "a_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_5", "m_5", "n_5", "p_5", "q_5"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("m_5"), Var("n_5")])
                , Var("o_5")
                )
              )
            , Seq(
                Build(Var("m_5"))
              , Seq(
                  CallT(SVar("a_4"), [], [])
                , Seq(
                    Match(Var("p_5"))
                  , Seq(
                      Build(Var("n_5"))
                    , Seq(
                        CallT(SVar("b_4"), [], [])
                      , Seq(
                          Match(Var("q_5"))
                        , Build(
                            Anno(
                              Op("Cons", [Var("p_5"), Var("q_5")])
                            , Var("o_5")
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
          "_2_0"
        , [ VarDec(
              "c_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_5", "r_5", "s_5", "u_5", "v_5"]
          , Seq(
              Match(
                Anno(
                  Op("", [Var("r_5"), Var("s_5")])
                , Var("t_5")
                )
              )
            , Seq(
                Build(Var("r_5"))
              , Seq(
                  CallT(SVar("c_4"), [], [])
                , Seq(
                    Match(Var("u_5"))
                  , Seq(
                      Build(Var("s_5"))
                    , Seq(
                        CallT(SVar("d_4"), [], [])
                      , Seq(
                          Match(Var("v_5"))
                        , Build(
                            Anno(
                              Op("", [Var("u_5"), Var("v_5")])
                            , Var("t_5")
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
          "Builtin_0_0"
        , []
        , []
        , Match(Anno(Op("Builtin", []), Wld()))
        )
      , SDefT(
          "DR__UNDEFINE_1_0"
        , [ VarDec(
              "e_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_5", "w_5", "y_5"]
          , Seq(
              Match(
                Anno(Op("DR_UNDEFINE", [Var("w_5")]), Var("x_5"))
              )
            , Seq(
                Build(Var("w_5"))
              , Seq(
                  CallT(SVar("e_4"), [], [])
                , Seq(
                    Match(Var("y_5"))
                  , Build(
                      Anno(Op("DR_UNDEFINE", [Var("y_5")]), Var("x_5"))
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
