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
          , OpDeclInj(ConstType(SortTuple([])))
          , OpDeclInj(
              FunType(
                [ConstType(SortVar("a"))]
              , ConstType(SortTuple([SortVar("a")]))
              )
            )
          , OpDeclInj(
              FunType(
                [ConstType(SortVar("a")), ConstType(SortVar("b"))]
              , ConstType(SortTuple([SortVar("a"), SortVar("b")]))
              )
            )
          , OpDeclInj(
              FunType(
                [ConstType(SortVar("a")), ConstType(SortVar("b")), ConstType(SortVar("c"))]
              , ConstType(
                  SortTuple([SortVar("a"), SortVar("b"), SortVar("c")])
                )
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
              ["z_1", "a_2"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [Var("a_2"), Anno(Op("Var", [Var("z_1")]), Wld())]
                    )
                  , Wld()
                  )
                )
              , Seq(
                  Build(
                    Anno(
                      Op("", [Var("z_1"), Var("a_2")])
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
                ["v_1", "w_1", "x_1", "y_1"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        ""
                      , [ Var("x_1")
                        , Anno(
                            Op(
                              "Abs"
                            , [Var("v_1"), Var("w_1"), Var("y_1")]
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
                                    Op("", [Var("v_1"), Var("w_1")])
                                  , Op("Nil", [])
                                  )
                                , Var("x_1")
                                ]
                              )
                            , Op("Nil", [])
                            )
                          , Var("y_1")
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
                  ["p_1", "q_1", "r_1", "s_1", "t_1", "u_1"]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          ""
                        , [ Var("r_1")
                          , Anno(
                              Op("App", [Var("p_1"), Var("s_1")])
                            , Wld()
                            )
                          ]
                        )
                      , Wld()
                      )
                    )
                  , Seq(
                      Match(Var("u_1"))
                    , Seq(
                        Build(
                          Anno(
                            Op("", [Var("r_1"), Var("p_1")])
                          , Op("Nil", [])
                          )
                        )
                      , Seq(
                          CallT(SVar("check_0_0"), [], [])
                        , Seq(
                            Match(
                              Anno(
                                Op("Fun", [Var("t_1"), Var("q_1")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("r_1"), Var("s_1")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("check_0_0"), [], [])
                              , Seq(
                                  Match(Var("t_1"))
                                , Seq(Build(Var("u_1")), Build(Var("q_1")))
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
                      ["m_1", "n_1", "o_1"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              ""
                            , [Var("m_1"), Anno(Op("Succ", [Var("n_1")]), Wld())]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("o_1"))
                        , Seq(
                            Build(
                              Anno(
                                Op("", [Var("m_1"), Var("n_1")])
                              , Op("Nil", [])
                              )
                            )
                          , Seq(
                              CallT(SVar("check_0_0"), [], [])
                            , Seq(
                                Match(Anno(Op("Num", []), Wld()))
                              , Seq(
                                  Build(Var("o_1"))
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
                        ["j_1", "k_1", "l_1"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                ""
                              , [Var("j_1"), Anno(Op("Pred", [Var("k_1")]), Wld())]
                              )
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("l_1"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("j_1"), Var("k_1")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("check_0_0"), [], [])
                              , Seq(
                                  Match(Anno(Op("Num", []), Wld()))
                                , Seq(
                                    Build(Var("l_1"))
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
                        ["d_1", "e_1", "f_1", "g_1", "h_1", "i_1"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                ""
                              , [ Var("f_1")
                                , Anno(
                                    Op(
                                      "Ifz"
                                    , [Var("e_1"), Var("g_1"), Var("d_1")]
                                    )
                                  , Wld()
                                  )
                                ]
                              )
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("i_1"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("f_1"), Var("e_1")])
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
                                        Op("", [Var("f_1"), Var("g_1")])
                                      , Op("Nil", [])
                                      )
                                    )
                                  , Seq(
                                      CallT(SVar("check_0_0"), [], [])
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
                                              Match(Var("h_1"))
                                            , Seq(Build(Var("i_1")), Build(Var("h_1")))
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
              ["e_3", "f_3"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [Var("f_3"), Anno(Op("Var", [Var("e_3")]), Wld())]
                    )
                  , Wld()
                  )
                )
              , Seq(
                  Build(
                    Anno(
                      Op("", [Var("e_3"), Var("f_3")])
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
                ["a_3", "b_3", "c_3", "d_3"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        ""
                      , [ Var("a_3")
                        , Anno(
                            Op(
                              "Abs"
                            , [Var("b_3"), Var("c_3"), Var("d_3")]
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
                      , [Var("b_3"), Var("c_3"), Var("d_3")]
                      )
                    , Op("Nil", [])
                    )
                  )
                )
              )
            , Id()
            , GuardedLChoice(
                Scope(
                  ["t_2", "u_2", "v_2", "w_2", "x_2", "y_2", "z_2"]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          ""
                        , [ Var("w_2")
                          , Anno(
                              Op("App", [Var("t_2"), Var("x_2")])
                            , Wld()
                            )
                          ]
                        )
                      , Wld()
                      )
                    )
                  , Seq(
                      Match(Var("z_2"))
                    , Seq(
                        Build(
                          Anno(
                            Op("", [Var("w_2"), Var("t_2")])
                          , Op("Nil", [])
                          )
                        )
                      , Seq(
                          CallT(SVar("eval_0_0"), [], [])
                        , Seq(
                            Match(
                              Anno(
                                Op("Abs", [Var("u_2"), Wld(), Var("v_2")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("w_2"), Var("x_2")])
                                , Op("Nil", [])
                                )
                              )
                            , Seq(
                                CallT(SVar("eval_0_0"), [], [])
                              , Seq(
                                  Match(Var("y_2"))
                                , Seq(
                                    Build(Var("z_2"))
                                  , Seq(
                                      Build(
                                        Anno(
                                          Op(
                                            ""
                                          , [ Anno(
                                                Op(
                                                  "Cons"
                                                , [ Anno(
                                                      Op("", [Var("u_2"), Var("y_2")])
                                                    , Op("Nil", [])
                                                    )
                                                  , Var("w_2")
                                                  ]
                                                )
                                              , Op("Nil", [])
                                              )
                                            , Var("v_2")
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
                      ["p_2", "q_2", "r_2", "s_2"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              ""
                            , [Var("p_2"), Anno(Op("Succ", [Var("q_2")]), Wld())]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("s_2"))
                        , Seq(
                            Build(
                              Anno(
                                Op("", [Var("p_2"), Var("q_2")])
                              , Op("Nil", [])
                              )
                            )
                          , Seq(
                              CallT(SVar("eval_0_0"), [], [])
                            , Seq(
                                Match(Var("r_2"))
                              , Seq(
                                  Build(Var("s_2"))
                                , Build(
                                    Anno(
                                      Op("Succ", [Var("r_2")])
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
                        ["l_2", "m_2", "n_2", "o_2"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                ""
                              , [Var("l_2"), Anno(Op("Pred", [Var("m_2")]), Wld())]
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
                                        Op("Pred", [Var("n_2")])
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
                          ["g_2", "h_2", "i_2", "j_2", "k_2"]
                        , Seq(
                            Match(
                              Anno(
                                Op(
                                  ""
                                , [ Var("i_2")
                                  , Anno(
                                      Op(
                                        "Ifz"
                                      , [Var("j_2"), Var("h_2"), Var("g_2")]
                                      )
                                    , Wld()
                                    )
                                  ]
                                )
                              , Wld()
                              )
                            )
                          , Seq(
                              Match(Var("k_2"))
                            , Seq(
                                Build(
                                  Anno(
                                    Op("", [Var("i_2"), Var("j_2")])
                                  , Op("Nil", [])
                                  )
                                )
                              , Seq(
                                  CallT(SVar("eval_0_0"), [], [])
                                , Seq(
                                    Match(Anno(Op("Zero", []), Wld()))
                                  , Seq(
                                      Build(Var("k_2"))
                                    , Seq(
                                        Build(
                                          Anno(
                                            Op("", [Var("i_2"), Var("h_2")])
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
                          ["b_2", "c_2", "d_2", "e_2", "f_2"]
                        , Seq(
                            Match(
                              Anno(
                                Op(
                                  ""
                                , [ Var("d_2")
                                  , Anno(
                                      Op(
                                        "Ifz"
                                      , [Var("b_2"), Var("e_2"), Var("c_2")]
                                      )
                                    , Wld()
                                    )
                                  ]
                                )
                              , Wld()
                              )
                            )
                          , Seq(
                              Match(Var("f_2"))
                            , Seq(
                                Build(
                                  Anno(
                                    Op("", [Var("d_2"), Var("e_2")])
                                  , Op("Nil", [])
                                  )
                                )
                              , Seq(
                                  CallT(SVar("eval_0_0"), [], [])
                                , Seq(
                                    Match(Anno(Op("Succ", [Wld()]), Wld()))
                                  , Seq(
                                      Build(Var("f_2"))
                                    , Seq(
                                        Build(
                                          Anno(
                                            Op("", [Var("d_2"), Var("c_2")])
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
            ["g_3", "h_3"]
          , Seq(
              Match(Var("g_3"))
            , Seq(
                Match(Var("h_3"))
              , Seq(
                  Build(
                    Anno(
                      Op(
                        ""
                      , [Anno(Op("Nil", []), Op("Nil", [])), Var("g_3")]
                      )
                    , Op("Nil", [])
                    )
                  )
                , Seq(
                    CallT(SVar("check_0_0"), [], [])
                  , Seq(
                      Build(Var("h_3"))
                    , Seq(
                        Build(
                          Anno(
                            Op(
                              ""
                            , [Anno(Op("Nil", []), Op("Nil", [])), Var("g_3")]
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
            ["i_3", "j_3", "k_3"]
          , GuardedLChoice(
              Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [ Var("j_3")
                      , Anno(
                          Op(
                            "Cons"
                          , [ Anno(
                                Op("", [Var("j_3"), Var("i_3")])
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
              , Build(Var("i_3"))
              )
            , Id()
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [ Var("j_3")
                      , Anno(Op("Cons", [Wld(), Var("k_3")]), Wld())
                      ]
                    )
                  , Wld()
                  )
                )
              , Seq(
                  Build(
                    Anno(
                      Op("", [Var("j_3"), Var("k_3")])
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
              "p_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_3", "m_3", "n_3", "o_3"]
          , Seq(
              Match(Anno(Var("l_3"), Var("m_3")))
            , Seq(
                Build(Var("l_3"))
              , Seq(
                  CallT(SVar("p_3"), [], [])
                , Seq(
                    Match(Var("n_3"))
                  , Seq(
                      Build(Var("m_3"))
                    , Seq(
                        CallT(SVar("q_3"), [], [])
                      , Seq(
                          Match(Var("o_3"))
                        , Build(Anno(Var("n_3"), Var("o_3")))
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
              "r_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_4", "n_4", "p_4"]
          , Seq(
              Match(
                Anno(Op("Var", [Var("n_4")]), Var("o_4"))
              )
            , Seq(
                Build(Var("n_4"))
              , Seq(
                  CallT(SVar("r_3"), [], [])
                , Seq(
                    Match(Var("p_4"))
                  , Build(
                      Anno(Op("Var", [Var("p_4")]), Var("o_4"))
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
              "s_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_4", "q_4", "r_4", "t_4", "u_4"]
          , Seq(
              Match(
                Anno(
                  Op("App", [Var("q_4"), Var("r_4")])
                , Var("s_4")
                )
              )
            , Seq(
                Build(Var("q_4"))
              , Seq(
                  CallT(SVar("s_3"), [], [])
                , Seq(
                    Match(Var("t_4"))
                  , Seq(
                      Build(Var("r_4"))
                    , Seq(
                        CallT(SVar("t_3"), [], [])
                      , Seq(
                          Match(Var("u_4"))
                        , Build(
                            Anno(
                              Op("App", [Var("t_4"), Var("u_4")])
                            , Var("s_4")
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
              "u_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
          ]
        , []
        , Scope(
            ["y_4", "v_4", "w_4", "x_4", "z_4", "a_5", "b_5"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Abs"
                  , [Var("v_4"), Var("w_4"), Var("x_4")]
                  )
                , Var("y_4")
                )
              )
            , Seq(
                Build(Var("v_4"))
              , Seq(
                  CallT(SVar("u_3"), [], [])
                , Seq(
                    Match(Var("z_4"))
                  , Seq(
                      Build(Var("w_4"))
                    , Seq(
                        CallT(SVar("v_3"), [], [])
                      , Seq(
                          Match(Var("a_5"))
                        , Seq(
                            Build(Var("x_4"))
                          , Seq(
                              CallT(SVar("w_3"), [], [])
                            , Seq(
                                Match(Var("b_5"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Abs"
                                    , [Var("z_4"), Var("a_5"), Var("b_5")]
                                    )
                                  , Var("y_4")
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
              "x_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_5", "c_5", "e_5"]
          , Seq(
              Match(
                Anno(Op("Succ", [Var("c_5")]), Var("d_5"))
              )
            , Seq(
                Build(Var("c_5"))
              , Seq(
                  CallT(SVar("x_3"), [], [])
                , Seq(
                    Match(Var("e_5"))
                  , Build(
                      Anno(Op("Succ", [Var("e_5")]), Var("d_5"))
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
              "y_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_5", "f_5", "h_5"]
          , Seq(
              Match(
                Anno(Op("Pred", [Var("f_5")]), Var("g_5"))
              )
            , Seq(
                Build(Var("f_5"))
              , Seq(
                  CallT(SVar("y_3"), [], [])
                , Seq(
                    Match(Var("h_5"))
                  , Build(
                      Anno(Op("Pred", [Var("h_5")]), Var("g_5"))
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
              "z_3"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["l_5", "i_5", "j_5", "k_5", "m_5", "n_5", "o_5"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Ifz"
                  , [Var("i_5"), Var("j_5"), Var("k_5")]
                  )
                , Var("l_5")
                )
              )
            , Seq(
                Build(Var("i_5"))
              , Seq(
                  CallT(SVar("z_3"), [], [])
                , Seq(
                    Match(Var("m_5"))
                  , Seq(
                      Build(Var("j_5"))
                    , Seq(
                        CallT(SVar("a_4"), [], [])
                      , Seq(
                          Match(Var("n_5"))
                        , Seq(
                            Build(Var("k_5"))
                          , Seq(
                              CallT(SVar("b_4"), [], [])
                            , Seq(
                                Match(Var("o_5"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Ifz"
                                    , [Var("m_5"), Var("n_5"), Var("o_5")]
                                    )
                                  , Var("l_5")
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
            ["r_5", "p_5", "q_5", "s_5", "t_5"]
          , Seq(
              Match(
                Anno(
                  Op("Fun", [Var("p_5"), Var("q_5")])
                , Var("r_5")
                )
              )
            , Seq(
                Build(Var("p_5"))
              , Seq(
                  CallT(SVar("c_4"), [], [])
                , Seq(
                    Match(Var("s_5"))
                  , Seq(
                      Build(Var("q_5"))
                    , Seq(
                        CallT(SVar("d_4"), [], [])
                      , Seq(
                          Match(Var("t_5"))
                        , Build(
                            Anno(
                              Op("Fun", [Var("s_5"), Var("t_5")])
                            , Var("r_5")
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
              "e_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_5", "u_5", "v_5", "x_5", "y_5"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("u_5"), Var("v_5")])
                , Var("w_5")
                )
              )
            , Seq(
                Build(Var("u_5"))
              , Seq(
                  CallT(SVar("e_4"), [], [])
                , Seq(
                    Match(Var("x_5"))
                  , Seq(
                      Build(Var("v_5"))
                    , Seq(
                        CallT(SVar("f_4"), [], [])
                      , Seq(
                          Match(Var("y_5"))
                        , Build(
                            Anno(
                              Op("Cons", [Var("x_5"), Var("y_5")])
                            , Var("w_5")
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
          "_0_0"
        , []
        , []
        , Match(Anno(Op("", []), Wld()))
        )
      , SDefT(
          "_1_0"
        , [ VarDec(
              "g_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_6", "z_5", "b_6"]
          , Seq(
              Match(
                Anno(Op("", [Var("z_5")]), Var("a_6"))
              )
            , Seq(
                Build(Var("z_5"))
              , Seq(
                  CallT(SVar("g_4"), [], [])
                , Seq(
                    Match(Var("b_6"))
                  , Build(
                      Anno(Op("", [Var("b_6")]), Var("a_6"))
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
              "h_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_6", "c_6", "d_6", "f_6", "g_6"]
          , Seq(
              Match(
                Anno(
                  Op("", [Var("c_6"), Var("d_6")])
                , Var("e_6")
                )
              )
            , Seq(
                Build(Var("c_6"))
              , Seq(
                  CallT(SVar("h_4"), [], [])
                , Seq(
                    Match(Var("f_6"))
                  , Seq(
                      Build(Var("d_6"))
                    , Seq(
                        CallT(SVar("i_4"), [], [])
                      , Seq(
                          Match(Var("g_6"))
                        , Build(
                            Anno(
                              Op("", [Var("f_6"), Var("g_6")])
                            , Var("e_6")
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
          "_3_0"
        , [ VarDec(
              "j_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_6", "h_6", "i_6", "j_6", "l_6", "m_6", "n_6"]
          , Seq(
              Match(
                Anno(
                  Op(
                    ""
                  , [Var("h_6"), Var("i_6"), Var("j_6")]
                  )
                , Var("k_6")
                )
              )
            , Seq(
                Build(Var("h_6"))
              , Seq(
                  CallT(SVar("j_4"), [], [])
                , Seq(
                    Match(Var("l_6"))
                  , Seq(
                      Build(Var("i_6"))
                    , Seq(
                        CallT(SVar("k_4"), [], [])
                      , Seq(
                          Match(Var("m_6"))
                        , Seq(
                            Build(Var("j_6"))
                          , Seq(
                              CallT(SVar("l_4"), [], [])
                            , Seq(
                                Match(Var("n_6"))
                              , Build(
                                  Anno(
                                    Op(
                                      ""
                                    , [Var("l_6"), Var("m_6"), Var("n_6")]
                                    )
                                  , Var("k_6")
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
          "Builtin_0_0"
        , []
        , []
        , Match(Anno(Op("Builtin", []), Wld()))
        )
      , SDefT(
          "DR__UNDEFINE_1_0"
        , [ VarDec(
              "m_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_6", "o_6", "q_6"]
          , Seq(
              Match(
                Anno(Op("DR_UNDEFINE", [Var("o_6")]), Var("p_6"))
              )
            , Seq(
                Build(Var("o_6"))
              , Seq(
                  CallT(SVar("m_4"), [], [])
                , Seq(
                    Match(Var("q_6"))
                  , Build(
                      Anno(Op("DR_UNDEFINE", [Var("q_6")]), Var("p_6"))
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
