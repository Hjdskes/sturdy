Specification(
  [ Signature(
      [ Constructors(
          [ OpDecl("Nil", ConstType(Sort("List", [SortVar("a")])))
          , OpDecl(
              "Cons"
            , FunType(
                [ConstType(SortVar("a")), ConstType(Sort("List", [SortVar("a")]))]
              , ConstType(Sort("List", [SortVar("a")]))
              )
            )
          , OpDecl(
              "AppBin"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "OpApp"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Qop")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Product"
            , FunType([ConstType(SortNoArgs("Exps2"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "ECons"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(Sort("List", [SortNoArgs("Exp")]))]
              , ConstType(SortNoArgs("Exps2"))
              )
            )
          , OpDecl(
              "Typed"
            , FunType(
                [ ConstType(SortNoArgs("Exp"))
                , ConstType(Sort("Option", [SortNoArgs("Context")]))
                , ConstType(SortNoArgs("Type"))
                ]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Negation"
            , FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "Labeled"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("LabelBinds"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Named"
            , FunType(
                [ConstType(SortNoArgs("Qvar")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "OpApp"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Qop")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Case"
            , FunType(
                [ConstType(SortNoArgs("AnyExp")), ConstType(SortNoArgs("AltList"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Do"
            , FunType([ConstType(SortNoArgs("StmtList"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "If"
            , FunType(
                [ConstType(SortNoArgs("AnyExp")), ConstType(SortNoArgs("AnyExp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Let"
            , FunType(
                [ConstType(SortNoArgs("Declbinds")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Abs"
            , FunType(
                [ConstType(SortNoArgs("Fargs")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "RSection"
            , FunType(
                [ConstType(SortNoArgs("QopNoNeg")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "LSection"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Qop"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "Lit"
            , FunType([ConstType(SortNoArgs("Literal"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "Constr"
            , FunType([ConstType(SortNoArgs("Gcon"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "Var"
            , FunType([ConstType(SortNoArgs("Qvar"))], ConstType(SortNoArgs("Exp")))
            )
          , OpDecl(
              "ArrProcedure"
            , FunType(
                [ConstType(SortNoArgs("APat")), ConstType(SortNoArgs("ArrCommand"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDecl(
              "BinOp"
            , FunType([ConstType(SortNoArgs("Qvarsym"))], ConstType(SortNoArgs("Qvar")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvarid"))], ConstType(SortNoArgs("Qvar")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QVARID"))], ConstType(SortNoArgs("Qvarid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Varid"))], ConstType(SortNoArgs("Qvarid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qconop"))], ConstType(SortNoArgs("Qop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvarop"))], ConstType(SortNoArgs("Qop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("FlexibleContext"))], ConstType(SortNoArgs("Context")))
            )
          , OpDecl(
              "Context"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Class")]))]
              , ConstType(SortNoArgs("Context"))
              )
            )
          , OpDecl(
              "Context"
            , FunType([ConstType(SortNoArgs("Class"))], ConstType(SortNoArgs("Context")))
            )
          , OpDecl(
              "TFunBin"
            , FunType(
                [ConstType(SortNoArgs("Type")), ConstType(SortNoArgs("Type"))]
              , ConstType(SortNoArgs("Type"))
              )
            )
          , OpDecl(
              "TAppBin"
            , FunType(
                [ConstType(SortNoArgs("Type")), ConstType(SortNoArgs("Type"))]
              , ConstType(SortNoArgs("Type"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("AType"))], ConstType(SortNoArgs("Type")))
            )
          , OpDecl(
              "TProd"
            , FunType([ConstType(SortNoArgs("Types2"))], ConstType(SortNoArgs("AType")))
            )
          , OpDecl(
              "TList"
            , FunType([ConstType(SortNoArgs("Type"))], ConstType(SortNoArgs("AType")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Type"))], ConstType(SortNoArgs("AType")))
            )
          , OpDecl(
              "TVar"
            , FunType([ConstType(SortNoArgs("Tyvar"))], ConstType(SortNoArgs("AType")))
            )
          , OpDecl(
              "TCon"
            , FunType([ConstType(SortNoArgs("Gtycon"))], ConstType(SortNoArgs("AType")))
            )
          , OpDecl(
              "TCons"
            , FunType(
                [ConstType(SortNoArgs("Type")), ConstType(Sort("List", [SortNoArgs("Type")]))]
              , ConstType(SortNoArgs("Types2"))
              )
            )
          , OpDecl(
              "LabelBinds"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Fbind")]))]
              , ConstType(SortNoArgs("LabelBinds"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("AnyExp")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("DeclList"))], ConstType(SortNoArgs("Declbinds")))
            )
          , OpDeclInj(
              FunType(
                [ConstType(Sort("List", [SortNoArgs("APat")]))]
              , ConstType(SortNoArgs("Fargs"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qop"))], ConstType(SortNoArgs("QopNoNeg")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Float-HASH"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Integer-HASH"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String-HASH"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Char-HASH"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "CLitLit"
            , FunType([ConstType(SortNoArgs("CLITLIT"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "PrimDouble"
            , FunType([ConstType(SortNoArgs("PRIMDOUBLE"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "PrimFloat"
            , FunType([ConstType(SortNoArgs("PRIMFLOAT"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "PrimString"
            , FunType([ConstType(SortNoArgs("PRIMSTRING"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "PrimChar"
            , FunType([ConstType(SortNoArgs("PRIMCHAR"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "PrimInt"
            , FunType([ConstType(SortNoArgs("PRIMINTEGER"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "Float"
            , FunType([ConstType(SortNoArgs("RATIONAL"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "Float"
            , FunType([ConstType(SortNoArgs("FLOAT"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Char"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDecl(
              "Int"
            , FunType([ConstType(SortNoArgs("INTEGER"))], ConstType(SortNoArgs("Literal")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qcon"))], ConstType(SortNoArgs("Gcon")))
            )
          , OpDecl("EmptyList", ConstType(SortNoArgs("Gcon")))
          , OpDecl("Unit", ConstType(SortNoArgs("Gcon")))
          , OpDecl(
              "Irrefutable"
            , FunType([ConstType(SortNoArgs("APat"))], ConstType(SortNoArgs("APat")))
            )
          , OpDecl(
              "List"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Pat")]))]
              , ConstType(SortNoArgs("APat"))
              )
            )
          , OpDecl(
              "Tuple"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(Sort("List", [SortNoArgs("Pat")]))]
              , ConstType(SortNoArgs("APat"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Pat"))], ConstType(SortNoArgs("APat")))
            )
          , OpDecl("Wildcard", ConstType(SortNoArgs("APat")))
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Literal"))], ConstType(SortNoArgs("APat")))
            )
          , OpDecl(
              "Labeled"
            , FunType(
                [ConstType(SortNoArgs("Qcon")), ConstType(SortNoArgs("LabeledPat"))]
              , ConstType(SortNoArgs("APat"))
              )
            )
          , OpDecl(
              "Constr"
            , FunType([ConstType(SortNoArgs("Gcon"))], ConstType(SortNoArgs("APat")))
            )
          , OpDecl(
              "Named"
            , FunType(
                [ConstType(SortNoArgs("Var")), ConstType(SortNoArgs("APat"))]
              , ConstType(SortNoArgs("APat"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Var"))], ConstType(SortNoArgs("APat")))
            )
          ]
        )
      ]
    )
  , Strategies(
      [ SDefT(
          "step_0_0"
        , []
        , []
        , GuardedLChoice(
            Scope(
              ["h_3", "i_3"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      "OpApp"
                    , [ Anno(
                          Op(
                            "AppBin"
                          , [ Anno(
                                Op("Var", [Anno(Str("arr"), Wld())])
                              , Wld()
                              )
                            , Var("i_3")
                            ]
                          )
                        , Wld()
                        )
                      , Anno(Str(">>>"), Wld())
                      , Anno(
                          Op(
                            "AppBin"
                          , [ Anno(
                                Op("Var", [Anno(Str("arr"), Wld())])
                              , Wld()
                              )
                            , Var("h_3")
                            ]
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
                      "AppBin"
                    , [ Anno(
                          Op(
                            "Var"
                          , [Anno(Str("arr"), Op("Nil", []))]
                          )
                        , Op("Nil", [])
                        )
                      , Anno(
                          Op(
                            "OpApp"
                          , [ Var("h_3")
                            , Anno(Str("."), Op("Nil", []))
                            , Var("i_3")
                            ]
                          )
                        , Op("Nil", [])
                        )
                      ]
                    )
                  , Op("Nil", [])
                  )
                )
              )
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["e_3", "f_3", "g_3"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        "OpApp"
                      , [ Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op("Var", [Anno(Str("arr"), Wld())])
                                , Wld()
                                )
                              , Var("g_3")
                              ]
                            )
                          , Wld()
                          )
                        , Anno(Str(">>>"), Wld())
                        , Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op(
                                    "AppBin"
                                  , [ Anno(
                                        Op("Var", [Anno(Str("loopD"), Wld())])
                                      , Wld()
                                      )
                                    , Var("e_3")
                                    ]
                                  )
                                , Wld()
                                )
                              , Var("f_3")
                              ]
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
                        "AppBin"
                      , [ Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op(
                                    "Var"
                                  , [Anno(Str("loopD"), Op("Nil", []))]
                                  )
                                , Op("Nil", [])
                                )
                              , Var("e_3")
                              ]
                            )
                          , Op("Nil", [])
                          )
                        , Anno(
                            Op(
                              "OpApp"
                            , [ Var("f_3")
                              , Anno(Str("."), Op("Nil", []))
                              , Anno(
                                  Op(
                                    "OpApp"
                                  , [ Var("g_3")
                                    , Anno(Str("***"), Op("Nil", []))
                                    , Anno(
                                        Op(
                                          "Var"
                                        , [Anno(Str("id"), Op("Nil", []))]
                                        )
                                      , Op("Nil", [])
                                      )
                                    ]
                                  )
                                , Op("Nil", [])
                                )
                              ]
                            )
                          , Op("Nil", [])
                          )
                        ]
                      )
                    , Op("Nil", [])
                    )
                  )
                )
              )
            , Id()
            , GuardedLChoice(
                Scope(
                  ["b_3", "c_3", "d_3"]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          "OpApp"
                        , [ Anno(
                              Op(
                                "AppBin"
                              , [ Anno(
                                    Op(
                                      "AppBin"
                                    , [ Anno(
                                          Op("Var", [Anno(Str("loopD"), Wld())])
                                        , Wld()
                                        )
                                      , Var("b_3")
                                      ]
                                    )
                                  , Wld()
                                  )
                                , Var("d_3")
                                ]
                              )
                            , Wld()
                            )
                          , Anno(Str(">>>"), Wld())
                          , Anno(
                              Op(
                                "AppBin"
                              , [ Anno(
                                    Op("Var", [Anno(Str("arr"), Wld())])
                                  , Wld()
                                  )
                                , Var("c_3")
                                ]
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
                          "AppBin"
                        , [ Anno(
                              Op(
                                "AppBin"
                              , [ Anno(
                                    Op(
                                      "Var"
                                    , [Anno(Str("loopD"), Op("Nil", []))]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Var("b_3")
                                ]
                              )
                            , Op("Nil", [])
                            )
                          , Anno(
                              Op(
                                "OpApp"
                              , [ Anno(
                                    Op(
                                      "OpApp"
                                    , [ Var("c_3")
                                      , Anno(Str("***"), Op("Nil", []))
                                      , Anno(
                                          Op(
                                            "Var"
                                          , [Anno(Str("id"), Op("Nil", []))]
                                          )
                                        , Op("Nil", [])
                                        )
                                      ]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Anno(Str("."), Op("Nil", []))
                                , Var("d_3")
                                ]
                              )
                            , Op("Nil", [])
                            )
                          ]
                        )
                      , Op("Nil", [])
                      )
                    )
                  )
                )
              , Id()
              , GuardedLChoice(
                  Scope(
                    ["x_2", "y_2", "z_2", "a_3"]
                  , Seq(
                      Match(
                        Anno(
                          Op(
                            "OpApp"
                          , [ Anno(
                                Op(
                                  "AppBin"
                                , [ Anno(
                                      Op(
                                        "AppBin"
                                      , [ Anno(
                                            Op("Var", [Anno(Str("loopD"), Wld())])
                                          , Wld()
                                          )
                                        , Var("x_2")
                                        ]
                                      )
                                    , Wld()
                                    )
                                  , Var("a_3")
                                  ]
                                )
                              , Wld()
                              )
                            , Anno(Str(">>>"), Wld())
                            , Anno(
                                Op(
                                  "AppBin"
                                , [ Anno(
                                      Op(
                                        "AppBin"
                                      , [ Anno(
                                            Op("Var", [Anno(Str("loopD"), Wld())])
                                          , Wld()
                                          )
                                        , Var("y_2")
                                        ]
                                      )
                                    , Wld()
                                    )
                                  , Var("z_2")
                                  ]
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
                            "AppBin"
                          , [ Anno(
                                Op(
                                  "AppBin"
                                , [ Anno(
                                      Op(
                                        "Var"
                                      , [Anno(Str("loopD"), Op("Nil", []))]
                                      )
                                    , Op("Nil", [])
                                    )
                                  , Anno(
                                      Op(
                                        "Product"
                                      , [ Anno(
                                            Op(
                                              "ECons"
                                            , [ Var("x_2")
                                              , Anno(
                                                  Op(
                                                    "Cons"
                                                  , [Var("y_2"), Anno(Op("Nil", []), Op("Nil", []))]
                                                  )
                                                , Op("Nil", [])
                                                )
                                              ]
                                            )
                                          , Op("Nil", [])
                                          )
                                        ]
                                      )
                                    , Op("Nil", [])
                                    )
                                  ]
                                )
                              , Op("Nil", [])
                              )
                            , Anno(
                                Op(
                                  "AppBin"
                                , [ Anno(
                                      Op(
                                        "Var"
                                      , [Anno(Str("assoc'"), Op("Nil", []))]
                                      )
                                    , Op("Nil", [])
                                    )
                                  , Anno(
                                      Op(
                                        "OpApp"
                                      , [ Anno(
                                            Op(
                                              "AppBin"
                                            , [ Anno(
                                                  Op(
                                                    "Var"
                                                  , [Anno(Str("juggle'"), Op("Nil", []))]
                                                  )
                                                , Op("Nil", [])
                                                )
                                              , Anno(
                                                  Op(
                                                    "OpApp"
                                                  , [ Var("z_2")
                                                    , Anno(Str("***"), Op("Nil", []))
                                                    , Anno(
                                                        Op(
                                                          "Var"
                                                        , [Anno(Str("id"), Op("Nil", []))]
                                                        )
                                                      , Op("Nil", [])
                                                      )
                                                    ]
                                                  )
                                                , Op("Nil", [])
                                                )
                                              ]
                                            )
                                          , Op("Nil", [])
                                          )
                                        , Anno(Str("."), Op("Nil", []))
                                        , Anno(
                                            Op(
                                              "OpApp"
                                            , [ Var("a_3")
                                              , Anno(Str("***"), Op("Nil", []))
                                              , Anno(
                                                  Op(
                                                    "Var"
                                                  , [Anno(Str("id"), Op("Nil", []))]
                                                  )
                                                , Op("Nil", [])
                                                )
                                              ]
                                            )
                                          , Op("Nil", [])
                                          )
                                        ]
                                      )
                                    , Op("Nil", [])
                                    )
                                  ]
                                )
                              , Op("Nil", [])
                              )
                            ]
                          )
                        , Op("Nil", [])
                        )
                      )
                    )
                  )
                , Id()
                , GuardedLChoice(
                    Scope(
                      ["v_2", "w_2"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op("Var", [Anno(Str("first"), Wld())])
                                , Wld()
                                )
                              , Anno(
                                  Op(
                                    "AppBin"
                                  , [ Anno(
                                        Op(
                                          "AppBin"
                                        , [ Anno(
                                              Op("Var", [Anno(Str("loopD"), Wld())])
                                            , Wld()
                                            )
                                          , Var("w_2")
                                          ]
                                        )
                                      , Wld()
                                      )
                                    , Var("v_2")
                                    ]
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
                              "AppBin"
                            , [ Anno(
                                  Op(
                                    "AppBin"
                                  , [ Anno(
                                        Op(
                                          "Var"
                                        , [Anno(Str("loopD"), Op("Nil", []))]
                                        )
                                      , Op("Nil", [])
                                      )
                                    , Var("w_2")
                                    ]
                                  )
                                , Op("Nil", [])
                                )
                              , Anno(
                                  Op(
                                    "AppBin"
                                  , [ Anno(
                                        Op(
                                          "Var"
                                        , [Anno(Str("juggle'"), Op("Nil", []))]
                                        )
                                      , Op("Nil", [])
                                      )
                                    , Anno(
                                        Op(
                                          "OpApp"
                                        , [ Anno(
                                              Op(
                                                "Var"
                                              , [Anno(Str("f"), Op("Nil", []))]
                                              )
                                            , Op("Nil", [])
                                            )
                                          , Anno(Str("***"), Op("Nil", []))
                                          , Anno(
                                              Op(
                                                "Var"
                                              , [Anno(Str("id"), Op("Nil", []))]
                                              )
                                            , Op("Nil", [])
                                            )
                                          ]
                                        )
                                      , Op("Nil", [])
                                      )
                                    ]
                                  )
                                , Op("Nil", [])
                                )
                              ]
                            )
                          , Op("Nil", [])
                          )
                        )
                      )
                    )
                  , Id()
                  , GuardedLChoice(
                      Scope(
                        ["u_2"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                "AppBin"
                              , [ Anno(
                                    Op("Var", [Anno(Str("loop"), Wld())])
                                  , Wld()
                                  )
                                , Anno(
                                    Op(
                                      "AppBin"
                                    , [ Anno(
                                          Op("Var", [Anno(Str("arr"), Wld())])
                                        , Wld()
                                        )
                                      , Var("u_2")
                                      ]
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
                                "AppBin"
                              , [ Anno(
                                    Op(
                                      "Var"
                                    , [Anno(Str("arr"), Op("Nil", []))]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Anno(
                                    Op(
                                      "AppBin"
                                    , [ Anno(
                                          Op(
                                            "Var"
                                          , [Anno(Str("trace"), Op("Nil", []))]
                                          )
                                        , Op("Nil", [])
                                        )
                                      , Var("u_2")
                                      ]
                                    )
                                  , Op("Nil", [])
                                  )
                                ]
                              )
                            , Op("Nil", [])
                            )
                          )
                        )
                      )
                    , Id()
                    , Scope(
                        ["s_2", "t_2"]
                      , Seq(
                          Match(
                            Anno(
                              Op(
                                "AppBin"
                              , [ Anno(
                                    Op("Var", [Anno(Str("loop"), Wld())])
                                  , Wld()
                                  )
                                , Anno(
                                    Op(
                                      "AppBin"
                                    , [ Anno(
                                          Op(
                                            "AppBin"
                                          , [ Anno(
                                                Op("Var", [Anno(Str("loopD"), Wld())])
                                              , Wld()
                                              )
                                            , Var("t_2")
                                            ]
                                          )
                                        , Wld()
                                        )
                                      , Var("s_2")
                                      ]
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
                                "AppBin"
                              , [ Anno(
                                    Op(
                                      "AppBin"
                                    , [ Anno(
                                          Op(
                                            "Var"
                                          , [Anno(Str("loopD"), Op("Nil", []))]
                                          )
                                        , Op("Nil", [])
                                        )
                                      , Var("t_2")
                                      ]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Anno(
                                    Op(
                                      "AppBin"
                                    , [ Anno(
                                          Op(
                                            "Var"
                                          , [Anno(Str("trace"), Op("Nil", []))]
                                          )
                                        , Op("Nil", [])
                                        )
                                      , Anno(
                                          Op(
                                            "AppBin"
                                          , [ Anno(
                                                Op(
                                                  "Var"
                                                , [Anno(Str("juggle'"), Op("Nil", []))]
                                                )
                                              , Op("Nil", [])
                                              )
                                            , Anno(
                                                Op(
                                                  "Var"
                                                , [Anno(Str("f"), Op("Nil", []))]
                                                )
                                              , Op("Nil", [])
                                              )
                                            ]
                                          )
                                        , Op("Nil", [])
                                        )
                                      ]
                                    )
                                  , Op("Nil", [])
                                  )
                                ]
                              )
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
          )
        )
      , SDefT(
          "norm_0_0"
        , []
        , []
        , GuardedLChoice(
            Scope(
              ["x_3"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      "AppBin"
                    , [ Anno(
                          Op("Var", [Anno(Str("arr"), Wld())])
                        , Wld()
                        )
                      , Var("x_3")
                      ]
                    )
                  , Wld()
                  )
                )
              , Build(
                  Anno(
                    Op(
                      "AppBin"
                    , [ Anno(
                          Op(
                            "Var"
                          , [Anno(Str("arr"), Op("Nil", []))]
                          )
                        , Op("Nil", [])
                        )
                      , Var("x_3")
                      ]
                    )
                  , Op("Nil", [])
                  )
                )
              )
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["v_3", "w_3"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        "AppBin"
                      , [ Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op("Var", [Anno(Str("loopD"), Wld())])
                                , Wld()
                                )
                              , Var("v_3")
                              ]
                            )
                          , Wld()
                          )
                        , Var("w_3")
                        ]
                      )
                    , Wld()
                    )
                  )
                , Build(
                    Anno(
                      Op(
                        "AppBin"
                      , [ Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op(
                                    "Var"
                                  , [Anno(Str("loopD"), Op("Nil", []))]
                                  )
                                , Op("Nil", [])
                                )
                              , Var("v_3")
                              ]
                            )
                          , Op("Nil", [])
                          )
                        , Var("w_3")
                        ]
                      )
                    , Op("Nil", [])
                    )
                  )
                )
              )
            , Id()
            , GuardedLChoice(
                Scope(
                  ["u_3"]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          "AppBin"
                        , [ Anno(
                              Op("Var", [Anno(Str("init"), Wld())])
                            , Wld()
                            )
                          , Var("u_3")
                          ]
                        )
                      , Wld()
                      )
                    )
                  , Build(
                      Anno(
                        Op(
                          "AppBin"
                        , [ Anno(
                              Op(
                                "AppBin"
                              , [ Anno(
                                    Op(
                                      "Var"
                                    , [Anno(Str("loopD"), Op("Nil", []))]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Var("u_3")
                                ]
                              )
                            , Op("Nil", [])
                            )
                          , Anno(
                              Op(
                                "Var"
                              , [Anno(Str("swap"), Op("Nil", []))]
                              )
                            , Op("Nil", [])
                            )
                          ]
                        )
                      , Op("Nil", [])
                      )
                    )
                  )
                )
              , Id()
              , GuardedLChoice(
                  Scope(
                    ["p_3", "q_3", "r_3", "s_3", "t_3"]
                  , Seq(
                      Match(
                        Anno(
                          Op(
                            "OpApp"
                          , [Var("p_3"), Anno(Str(">>>"), Wld()), Var("r_3")]
                          )
                        , Wld()
                        )
                      )
                    , Seq(
                        Match(Var("t_3"))
                      , Seq(
                          Build(Var("p_3"))
                        , Seq(
                            CallT(SVar("norm_0_0"), [], [])
                          , Seq(
                              Match(Var("q_3"))
                            , Seq(
                                Build(Var("r_3"))
                              , Seq(
                                  CallT(SVar("norm_0_0"), [], [])
                                , Seq(
                                    Match(Var("s_3"))
                                  , Seq(
                                      Build(Var("t_3"))
                                    , Seq(
                                        Build(
                                          Anno(
                                            Op(
                                              "OpApp"
                                            , [ Var("q_3")
                                              , Anno(Str(">>>"), Op("Nil", []))
                                              , Var("s_3")
                                              ]
                                            )
                                          , Op("Nil", [])
                                          )
                                        )
                                      , CallT(SVar("step_0_0"), [], [])
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
                      ["m_3", "n_3", "o_3"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op("Var", [Anno(Str("first"), Wld())])
                                , Wld()
                                )
                              , Var("m_3")
                              ]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("o_3"))
                        , Seq(
                            Build(Var("m_3"))
                          , Seq(
                              CallT(SVar("norm_0_0"), [], [])
                            , Seq(
                                Match(Var("n_3"))
                              , Seq(
                                  Build(Var("o_3"))
                                , Seq(
                                    Build(
                                      Anno(
                                        Op(
                                          "AppBin"
                                        , [ Anno(
                                              Op(
                                                "Var"
                                              , [Anno(Str("first"), Op("Nil", []))]
                                              )
                                            , Op("Nil", [])
                                            )
                                          , Var("n_3")
                                          ]
                                        )
                                      , Op("Nil", [])
                                      )
                                    )
                                  , CallT(SVar("step_0_0"), [], [])
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
                      ["j_3", "k_3", "l_3"]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              "AppBin"
                            , [ Anno(
                                  Op("Var", [Anno(Str("loop"), Wld())])
                                , Wld()
                                )
                              , Var("j_3")
                              ]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("l_3"))
                        , Seq(
                            Build(Var("j_3"))
                          , Seq(
                              CallT(SVar("norm_0_0"), [], [])
                            , Seq(
                                Match(Var("k_3"))
                              , Seq(
                                  Build(Var("l_3"))
                                , Seq(
                                    Build(
                                      Anno(
                                        Op(
                                          "AppBin"
                                        , [ Anno(
                                              Op(
                                                "Var"
                                              , [Anno(Str("loop"), Op("Nil", []))]
                                              )
                                            , Op("Nil", [])
                                            )
                                          , Var("k_3")
                                          ]
                                        )
                                      , Op("Nil", [])
                                      )
                                    )
                                  , CallT(SVar("step_0_0"), [], [])
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
          "Anno__Cong_____2_0"
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
            ["y_3", "z_3", "a_4", "b_4"]
          , Seq(
              Match(Anno(Var("y_3"), Var("z_3")))
            , Seq(
                Build(Var("y_3"))
              , Seq(
                  CallT(SVar("c_4"), [], [])
                , Seq(
                    Match(Var("a_4"))
                  , Seq(
                      Build(Var("z_3"))
                    , Seq(
                        CallT(SVar("d_4"), [], [])
                      , Seq(
                          Match(Var("b_4"))
                        , Build(Anno(Var("a_4"), Var("b_4")))
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
            ["r_6", "p_6", "q_6", "s_6", "t_6"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("p_6"), Var("q_6")])
                , Var("r_6")
                )
              )
            , Seq(
                Build(Var("p_6"))
              , Seq(
                  CallT(SVar("e_4"), [], [])
                , Seq(
                    Match(Var("s_6"))
                  , Seq(
                      Build(Var("q_6"))
                    , Seq(
                        CallT(SVar("f_4"), [], [])
                      , Seq(
                          Match(Var("t_6"))
                        , Build(
                            Anno(
                              Op("Cons", [Var("s_6"), Var("t_6")])
                            , Var("r_6")
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
          "AppBin_2_0"
        , [ VarDec(
              "g_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_6", "u_6", "v_6", "x_6", "y_6"]
          , Seq(
              Match(
                Anno(
                  Op("AppBin", [Var("u_6"), Var("v_6")])
                , Var("w_6")
                )
              )
            , Seq(
                Build(Var("u_6"))
              , Seq(
                  CallT(SVar("g_4"), [], [])
                , Seq(
                    Match(Var("x_6"))
                  , Seq(
                      Build(Var("v_6"))
                    , Seq(
                        CallT(SVar("h_4"), [], [])
                      , Seq(
                          Match(Var("y_6"))
                        , Build(
                            Anno(
                              Op("AppBin", [Var("x_6"), Var("y_6")])
                            , Var("w_6")
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
          "OpApp_3_0"
        , [ VarDec(
              "i_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
          ]
        , []
        , Scope(
            ["c_7", "z_6", "a_7", "b_7", "d_7", "e_7", "f_7"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "OpApp"
                  , [Var("z_6"), Var("a_7"), Var("b_7")]
                  )
                , Var("c_7")
                )
              )
            , Seq(
                Build(Var("z_6"))
              , Seq(
                  CallT(SVar("i_4"), [], [])
                , Seq(
                    Match(Var("d_7"))
                  , Seq(
                      Build(Var("a_7"))
                    , Seq(
                        CallT(SVar("j_4"), [], [])
                      , Seq(
                          Match(Var("e_7"))
                        , Seq(
                            Build(Var("b_7"))
                          , Seq(
                              CallT(SVar("k_4"), [], [])
                            , Seq(
                                Match(Var("f_7"))
                              , Build(
                                  Anno(
                                    Op(
                                      "OpApp"
                                    , [Var("d_7"), Var("e_7"), Var("f_7")]
                                    )
                                  , Var("c_7")
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
          "Product_1_0"
        , [ VarDec(
              "l_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_7", "g_7", "i_7"]
          , Seq(
              Match(
                Anno(Op("Product", [Var("g_7")]), Var("h_7"))
              )
            , Seq(
                Build(Var("g_7"))
              , Seq(
                  CallT(SVar("l_4"), [], [])
                , Seq(
                    Match(Var("i_7"))
                  , Build(
                      Anno(Op("Product", [Var("i_7")]), Var("h_7"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ECons_2_0"
        , [ VarDec(
              "m_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_7", "j_7", "k_7", "m_7", "n_7"]
          , Seq(
              Match(
                Anno(
                  Op("ECons", [Var("j_7"), Var("k_7")])
                , Var("l_7")
                )
              )
            , Seq(
                Build(Var("j_7"))
              , Seq(
                  CallT(SVar("m_4"), [], [])
                , Seq(
                    Match(Var("m_7"))
                  , Seq(
                      Build(Var("k_7"))
                    , Seq(
                        CallT(SVar("n_4"), [], [])
                      , Seq(
                          Match(Var("n_7"))
                        , Build(
                            Anno(
                              Op("ECons", [Var("m_7"), Var("n_7")])
                            , Var("l_7")
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
          "Typed_3_0"
        , [ VarDec(
              "o_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "p_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_7", "o_7", "p_7", "q_7", "s_7", "t_7", "u_7"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Typed"
                  , [Var("o_7"), Var("p_7"), Var("q_7")]
                  )
                , Var("r_7")
                )
              )
            , Seq(
                Build(Var("o_7"))
              , Seq(
                  CallT(SVar("o_4"), [], [])
                , Seq(
                    Match(Var("s_7"))
                  , Seq(
                      Build(Var("p_7"))
                    , Seq(
                        CallT(SVar("p_4"), [], [])
                      , Seq(
                          Match(Var("t_7"))
                        , Seq(
                            Build(Var("q_7"))
                          , Seq(
                              CallT(SVar("q_4"), [], [])
                            , Seq(
                                Match(Var("u_7"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Typed"
                                    , [Var("s_7"), Var("t_7"), Var("u_7")]
                                    )
                                  , Var("r_7")
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
          "Negation_1_0"
        , [ VarDec(
              "r_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_7", "v_7", "x_7"]
          , Seq(
              Match(
                Anno(Op("Negation", [Var("v_7")]), Var("w_7"))
              )
            , Seq(
                Build(Var("v_7"))
              , Seq(
                  CallT(SVar("r_4"), [], [])
                , Seq(
                    Match(Var("x_7"))
                  , Build(
                      Anno(Op("Negation", [Var("x_7")]), Var("w_7"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Labeled_2_0"
        , [ VarDec(
              "s_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_8", "y_7", "z_7", "b_8", "c_8"]
          , Seq(
              Match(
                Anno(
                  Op("Labeled", [Var("y_7"), Var("z_7")])
                , Var("a_8")
                )
              )
            , Seq(
                Build(Var("y_7"))
              , Seq(
                  CallT(SVar("s_4"), [], [])
                , Seq(
                    Match(Var("b_8"))
                  , Seq(
                      Build(Var("z_7"))
                    , Seq(
                        CallT(SVar("t_4"), [], [])
                      , Seq(
                          Match(Var("c_8"))
                        , Build(
                            Anno(
                              Op("Labeled", [Var("b_8"), Var("c_8")])
                            , Var("a_8")
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
          "Named_2_0"
        , [ VarDec(
              "u_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_8", "d_8", "e_8", "g_8", "h_8"]
          , Seq(
              Match(
                Anno(
                  Op("Named", [Var("d_8"), Var("e_8")])
                , Var("f_8")
                )
              )
            , Seq(
                Build(Var("d_8"))
              , Seq(
                  CallT(SVar("u_4"), [], [])
                , Seq(
                    Match(Var("g_8"))
                  , Seq(
                      Build(Var("e_8"))
                    , Seq(
                        CallT(SVar("v_4"), [], [])
                      , Seq(
                          Match(Var("h_8"))
                        , Build(
                            Anno(
                              Op("Named", [Var("g_8"), Var("h_8")])
                            , Var("f_8")
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
          "Case_2_0"
        , [ VarDec(
              "w_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_8", "i_8", "j_8", "l_8", "m_8"]
          , Seq(
              Match(
                Anno(
                  Op("Case", [Var("i_8"), Var("j_8")])
                , Var("k_8")
                )
              )
            , Seq(
                Build(Var("i_8"))
              , Seq(
                  CallT(SVar("w_4"), [], [])
                , Seq(
                    Match(Var("l_8"))
                  , Seq(
                      Build(Var("j_8"))
                    , Seq(
                        CallT(SVar("x_4"), [], [])
                      , Seq(
                          Match(Var("m_8"))
                        , Build(
                            Anno(
                              Op("Case", [Var("l_8"), Var("m_8")])
                            , Var("k_8")
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
          "Do_1_0"
        , [ VarDec(
              "y_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_8", "n_8", "p_8"]
          , Seq(
              Match(
                Anno(Op("Do", [Var("n_8")]), Var("o_8"))
              )
            , Seq(
                Build(Var("n_8"))
              , Seq(
                  CallT(SVar("y_4"), [], [])
                , Seq(
                    Match(Var("p_8"))
                  , Build(
                      Anno(Op("Do", [Var("p_8")]), Var("o_8"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "If_3_0"
        , [ VarDec(
              "z_4"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_8", "q_8", "r_8", "s_8", "u_8", "v_8", "w_8"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "If"
                  , [Var("q_8"), Var("r_8"), Var("s_8")]
                  )
                , Var("t_8")
                )
              )
            , Seq(
                Build(Var("q_8"))
              , Seq(
                  CallT(SVar("z_4"), [], [])
                , Seq(
                    Match(Var("u_8"))
                  , Seq(
                      Build(Var("r_8"))
                    , Seq(
                        CallT(SVar("a_5"), [], [])
                      , Seq(
                          Match(Var("v_8"))
                        , Seq(
                            Build(Var("s_8"))
                          , Seq(
                              CallT(SVar("b_5"), [], [])
                            , Seq(
                                Match(Var("w_8"))
                              , Build(
                                  Anno(
                                    Op(
                                      "If"
                                    , [Var("u_8"), Var("v_8"), Var("w_8")]
                                    )
                                  , Var("t_8")
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
          "Let_2_0"
        , [ VarDec(
              "c_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_8", "x_8", "y_8", "a_9", "b_9"]
          , Seq(
              Match(
                Anno(
                  Op("Let", [Var("x_8"), Var("y_8")])
                , Var("z_8")
                )
              )
            , Seq(
                Build(Var("x_8"))
              , Seq(
                  CallT(SVar("c_5"), [], [])
                , Seq(
                    Match(Var("a_9"))
                  , Seq(
                      Build(Var("y_8"))
                    , Seq(
                        CallT(SVar("d_5"), [], [])
                      , Seq(
                          Match(Var("b_9"))
                        , Build(
                            Anno(
                              Op("Let", [Var("a_9"), Var("b_9")])
                            , Var("z_8")
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
          "Abs_2_0"
        , [ VarDec(
              "e_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_9", "c_9", "d_9", "f_9", "g_9"]
          , Seq(
              Match(
                Anno(
                  Op("Abs", [Var("c_9"), Var("d_9")])
                , Var("e_9")
                )
              )
            , Seq(
                Build(Var("c_9"))
              , Seq(
                  CallT(SVar("e_5"), [], [])
                , Seq(
                    Match(Var("f_9"))
                  , Seq(
                      Build(Var("d_9"))
                    , Seq(
                        CallT(SVar("f_5"), [], [])
                      , Seq(
                          Match(Var("g_9"))
                        , Build(
                            Anno(
                              Op("Abs", [Var("f_9"), Var("g_9")])
                            , Var("e_9")
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
          "RSection_2_0"
        , [ VarDec(
              "g_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_9", "h_9", "i_9", "k_9", "l_9"]
          , Seq(
              Match(
                Anno(
                  Op("RSection", [Var("h_9"), Var("i_9")])
                , Var("j_9")
                )
              )
            , Seq(
                Build(Var("h_9"))
              , Seq(
                  CallT(SVar("g_5"), [], [])
                , Seq(
                    Match(Var("k_9"))
                  , Seq(
                      Build(Var("i_9"))
                    , Seq(
                        CallT(SVar("h_5"), [], [])
                      , Seq(
                          Match(Var("l_9"))
                        , Build(
                            Anno(
                              Op("RSection", [Var("k_9"), Var("l_9")])
                            , Var("j_9")
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
          "LSection_2_0"
        , [ VarDec(
              "i_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_9", "m_9", "n_9", "p_9", "q_9"]
          , Seq(
              Match(
                Anno(
                  Op("LSection", [Var("m_9"), Var("n_9")])
                , Var("o_9")
                )
              )
            , Seq(
                Build(Var("m_9"))
              , Seq(
                  CallT(SVar("i_5"), [], [])
                , Seq(
                    Match(Var("p_9"))
                  , Seq(
                      Build(Var("n_9"))
                    , Seq(
                        CallT(SVar("j_5"), [], [])
                      , Seq(
                          Match(Var("q_9"))
                        , Build(
                            Anno(
                              Op("LSection", [Var("p_9"), Var("q_9")])
                            , Var("o_9")
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
          "Lit_1_0"
        , [ VarDec(
              "k_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_9", "r_9", "t_9"]
          , Seq(
              Match(
                Anno(Op("Lit", [Var("r_9")]), Var("s_9"))
              )
            , Seq(
                Build(Var("r_9"))
              , Seq(
                  CallT(SVar("k_5"), [], [])
                , Seq(
                    Match(Var("t_9"))
                  , Build(
                      Anno(Op("Lit", [Var("t_9")]), Var("s_9"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Constr_1_0"
        , [ VarDec(
              "l_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_9", "u_9", "w_9"]
          , Seq(
              Match(
                Anno(Op("Constr", [Var("u_9")]), Var("v_9"))
              )
            , Seq(
                Build(Var("u_9"))
              , Seq(
                  CallT(SVar("l_5"), [], [])
                , Seq(
                    Match(Var("w_9"))
                  , Build(
                      Anno(Op("Constr", [Var("w_9")]), Var("v_9"))
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
              "m_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_9", "x_9", "z_9"]
          , Seq(
              Match(
                Anno(Op("Var", [Var("x_9")]), Var("y_9"))
              )
            , Seq(
                Build(Var("x_9"))
              , Seq(
                  CallT(SVar("m_5"), [], [])
                , Seq(
                    Match(Var("z_9"))
                  , Build(
                      Anno(Op("Var", [Var("z_9")]), Var("y_9"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ArrProcedure_2_0"
        , [ VarDec(
              "n_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_10", "a_10", "b_10", "d_10", "e_10"]
          , Seq(
              Match(
                Anno(
                  Op("ArrProcedure", [Var("a_10"), Var("b_10")])
                , Var("c_10")
                )
              )
            , Seq(
                Build(Var("a_10"))
              , Seq(
                  CallT(SVar("n_5"), [], [])
                , Seq(
                    Match(Var("d_10"))
                  , Seq(
                      Build(Var("b_10"))
                    , Seq(
                        CallT(SVar("o_5"), [], [])
                      , Seq(
                          Match(Var("e_10"))
                        , Build(
                            Anno(
                              Op("ArrProcedure", [Var("d_10"), Var("e_10")])
                            , Var("c_10")
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
          "BinOp_1_0"
        , [ VarDec(
              "p_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_10", "f_10", "h_10"]
          , Seq(
              Match(
                Anno(Op("BinOp", [Var("f_10")]), Var("g_10"))
              )
            , Seq(
                Build(Var("f_10"))
              , Seq(
                  CallT(SVar("p_5"), [], [])
                , Seq(
                    Match(Var("h_10"))
                  , Build(
                      Anno(Op("BinOp", [Var("h_10")]), Var("g_10"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Context_1_0"
        , [ VarDec(
              "q_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_10", "i_10", "k_10"]
          , Seq(
              Match(
                Anno(Op("Context", [Var("i_10")]), Var("j_10"))
              )
            , Seq(
                Build(Var("i_10"))
              , Seq(
                  CallT(SVar("q_5"), [], [])
                , Seq(
                    Match(Var("k_10"))
                  , Build(
                      Anno(Op("Context", [Var("k_10")]), Var("j_10"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "TFunBin_2_0"
        , [ VarDec(
              "r_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_10", "l_10", "m_10", "o_10", "p_10"]
          , Seq(
              Match(
                Anno(
                  Op("TFunBin", [Var("l_10"), Var("m_10")])
                , Var("n_10")
                )
              )
            , Seq(
                Build(Var("l_10"))
              , Seq(
                  CallT(SVar("r_5"), [], [])
                , Seq(
                    Match(Var("o_10"))
                  , Seq(
                      Build(Var("m_10"))
                    , Seq(
                        CallT(SVar("s_5"), [], [])
                      , Seq(
                          Match(Var("p_10"))
                        , Build(
                            Anno(
                              Op("TFunBin", [Var("o_10"), Var("p_10")])
                            , Var("n_10")
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
          "TAppBin_2_0"
        , [ VarDec(
              "t_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "u_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_10", "q_10", "r_10", "t_10", "u_10"]
          , Seq(
              Match(
                Anno(
                  Op("TAppBin", [Var("q_10"), Var("r_10")])
                , Var("s_10")
                )
              )
            , Seq(
                Build(Var("q_10"))
              , Seq(
                  CallT(SVar("t_5"), [], [])
                , Seq(
                    Match(Var("t_10"))
                  , Seq(
                      Build(Var("r_10"))
                    , Seq(
                        CallT(SVar("u_5"), [], [])
                      , Seq(
                          Match(Var("u_10"))
                        , Build(
                            Anno(
                              Op("TAppBin", [Var("t_10"), Var("u_10")])
                            , Var("s_10")
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
          "TProd_1_0"
        , [ VarDec(
              "v_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_10", "v_10", "x_10"]
          , Seq(
              Match(
                Anno(Op("TProd", [Var("v_10")]), Var("w_10"))
              )
            , Seq(
                Build(Var("v_10"))
              , Seq(
                  CallT(SVar("v_5"), [], [])
                , Seq(
                    Match(Var("x_10"))
                  , Build(
                      Anno(Op("TProd", [Var("x_10")]), Var("w_10"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "TList_1_0"
        , [ VarDec(
              "w_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_10", "y_10", "a_11"]
          , Seq(
              Match(
                Anno(Op("TList", [Var("y_10")]), Var("z_10"))
              )
            , Seq(
                Build(Var("y_10"))
              , Seq(
                  CallT(SVar("w_5"), [], [])
                , Seq(
                    Match(Var("a_11"))
                  , Build(
                      Anno(Op("TList", [Var("a_11")]), Var("z_10"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "TVar_1_0"
        , [ VarDec(
              "x_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_11", "b_11", "d_11"]
          , Seq(
              Match(
                Anno(Op("TVar", [Var("b_11")]), Var("c_11"))
              )
            , Seq(
                Build(Var("b_11"))
              , Seq(
                  CallT(SVar("x_5"), [], [])
                , Seq(
                    Match(Var("d_11"))
                  , Build(
                      Anno(Op("TVar", [Var("d_11")]), Var("c_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "TCon_1_0"
        , [ VarDec(
              "y_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_11", "e_11", "g_11"]
          , Seq(
              Match(
                Anno(Op("TCon", [Var("e_11")]), Var("f_11"))
              )
            , Seq(
                Build(Var("e_11"))
              , Seq(
                  CallT(SVar("y_5"), [], [])
                , Seq(
                    Match(Var("g_11"))
                  , Build(
                      Anno(Op("TCon", [Var("g_11")]), Var("f_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "TCons_2_0"
        , [ VarDec(
              "z_5"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_11", "h_11", "i_11", "k_11", "l_11"]
          , Seq(
              Match(
                Anno(
                  Op("TCons", [Var("h_11"), Var("i_11")])
                , Var("j_11")
                )
              )
            , Seq(
                Build(Var("h_11"))
              , Seq(
                  CallT(SVar("z_5"), [], [])
                , Seq(
                    Match(Var("k_11"))
                  , Seq(
                      Build(Var("i_11"))
                    , Seq(
                        CallT(SVar("a_6"), [], [])
                      , Seq(
                          Match(Var("l_11"))
                        , Build(
                            Anno(
                              Op("TCons", [Var("k_11"), Var("l_11")])
                            , Var("j_11")
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
          "LabelBinds_1_0"
        , [ VarDec(
              "b_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_11", "m_11", "o_11"]
          , Seq(
              Match(
                Anno(Op("LabelBinds", [Var("m_11")]), Var("n_11"))
              )
            , Seq(
                Build(Var("m_11"))
              , Seq(
                  CallT(SVar("b_6"), [], [])
                , Seq(
                    Match(Var("o_11"))
                  , Build(
                      Anno(Op("LabelBinds", [Var("o_11")]), Var("n_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "CLitLit_1_0"
        , [ VarDec(
              "c_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_11", "p_11", "r_11"]
          , Seq(
              Match(
                Anno(Op("CLitLit", [Var("p_11")]), Var("q_11"))
              )
            , Seq(
                Build(Var("p_11"))
              , Seq(
                  CallT(SVar("c_6"), [], [])
                , Seq(
                    Match(Var("r_11"))
                  , Build(
                      Anno(Op("CLitLit", [Var("r_11")]), Var("q_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrimDouble_1_0"
        , [ VarDec(
              "d_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_11", "s_11", "u_11"]
          , Seq(
              Match(
                Anno(Op("PrimDouble", [Var("s_11")]), Var("t_11"))
              )
            , Seq(
                Build(Var("s_11"))
              , Seq(
                  CallT(SVar("d_6"), [], [])
                , Seq(
                    Match(Var("u_11"))
                  , Build(
                      Anno(Op("PrimDouble", [Var("u_11")]), Var("t_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrimFloat_1_0"
        , [ VarDec(
              "e_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_11", "v_11", "x_11"]
          , Seq(
              Match(
                Anno(Op("PrimFloat", [Var("v_11")]), Var("w_11"))
              )
            , Seq(
                Build(Var("v_11"))
              , Seq(
                  CallT(SVar("e_6"), [], [])
                , Seq(
                    Match(Var("x_11"))
                  , Build(
                      Anno(Op("PrimFloat", [Var("x_11")]), Var("w_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrimString_1_0"
        , [ VarDec(
              "f_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_11", "y_11", "a_12"]
          , Seq(
              Match(
                Anno(Op("PrimString", [Var("y_11")]), Var("z_11"))
              )
            , Seq(
                Build(Var("y_11"))
              , Seq(
                  CallT(SVar("f_6"), [], [])
                , Seq(
                    Match(Var("a_12"))
                  , Build(
                      Anno(Op("PrimString", [Var("a_12")]), Var("z_11"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrimChar_1_0"
        , [ VarDec(
              "g_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_12", "b_12", "d_12"]
          , Seq(
              Match(
                Anno(Op("PrimChar", [Var("b_12")]), Var("c_12"))
              )
            , Seq(
                Build(Var("b_12"))
              , Seq(
                  CallT(SVar("g_6"), [], [])
                , Seq(
                    Match(Var("d_12"))
                  , Build(
                      Anno(Op("PrimChar", [Var("d_12")]), Var("c_12"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrimInt_1_0"
        , [ VarDec(
              "h_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_12", "e_12", "g_12"]
          , Seq(
              Match(
                Anno(Op("PrimInt", [Var("e_12")]), Var("f_12"))
              )
            , Seq(
                Build(Var("e_12"))
              , Seq(
                  CallT(SVar("h_6"), [], [])
                , Seq(
                    Match(Var("g_12"))
                  , Build(
                      Anno(Op("PrimInt", [Var("g_12")]), Var("f_12"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Float_1_0"
        , [ VarDec(
              "i_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_12", "h_12", "j_12"]
          , Seq(
              Match(
                Anno(Op("Float", [Var("h_12")]), Var("i_12"))
              )
            , Seq(
                Build(Var("h_12"))
              , Seq(
                  CallT(SVar("i_6"), [], [])
                , Seq(
                    Match(Var("j_12"))
                  , Build(
                      Anno(Op("Float", [Var("j_12")]), Var("i_12"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Int_1_0"
        , [ VarDec(
              "j_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_12", "k_12", "m_12"]
          , Seq(
              Match(
                Anno(Op("Int", [Var("k_12")]), Var("l_12"))
              )
            , Seq(
                Build(Var("k_12"))
              , Seq(
                  CallT(SVar("j_6"), [], [])
                , Seq(
                    Match(Var("m_12"))
                  , Build(
                      Anno(Op("Int", [Var("m_12")]), Var("l_12"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "EmptyList_0_0"
        , []
        , []
        , Match(Anno(Op("EmptyList", []), Wld()))
        )
      , SDefT(
          "Unit_0_0"
        , []
        , []
        , Match(Anno(Op("Unit", []), Wld()))
        )
      , SDefT(
          "Irrefutable_1_0"
        , [ VarDec(
              "k_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_12", "n_12", "p_12"]
          , Seq(
              Match(
                Anno(Op("Irrefutable", [Var("n_12")]), Var("o_12"))
              )
            , Seq(
                Build(Var("n_12"))
              , Seq(
                  CallT(SVar("k_6"), [], [])
                , Seq(
                    Match(Var("p_12"))
                  , Build(
                      Anno(Op("Irrefutable", [Var("p_12")]), Var("o_12"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "List_1_0"
        , [ VarDec(
              "l_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_12", "q_12", "s_12"]
          , Seq(
              Match(
                Anno(Op("List", [Var("q_12")]), Var("r_12"))
              )
            , Seq(
                Build(Var("q_12"))
              , Seq(
                  CallT(SVar("l_6"), [], [])
                , Seq(
                    Match(Var("s_12"))
                  , Build(
                      Anno(Op("List", [Var("s_12")]), Var("r_12"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Tuple_2_0"
        , [ VarDec(
              "m_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_12", "t_12", "u_12", "w_12", "x_12"]
          , Seq(
              Match(
                Anno(
                  Op("Tuple", [Var("t_12"), Var("u_12")])
                , Var("v_12")
                )
              )
            , Seq(
                Build(Var("t_12"))
              , Seq(
                  CallT(SVar("m_6"), [], [])
                , Seq(
                    Match(Var("w_12"))
                  , Seq(
                      Build(Var("u_12"))
                    , Seq(
                        CallT(SVar("n_6"), [], [])
                      , Seq(
                          Match(Var("x_12"))
                        , Build(
                            Anno(
                              Op("Tuple", [Var("w_12"), Var("x_12")])
                            , Var("v_12")
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
          "Wildcard_0_0"
        , []
        , []
        , Match(Anno(Op("Wildcard", []), Wld()))
        )
      , SDefT(
          "DR__UNDEFINE_1_0"
        , [ VarDec(
              "o_6"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_12", "y_12", "a_13"]
          , Seq(
              Match(
                Anno(Op("DR_UNDEFINE", [Var("y_12")]), Var("z_12"))
              )
            , Seq(
                Build(Var("y_12"))
              , Seq(
                  CallT(SVar("o_6"), [], [])
                , Seq(
                    Match(Var("a_13"))
                  , Build(
                      Anno(Op("DR_UNDEFINE", [Var("a_13")]), Var("z_12"))
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
