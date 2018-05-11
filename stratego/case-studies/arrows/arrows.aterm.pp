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
              "Conc"
            , FunType(
                [ ConstType(Sort("List", [SortVar("a")]))
                , ConstType(Sort("List", [SortVar("a")]))
                ]
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
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Empty"))], ConstType(SortNoArgs("NoOffsideDeclListSem_Empty0")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideDeclListSem"))], ConstType(SortNoArgs("NoOffsideDeclListSem_Empty0")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Empty"))], ConstType(SortNoArgs("OffsideDeclList_Empty0")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideDeclList"))], ConstType(SortNoArgs("OffsideDeclList_Empty0")))
            )
          , OpDecl(
              "Conc"
            , FunType(
                [ConstType(SortNoArgs("ListStarOfCharClass0")), ConstType(SortNoArgs("ListPlusOfCharClass0"))]
              , ConstType(SortNoArgs("ListPlusOfCharClass0"))
              )
            )
          , OpDecl(
              "Conc"
            , FunType(
                [ConstType(SortNoArgs("ListPlusOfCharClass0")), ConstType(SortNoArgs("ListStarOfCharClass0"))]
              , ConstType(SortNoArgs("ListPlusOfCharClass0"))
              )
            )
          , OpDecl(
              "Conc"
            , FunType(
                [ConstType(SortNoArgs("ListPlusOfCharClass0")), ConstType(SortNoArgs("ListPlusOfCharClass0"))]
              , ConstType(SortNoArgs("ListPlusOfCharClass0"))
              )
            )
          , OpDecl(
              "Cons"
            , FunType(
                [ConstType(SortNoArgs("Int")), ConstType(SortNoArgs("ListStarOfCharClass0"))]
              , ConstType(SortNoArgs("ListPlusOfCharClass0"))
              )
            )
          , OpDecl(
              "StmtSeq"
            , FunType(
                [ConstType(SortNoArgs("OffsideStmt")), ConstType(SortNoArgs("OffsideStmt"))]
              , ConstType(SortNoArgs("OffsideStmt"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Stmt"))], ConstType(SortNoArgs("OffsideStmt")))
            )
          , OpDecl(
              "DeclSeq"
            , FunType(
                [ConstType(SortNoArgs("OffsideDecl")), ConstType(SortNoArgs("Decl"))]
              , ConstType(SortNoArgs("OffsideDecl"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Decl"))], ConstType(SortNoArgs("OffsideDecl")))
            )
          , OpDecl(
              "AltSeq"
            , FunType(
                [ConstType(SortNoArgs("OffsideAlt")), ConstType(SortNoArgs("Alt"))]
              , ConstType(SortNoArgs("OffsideAlt"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Alt"))], ConstType(SortNoArgs("OffsideAlt")))
            )
          , OpDecl(
              "TopdeclSeq"
            , FunType(
                [ConstType(SortNoArgs("Topdecl")), ConstType(SortNoArgs("OffsideTopdecl"))]
              , ConstType(SortNoArgs("OffsideTopdecl"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Topdecl"))], ConstType(SortNoArgs("OffsideTopdecl")))
            )
          , OpDecl(
              "ImportdeclSeq"
            , FunType(
                [ConstType(SortNoArgs("Importdecl")), ConstType(SortNoArgs("OffsideImportdecl"))]
              , ConstType(SortNoArgs("OffsideImportdecl"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Importdecl"))], ConstType(SortNoArgs("OffsideImportdecl")))
            )
          , OpDecl(
              "FloatHash"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Float-HASH")))
            )
          , OpDecl(
              "IntegerHash"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Integer-HASH")))
            )
          , OpDecl(
              "StringHash"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("StringChar")]))]
              , ConstType(SortNoArgs("String-HASH"))
              )
            )
          , OpDecl(
              "CharHash"
            , FunType([ConstType(SortNoArgs("CharChar"))], ConstType(SortNoArgs("Char-HASH")))
            )
          , OpDecl(
              "FlexibleContext"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("FlexibleClass")]))]
              , ConstType(SortNoArgs("FlexibleContext"))
              )
            )
          , OpDecl(
              "FlexibleContext"
            , FunType([ConstType(SortNoArgs("FlexibleClass"))], ConstType(SortNoArgs("FlexibleContext")))
            )
          , OpDecl(
              "SimpleClass"
            , FunType(
                [ConstType(SortNoArgs("Qtycls")), ConstType(SortNoArgs("Tyvar"))]
              , ConstType(SortNoArgs("FlexibleClass"))
              )
            )
          , OpDecl(
              "Class"
            , FunType(
                [ConstType(SortNoArgs("Qtycls")), ConstType(SortNoArgs("Gtycon"))]
              , ConstType(SortNoArgs("FlexibleClass"))
              )
            )
          , OpDecl(
              "Class"
            , FunType(
                [ConstType(SortNoArgs("Qtycls")), ConstType(SortNoArgs("Type"))]
              , ConstType(SortNoArgs("FlexibleClass"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideStmt"))], ConstType(SortNoArgs("OffsideStmtList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Stmt"))], ConstType(SortNoArgs("NoOffsideStmt")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideStmtList"))], ConstType(SortNoArgs("NoOffsideStmtListSem")))
            )
          , OpDecl(
              "StmtSeq"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideStmt")), ConstType(SortNoArgs("NoOffsideStmtList"))]
              , ConstType(SortNoArgs("NoOffsideStmtList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideStmt"))], ConstType(SortNoArgs("NoOffsideStmtList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideStmtListSem"))], ConstType(SortNoArgs("NoOffsideStmtBlock")))
            )
          , OpDecl(
              "StmtList"
            , FunType([ConstType(SortNoArgs("OffsideStmtList"))], ConstType(SortNoArgs("StmtList")))
            )
          , OpDecl(
              "StmtList"
            , FunType([ConstType(SortNoArgs("NoOffsideStmtBlock"))], ConstType(SortNoArgs("StmtList")))
            )
          , OpDecl(
              "FBind"
            , FunType(
                [ConstType(SortNoArgs("Qvar")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Fbind"))
              )
            )
          , OpDecl(
              "LetStmt"
            , FunType([ConstType(SortNoArgs("Declbinds"))], ConstType(SortNoArgs("Stmt")))
            )
          , OpDecl(
              "ExpStmt"
            , FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("Stmt")))
            )
          , OpDecl(
              "BindStmt"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Stmt"))
              )
            )
          , OpDecl(
              "ListCompr"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(Sort("List", [SortNoArgs("Qual")]))]
              , ConstType(SortNoArgs("List"))
              )
            )
          , OpDecl(
              "ListFirstFromTo"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("List"))
              )
            )
          , OpDecl(
              "ListFromTo"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("List"))
              )
            )
          , OpDecl(
              "ListFirstFrom"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("List"))
              )
            )
          , OpDecl(
              "ListFrom"
            , FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("List")))
            )
          , OpDecl(
              "List"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Exp")]))]
              , ConstType(SortNoArgs("List"))
              )
            )
          , OpDecl(
              "QualLet"
            , FunType([ConstType(SortNoArgs("Declbinds"))], ConstType(SortNoArgs("Qual")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("Qual")))
            )
          , OpDecl(
              "QualBind"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Qual"))
              )
            )
          , OpDecl(
              "PatBind"
            , FunType(
                [ConstType(SortNoArgs("Qvar")), ConstType(SortNoArgs("Pat"))]
              , ConstType(SortNoArgs("FPat"))
              )
            )
          , OpDecl(
              "LabeledPats"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("FPat")]))]
              , ConstType(SortNoArgs("LabeledPat"))
              )
            )
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
          , OpDecl(
              "ConstrApp"
            , FunType(
                [ConstType(SortNoArgs("Gcon")), ConstType(Sort("List", [SortNoArgs("APat")]))]
              , ConstType(SortNoArgs("LPat"))
              )
            )
          , OpDecl(
              "Negation"
            , FunType([ConstType(SortNoArgs("Literal"))], ConstType(SortNoArgs("LPat")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("APat"))], ConstType(SortNoArgs("LPat")))
            )
          , OpDecl(
              "BinOpApp"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("Qconop")), ConstType(SortNoArgs("LPat"))]
              , ConstType(SortNoArgs("Pat"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("LPat"))], ConstType(SortNoArgs("Pat")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideDecl"))], ConstType(SortNoArgs("OffsideDeclList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Decl"))], ConstType(SortNoArgs("NoOffsideDecl")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideDeclList"))], ConstType(SortNoArgs("NoOffsideDeclListSem")))
            )
          , OpDecl(
              "DeclSeq"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideDecl")), ConstType(SortNoArgs("NoOffsideDeclList"))]
              , ConstType(SortNoArgs("NoOffsideDeclList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideDecl"))], ConstType(SortNoArgs("NoOffsideDeclList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideDeclListSem_Empty0"))], ConstType(SortNoArgs("NoOffsideDeclBlock")))
            )
          , OpDecl(
              "DeclList"
            , FunType([ConstType(SortNoArgs("OffsideDeclList_Empty0"))], ConstType(SortNoArgs("DeclList")))
            )
          , OpDecl(
              "DeclList"
            , FunType([ConstType(SortNoArgs("NoOffsideDeclBlock"))], ConstType(SortNoArgs("DeclList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("DeclList"))], ConstType(SortNoArgs("Declbinds")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Where"))], ConstType(SortNoArgs("MaybeWhere")))
            )
          , OpDecl(
              "Where"
            , FunType([ConstType(SortNoArgs("DeclList"))], ConstType(SortNoArgs("Where")))
            )
          , OpDecl(
              "NestedFunLHS"
            , FunType(
                [ConstType(SortNoArgs("FunLHS")), ConstType(Sort("List", [SortNoArgs("APat")]))]
              , ConstType(SortNoArgs("FunLHS"))
              )
            )
          , OpDecl(
              "OpFunLHS"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("Varop")), ConstType(SortNoArgs("Pat"))]
              , ConstType(SortNoArgs("FunLHS"))
              )
            )
          , OpDecl(
              "VarFunLHS"
            , FunType(
                [ConstType(SortNoArgs("Var")), ConstType(Sort("List", [SortNoArgs("APat")]))]
              , ConstType(SortNoArgs("FunLHS"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Pat"))], ConstType(SortNoArgs("FunLHS")))
            )
          , OpDecl(
              "Guarded"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Gdrh"))
              )
            )
          , OpDecl(
              "GdValdef"
            , FunType(
                [ ConstType(SortNoArgs("FunLHS"))
                , ConstType(Sort("List", [SortNoArgs("Gdrh")]))
                , ConstType(SortNoArgs("MaybeWhere"))
                ]
              , ConstType(SortNoArgs("Valdef"))
              )
            )
          , OpDecl(
              "Valdef"
            , FunType(
                [ConstType(SortNoArgs("FunLHS")), ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("MaybeWhere"))]
              , ConstType(SortNoArgs("Valdef"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideAlt"))], ConstType(SortNoArgs("OffsideAltList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Alt"))], ConstType(SortNoArgs("NoOffsideAlt")))
            )
          , OpDecl(
              "AltSeq"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideAlt")), ConstType(SortNoArgs("NoOffsideAltList"))]
              , ConstType(SortNoArgs("NoOffsideAltList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideAlt"))], ConstType(SortNoArgs("NoOffsideAltList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideAltList"))], ConstType(SortNoArgs("NoOffsideAltBlock")))
            )
          , OpDecl(
              "AltList"
            , FunType([ConstType(SortNoArgs("OffsideAltList"))], ConstType(SortNoArgs("AltList")))
            )
          , OpDecl(
              "AltList"
            , FunType([ConstType(SortNoArgs("NoOffsideAltBlock"))], ConstType(SortNoArgs("AltList")))
            )
          , OpDecl(
              "GdPat"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Gdpat"))
              )
            )
          , OpDecl(
              "GdAlt"
            , FunType(
                [ ConstType(SortNoArgs("Pat"))
                , ConstType(Sort("List", [SortNoArgs("Gdpat")]))
                , ConstType(SortNoArgs("MaybeWhere"))
                ]
              , ConstType(SortNoArgs("Alt"))
              )
            )
          , OpDecl(
              "Alt"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("MaybeWhere"))]
              , ConstType(SortNoArgs("Alt"))
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
              FunType([ConstType(SortNoArgs("Qop"))], ConstType(SortNoArgs("QopNoNeg")))
            )
          , OpDecl(
              "FixDecl"
            , FunType(
                [ConstType(SortNoArgs("Infix")), ConstType(SortNoArgs("Prec")), ConstType(SortNoArgs("Ops"))]
              , ConstType(SortNoArgs("Fixdecl"))
              )
            )
          , OpDeclInj(
              FunType(
                [ConstType(Sort("List", [SortNoArgs("Op")]))]
              , ConstType(SortNoArgs("Ops"))
              )
            )
          , OpDeclInj(
              FunType(
                [ConstType(Sort("Option", [SortNoArgs("INTEGER")]))]
              , ConstType(SortNoArgs("Prec"))
              )
            )
          , OpDecl("InfixR", ConstType(SortNoArgs("Infix")))
          , OpDecl("InfixL", ConstType(SortNoArgs("Infix")))
          , OpDecl("Infix", ConstType(SortNoArgs("Infix")))
          , OpDeclInj(
              FunType(
                [ConstType(Sort("List", [SortNoArgs("APat")]))]
              , ConstType(SortNoArgs("Fargs"))
              )
            )
          , OpDecl(
              "ECons"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(Sort("List", [SortNoArgs("Exp")]))]
              , ConstType(SortNoArgs("Exps2"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Exp"))], ConstType(SortNoArgs("AnyExp")))
            )
          , OpDecl(
              "ArrOpApp"
            , FunType(
                [ConstType(SortNoArgs("ArrCommand")), ConstType(SortNoArgs("Qop")), ConstType(SortNoArgs("ArrCommand"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrForm"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(Sort("List", [SortNoArgs("ArrCommand")]))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrAppBin"
            , FunType(
                [ConstType(SortNoArgs("ArrCommand")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrDo"
            , FunType([ConstType(SortNoArgs("ArrStmtList"))], ConstType(SortNoArgs("ArrCommand")))
            )
          , OpDecl(
              "ArrCase"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("ArrAltList"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrIf"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("ArrCommand")), ConstType(SortNoArgs("ArrCommand"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrLet"
            , FunType(
                [ConstType(SortNoArgs("Declbinds")), ConstType(SortNoArgs("ArrCommand"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrAbs"
            , FunType(
                [ConstType(SortNoArgs("Fargs")), ConstType(SortNoArgs("ArrCommand"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrHigher"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("ArrCommand"))
              )
            )
          , OpDecl(
              "ArrFirst"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("ArrCommand"))
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
              "AppBin"
            , FunType(
                [ConstType(SortNoArgs("Exp")), ConstType(SortNoArgs("Exp"))]
              , ConstType(SortNoArgs("Exp"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("List"))], ConstType(SortNoArgs("Exp")))
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
              "Product"
            , FunType([ConstType(SortNoArgs("Exps2"))], ConstType(SortNoArgs("Exp")))
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
              "ArrStmtSeq"
            , FunType(
                [ConstType(SortNoArgs("ArrImplStmt")), ConstType(SortNoArgs("ArrImplStmtList"))]
              , ConstType(SortNoArgs("ArrImplStmtList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrImplStmt"))], ConstType(SortNoArgs("ArrImplStmtList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrStmt"))], ConstType(SortNoArgs("ArrImplStmt")))
            )
          , OpDecl(
              "ArrStmtSeq"
            , FunType(
                [ConstType(SortNoArgs("ArrStmt")), ConstType(SortNoArgs("ArrExplStmtList"))]
              , ConstType(SortNoArgs("ArrExplStmtList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrStmt"))], ConstType(SortNoArgs("ArrExplStmtList")))
            )
          , OpDecl(
              "ArrStmtList"
            , FunType([ConstType(SortNoArgs("ArrImplStmtList"))], ConstType(SortNoArgs("ArrStmtList")))
            )
          , OpDecl(
              "ArrStmtList"
            , FunType([ConstType(SortNoArgs("ArrExplStmtList"))], ConstType(SortNoArgs("ArrStmtList")))
            )
          , OpDecl(
              "ArrCmdStmt"
            , FunType([ConstType(SortNoArgs("ArrCommand"))], ConstType(SortNoArgs("ArrStmt")))
            )
          , OpDecl(
              "ArrBindStmt"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("ArrCommand"))]
              , ConstType(SortNoArgs("ArrStmt"))
              )
            )
          , OpDecl(
              "ArrLetStmt"
            , FunType([ConstType(SortNoArgs("Declbinds"))], ConstType(SortNoArgs("ArrStmt")))
            )
          , OpDecl(
              "ArrAltSeq"
            , FunType(
                [ConstType(SortNoArgs("ArrOffsideAlt")), ConstType(SortNoArgs("ArrOffsideAltList"))]
              , ConstType(SortNoArgs("ArrOffsideAltList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrOffsideAlt"))], ConstType(SortNoArgs("ArrOffsideAltList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrAlt"))], ConstType(SortNoArgs("ArrOffsideAlt")))
            )
          , OpDecl(
              "ArrAltSeq"
            , FunType(
                [ConstType(SortNoArgs("ArrAlt")), ConstType(SortNoArgs("ArrNoOffsideAltList"))]
              , ConstType(SortNoArgs("ArrNoOffsideAltList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrAlt"))], ConstType(SortNoArgs("ArrNoOffsideAltList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ArrNoOffsideAltList"))], ConstType(SortNoArgs("ArrNoOffsideAltBlock")))
            )
          , OpDecl(
              "AltList"
            , FunType([ConstType(SortNoArgs("ArrOffsideAltList"))], ConstType(SortNoArgs("ArrAltList")))
            )
          , OpDecl(
              "AltList"
            , FunType([ConstType(SortNoArgs("ArrNoOffsideAltBlock"))], ConstType(SortNoArgs("ArrAltList")))
            )
          , OpDecl(
              "ArrAlt"
            , FunType(
                [ConstType(SortNoArgs("Pat")), ConstType(SortNoArgs("ArrCommand")), ConstType(SortNoArgs("MaybeWhere"))]
              , ConstType(SortNoArgs("ArrAlt"))
              )
            )
          , OpDecl(
              "SignDecl"
            , FunType(
                [ ConstType(SortNoArgs("Vars"))
                , ConstType(Sort("Option", [SortNoArgs("Context")]))
                , ConstType(SortNoArgs("Type"))
                ]
              , ConstType(SortNoArgs("Signdecl"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Valdef"))], ConstType(SortNoArgs("Decl")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Fixdecl"))], ConstType(SortNoArgs("Decl")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Signdecl"))], ConstType(SortNoArgs("Decl")))
            )
          , OpDecl(
              "Class"
            , FunType(
                [ ConstType(SortNoArgs("Qtycls"))
                , ConstType(SortNoArgs("Tyvar"))
                , ConstType(Sort("List", [SortNoArgs("AType")]))
                ]
              , ConstType(SortNoArgs("Class"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("SimpleClass"))], ConstType(SortNoArgs("Class")))
            )
          , OpDecl(
              "SimpleClass"
            , FunType(
                [ConstType(SortNoArgs("Qtycls")), ConstType(SortNoArgs("Tyvar"))]
              , ConstType(SortNoArgs("SimpleClass"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("FlexibleContext"))], ConstType(SortNoArgs("SContext")))
            )
          , OpDecl(
              "SContext"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("SimpleClass")]))]
              , ConstType(SortNoArgs("SContext"))
              )
            )
          , OpDecl(
              "SContext"
            , FunType([ConstType(SortNoArgs("SimpleClass"))], ConstType(SortNoArgs("SContext")))
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
              "InstArrow"
            , FunType(
                [ConstType(SortNoArgs("Tyvar")), ConstType(SortNoArgs("Tyvar"))]
              , ConstType(SortNoArgs("Inst"))
              )
            )
          , OpDecl(
              "InstList"
            , FunType([ConstType(SortNoArgs("Tyvar"))], ConstType(SortNoArgs("Inst")))
            )
          , OpDecl(
              "InstTuple"
            , FunType(
                [ConstType(SortNoArgs("Tyvar")), ConstType(Sort("List", [SortNoArgs("Tyvar")]))]
              , ConstType(SortNoArgs("Inst"))
              )
            )
          , OpDecl(
              "InstApp"
            , FunType(
                [ConstType(SortNoArgs("Gtycon")), ConstType(Sort("List", [SortNoArgs("Tyvar")]))]
              , ConstType(SortNoArgs("Inst"))
              )
            )
          , OpDecl(
              "InstCons"
            , FunType([ConstType(SortNoArgs("Gtycon"))], ConstType(SortNoArgs("Inst")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Type"))], ConstType(SortNoArgs("Sbtype")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("AType"))], ConstType(SortNoArgs("Satype")))
            )
          , OpDecl(
              "InfixConstr"
            , FunType(
                [ConstType(SortNoArgs("Sbtype")), ConstType(SortNoArgs("Conop")), ConstType(SortNoArgs("Sbtype"))]
              , ConstType(SortNoArgs("Constr"))
              )
            )
          , OpDecl(
              "ConstrDecl"
            , FunType(
                [ConstType(SortNoArgs("Conid")), ConstType(Sort("List", [SortNoArgs("Satype")]))]
              , ConstType(SortNoArgs("Constr"))
              )
            )
          , OpDecl(
              "ConstrDecls"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Constr")]))]
              , ConstType(SortNoArgs("Constrs"))
              )
            )
          , OpDecl("NoConstrDecls", ConstType(SortNoArgs("Constrs")))
          , OpDecl(
              "Derive"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Qtycls")]))]
              , ConstType(SortNoArgs("Deriving"))
              )
            )
          , OpDecl("NoDeriving", ConstType(SortNoArgs("Deriving")))
          , OpDecl(
              "Derive"
            , FunType([ConstType(SortNoArgs("Qtycls"))], ConstType(SortNoArgs("Deriving")))
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
          , OpDecl("TList", ConstType(SortNoArgs("Gtycon")))
          , OpDecl("TUnit", ConstType(SortNoArgs("Gtycon")))
          , OpDecl("TArrow", ConstType(SortNoArgs("Gtycon")))
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qtycon"))], ConstType(SortNoArgs("Gtycon")))
            )
          , OpDecl(
              "Hiding"
            , FunType([ConstType(SortNoArgs("Exportlist"))], ConstType(SortNoArgs("Impspec")))
            )
          , OpDecl(
              "Impspec"
            , FunType([ConstType(SortNoArgs("Exportlist"))], ConstType(SortNoArgs("Impspec")))
            )
          , OpDecl(
              "As"
            , FunType([ConstType(SortNoArgs("Modid"))], ConstType(SortNoArgs("As")))
            )
          , OpDecl("Qualified", ConstType(SortNoArgs("Qualified")))
          , OpDecl("SOURCE", ConstType(SortNoArgs("Src")))
          , OpDecl(
              "Import"
            , FunType(
                [ ConstType(Sort("Option", [SortNoArgs("Src")]))
                , ConstType(Sort("Option", [SortNoArgs("Qualified")]))
                , ConstType(SortNoArgs("Modid"))
                , ConstType(Sort("Option", [SortNoArgs("As")]))
                , ConstType(Sort("Option", [SortNoArgs("Impspec")]))
                ]
              , ConstType(SortNoArgs("Importdecl"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Gtycon"))], ConstType(SortNoArgs("Export")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvar"))], ConstType(SortNoArgs("Export")))
            )
          , OpDecl(
              "Exports"
            , FunType([ConstType(SortNoArgs("Exportlist"))], ConstType(SortNoArgs("Exports")))
            )
          , OpDecl(
              "Exportlist"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Export")]))]
              , ConstType(SortNoArgs("Exportlist"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideTopdecl"))], ConstType(SortNoArgs("OffsideTopdeclList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideImportdecl"))], ConstType(SortNoArgs("OffsideImportdeclList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Topdecl"))], ConstType(SortNoArgs("NoOffsideTopdecl")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideTopdeclList"))], ConstType(SortNoArgs("NoOffsideTopdeclListSem")))
            )
          , OpDecl(
              "TopdeclSeq"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideTopdecl")), ConstType(SortNoArgs("NoOffsideTopdeclList"))]
              , ConstType(SortNoArgs("NoOffsideTopdeclList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideTopdecl"))], ConstType(SortNoArgs("NoOffsideTopdeclList")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Importdecl"))], ConstType(SortNoArgs("NoOffsideImportdecl")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideImportdeclList"))], ConstType(SortNoArgs("NoOffsideImportdeclListSem")))
            )
          , OpDecl(
              "ImportdeclSeq"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideImportdecl")), ConstType(SortNoArgs("NoOffsideImportdeclList"))]
              , ConstType(SortNoArgs("NoOffsideImportdeclList"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideImportdecl"))], ConstType(SortNoArgs("NoOffsideImportdeclList")))
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("OffsideImportdeclList")), ConstType(SortNoArgs("Empty"))]
              , ConstType(SortNoArgs("OffsideBody"))
              )
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("Empty")), ConstType(SortNoArgs("OffsideTopdeclList"))]
              , ConstType(SortNoArgs("OffsideBody"))
              )
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("Empty")), ConstType(SortNoArgs("Empty"))]
              , ConstType(SortNoArgs("OffsideBody"))
              )
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideImportdeclListSem")), ConstType(SortNoArgs("NoOffsideTopdeclList"))]
              , ConstType(SortNoArgs("NoOffsideBody"))
              )
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("NoOffsideImportdeclListSem")), ConstType(SortNoArgs("Empty"))]
              , ConstType(SortNoArgs("NoOffsideBody"))
              )
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("Empty")), ConstType(SortNoArgs("NoOffsideTopdeclListSem"))]
              , ConstType(SortNoArgs("NoOffsideBody"))
              )
            )
          , OpDecl(
              "Body"
            , FunType(
                [ConstType(SortNoArgs("Empty")), ConstType(SortNoArgs("Empty"))]
              , ConstType(SortNoArgs("NoOffsideBody"))
              )
            )
          , OpDecl("Empty", ConstType(SortNoArgs("Empty")))
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("OffsideBody"))], ConstType(SortNoArgs("Body")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("NoOffsideBody"))], ConstType(SortNoArgs("Body")))
            )
          , OpDecl(
              "FlexibleInstance"
            , FunType(
                [ ConstType(Sort("Option", [SortNoArgs("SContext")]))
                , ConstType(SortNoArgs("Qtycls"))
                , ConstType(Sort("List", [SortNoArgs("AType")]))
                , ConstType(SortNoArgs("MaybeWhere"))
                ]
              , ConstType(SortNoArgs("Topdecl"))
              )
            )
          , OpDecl(
              "Default"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("Type")]))]
              , ConstType(SortNoArgs("Topdecl"))
              )
            )
          , OpDecl(
              "Instance"
            , FunType(
                [ ConstType(Sort("Option", [SortNoArgs("SContext")]))
                , ConstType(SortNoArgs("Qtycls"))
                , ConstType(Sort("List", [SortNoArgs("Inst")]))
                , ConstType(SortNoArgs("MaybeWhere"))
                ]
              , ConstType(SortNoArgs("Topdecl"))
              )
            )
          , OpDecl(
              "Class"
            , FunType(
                [ ConstType(Sort("Option", [SortNoArgs("SContext")]))
                , ConstType(SortNoArgs("Tycls"))
                , ConstType(SortNoArgs("Tyvar"))
                , ConstType(SortNoArgs("MaybeWhere"))
                ]
              , ConstType(SortNoArgs("Topdecl"))
              )
            )
          , OpDecl(
              "Data"
            , FunType(
                [ ConstType(Sort("Option", [SortNoArgs("Context")]))
                , ConstType(SortNoArgs("Type"))
                , ConstType(SortNoArgs("Constrs"))
                , ConstType(SortNoArgs("Deriving"))
                ]
              , ConstType(SortNoArgs("Topdecl"))
              )
            )
          , OpDecl(
              "TypeDecl"
            , FunType(
                [ ConstType(SortNoArgs("Tycon"))
                , ConstType(Sort("List", [SortNoArgs("Tyvar")]))
                , ConstType(SortNoArgs("Type"))
                ]
              , ConstType(SortNoArgs("Topdecl"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Decl"))], ConstType(SortNoArgs("Topdecl")))
            )
          , OpDecl(
              "Program"
            , FunType([ConstType(SortNoArgs("Body"))], ConstType(SortNoArgs("Module")))
            )
          , OpDecl(
              "Module"
            , FunType(
                [ConstType(SortNoArgs("ModuleDec")), ConstType(SortNoArgs("Body"))]
              , ConstType(SortNoArgs("Module"))
              )
            )
          , OpDecl(
              "ModuleDec"
            , FunType(
                [ConstType(SortNoArgs("Modid")), ConstType(Sort("Option", [SortNoArgs("Exports")]))]
              , ConstType(SortNoArgs("ModuleDec"))
              )
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
          , OpDecl(
              "HexadecimalEsc"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Escape")))
            )
          , OpDecl(
              "OctalEsc"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Escape")))
            )
          , OpDecl(
              "DecimalEsc"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Escape")))
            )
          , OpDecl(
              "ASCIIEsc"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Escape")))
            )
          , OpDecl(
              "CharEsc"
            , FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Escape")))
            )
          , OpDecl(
              "Gap"
            , FunType([ConstType(SortNoArgs("ListPlusOfCharClass0"))], ConstType(SortNoArgs("StringChar")))
            )
          , OpDecl(
              "Escape"
            , FunType([ConstType(SortNoArgs("Escape"))], ConstType(SortNoArgs("StringChar")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("StringChar")))
            )
          , OpDecl(
              "Escape"
            , FunType([ConstType(SortNoArgs("Escape"))], ConstType(SortNoArgs("CharChar")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("CharChar")))
            )
          , OpDecl(
              "String"
            , FunType(
                [ConstType(Sort("List", [SortNoArgs("StringChar")]))]
              , ConstType(SortNoArgs("String"))
              )
            )
          , OpDecl(
              "Char"
            , FunType([ConstType(SortNoArgs("CharChar"))], ConstType(SortNoArgs("Char")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("CLITLIT")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("PRIMDOUBLE")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("PRIMFLOAT")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("PRIMINTEGER")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("PRIMSTRING")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("PRIMCHAR")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("RATIONAL")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("FLOAT")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("INTEGER")))
            )
          , OpDecl(
              "QModId"
            , FunType(
                [ConstType(SortNoArgs("String")), ConstType(SortNoArgs("QModid"))]
              , ConstType(SortNoArgs("QModid"))
              )
            )
          , OpDecl(
              "QModId"
            , FunType(
                [ConstType(SortNoArgs("String")), ConstType(SortNoArgs("String"))]
              , ConstType(SortNoArgs("QModid"))
              )
            )
          , OpDecl(
              "QConSym"
            , FunType(
                [ConstType(SortNoArgs("Modid")), ConstType(SortNoArgs("String"))]
              , ConstType(SortNoArgs("QCONSYM"))
              )
            )
          , OpDecl(
              "QVarSym"
            , FunType(
                [ConstType(SortNoArgs("Modid")), ConstType(SortNoArgs("String"))]
              , ConstType(SortNoArgs("QVARSYM"))
              )
            )
          , OpDecl(
              "QConId"
            , FunType(
                [ConstType(SortNoArgs("Modid")), ConstType(SortNoArgs("String"))]
              , ConstType(SortNoArgs("QCONID"))
              )
            )
          , OpDecl(
              "QVarId"
            , FunType(
                [ConstType(SortNoArgs("Modid")), ConstType(SortNoArgs("String"))]
              , ConstType(SortNoArgs("QVARID"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QModid"))], ConstType(SortNoArgs("Modid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Modid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QCONID"))], ConstType(SortNoArgs("Qconid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Conid"))], ConstType(SortNoArgs("Qconid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("CONID"))], ConstType(SortNoArgs("Conid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qtycon"))], ConstType(SortNoArgs("Qtycls")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Tycon"))], ConstType(SortNoArgs("Tycls")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QCONID"))], ConstType(SortNoArgs("Qtycon")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Tycon"))], ConstType(SortNoArgs("Qtycon")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("CONID"))], ConstType(SortNoArgs("Tycon")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QVARSYM"))], ConstType(SortNoArgs("Qvarsym1")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("VARSYM"))], ConstType(SortNoArgs("Varsym")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qconid"))], ConstType(SortNoArgs("Qcon")))
            )
          , OpDecl(
              "BinCon"
            , FunType([ConstType(SortNoArgs("Qconsym"))], ConstType(SortNoArgs("Qcon")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("CONSYM"))], ConstType(SortNoArgs("Consym")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QCONSYM"))], ConstType(SortNoArgs("Qconsym")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Consym"))], ConstType(SortNoArgs("Qconsym")))
            )
          , OpDecl(
              "ConsOp"
            , FunType([ConstType(SortNoArgs("CONSOP"))], ConstType(SortNoArgs("ConsOp")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("ConsOp"))], ConstType(SortNoArgs("Gconsym")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qconsym"))], ConstType(SortNoArgs("Gconsym")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qconop"))], ConstType(SortNoArgs("Qop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvarop"))], ConstType(SortNoArgs("Qop")))
            )
          , OpDecl(
              "PrefCon"
            , FunType([ConstType(SortNoArgs("Qconid"))], ConstType(SortNoArgs("Qconop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Gconsym"))], ConstType(SortNoArgs("Qconop")))
            )
          , OpDecl(
              "PrefCon"
            , FunType([ConstType(SortNoArgs("Conid"))], ConstType(SortNoArgs("Conop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Consym"))], ConstType(SortNoArgs("Conop")))
            )
          , OpDecl(
              "PrefOp"
            , FunType([ConstType(SortNoArgs("Qvarid"))], ConstType(SortNoArgs("Qvarop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvarsym"))], ConstType(SortNoArgs("Qvarop")))
            )
          , OpDecl(
              "PrefOp"
            , FunType([ConstType(SortNoArgs("Varid"))], ConstType(SortNoArgs("Varop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Varsym"))], ConstType(SortNoArgs("Varop")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvarsym1"))], ConstType(SortNoArgs("Qvarsym")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Varsym"))], ConstType(SortNoArgs("Qvarsym")))
            )
          , OpDecl(
              "ConOp"
            , FunType([ConstType(SortNoArgs("Conop"))], ConstType(SortNoArgs("Op")))
            )
          , OpDecl(
              "Op"
            , FunType([ConstType(SortNoArgs("Varop"))], ConstType(SortNoArgs("Op")))
            )
          , OpDecl(
              "BinOp"
            , FunType([ConstType(SortNoArgs("Qvarsym"))], ConstType(SortNoArgs("Qvar")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qvarid"))], ConstType(SortNoArgs("Qvar")))
            )
          , OpDecl(
              "BinOp"
            , FunType([ConstType(SortNoArgs("Varsym"))], ConstType(SortNoArgs("Var")))
            )
          , OpDecl(
              "Var"
            , FunType([ConstType(SortNoArgs("Varid"))], ConstType(SortNoArgs("Var")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("QVARID"))], ConstType(SortNoArgs("Qvarid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Varid"))], ConstType(SortNoArgs("Qvarid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("Qcon"))], ConstType(SortNoArgs("Gcon")))
            )
          , OpDecl("EmptyList", ConstType(SortNoArgs("Gcon")))
          , OpDecl("Unit", ConstType(SortNoArgs("Gcon")))
          , OpDecl(
              "Ins"
            , FunType([ConstType(SortNoArgs("Qvar"))], ConstType(SortNoArgs("Vars")))
            )
          , OpDecl(
              "Snoc"
            , FunType(
                [ConstType(SortNoArgs("Vars")), ConstType(SortNoArgs("Var"))]
              , ConstType(SortNoArgs("Vars"))
              )
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Tyvar")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("Varid")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("CONSOP")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("CONSYM")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("VARSYM")))
            )
          , OpDeclInj(
              FunType([ConstType(SortNoArgs("String"))], ConstType(SortNoArgs("CONID")))
            )
          , OpDecl("Builtin", ConstType(SortNoArgs("Varid")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Varsym")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Qconsym")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Qvarsym")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Qconid")))
          , OpDecl("Builtin", ConstType(SortNoArgs("INTEGER")))
          , OpDecl("Builtin", ConstType(SortNoArgs("FLOAT")))
          , OpDecl("Builtin", ConstType(SortNoArgs("RATIONAL")))
          , OpDecl("Builtin", ConstType(SortNoArgs("PRIMINTEGER")))
          , OpDecl("Builtin", ConstType(SortNoArgs("PRIMCHAR")))
          , OpDecl("Builtin", ConstType(SortNoArgs("PRIMSTRING")))
          , OpDecl("Builtin", ConstType(SortNoArgs("PRIMFLOAT")))
          , OpDecl("Builtin", ConstType(SortNoArgs("PRIMDOUBLE")))
          , OpDecl("Builtin", ConstType(SortNoArgs("CLITLIT")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Qop")))
          , OpDecl("Builtin", ConstType(SortNoArgs("QopNoNeg")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Fargs")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Declbinds")))
          , OpDecl("Builtin", ConstType(SortNoArgs("AnyExp")))
          , OpDecl("Builtin", ConstType(SortNoArgs("NoOffsideStmtBlock")))
          , OpDecl("Builtin", ConstType(SortNoArgs("OffsideStmtList")))
          , OpDecl("Builtin", ConstType(SortNoArgs("NoOffsideAltBlock")))
          , OpDecl("Builtin", ConstType(SortNoArgs("OffsideAltList")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Qtycls")))
          , OpDecl("Builtin", ConstType(SortNoArgs("Tyvar")))
          , OpDecl("Builtin", ConstType(SortNoArgs("ArrNoOffsideAltBlock")))
          , OpDecl("Builtin", ConstType(SortNoArgs("ArrOffsideAlt")))
          , OpDecl("Builtin", ConstType(SortNoArgs("ArrImplStmt")))
          ]
        )
      ]
    )
  , Strategies(
      [ SDefT(
          "desugar_arrow_0_0"
        , []
        , []
        , Scope(
            ["m_11", "n_11", "o_11", "p_11", "q_11", "s_11", "r_11", "t_11"]
          , Seq(
              Match(
                Anno(
                  Op("ArrProcedure", [Var("n_11"), Var("m_11")])
                , Wld()
                )
              )
            , Seq(
                Match(Var("p_11"))
              , Seq(
                  Build(Var("n_11"))
                , Seq(
                    CallT(SVar("free_pat_vars_0_0"), [], [])
                  , Seq(
                      Match(Var("o_11"))
                    , Seq(
                        Build(Var("p_11"))
                      , Seq(
                          Match(Var("s_11"))
                        , Seq(
                            Build(Var("o_11"))
                          , Seq(
                              CallT(SVar("tuple_0_0"), [], [])
                            , Seq(
                                Match(Var("q_11"))
                              , Seq(
                                  Build(Var("s_11"))
                                , Seq(
                                    Match(Var("t_11"))
                                  , Seq(
                                      Build(Var("m_11"))
                                    , Seq(
                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("o_11")])
                                      , Seq(
                                          Match(Var("r_11"))
                                        , Seq(
                                            Build(Var("t_11"))
                                          , Build(
                                              Anno(
                                                Op(
                                                  "OpApp"
                                                , [ Anno(
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
                                                              "Abs"
                                                            , [ Anno(
                                                                  Op(
                                                                    "Cons"
                                                                  , [Var("n_11"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                  )
                                                                , Op("Nil", [])
                                                                )
                                                              , Var("q_11")
                                                              ]
                                                            )
                                                          , Op("Nil", [])
                                                          )
                                                        ]
                                                      )
                                                    , Op("Nil", [])
                                                    )
                                                  , Anno(Str(">>>"), Op("Nil", []))
                                                  , Var("r_11")
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
          "desugar_arrow_p__0_1"
        , []
        , [VarDec("i_30", ConstType(Sort("ATerm", [])))]
        , GuardedLChoice(
            Scope(
              ["g_16", "h_16", "i_16", "j_16"]
            , Seq(
                Match(
                  Anno(
                    Op("ArrFirst", [Var("h_16"), Var("g_16")])
                  , Wld()
                  )
                )
              , Seq(
                  Match(Var("j_16"))
                , Seq(
                    Build(Var("i_30"))
                  , Seq(
                      CallT(SVar("tuple_pat_0_0"), [], [])
                    , Seq(
                        Match(Var("i_16"))
                      , Seq(
                          Build(Var("j_16"))
                        , Build(
                            Anno(
                              Op(
                                "OpApp"
                              , [ Anno(
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
                                            "Abs"
                                          , [ Anno(
                                                Op(
                                                  "Cons"
                                                , [Var("i_16"), Anno(Op("Nil", []), Op("Nil", []))]
                                                )
                                              , Op("Nil", [])
                                              )
                                            , Var("g_16")
                                            ]
                                          )
                                        , Op("Nil", [])
                                        )
                                      ]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Anno(Str(">>>"), Op("Nil", []))
                                , Var("h_16")
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
          , Id()
          , GuardedLChoice(
              Scope(
                ["b_16", "c_16", "d_16", "e_16"]
              , Seq(
                  Match(
                    Anno(
                      Op("ArrHigher", [Var("b_16"), Var("c_16")])
                    , Wld()
                    )
                  )
                , Seq(
                    Match(Var("e_16"))
                  , Seq(
                      Build(Var("i_30"))
                    , Seq(
                        CallT(SVar("tuple_pat_0_0"), [], [])
                      , Seq(
                          Match(Var("d_16"))
                        , Seq(
                            Build(Var("e_16"))
                          , Build(
                              Anno(
                                Op(
                                  "OpApp"
                                , [ Anno(
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
                                              "Abs"
                                            , [ Anno(
                                                  Op(
                                                    "Cons"
                                                  , [Var("d_16"), Anno(Op("Nil", []), Op("Nil", []))]
                                                  )
                                                , Op("Nil", [])
                                                )
                                              , Anno(
                                                  Op(
                                                    "Product"
                                                  , [ Anno(
                                                        Op(
                                                          "ECons"
                                                        , [ Var("b_16")
                                                          , Anno(
                                                              Op(
                                                                "Cons"
                                                              , [Var("c_16"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                  , Anno(Str(">>>"), Op("Nil", []))
                                  , Anno(
                                      Op(
                                        "Var"
                                      , [Anno(Str("app"), Op("Nil", []))]
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
            , Id()
            , GuardedLChoice(
                Scope(
                  [ "n_15"
                  , "o_15"
                  , "p_15"
                  , "q_15"
                  , "v_15"
                  , "r_15"
                  , "w_15"
                  , "s_15"
                  , "x_15"
                  , "t_15"
                  , "y_15"
                  , "u_15"
                  , "z_15"
                  ]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          "ArrIf"
                        , [Var("n_15"), Var("o_15"), Var("p_15")]
                        )
                      , Wld()
                      )
                    )
                  , Seq(
                      Match(Var("v_15"))
                    , Seq(
                        Build(Var("i_30"))
                      , Seq(
                          CallT(SVar("tuple_pat_0_0"), [], [])
                        , Seq(
                            Match(Var("q_15"))
                          , Seq(
                              Build(Var("v_15"))
                            , Seq(
                                Match(Var("w_15"))
                              , Seq(
                                  Build(Var("i_30"))
                                , Seq(
                                    CallT(SVar("tuple_0_0"), [], [])
                                  , Seq(
                                      Match(Var("r_15"))
                                    , Seq(
                                        Build(Var("w_15"))
                                      , Seq(
                                          Match(Var("x_15"))
                                        , Seq(
                                            Build(Var("i_30"))
                                          , Seq(
                                              CallT(SVar("tuple_0_0"), [], [])
                                            , Seq(
                                                Match(Var("s_15"))
                                              , Seq(
                                                  Build(Var("x_15"))
                                                , Seq(
                                                    Match(Var("y_15"))
                                                  , Seq(
                                                      Build(Var("o_15"))
                                                    , Seq(
                                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                                      , Seq(
                                                          Match(Var("t_15"))
                                                        , Seq(
                                                            Build(Var("y_15"))
                                                          , Seq(
                                                              Match(Var("z_15"))
                                                            , Seq(
                                                                Build(Var("p_15"))
                                                              , Seq(
                                                                  CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                                                , Seq(
                                                                    Match(Var("u_15"))
                                                                  , Seq(
                                                                      Build(Var("z_15"))
                                                                    , Build(
                                                                        Anno(
                                                                          Op(
                                                                            "OpApp"
                                                                          , [ Anno(
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
                                                                                        "Abs"
                                                                                      , [ Anno(
                                                                                            Op(
                                                                                              "Cons"
                                                                                            , [Var("q_15"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                            )
                                                                                          , Op("Nil", [])
                                                                                          )
                                                                                        , Anno(
                                                                                            Op(
                                                                                              "If"
                                                                                            , [ Var("n_15")
                                                                                              , Anno(
                                                                                                  Op(
                                                                                                    "AppBin"
                                                                                                  , [ Anno(
                                                                                                        Op(
                                                                                                          "Constr"
                                                                                                        , [Anno(Str("Left"), Op("Nil", []))]
                                                                                                        )
                                                                                                      , Op("Nil", [])
                                                                                                      )
                                                                                                    , Var("r_15")
                                                                                                    ]
                                                                                                  )
                                                                                                , Op("Nil", [])
                                                                                                )
                                                                                              , Anno(
                                                                                                  Op(
                                                                                                    "AppBin"
                                                                                                  , [ Anno(
                                                                                                        Op(
                                                                                                          "Constr"
                                                                                                        , [Anno(Str("Right"), Op("Nil", []))]
                                                                                                        )
                                                                                                      , Op("Nil", [])
                                                                                                      )
                                                                                                    , Var("s_15")
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
                                                                            , Anno(Str(">>>"), Op("Nil", []))
                                                                            , Anno(
                                                                                Op(
                                                                                  "OpApp"
                                                                                , [ Var("t_15")
                                                                                  , Anno(Str("|||"), Op("Nil", []))
                                                                                  , Var("u_15")
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
              , Id()
              , GuardedLChoice(
                  Scope(
                    [ "b_15"
                    , "c_15"
                    , "d_15"
                    , "e_15"
                    , "f_15"
                    , "g_15"
                    , "j_15"
                    , "h_15"
                    , "k_15"
                    , "i_15"
                    , "l_15"
                    ]
                  , Seq(
                      Match(
                        Anno(
                          Op("ArrLet", [Var("c_15"), Var("b_15")])
                        , Wld()
                        )
                      )
                    , Seq(
                        Match(Var("f_15"))
                      , Seq(
                          Build(Var("c_15"))
                        , Seq(
                            CallT(SVar("free_decls_vars_0_0"), [], [])
                          , Seq(
                              Match(Var("d_15"))
                            , Seq(
                                Build(
                                  Anno(
                                    Op("", [Var("i_30"), Var("d_15")])
                                  , Op("Nil", [])
                                  )
                                )
                              , Seq(
                                  CallT(SVar("conc_0_0"), [], [])
                                , Seq(
                                    Match(Var("e_15"))
                                  , Seq(
                                      Build(Var("f_15"))
                                    , Seq(
                                        Match(Var("j_15"))
                                      , Seq(
                                          Build(Var("i_30"))
                                        , Seq(
                                            CallT(SVar("tuple_pat_0_0"), [], [])
                                          , Seq(
                                              Match(Var("g_15"))
                                            , Seq(
                                                Build(Var("j_15"))
                                              , Seq(
                                                  Match(Var("k_15"))
                                                , Seq(
                                                    Build(Var("e_15"))
                                                  , Seq(
                                                      CallT(SVar("tuple_0_0"), [], [])
                                                    , Seq(
                                                        Match(Var("h_15"))
                                                      , Seq(
                                                          Build(Var("k_15"))
                                                        , Seq(
                                                            Match(Var("l_15"))
                                                          , Seq(
                                                              Build(Var("b_15"))
                                                            , Seq(
                                                                CallT(SVar("desugar_arrow_p__0_1"), [], [Var("e_15")])
                                                              , Seq(
                                                                  Match(Var("i_15"))
                                                                , Seq(
                                                                    Build(Var("l_15"))
                                                                  , Build(
                                                                      Anno(
                                                                        Op(
                                                                          "OpApp"
                                                                        , [ Anno(
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
                                                                                      "Abs"
                                                                                    , [ Anno(
                                                                                          Op(
                                                                                            "Cons"
                                                                                          , [Var("g_15"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                          )
                                                                                        , Op("Nil", [])
                                                                                        )
                                                                                      , Anno(
                                                                                          Op("Let", [Var("c_15"), Var("h_15")])
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
                                                                          , Anno(Str(">>>"), Op("Nil", []))
                                                                          , Var("i_15")
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
                , Id()
                , GuardedLChoice(
                    Scope(
                      [ "p_14"
                      , "q_14"
                      , "r_14"
                      , "s_14"
                      , "t_14"
                      , "u_14"
                      , "x_14"
                      , "v_14"
                      , "y_14"
                      , "w_14"
                      , "z_14"
                      ]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              "ArrAbs"
                            , [ Anno(
                                  Op(
                                    "Cons"
                                  , [Var("q_14"), Anno(Op("Nil", []), Wld())]
                                  )
                                , Wld()
                                )
                              , Var("p_14")
                              ]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("t_14"))
                        , Seq(
                            Build(Var("q_14"))
                          , Seq(
                              CallT(SVar("free_pat_vars_0_0"), [], [])
                            , Seq(
                                Match(Var("r_14"))
                              , Seq(
                                  Build(
                                    Anno(
                                      Op("", [Var("i_30"), Var("r_14")])
                                    , Op("Nil", [])
                                    )
                                  )
                                , Seq(
                                    CallT(SVar("conc_0_0"), [], [])
                                  , Seq(
                                      Match(Var("s_14"))
                                    , Seq(
                                        Build(Var("t_14"))
                                      , Seq(
                                          Match(Var("x_14"))
                                        , Seq(
                                            Build(Var("i_30"))
                                          , Seq(
                                              CallT(SVar("tuple_pat_0_0"), [], [])
                                            , Seq(
                                                Match(Var("u_14"))
                                              , Seq(
                                                  Build(Var("x_14"))
                                                , Seq(
                                                    Match(Var("y_14"))
                                                  , Seq(
                                                      Build(Var("s_14"))
                                                    , Seq(
                                                        CallT(SVar("tuple_0_0"), [], [])
                                                      , Seq(
                                                          Match(Var("v_14"))
                                                        , Seq(
                                                            Build(Var("y_14"))
                                                          , Seq(
                                                              Match(Var("z_14"))
                                                            , Seq(
                                                                Build(Var("p_14"))
                                                              , Seq(
                                                                  CallT(SVar("desugar_arrow_p__0_1"), [], [Var("s_14")])
                                                                , Seq(
                                                                    Match(Var("w_14"))
                                                                  , Seq(
                                                                      Build(Var("z_14"))
                                                                    , Build(
                                                                        Anno(
                                                                          Op(
                                                                            "OpApp"
                                                                          , [ Anno(
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
                                                                                        "Abs"
                                                                                      , [ Anno(
                                                                                            Op(
                                                                                              "Cons"
                                                                                            , [ Anno(
                                                                                                  Op(
                                                                                                    "Tuple"
                                                                                                  , [ Var("u_14")
                                                                                                    , Anno(
                                                                                                        Op(
                                                                                                          "Cons"
                                                                                                        , [ Anno(
                                                                                                              Op("Var", [Var("q_14")])
                                                                                                            , Op("Nil", [])
                                                                                                            )
                                                                                                          , Anno(Op("Nil", []), Op("Nil", []))
                                                                                                          ]
                                                                                                        )
                                                                                                      , Op("Nil", [])
                                                                                                      )
                                                                                                    ]
                                                                                                  )
                                                                                                , Op("Nil", [])
                                                                                                )
                                                                                              , Anno(Op("Nil", []), Op("Nil", []))
                                                                                              ]
                                                                                            )
                                                                                          , Op("Nil", [])
                                                                                          )
                                                                                        , Var("v_14")
                                                                                        ]
                                                                                      )
                                                                                    , Op("Nil", [])
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              , Op("Nil", [])
                                                                              )
                                                                            , Anno(Str(">>>"), Op("Nil", []))
                                                                            , Var("w_14")
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
                  , Id()
                  , GuardedLChoice(
                      Scope(
                        ["g_14", "h_14", "i_14", "l_14", "j_14", "m_14", "k_14", "n_14"]
                      , Seq(
                          Match(
                            Anno(
                              Op("ArrAppBin", [Var("h_14"), Var("g_14")])
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("l_14"))
                          , Seq(
                              Build(Var("i_30"))
                            , Seq(
                                CallT(SVar("tuple_pat_0_0"), [], [])
                              , Seq(
                                  Match(Var("i_14"))
                                , Seq(
                                    Build(Var("l_14"))
                                  , Seq(
                                      Match(Var("m_14"))
                                    , Seq(
                                        Build(Var("i_30"))
                                      , Seq(
                                          CallT(SVar("tuple_0_0"), [], [])
                                        , Seq(
                                            Match(Var("j_14"))
                                          , Seq(
                                              Build(Var("m_14"))
                                            , Seq(
                                                Match(Var("n_14"))
                                              , Seq(
                                                  Build(Var("h_14"))
                                                , Seq(
                                                    CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                                  , Seq(
                                                      Match(Var("k_14"))
                                                    , Seq(
                                                        Build(Var("n_14"))
                                                      , Build(
                                                          Anno(
                                                            Op(
                                                              "OpApp"
                                                            , [ Anno(
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
                                                                          "Abs"
                                                                        , [ Anno(
                                                                              Op(
                                                                                "Cons"
                                                                              , [Var("i_14"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                              )
                                                                            , Op("Nil", [])
                                                                            )
                                                                          , Anno(
                                                                              Op(
                                                                                "Product"
                                                                              , [ Anno(
                                                                                    Op(
                                                                                      "ECons"
                                                                                    , [ Var("j_14")
                                                                                      , Anno(
                                                                                          Op(
                                                                                            "Cons"
                                                                                          , [Var("g_14"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                              , Anno(Str(">>>"), Op("Nil", []))
                                                              , Var("k_14")
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
                          [ "v_13"
                          , "w_13"
                          , "x_13"
                          , "y_13"
                          , "z_13"
                          , "b_14"
                          , "a_14"
                          , "c_14"
                          , "d_14"
                          , "e_14"
                          ]
                        , Seq(
                            Match(
                              Anno(
                                Op("ArrForm", [Var("v_13"), Var("w_13")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Match(Var("y_13"))
                            , Seq(
                                Match(Var("b_14"))
                              , Seq(
                                  Build(Var("i_30"))
                                , Seq(
                                    CallT(SVar("tuple_pat_0_0"), [], [])
                                  , Seq(
                                      Match(Var("z_13"))
                                    , Seq(
                                        Build(Var("b_14"))
                                      , Seq(
                                          Match(Var("c_14"))
                                        , Seq(
                                            Build(Var("i_30"))
                                          , Seq(
                                              CallT(SVar("tuple_0_0"), [], [])
                                            , Seq(
                                                Match(Var("a_14"))
                                              , Seq(
                                                  Build(Var("c_14"))
                                                , Seq(
                                                    Build(
                                                      Anno(
                                                        Op(
                                                          "Abs"
                                                        , [ Anno(
                                                              Op(
                                                                "Cons"
                                                              , [Var("z_13"), Anno(Op("Nil", []), Op("Nil", []))]
                                                              )
                                                            , Op("Nil", [])
                                                            )
                                                          , Var("a_14")
                                                          ]
                                                        )
                                                      , Op("Nil", [])
                                                      )
                                                    )
                                                  , Seq(
                                                      Match(Var("x_13"))
                                                    , Seq(
                                                        Build(Var("y_13"))
                                                      , Seq(
                                                          Match(Var("e_14"))
                                                        , Seq(
                                                            Build(Var("w_13"))
                                                          , Seq(
                                                              CallT(
                                                                SVar("map_1_0")
                                                              , [CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])]
                                                              , []
                                                              )
                                                            , Seq(
                                                                Match(Var("d_14"))
                                                              , Seq(
                                                                  Build(Var("e_14"))
                                                                , Seq(
                                                                    Build(
                                                                      Anno(
                                                                        Op("", [Var("v_13"), Var("d_14")])
                                                                      , Op("Nil", [])
                                                                      )
                                                                    )
                                                                  , CallT(SVar("apply_all_0_1"), [], [Var("x_13")])
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
                            )
                          )
                        )
                      , Id()
                      , GuardedLChoice(
                          Scope(
                            ["r_13", "s_13", "t_13"]
                          , Seq(
                              Match(
                                Anno(
                                  Op(
                                    "ArrOpApp"
                                  , [Var("s_13"), Var("r_13"), Var("t_13")]
                                  )
                                , Wld()
                                )
                              )
                            , Seq(
                                Build(
                                  Anno(
                                    Op(
                                      "ArrForm"
                                    , [ Anno(
                                          Op("BinCon", [Var("r_13")])
                                        , Op("Nil", [])
                                        )
                                      , Anno(
                                          Op(
                                            "Cons"
                                          , [ Var("s_13")
                                            , Anno(
                                                Op(
                                                  "Cons"
                                                , [Var("t_13"), Anno(Op("Nil", []), Op("Nil", []))]
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
                              , CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                              )
                            )
                          )
                        , Id()
                        , GuardedLChoice(
                            Scope(
                              ["p_13"]
                            , Seq(
                                Match(
                                  Anno(
                                    Op(
                                      "ArrDo"
                                    , [ Anno(
                                          Op(
                                            "ArrStmtList"
                                          , [Anno(Op("ArrCmdStmt", [Var("p_13")]), Wld())]
                                          )
                                        , Wld()
                                        )
                                      ]
                                    )
                                  , Wld()
                                  )
                                )
                              , Seq(
                                  Build(Var("p_13"))
                                , CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                )
                              )
                            )
                          , Id()
                          , GuardedLChoice(
                              Scope(
                                [ "d_13"
                                , "e_13"
                                , "f_13"
                                , "g_13"
                                , "h_13"
                                , "i_13"
                                , "l_13"
                                , "j_13"
                                , "m_13"
                                , "k_13"
                                , "n_13"
                                ]
                              , Seq(
                                  Match(
                                    Anno(
                                      Op(
                                        "ArrDo"
                                      , [ Anno(
                                            Op(
                                              "ArrStmtList"
                                            , [ Anno(
                                                  Op(
                                                    "ArrStmtSeq"
                                                  , [Anno(Op("ArrLetStmt", [Var("e_13")]), Wld()), Var("d_13")]
                                                  )
                                                , Wld()
                                                )
                                              ]
                                            )
                                          , Wld()
                                          )
                                        ]
                                      )
                                    , Wld()
                                    )
                                  )
                                , Seq(
                                    Match(Var("h_13"))
                                  , Seq(
                                      Build(Var("e_13"))
                                    , Seq(
                                        CallT(SVar("free_decls_vars_0_0"), [], [])
                                      , Seq(
                                          Match(Var("f_13"))
                                        , Seq(
                                            Build(
                                              Anno(
                                                Op("", [Var("i_30"), Var("f_13")])
                                              , Op("Nil", [])
                                              )
                                            )
                                          , Seq(
                                              CallT(SVar("conc_0_0"), [], [])
                                            , Seq(
                                                Match(Var("g_13"))
                                              , Seq(
                                                  Build(Var("h_13"))
                                                , Seq(
                                                    Match(Var("l_13"))
                                                  , Seq(
                                                      Build(Var("i_30"))
                                                    , Seq(
                                                        CallT(SVar("tuple_pat_0_0"), [], [])
                                                      , Seq(
                                                          Match(Var("i_13"))
                                                        , Seq(
                                                            Build(Var("l_13"))
                                                          , Seq(
                                                              Match(Var("m_13"))
                                                            , Seq(
                                                                Build(Var("g_13"))
                                                              , Seq(
                                                                  CallT(SVar("tuple_0_0"), [], [])
                                                                , Seq(
                                                                    Match(Var("j_13"))
                                                                  , Seq(
                                                                      Build(Var("m_13"))
                                                                    , Seq(
                                                                        Match(Var("n_13"))
                                                                      , Seq(
                                                                          Build(
                                                                            Anno(
                                                                              Op(
                                                                                "ArrDo"
                                                                              , [Anno(
                                                                                   Op("ArrStmtList", [Var("d_13")])
                                                                                 , Op("Nil", [])
                                                                                 )]
                                                                              )
                                                                            , Op("Nil", [])
                                                                            )
                                                                          )
                                                                        , Seq(
                                                                            CallT(SVar("desugar_arrow_p__0_1"), [], [Var("g_13")])
                                                                          , Seq(
                                                                              Match(Var("k_13"))
                                                                            , Seq(
                                                                                Build(Var("n_13"))
                                                                              , Build(
                                                                                  Anno(
                                                                                    Op(
                                                                                      "OpApp"
                                                                                    , [ Anno(
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
                                                                                                  "Abs"
                                                                                                , [ Anno(
                                                                                                      Op(
                                                                                                        "Cons"
                                                                                                      , [Var("i_13"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                      )
                                                                                                    , Op("Nil", [])
                                                                                                    )
                                                                                                  , Anno(
                                                                                                      Op("Let", [Var("e_13"), Var("j_13")])
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
                                                                                      , Anno(Str(">>>"), Op("Nil", []))
                                                                                      , Var("k_13")
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
                            , Id()
                            , GuardedLChoice(
                                Scope(
                                  [ "q_12"
                                  , "r_12"
                                  , "s_12"
                                  , "x_12"
                                  , "t_12"
                                  , "y_12"
                                  , "u_12"
                                  , "z_12"
                                  , "v_12"
                                  , "a_13"
                                  , "w_12"
                                  , "b_13"
                                  ]
                                , Seq(
                                    Match(
                                      Anno(
                                        Op(
                                          "ArrDo"
                                        , [ Anno(
                                              Op(
                                                "ArrStmtList"
                                              , [ Anno(
                                                    Op(
                                                      "ArrStmtSeq"
                                                    , [Anno(Op("ArrCmdStmt", [Var("q_12")]), Wld()), Var("r_12")]
                                                    )
                                                  , Wld()
                                                  )
                                                ]
                                              )
                                            , Wld()
                                            )
                                          ]
                                        )
                                      , Wld()
                                      )
                                    )
                                  , Seq(
                                      Match(Var("x_12"))
                                    , Seq(
                                        Build(Var("i_30"))
                                      , Seq(
                                          CallT(SVar("tuple_pat_0_0"), [], [])
                                        , Seq(
                                            Match(Var("s_12"))
                                          , Seq(
                                              Build(Var("x_12"))
                                            , Seq(
                                                Match(Var("y_12"))
                                              , Seq(
                                                  Build(Var("i_30"))
                                                , Seq(
                                                    CallT(SVar("tuple_0_0"), [], [])
                                                  , Seq(
                                                      Match(Var("t_12"))
                                                    , Seq(
                                                        Build(Var("y_12"))
                                                      , Seq(
                                                          Match(Var("z_12"))
                                                        , Seq(
                                                            Build(Var("i_30"))
                                                          , Seq(
                                                              CallT(SVar("tuple_0_0"), [], [])
                                                            , Seq(
                                                                Match(Var("u_12"))
                                                              , Seq(
                                                                  Build(Var("z_12"))
                                                                , Seq(
                                                                    Match(Var("a_13"))
                                                                  , Seq(
                                                                      Build(Var("q_12"))
                                                                    , Seq(
                                                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                                                      , Seq(
                                                                          Match(Var("v_12"))
                                                                        , Seq(
                                                                            Build(Var("a_13"))
                                                                          , Seq(
                                                                              Match(Var("b_13"))
                                                                            , Seq(
                                                                                Build(
                                                                                  Anno(
                                                                                    Op(
                                                                                      "ArrDo"
                                                                                    , [Anno(
                                                                                         Op("ArrStmtList", [Var("r_12")])
                                                                                       , Op("Nil", [])
                                                                                       )]
                                                                                    )
                                                                                  , Op("Nil", [])
                                                                                  )
                                                                                )
                                                                              , Seq(
                                                                                  CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                                                                , Seq(
                                                                                    Match(Var("w_12"))
                                                                                  , Seq(
                                                                                      Build(Var("b_13"))
                                                                                    , Build(
                                                                                        Anno(
                                                                                          Op(
                                                                                            "OpApp"
                                                                                          , [ Anno(
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
                                                                                                        "Abs"
                                                                                                      , [ Anno(
                                                                                                            Op(
                                                                                                              "Cons"
                                                                                                            , [Var("s_12"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                            )
                                                                                                          , Op("Nil", [])
                                                                                                          )
                                                                                                        , Anno(
                                                                                                            Op(
                                                                                                              "Product"
                                                                                                            , [ Anno(
                                                                                                                  Op(
                                                                                                                    "ECons"
                                                                                                                  , [ Var("t_12")
                                                                                                                    , Anno(
                                                                                                                        Op(
                                                                                                                          "Cons"
                                                                                                                        , [Var("u_12"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                                                            , Anno(Str(">>>"), Op("Nil", []))
                                                                                            , Anno(
                                                                                                Op(
                                                                                                  "OpApp"
                                                                                                , [ Anno(
                                                                                                      Op(
                                                                                                        "AppBin"
                                                                                                      , [ Anno(
                                                                                                            Op(
                                                                                                              "Var"
                                                                                                            , [Anno(Str("first"), Op("Nil", []))]
                                                                                                            )
                                                                                                          , Op("Nil", [])
                                                                                                          )
                                                                                                        , Var("v_12")
                                                                                                        ]
                                                                                                      )
                                                                                                    , Op("Nil", [])
                                                                                                    )
                                                                                                  , Anno(Str(">>>"), Op("Nil", []))
                                                                                                  , Anno(
                                                                                                      Op(
                                                                                                        "OpApp"
                                                                                                      , [ Anno(
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
                                                                                                                    "Var"
                                                                                                                  , [Anno(Str("snd"), Op("Nil", []))]
                                                                                                                  )
                                                                                                                , Op("Nil", [])
                                                                                                                )
                                                                                                              ]
                                                                                                            )
                                                                                                          , Op("Nil", [])
                                                                                                          )
                                                                                                        , Anno(Str(">>>"), Op("Nil", []))
                                                                                                        , Var("w_12")
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
                              , Id()
                              , Scope(
                                  [ "v_11"
                                  , "w_11"
                                  , "x_11"
                                  , "y_11"
                                  , "z_11"
                                  , "a_12"
                                  , "b_12"
                                  , "i_12"
                                  , "c_12"
                                  , "j_12"
                                  , "d_12"
                                  , "k_12"
                                  , "e_12"
                                  , "l_12"
                                  , "f_12"
                                  , "m_12"
                                  , "g_12"
                                  , "n_12"
                                  , "h_12"
                                  , "o_12"
                                  ]
                                , Seq(
                                    Match(
                                      Anno(
                                        Op(
                                          "ArrDo"
                                        , [ Anno(
                                              Op(
                                                "ArrStmtList"
                                              , [ Anno(
                                                    Op(
                                                      "ArrStmtSeq"
                                                    , [ Anno(
                                                          Op("ArrBindStmt", [Var("x_11"), Var("v_11")])
                                                        , Wld()
                                                        )
                                                      , Var("w_11")
                                                      ]
                                                    )
                                                  , Wld()
                                                  )
                                                ]
                                              )
                                            , Wld()
                                            )
                                          ]
                                        )
                                      , Wld()
                                      )
                                    )
                                  , Seq(
                                      Match(Var("a_12"))
                                    , Seq(
                                        Build(Var("x_11"))
                                      , Seq(
                                          CallT(SVar("free_pat_vars_0_0"), [], [])
                                        , Seq(
                                            Match(Var("y_11"))
                                          , Seq(
                                              Build(
                                                Anno(
                                                  Op("", [Var("y_11"), Var("i_30")])
                                                , Op("Nil", [])
                                                )
                                              )
                                            , Seq(
                                                CallT(SVar("conc_0_0"), [], [])
                                              , Seq(
                                                  Match(Var("z_11"))
                                                , Seq(
                                                    Build(Var("a_12"))
                                                  , Seq(
                                                      Match(Var("i_12"))
                                                    , Seq(
                                                        Build(Var("i_30"))
                                                      , Seq(
                                                          CallT(SVar("tuple_pat_0_0"), [], [])
                                                        , Seq(
                                                            Match(Var("b_12"))
                                                          , Seq(
                                                              Build(Var("i_12"))
                                                            , Seq(
                                                                Match(Var("j_12"))
                                                              , Seq(
                                                                  Build(Var("i_30"))
                                                                , Seq(
                                                                    CallT(SVar("tuple_0_0"), [], [])
                                                                  , Seq(
                                                                      Match(Var("c_12"))
                                                                    , Seq(
                                                                        Build(Var("j_12"))
                                                                      , Seq(
                                                                          Match(Var("k_12"))
                                                                        , Seq(
                                                                            Build(Var("i_30"))
                                                                          , Seq(
                                                                              CallT(SVar("tuple_0_0"), [], [])
                                                                            , Seq(
                                                                                Match(Var("d_12"))
                                                                              , Seq(
                                                                                  Build(Var("k_12"))
                                                                                , Seq(
                                                                                    Match(Var("l_12"))
                                                                                  , Seq(
                                                                                      Build(Var("v_11"))
                                                                                    , Seq(
                                                                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("i_30")])
                                                                                      , Seq(
                                                                                          Match(Var("e_12"))
                                                                                        , Seq(
                                                                                            Build(Var("l_12"))
                                                                                          , Seq(
                                                                                              Match(Var("m_12"))
                                                                                            , Seq(
                                                                                                Build(Var("i_30"))
                                                                                              , Seq(
                                                                                                  CallT(SVar("tuple_pat_0_0"), [], [])
                                                                                                , Seq(
                                                                                                    Match(Var("f_12"))
                                                                                                  , Seq(
                                                                                                      Build(Var("m_12"))
                                                                                                    , Seq(
                                                                                                        Match(Var("n_12"))
                                                                                                      , Seq(
                                                                                                          Build(Var("z_11"))
                                                                                                        , Seq(
                                                                                                            CallT(SVar("tuple_0_0"), [], [])
                                                                                                          , Seq(
                                                                                                              Match(Var("g_12"))
                                                                                                            , Seq(
                                                                                                                Build(Var("n_12"))
                                                                                                              , Seq(
                                                                                                                  Match(Var("o_12"))
                                                                                                                , Seq(
                                                                                                                    Build(
                                                                                                                      Anno(
                                                                                                                        Op(
                                                                                                                          "ArrDo"
                                                                                                                        , [Anno(
                                                                                                                             Op("ArrStmtList", [Var("w_11")])
                                                                                                                           , Op("Nil", [])
                                                                                                                           )]
                                                                                                                        )
                                                                                                                      , Op("Nil", [])
                                                                                                                      )
                                                                                                                    )
                                                                                                                  , Seq(
                                                                                                                      CallT(SVar("desugar_arrow_p__0_1"), [], [Var("z_11")])
                                                                                                                    , Seq(
                                                                                                                        Match(Var("h_12"))
                                                                                                                      , Seq(
                                                                                                                          Build(Var("o_12"))
                                                                                                                        , Build(
                                                                                                                            Anno(
                                                                                                                              Op(
                                                                                                                                "OpApp"
                                                                                                                              , [ Anno(
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
                                                                                                                                            "Abs"
                                                                                                                                          , [ Anno(
                                                                                                                                                Op(
                                                                                                                                                  "Cons"
                                                                                                                                                , [Var("b_12"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                                                                )
                                                                                                                                              , Op("Nil", [])
                                                                                                                                              )
                                                                                                                                            , Anno(
                                                                                                                                                Op(
                                                                                                                                                  "Product"
                                                                                                                                                , [ Anno(
                                                                                                                                                      Op(
                                                                                                                                                        "ECons"
                                                                                                                                                      , [ Var("c_12")
                                                                                                                                                        , Anno(
                                                                                                                                                            Op(
                                                                                                                                                              "Cons"
                                                                                                                                                            , [Var("d_12"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                                                                                                , Anno(Str(">>>"), Op("Nil", []))
                                                                                                                                , Anno(
                                                                                                                                    Op(
                                                                                                                                      "OpApp"
                                                                                                                                    , [ Anno(
                                                                                                                                          Op(
                                                                                                                                            "AppBin"
                                                                                                                                          , [ Anno(
                                                                                                                                                Op(
                                                                                                                                                  "Var"
                                                                                                                                                , [Anno(Str("first"), Op("Nil", []))]
                                                                                                                                                )
                                                                                                                                              , Op("Nil", [])
                                                                                                                                              )
                                                                                                                                            , Var("e_12")
                                                                                                                                            ]
                                                                                                                                          )
                                                                                                                                        , Op("Nil", [])
                                                                                                                                        )
                                                                                                                                      , Anno(Str(">>>"), Op("Nil", []))
                                                                                                                                      , Anno(
                                                                                                                                          Op(
                                                                                                                                            "OpApp"
                                                                                                                                          , [ Anno(
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
                                                                                                                                                        "Abs"
                                                                                                                                                      , [ Anno(
                                                                                                                                                            Op(
                                                                                                                                                              "Cons"
                                                                                                                                                            , [ Anno(
                                                                                                                                                                  Op(
                                                                                                                                                                    "Tuple"
                                                                                                                                                                  , [ Var("x_11")
                                                                                                                                                                    , Anno(
                                                                                                                                                                        Op(
                                                                                                                                                                          "Cons"
                                                                                                                                                                        , [Var("f_12"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                                                                                        )
                                                                                                                                                                      , Op("Nil", [])
                                                                                                                                                                      )
                                                                                                                                                                    ]
                                                                                                                                                                  )
                                                                                                                                                                , Op("Nil", [])
                                                                                                                                                                )
                                                                                                                                                              , Anno(Op("Nil", []), Op("Nil", []))
                                                                                                                                                              ]
                                                                                                                                                            )
                                                                                                                                                          , Op("Nil", [])
                                                                                                                                                          )
                                                                                                                                                        , Var("g_12")
                                                                                                                                                        ]
                                                                                                                                                      )
                                                                                                                                                    , Op("Nil", [])
                                                                                                                                                    )
                                                                                                                                                  ]
                                                                                                                                                )
                                                                                                                                              , Op("Nil", [])
                                                                                                                                              )
                                                                                                                                            , Anno(Str(">>>"), Op("Nil", []))
                                                                                                                                            , Var("h_12")
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
          "tuple_pat_0_0"
        , []
        , []
        , GuardedLChoice(
            Seq(
              Match(Anno(Op("Nil", []), Wld()))
            , Build(
                Anno(
                  Op(
                    "Constr"
                  , [Anno(Op("Unit", []), Op("Nil", []))]
                  )
                , Op("Nil", [])
                )
              )
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["m_16"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        "Cons"
                      , [Var("m_16"), Anno(Op("Nil", []), Wld())]
                      )
                    , Wld()
                    )
                  )
                , Build(Var("m_16"))
                )
              )
            , Id()
            , Scope(
                ["k_16", "l_16"]
              , Seq(
                  Match(
                    Anno(
                      Op("Cons", [Var("k_16"), Var("l_16")])
                    , Wld()
                    )
                  )
                , Build(
                    Anno(
                      Op("Tuple", [Var("k_16"), Var("l_16")])
                    , Op("Nil", [])
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "tuple_0_0"
        , []
        , []
        , GuardedLChoice(
            Seq(
              Match(Anno(Op("Nil", []), Wld()))
            , Build(
                Anno(
                  Op(
                    "Constr"
                  , [Anno(Op("Unit", []), Op("Nil", []))]
                  )
                , Op("Nil", [])
                )
              )
            )
          , Id()
          , GuardedLChoice(
              Scope(
                ["p_16"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        "Cons"
                      , [Var("p_16"), Anno(Op("Nil", []), Wld())]
                      )
                    , Wld()
                    )
                  )
                , Build(Var("p_16"))
                )
              )
            , Id()
            , Scope(
                ["n_16", "o_16"]
              , Seq(
                  Match(
                    Anno(
                      Op("Cons", [Var("n_16"), Var("o_16")])
                    , Wld()
                    )
                  )
                , Build(
                    Anno(
                      Op(
                        "Product"
                      , [ Anno(
                            Op("ECons", [Var("n_16"), Var("o_16")])
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
      , SDefT(
          "free_pat_vars_0_0"
        , []
        , []
        , CallT(
            SVar("collect_all_1_0")
          , [Match(Anno(Op("Var", [Wld()]), Wld()))]
          , []
          )
        )
      , SDefT(
          "free_decls_vars_0_0"
        , []
        , []
        , CallT(
            SVar("collect_all_3_0")
          , [ Match(Anno(Op("Var", [Wld()]), Wld()))
            , CallT(SVar("union_0_0"), [], [])
            , Scope(
                ["q_16"]
              , Seq(
                  Match(
                    Anno(Op("VarFunLHS", [Var("q_16"), Wld()]), Wld())
                  )
                , Build(Var("q_16"))
                )
              )
            ]
          , []
          )
        )
      , SDefT(
          "apply_all_0_1"
        , []
        , [VarDec("j_30", ConstType(Sort("ATerm", [])))]
        , GuardedLChoice(
            Scope(
              ["w_16"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [Var("w_16"), Anno(Op("Nil", []), Wld())]
                    )
                  , Wld()
                  )
                )
              , Build(Var("w_16"))
              )
            )
          , Id()
          , Scope(
              ["s_16", "t_16", "u_16"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [ Var("s_16")
                      , Anno(
                          Op("Cons", [Var("t_16"), Var("u_16")])
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
                              "AppBin"
                            , [ Var("s_16")
                              , Anno(
                                  Op(
                                    "OpApp"
                                  , [ Anno(
                                        Op(
                                          "AppBin"
                                        , [ Anno(
                                              Op(
                                                "Var"
                                              , [Anno(Str("arr"), Op("Nil", []))]
                                              )
                                            , Op("Nil", [])
                                            )
                                          , Var("j_30")
                                          ]
                                        )
                                      , Op("Nil", [])
                                      )
                                    , Anno(Str(">>>"), Op("Nil", []))
                                    , Var("t_16")
                                    ]
                                  )
                                , Op("Nil", [])
                                )
                              ]
                            )
                          , Op("Nil", [])
                          )
                        , Var("u_16")
                        ]
                      )
                    , Op("Nil", [])
                    )
                  )
                , CallT(SVar("apply_all_0_1"), [], [Var("j_30")])
                )
              )
            )
          )
        )
      , SDefT(
          "map_1_0"
        , [ VarDec(
              "c_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "d_17"
              , []
              , []
              , GuardedLChoice(
                  Match(Anno(Op("Nil", []), Wld()))
                , Id()
                , Scope(
                    ["x_16", "y_16", "z_16", "a_17", "b_17"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("x_16"), Var("y_16")])
                        , Var("b_17")
                        )
                      )
                    , Seq(
                        Build(Var("x_16"))
                      , Seq(
                          CallT(SVar("c_17"), [], [])
                        , Seq(
                            Match(Var("z_16"))
                          , Seq(
                              Build(Var("y_16"))
                            , Seq(
                                CallT(SVar("d_17"), [], [])
                              , Seq(
                                  Match(Var("a_17"))
                                , Build(
                                    Anno(
                                      Op("Cons", [Var("z_16"), Var("a_17")])
                                    , Var("b_17")
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
            ]
          , CallT(SVar("d_17"), [], [])
          )
        )
      , SDefT(
          "collect_all_1_0"
        , [ VarDec(
              "e_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , CallT(
            SVar("collect_all_2_0")
          , [ CallT(SVar("e_17"), [], [])
            , CallT(SVar("union_0_0"), [], [])
            ]
          , []
          )
        )
      , SDefT(
          "collect_all_2_0"
        , [ VarDec(
              "f_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "h_17"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["i_17", "k_17", "j_17", "l_17"]
                  , Seq(
                      Match(Var("k_17"))
                    , Seq(
                        CallT(SVar("f_17"), [], [])
                      , Seq(
                          Match(Var("i_17"))
                        , Seq(
                            Build(Var("k_17"))
                          , Seq(
                              Match(Var("l_17"))
                            , Seq(
                                CallT(
                                  SVar("crush_3_0")
                                , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                                  , CallT(SVar("g_17"), [], [])
                                  , CallT(SVar("h_17"), [], [])
                                  ]
                                , []
                                )
                              , Seq(
                                  Match(Var("j_17"))
                                , Seq(
                                    Build(Var("l_17"))
                                  , Build(
                                      Anno(
                                        Op("Cons", [Var("i_17"), Var("j_17")])
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
                , Id()
                , CallT(
                    SVar("crush_3_0")
                  , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                    , CallT(SVar("g_17"), [], [])
                    , CallT(SVar("h_17"), [], [])
                    ]
                  , []
                  )
                )
              )
            ]
          , CallT(SVar("h_17"), [], [])
          )
        )
      , SDefT(
          "collect_all_3_0"
        , [ VarDec(
              "m_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "p_17"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["q_17", "s_17", "r_17", "t_17"]
                  , Seq(
                      Match(Var("s_17"))
                    , Seq(
                        CallT(SVar("m_17"), [], [])
                      , Seq(
                          Match(Var("q_17"))
                        , Seq(
                            Build(Var("s_17"))
                          , Seq(
                              Match(Var("t_17"))
                            , Seq(
                                CallT(
                                  SVar("crush_3_0")
                                , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                                  , CallT(SVar("n_17"), [], [])
                                  , CallT(SVar("p_17"), [], [])
                                  ]
                                , []
                                )
                              , Seq(
                                  Match(Var("r_17"))
                                , Seq(
                                    Build(Var("t_17"))
                                  , Build(
                                      Anno(
                                        Op("Cons", [Var("q_17"), Var("r_17")])
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
                , Id()
                , GuardedLChoice(
                    Seq(
                      CallT(SVar("o_17"), [], [])
                    , CallT(SVar("p_17"), [], [])
                    )
                  , Id()
                  , CallT(
                      SVar("crush_3_0")
                    , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                      , CallT(SVar("n_17"), [], [])
                      , CallT(SVar("p_17"), [], [])
                      ]
                    , []
                    )
                  )
                )
              )
            ]
          , CallT(SVar("p_17"), [], [])
          )
        )
      , SDefT(
          "crush_3_0"
        , [ VarDec(
              "v_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "w_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_17"]
          , Seq(
              Match(Anno(Explode(Wld(), Var("u_17")), Wld()))
            , Seq(
                Build(Var("u_17"))
              , CallT(
                  SVar("foldr_3_0")
                , [ CallT(SVar("v_17"), [], [])
                  , CallT(SVar("w_17"), [], [])
                  , CallT(SVar("x_17"), [], [])
                  ]
                , []
                )
              )
            )
          )
        )
      , SDefT(
          "foldr_3_0"
        , [ VarDec(
              "a_18"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_18"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_18"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , GuardedLChoice(
            Seq(
              Match(Anno(Op("Nil", []), Wld()))
            , CallT(SVar("a_18"), [], [])
            )
          , Id()
          , Scope(
              ["y_17", "z_17", "d_18", "f_18", "e_18", "g_18"]
            , Seq(
                Match(
                  Anno(
                    Op("Cons", [Var("y_17"), Var("z_17")])
                  , Wld()
                  )
                )
              , Seq(
                  Match(Var("f_18"))
                , Seq(
                    Build(Var("y_17"))
                  , Seq(
                      CallT(SVar("c_18"), [], [])
                    , Seq(
                        Match(Var("d_18"))
                      , Seq(
                          Build(Var("f_18"))
                        , Seq(
                            Match(Var("g_18"))
                          , Seq(
                              Build(Var("z_17"))
                            , Seq(
                                CallT(
                                  SVar("foldr_3_0")
                                , [ CallT(SVar("a_18"), [], [])
                                  , CallT(SVar("b_18"), [], [])
                                  , CallT(SVar("c_18"), [], [])
                                  ]
                                , []
                                )
                              , Seq(
                                  Match(Var("e_18"))
                                , Seq(
                                    Build(Var("g_18"))
                                  , Seq(
                                      Build(
                                        Anno(
                                          Op("", [Var("d_18"), Var("e_18")])
                                        , Op("Nil", [])
                                        )
                                      )
                                    , CallT(SVar("b_18"), [], [])
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
          "conc_0_0"
        , []
        , []
        , GuardedLChoice(
            Scope(
              ["h_18", "i_18"]
            , Seq(
                Match(
                  Anno(
                    Op("", [Var("h_18"), Var("i_18")])
                  , Wld()
                  )
                )
              , Seq(
                  Build(Var("h_18"))
                , CallT(SVar("at_end_1_0"), [Build(Var("i_18"))], [])
                )
              )
            )
          , Id()
          , Scope(
              ["j_18"]
            , Seq(
                Match(
                  Anno(
                    Explode(Anno(Str(""), Wld()), Var("j_18"))
                  , Wld()
                  )
                )
              , Seq(
                  Build(Var("j_18"))
                , CallT(SVar("concat_0_0"), [], [])
                )
              )
            )
          )
        )
      , SDefT(
          "at_end_1_0"
        , [ VarDec(
              "p_18"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "q_18"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["k_18", "l_18", "m_18", "n_18", "o_18"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("k_18"), Var("l_18")])
                        , Var("o_18")
                        )
                      )
                    , Seq(
                        Build(Var("k_18"))
                      , Seq(
                          Match(Var("m_18"))
                        , Seq(
                            Build(Var("l_18"))
                          , Seq(
                              CallT(SVar("q_18"), [], [])
                            , Seq(
                                Match(Var("n_18"))
                              , Build(
                                  Anno(
                                    Op("Cons", [Var("m_18"), Var("n_18")])
                                  , Var("o_18")
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
                , Seq(
                    Match(Anno(Op("Nil", []), Wld()))
                  , CallT(SVar("p_18"), [], [])
                  )
                )
              )
            ]
          , CallT(SVar("q_18"), [], [])
          )
        )
      , SDefT(
          "concat_0_0"
        , []
        , []
        , Let(
            [ SDefT(
                "t_18"
              , []
              , []
              , GuardedLChoice(
                  Match(Anno(Op("Nil", []), Wld()))
                , Id()
                , Scope(
                    ["r_18", "s_18"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("r_18"), Var("s_18")])
                        , Wld()
                        )
                      )
                    , Seq(
                        Build(Var("r_18"))
                      , CallT(
                          SVar("at_end_1_0")
                        , [Seq(
                             Build(Var("s_18"))
                           , CallT(SVar("t_18"), [], [])
                           )]
                        , []
                        )
                      )
                    )
                  )
                )
              )
            ]
          , CallT(SVar("t_18"), [], [])
          )
        )
      , SDefT(
          "union_0_0"
        , []
        , []
        , Scope(
            ["u_18", "v_18"]
          , Let(
              [ SDefT(
                  "b_19"
                , []
                , []
                , GuardedLChoice(
                    Seq(
                      Match(Anno(Op("Nil", []), Wld()))
                    , Build(Var("u_18"))
                    )
                  , Id()
                  , GuardedLChoice(
                      Seq(
                        CallT(SVar("HdMember_1_0"), [Build(Var("u_18"))], [])
                      , CallT(SVar("b_19"), [], [])
                      )
                    , Id()
                    , Scope(
                        ["w_18", "x_18", "y_18", "z_18", "a_19"]
                      , Seq(
                          Match(
                            Anno(
                              Op("Cons", [Var("w_18"), Var("x_18")])
                            , Var("a_19")
                            )
                          )
                        , Seq(
                            Build(Var("w_18"))
                          , Seq(
                              Match(Var("y_18"))
                            , Seq(
                                Build(Var("x_18"))
                              , Seq(
                                  CallT(SVar("b_19"), [], [])
                                , Seq(
                                    Match(Var("z_18"))
                                  , Build(
                                      Anno(
                                        Op("Cons", [Var("y_18"), Var("z_18")])
                                      , Var("a_19")
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
              ]
            , Seq(
                Match(
                  Anno(
                    Op("", [Var("v_18"), Var("u_18")])
                  , Wld()
                  )
                )
              , Seq(
                  Build(Var("v_18"))
                , CallT(SVar("b_19"), [], [])
                )
              )
            )
          )
        )
      , SDefT(
          "HdMember_1_0"
        , [ VarDec(
              "f_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_19", "d_19", "g_19"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("d_19"), Var("c_19")])
                , Wld()
                )
              )
            , Seq(
                Match(Var("g_19"))
              , Seq(
                  CallT(SVar("f_19"), [], [])
                , Seq(
                    CallT(
                      SVar("fetch_1_0")
                    , [ Scope(
                          ["e_19"]
                        , Seq(
                            Match(Var("e_19"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("d_19"), Var("e_19")])
                                , Op("Nil", [])
                                )
                              )
                            , CallT(SVar("eq_0_0"), [], [])
                            )
                          )
                        )
                      ]
                    , []
                    )
                  , Seq(Build(Var("g_19")), Build(Var("c_19")))
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "fetch_1_0"
        , [ VarDec(
              "r_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "s_19"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["h_19", "i_19", "j_19", "k_19", "l_19"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("h_19"), Var("i_19")])
                        , Var("l_19")
                        )
                      )
                    , Seq(
                        Build(Var("h_19"))
                      , Seq(
                          CallT(SVar("r_19"), [], [])
                        , Seq(
                            Match(Var("j_19"))
                          , Seq(
                              Build(Var("i_19"))
                            , Seq(
                                Match(Var("k_19"))
                              , Build(
                                  Anno(
                                    Op("Cons", [Var("j_19"), Var("k_19")])
                                  , Var("l_19")
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
                , Scope(
                    ["m_19", "n_19", "o_19", "p_19", "q_19"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("m_19"), Var("n_19")])
                        , Var("q_19")
                        )
                      )
                    , Seq(
                        Build(Var("m_19"))
                      , Seq(
                          Match(Var("o_19"))
                        , Seq(
                            Build(Var("n_19"))
                          , Seq(
                              CallT(SVar("s_19"), [], [])
                            , Seq(
                                Match(Var("p_19"))
                              , Build(
                                  Anno(
                                    Op("Cons", [Var("o_19"), Var("p_19")])
                                  , Var("q_19")
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
            ]
          , CallT(SVar("s_19"), [], [])
          )
        )
      , SDefT(
          "eq_0_0"
        , []
        , []
        , Scope(
            ["t_19"]
          , Match(
              Anno(
                Op("", [Var("t_19"), Var("t_19")])
              , Wld()
              )
            )
          )
        )
      , SDefT(
          "oncetd_1_0"
        , [ VarDec(
              "u_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "v_19"
              , []
              , []
              , GuardedLChoice(
                  CallT(SVar("u_19"), [], [])
                , Id()
                , One(CallT(SVar("v_19"), [], []))
                )
              )
            ]
          , CallT(SVar("v_19"), [], [])
          )
        )
      , SDefT(
          "main_0_0"
        , []
        , []
        , CallT(
            SVar("oncetd_1_0")
          , [CallT(SVar("desugar_arrow_0_0"), [], [])]
          , []
          )
        )
      , SDefT(
          "Anno__Cong_____2_0"
        , [ VarDec(
              "a_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_19", "x_19", "y_19", "z_19"]
          , Seq(
              Match(Anno(Var("w_19"), Var("x_19")))
            , Seq(
                Build(Var("w_19"))
              , Seq(
                  CallT(SVar("a_20"), [], [])
                , Seq(
                    Match(Var("y_19"))
                  , Seq(
                      Build(Var("x_19"))
                    , Seq(
                        CallT(SVar("b_20"), [], [])
                      , Seq(
                          Match(Var("z_19"))
                        , Build(Anno(Var("y_19"), Var("z_19")))
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
          "Conc_2_0"
        , [ VarDec(
              "c_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_30", "k_30", "l_30", "n_30", "o_30"]
          , Seq(
              Match(
                Anno(
                  Op("Conc", [Var("k_30"), Var("l_30")])
                , Var("m_30")
                )
              )
            , Seq(
                Build(Var("k_30"))
              , Seq(
                  CallT(SVar("c_20"), [], [])
                , Seq(
                    Match(Var("n_30"))
                  , Seq(
                      Build(Var("l_30"))
                    , Seq(
                        CallT(SVar("d_20"), [], [])
                      , Seq(
                          Match(Var("o_30"))
                        , Build(
                            Anno(
                              Op("Conc", [Var("n_30"), Var("o_30")])
                            , Var("m_30")
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
          "Cons_2_0"
        , [ VarDec(
              "e_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_30", "p_30", "q_30", "s_30", "t_30"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("p_30"), Var("q_30")])
                , Var("r_30")
                )
              )
            , Seq(
                Build(Var("p_30"))
              , Seq(
                  CallT(SVar("e_20"), [], [])
                , Seq(
                    Match(Var("s_30"))
                  , Seq(
                      Build(Var("q_30"))
                    , Seq(
                        CallT(SVar("f_20"), [], [])
                      , Seq(
                          Match(Var("t_30"))
                        , Build(
                            Anno(
                              Op("Cons", [Var("s_30"), Var("t_30")])
                            , Var("r_30")
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
          "StmtSeq_2_0"
        , [ VarDec(
              "g_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_30", "u_30", "v_30", "x_30", "y_30"]
          , Seq(
              Match(
                Anno(
                  Op("StmtSeq", [Var("u_30"), Var("v_30")])
                , Var("w_30")
                )
              )
            , Seq(
                Build(Var("u_30"))
              , Seq(
                  CallT(SVar("g_20"), [], [])
                , Seq(
                    Match(Var("x_30"))
                  , Seq(
                      Build(Var("v_30"))
                    , Seq(
                        CallT(SVar("h_20"), [], [])
                      , Seq(
                          Match(Var("y_30"))
                        , Build(
                            Anno(
                              Op("StmtSeq", [Var("x_30"), Var("y_30")])
                            , Var("w_30")
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
          "DeclSeq_2_0"
        , [ VarDec(
              "i_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_31", "z_30", "a_31", "c_31", "d_31"]
          , Seq(
              Match(
                Anno(
                  Op("DeclSeq", [Var("z_30"), Var("a_31")])
                , Var("b_31")
                )
              )
            , Seq(
                Build(Var("z_30"))
              , Seq(
                  CallT(SVar("i_20"), [], [])
                , Seq(
                    Match(Var("c_31"))
                  , Seq(
                      Build(Var("a_31"))
                    , Seq(
                        CallT(SVar("j_20"), [], [])
                      , Seq(
                          Match(Var("d_31"))
                        , Build(
                            Anno(
                              Op("DeclSeq", [Var("c_31"), Var("d_31")])
                            , Var("b_31")
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
          "AltSeq_2_0"
        , [ VarDec(
              "k_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_31", "e_31", "f_31", "h_31", "i_31"]
          , Seq(
              Match(
                Anno(
                  Op("AltSeq", [Var("e_31"), Var("f_31")])
                , Var("g_31")
                )
              )
            , Seq(
                Build(Var("e_31"))
              , Seq(
                  CallT(SVar("k_20"), [], [])
                , Seq(
                    Match(Var("h_31"))
                  , Seq(
                      Build(Var("f_31"))
                    , Seq(
                        CallT(SVar("l_20"), [], [])
                      , Seq(
                          Match(Var("i_31"))
                        , Build(
                            Anno(
                              Op("AltSeq", [Var("h_31"), Var("i_31")])
                            , Var("g_31")
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
          "TopdeclSeq_2_0"
        , [ VarDec(
              "m_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_31", "j_31", "k_31", "m_31", "n_31"]
          , Seq(
              Match(
                Anno(
                  Op("TopdeclSeq", [Var("j_31"), Var("k_31")])
                , Var("l_31")
                )
              )
            , Seq(
                Build(Var("j_31"))
              , Seq(
                  CallT(SVar("m_20"), [], [])
                , Seq(
                    Match(Var("m_31"))
                  , Seq(
                      Build(Var("k_31"))
                    , Seq(
                        CallT(SVar("n_20"), [], [])
                      , Seq(
                          Match(Var("n_31"))
                        , Build(
                            Anno(
                              Op("TopdeclSeq", [Var("m_31"), Var("n_31")])
                            , Var("l_31")
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
          "ImportdeclSeq_2_0"
        , [ VarDec(
              "o_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "p_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_31", "o_31", "p_31", "r_31", "s_31"]
          , Seq(
              Match(
                Anno(
                  Op("ImportdeclSeq", [Var("o_31"), Var("p_31")])
                , Var("q_31")
                )
              )
            , Seq(
                Build(Var("o_31"))
              , Seq(
                  CallT(SVar("o_20"), [], [])
                , Seq(
                    Match(Var("r_31"))
                  , Seq(
                      Build(Var("p_31"))
                    , Seq(
                        CallT(SVar("p_20"), [], [])
                      , Seq(
                          Match(Var("s_31"))
                        , Build(
                            Anno(
                              Op("ImportdeclSeq", [Var("r_31"), Var("s_31")])
                            , Var("q_31")
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
          "FloatHash_1_0"
        , [ VarDec(
              "q_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_31", "t_31", "v_31"]
          , Seq(
              Match(
                Anno(Op("FloatHash", [Var("t_31")]), Var("u_31"))
              )
            , Seq(
                Build(Var("t_31"))
              , Seq(
                  CallT(SVar("q_20"), [], [])
                , Seq(
                    Match(Var("v_31"))
                  , Build(
                      Anno(Op("FloatHash", [Var("v_31")]), Var("u_31"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "IntegerHash_1_0"
        , [ VarDec(
              "r_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_31", "w_31", "y_31"]
          , Seq(
              Match(
                Anno(Op("IntegerHash", [Var("w_31")]), Var("x_31"))
              )
            , Seq(
                Build(Var("w_31"))
              , Seq(
                  CallT(SVar("r_20"), [], [])
                , Seq(
                    Match(Var("y_31"))
                  , Build(
                      Anno(Op("IntegerHash", [Var("y_31")]), Var("x_31"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "StringHash_1_0"
        , [ VarDec(
              "s_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_32", "z_31", "b_32"]
          , Seq(
              Match(
                Anno(Op("StringHash", [Var("z_31")]), Var("a_32"))
              )
            , Seq(
                Build(Var("z_31"))
              , Seq(
                  CallT(SVar("s_20"), [], [])
                , Seq(
                    Match(Var("b_32"))
                  , Build(
                      Anno(Op("StringHash", [Var("b_32")]), Var("a_32"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "CharHash_1_0"
        , [ VarDec(
              "t_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_32", "c_32", "e_32"]
          , Seq(
              Match(
                Anno(Op("CharHash", [Var("c_32")]), Var("d_32"))
              )
            , Seq(
                Build(Var("c_32"))
              , Seq(
                  CallT(SVar("t_20"), [], [])
                , Seq(
                    Match(Var("e_32"))
                  , Build(
                      Anno(Op("CharHash", [Var("e_32")]), Var("d_32"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "FlexibleContext_1_0"
        , [ VarDec(
              "u_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_32", "f_32", "h_32"]
          , Seq(
              Match(
                Anno(Op("FlexibleContext", [Var("f_32")]), Var("g_32"))
              )
            , Seq(
                Build(Var("f_32"))
              , Seq(
                  CallT(SVar("u_20"), [], [])
                , Seq(
                    Match(Var("h_32"))
                  , Build(
                      Anno(Op("FlexibleContext", [Var("h_32")]), Var("g_32"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "SimpleClass_2_0"
        , [ VarDec(
              "v_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "w_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_32", "i_32", "j_32", "l_32", "m_32"]
          , Seq(
              Match(
                Anno(
                  Op("SimpleClass", [Var("i_32"), Var("j_32")])
                , Var("k_32")
                )
              )
            , Seq(
                Build(Var("i_32"))
              , Seq(
                  CallT(SVar("v_20"), [], [])
                , Seq(
                    Match(Var("l_32"))
                  , Seq(
                      Build(Var("j_32"))
                    , Seq(
                        CallT(SVar("w_20"), [], [])
                      , Seq(
                          Match(Var("m_32"))
                        , Build(
                            Anno(
                              Op("SimpleClass", [Var("l_32"), Var("m_32")])
                            , Var("k_32")
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
          "Class_2_0"
        , [ VarDec(
              "x_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_32", "n_32", "o_32", "q_32", "r_32"]
          , Seq(
              Match(
                Anno(
                  Op("Class", [Var("n_32"), Var("o_32")])
                , Var("p_32")
                )
              )
            , Seq(
                Build(Var("n_32"))
              , Seq(
                  CallT(SVar("x_20"), [], [])
                , Seq(
                    Match(Var("q_32"))
                  , Seq(
                      Build(Var("o_32"))
                    , Seq(
                        CallT(SVar("y_20"), [], [])
                      , Seq(
                          Match(Var("r_32"))
                        , Build(
                            Anno(
                              Op("Class", [Var("q_32"), Var("r_32")])
                            , Var("p_32")
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
          "StmtList_1_0"
        , [ VarDec(
              "z_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_32", "s_32", "u_32"]
          , Seq(
              Match(
                Anno(Op("StmtList", [Var("s_32")]), Var("t_32"))
              )
            , Seq(
                Build(Var("s_32"))
              , Seq(
                  CallT(SVar("z_20"), [], [])
                , Seq(
                    Match(Var("u_32"))
                  , Build(
                      Anno(Op("StmtList", [Var("u_32")]), Var("t_32"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "FBind_2_0"
        , [ VarDec(
              "a_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_32", "v_32", "w_32", "y_32", "z_32"]
          , Seq(
              Match(
                Anno(
                  Op("FBind", [Var("v_32"), Var("w_32")])
                , Var("x_32")
                )
              )
            , Seq(
                Build(Var("v_32"))
              , Seq(
                  CallT(SVar("a_21"), [], [])
                , Seq(
                    Match(Var("y_32"))
                  , Seq(
                      Build(Var("w_32"))
                    , Seq(
                        CallT(SVar("b_21"), [], [])
                      , Seq(
                          Match(Var("z_32"))
                        , Build(
                            Anno(
                              Op("FBind", [Var("y_32"), Var("z_32")])
                            , Var("x_32")
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
          "LetStmt_1_0"
        , [ VarDec(
              "c_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_33", "a_33", "c_33"]
          , Seq(
              Match(
                Anno(Op("LetStmt", [Var("a_33")]), Var("b_33"))
              )
            , Seq(
                Build(Var("a_33"))
              , Seq(
                  CallT(SVar("c_21"), [], [])
                , Seq(
                    Match(Var("c_33"))
                  , Build(
                      Anno(Op("LetStmt", [Var("c_33")]), Var("b_33"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ExpStmt_1_0"
        , [ VarDec(
              "d_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_33", "d_33", "f_33"]
          , Seq(
              Match(
                Anno(Op("ExpStmt", [Var("d_33")]), Var("e_33"))
              )
            , Seq(
                Build(Var("d_33"))
              , Seq(
                  CallT(SVar("d_21"), [], [])
                , Seq(
                    Match(Var("f_33"))
                  , Build(
                      Anno(Op("ExpStmt", [Var("f_33")]), Var("e_33"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "BindStmt_2_0"
        , [ VarDec(
              "e_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_33", "g_33", "h_33", "j_33", "k_33"]
          , Seq(
              Match(
                Anno(
                  Op("BindStmt", [Var("g_33"), Var("h_33")])
                , Var("i_33")
                )
              )
            , Seq(
                Build(Var("g_33"))
              , Seq(
                  CallT(SVar("e_21"), [], [])
                , Seq(
                    Match(Var("j_33"))
                  , Seq(
                      Build(Var("h_33"))
                    , Seq(
                        CallT(SVar("f_21"), [], [])
                      , Seq(
                          Match(Var("k_33"))
                        , Build(
                            Anno(
                              Op("BindStmt", [Var("j_33"), Var("k_33")])
                            , Var("i_33")
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
          "ListCompr_2_0"
        , [ VarDec(
              "g_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_33", "l_33", "m_33", "o_33", "p_33"]
          , Seq(
              Match(
                Anno(
                  Op("ListCompr", [Var("l_33"), Var("m_33")])
                , Var("n_33")
                )
              )
            , Seq(
                Build(Var("l_33"))
              , Seq(
                  CallT(SVar("g_21"), [], [])
                , Seq(
                    Match(Var("o_33"))
                  , Seq(
                      Build(Var("m_33"))
                    , Seq(
                        CallT(SVar("h_21"), [], [])
                      , Seq(
                          Match(Var("p_33"))
                        , Build(
                            Anno(
                              Op("ListCompr", [Var("o_33"), Var("p_33")])
                            , Var("n_33")
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
          "ListFirstFromTo_3_0"
        , [ VarDec(
              "i_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_33", "q_33", "r_33", "s_33", "u_33", "v_33", "w_33"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ListFirstFromTo"
                  , [Var("q_33"), Var("r_33"), Var("s_33")]
                  )
                , Var("t_33")
                )
              )
            , Seq(
                Build(Var("q_33"))
              , Seq(
                  CallT(SVar("i_21"), [], [])
                , Seq(
                    Match(Var("u_33"))
                  , Seq(
                      Build(Var("r_33"))
                    , Seq(
                        CallT(SVar("j_21"), [], [])
                      , Seq(
                          Match(Var("v_33"))
                        , Seq(
                            Build(Var("s_33"))
                          , Seq(
                              CallT(SVar("k_21"), [], [])
                            , Seq(
                                Match(Var("w_33"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ListFirstFromTo"
                                    , [Var("u_33"), Var("v_33"), Var("w_33")]
                                    )
                                  , Var("t_33")
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
          "ListFromTo_2_0"
        , [ VarDec(
              "l_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "m_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_33", "x_33", "y_33", "a_34", "b_34"]
          , Seq(
              Match(
                Anno(
                  Op("ListFromTo", [Var("x_33"), Var("y_33")])
                , Var("z_33")
                )
              )
            , Seq(
                Build(Var("x_33"))
              , Seq(
                  CallT(SVar("l_21"), [], [])
                , Seq(
                    Match(Var("a_34"))
                  , Seq(
                      Build(Var("y_33"))
                    , Seq(
                        CallT(SVar("m_21"), [], [])
                      , Seq(
                          Match(Var("b_34"))
                        , Build(
                            Anno(
                              Op("ListFromTo", [Var("a_34"), Var("b_34")])
                            , Var("z_33")
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
          "ListFirstFrom_2_0"
        , [ VarDec(
              "n_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_34", "c_34", "d_34", "f_34", "g_34"]
          , Seq(
              Match(
                Anno(
                  Op("ListFirstFrom", [Var("c_34"), Var("d_34")])
                , Var("e_34")
                )
              )
            , Seq(
                Build(Var("c_34"))
              , Seq(
                  CallT(SVar("n_21"), [], [])
                , Seq(
                    Match(Var("f_34"))
                  , Seq(
                      Build(Var("d_34"))
                    , Seq(
                        CallT(SVar("o_21"), [], [])
                      , Seq(
                          Match(Var("g_34"))
                        , Build(
                            Anno(
                              Op("ListFirstFrom", [Var("f_34"), Var("g_34")])
                            , Var("e_34")
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
          "ListFrom_1_0"
        , [ VarDec(
              "p_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_34", "h_34", "j_34"]
          , Seq(
              Match(
                Anno(Op("ListFrom", [Var("h_34")]), Var("i_34"))
              )
            , Seq(
                Build(Var("h_34"))
              , Seq(
                  CallT(SVar("p_21"), [], [])
                , Seq(
                    Match(Var("j_34"))
                  , Build(
                      Anno(Op("ListFrom", [Var("j_34")]), Var("i_34"))
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
              "q_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_34", "k_34", "m_34"]
          , Seq(
              Match(
                Anno(Op("List", [Var("k_34")]), Var("l_34"))
              )
            , Seq(
                Build(Var("k_34"))
              , Seq(
                  CallT(SVar("q_21"), [], [])
                , Seq(
                    Match(Var("m_34"))
                  , Build(
                      Anno(Op("List", [Var("m_34")]), Var("l_34"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "QualLet_1_0"
        , [ VarDec(
              "r_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_34", "n_34", "p_34"]
          , Seq(
              Match(
                Anno(Op("QualLet", [Var("n_34")]), Var("o_34"))
              )
            , Seq(
                Build(Var("n_34"))
              , Seq(
                  CallT(SVar("r_21"), [], [])
                , Seq(
                    Match(Var("p_34"))
                  , Build(
                      Anno(Op("QualLet", [Var("p_34")]), Var("o_34"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "QualBind_2_0"
        , [ VarDec(
              "s_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_34", "q_34", "r_34", "t_34", "u_34"]
          , Seq(
              Match(
                Anno(
                  Op("QualBind", [Var("q_34"), Var("r_34")])
                , Var("s_34")
                )
              )
            , Seq(
                Build(Var("q_34"))
              , Seq(
                  CallT(SVar("s_21"), [], [])
                , Seq(
                    Match(Var("t_34"))
                  , Seq(
                      Build(Var("r_34"))
                    , Seq(
                        CallT(SVar("t_21"), [], [])
                      , Seq(
                          Match(Var("u_34"))
                        , Build(
                            Anno(
                              Op("QualBind", [Var("t_34"), Var("u_34")])
                            , Var("s_34")
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
          "PatBind_2_0"
        , [ VarDec(
              "u_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_34", "v_34", "w_34", "y_34", "z_34"]
          , Seq(
              Match(
                Anno(
                  Op("PatBind", [Var("v_34"), Var("w_34")])
                , Var("x_34")
                )
              )
            , Seq(
                Build(Var("v_34"))
              , Seq(
                  CallT(SVar("u_21"), [], [])
                , Seq(
                    Match(Var("y_34"))
                  , Seq(
                      Build(Var("w_34"))
                    , Seq(
                        CallT(SVar("v_21"), [], [])
                      , Seq(
                          Match(Var("z_34"))
                        , Build(
                            Anno(
                              Op("PatBind", [Var("y_34"), Var("z_34")])
                            , Var("x_34")
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
          "LabeledPats_1_0"
        , [ VarDec(
              "w_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_35", "a_35", "c_35"]
          , Seq(
              Match(
                Anno(Op("LabeledPats", [Var("a_35")]), Var("b_35"))
              )
            , Seq(
                Build(Var("a_35"))
              , Seq(
                  CallT(SVar("w_21"), [], [])
                , Seq(
                    Match(Var("c_35"))
                  , Build(
                      Anno(Op("LabeledPats", [Var("c_35")]), Var("b_35"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Irrefutable_1_0"
        , [ VarDec(
              "x_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_35", "d_35", "f_35"]
          , Seq(
              Match(
                Anno(Op("Irrefutable", [Var("d_35")]), Var("e_35"))
              )
            , Seq(
                Build(Var("d_35"))
              , Seq(
                  CallT(SVar("x_21"), [], [])
                , Seq(
                    Match(Var("f_35"))
                  , Build(
                      Anno(Op("Irrefutable", [Var("f_35")]), Var("e_35"))
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
              "y_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "z_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_35", "g_35", "h_35", "j_35", "k_35"]
          , Seq(
              Match(
                Anno(
                  Op("Tuple", [Var("g_35"), Var("h_35")])
                , Var("i_35")
                )
              )
            , Seq(
                Build(Var("g_35"))
              , Seq(
                  CallT(SVar("y_21"), [], [])
                , Seq(
                    Match(Var("j_35"))
                  , Seq(
                      Build(Var("h_35"))
                    , Seq(
                        CallT(SVar("z_21"), [], [])
                      , Seq(
                          Match(Var("k_35"))
                        , Build(
                            Anno(
                              Op("Tuple", [Var("j_35"), Var("k_35")])
                            , Var("i_35")
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
          "Labeled_2_0"
        , [ VarDec(
              "a_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_35", "l_35", "m_35", "o_35", "p_35"]
          , Seq(
              Match(
                Anno(
                  Op("Labeled", [Var("l_35"), Var("m_35")])
                , Var("n_35")
                )
              )
            , Seq(
                Build(Var("l_35"))
              , Seq(
                  CallT(SVar("a_22"), [], [])
                , Seq(
                    Match(Var("o_35"))
                  , Seq(
                      Build(Var("m_35"))
                    , Seq(
                        CallT(SVar("b_22"), [], [])
                      , Seq(
                          Match(Var("p_35"))
                        , Build(
                            Anno(
                              Op("Labeled", [Var("o_35"), Var("p_35")])
                            , Var("n_35")
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
          "Constr_1_0"
        , [ VarDec(
              "c_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_35", "q_35", "s_35"]
          , Seq(
              Match(
                Anno(Op("Constr", [Var("q_35")]), Var("r_35"))
              )
            , Seq(
                Build(Var("q_35"))
              , Seq(
                  CallT(SVar("c_22"), [], [])
                , Seq(
                    Match(Var("s_35"))
                  , Build(
                      Anno(Op("Constr", [Var("s_35")]), Var("r_35"))
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
              "d_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_35", "t_35", "u_35", "w_35", "x_35"]
          , Seq(
              Match(
                Anno(
                  Op("Named", [Var("t_35"), Var("u_35")])
                , Var("v_35")
                )
              )
            , Seq(
                Build(Var("t_35"))
              , Seq(
                  CallT(SVar("d_22"), [], [])
                , Seq(
                    Match(Var("w_35"))
                  , Seq(
                      Build(Var("u_35"))
                    , Seq(
                        CallT(SVar("e_22"), [], [])
                      , Seq(
                          Match(Var("x_35"))
                        , Build(
                            Anno(
                              Op("Named", [Var("w_35"), Var("x_35")])
                            , Var("v_35")
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
          "ConstrApp_2_0"
        , [ VarDec(
              "f_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_36", "y_35", "z_35", "b_36", "c_36"]
          , Seq(
              Match(
                Anno(
                  Op("ConstrApp", [Var("y_35"), Var("z_35")])
                , Var("a_36")
                )
              )
            , Seq(
                Build(Var("y_35"))
              , Seq(
                  CallT(SVar("f_22"), [], [])
                , Seq(
                    Match(Var("b_36"))
                  , Seq(
                      Build(Var("z_35"))
                    , Seq(
                        CallT(SVar("g_22"), [], [])
                      , Seq(
                          Match(Var("c_36"))
                        , Build(
                            Anno(
                              Op("ConstrApp", [Var("b_36"), Var("c_36")])
                            , Var("a_36")
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
              "h_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_36", "d_36", "f_36"]
          , Seq(
              Match(
                Anno(Op("Negation", [Var("d_36")]), Var("e_36"))
              )
            , Seq(
                Build(Var("d_36"))
              , Seq(
                  CallT(SVar("h_22"), [], [])
                , Seq(
                    Match(Var("f_36"))
                  , Build(
                      Anno(Op("Negation", [Var("f_36")]), Var("e_36"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "BinOpApp_3_0"
        , [ VarDec(
              "i_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_36", "g_36", "h_36", "i_36", "k_36", "l_36", "m_36"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "BinOpApp"
                  , [Var("g_36"), Var("h_36"), Var("i_36")]
                  )
                , Var("j_36")
                )
              )
            , Seq(
                Build(Var("g_36"))
              , Seq(
                  CallT(SVar("i_22"), [], [])
                , Seq(
                    Match(Var("k_36"))
                  , Seq(
                      Build(Var("h_36"))
                    , Seq(
                        CallT(SVar("j_22"), [], [])
                      , Seq(
                          Match(Var("l_36"))
                        , Seq(
                            Build(Var("i_36"))
                          , Seq(
                              CallT(SVar("k_22"), [], [])
                            , Seq(
                                Match(Var("m_36"))
                              , Build(
                                  Anno(
                                    Op(
                                      "BinOpApp"
                                    , [Var("k_36"), Var("l_36"), Var("m_36")]
                                    )
                                  , Var("j_36")
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
          "DeclList_1_0"
        , [ VarDec(
              "l_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_36", "n_36", "p_36"]
          , Seq(
              Match(
                Anno(Op("DeclList", [Var("n_36")]), Var("o_36"))
              )
            , Seq(
                Build(Var("n_36"))
              , Seq(
                  CallT(SVar("l_22"), [], [])
                , Seq(
                    Match(Var("p_36"))
                  , Build(
                      Anno(Op("DeclList", [Var("p_36")]), Var("o_36"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Where_1_0"
        , [ VarDec(
              "m_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_36", "q_36", "s_36"]
          , Seq(
              Match(
                Anno(Op("Where", [Var("q_36")]), Var("r_36"))
              )
            , Seq(
                Build(Var("q_36"))
              , Seq(
                  CallT(SVar("m_22"), [], [])
                , Seq(
                    Match(Var("s_36"))
                  , Build(
                      Anno(Op("Where", [Var("s_36")]), Var("r_36"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "NestedFunLHS_2_0"
        , [ VarDec(
              "n_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_36", "t_36", "u_36", "w_36", "x_36"]
          , Seq(
              Match(
                Anno(
                  Op("NestedFunLHS", [Var("t_36"), Var("u_36")])
                , Var("v_36")
                )
              )
            , Seq(
                Build(Var("t_36"))
              , Seq(
                  CallT(SVar("n_22"), [], [])
                , Seq(
                    Match(Var("w_36"))
                  , Seq(
                      Build(Var("u_36"))
                    , Seq(
                        CallT(SVar("o_22"), [], [])
                      , Seq(
                          Match(Var("x_36"))
                        , Build(
                            Anno(
                              Op("NestedFunLHS", [Var("w_36"), Var("x_36")])
                            , Var("v_36")
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
          "OpFunLHS_3_0"
        , [ VarDec(
              "p_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "r_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_37", "y_36", "z_36", "a_37", "c_37", "d_37", "e_37"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "OpFunLHS"
                  , [Var("y_36"), Var("z_36"), Var("a_37")]
                  )
                , Var("b_37")
                )
              )
            , Seq(
                Build(Var("y_36"))
              , Seq(
                  CallT(SVar("p_22"), [], [])
                , Seq(
                    Match(Var("c_37"))
                  , Seq(
                      Build(Var("z_36"))
                    , Seq(
                        CallT(SVar("q_22"), [], [])
                      , Seq(
                          Match(Var("d_37"))
                        , Seq(
                            Build(Var("a_37"))
                          , Seq(
                              CallT(SVar("r_22"), [], [])
                            , Seq(
                                Match(Var("e_37"))
                              , Build(
                                  Anno(
                                    Op(
                                      "OpFunLHS"
                                    , [Var("c_37"), Var("d_37"), Var("e_37")]
                                    )
                                  , Var("b_37")
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
          "VarFunLHS_2_0"
        , [ VarDec(
              "s_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_37", "f_37", "g_37", "i_37", "j_37"]
          , Seq(
              Match(
                Anno(
                  Op("VarFunLHS", [Var("f_37"), Var("g_37")])
                , Var("h_37")
                )
              )
            , Seq(
                Build(Var("f_37"))
              , Seq(
                  CallT(SVar("s_22"), [], [])
                , Seq(
                    Match(Var("i_37"))
                  , Seq(
                      Build(Var("g_37"))
                    , Seq(
                        CallT(SVar("t_22"), [], [])
                      , Seq(
                          Match(Var("j_37"))
                        , Build(
                            Anno(
                              Op("VarFunLHS", [Var("i_37"), Var("j_37")])
                            , Var("h_37")
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
          "Guarded_2_0"
        , [ VarDec(
              "u_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_37", "k_37", "l_37", "n_37", "o_37"]
          , Seq(
              Match(
                Anno(
                  Op("Guarded", [Var("k_37"), Var("l_37")])
                , Var("m_37")
                )
              )
            , Seq(
                Build(Var("k_37"))
              , Seq(
                  CallT(SVar("u_22"), [], [])
                , Seq(
                    Match(Var("n_37"))
                  , Seq(
                      Build(Var("l_37"))
                    , Seq(
                        CallT(SVar("v_22"), [], [])
                      , Seq(
                          Match(Var("o_37"))
                        , Build(
                            Anno(
                              Op("Guarded", [Var("n_37"), Var("o_37")])
                            , Var("m_37")
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
          "GdValdef_3_0"
        , [ VarDec(
              "w_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_37", "p_37", "q_37", "r_37", "t_37", "u_37", "v_37"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "GdValdef"
                  , [Var("p_37"), Var("q_37"), Var("r_37")]
                  )
                , Var("s_37")
                )
              )
            , Seq(
                Build(Var("p_37"))
              , Seq(
                  CallT(SVar("w_22"), [], [])
                , Seq(
                    Match(Var("t_37"))
                  , Seq(
                      Build(Var("q_37"))
                    , Seq(
                        CallT(SVar("x_22"), [], [])
                      , Seq(
                          Match(Var("u_37"))
                        , Seq(
                            Build(Var("r_37"))
                          , Seq(
                              CallT(SVar("y_22"), [], [])
                            , Seq(
                                Match(Var("v_37"))
                              , Build(
                                  Anno(
                                    Op(
                                      "GdValdef"
                                    , [Var("t_37"), Var("u_37"), Var("v_37")]
                                    )
                                  , Var("s_37")
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
          "Valdef_3_0"
        , [ VarDec(
              "z_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_37", "w_37", "x_37", "y_37", "a_38", "b_38", "c_38"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Valdef"
                  , [Var("w_37"), Var("x_37"), Var("y_37")]
                  )
                , Var("z_37")
                )
              )
            , Seq(
                Build(Var("w_37"))
              , Seq(
                  CallT(SVar("z_22"), [], [])
                , Seq(
                    Match(Var("a_38"))
                  , Seq(
                      Build(Var("x_37"))
                    , Seq(
                        CallT(SVar("a_23"), [], [])
                      , Seq(
                          Match(Var("b_38"))
                        , Seq(
                            Build(Var("y_37"))
                          , Seq(
                              CallT(SVar("b_23"), [], [])
                            , Seq(
                                Match(Var("c_38"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Valdef"
                                    , [Var("a_38"), Var("b_38"), Var("c_38")]
                                    )
                                  , Var("z_37")
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
          "AltList_1_0"
        , [ VarDec(
              "c_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_38", "d_38", "f_38"]
          , Seq(
              Match(
                Anno(Op("AltList", [Var("d_38")]), Var("e_38"))
              )
            , Seq(
                Build(Var("d_38"))
              , Seq(
                  CallT(SVar("c_23"), [], [])
                , Seq(
                    Match(Var("f_38"))
                  , Build(
                      Anno(Op("AltList", [Var("f_38")]), Var("e_38"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "GdPat_2_0"
        , [ VarDec(
              "d_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_38", "g_38", "h_38", "j_38", "k_38"]
          , Seq(
              Match(
                Anno(
                  Op("GdPat", [Var("g_38"), Var("h_38")])
                , Var("i_38")
                )
              )
            , Seq(
                Build(Var("g_38"))
              , Seq(
                  CallT(SVar("d_23"), [], [])
                , Seq(
                    Match(Var("j_38"))
                  , Seq(
                      Build(Var("h_38"))
                    , Seq(
                        CallT(SVar("e_23"), [], [])
                      , Seq(
                          Match(Var("k_38"))
                        , Build(
                            Anno(
                              Op("GdPat", [Var("j_38"), Var("k_38")])
                            , Var("i_38")
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
          "GdAlt_3_0"
        , [ VarDec(
              "f_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_38", "l_38", "m_38", "n_38", "p_38", "q_38", "r_38"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "GdAlt"
                  , [Var("l_38"), Var("m_38"), Var("n_38")]
                  )
                , Var("o_38")
                )
              )
            , Seq(
                Build(Var("l_38"))
              , Seq(
                  CallT(SVar("f_23"), [], [])
                , Seq(
                    Match(Var("p_38"))
                  , Seq(
                      Build(Var("m_38"))
                    , Seq(
                        CallT(SVar("g_23"), [], [])
                      , Seq(
                          Match(Var("q_38"))
                        , Seq(
                            Build(Var("n_38"))
                          , Seq(
                              CallT(SVar("h_23"), [], [])
                            , Seq(
                                Match(Var("r_38"))
                              , Build(
                                  Anno(
                                    Op(
                                      "GdAlt"
                                    , [Var("p_38"), Var("q_38"), Var("r_38")]
                                    )
                                  , Var("o_38")
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
          "Alt_3_0"
        , [ VarDec(
              "i_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_38", "s_38", "t_38", "u_38", "w_38", "x_38", "y_38"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Alt"
                  , [Var("s_38"), Var("t_38"), Var("u_38")]
                  )
                , Var("v_38")
                )
              )
            , Seq(
                Build(Var("s_38"))
              , Seq(
                  CallT(SVar("i_23"), [], [])
                , Seq(
                    Match(Var("w_38"))
                  , Seq(
                      Build(Var("t_38"))
                    , Seq(
                        CallT(SVar("j_23"), [], [])
                      , Seq(
                          Match(Var("x_38"))
                        , Seq(
                            Build(Var("u_38"))
                          , Seq(
                              CallT(SVar("k_23"), [], [])
                            , Seq(
                                Match(Var("y_38"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Alt"
                                    , [Var("w_38"), Var("x_38"), Var("y_38")]
                                    )
                                  , Var("v_38")
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
          "LabelBinds_1_0"
        , [ VarDec(
              "l_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_39", "z_38", "b_39"]
          , Seq(
              Match(
                Anno(Op("LabelBinds", [Var("z_38")]), Var("a_39"))
              )
            , Seq(
                Build(Var("z_38"))
              , Seq(
                  CallT(SVar("l_23"), [], [])
                , Seq(
                    Match(Var("b_39"))
                  , Build(
                      Anno(Op("LabelBinds", [Var("b_39")]), Var("a_39"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "FixDecl_3_0"
        , [ VarDec(
              "m_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_39", "c_39", "d_39", "e_39", "g_39", "h_39", "i_39"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "FixDecl"
                  , [Var("c_39"), Var("d_39"), Var("e_39")]
                  )
                , Var("f_39")
                )
              )
            , Seq(
                Build(Var("c_39"))
              , Seq(
                  CallT(SVar("m_23"), [], [])
                , Seq(
                    Match(Var("g_39"))
                  , Seq(
                      Build(Var("d_39"))
                    , Seq(
                        CallT(SVar("n_23"), [], [])
                      , Seq(
                          Match(Var("h_39"))
                        , Seq(
                            Build(Var("e_39"))
                          , Seq(
                              CallT(SVar("o_23"), [], [])
                            , Seq(
                                Match(Var("i_39"))
                              , Build(
                                  Anno(
                                    Op(
                                      "FixDecl"
                                    , [Var("g_39"), Var("h_39"), Var("i_39")]
                                    )
                                  , Var("f_39")
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
          "InfixR_0_0"
        , []
        , []
        , Match(Anno(Op("InfixR", []), Wld()))
        )
      , SDefT(
          "InfixL_0_0"
        , []
        , []
        , Match(Anno(Op("InfixL", []), Wld()))
        )
      , SDefT(
          "Infix_0_0"
        , []
        , []
        , Match(Anno(Op("Infix", []), Wld()))
        )
      , SDefT(
          "ECons_2_0"
        , [ VarDec(
              "p_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_39", "j_39", "k_39", "m_39", "n_39"]
          , Seq(
              Match(
                Anno(
                  Op("ECons", [Var("j_39"), Var("k_39")])
                , Var("l_39")
                )
              )
            , Seq(
                Build(Var("j_39"))
              , Seq(
                  CallT(SVar("p_23"), [], [])
                , Seq(
                    Match(Var("m_39"))
                  , Seq(
                      Build(Var("k_39"))
                    , Seq(
                        CallT(SVar("q_23"), [], [])
                      , Seq(
                          Match(Var("n_39"))
                        , Build(
                            Anno(
                              Op("ECons", [Var("m_39"), Var("n_39")])
                            , Var("l_39")
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
          "ArrOpApp_3_0"
        , [ VarDec(
              "r_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_39", "o_39", "p_39", "q_39", "s_39", "t_39", "u_39"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ArrOpApp"
                  , [Var("o_39"), Var("p_39"), Var("q_39")]
                  )
                , Var("r_39")
                )
              )
            , Seq(
                Build(Var("o_39"))
              , Seq(
                  CallT(SVar("r_23"), [], [])
                , Seq(
                    Match(Var("s_39"))
                  , Seq(
                      Build(Var("p_39"))
                    , Seq(
                        CallT(SVar("s_23"), [], [])
                      , Seq(
                          Match(Var("t_39"))
                        , Seq(
                            Build(Var("q_39"))
                          , Seq(
                              CallT(SVar("t_23"), [], [])
                            , Seq(
                                Match(Var("u_39"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ArrOpApp"
                                    , [Var("s_39"), Var("t_39"), Var("u_39")]
                                    )
                                  , Var("r_39")
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
          "ArrForm_2_0"
        , [ VarDec(
              "u_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_39", "v_39", "w_39", "y_39", "z_39"]
          , Seq(
              Match(
                Anno(
                  Op("ArrForm", [Var("v_39"), Var("w_39")])
                , Var("x_39")
                )
              )
            , Seq(
                Build(Var("v_39"))
              , Seq(
                  CallT(SVar("u_23"), [], [])
                , Seq(
                    Match(Var("y_39"))
                  , Seq(
                      Build(Var("w_39"))
                    , Seq(
                        CallT(SVar("v_23"), [], [])
                      , Seq(
                          Match(Var("z_39"))
                        , Build(
                            Anno(
                              Op("ArrForm", [Var("y_39"), Var("z_39")])
                            , Var("x_39")
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
          "ArrAppBin_2_0"
        , [ VarDec(
              "w_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_40", "a_40", "b_40", "d_40", "e_40"]
          , Seq(
              Match(
                Anno(
                  Op("ArrAppBin", [Var("a_40"), Var("b_40")])
                , Var("c_40")
                )
              )
            , Seq(
                Build(Var("a_40"))
              , Seq(
                  CallT(SVar("w_23"), [], [])
                , Seq(
                    Match(Var("d_40"))
                  , Seq(
                      Build(Var("b_40"))
                    , Seq(
                        CallT(SVar("x_23"), [], [])
                      , Seq(
                          Match(Var("e_40"))
                        , Build(
                            Anno(
                              Op("ArrAppBin", [Var("d_40"), Var("e_40")])
                            , Var("c_40")
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
          "ArrDo_1_0"
        , [ VarDec(
              "y_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_40", "f_40", "h_40"]
          , Seq(
              Match(
                Anno(Op("ArrDo", [Var("f_40")]), Var("g_40"))
              )
            , Seq(
                Build(Var("f_40"))
              , Seq(
                  CallT(SVar("y_23"), [], [])
                , Seq(
                    Match(Var("h_40"))
                  , Build(
                      Anno(Op("ArrDo", [Var("h_40")]), Var("g_40"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ArrCase_2_0"
        , [ VarDec(
              "z_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_40", "i_40", "j_40", "l_40", "m_40"]
          , Seq(
              Match(
                Anno(
                  Op("ArrCase", [Var("i_40"), Var("j_40")])
                , Var("k_40")
                )
              )
            , Seq(
                Build(Var("i_40"))
              , Seq(
                  CallT(SVar("z_23"), [], [])
                , Seq(
                    Match(Var("l_40"))
                  , Seq(
                      Build(Var("j_40"))
                    , Seq(
                        CallT(SVar("a_24"), [], [])
                      , Seq(
                          Match(Var("m_40"))
                        , Build(
                            Anno(
                              Op("ArrCase", [Var("l_40"), Var("m_40")])
                            , Var("k_40")
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
          "ArrIf_3_0"
        , [ VarDec(
              "b_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_40", "n_40", "o_40", "p_40", "r_40", "s_40", "t_40"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ArrIf"
                  , [Var("n_40"), Var("o_40"), Var("p_40")]
                  )
                , Var("q_40")
                )
              )
            , Seq(
                Build(Var("n_40"))
              , Seq(
                  CallT(SVar("b_24"), [], [])
                , Seq(
                    Match(Var("r_40"))
                  , Seq(
                      Build(Var("o_40"))
                    , Seq(
                        CallT(SVar("c_24"), [], [])
                      , Seq(
                          Match(Var("s_40"))
                        , Seq(
                            Build(Var("p_40"))
                          , Seq(
                              CallT(SVar("d_24"), [], [])
                            , Seq(
                                Match(Var("t_40"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ArrIf"
                                    , [Var("r_40"), Var("s_40"), Var("t_40")]
                                    )
                                  , Var("q_40")
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
          "ArrLet_2_0"
        , [ VarDec(
              "e_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_40", "u_40", "v_40", "x_40", "y_40"]
          , Seq(
              Match(
                Anno(
                  Op("ArrLet", [Var("u_40"), Var("v_40")])
                , Var("w_40")
                )
              )
            , Seq(
                Build(Var("u_40"))
              , Seq(
                  CallT(SVar("e_24"), [], [])
                , Seq(
                    Match(Var("x_40"))
                  , Seq(
                      Build(Var("v_40"))
                    , Seq(
                        CallT(SVar("f_24"), [], [])
                      , Seq(
                          Match(Var("y_40"))
                        , Build(
                            Anno(
                              Op("ArrLet", [Var("x_40"), Var("y_40")])
                            , Var("w_40")
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
          "ArrAbs_2_0"
        , [ VarDec(
              "g_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_41", "z_40", "a_41", "c_41", "d_41"]
          , Seq(
              Match(
                Anno(
                  Op("ArrAbs", [Var("z_40"), Var("a_41")])
                , Var("b_41")
                )
              )
            , Seq(
                Build(Var("z_40"))
              , Seq(
                  CallT(SVar("g_24"), [], [])
                , Seq(
                    Match(Var("c_41"))
                  , Seq(
                      Build(Var("a_41"))
                    , Seq(
                        CallT(SVar("h_24"), [], [])
                      , Seq(
                          Match(Var("d_41"))
                        , Build(
                            Anno(
                              Op("ArrAbs", [Var("c_41"), Var("d_41")])
                            , Var("b_41")
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
          "ArrHigher_2_0"
        , [ VarDec(
              "i_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_41", "e_41", "f_41", "h_41", "i_41"]
          , Seq(
              Match(
                Anno(
                  Op("ArrHigher", [Var("e_41"), Var("f_41")])
                , Var("g_41")
                )
              )
            , Seq(
                Build(Var("e_41"))
              , Seq(
                  CallT(SVar("i_24"), [], [])
                , Seq(
                    Match(Var("h_41"))
                  , Seq(
                      Build(Var("f_41"))
                    , Seq(
                        CallT(SVar("j_24"), [], [])
                      , Seq(
                          Match(Var("i_41"))
                        , Build(
                            Anno(
                              Op("ArrHigher", [Var("h_41"), Var("i_41")])
                            , Var("g_41")
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
          "ArrFirst_2_0"
        , [ VarDec(
              "k_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_41", "j_41", "k_41", "m_41", "n_41"]
          , Seq(
              Match(
                Anno(
                  Op("ArrFirst", [Var("j_41"), Var("k_41")])
                , Var("l_41")
                )
              )
            , Seq(
                Build(Var("j_41"))
              , Seq(
                  CallT(SVar("k_24"), [], [])
                , Seq(
                    Match(Var("m_41"))
                  , Seq(
                      Build(Var("k_41"))
                    , Seq(
                        CallT(SVar("l_24"), [], [])
                      , Seq(
                          Match(Var("n_41"))
                        , Build(
                            Anno(
                              Op("ArrFirst", [Var("m_41"), Var("n_41")])
                            , Var("l_41")
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
              "m_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_41", "o_41", "p_41", "q_41", "s_41", "t_41", "u_41"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Typed"
                  , [Var("o_41"), Var("p_41"), Var("q_41")]
                  )
                , Var("r_41")
                )
              )
            , Seq(
                Build(Var("o_41"))
              , Seq(
                  CallT(SVar("m_24"), [], [])
                , Seq(
                    Match(Var("s_41"))
                  , Seq(
                      Build(Var("p_41"))
                    , Seq(
                        CallT(SVar("n_24"), [], [])
                      , Seq(
                          Match(Var("t_41"))
                        , Seq(
                            Build(Var("q_41"))
                          , Seq(
                              CallT(SVar("o_24"), [], [])
                            , Seq(
                                Match(Var("u_41"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Typed"
                                    , [Var("s_41"), Var("t_41"), Var("u_41")]
                                    )
                                  , Var("r_41")
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
          "OpApp_3_0"
        , [ VarDec(
              "p_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "r_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_41", "v_41", "w_41", "x_41", "z_41", "a_42", "b_42"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "OpApp"
                  , [Var("v_41"), Var("w_41"), Var("x_41")]
                  )
                , Var("y_41")
                )
              )
            , Seq(
                Build(Var("v_41"))
              , Seq(
                  CallT(SVar("p_24"), [], [])
                , Seq(
                    Match(Var("z_41"))
                  , Seq(
                      Build(Var("w_41"))
                    , Seq(
                        CallT(SVar("q_24"), [], [])
                      , Seq(
                          Match(Var("a_42"))
                        , Seq(
                            Build(Var("x_41"))
                          , Seq(
                              CallT(SVar("r_24"), [], [])
                            , Seq(
                                Match(Var("b_42"))
                              , Build(
                                  Anno(
                                    Op(
                                      "OpApp"
                                    , [Var("z_41"), Var("a_42"), Var("b_42")]
                                    )
                                  , Var("y_41")
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
          "AppBin_2_0"
        , [ VarDec(
              "s_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_42", "c_42", "d_42", "f_42", "g_42"]
          , Seq(
              Match(
                Anno(
                  Op("AppBin", [Var("c_42"), Var("d_42")])
                , Var("e_42")
                )
              )
            , Seq(
                Build(Var("c_42"))
              , Seq(
                  CallT(SVar("s_24"), [], [])
                , Seq(
                    Match(Var("f_42"))
                  , Seq(
                      Build(Var("d_42"))
                    , Seq(
                        CallT(SVar("t_24"), [], [])
                      , Seq(
                          Match(Var("g_42"))
                        , Build(
                            Anno(
                              Op("AppBin", [Var("f_42"), Var("g_42")])
                            , Var("e_42")
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
              "u_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_42", "h_42", "i_42", "k_42", "l_42"]
          , Seq(
              Match(
                Anno(
                  Op("Case", [Var("h_42"), Var("i_42")])
                , Var("j_42")
                )
              )
            , Seq(
                Build(Var("h_42"))
              , Seq(
                  CallT(SVar("u_24"), [], [])
                , Seq(
                    Match(Var("k_42"))
                  , Seq(
                      Build(Var("i_42"))
                    , Seq(
                        CallT(SVar("v_24"), [], [])
                      , Seq(
                          Match(Var("l_42"))
                        , Build(
                            Anno(
                              Op("Case", [Var("k_42"), Var("l_42")])
                            , Var("j_42")
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
              "w_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_42", "m_42", "o_42"]
          , Seq(
              Match(
                Anno(Op("Do", [Var("m_42")]), Var("n_42"))
              )
            , Seq(
                Build(Var("m_42"))
              , Seq(
                  CallT(SVar("w_24"), [], [])
                , Seq(
                    Match(Var("o_42"))
                  , Build(
                      Anno(Op("Do", [Var("o_42")]), Var("n_42"))
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
              "x_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "z_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_42", "p_42", "q_42", "r_42", "t_42", "u_42", "v_42"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "If"
                  , [Var("p_42"), Var("q_42"), Var("r_42")]
                  )
                , Var("s_42")
                )
              )
            , Seq(
                Build(Var("p_42"))
              , Seq(
                  CallT(SVar("x_24"), [], [])
                , Seq(
                    Match(Var("t_42"))
                  , Seq(
                      Build(Var("q_42"))
                    , Seq(
                        CallT(SVar("y_24"), [], [])
                      , Seq(
                          Match(Var("u_42"))
                        , Seq(
                            Build(Var("r_42"))
                          , Seq(
                              CallT(SVar("z_24"), [], [])
                            , Seq(
                                Match(Var("v_42"))
                              , Build(
                                  Anno(
                                    Op(
                                      "If"
                                    , [Var("t_42"), Var("u_42"), Var("v_42")]
                                    )
                                  , Var("s_42")
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
              "a_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_42", "w_42", "x_42", "z_42", "a_43"]
          , Seq(
              Match(
                Anno(
                  Op("Let", [Var("w_42"), Var("x_42")])
                , Var("y_42")
                )
              )
            , Seq(
                Build(Var("w_42"))
              , Seq(
                  CallT(SVar("a_25"), [], [])
                , Seq(
                    Match(Var("z_42"))
                  , Seq(
                      Build(Var("x_42"))
                    , Seq(
                        CallT(SVar("b_25"), [], [])
                      , Seq(
                          Match(Var("a_43"))
                        , Build(
                            Anno(
                              Op("Let", [Var("z_42"), Var("a_43")])
                            , Var("y_42")
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
              "c_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_43", "b_43", "c_43", "e_43", "f_43"]
          , Seq(
              Match(
                Anno(
                  Op("Abs", [Var("b_43"), Var("c_43")])
                , Var("d_43")
                )
              )
            , Seq(
                Build(Var("b_43"))
              , Seq(
                  CallT(SVar("c_25"), [], [])
                , Seq(
                    Match(Var("e_43"))
                  , Seq(
                      Build(Var("c_43"))
                    , Seq(
                        CallT(SVar("d_25"), [], [])
                      , Seq(
                          Match(Var("f_43"))
                        , Build(
                            Anno(
                              Op("Abs", [Var("e_43"), Var("f_43")])
                            , Var("d_43")
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
              "e_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_43", "g_43", "h_43", "j_43", "k_43"]
          , Seq(
              Match(
                Anno(
                  Op("RSection", [Var("g_43"), Var("h_43")])
                , Var("i_43")
                )
              )
            , Seq(
                Build(Var("g_43"))
              , Seq(
                  CallT(SVar("e_25"), [], [])
                , Seq(
                    Match(Var("j_43"))
                  , Seq(
                      Build(Var("h_43"))
                    , Seq(
                        CallT(SVar("f_25"), [], [])
                      , Seq(
                          Match(Var("k_43"))
                        , Build(
                            Anno(
                              Op("RSection", [Var("j_43"), Var("k_43")])
                            , Var("i_43")
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
              "g_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_43", "l_43", "m_43", "o_43", "p_43"]
          , Seq(
              Match(
                Anno(
                  Op("LSection", [Var("l_43"), Var("m_43")])
                , Var("n_43")
                )
              )
            , Seq(
                Build(Var("l_43"))
              , Seq(
                  CallT(SVar("g_25"), [], [])
                , Seq(
                    Match(Var("o_43"))
                  , Seq(
                      Build(Var("m_43"))
                    , Seq(
                        CallT(SVar("h_25"), [], [])
                      , Seq(
                          Match(Var("p_43"))
                        , Build(
                            Anno(
                              Op("LSection", [Var("o_43"), Var("p_43")])
                            , Var("n_43")
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
              "i_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_43", "q_43", "s_43"]
          , Seq(
              Match(
                Anno(Op("Product", [Var("q_43")]), Var("r_43"))
              )
            , Seq(
                Build(Var("q_43"))
              , Seq(
                  CallT(SVar("i_25"), [], [])
                , Seq(
                    Match(Var("s_43"))
                  , Build(
                      Anno(Op("Product", [Var("s_43")]), Var("r_43"))
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
              "j_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_43", "t_43", "v_43"]
          , Seq(
              Match(
                Anno(Op("Lit", [Var("t_43")]), Var("u_43"))
              )
            , Seq(
                Build(Var("t_43"))
              , Seq(
                  CallT(SVar("j_25"), [], [])
                , Seq(
                    Match(Var("v_43"))
                  , Build(
                      Anno(Op("Lit", [Var("v_43")]), Var("u_43"))
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
              "k_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_43", "w_43", "y_43"]
          , Seq(
              Match(
                Anno(Op("Var", [Var("w_43")]), Var("x_43"))
              )
            , Seq(
                Build(Var("w_43"))
              , Seq(
                  CallT(SVar("k_25"), [], [])
                , Seq(
                    Match(Var("y_43"))
                  , Build(
                      Anno(Op("Var", [Var("y_43")]), Var("x_43"))
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
              "l_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "m_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_44", "z_43", "a_44", "c_44", "d_44"]
          , Seq(
              Match(
                Anno(
                  Op("ArrProcedure", [Var("z_43"), Var("a_44")])
                , Var("b_44")
                )
              )
            , Seq(
                Build(Var("z_43"))
              , Seq(
                  CallT(SVar("l_25"), [], [])
                , Seq(
                    Match(Var("c_44"))
                  , Seq(
                      Build(Var("a_44"))
                    , Seq(
                        CallT(SVar("m_25"), [], [])
                      , Seq(
                          Match(Var("d_44"))
                        , Build(
                            Anno(
                              Op("ArrProcedure", [Var("c_44"), Var("d_44")])
                            , Var("b_44")
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
          "ArrStmtSeq_2_0"
        , [ VarDec(
              "n_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_44", "e_44", "f_44", "h_44", "i_44"]
          , Seq(
              Match(
                Anno(
                  Op("ArrStmtSeq", [Var("e_44"), Var("f_44")])
                , Var("g_44")
                )
              )
            , Seq(
                Build(Var("e_44"))
              , Seq(
                  CallT(SVar("n_25"), [], [])
                , Seq(
                    Match(Var("h_44"))
                  , Seq(
                      Build(Var("f_44"))
                    , Seq(
                        CallT(SVar("o_25"), [], [])
                      , Seq(
                          Match(Var("i_44"))
                        , Build(
                            Anno(
                              Op("ArrStmtSeq", [Var("h_44"), Var("i_44")])
                            , Var("g_44")
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
          "ArrStmtList_1_0"
        , [ VarDec(
              "p_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_44", "j_44", "l_44"]
          , Seq(
              Match(
                Anno(Op("ArrStmtList", [Var("j_44")]), Var("k_44"))
              )
            , Seq(
                Build(Var("j_44"))
              , Seq(
                  CallT(SVar("p_25"), [], [])
                , Seq(
                    Match(Var("l_44"))
                  , Build(
                      Anno(Op("ArrStmtList", [Var("l_44")]), Var("k_44"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ArrCmdStmt_1_0"
        , [ VarDec(
              "q_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_44", "m_44", "o_44"]
          , Seq(
              Match(
                Anno(Op("ArrCmdStmt", [Var("m_44")]), Var("n_44"))
              )
            , Seq(
                Build(Var("m_44"))
              , Seq(
                  CallT(SVar("q_25"), [], [])
                , Seq(
                    Match(Var("o_44"))
                  , Build(
                      Anno(Op("ArrCmdStmt", [Var("o_44")]), Var("n_44"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ArrBindStmt_2_0"
        , [ VarDec(
              "r_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_44", "p_44", "q_44", "s_44", "t_44"]
          , Seq(
              Match(
                Anno(
                  Op("ArrBindStmt", [Var("p_44"), Var("q_44")])
                , Var("r_44")
                )
              )
            , Seq(
                Build(Var("p_44"))
              , Seq(
                  CallT(SVar("r_25"), [], [])
                , Seq(
                    Match(Var("s_44"))
                  , Seq(
                      Build(Var("q_44"))
                    , Seq(
                        CallT(SVar("s_25"), [], [])
                      , Seq(
                          Match(Var("t_44"))
                        , Build(
                            Anno(
                              Op("ArrBindStmt", [Var("s_44"), Var("t_44")])
                            , Var("r_44")
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
          "ArrLetStmt_1_0"
        , [ VarDec(
              "t_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_44", "u_44", "w_44"]
          , Seq(
              Match(
                Anno(Op("ArrLetStmt", [Var("u_44")]), Var("v_44"))
              )
            , Seq(
                Build(Var("u_44"))
              , Seq(
                  CallT(SVar("t_25"), [], [])
                , Seq(
                    Match(Var("w_44"))
                  , Build(
                      Anno(Op("ArrLetStmt", [Var("w_44")]), Var("v_44"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ArrAltSeq_2_0"
        , [ VarDec(
              "u_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_44", "x_44", "y_44", "a_45", "b_45"]
          , Seq(
              Match(
                Anno(
                  Op("ArrAltSeq", [Var("x_44"), Var("y_44")])
                , Var("z_44")
                )
              )
            , Seq(
                Build(Var("x_44"))
              , Seq(
                  CallT(SVar("u_25"), [], [])
                , Seq(
                    Match(Var("a_45"))
                  , Seq(
                      Build(Var("y_44"))
                    , Seq(
                        CallT(SVar("v_25"), [], [])
                      , Seq(
                          Match(Var("b_45"))
                        , Build(
                            Anno(
                              Op("ArrAltSeq", [Var("a_45"), Var("b_45")])
                            , Var("z_44")
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
          "ArrAlt_3_0"
        , [ VarDec(
              "w_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_45", "c_45", "d_45", "e_45", "g_45", "h_45", "i_45"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ArrAlt"
                  , [Var("c_45"), Var("d_45"), Var("e_45")]
                  )
                , Var("f_45")
                )
              )
            , Seq(
                Build(Var("c_45"))
              , Seq(
                  CallT(SVar("w_25"), [], [])
                , Seq(
                    Match(Var("g_45"))
                  , Seq(
                      Build(Var("d_45"))
                    , Seq(
                        CallT(SVar("x_25"), [], [])
                      , Seq(
                          Match(Var("h_45"))
                        , Seq(
                            Build(Var("e_45"))
                          , Seq(
                              CallT(SVar("y_25"), [], [])
                            , Seq(
                                Match(Var("i_45"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ArrAlt"
                                    , [Var("g_45"), Var("h_45"), Var("i_45")]
                                    )
                                  , Var("f_45")
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
          "SignDecl_3_0"
        , [ VarDec(
              "z_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_45", "j_45", "k_45", "l_45", "n_45", "o_45", "p_45"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "SignDecl"
                  , [Var("j_45"), Var("k_45"), Var("l_45")]
                  )
                , Var("m_45")
                )
              )
            , Seq(
                Build(Var("j_45"))
              , Seq(
                  CallT(SVar("z_25"), [], [])
                , Seq(
                    Match(Var("n_45"))
                  , Seq(
                      Build(Var("k_45"))
                    , Seq(
                        CallT(SVar("a_26"), [], [])
                      , Seq(
                          Match(Var("o_45"))
                        , Seq(
                            Build(Var("l_45"))
                          , Seq(
                              CallT(SVar("b_26"), [], [])
                            , Seq(
                                Match(Var("p_45"))
                              , Build(
                                  Anno(
                                    Op(
                                      "SignDecl"
                                    , [Var("n_45"), Var("o_45"), Var("p_45")]
                                    )
                                  , Var("m_45")
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
          "Class_3_0"
        , [ VarDec(
              "c_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_45", "q_45", "r_45", "s_45", "u_45", "v_45", "w_45"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Class"
                  , [Var("q_45"), Var("r_45"), Var("s_45")]
                  )
                , Var("t_45")
                )
              )
            , Seq(
                Build(Var("q_45"))
              , Seq(
                  CallT(SVar("c_26"), [], [])
                , Seq(
                    Match(Var("u_45"))
                  , Seq(
                      Build(Var("r_45"))
                    , Seq(
                        CallT(SVar("d_26"), [], [])
                      , Seq(
                          Match(Var("v_45"))
                        , Seq(
                            Build(Var("s_45"))
                          , Seq(
                              CallT(SVar("e_26"), [], [])
                            , Seq(
                                Match(Var("w_45"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Class"
                                    , [Var("u_45"), Var("v_45"), Var("w_45")]
                                    )
                                  , Var("t_45")
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
          "SContext_1_0"
        , [ VarDec(
              "f_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_45", "x_45", "z_45"]
          , Seq(
              Match(
                Anno(Op("SContext", [Var("x_45")]), Var("y_45"))
              )
            , Seq(
                Build(Var("x_45"))
              , Seq(
                  CallT(SVar("f_26"), [], [])
                , Seq(
                    Match(Var("z_45"))
                  , Build(
                      Anno(Op("SContext", [Var("z_45")]), Var("y_45"))
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
              "g_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_46", "a_46", "c_46"]
          , Seq(
              Match(
                Anno(Op("Context", [Var("a_46")]), Var("b_46"))
              )
            , Seq(
                Build(Var("a_46"))
              , Seq(
                  CallT(SVar("g_26"), [], [])
                , Seq(
                    Match(Var("c_46"))
                  , Build(
                      Anno(Op("Context", [Var("c_46")]), Var("b_46"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "InstArrow_2_0"
        , [ VarDec(
              "h_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_46", "d_46", "e_46", "g_46", "h_46"]
          , Seq(
              Match(
                Anno(
                  Op("InstArrow", [Var("d_46"), Var("e_46")])
                , Var("f_46")
                )
              )
            , Seq(
                Build(Var("d_46"))
              , Seq(
                  CallT(SVar("h_26"), [], [])
                , Seq(
                    Match(Var("g_46"))
                  , Seq(
                      Build(Var("e_46"))
                    , Seq(
                        CallT(SVar("i_26"), [], [])
                      , Seq(
                          Match(Var("h_46"))
                        , Build(
                            Anno(
                              Op("InstArrow", [Var("g_46"), Var("h_46")])
                            , Var("f_46")
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
          "InstList_1_0"
        , [ VarDec(
              "j_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_46", "i_46", "k_46"]
          , Seq(
              Match(
                Anno(Op("InstList", [Var("i_46")]), Var("j_46"))
              )
            , Seq(
                Build(Var("i_46"))
              , Seq(
                  CallT(SVar("j_26"), [], [])
                , Seq(
                    Match(Var("k_46"))
                  , Build(
                      Anno(Op("InstList", [Var("k_46")]), Var("j_46"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "InstTuple_2_0"
        , [ VarDec(
              "k_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_46", "l_46", "m_46", "o_46", "p_46"]
          , Seq(
              Match(
                Anno(
                  Op("InstTuple", [Var("l_46"), Var("m_46")])
                , Var("n_46")
                )
              )
            , Seq(
                Build(Var("l_46"))
              , Seq(
                  CallT(SVar("k_26"), [], [])
                , Seq(
                    Match(Var("o_46"))
                  , Seq(
                      Build(Var("m_46"))
                    , Seq(
                        CallT(SVar("l_26"), [], [])
                      , Seq(
                          Match(Var("p_46"))
                        , Build(
                            Anno(
                              Op("InstTuple", [Var("o_46"), Var("p_46")])
                            , Var("n_46")
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
          "InstApp_2_0"
        , [ VarDec(
              "m_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_46", "q_46", "r_46", "t_46", "u_46"]
          , Seq(
              Match(
                Anno(
                  Op("InstApp", [Var("q_46"), Var("r_46")])
                , Var("s_46")
                )
              )
            , Seq(
                Build(Var("q_46"))
              , Seq(
                  CallT(SVar("m_26"), [], [])
                , Seq(
                    Match(Var("t_46"))
                  , Seq(
                      Build(Var("r_46"))
                    , Seq(
                        CallT(SVar("n_26"), [], [])
                      , Seq(
                          Match(Var("u_46"))
                        , Build(
                            Anno(
                              Op("InstApp", [Var("t_46"), Var("u_46")])
                            , Var("s_46")
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
          "InstCons_1_0"
        , [ VarDec(
              "o_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_46", "v_46", "x_46"]
          , Seq(
              Match(
                Anno(Op("InstCons", [Var("v_46")]), Var("w_46"))
              )
            , Seq(
                Build(Var("v_46"))
              , Seq(
                  CallT(SVar("o_26"), [], [])
                , Seq(
                    Match(Var("x_46"))
                  , Build(
                      Anno(Op("InstCons", [Var("x_46")]), Var("w_46"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "InfixConstr_3_0"
        , [ VarDec(
              "p_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "r_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_47", "y_46", "z_46", "a_47", "c_47", "d_47", "e_47"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "InfixConstr"
                  , [Var("y_46"), Var("z_46"), Var("a_47")]
                  )
                , Var("b_47")
                )
              )
            , Seq(
                Build(Var("y_46"))
              , Seq(
                  CallT(SVar("p_26"), [], [])
                , Seq(
                    Match(Var("c_47"))
                  , Seq(
                      Build(Var("z_46"))
                    , Seq(
                        CallT(SVar("q_26"), [], [])
                      , Seq(
                          Match(Var("d_47"))
                        , Seq(
                            Build(Var("a_47"))
                          , Seq(
                              CallT(SVar("r_26"), [], [])
                            , Seq(
                                Match(Var("e_47"))
                              , Build(
                                  Anno(
                                    Op(
                                      "InfixConstr"
                                    , [Var("c_47"), Var("d_47"), Var("e_47")]
                                    )
                                  , Var("b_47")
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
          "ConstrDecl_2_0"
        , [ VarDec(
              "s_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_47", "f_47", "g_47", "i_47", "j_47"]
          , Seq(
              Match(
                Anno(
                  Op("ConstrDecl", [Var("f_47"), Var("g_47")])
                , Var("h_47")
                )
              )
            , Seq(
                Build(Var("f_47"))
              , Seq(
                  CallT(SVar("s_26"), [], [])
                , Seq(
                    Match(Var("i_47"))
                  , Seq(
                      Build(Var("g_47"))
                    , Seq(
                        CallT(SVar("t_26"), [], [])
                      , Seq(
                          Match(Var("j_47"))
                        , Build(
                            Anno(
                              Op("ConstrDecl", [Var("i_47"), Var("j_47")])
                            , Var("h_47")
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
          "ConstrDecls_1_0"
        , [ VarDec(
              "u_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_47", "k_47", "m_47"]
          , Seq(
              Match(
                Anno(Op("ConstrDecls", [Var("k_47")]), Var("l_47"))
              )
            , Seq(
                Build(Var("k_47"))
              , Seq(
                  CallT(SVar("u_26"), [], [])
                , Seq(
                    Match(Var("m_47"))
                  , Build(
                      Anno(Op("ConstrDecls", [Var("m_47")]), Var("l_47"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "NoConstrDecls_0_0"
        , []
        , []
        , Match(Anno(Op("NoConstrDecls", []), Wld()))
        )
      , SDefT(
          "Derive_1_0"
        , [ VarDec(
              "v_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_47", "n_47", "p_47"]
          , Seq(
              Match(
                Anno(Op("Derive", [Var("n_47")]), Var("o_47"))
              )
            , Seq(
                Build(Var("n_47"))
              , Seq(
                  CallT(SVar("v_26"), [], [])
                , Seq(
                    Match(Var("p_47"))
                  , Build(
                      Anno(Op("Derive", [Var("p_47")]), Var("o_47"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "NoDeriving_0_0"
        , []
        , []
        , Match(Anno(Op("NoDeriving", []), Wld()))
        )
      , SDefT(
          "TFunBin_2_0"
        , [ VarDec(
              "w_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_47", "q_47", "r_47", "t_47", "u_47"]
          , Seq(
              Match(
                Anno(
                  Op("TFunBin", [Var("q_47"), Var("r_47")])
                , Var("s_47")
                )
              )
            , Seq(
                Build(Var("q_47"))
              , Seq(
                  CallT(SVar("w_26"), [], [])
                , Seq(
                    Match(Var("t_47"))
                  , Seq(
                      Build(Var("r_47"))
                    , Seq(
                        CallT(SVar("x_26"), [], [])
                      , Seq(
                          Match(Var("u_47"))
                        , Build(
                            Anno(
                              Op("TFunBin", [Var("t_47"), Var("u_47")])
                            , Var("s_47")
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
              "y_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "z_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_47", "v_47", "w_47", "y_47", "z_47"]
          , Seq(
              Match(
                Anno(
                  Op("TAppBin", [Var("v_47"), Var("w_47")])
                , Var("x_47")
                )
              )
            , Seq(
                Build(Var("v_47"))
              , Seq(
                  CallT(SVar("y_26"), [], [])
                , Seq(
                    Match(Var("y_47"))
                  , Seq(
                      Build(Var("w_47"))
                    , Seq(
                        CallT(SVar("z_26"), [], [])
                      , Seq(
                          Match(Var("z_47"))
                        , Build(
                            Anno(
                              Op("TAppBin", [Var("y_47"), Var("z_47")])
                            , Var("x_47")
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
              "a_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_48", "a_48", "c_48"]
          , Seq(
              Match(
                Anno(Op("TProd", [Var("a_48")]), Var("b_48"))
              )
            , Seq(
                Build(Var("a_48"))
              , Seq(
                  CallT(SVar("a_27"), [], [])
                , Seq(
                    Match(Var("c_48"))
                  , Build(
                      Anno(Op("TProd", [Var("c_48")]), Var("b_48"))
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
              "b_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_48", "d_48", "f_48"]
          , Seq(
              Match(
                Anno(Op("TList", [Var("d_48")]), Var("e_48"))
              )
            , Seq(
                Build(Var("d_48"))
              , Seq(
                  CallT(SVar("b_27"), [], [])
                , Seq(
                    Match(Var("f_48"))
                  , Build(
                      Anno(Op("TList", [Var("f_48")]), Var("e_48"))
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
              "c_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_48", "g_48", "i_48"]
          , Seq(
              Match(
                Anno(Op("TVar", [Var("g_48")]), Var("h_48"))
              )
            , Seq(
                Build(Var("g_48"))
              , Seq(
                  CallT(SVar("c_27"), [], [])
                , Seq(
                    Match(Var("i_48"))
                  , Build(
                      Anno(Op("TVar", [Var("i_48")]), Var("h_48"))
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
              "d_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_48", "j_48", "l_48"]
          , Seq(
              Match(
                Anno(Op("TCon", [Var("j_48")]), Var("k_48"))
              )
            , Seq(
                Build(Var("j_48"))
              , Seq(
                  CallT(SVar("d_27"), [], [])
                , Seq(
                    Match(Var("l_48"))
                  , Build(
                      Anno(Op("TCon", [Var("l_48")]), Var("k_48"))
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
              "e_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_48", "m_48", "n_48", "p_48", "q_48"]
          , Seq(
              Match(
                Anno(
                  Op("TCons", [Var("m_48"), Var("n_48")])
                , Var("o_48")
                )
              )
            , Seq(
                Build(Var("m_48"))
              , Seq(
                  CallT(SVar("e_27"), [], [])
                , Seq(
                    Match(Var("p_48"))
                  , Seq(
                      Build(Var("n_48"))
                    , Seq(
                        CallT(SVar("f_27"), [], [])
                      , Seq(
                          Match(Var("q_48"))
                        , Build(
                            Anno(
                              Op("TCons", [Var("p_48"), Var("q_48")])
                            , Var("o_48")
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
          "TList_0_0"
        , []
        , []
        , Match(Anno(Op("TList", []), Wld()))
        )
      , SDefT(
          "TUnit_0_0"
        , []
        , []
        , Match(Anno(Op("TUnit", []), Wld()))
        )
      , SDefT(
          "TArrow_0_0"
        , []
        , []
        , Match(Anno(Op("TArrow", []), Wld()))
        )
      , SDefT(
          "Hiding_1_0"
        , [ VarDec(
              "g_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_48", "r_48", "t_48"]
          , Seq(
              Match(
                Anno(Op("Hiding", [Var("r_48")]), Var("s_48"))
              )
            , Seq(
                Build(Var("r_48"))
              , Seq(
                  CallT(SVar("g_27"), [], [])
                , Seq(
                    Match(Var("t_48"))
                  , Build(
                      Anno(Op("Hiding", [Var("t_48")]), Var("s_48"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Impspec_1_0"
        , [ VarDec(
              "h_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_48", "u_48", "w_48"]
          , Seq(
              Match(
                Anno(Op("Impspec", [Var("u_48")]), Var("v_48"))
              )
            , Seq(
                Build(Var("u_48"))
              , Seq(
                  CallT(SVar("h_27"), [], [])
                , Seq(
                    Match(Var("w_48"))
                  , Build(
                      Anno(Op("Impspec", [Var("w_48")]), Var("v_48"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "As_1_0"
        , [ VarDec(
              "i_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_48", "x_48", "z_48"]
          , Seq(
              Match(
                Anno(Op("As", [Var("x_48")]), Var("y_48"))
              )
            , Seq(
                Build(Var("x_48"))
              , Seq(
                  CallT(SVar("i_27"), [], [])
                , Seq(
                    Match(Var("z_48"))
                  , Build(
                      Anno(Op("As", [Var("z_48")]), Var("y_48"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Qualified_0_0"
        , []
        , []
        , Match(Anno(Op("Qualified", []), Wld()))
        )
      , SDefT(
          "SOURCE_0_0"
        , []
        , []
        , Match(Anno(Op("SOURCE", []), Wld()))
        )
      , SDefT(
          "Import_5_0"
        , [ VarDec(
              "j_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "m_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            [ "f_49"
            , "a_49"
            , "b_49"
            , "c_49"
            , "d_49"
            , "e_49"
            , "g_49"
            , "h_49"
            , "i_49"
            , "j_49"
            , "k_49"
            ]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Import"
                  , [ Var("a_49")
                    , Var("b_49")
                    , Var("c_49")
                    , Var("d_49")
                    , Var("e_49")
                    ]
                  )
                , Var("f_49")
                )
              )
            , Seq(
                Build(Var("a_49"))
              , Seq(
                  CallT(SVar("j_27"), [], [])
                , Seq(
                    Match(Var("g_49"))
                  , Seq(
                      Build(Var("b_49"))
                    , Seq(
                        CallT(SVar("k_27"), [], [])
                      , Seq(
                          Match(Var("h_49"))
                        , Seq(
                            Build(Var("c_49"))
                          , Seq(
                              CallT(SVar("l_27"), [], [])
                            , Seq(
                                Match(Var("i_49"))
                              , Seq(
                                  Build(Var("d_49"))
                                , Seq(
                                    CallT(SVar("m_27"), [], [])
                                  , Seq(
                                      Match(Var("j_49"))
                                    , Seq(
                                        Build(Var("e_49"))
                                      , Seq(
                                          CallT(SVar("n_27"), [], [])
                                        , Seq(
                                            Match(Var("k_49"))
                                          , Build(
                                              Anno(
                                                Op(
                                                  "Import"
                                                , [ Var("g_49")
                                                  , Var("h_49")
                                                  , Var("i_49")
                                                  , Var("j_49")
                                                  , Var("k_49")
                                                  ]
                                                )
                                              , Var("f_49")
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
        )
      , SDefT(
          "Exports_1_0"
        , [ VarDec(
              "o_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_49", "l_49", "n_49"]
          , Seq(
              Match(
                Anno(Op("Exports", [Var("l_49")]), Var("m_49"))
              )
            , Seq(
                Build(Var("l_49"))
              , Seq(
                  CallT(SVar("o_27"), [], [])
                , Seq(
                    Match(Var("n_49"))
                  , Build(
                      Anno(Op("Exports", [Var("n_49")]), Var("m_49"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Exportlist_1_0"
        , [ VarDec(
              "p_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_49", "o_49", "q_49"]
          , Seq(
              Match(
                Anno(Op("Exportlist", [Var("o_49")]), Var("p_49"))
              )
            , Seq(
                Build(Var("o_49"))
              , Seq(
                  CallT(SVar("p_27"), [], [])
                , Seq(
                    Match(Var("q_49"))
                  , Build(
                      Anno(Op("Exportlist", [Var("q_49")]), Var("p_49"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Body_2_0"
        , [ VarDec(
              "q_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "r_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_49", "r_49", "s_49", "u_49", "v_49"]
          , Seq(
              Match(
                Anno(
                  Op("Body", [Var("r_49"), Var("s_49")])
                , Var("t_49")
                )
              )
            , Seq(
                Build(Var("r_49"))
              , Seq(
                  CallT(SVar("q_27"), [], [])
                , Seq(
                    Match(Var("u_49"))
                  , Seq(
                      Build(Var("s_49"))
                    , Seq(
                        CallT(SVar("r_27"), [], [])
                      , Seq(
                          Match(Var("v_49"))
                        , Build(
                            Anno(
                              Op("Body", [Var("u_49"), Var("v_49")])
                            , Var("t_49")
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
          "Empty_0_0"
        , []
        , []
        , Match(Anno(Op("Empty", []), Wld()))
        )
      , SDefT(
          "FlexibleInstance_4_0"
        , [ VarDec(
              "s_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "u_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_50", "w_49", "x_49", "y_49", "z_49", "b_50", "c_50", "d_50", "e_50"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "FlexibleInstance"
                  , [Var("w_49"), Var("x_49"), Var("y_49"), Var("z_49")]
                  )
                , Var("a_50")
                )
              )
            , Seq(
                Build(Var("w_49"))
              , Seq(
                  CallT(SVar("s_27"), [], [])
                , Seq(
                    Match(Var("b_50"))
                  , Seq(
                      Build(Var("x_49"))
                    , Seq(
                        CallT(SVar("t_27"), [], [])
                      , Seq(
                          Match(Var("c_50"))
                        , Seq(
                            Build(Var("y_49"))
                          , Seq(
                              CallT(SVar("u_27"), [], [])
                            , Seq(
                                Match(Var("d_50"))
                              , Seq(
                                  Build(Var("z_49"))
                                , Seq(
                                    CallT(SVar("v_27"), [], [])
                                  , Seq(
                                      Match(Var("e_50"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "FlexibleInstance"
                                          , [Var("b_50"), Var("c_50"), Var("d_50"), Var("e_50")]
                                          )
                                        , Var("a_50")
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
          "Default_1_0"
        , [ VarDec(
              "w_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_50", "f_50", "h_50"]
          , Seq(
              Match(
                Anno(Op("Default", [Var("f_50")]), Var("g_50"))
              )
            , Seq(
                Build(Var("f_50"))
              , Seq(
                  CallT(SVar("w_27"), [], [])
                , Seq(
                    Match(Var("h_50"))
                  , Build(
                      Anno(Op("Default", [Var("h_50")]), Var("g_50"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Instance_4_0"
        , [ VarDec(
              "x_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "z_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_50", "i_50", "j_50", "k_50", "l_50", "n_50", "o_50", "p_50", "q_50"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Instance"
                  , [Var("i_50"), Var("j_50"), Var("k_50"), Var("l_50")]
                  )
                , Var("m_50")
                )
              )
            , Seq(
                Build(Var("i_50"))
              , Seq(
                  CallT(SVar("x_27"), [], [])
                , Seq(
                    Match(Var("n_50"))
                  , Seq(
                      Build(Var("j_50"))
                    , Seq(
                        CallT(SVar("y_27"), [], [])
                      , Seq(
                          Match(Var("o_50"))
                        , Seq(
                            Build(Var("k_50"))
                          , Seq(
                              CallT(SVar("z_27"), [], [])
                            , Seq(
                                Match(Var("p_50"))
                              , Seq(
                                  Build(Var("l_50"))
                                , Seq(
                                    CallT(SVar("a_28"), [], [])
                                  , Seq(
                                      Match(Var("q_50"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "Instance"
                                          , [Var("n_50"), Var("o_50"), Var("p_50"), Var("q_50")]
                                          )
                                        , Var("m_50")
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
          "Class_4_0"
        , [ VarDec(
              "b_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_50", "r_50", "s_50", "t_50", "u_50", "w_50", "x_50", "y_50", "z_50"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Class"
                  , [Var("r_50"), Var("s_50"), Var("t_50"), Var("u_50")]
                  )
                , Var("v_50")
                )
              )
            , Seq(
                Build(Var("r_50"))
              , Seq(
                  CallT(SVar("b_28"), [], [])
                , Seq(
                    Match(Var("w_50"))
                  , Seq(
                      Build(Var("s_50"))
                    , Seq(
                        CallT(SVar("c_28"), [], [])
                      , Seq(
                          Match(Var("x_50"))
                        , Seq(
                            Build(Var("t_50"))
                          , Seq(
                              CallT(SVar("d_28"), [], [])
                            , Seq(
                                Match(Var("y_50"))
                              , Seq(
                                  Build(Var("u_50"))
                                , Seq(
                                    CallT(SVar("e_28"), [], [])
                                  , Seq(
                                      Match(Var("z_50"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "Class"
                                          , [Var("w_50"), Var("x_50"), Var("y_50"), Var("z_50")]
                                          )
                                        , Var("v_50")
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
          "Data_4_0"
        , [ VarDec(
              "f_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_51", "a_51", "b_51", "c_51", "d_51", "f_51", "g_51", "h_51", "i_51"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Data"
                  , [Var("a_51"), Var("b_51"), Var("c_51"), Var("d_51")]
                  )
                , Var("e_51")
                )
              )
            , Seq(
                Build(Var("a_51"))
              , Seq(
                  CallT(SVar("f_28"), [], [])
                , Seq(
                    Match(Var("f_51"))
                  , Seq(
                      Build(Var("b_51"))
                    , Seq(
                        CallT(SVar("g_28"), [], [])
                      , Seq(
                          Match(Var("g_51"))
                        , Seq(
                            Build(Var("c_51"))
                          , Seq(
                              CallT(SVar("h_28"), [], [])
                            , Seq(
                                Match(Var("h_51"))
                              , Seq(
                                  Build(Var("d_51"))
                                , Seq(
                                    CallT(SVar("i_28"), [], [])
                                  , Seq(
                                      Match(Var("i_51"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "Data"
                                          , [Var("f_51"), Var("g_51"), Var("h_51"), Var("i_51")]
                                          )
                                        , Var("e_51")
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
          "TypeDecl_3_0"
        , [ VarDec(
              "j_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_51", "j_51", "k_51", "l_51", "n_51", "o_51", "p_51"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "TypeDecl"
                  , [Var("j_51"), Var("k_51"), Var("l_51")]
                  )
                , Var("m_51")
                )
              )
            , Seq(
                Build(Var("j_51"))
              , Seq(
                  CallT(SVar("j_28"), [], [])
                , Seq(
                    Match(Var("n_51"))
                  , Seq(
                      Build(Var("k_51"))
                    , Seq(
                        CallT(SVar("k_28"), [], [])
                      , Seq(
                          Match(Var("o_51"))
                        , Seq(
                            Build(Var("l_51"))
                          , Seq(
                              CallT(SVar("l_28"), [], [])
                            , Seq(
                                Match(Var("p_51"))
                              , Build(
                                  Anno(
                                    Op(
                                      "TypeDecl"
                                    , [Var("n_51"), Var("o_51"), Var("p_51")]
                                    )
                                  , Var("m_51")
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
          "Program_1_0"
        , [ VarDec(
              "m_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_51", "q_51", "s_51"]
          , Seq(
              Match(
                Anno(Op("Program", [Var("q_51")]), Var("r_51"))
              )
            , Seq(
                Build(Var("q_51"))
              , Seq(
                  CallT(SVar("m_28"), [], [])
                , Seq(
                    Match(Var("s_51"))
                  , Build(
                      Anno(Op("Program", [Var("s_51")]), Var("r_51"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Module_2_0"
        , [ VarDec(
              "n_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_51", "t_51", "u_51", "w_51", "x_51"]
          , Seq(
              Match(
                Anno(
                  Op("Module", [Var("t_51"), Var("u_51")])
                , Var("v_51")
                )
              )
            , Seq(
                Build(Var("t_51"))
              , Seq(
                  CallT(SVar("n_28"), [], [])
                , Seq(
                    Match(Var("w_51"))
                  , Seq(
                      Build(Var("u_51"))
                    , Seq(
                        CallT(SVar("o_28"), [], [])
                      , Seq(
                          Match(Var("x_51"))
                        , Build(
                            Anno(
                              Op("Module", [Var("w_51"), Var("x_51")])
                            , Var("v_51")
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
          "ModuleDec_2_0"
        , [ VarDec(
              "p_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_52", "y_51", "z_51", "b_52", "c_52"]
          , Seq(
              Match(
                Anno(
                  Op("ModuleDec", [Var("y_51"), Var("z_51")])
                , Var("a_52")
                )
              )
            , Seq(
                Build(Var("y_51"))
              , Seq(
                  CallT(SVar("p_28"), [], [])
                , Seq(
                    Match(Var("b_52"))
                  , Seq(
                      Build(Var("z_51"))
                    , Seq(
                        CallT(SVar("q_28"), [], [])
                      , Seq(
                          Match(Var("c_52"))
                        , Build(
                            Anno(
                              Op("ModuleDec", [Var("b_52"), Var("c_52")])
                            , Var("a_52")
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
          "CLitLit_1_0"
        , [ VarDec(
              "r_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_52", "d_52", "f_52"]
          , Seq(
              Match(
                Anno(Op("CLitLit", [Var("d_52")]), Var("e_52"))
              )
            , Seq(
                Build(Var("d_52"))
              , Seq(
                  CallT(SVar("r_28"), [], [])
                , Seq(
                    Match(Var("f_52"))
                  , Build(
                      Anno(Op("CLitLit", [Var("f_52")]), Var("e_52"))
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
              "s_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_52", "g_52", "i_52"]
          , Seq(
              Match(
                Anno(Op("PrimDouble", [Var("g_52")]), Var("h_52"))
              )
            , Seq(
                Build(Var("g_52"))
              , Seq(
                  CallT(SVar("s_28"), [], [])
                , Seq(
                    Match(Var("i_52"))
                  , Build(
                      Anno(Op("PrimDouble", [Var("i_52")]), Var("h_52"))
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
              "t_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_52", "j_52", "l_52"]
          , Seq(
              Match(
                Anno(Op("PrimFloat", [Var("j_52")]), Var("k_52"))
              )
            , Seq(
                Build(Var("j_52"))
              , Seq(
                  CallT(SVar("t_28"), [], [])
                , Seq(
                    Match(Var("l_52"))
                  , Build(
                      Anno(Op("PrimFloat", [Var("l_52")]), Var("k_52"))
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
              "u_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_52", "m_52", "o_52"]
          , Seq(
              Match(
                Anno(Op("PrimString", [Var("m_52")]), Var("n_52"))
              )
            , Seq(
                Build(Var("m_52"))
              , Seq(
                  CallT(SVar("u_28"), [], [])
                , Seq(
                    Match(Var("o_52"))
                  , Build(
                      Anno(Op("PrimString", [Var("o_52")]), Var("n_52"))
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
              "v_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_52", "p_52", "r_52"]
          , Seq(
              Match(
                Anno(Op("PrimChar", [Var("p_52")]), Var("q_52"))
              )
            , Seq(
                Build(Var("p_52"))
              , Seq(
                  CallT(SVar("v_28"), [], [])
                , Seq(
                    Match(Var("r_52"))
                  , Build(
                      Anno(Op("PrimChar", [Var("r_52")]), Var("q_52"))
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
              "w_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_52", "s_52", "u_52"]
          , Seq(
              Match(
                Anno(Op("PrimInt", [Var("s_52")]), Var("t_52"))
              )
            , Seq(
                Build(Var("s_52"))
              , Seq(
                  CallT(SVar("w_28"), [], [])
                , Seq(
                    Match(Var("u_52"))
                  , Build(
                      Anno(Op("PrimInt", [Var("u_52")]), Var("t_52"))
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
              "x_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_52", "v_52", "x_52"]
          , Seq(
              Match(
                Anno(Op("Float", [Var("v_52")]), Var("w_52"))
              )
            , Seq(
                Build(Var("v_52"))
              , Seq(
                  CallT(SVar("x_28"), [], [])
                , Seq(
                    Match(Var("x_52"))
                  , Build(
                      Anno(Op("Float", [Var("x_52")]), Var("w_52"))
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
              "y_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_52", "y_52", "a_53"]
          , Seq(
              Match(
                Anno(Op("Int", [Var("y_52")]), Var("z_52"))
              )
            , Seq(
                Build(Var("y_52"))
              , Seq(
                  CallT(SVar("y_28"), [], [])
                , Seq(
                    Match(Var("a_53"))
                  , Build(
                      Anno(Op("Int", [Var("a_53")]), Var("z_52"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "HexadecimalEsc_1_0"
        , [ VarDec(
              "z_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_53", "b_53", "d_53"]
          , Seq(
              Match(
                Anno(Op("HexadecimalEsc", [Var("b_53")]), Var("c_53"))
              )
            , Seq(
                Build(Var("b_53"))
              , Seq(
                  CallT(SVar("z_28"), [], [])
                , Seq(
                    Match(Var("d_53"))
                  , Build(
                      Anno(Op("HexadecimalEsc", [Var("d_53")]), Var("c_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "OctalEsc_1_0"
        , [ VarDec(
              "a_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_53", "e_53", "g_53"]
          , Seq(
              Match(
                Anno(Op("OctalEsc", [Var("e_53")]), Var("f_53"))
              )
            , Seq(
                Build(Var("e_53"))
              , Seq(
                  CallT(SVar("a_29"), [], [])
                , Seq(
                    Match(Var("g_53"))
                  , Build(
                      Anno(Op("OctalEsc", [Var("g_53")]), Var("f_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "DecimalEsc_1_0"
        , [ VarDec(
              "b_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_53", "h_53", "j_53"]
          , Seq(
              Match(
                Anno(Op("DecimalEsc", [Var("h_53")]), Var("i_53"))
              )
            , Seq(
                Build(Var("h_53"))
              , Seq(
                  CallT(SVar("b_29"), [], [])
                , Seq(
                    Match(Var("j_53"))
                  , Build(
                      Anno(Op("DecimalEsc", [Var("j_53")]), Var("i_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ASCIIEsc_1_0"
        , [ VarDec(
              "c_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_53", "k_53", "m_53"]
          , Seq(
              Match(
                Anno(Op("ASCIIEsc", [Var("k_53")]), Var("l_53"))
              )
            , Seq(
                Build(Var("k_53"))
              , Seq(
                  CallT(SVar("c_29"), [], [])
                , Seq(
                    Match(Var("m_53"))
                  , Build(
                      Anno(Op("ASCIIEsc", [Var("m_53")]), Var("l_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "CharEsc_1_0"
        , [ VarDec(
              "d_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_53", "n_53", "p_53"]
          , Seq(
              Match(
                Anno(Op("CharEsc", [Var("n_53")]), Var("o_53"))
              )
            , Seq(
                Build(Var("n_53"))
              , Seq(
                  CallT(SVar("d_29"), [], [])
                , Seq(
                    Match(Var("p_53"))
                  , Build(
                      Anno(Op("CharEsc", [Var("p_53")]), Var("o_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Gap_1_0"
        , [ VarDec(
              "e_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_53", "q_53", "s_53"]
          , Seq(
              Match(
                Anno(Op("Gap", [Var("q_53")]), Var("r_53"))
              )
            , Seq(
                Build(Var("q_53"))
              , Seq(
                  CallT(SVar("e_29"), [], [])
                , Seq(
                    Match(Var("s_53"))
                  , Build(
                      Anno(Op("Gap", [Var("s_53")]), Var("r_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Escape_1_0"
        , [ VarDec(
              "f_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_53", "t_53", "v_53"]
          , Seq(
              Match(
                Anno(Op("Escape", [Var("t_53")]), Var("u_53"))
              )
            , Seq(
                Build(Var("t_53"))
              , Seq(
                  CallT(SVar("f_29"), [], [])
                , Seq(
                    Match(Var("v_53"))
                  , Build(
                      Anno(Op("Escape", [Var("v_53")]), Var("u_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "String_1_0"
        , [ VarDec(
              "g_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_53", "w_53", "y_53"]
          , Seq(
              Match(
                Anno(Op("String", [Var("w_53")]), Var("x_53"))
              )
            , Seq(
                Build(Var("w_53"))
              , Seq(
                  CallT(SVar("g_29"), [], [])
                , Seq(
                    Match(Var("y_53"))
                  , Build(
                      Anno(Op("String", [Var("y_53")]), Var("x_53"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Char_1_0"
        , [ VarDec(
              "h_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_54", "z_53", "b_54"]
          , Seq(
              Match(
                Anno(Op("Char", [Var("z_53")]), Var("a_54"))
              )
            , Seq(
                Build(Var("z_53"))
              , Seq(
                  CallT(SVar("h_29"), [], [])
                , Seq(
                    Match(Var("b_54"))
                  , Build(
                      Anno(Op("Char", [Var("b_54")]), Var("a_54"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "QModId_2_0"
        , [ VarDec(
              "i_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_54", "c_54", "d_54", "f_54", "g_54"]
          , Seq(
              Match(
                Anno(
                  Op("QModId", [Var("c_54"), Var("d_54")])
                , Var("e_54")
                )
              )
            , Seq(
                Build(Var("c_54"))
              , Seq(
                  CallT(SVar("i_29"), [], [])
                , Seq(
                    Match(Var("f_54"))
                  , Seq(
                      Build(Var("d_54"))
                    , Seq(
                        CallT(SVar("j_29"), [], [])
                      , Seq(
                          Match(Var("g_54"))
                        , Build(
                            Anno(
                              Op("QModId", [Var("f_54"), Var("g_54")])
                            , Var("e_54")
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
          "QConSym_2_0"
        , [ VarDec(
              "k_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_54", "h_54", "i_54", "k_54", "l_54"]
          , Seq(
              Match(
                Anno(
                  Op("QConSym", [Var("h_54"), Var("i_54")])
                , Var("j_54")
                )
              )
            , Seq(
                Build(Var("h_54"))
              , Seq(
                  CallT(SVar("k_29"), [], [])
                , Seq(
                    Match(Var("k_54"))
                  , Seq(
                      Build(Var("i_54"))
                    , Seq(
                        CallT(SVar("l_29"), [], [])
                      , Seq(
                          Match(Var("l_54"))
                        , Build(
                            Anno(
                              Op("QConSym", [Var("k_54"), Var("l_54")])
                            , Var("j_54")
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
          "QVarSym_2_0"
        , [ VarDec(
              "m_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_54", "m_54", "n_54", "p_54", "q_54"]
          , Seq(
              Match(
                Anno(
                  Op("QVarSym", [Var("m_54"), Var("n_54")])
                , Var("o_54")
                )
              )
            , Seq(
                Build(Var("m_54"))
              , Seq(
                  CallT(SVar("m_29"), [], [])
                , Seq(
                    Match(Var("p_54"))
                  , Seq(
                      Build(Var("n_54"))
                    , Seq(
                        CallT(SVar("n_29"), [], [])
                      , Seq(
                          Match(Var("q_54"))
                        , Build(
                            Anno(
                              Op("QVarSym", [Var("p_54"), Var("q_54")])
                            , Var("o_54")
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
          "QConId_2_0"
        , [ VarDec(
              "o_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "p_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_54", "r_54", "s_54", "u_54", "v_54"]
          , Seq(
              Match(
                Anno(
                  Op("QConId", [Var("r_54"), Var("s_54")])
                , Var("t_54")
                )
              )
            , Seq(
                Build(Var("r_54"))
              , Seq(
                  CallT(SVar("o_29"), [], [])
                , Seq(
                    Match(Var("u_54"))
                  , Seq(
                      Build(Var("s_54"))
                    , Seq(
                        CallT(SVar("p_29"), [], [])
                      , Seq(
                          Match(Var("v_54"))
                        , Build(
                            Anno(
                              Op("QConId", [Var("u_54"), Var("v_54")])
                            , Var("t_54")
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
          "QVarId_2_0"
        , [ VarDec(
              "q_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "r_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_54", "w_54", "x_54", "z_54", "a_55"]
          , Seq(
              Match(
                Anno(
                  Op("QVarId", [Var("w_54"), Var("x_54")])
                , Var("y_54")
                )
              )
            , Seq(
                Build(Var("w_54"))
              , Seq(
                  CallT(SVar("q_29"), [], [])
                , Seq(
                    Match(Var("z_54"))
                  , Seq(
                      Build(Var("x_54"))
                    , Seq(
                        CallT(SVar("r_29"), [], [])
                      , Seq(
                          Match(Var("a_55"))
                        , Build(
                            Anno(
                              Op("QVarId", [Var("z_54"), Var("a_55")])
                            , Var("y_54")
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
          "BinCon_1_0"
        , [ VarDec(
              "s_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_55", "b_55", "d_55"]
          , Seq(
              Match(
                Anno(Op("BinCon", [Var("b_55")]), Var("c_55"))
              )
            , Seq(
                Build(Var("b_55"))
              , Seq(
                  CallT(SVar("s_29"), [], [])
                , Seq(
                    Match(Var("d_55"))
                  , Build(
                      Anno(Op("BinCon", [Var("d_55")]), Var("c_55"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ConsOp_1_0"
        , [ VarDec(
              "t_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_55", "e_55", "g_55"]
          , Seq(
              Match(
                Anno(Op("ConsOp", [Var("e_55")]), Var("f_55"))
              )
            , Seq(
                Build(Var("e_55"))
              , Seq(
                  CallT(SVar("t_29"), [], [])
                , Seq(
                    Match(Var("g_55"))
                  , Build(
                      Anno(Op("ConsOp", [Var("g_55")]), Var("f_55"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrefCon_1_0"
        , [ VarDec(
              "u_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_55", "h_55", "j_55"]
          , Seq(
              Match(
                Anno(Op("PrefCon", [Var("h_55")]), Var("i_55"))
              )
            , Seq(
                Build(Var("h_55"))
              , Seq(
                  CallT(SVar("u_29"), [], [])
                , Seq(
                    Match(Var("j_55"))
                  , Build(
                      Anno(Op("PrefCon", [Var("j_55")]), Var("i_55"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "PrefOp_1_0"
        , [ VarDec(
              "v_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_55", "k_55", "m_55"]
          , Seq(
              Match(
                Anno(Op("PrefOp", [Var("k_55")]), Var("l_55"))
              )
            , Seq(
                Build(Var("k_55"))
              , Seq(
                  CallT(SVar("v_29"), [], [])
                , Seq(
                    Match(Var("m_55"))
                  , Build(
                      Anno(Op("PrefOp", [Var("m_55")]), Var("l_55"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "ConOp_1_0"
        , [ VarDec(
              "w_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_55", "n_55", "p_55"]
          , Seq(
              Match(
                Anno(Op("ConOp", [Var("n_55")]), Var("o_55"))
              )
            , Seq(
                Build(Var("n_55"))
              , Seq(
                  CallT(SVar("w_29"), [], [])
                , Seq(
                    Match(Var("p_55"))
                  , Build(
                      Anno(Op("ConOp", [Var("p_55")]), Var("o_55"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Op_1_0"
        , [ VarDec(
              "x_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_55", "q_55", "s_55"]
          , Seq(
              Match(
                Anno(Op("Op", [Var("q_55")]), Var("r_55"))
              )
            , Seq(
                Build(Var("q_55"))
              , Seq(
                  CallT(SVar("x_29"), [], [])
                , Seq(
                    Match(Var("s_55"))
                  , Build(
                      Anno(Op("Op", [Var("s_55")]), Var("r_55"))
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
              "y_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_55", "t_55", "v_55"]
          , Seq(
              Match(
                Anno(Op("BinOp", [Var("t_55")]), Var("u_55"))
              )
            , Seq(
                Build(Var("t_55"))
              , Seq(
                  CallT(SVar("y_29"), [], [])
                , Seq(
                    Match(Var("v_55"))
                  , Build(
                      Anno(Op("BinOp", [Var("v_55")]), Var("u_55"))
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
          "Ins_1_0"
        , [ VarDec(
              "z_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_55", "w_55", "y_55"]
          , Seq(
              Match(
                Anno(Op("Ins", [Var("w_55")]), Var("x_55"))
              )
            , Seq(
                Build(Var("w_55"))
              , Seq(
                  CallT(SVar("z_29"), [], [])
                , Seq(
                    Match(Var("y_55"))
                  , Build(
                      Anno(Op("Ins", [Var("y_55")]), Var("x_55"))
                    )
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "Snoc_2_0"
        , [ VarDec(
              "a_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "b_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_56", "z_55", "a_56", "c_56", "d_56"]
          , Seq(
              Match(
                Anno(
                  Op("Snoc", [Var("z_55"), Var("a_56")])
                , Var("b_56")
                )
              )
            , Seq(
                Build(Var("z_55"))
              , Seq(
                  CallT(SVar("a_30"), [], [])
                , Seq(
                    Match(Var("c_56"))
                  , Seq(
                      Build(Var("a_56"))
                    , Seq(
                        CallT(SVar("b_30"), [], [])
                      , Seq(
                          Match(Var("d_56"))
                        , Build(
                            Anno(
                              Op("Snoc", [Var("c_56"), Var("d_56")])
                            , Var("b_56")
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
          "_0_0"
        , []
        , []
        , Match(Anno(Op("", []), Wld()))
        )
      , SDefT(
          "_2_0"
        , [ VarDec(
              "c_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_56", "e_56", "f_56", "h_56", "i_56"]
          , Seq(
              Match(
                Anno(
                  Op("", [Var("e_56"), Var("f_56")])
                , Var("g_56")
                )
              )
            , Seq(
                Build(Var("e_56"))
              , Seq(
                  CallT(SVar("c_30"), [], [])
                , Seq(
                    Match(Var("h_56"))
                  , Seq(
                      Build(Var("f_56"))
                    , Seq(
                        CallT(SVar("d_30"), [], [])
                      , Seq(
                          Match(Var("i_56"))
                        , Build(
                            Anno(
                              Op("", [Var("h_56"), Var("i_56")])
                            , Var("g_56")
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
              "e_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_56", "j_56", "k_56", "l_56", "n_56", "o_56", "p_56"]
          , Seq(
              Match(
                Anno(
                  Op(
                    ""
                  , [Var("j_56"), Var("k_56"), Var("l_56")]
                  )
                , Var("m_56")
                )
              )
            , Seq(
                Build(Var("j_56"))
              , Seq(
                  CallT(SVar("e_30"), [], [])
                , Seq(
                    Match(Var("n_56"))
                  , Seq(
                      Build(Var("k_56"))
                    , Seq(
                        CallT(SVar("f_30"), [], [])
                      , Seq(
                          Match(Var("o_56"))
                        , Seq(
                            Build(Var("l_56"))
                          , Seq(
                              CallT(SVar("g_30"), [], [])
                            , Seq(
                                Match(Var("p_56"))
                              , Build(
                                  Anno(
                                    Op(
                                      ""
                                    , [Var("n_56"), Var("o_56"), Var("p_56")]
                                    )
                                  , Var("m_56")
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
              "h_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_56", "q_56", "s_56"]
          , Seq(
              Match(
                Anno(Op("DR_UNDEFINE", [Var("q_56")]), Var("r_56"))
              )
            , Seq(
                Build(Var("q_56"))
              , Seq(
                  CallT(SVar("h_30"), [], [])
                , Seq(
                    Match(Var("s_56"))
                  , Build(
                      Anno(Op("DR_UNDEFINE", [Var("s_56")]), Var("r_56"))
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
