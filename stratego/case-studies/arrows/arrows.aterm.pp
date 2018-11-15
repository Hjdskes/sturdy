Specification(
  [ Signature(
      [ Constructors(
          [ OpDeclInj(
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
            ["j_11", "k_11", "l_11", "m_11", "n_11", "p_11", "o_11", "q_11"]
          , Seq(
              Match(
                Anno(
                  Op("ArrProcedure", [Var("k_11"), Var("j_11")])
                , Wld()
                )
              )
            , Seq(
                Match(Var("m_11"))
              , Seq(
                  Build(Var("k_11"))
                , Seq(
                    CallT(SVar("free_pat_vars_0_0"), [], [])
                  , Seq(
                      Match(Var("l_11"))
                    , Seq(
                        Build(Var("m_11"))
                      , Seq(
                          Match(Var("p_11"))
                        , Seq(
                            Build(Var("l_11"))
                          , Seq(
                              CallT(SVar("tuple_0_0"), [], [])
                            , Seq(
                                Match(Var("n_11"))
                              , Seq(
                                  Build(Var("p_11"))
                                , Seq(
                                    Match(Var("q_11"))
                                  , Seq(
                                      Build(Var("j_11"))
                                    , Seq(
                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("l_11")])
                                      , Seq(
                                          Match(Var("o_11"))
                                        , Seq(
                                            Build(Var("q_11"))
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
                                                                  , [Var("k_11"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                  )
                                                                , Op("Nil", [])
                                                                )
                                                              , Var("n_11")
                                                              ]
                                                            )
                                                          , Op("Nil", [])
                                                          )
                                                        ]
                                                      )
                                                    , Op("Nil", [])
                                                    )
                                                  , Anno(Str(">>>"), Op("Nil", []))
                                                  , Var("o_11")
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
        , [VarDec("c_30", ConstType(Sort("ATerm", [])))]
        , GuardedLChoice(
            Scope(
              ["d_16", "e_16", "f_16", "g_16"]
            , Seq(
                Match(
                  Anno(
                    Op("ArrFirst", [Var("e_16"), Var("d_16")])
                  , Wld()
                  )
                )
              , Seq(
                  Match(Var("g_16"))
                , Seq(
                    Build(Var("c_30"))
                  , Seq(
                      CallT(SVar("tuple_pat_0_0"), [], [])
                    , Seq(
                        Match(Var("f_16"))
                      , Seq(
                          Build(Var("g_16"))
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
                                                , [Var("f_16"), Anno(Op("Nil", []), Op("Nil", []))]
                                                )
                                              , Op("Nil", [])
                                              )
                                            , Var("d_16")
                                            ]
                                          )
                                        , Op("Nil", [])
                                        )
                                      ]
                                    )
                                  , Op("Nil", [])
                                  )
                                , Anno(Str(">>>"), Op("Nil", []))
                                , Var("e_16")
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
                ["y_15", "z_15", "a_16", "b_16"]
              , Seq(
                  Match(
                    Anno(
                      Op("ArrHigher", [Var("y_15"), Var("z_15")])
                    , Wld()
                    )
                  )
                , Seq(
                    Match(Var("b_16"))
                  , Seq(
                      Build(Var("c_30"))
                    , Seq(
                        CallT(SVar("tuple_pat_0_0"), [], [])
                      , Seq(
                          Match(Var("a_16"))
                        , Seq(
                            Build(Var("b_16"))
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
                                                  , [Var("a_16"), Anno(Op("Nil", []), Op("Nil", []))]
                                                  )
                                                , Op("Nil", [])
                                                )
                                              , Anno(
                                                  Op(
                                                    "Product"
                                                  , [ Anno(
                                                        Op(
                                                          "ECons"
                                                        , [ Var("y_15")
                                                          , Anno(
                                                              Op(
                                                                "Cons"
                                                              , [Var("z_15"), Anno(Op("Nil", []), Op("Nil", []))]
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
                  [ "k_15"
                  , "l_15"
                  , "m_15"
                  , "n_15"
                  , "s_15"
                  , "o_15"
                  , "t_15"
                  , "p_15"
                  , "u_15"
                  , "q_15"
                  , "v_15"
                  , "r_15"
                  , "w_15"
                  ]
                , Seq(
                    Match(
                      Anno(
                        Op(
                          "ArrIf"
                        , [Var("k_15"), Var("l_15"), Var("m_15")]
                        )
                      , Wld()
                      )
                    )
                  , Seq(
                      Match(Var("s_15"))
                    , Seq(
                        Build(Var("c_30"))
                      , Seq(
                          CallT(SVar("tuple_pat_0_0"), [], [])
                        , Seq(
                            Match(Var("n_15"))
                          , Seq(
                              Build(Var("s_15"))
                            , Seq(
                                Match(Var("t_15"))
                              , Seq(
                                  Build(Var("c_30"))
                                , Seq(
                                    CallT(SVar("tuple_0_0"), [], [])
                                  , Seq(
                                      Match(Var("o_15"))
                                    , Seq(
                                        Build(Var("t_15"))
                                      , Seq(
                                          Match(Var("u_15"))
                                        , Seq(
                                            Build(Var("c_30"))
                                          , Seq(
                                              CallT(SVar("tuple_0_0"), [], [])
                                            , Seq(
                                                Match(Var("p_15"))
                                              , Seq(
                                                  Build(Var("u_15"))
                                                , Seq(
                                                    Match(Var("v_15"))
                                                  , Seq(
                                                      Build(Var("l_15"))
                                                    , Seq(
                                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                                      , Seq(
                                                          Match(Var("q_15"))
                                                        , Seq(
                                                            Build(Var("v_15"))
                                                          , Seq(
                                                              Match(Var("w_15"))
                                                            , Seq(
                                                                Build(Var("m_15"))
                                                              , Seq(
                                                                  CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                                                , Seq(
                                                                    Match(Var("r_15"))
                                                                  , Seq(
                                                                      Build(Var("w_15"))
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
                                                                                            , [Var("n_15"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                            )
                                                                                          , Op("Nil", [])
                                                                                          )
                                                                                        , Anno(
                                                                                            Op(
                                                                                              "If"
                                                                                            , [ Var("k_15")
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
                                                                                                    , Var("o_15")
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
                                                                                                    , Var("p_15")
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
                                                                                , [ Var("q_15")
                                                                                  , Anno(Str("|||"), Op("Nil", []))
                                                                                  , Var("r_15")
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
                    [ "y_14"
                    , "z_14"
                    , "a_15"
                    , "b_15"
                    , "c_15"
                    , "d_15"
                    , "g_15"
                    , "e_15"
                    , "h_15"
                    , "f_15"
                    , "i_15"
                    ]
                  , Seq(
                      Match(
                        Anno(
                          Op("ArrLet", [Var("z_14"), Var("y_14")])
                        , Wld()
                        )
                      )
                    , Seq(
                        Match(Var("c_15"))
                      , Seq(
                          Build(Var("z_14"))
                        , Seq(
                            CallT(SVar("free_decls_vars_0_0"), [], [])
                          , Seq(
                              Match(Var("a_15"))
                            , Seq(
                                Build(
                                  Anno(
                                    Op("", [Var("c_30"), Var("a_15")])
                                  , Op("Nil", [])
                                  )
                                )
                              , Seq(
                                  CallT(SVar("conc_0_0"), [], [])
                                , Seq(
                                    Match(Var("b_15"))
                                  , Seq(
                                      Build(Var("c_15"))
                                    , Seq(
                                        Match(Var("g_15"))
                                      , Seq(
                                          Build(Var("c_30"))
                                        , Seq(
                                            CallT(SVar("tuple_pat_0_0"), [], [])
                                          , Seq(
                                              Match(Var("d_15"))
                                            , Seq(
                                                Build(Var("g_15"))
                                              , Seq(
                                                  Match(Var("h_15"))
                                                , Seq(
                                                    Build(Var("b_15"))
                                                  , Seq(
                                                      CallT(SVar("tuple_0_0"), [], [])
                                                    , Seq(
                                                        Match(Var("e_15"))
                                                      , Seq(
                                                          Build(Var("h_15"))
                                                        , Seq(
                                                            Match(Var("i_15"))
                                                          , Seq(
                                                              Build(Var("y_14"))
                                                            , Seq(
                                                                CallT(SVar("desugar_arrow_p__0_1"), [], [Var("b_15")])
                                                              , Seq(
                                                                  Match(Var("f_15"))
                                                                , Seq(
                                                                    Build(Var("i_15"))
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
                                                                                          , [Var("d_15"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                          )
                                                                                        , Op("Nil", [])
                                                                                        )
                                                                                      , Anno(
                                                                                          Op("Let", [Var("z_14"), Var("e_15")])
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
                                                                          , Var("f_15")
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
                      [ "m_14"
                      , "n_14"
                      , "o_14"
                      , "p_14"
                      , "q_14"
                      , "r_14"
                      , "u_14"
                      , "s_14"
                      , "v_14"
                      , "t_14"
                      , "w_14"
                      ]
                    , Seq(
                        Match(
                          Anno(
                            Op(
                              "ArrAbs"
                            , [ Anno(
                                  Op(
                                    "Cons"
                                  , [Var("n_14"), Anno(Op("Nil", []), Wld())]
                                  )
                                , Wld()
                                )
                              , Var("m_14")
                              ]
                            )
                          , Wld()
                          )
                        )
                      , Seq(
                          Match(Var("q_14"))
                        , Seq(
                            Build(Var("n_14"))
                          , Seq(
                              CallT(SVar("free_pat_vars_0_0"), [], [])
                            , Seq(
                                Match(Var("o_14"))
                              , Seq(
                                  Build(
                                    Anno(
                                      Op("", [Var("c_30"), Var("o_14")])
                                    , Op("Nil", [])
                                    )
                                  )
                                , Seq(
                                    CallT(SVar("conc_0_0"), [], [])
                                  , Seq(
                                      Match(Var("p_14"))
                                    , Seq(
                                        Build(Var("q_14"))
                                      , Seq(
                                          Match(Var("u_14"))
                                        , Seq(
                                            Build(Var("c_30"))
                                          , Seq(
                                              CallT(SVar("tuple_pat_0_0"), [], [])
                                            , Seq(
                                                Match(Var("r_14"))
                                              , Seq(
                                                  Build(Var("u_14"))
                                                , Seq(
                                                    Match(Var("v_14"))
                                                  , Seq(
                                                      Build(Var("p_14"))
                                                    , Seq(
                                                        CallT(SVar("tuple_0_0"), [], [])
                                                      , Seq(
                                                          Match(Var("s_14"))
                                                        , Seq(
                                                            Build(Var("v_14"))
                                                          , Seq(
                                                              Match(Var("w_14"))
                                                            , Seq(
                                                                Build(Var("m_14"))
                                                              , Seq(
                                                                  CallT(SVar("desugar_arrow_p__0_1"), [], [Var("p_14")])
                                                                , Seq(
                                                                    Match(Var("t_14"))
                                                                  , Seq(
                                                                      Build(Var("w_14"))
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
                                                                                                  , [ Var("r_14")
                                                                                                    , Anno(
                                                                                                        Op(
                                                                                                          "Cons"
                                                                                                        , [ Anno(
                                                                                                              Op("Var", [Var("n_14")])
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
                                                                                        , Var("s_14")
                                                                                        ]
                                                                                      )
                                                                                    , Op("Nil", [])
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              , Op("Nil", [])
                                                                              )
                                                                            , Anno(Str(">>>"), Op("Nil", []))
                                                                            , Var("t_14")
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
                        ["d_14", "e_14", "f_14", "i_14", "g_14", "j_14", "h_14", "k_14"]
                      , Seq(
                          Match(
                            Anno(
                              Op("ArrAppBin", [Var("e_14"), Var("d_14")])
                            , Wld()
                            )
                          )
                        , Seq(
                            Match(Var("i_14"))
                          , Seq(
                              Build(Var("c_30"))
                            , Seq(
                                CallT(SVar("tuple_pat_0_0"), [], [])
                              , Seq(
                                  Match(Var("f_14"))
                                , Seq(
                                    Build(Var("i_14"))
                                  , Seq(
                                      Match(Var("j_14"))
                                    , Seq(
                                        Build(Var("c_30"))
                                      , Seq(
                                          CallT(SVar("tuple_0_0"), [], [])
                                        , Seq(
                                            Match(Var("g_14"))
                                          , Seq(
                                              Build(Var("j_14"))
                                            , Seq(
                                                Match(Var("k_14"))
                                              , Seq(
                                                  Build(Var("e_14"))
                                                , Seq(
                                                    CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                                  , Seq(
                                                      Match(Var("h_14"))
                                                    , Seq(
                                                        Build(Var("k_14"))
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
                                                                              , [Var("f_14"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                              )
                                                                            , Op("Nil", [])
                                                                            )
                                                                          , Anno(
                                                                              Op(
                                                                                "Product"
                                                                              , [ Anno(
                                                                                    Op(
                                                                                      "ECons"
                                                                                    , [ Var("g_14")
                                                                                      , Anno(
                                                                                          Op(
                                                                                            "Cons"
                                                                                          , [Var("d_14"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                              , Var("h_14")
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
                          [ "s_13"
                          , "t_13"
                          , "u_13"
                          , "v_13"
                          , "w_13"
                          , "y_13"
                          , "x_13"
                          , "z_13"
                          , "a_14"
                          , "b_14"
                          ]
                        , Seq(
                            Match(
                              Anno(
                                Op("ArrForm", [Var("s_13"), Var("t_13")])
                              , Wld()
                              )
                            )
                          , Seq(
                              Match(Var("v_13"))
                            , Seq(
                                Match(Var("y_13"))
                              , Seq(
                                  Build(Var("c_30"))
                                , Seq(
                                    CallT(SVar("tuple_pat_0_0"), [], [])
                                  , Seq(
                                      Match(Var("w_13"))
                                    , Seq(
                                        Build(Var("y_13"))
                                      , Seq(
                                          Match(Var("z_13"))
                                        , Seq(
                                            Build(Var("c_30"))
                                          , Seq(
                                              CallT(SVar("tuple_0_0"), [], [])
                                            , Seq(
                                                Match(Var("x_13"))
                                              , Seq(
                                                  Build(Var("z_13"))
                                                , Seq(
                                                    Build(
                                                      Anno(
                                                        Op(
                                                          "Abs"
                                                        , [ Anno(
                                                              Op(
                                                                "Cons"
                                                              , [Var("w_13"), Anno(Op("Nil", []), Op("Nil", []))]
                                                              )
                                                            , Op("Nil", [])
                                                            )
                                                          , Var("x_13")
                                                          ]
                                                        )
                                                      , Op("Nil", [])
                                                      )
                                                    )
                                                  , Seq(
                                                      Match(Var("u_13"))
                                                    , Seq(
                                                        Build(Var("v_13"))
                                                      , Seq(
                                                          Match(Var("b_14"))
                                                        , Seq(
                                                            Build(Var("t_13"))
                                                          , Seq(
                                                              CallT(
                                                                SVar("map_1_0")
                                                              , [CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])]
                                                              , []
                                                              )
                                                            , Seq(
                                                                Match(Var("a_14"))
                                                              , Seq(
                                                                  Build(Var("b_14"))
                                                                , Seq(
                                                                    Build(
                                                                      Anno(
                                                                        Op("", [Var("s_13"), Var("a_14")])
                                                                      , Op("Nil", [])
                                                                      )
                                                                    )
                                                                  , CallT(SVar("apply_all_0_1"), [], [Var("u_13")])
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            )
                                          )
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
                            ["o_13", "p_13", "q_13"]
                          , Seq(
                              Match(
                                Anno(
                                  Op(
                                    "ArrOpApp"
                                  , [Var("p_13"), Var("o_13"), Var("q_13")]
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
                                          Op("BinCon", [Var("o_13")])
                                        , Op("Nil", [])
                                        )
                                      , Anno(
                                          Op(
                                            "Cons"
                                          , [ Var("p_13")
                                            , Anno(
                                                Op(
                                                  "Cons"
                                                , [Var("q_13"), Anno(Op("Nil", []), Op("Nil", []))]
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
                              , CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                              )
                            )
                          )
                        , Id()
                        , GuardedLChoice(
                            Scope(
                              ["m_13"]
                            , Seq(
                                Match(
                                  Anno(
                                    Op(
                                      "ArrDo"
                                    , [ Anno(
                                          Op(
                                            "ArrStmtList"
                                          , [Anno(Op("ArrCmdStmt", [Var("m_13")]), Wld())]
                                          )
                                        , Wld()
                                        )
                                      ]
                                    )
                                  , Wld()
                                  )
                                )
                              , Seq(
                                  Build(Var("m_13"))
                                , CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                )
                              )
                            )
                          , Id()
                          , GuardedLChoice(
                              Scope(
                                [ "a_13"
                                , "b_13"
                                , "c_13"
                                , "d_13"
                                , "e_13"
                                , "f_13"
                                , "i_13"
                                , "g_13"
                                , "j_13"
                                , "h_13"
                                , "k_13"
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
                                                  , [Anno(Op("ArrLetStmt", [Var("b_13")]), Wld()), Var("a_13")]
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
                                    Match(Var("e_13"))
                                  , Seq(
                                      Build(Var("b_13"))
                                    , Seq(
                                        CallT(SVar("free_decls_vars_0_0"), [], [])
                                      , Seq(
                                          Match(Var("c_13"))
                                        , Seq(
                                            Build(
                                              Anno(
                                                Op("", [Var("c_30"), Var("c_13")])
                                              , Op("Nil", [])
                                              )
                                            )
                                          , Seq(
                                              CallT(SVar("conc_0_0"), [], [])
                                            , Seq(
                                                Match(Var("d_13"))
                                              , Seq(
                                                  Build(Var("e_13"))
                                                , Seq(
                                                    Match(Var("i_13"))
                                                  , Seq(
                                                      Build(Var("c_30"))
                                                    , Seq(
                                                        CallT(SVar("tuple_pat_0_0"), [], [])
                                                      , Seq(
                                                          Match(Var("f_13"))
                                                        , Seq(
                                                            Build(Var("i_13"))
                                                          , Seq(
                                                              Match(Var("j_13"))
                                                            , Seq(
                                                                Build(Var("d_13"))
                                                              , Seq(
                                                                  CallT(SVar("tuple_0_0"), [], [])
                                                                , Seq(
                                                                    Match(Var("g_13"))
                                                                  , Seq(
                                                                      Build(Var("j_13"))
                                                                    , Seq(
                                                                        Match(Var("k_13"))
                                                                      , Seq(
                                                                          Build(
                                                                            Anno(
                                                                              Op(
                                                                                "ArrDo"
                                                                              , [Anno(
                                                                                   Op("ArrStmtList", [Var("a_13")])
                                                                                 , Op("Nil", [])
                                                                                 )]
                                                                              )
                                                                            , Op("Nil", [])
                                                                            )
                                                                          )
                                                                        , Seq(
                                                                            CallT(SVar("desugar_arrow_p__0_1"), [], [Var("d_13")])
                                                                          , Seq(
                                                                              Match(Var("h_13"))
                                                                            , Seq(
                                                                                Build(Var("k_13"))
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
                                                                                                      , [Var("f_13"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                      )
                                                                                                    , Op("Nil", [])
                                                                                                    )
                                                                                                  , Anno(
                                                                                                      Op("Let", [Var("b_13"), Var("g_13")])
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
                                                                                      , Var("h_13")
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
                                  [ "n_12"
                                  , "o_12"
                                  , "p_12"
                                  , "u_12"
                                  , "q_12"
                                  , "v_12"
                                  , "r_12"
                                  , "w_12"
                                  , "s_12"
                                  , "x_12"
                                  , "t_12"
                                  , "y_12"
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
                                                    , [Anno(Op("ArrCmdStmt", [Var("n_12")]), Wld()), Var("o_12")]
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
                                      Match(Var("u_12"))
                                    , Seq(
                                        Build(Var("c_30"))
                                      , Seq(
                                          CallT(SVar("tuple_pat_0_0"), [], [])
                                        , Seq(
                                            Match(Var("p_12"))
                                          , Seq(
                                              Build(Var("u_12"))
                                            , Seq(
                                                Match(Var("v_12"))
                                              , Seq(
                                                  Build(Var("c_30"))
                                                , Seq(
                                                    CallT(SVar("tuple_0_0"), [], [])
                                                  , Seq(
                                                      Match(Var("q_12"))
                                                    , Seq(
                                                        Build(Var("v_12"))
                                                      , Seq(
                                                          Match(Var("w_12"))
                                                        , Seq(
                                                            Build(Var("c_30"))
                                                          , Seq(
                                                              CallT(SVar("tuple_0_0"), [], [])
                                                            , Seq(
                                                                Match(Var("r_12"))
                                                              , Seq(
                                                                  Build(Var("w_12"))
                                                                , Seq(
                                                                    Match(Var("x_12"))
                                                                  , Seq(
                                                                      Build(Var("n_12"))
                                                                    , Seq(
                                                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                                                      , Seq(
                                                                          Match(Var("s_12"))
                                                                        , Seq(
                                                                            Build(Var("x_12"))
                                                                          , Seq(
                                                                              Match(Var("y_12"))
                                                                            , Seq(
                                                                                Build(
                                                                                  Anno(
                                                                                    Op(
                                                                                      "ArrDo"
                                                                                    , [Anno(
                                                                                         Op("ArrStmtList", [Var("o_12")])
                                                                                       , Op("Nil", [])
                                                                                       )]
                                                                                    )
                                                                                  , Op("Nil", [])
                                                                                  )
                                                                                )
                                                                              , Seq(
                                                                                  CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                                                                , Seq(
                                                                                    Match(Var("t_12"))
                                                                                  , Seq(
                                                                                      Build(Var("y_12"))
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
                                                                                                            , [Var("p_12"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                            )
                                                                                                          , Op("Nil", [])
                                                                                                          )
                                                                                                        , Anno(
                                                                                                            Op(
                                                                                                              "Product"
                                                                                                            , [ Anno(
                                                                                                                  Op(
                                                                                                                    "ECons"
                                                                                                                  , [ Var("q_12")
                                                                                                                    , Anno(
                                                                                                                        Op(
                                                                                                                          "Cons"
                                                                                                                        , [Var("r_12"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                                                                        , Var("s_12")
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
                                                                                                        , Var("t_12")
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
                                  [ "s_11"
                                  , "t_11"
                                  , "u_11"
                                  , "v_11"
                                  , "w_11"
                                  , "x_11"
                                  , "y_11"
                                  , "f_12"
                                  , "z_11"
                                  , "g_12"
                                  , "a_12"
                                  , "h_12"
                                  , "b_12"
                                  , "i_12"
                                  , "c_12"
                                  , "j_12"
                                  , "d_12"
                                  , "k_12"
                                  , "e_12"
                                  , "l_12"
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
                                                          Op("ArrBindStmt", [Var("u_11"), Var("s_11")])
                                                        , Wld()
                                                        )
                                                      , Var("t_11")
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
                                      Match(Var("x_11"))
                                    , Seq(
                                        Build(Var("u_11"))
                                      , Seq(
                                          CallT(SVar("free_pat_vars_0_0"), [], [])
                                        , Seq(
                                            Match(Var("v_11"))
                                          , Seq(
                                              Build(
                                                Anno(
                                                  Op("", [Var("v_11"), Var("c_30")])
                                                , Op("Nil", [])
                                                )
                                              )
                                            , Seq(
                                                CallT(SVar("conc_0_0"), [], [])
                                              , Seq(
                                                  Match(Var("w_11"))
                                                , Seq(
                                                    Build(Var("x_11"))
                                                  , Seq(
                                                      Match(Var("f_12"))
                                                    , Seq(
                                                        Build(Var("c_30"))
                                                      , Seq(
                                                          CallT(SVar("tuple_pat_0_0"), [], [])
                                                        , Seq(
                                                            Match(Var("y_11"))
                                                          , Seq(
                                                              Build(Var("f_12"))
                                                            , Seq(
                                                                Match(Var("g_12"))
                                                              , Seq(
                                                                  Build(Var("c_30"))
                                                                , Seq(
                                                                    CallT(SVar("tuple_0_0"), [], [])
                                                                  , Seq(
                                                                      Match(Var("z_11"))
                                                                    , Seq(
                                                                        Build(Var("g_12"))
                                                                      , Seq(
                                                                          Match(Var("h_12"))
                                                                        , Seq(
                                                                            Build(Var("c_30"))
                                                                          , Seq(
                                                                              CallT(SVar("tuple_0_0"), [], [])
                                                                            , Seq(
                                                                                Match(Var("a_12"))
                                                                              , Seq(
                                                                                  Build(Var("h_12"))
                                                                                , Seq(
                                                                                    Match(Var("i_12"))
                                                                                  , Seq(
                                                                                      Build(Var("s_11"))
                                                                                    , Seq(
                                                                                        CallT(SVar("desugar_arrow_p__0_1"), [], [Var("c_30")])
                                                                                      , Seq(
                                                                                          Match(Var("b_12"))
                                                                                        , Seq(
                                                                                            Build(Var("i_12"))
                                                                                          , Seq(
                                                                                              Match(Var("j_12"))
                                                                                            , Seq(
                                                                                                Build(Var("c_30"))
                                                                                              , Seq(
                                                                                                  CallT(SVar("tuple_pat_0_0"), [], [])
                                                                                                , Seq(
                                                                                                    Match(Var("c_12"))
                                                                                                  , Seq(
                                                                                                      Build(Var("j_12"))
                                                                                                    , Seq(
                                                                                                        Match(Var("k_12"))
                                                                                                      , Seq(
                                                                                                          Build(Var("w_11"))
                                                                                                        , Seq(
                                                                                                            CallT(SVar("tuple_0_0"), [], [])
                                                                                                          , Seq(
                                                                                                              Match(Var("d_12"))
                                                                                                            , Seq(
                                                                                                                Build(Var("k_12"))
                                                                                                              , Seq(
                                                                                                                  Match(Var("l_12"))
                                                                                                                , Seq(
                                                                                                                    Build(
                                                                                                                      Anno(
                                                                                                                        Op(
                                                                                                                          "ArrDo"
                                                                                                                        , [Anno(
                                                                                                                             Op("ArrStmtList", [Var("t_11")])
                                                                                                                           , Op("Nil", [])
                                                                                                                           )]
                                                                                                                        )
                                                                                                                      , Op("Nil", [])
                                                                                                                      )
                                                                                                                    )
                                                                                                                  , Seq(
                                                                                                                      CallT(SVar("desugar_arrow_p__0_1"), [], [Var("w_11")])
                                                                                                                    , Seq(
                                                                                                                        Match(Var("e_12"))
                                                                                                                      , Seq(
                                                                                                                          Build(Var("l_12"))
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
                                                                                                                                                , [Var("y_11"), Anno(Op("Nil", []), Op("Nil", []))]
                                                                                                                                                )
                                                                                                                                              , Op("Nil", [])
                                                                                                                                              )
                                                                                                                                            , Anno(
                                                                                                                                                Op(
                                                                                                                                                  "Product"
                                                                                                                                                , [ Anno(
                                                                                                                                                      Op(
                                                                                                                                                        "ECons"
                                                                                                                                                      , [ Var("z_11")
                                                                                                                                                        , Anno(
                                                                                                                                                            Op(
                                                                                                                                                              "Cons"
                                                                                                                                                            , [Var("a_12"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                                                                                                            , Var("b_12")
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
                                                                                                                                                                  , [ Var("u_11")
                                                                                                                                                                    , Anno(
                                                                                                                                                                        Op(
                                                                                                                                                                          "Cons"
                                                                                                                                                                        , [Var("c_12"), Anno(Op("Nil", []), Op("Nil", []))]
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
                                                                                                                                                        , Var("d_12")
                                                                                                                                                        ]
                                                                                                                                                      )
                                                                                                                                                    , Op("Nil", [])
                                                                                                                                                    )
                                                                                                                                                  ]
                                                                                                                                                )
                                                                                                                                              , Op("Nil", [])
                                                                                                                                              )
                                                                                                                                            , Anno(Str(">>>"), Op("Nil", []))
                                                                                                                                            , Var("e_12")
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
                ["j_16"]
              , Seq(
                  Match(
                    Anno(
                      Op(
                        "Cons"
                      , [Var("j_16"), Anno(Op("Nil", []), Wld())]
                      )
                    , Wld()
                    )
                  )
                , Build(Var("j_16"))
                )
              )
            , Id()
            , Scope(
                ["h_16", "i_16"]
              , Seq(
                  Match(
                    Anno(
                      Op("Cons", [Var("h_16"), Var("i_16")])
                    , Wld()
                    )
                  )
                , Build(
                    Anno(
                      Op("Tuple", [Var("h_16"), Var("i_16")])
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
                      Op(
                        "Product"
                      , [ Anno(
                            Op("ECons", [Var("k_16"), Var("l_16")])
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
                ["n_16"]
              , Seq(
                  Match(
                    Anno(Op("VarFunLHS", [Var("n_16"), Wld()]), Wld())
                  )
                , Build(Var("n_16"))
                )
              )
            ]
          , []
          )
        )
      , SDefT(
          "apply_all_0_1"
        , []
        , [VarDec("d_30", ConstType(Sort("ATerm", [])))]
        , GuardedLChoice(
            Scope(
              ["t_16"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [Var("t_16"), Anno(Op("Nil", []), Wld())]
                    )
                  , Wld()
                  )
                )
              , Build(Var("t_16"))
              )
            )
          , Id()
          , Scope(
              ["p_16", "q_16", "r_16"]
            , Seq(
                Match(
                  Anno(
                    Op(
                      ""
                    , [ Var("p_16")
                      , Anno(
                          Op("Cons", [Var("q_16"), Var("r_16")])
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
                            , [ Var("p_16")
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
                                          , Var("d_30")
                                          ]
                                        )
                                      , Op("Nil", [])
                                      )
                                    , Anno(Str(">>>"), Op("Nil", []))
                                    , Var("q_16")
                                    ]
                                  )
                                , Op("Nil", [])
                                )
                              ]
                            )
                          , Op("Nil", [])
                          )
                        , Var("r_16")
                        ]
                      )
                    , Op("Nil", [])
                    )
                  )
                , CallT(SVar("apply_all_0_1"), [], [Var("d_30")])
                )
              )
            )
          )
        )
      , SDefT(
          "map_1_0"
        , [ VarDec(
              "z_16"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "a_17"
              , []
              , []
              , GuardedLChoice(
                  Match(Anno(Op("Nil", []), Wld()))
                , Id()
                , Scope(
                    ["u_16", "v_16", "w_16", "x_16", "y_16"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("u_16"), Var("v_16")])
                        , Var("y_16")
                        )
                      )
                    , Seq(
                        Build(Var("u_16"))
                      , Seq(
                          CallT(SVar("z_16"), [], [])
                        , Seq(
                            Match(Var("w_16"))
                          , Seq(
                              Build(Var("v_16"))
                            , Seq(
                                CallT(SVar("a_17"), [], [])
                              , Seq(
                                  Match(Var("x_16"))
                                , Build(
                                    Anno(
                                      Op("Cons", [Var("w_16"), Var("x_16")])
                                    , Var("y_16")
                                    )
                                  )
                                )
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
          , CallT(SVar("a_17"), [], [])
          )
        )
      , SDefT(
          "collect_all_1_0"
        , [ VarDec(
              "b_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , CallT(
            SVar("collect_all_2_0")
          , [ CallT(SVar("b_17"), [], [])
            , CallT(SVar("union_0_0"), [], [])
            ]
          , []
          )
        )
      , SDefT(
          "collect_all_2_0"
        , [ VarDec(
              "c_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "e_17"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["f_17", "h_17", "g_17", "i_17"]
                  , Seq(
                      Match(Var("h_17"))
                    , Seq(
                        CallT(SVar("c_17"), [], [])
                      , Seq(
                          Match(Var("f_17"))
                        , Seq(
                            Build(Var("h_17"))
                          , Seq(
                              Match(Var("i_17"))
                            , Seq(
                                CallT(
                                  SVar("crush_3_0")
                                , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                                  , CallT(SVar("d_17"), [], [])
                                  , CallT(SVar("e_17"), [], [])
                                  ]
                                , []
                                )
                              , Seq(
                                  Match(Var("g_17"))
                                , Seq(
                                    Build(Var("i_17"))
                                  , Build(
                                      Anno(
                                        Op("Cons", [Var("f_17"), Var("g_17")])
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
                    , CallT(SVar("d_17"), [], [])
                    , CallT(SVar("e_17"), [], [])
                    ]
                  , []
                  )
                )
              )
            ]
          , CallT(SVar("e_17"), [], [])
          )
        )
      , SDefT(
          "collect_all_3_0"
        , [ VarDec(
              "j_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "m_17"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["n_17", "p_17", "o_17", "q_17"]
                  , Seq(
                      Match(Var("p_17"))
                    , Seq(
                        CallT(SVar("j_17"), [], [])
                      , Seq(
                          Match(Var("n_17"))
                        , Seq(
                            Build(Var("p_17"))
                          , Seq(
                              Match(Var("q_17"))
                            , Seq(
                                CallT(
                                  SVar("crush_3_0")
                                , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                                  , CallT(SVar("k_17"), [], [])
                                  , CallT(SVar("m_17"), [], [])
                                  ]
                                , []
                                )
                              , Seq(
                                  Match(Var("o_17"))
                                , Seq(
                                    Build(Var("q_17"))
                                  , Build(
                                      Anno(
                                        Op("Cons", [Var("n_17"), Var("o_17")])
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
                      CallT(SVar("l_17"), [], [])
                    , CallT(SVar("m_17"), [], [])
                    )
                  , Id()
                  , CallT(
                      SVar("crush_3_0")
                    , [ Build(Anno(Op("Nil", []), Op("Nil", [])))
                      , CallT(SVar("k_17"), [], [])
                      , CallT(SVar("m_17"), [], [])
                      ]
                    , []
                    )
                  )
                )
              )
            ]
          , CallT(SVar("m_17"), [], [])
          )
        )
      , SDefT(
          "crush_3_0"
        , [ VarDec(
              "s_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "u_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_17"]
          , Seq(
              Match(Anno(Explode(Wld(), Var("r_17")), Wld()))
            , Seq(
                Build(Var("r_17"))
              , CallT(
                  SVar("foldr_3_0")
                , [ CallT(SVar("s_17"), [], [])
                  , CallT(SVar("t_17"), [], [])
                  , CallT(SVar("u_17"), [], [])
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
              "x_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_17"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "z_17"
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
            , CallT(SVar("x_17"), [], [])
            )
          , Id()
          , Scope(
              ["v_17", "w_17", "a_18", "c_18", "b_18", "d_18"]
            , Seq(
                Match(
                  Anno(
                    Op("Cons", [Var("v_17"), Var("w_17")])
                  , Wld()
                  )
                )
              , Seq(
                  Match(Var("c_18"))
                , Seq(
                    Build(Var("v_17"))
                  , Seq(
                      CallT(SVar("z_17"), [], [])
                    , Seq(
                        Match(Var("a_18"))
                      , Seq(
                          Build(Var("c_18"))
                        , Seq(
                            Match(Var("d_18"))
                          , Seq(
                              Build(Var("w_17"))
                            , Seq(
                                CallT(
                                  SVar("foldr_3_0")
                                , [ CallT(SVar("x_17"), [], [])
                                  , CallT(SVar("y_17"), [], [])
                                  , CallT(SVar("z_17"), [], [])
                                  ]
                                , []
                                )
                              , Seq(
                                  Match(Var("b_18"))
                                , Seq(
                                    Build(Var("d_18"))
                                  , Seq(
                                      Build(
                                        Anno(
                                          Op("", [Var("a_18"), Var("b_18")])
                                        , Op("Nil", [])
                                        )
                                      )
                                    , CallT(SVar("y_17"), [], [])
                                    )
                                  )
                                )
                              )
                            )
                          )
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
              ["e_18", "f_18"]
            , Seq(
                Match(
                  Anno(
                    Op("", [Var("e_18"), Var("f_18")])
                  , Wld()
                  )
                )
              , Seq(
                  Build(Var("e_18"))
                , CallT(SVar("at_end_1_0"), [Build(Var("f_18"))], [])
                )
              )
            )
          , Id()
          , Scope(
              ["g_18"]
            , Seq(
                Match(
                  Anno(
                    Explode(Anno(Str(""), Wld()), Var("g_18"))
                  , Wld()
                  )
                )
              , Seq(
                  Build(Var("g_18"))
                , CallT(SVar("concat_0_0"), [], [])
                )
              )
            )
          )
        )
      , SDefT(
          "at_end_1_0"
        , [ VarDec(
              "m_18"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "n_18"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["h_18", "i_18", "j_18", "k_18", "l_18"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("h_18"), Var("i_18")])
                        , Var("l_18")
                        )
                      )
                    , Seq(
                        Build(Var("h_18"))
                      , Seq(
                          Match(Var("j_18"))
                        , Seq(
                            Build(Var("i_18"))
                          , Seq(
                              CallT(SVar("n_18"), [], [])
                            , Seq(
                                Match(Var("k_18"))
                              , Build(
                                  Anno(
                                    Op("Cons", [Var("j_18"), Var("k_18")])
                                  , Var("l_18")
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
                  , CallT(SVar("m_18"), [], [])
                  )
                )
              )
            ]
          , CallT(SVar("n_18"), [], [])
          )
        )
      , SDefT(
          "concat_0_0"
        , []
        , []
        , Let(
            [ SDefT(
                "q_18"
              , []
              , []
              , GuardedLChoice(
                  Match(Anno(Op("Nil", []), Wld()))
                , Id()
                , Scope(
                    ["o_18", "p_18"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("o_18"), Var("p_18")])
                        , Wld()
                        )
                      )
                    , Seq(
                        Build(Var("o_18"))
                      , CallT(
                          SVar("at_end_1_0")
                        , [Seq(
                             Build(Var("p_18"))
                           , CallT(SVar("q_18"), [], [])
                           )]
                        , []
                        )
                      )
                    )
                  )
                )
              )
            ]
          , CallT(SVar("q_18"), [], [])
          )
        )
      , SDefT(
          "union_0_0"
        , []
        , []
        , Scope(
            ["r_18", "s_18"]
          , Let(
              [ SDefT(
                  "y_18"
                , []
                , []
                , GuardedLChoice(
                    Seq(
                      Match(Anno(Op("Nil", []), Wld()))
                    , Build(Var("r_18"))
                    )
                  , Id()
                  , GuardedLChoice(
                      Seq(
                        CallT(SVar("HdMember_1_0"), [Build(Var("r_18"))], [])
                      , CallT(SVar("y_18"), [], [])
                      )
                    , Id()
                    , Scope(
                        ["t_18", "u_18", "v_18", "w_18", "x_18"]
                      , Seq(
                          Match(
                            Anno(
                              Op("Cons", [Var("t_18"), Var("u_18")])
                            , Var("x_18")
                            )
                          )
                        , Seq(
                            Build(Var("t_18"))
                          , Seq(
                              Match(Var("v_18"))
                            , Seq(
                                Build(Var("u_18"))
                              , Seq(
                                  CallT(SVar("y_18"), [], [])
                                , Seq(
                                    Match(Var("w_18"))
                                  , Build(
                                      Anno(
                                        Op("Cons", [Var("v_18"), Var("w_18")])
                                      , Var("x_18")
                                      )
                                    )
                                  )
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
                    Op("", [Var("s_18"), Var("r_18")])
                  , Wld()
                  )
                )
              , Seq(
                  Build(Var("s_18"))
                , CallT(SVar("y_18"), [], [])
                )
              )
            )
          )
        )
      , SDefT(
          "HdMember_1_0"
        , [ VarDec(
              "c_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_18", "a_19", "d_19"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("a_19"), Var("z_18")])
                , Wld()
                )
              )
            , Seq(
                Match(Var("d_19"))
              , Seq(
                  CallT(SVar("c_19"), [], [])
                , Seq(
                    CallT(
                      SVar("fetch_1_0")
                    , [ Scope(
                          ["b_19"]
                        , Seq(
                            Match(Var("b_19"))
                          , Seq(
                              Build(
                                Anno(
                                  Op("", [Var("a_19"), Var("b_19")])
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
                  , Seq(Build(Var("d_19")), Build(Var("z_18")))
                  )
                )
              )
            )
          )
        )
      , SDefT(
          "fetch_1_0"
        , [ VarDec(
              "o_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Let(
            [ SDefT(
                "p_19"
              , []
              , []
              , GuardedLChoice(
                  Scope(
                    ["e_19", "f_19", "g_19", "h_19", "i_19"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("e_19"), Var("f_19")])
                        , Var("i_19")
                        )
                      )
                    , Seq(
                        Build(Var("e_19"))
                      , Seq(
                          CallT(SVar("o_19"), [], [])
                        , Seq(
                            Match(Var("g_19"))
                          , Seq(
                              Build(Var("f_19"))
                            , Seq(
                                Match(Var("h_19"))
                              , Build(
                                  Anno(
                                    Op("Cons", [Var("g_19"), Var("h_19")])
                                  , Var("i_19")
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
                    ["j_19", "k_19", "l_19", "m_19", "n_19"]
                  , Seq(
                      Match(
                        Anno(
                          Op("Cons", [Var("j_19"), Var("k_19")])
                        , Var("n_19")
                        )
                      )
                    , Seq(
                        Build(Var("j_19"))
                      , Seq(
                          Match(Var("l_19"))
                        , Seq(
                            Build(Var("k_19"))
                          , Seq(
                              CallT(SVar("p_19"), [], [])
                            , Seq(
                                Match(Var("m_19"))
                              , Build(
                                  Anno(
                                    Op("Cons", [Var("l_19"), Var("m_19")])
                                  , Var("n_19")
                                  )
                                )
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
          , CallT(SVar("p_19"), [], [])
          )
        )
      , SDefT(
          "eq_0_0"
        , []
        , []
        , Scope(
            ["q_19"]
          , Match(
              Anno(
                Op("", [Var("q_19"), Var("q_19")])
              , Wld()
              )
            )
          )
        )
      , SDefT(
          "oncetd_1_0"
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
                  CallT(SVar("r_19"), [], [])
                , Id()
                , One(CallT(SVar("s_19"), [], []))
                )
              )
            ]
          , CallT(SVar("s_19"), [], [])
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
              "x_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["t_19", "u_19", "v_19", "w_19"]
          , Seq(
              Match(Anno(Var("t_19"), Var("u_19")))
            , Seq(
                Build(Var("t_19"))
              , Seq(
                  CallT(SVar("x_19"), [], [])
                , Seq(
                    Match(Var("v_19"))
                  , Seq(
                      Build(Var("u_19"))
                    , Seq(
                        CallT(SVar("y_19"), [], [])
                      , Seq(
                          Match(Var("w_19"))
                        , Build(Anno(Var("v_19"), Var("w_19")))
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
              "z_19"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_30", "e_30", "f_30", "h_30", "i_30"]
          , Seq(
              Match(
                Anno(
                  Op("Conc", [Var("e_30"), Var("f_30")])
                , Var("g_30")
                )
              )
            , Seq(
                Build(Var("e_30"))
              , Seq(
                  CallT(SVar("z_19"), [], [])
                , Seq(
                    Match(Var("h_30"))
                  , Seq(
                      Build(Var("f_30"))
                    , Seq(
                        CallT(SVar("a_20"), [], [])
                      , Seq(
                          Match(Var("i_30"))
                        , Build(
                            Anno(
                              Op("Conc", [Var("h_30"), Var("i_30")])
                            , Var("g_30")
                            )
                          )
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
              "b_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_30", "j_30", "k_30", "m_30", "n_30"]
          , Seq(
              Match(
                Anno(
                  Op("Cons", [Var("j_30"), Var("k_30")])
                , Var("l_30")
                )
              )
            , Seq(
                Build(Var("j_30"))
              , Seq(
                  CallT(SVar("b_20"), [], [])
                , Seq(
                    Match(Var("m_30"))
                  , Seq(
                      Build(Var("k_30"))
                    , Seq(
                        CallT(SVar("c_20"), [], [])
                      , Seq(
                          Match(Var("n_30"))
                        , Build(
                            Anno(
                              Op("Cons", [Var("m_30"), Var("n_30")])
                            , Var("l_30")
                            )
                          )
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
              "d_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_30", "o_30", "p_30", "r_30", "s_30"]
          , Seq(
              Match(
                Anno(
                  Op("StmtSeq", [Var("o_30"), Var("p_30")])
                , Var("q_30")
                )
              )
            , Seq(
                Build(Var("o_30"))
              , Seq(
                  CallT(SVar("d_20"), [], [])
                , Seq(
                    Match(Var("r_30"))
                  , Seq(
                      Build(Var("p_30"))
                    , Seq(
                        CallT(SVar("e_20"), [], [])
                      , Seq(
                          Match(Var("s_30"))
                        , Build(
                            Anno(
                              Op("StmtSeq", [Var("r_30"), Var("s_30")])
                            , Var("q_30")
                            )
                          )
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
              "f_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_30", "t_30", "u_30", "w_30", "x_30"]
          , Seq(
              Match(
                Anno(
                  Op("DeclSeq", [Var("t_30"), Var("u_30")])
                , Var("v_30")
                )
              )
            , Seq(
                Build(Var("t_30"))
              , Seq(
                  CallT(SVar("f_20"), [], [])
                , Seq(
                    Match(Var("w_30"))
                  , Seq(
                      Build(Var("u_30"))
                    , Seq(
                        CallT(SVar("g_20"), [], [])
                      , Seq(
                          Match(Var("x_30"))
                        , Build(
                            Anno(
                              Op("DeclSeq", [Var("w_30"), Var("x_30")])
                            , Var("v_30")
                            )
                          )
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
              "h_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_31", "y_30", "z_30", "b_31", "c_31"]
          , Seq(
              Match(
                Anno(
                  Op("AltSeq", [Var("y_30"), Var("z_30")])
                , Var("a_31")
                )
              )
            , Seq(
                Build(Var("y_30"))
              , Seq(
                  CallT(SVar("h_20"), [], [])
                , Seq(
                    Match(Var("b_31"))
                  , Seq(
                      Build(Var("z_30"))
                    , Seq(
                        CallT(SVar("i_20"), [], [])
                      , Seq(
                          Match(Var("c_31"))
                        , Build(
                            Anno(
                              Op("AltSeq", [Var("b_31"), Var("c_31")])
                            , Var("a_31")
                            )
                          )
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
              "j_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_31", "d_31", "e_31", "g_31", "h_31"]
          , Seq(
              Match(
                Anno(
                  Op("TopdeclSeq", [Var("d_31"), Var("e_31")])
                , Var("f_31")
                )
              )
            , Seq(
                Build(Var("d_31"))
              , Seq(
                  CallT(SVar("j_20"), [], [])
                , Seq(
                    Match(Var("g_31"))
                  , Seq(
                      Build(Var("e_31"))
                    , Seq(
                        CallT(SVar("k_20"), [], [])
                      , Seq(
                          Match(Var("h_31"))
                        , Build(
                            Anno(
                              Op("TopdeclSeq", [Var("g_31"), Var("h_31")])
                            , Var("f_31")
                            )
                          )
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
              "l_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "m_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["k_31", "i_31", "j_31", "l_31", "m_31"]
          , Seq(
              Match(
                Anno(
                  Op("ImportdeclSeq", [Var("i_31"), Var("j_31")])
                , Var("k_31")
                )
              )
            , Seq(
                Build(Var("i_31"))
              , Seq(
                  CallT(SVar("l_20"), [], [])
                , Seq(
                    Match(Var("l_31"))
                  , Seq(
                      Build(Var("j_31"))
                    , Seq(
                        CallT(SVar("m_20"), [], [])
                      , Seq(
                          Match(Var("m_31"))
                        , Build(
                            Anno(
                              Op("ImportdeclSeq", [Var("l_31"), Var("m_31")])
                            , Var("k_31")
                            )
                          )
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
              "n_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_31", "n_31", "p_31"]
          , Seq(
              Match(
                Anno(Op("FloatHash", [Var("n_31")]), Var("o_31"))
              )
            , Seq(
                Build(Var("n_31"))
              , Seq(
                  CallT(SVar("n_20"), [], [])
                , Seq(
                    Match(Var("p_31"))
                  , Build(
                      Anno(Op("FloatHash", [Var("p_31")]), Var("o_31"))
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
              "o_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_31", "q_31", "s_31"]
          , Seq(
              Match(
                Anno(Op("IntegerHash", [Var("q_31")]), Var("r_31"))
              )
            , Seq(
                Build(Var("q_31"))
              , Seq(
                  CallT(SVar("o_20"), [], [])
                , Seq(
                    Match(Var("s_31"))
                  , Build(
                      Anno(Op("IntegerHash", [Var("s_31")]), Var("r_31"))
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
              "p_20"
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
                Anno(Op("StringHash", [Var("t_31")]), Var("u_31"))
              )
            , Seq(
                Build(Var("t_31"))
              , Seq(
                  CallT(SVar("p_20"), [], [])
                , Seq(
                    Match(Var("v_31"))
                  , Build(
                      Anno(Op("StringHash", [Var("v_31")]), Var("u_31"))
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
              "q_20"
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
                Anno(Op("CharHash", [Var("w_31")]), Var("x_31"))
              )
            , Seq(
                Build(Var("w_31"))
              , Seq(
                  CallT(SVar("q_20"), [], [])
                , Seq(
                    Match(Var("y_31"))
                  , Build(
                      Anno(Op("CharHash", [Var("y_31")]), Var("x_31"))
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
              "r_20"
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
                Anno(Op("FlexibleContext", [Var("z_31")]), Var("a_32"))
              )
            , Seq(
                Build(Var("z_31"))
              , Seq(
                  CallT(SVar("r_20"), [], [])
                , Seq(
                    Match(Var("b_32"))
                  , Build(
                      Anno(Op("FlexibleContext", [Var("b_32")]), Var("a_32"))
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
              "s_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "t_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_32", "c_32", "d_32", "f_32", "g_32"]
          , Seq(
              Match(
                Anno(
                  Op("SimpleClass", [Var("c_32"), Var("d_32")])
                , Var("e_32")
                )
              )
            , Seq(
                Build(Var("c_32"))
              , Seq(
                  CallT(SVar("s_20"), [], [])
                , Seq(
                    Match(Var("f_32"))
                  , Seq(
                      Build(Var("d_32"))
                    , Seq(
                        CallT(SVar("t_20"), [], [])
                      , Seq(
                          Match(Var("g_32"))
                        , Build(
                            Anno(
                              Op("SimpleClass", [Var("f_32"), Var("g_32")])
                            , Var("e_32")
                            )
                          )
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
              "u_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "v_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_32", "h_32", "i_32", "k_32", "l_32"]
          , Seq(
              Match(
                Anno(
                  Op("Class", [Var("h_32"), Var("i_32")])
                , Var("j_32")
                )
              )
            , Seq(
                Build(Var("h_32"))
              , Seq(
                  CallT(SVar("u_20"), [], [])
                , Seq(
                    Match(Var("k_32"))
                  , Seq(
                      Build(Var("i_32"))
                    , Seq(
                        CallT(SVar("v_20"), [], [])
                      , Seq(
                          Match(Var("l_32"))
                        , Build(
                            Anno(
                              Op("Class", [Var("k_32"), Var("l_32")])
                            , Var("j_32")
                            )
                          )
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
              "w_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_32", "m_32", "o_32"]
          , Seq(
              Match(
                Anno(Op("StmtList", [Var("m_32")]), Var("n_32"))
              )
            , Seq(
                Build(Var("m_32"))
              , Seq(
                  CallT(SVar("w_20"), [], [])
                , Seq(
                    Match(Var("o_32"))
                  , Build(
                      Anno(Op("StmtList", [Var("o_32")]), Var("n_32"))
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
            ["r_32", "p_32", "q_32", "s_32", "t_32"]
          , Seq(
              Match(
                Anno(
                  Op("FBind", [Var("p_32"), Var("q_32")])
                , Var("r_32")
                )
              )
            , Seq(
                Build(Var("p_32"))
              , Seq(
                  CallT(SVar("x_20"), [], [])
                , Seq(
                    Match(Var("s_32"))
                  , Seq(
                      Build(Var("q_32"))
                    , Seq(
                        CallT(SVar("y_20"), [], [])
                      , Seq(
                          Match(Var("t_32"))
                        , Build(
                            Anno(
                              Op("FBind", [Var("s_32"), Var("t_32")])
                            , Var("r_32")
                            )
                          )
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
              "z_20"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_32", "u_32", "w_32"]
          , Seq(
              Match(
                Anno(Op("LetStmt", [Var("u_32")]), Var("v_32"))
              )
            , Seq(
                Build(Var("u_32"))
              , Seq(
                  CallT(SVar("z_20"), [], [])
                , Seq(
                    Match(Var("w_32"))
                  , Build(
                      Anno(Op("LetStmt", [Var("w_32")]), Var("v_32"))
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
              "a_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_32", "x_32", "z_32"]
          , Seq(
              Match(
                Anno(Op("ExpStmt", [Var("x_32")]), Var("y_32"))
              )
            , Seq(
                Build(Var("x_32"))
              , Seq(
                  CallT(SVar("a_21"), [], [])
                , Seq(
                    Match(Var("z_32"))
                  , Build(
                      Anno(Op("ExpStmt", [Var("z_32")]), Var("y_32"))
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
              "b_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_33", "a_33", "b_33", "d_33", "e_33"]
          , Seq(
              Match(
                Anno(
                  Op("BindStmt", [Var("a_33"), Var("b_33")])
                , Var("c_33")
                )
              )
            , Seq(
                Build(Var("a_33"))
              , Seq(
                  CallT(SVar("b_21"), [], [])
                , Seq(
                    Match(Var("d_33"))
                  , Seq(
                      Build(Var("b_33"))
                    , Seq(
                        CallT(SVar("c_21"), [], [])
                      , Seq(
                          Match(Var("e_33"))
                        , Build(
                            Anno(
                              Op("BindStmt", [Var("d_33"), Var("e_33")])
                            , Var("c_33")
                            )
                          )
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
              "d_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_33", "f_33", "g_33", "i_33", "j_33"]
          , Seq(
              Match(
                Anno(
                  Op("ListCompr", [Var("f_33"), Var("g_33")])
                , Var("h_33")
                )
              )
            , Seq(
                Build(Var("f_33"))
              , Seq(
                  CallT(SVar("d_21"), [], [])
                , Seq(
                    Match(Var("i_33"))
                  , Seq(
                      Build(Var("g_33"))
                    , Seq(
                        CallT(SVar("e_21"), [], [])
                      , Seq(
                          Match(Var("j_33"))
                        , Build(
                            Anno(
                              Op("ListCompr", [Var("i_33"), Var("j_33")])
                            , Var("h_33")
                            )
                          )
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
              "f_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["n_33", "k_33", "l_33", "m_33", "o_33", "p_33", "q_33"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ListFirstFromTo"
                  , [Var("k_33"), Var("l_33"), Var("m_33")]
                  )
                , Var("n_33")
                )
              )
            , Seq(
                Build(Var("k_33"))
              , Seq(
                  CallT(SVar("f_21"), [], [])
                , Seq(
                    Match(Var("o_33"))
                  , Seq(
                      Build(Var("l_33"))
                    , Seq(
                        CallT(SVar("g_21"), [], [])
                      , Seq(
                          Match(Var("p_33"))
                        , Seq(
                            Build(Var("m_33"))
                          , Seq(
                              CallT(SVar("h_21"), [], [])
                            , Seq(
                                Match(Var("q_33"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ListFirstFromTo"
                                    , [Var("o_33"), Var("p_33"), Var("q_33")]
                                    )
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
            )
          )
        )
      , SDefT(
          "ListFromTo_2_0"
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
          ]
        , []
        , Scope(
            ["t_33", "r_33", "s_33", "u_33", "v_33"]
          , Seq(
              Match(
                Anno(
                  Op("ListFromTo", [Var("r_33"), Var("s_33")])
                , Var("t_33")
                )
              )
            , Seq(
                Build(Var("r_33"))
              , Seq(
                  CallT(SVar("i_21"), [], [])
                , Seq(
                    Match(Var("u_33"))
                  , Seq(
                      Build(Var("s_33"))
                    , Seq(
                        CallT(SVar("j_21"), [], [])
                      , Seq(
                          Match(Var("v_33"))
                        , Build(
                            Anno(
                              Op("ListFromTo", [Var("u_33"), Var("v_33")])
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
      , SDefT(
          "ListFirstFrom_2_0"
        , [ VarDec(
              "k_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_33", "w_33", "x_33", "z_33", "a_34"]
          , Seq(
              Match(
                Anno(
                  Op("ListFirstFrom", [Var("w_33"), Var("x_33")])
                , Var("y_33")
                )
              )
            , Seq(
                Build(Var("w_33"))
              , Seq(
                  CallT(SVar("k_21"), [], [])
                , Seq(
                    Match(Var("z_33"))
                  , Seq(
                      Build(Var("x_33"))
                    , Seq(
                        CallT(SVar("l_21"), [], [])
                      , Seq(
                          Match(Var("a_34"))
                        , Build(
                            Anno(
                              Op("ListFirstFrom", [Var("z_33"), Var("a_34")])
                            , Var("y_33")
                            )
                          )
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
              "m_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_34", "b_34", "d_34"]
          , Seq(
              Match(
                Anno(Op("ListFrom", [Var("b_34")]), Var("c_34"))
              )
            , Seq(
                Build(Var("b_34"))
              , Seq(
                  CallT(SVar("m_21"), [], [])
                , Seq(
                    Match(Var("d_34"))
                  , Build(
                      Anno(Op("ListFrom", [Var("d_34")]), Var("c_34"))
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
              "n_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_34", "e_34", "g_34"]
          , Seq(
              Match(
                Anno(Op("List", [Var("e_34")]), Var("f_34"))
              )
            , Seq(
                Build(Var("e_34"))
              , Seq(
                  CallT(SVar("n_21"), [], [])
                , Seq(
                    Match(Var("g_34"))
                  , Build(
                      Anno(Op("List", [Var("g_34")]), Var("f_34"))
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
              "o_21"
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
                Anno(Op("QualLet", [Var("h_34")]), Var("i_34"))
              )
            , Seq(
                Build(Var("h_34"))
              , Seq(
                  CallT(SVar("o_21"), [], [])
                , Seq(
                    Match(Var("j_34"))
                  , Build(
                      Anno(Op("QualLet", [Var("j_34")]), Var("i_34"))
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
              "p_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "q_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_34", "k_34", "l_34", "n_34", "o_34"]
          , Seq(
              Match(
                Anno(
                  Op("QualBind", [Var("k_34"), Var("l_34")])
                , Var("m_34")
                )
              )
            , Seq(
                Build(Var("k_34"))
              , Seq(
                  CallT(SVar("p_21"), [], [])
                , Seq(
                    Match(Var("n_34"))
                  , Seq(
                      Build(Var("l_34"))
                    , Seq(
                        CallT(SVar("q_21"), [], [])
                      , Seq(
                          Match(Var("o_34"))
                        , Build(
                            Anno(
                              Op("QualBind", [Var("n_34"), Var("o_34")])
                            , Var("m_34")
                            )
                          )
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
              "r_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_34", "p_34", "q_34", "s_34", "t_34"]
          , Seq(
              Match(
                Anno(
                  Op("PatBind", [Var("p_34"), Var("q_34")])
                , Var("r_34")
                )
              )
            , Seq(
                Build(Var("p_34"))
              , Seq(
                  CallT(SVar("r_21"), [], [])
                , Seq(
                    Match(Var("s_34"))
                  , Seq(
                      Build(Var("q_34"))
                    , Seq(
                        CallT(SVar("s_21"), [], [])
                      , Seq(
                          Match(Var("t_34"))
                        , Build(
                            Anno(
                              Op("PatBind", [Var("s_34"), Var("t_34")])
                            , Var("r_34")
                            )
                          )
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
              "t_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_34", "u_34", "w_34"]
          , Seq(
              Match(
                Anno(Op("LabeledPats", [Var("u_34")]), Var("v_34"))
              )
            , Seq(
                Build(Var("u_34"))
              , Seq(
                  CallT(SVar("t_21"), [], [])
                , Seq(
                    Match(Var("w_34"))
                  , Build(
                      Anno(Op("LabeledPats", [Var("w_34")]), Var("v_34"))
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
              "u_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_34", "x_34", "z_34"]
          , Seq(
              Match(
                Anno(Op("Irrefutable", [Var("x_34")]), Var("y_34"))
              )
            , Seq(
                Build(Var("x_34"))
              , Seq(
                  CallT(SVar("u_21"), [], [])
                , Seq(
                    Match(Var("z_34"))
                  , Build(
                      Anno(Op("Irrefutable", [Var("z_34")]), Var("y_34"))
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
              "v_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "w_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_35", "a_35", "b_35", "d_35", "e_35"]
          , Seq(
              Match(
                Anno(
                  Op("Tuple", [Var("a_35"), Var("b_35")])
                , Var("c_35")
                )
              )
            , Seq(
                Build(Var("a_35"))
              , Seq(
                  CallT(SVar("v_21"), [], [])
                , Seq(
                    Match(Var("d_35"))
                  , Seq(
                      Build(Var("b_35"))
                    , Seq(
                        CallT(SVar("w_21"), [], [])
                      , Seq(
                          Match(Var("e_35"))
                        , Build(
                            Anno(
                              Op("Tuple", [Var("d_35"), Var("e_35")])
                            , Var("c_35")
                            )
                          )
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
              "x_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_35", "f_35", "g_35", "i_35", "j_35"]
          , Seq(
              Match(
                Anno(
                  Op("Labeled", [Var("f_35"), Var("g_35")])
                , Var("h_35")
                )
              )
            , Seq(
                Build(Var("f_35"))
              , Seq(
                  CallT(SVar("x_21"), [], [])
                , Seq(
                    Match(Var("i_35"))
                  , Seq(
                      Build(Var("g_35"))
                    , Seq(
                        CallT(SVar("y_21"), [], [])
                      , Seq(
                          Match(Var("j_35"))
                        , Build(
                            Anno(
                              Op("Labeled", [Var("i_35"), Var("j_35")])
                            , Var("h_35")
                            )
                          )
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
              "z_21"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_35", "k_35", "m_35"]
          , Seq(
              Match(
                Anno(Op("Constr", [Var("k_35")]), Var("l_35"))
              )
            , Seq(
                Build(Var("k_35"))
              , Seq(
                  CallT(SVar("z_21"), [], [])
                , Seq(
                    Match(Var("m_35"))
                  , Build(
                      Anno(Op("Constr", [Var("m_35")]), Var("l_35"))
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
            ["p_35", "n_35", "o_35", "q_35", "r_35"]
          , Seq(
              Match(
                Anno(
                  Op("Named", [Var("n_35"), Var("o_35")])
                , Var("p_35")
                )
              )
            , Seq(
                Build(Var("n_35"))
              , Seq(
                  CallT(SVar("a_22"), [], [])
                , Seq(
                    Match(Var("q_35"))
                  , Seq(
                      Build(Var("o_35"))
                    , Seq(
                        CallT(SVar("b_22"), [], [])
                      , Seq(
                          Match(Var("r_35"))
                        , Build(
                            Anno(
                              Op("Named", [Var("q_35"), Var("r_35")])
                            , Var("p_35")
                            )
                          )
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
              "c_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "d_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_35", "s_35", "t_35", "v_35", "w_35"]
          , Seq(
              Match(
                Anno(
                  Op("ConstrApp", [Var("s_35"), Var("t_35")])
                , Var("u_35")
                )
              )
            , Seq(
                Build(Var("s_35"))
              , Seq(
                  CallT(SVar("c_22"), [], [])
                , Seq(
                    Match(Var("v_35"))
                  , Seq(
                      Build(Var("t_35"))
                    , Seq(
                        CallT(SVar("d_22"), [], [])
                      , Seq(
                          Match(Var("w_35"))
                        , Build(
                            Anno(
                              Op("ConstrApp", [Var("v_35"), Var("w_35")])
                            , Var("u_35")
                            )
                          )
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
              "e_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_35", "x_35", "z_35"]
          , Seq(
              Match(
                Anno(Op("Negation", [Var("x_35")]), Var("y_35"))
              )
            , Seq(
                Build(Var("x_35"))
              , Seq(
                  CallT(SVar("e_22"), [], [])
                , Seq(
                    Match(Var("z_35"))
                  , Build(
                      Anno(Op("Negation", [Var("z_35")]), Var("y_35"))
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
          , VarDec(
              "h_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_36", "a_36", "b_36", "c_36", "e_36", "f_36", "g_36"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "BinOpApp"
                  , [Var("a_36"), Var("b_36"), Var("c_36")]
                  )
                , Var("d_36")
                )
              )
            , Seq(
                Build(Var("a_36"))
              , Seq(
                  CallT(SVar("f_22"), [], [])
                , Seq(
                    Match(Var("e_36"))
                  , Seq(
                      Build(Var("b_36"))
                    , Seq(
                        CallT(SVar("g_22"), [], [])
                      , Seq(
                          Match(Var("f_36"))
                        , Seq(
                            Build(Var("c_36"))
                          , Seq(
                              CallT(SVar("h_22"), [], [])
                            , Seq(
                                Match(Var("g_36"))
                              , Build(
                                  Anno(
                                    Op(
                                      "BinOpApp"
                                    , [Var("e_36"), Var("f_36"), Var("g_36")]
                                    )
                                  , Var("d_36")
                                  )
                                )
                              )
                            )
                          )
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
              "i_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_36", "h_36", "j_36"]
          , Seq(
              Match(
                Anno(Op("DeclList", [Var("h_36")]), Var("i_36"))
              )
            , Seq(
                Build(Var("h_36"))
              , Seq(
                  CallT(SVar("i_22"), [], [])
                , Seq(
                    Match(Var("j_36"))
                  , Build(
                      Anno(Op("DeclList", [Var("j_36")]), Var("i_36"))
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
              "j_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_36", "k_36", "m_36"]
          , Seq(
              Match(
                Anno(Op("Where", [Var("k_36")]), Var("l_36"))
              )
            , Seq(
                Build(Var("k_36"))
              , Seq(
                  CallT(SVar("j_22"), [], [])
                , Seq(
                    Match(Var("m_36"))
                  , Build(
                      Anno(Op("Where", [Var("m_36")]), Var("l_36"))
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
              "k_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_36", "n_36", "o_36", "q_36", "r_36"]
          , Seq(
              Match(
                Anno(
                  Op("NestedFunLHS", [Var("n_36"), Var("o_36")])
                , Var("p_36")
                )
              )
            , Seq(
                Build(Var("n_36"))
              , Seq(
                  CallT(SVar("k_22"), [], [])
                , Seq(
                    Match(Var("q_36"))
                  , Seq(
                      Build(Var("o_36"))
                    , Seq(
                        CallT(SVar("l_22"), [], [])
                      , Seq(
                          Match(Var("r_36"))
                        , Build(
                            Anno(
                              Op("NestedFunLHS", [Var("q_36"), Var("r_36")])
                            , Var("p_36")
                            )
                          )
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
              "m_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["v_36", "s_36", "t_36", "u_36", "w_36", "x_36", "y_36"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "OpFunLHS"
                  , [Var("s_36"), Var("t_36"), Var("u_36")]
                  )
                , Var("v_36")
                )
              )
            , Seq(
                Build(Var("s_36"))
              , Seq(
                  CallT(SVar("m_22"), [], [])
                , Seq(
                    Match(Var("w_36"))
                  , Seq(
                      Build(Var("t_36"))
                    , Seq(
                        CallT(SVar("n_22"), [], [])
                      , Seq(
                          Match(Var("x_36"))
                        , Seq(
                            Build(Var("u_36"))
                          , Seq(
                              CallT(SVar("o_22"), [], [])
                            , Seq(
                                Match(Var("y_36"))
                              , Build(
                                  Anno(
                                    Op(
                                      "OpFunLHS"
                                    , [Var("w_36"), Var("x_36"), Var("y_36")]
                                    )
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
            )
          )
        )
      , SDefT(
          "VarFunLHS_2_0"
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
          ]
        , []
        , Scope(
            ["b_37", "z_36", "a_37", "c_37", "d_37"]
          , Seq(
              Match(
                Anno(
                  Op("VarFunLHS", [Var("z_36"), Var("a_37")])
                , Var("b_37")
                )
              )
            , Seq(
                Build(Var("z_36"))
              , Seq(
                  CallT(SVar("p_22"), [], [])
                , Seq(
                    Match(Var("c_37"))
                  , Seq(
                      Build(Var("a_37"))
                    , Seq(
                        CallT(SVar("q_22"), [], [])
                      , Seq(
                          Match(Var("d_37"))
                        , Build(
                            Anno(
                              Op("VarFunLHS", [Var("c_37"), Var("d_37")])
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
      , SDefT(
          "Guarded_2_0"
        , [ VarDec(
              "r_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_37", "e_37", "f_37", "h_37", "i_37"]
          , Seq(
              Match(
                Anno(
                  Op("Guarded", [Var("e_37"), Var("f_37")])
                , Var("g_37")
                )
              )
            , Seq(
                Build(Var("e_37"))
              , Seq(
                  CallT(SVar("r_22"), [], [])
                , Seq(
                    Match(Var("h_37"))
                  , Seq(
                      Build(Var("f_37"))
                    , Seq(
                        CallT(SVar("s_22"), [], [])
                      , Seq(
                          Match(Var("i_37"))
                        , Build(
                            Anno(
                              Op("Guarded", [Var("h_37"), Var("i_37")])
                            , Var("g_37")
                            )
                          )
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
              "t_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["m_37", "j_37", "k_37", "l_37", "n_37", "o_37", "p_37"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "GdValdef"
                  , [Var("j_37"), Var("k_37"), Var("l_37")]
                  )
                , Var("m_37")
                )
              )
            , Seq(
                Build(Var("j_37"))
              , Seq(
                  CallT(SVar("t_22"), [], [])
                , Seq(
                    Match(Var("n_37"))
                  , Seq(
                      Build(Var("k_37"))
                    , Seq(
                        CallT(SVar("u_22"), [], [])
                      , Seq(
                          Match(Var("o_37"))
                        , Seq(
                            Build(Var("l_37"))
                          , Seq(
                              CallT(SVar("v_22"), [], [])
                            , Seq(
                                Match(Var("p_37"))
                              , Build(
                                  Anno(
                                    Op(
                                      "GdValdef"
                                    , [Var("n_37"), Var("o_37"), Var("p_37")]
                                    )
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
            )
          )
        )
      , SDefT(
          "Valdef_3_0"
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
            ["t_37", "q_37", "r_37", "s_37", "u_37", "v_37", "w_37"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Valdef"
                  , [Var("q_37"), Var("r_37"), Var("s_37")]
                  )
                , Var("t_37")
                )
              )
            , Seq(
                Build(Var("q_37"))
              , Seq(
                  CallT(SVar("w_22"), [], [])
                , Seq(
                    Match(Var("u_37"))
                  , Seq(
                      Build(Var("r_37"))
                    , Seq(
                        CallT(SVar("x_22"), [], [])
                      , Seq(
                          Match(Var("v_37"))
                        , Seq(
                            Build(Var("s_37"))
                          , Seq(
                              CallT(SVar("y_22"), [], [])
                            , Seq(
                                Match(Var("w_37"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Valdef"
                                    , [Var("u_37"), Var("v_37"), Var("w_37")]
                                    )
                                  , Var("t_37")
                                  )
                                )
                              )
                            )
                          )
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
              "z_22"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_37", "x_37", "z_37"]
          , Seq(
              Match(
                Anno(Op("AltList", [Var("x_37")]), Var("y_37"))
              )
            , Seq(
                Build(Var("x_37"))
              , Seq(
                  CallT(SVar("z_22"), [], [])
                , Seq(
                    Match(Var("z_37"))
                  , Build(
                      Anno(Op("AltList", [Var("z_37")]), Var("y_37"))
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
            ["c_38", "a_38", "b_38", "d_38", "e_38"]
          , Seq(
              Match(
                Anno(
                  Op("GdPat", [Var("a_38"), Var("b_38")])
                , Var("c_38")
                )
              )
            , Seq(
                Build(Var("a_38"))
              , Seq(
                  CallT(SVar("a_23"), [], [])
                , Seq(
                    Match(Var("d_38"))
                  , Seq(
                      Build(Var("b_38"))
                    , Seq(
                        CallT(SVar("b_23"), [], [])
                      , Seq(
                          Match(Var("e_38"))
                        , Build(
                            Anno(
                              Op("GdPat", [Var("d_38"), Var("e_38")])
                            , Var("c_38")
                            )
                          )
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
              "c_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["i_38", "f_38", "g_38", "h_38", "j_38", "k_38", "l_38"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "GdAlt"
                  , [Var("f_38"), Var("g_38"), Var("h_38")]
                  )
                , Var("i_38")
                )
              )
            , Seq(
                Build(Var("f_38"))
              , Seq(
                  CallT(SVar("c_23"), [], [])
                , Seq(
                    Match(Var("j_38"))
                  , Seq(
                      Build(Var("g_38"))
                    , Seq(
                        CallT(SVar("d_23"), [], [])
                      , Seq(
                          Match(Var("k_38"))
                        , Seq(
                            Build(Var("h_38"))
                          , Seq(
                              CallT(SVar("e_23"), [], [])
                            , Seq(
                                Match(Var("l_38"))
                              , Build(
                                  Anno(
                                    Op(
                                      "GdAlt"
                                    , [Var("j_38"), Var("k_38"), Var("l_38")]
                                    )
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
            )
          )
        )
      , SDefT(
          "Alt_3_0"
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
            ["p_38", "m_38", "n_38", "o_38", "q_38", "r_38", "s_38"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Alt"
                  , [Var("m_38"), Var("n_38"), Var("o_38")]
                  )
                , Var("p_38")
                )
              )
            , Seq(
                Build(Var("m_38"))
              , Seq(
                  CallT(SVar("f_23"), [], [])
                , Seq(
                    Match(Var("q_38"))
                  , Seq(
                      Build(Var("n_38"))
                    , Seq(
                        CallT(SVar("g_23"), [], [])
                      , Seq(
                          Match(Var("r_38"))
                        , Seq(
                            Build(Var("o_38"))
                          , Seq(
                              CallT(SVar("h_23"), [], [])
                            , Seq(
                                Match(Var("s_38"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Alt"
                                    , [Var("q_38"), Var("r_38"), Var("s_38")]
                                    )
                                  , Var("p_38")
                                  )
                                )
                              )
                            )
                          )
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
              "i_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_38", "t_38", "v_38"]
          , Seq(
              Match(
                Anno(Op("LabelBinds", [Var("t_38")]), Var("u_38"))
              )
            , Seq(
                Build(Var("t_38"))
              , Seq(
                  CallT(SVar("i_23"), [], [])
                , Seq(
                    Match(Var("v_38"))
                  , Build(
                      Anno(Op("LabelBinds", [Var("v_38")]), Var("u_38"))
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
          , VarDec(
              "l_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_38", "w_38", "x_38", "y_38", "a_39", "b_39", "c_39"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "FixDecl"
                  , [Var("w_38"), Var("x_38"), Var("y_38")]
                  )
                , Var("z_38")
                )
              )
            , Seq(
                Build(Var("w_38"))
              , Seq(
                  CallT(SVar("j_23"), [], [])
                , Seq(
                    Match(Var("a_39"))
                  , Seq(
                      Build(Var("x_38"))
                    , Seq(
                        CallT(SVar("k_23"), [], [])
                      , Seq(
                          Match(Var("b_39"))
                        , Seq(
                            Build(Var("y_38"))
                          , Seq(
                              CallT(SVar("l_23"), [], [])
                            , Seq(
                                Match(Var("c_39"))
                              , Build(
                                  Anno(
                                    Op(
                                      "FixDecl"
                                    , [Var("a_39"), Var("b_39"), Var("c_39")]
                                    )
                                  , Var("z_38")
                                  )
                                )
                              )
                            )
                          )
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
          ]
        , []
        , Scope(
            ["f_39", "d_39", "e_39", "g_39", "h_39"]
          , Seq(
              Match(
                Anno(
                  Op("ECons", [Var("d_39"), Var("e_39")])
                , Var("f_39")
                )
              )
            , Seq(
                Build(Var("d_39"))
              , Seq(
                  CallT(SVar("m_23"), [], [])
                , Seq(
                    Match(Var("g_39"))
                  , Seq(
                      Build(Var("e_39"))
                    , Seq(
                        CallT(SVar("n_23"), [], [])
                      , Seq(
                          Match(Var("h_39"))
                        , Build(
                            Anno(
                              Op("ECons", [Var("g_39"), Var("h_39")])
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
      , SDefT(
          "ArrOpApp_3_0"
        , [ VarDec(
              "o_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["l_39", "i_39", "j_39", "k_39", "m_39", "n_39", "o_39"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ArrOpApp"
                  , [Var("i_39"), Var("j_39"), Var("k_39")]
                  )
                , Var("l_39")
                )
              )
            , Seq(
                Build(Var("i_39"))
              , Seq(
                  CallT(SVar("o_23"), [], [])
                , Seq(
                    Match(Var("m_39"))
                  , Seq(
                      Build(Var("j_39"))
                    , Seq(
                        CallT(SVar("p_23"), [], [])
                      , Seq(
                          Match(Var("n_39"))
                        , Seq(
                            Build(Var("k_39"))
                          , Seq(
                              CallT(SVar("q_23"), [], [])
                            , Seq(
                                Match(Var("o_39"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ArrOpApp"
                                    , [Var("m_39"), Var("n_39"), Var("o_39")]
                                    )
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
            )
          )
        )
      , SDefT(
          "ArrForm_2_0"
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
          ]
        , []
        , Scope(
            ["r_39", "p_39", "q_39", "s_39", "t_39"]
          , Seq(
              Match(
                Anno(
                  Op("ArrForm", [Var("p_39"), Var("q_39")])
                , Var("r_39")
                )
              )
            , Seq(
                Build(Var("p_39"))
              , Seq(
                  CallT(SVar("r_23"), [], [])
                , Seq(
                    Match(Var("s_39"))
                  , Seq(
                      Build(Var("q_39"))
                    , Seq(
                        CallT(SVar("s_23"), [], [])
                      , Seq(
                          Match(Var("t_39"))
                        , Build(
                            Anno(
                              Op("ArrForm", [Var("s_39"), Var("t_39")])
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
      , SDefT(
          "ArrAppBin_2_0"
        , [ VarDec(
              "t_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "u_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_39", "u_39", "v_39", "x_39", "y_39"]
          , Seq(
              Match(
                Anno(
                  Op("ArrAppBin", [Var("u_39"), Var("v_39")])
                , Var("w_39")
                )
              )
            , Seq(
                Build(Var("u_39"))
              , Seq(
                  CallT(SVar("t_23"), [], [])
                , Seq(
                    Match(Var("x_39"))
                  , Seq(
                      Build(Var("v_39"))
                    , Seq(
                        CallT(SVar("u_23"), [], [])
                      , Seq(
                          Match(Var("y_39"))
                        , Build(
                            Anno(
                              Op("ArrAppBin", [Var("x_39"), Var("y_39")])
                            , Var("w_39")
                            )
                          )
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
              "v_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_40", "z_39", "b_40"]
          , Seq(
              Match(
                Anno(Op("ArrDo", [Var("z_39")]), Var("a_40"))
              )
            , Seq(
                Build(Var("z_39"))
              , Seq(
                  CallT(SVar("v_23"), [], [])
                , Seq(
                    Match(Var("b_40"))
                  , Build(
                      Anno(Op("ArrDo", [Var("b_40")]), Var("a_40"))
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
            ["e_40", "c_40", "d_40", "f_40", "g_40"]
          , Seq(
              Match(
                Anno(
                  Op("ArrCase", [Var("c_40"), Var("d_40")])
                , Var("e_40")
                )
              )
            , Seq(
                Build(Var("c_40"))
              , Seq(
                  CallT(SVar("w_23"), [], [])
                , Seq(
                    Match(Var("f_40"))
                  , Seq(
                      Build(Var("d_40"))
                    , Seq(
                        CallT(SVar("x_23"), [], [])
                      , Seq(
                          Match(Var("g_40"))
                        , Build(
                            Anno(
                              Op("ArrCase", [Var("f_40"), Var("g_40")])
                            , Var("e_40")
                            )
                          )
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
              "y_23"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["k_40", "h_40", "i_40", "j_40", "l_40", "m_40", "n_40"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ArrIf"
                  , [Var("h_40"), Var("i_40"), Var("j_40")]
                  )
                , Var("k_40")
                )
              )
            , Seq(
                Build(Var("h_40"))
              , Seq(
                  CallT(SVar("y_23"), [], [])
                , Seq(
                    Match(Var("l_40"))
                  , Seq(
                      Build(Var("i_40"))
                    , Seq(
                        CallT(SVar("z_23"), [], [])
                      , Seq(
                          Match(Var("m_40"))
                        , Seq(
                            Build(Var("j_40"))
                          , Seq(
                              CallT(SVar("a_24"), [], [])
                            , Seq(
                                Match(Var("n_40"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ArrIf"
                                    , [Var("l_40"), Var("m_40"), Var("n_40")]
                                    )
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
            )
          )
        )
      , SDefT(
          "ArrLet_2_0"
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
          ]
        , []
        , Scope(
            ["q_40", "o_40", "p_40", "r_40", "s_40"]
          , Seq(
              Match(
                Anno(
                  Op("ArrLet", [Var("o_40"), Var("p_40")])
                , Var("q_40")
                )
              )
            , Seq(
                Build(Var("o_40"))
              , Seq(
                  CallT(SVar("b_24"), [], [])
                , Seq(
                    Match(Var("r_40"))
                  , Seq(
                      Build(Var("p_40"))
                    , Seq(
                        CallT(SVar("c_24"), [], [])
                      , Seq(
                          Match(Var("s_40"))
                        , Build(
                            Anno(
                              Op("ArrLet", [Var("r_40"), Var("s_40")])
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
      , SDefT(
          "ArrAbs_2_0"
        , [ VarDec(
              "d_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_40", "t_40", "u_40", "w_40", "x_40"]
          , Seq(
              Match(
                Anno(
                  Op("ArrAbs", [Var("t_40"), Var("u_40")])
                , Var("v_40")
                )
              )
            , Seq(
                Build(Var("t_40"))
              , Seq(
                  CallT(SVar("d_24"), [], [])
                , Seq(
                    Match(Var("w_40"))
                  , Seq(
                      Build(Var("u_40"))
                    , Seq(
                        CallT(SVar("e_24"), [], [])
                      , Seq(
                          Match(Var("x_40"))
                        , Build(
                            Anno(
                              Op("ArrAbs", [Var("w_40"), Var("x_40")])
                            , Var("v_40")
                            )
                          )
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
              "f_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_41", "y_40", "z_40", "b_41", "c_41"]
          , Seq(
              Match(
                Anno(
                  Op("ArrHigher", [Var("y_40"), Var("z_40")])
                , Var("a_41")
                )
              )
            , Seq(
                Build(Var("y_40"))
              , Seq(
                  CallT(SVar("f_24"), [], [])
                , Seq(
                    Match(Var("b_41"))
                  , Seq(
                      Build(Var("z_40"))
                    , Seq(
                        CallT(SVar("g_24"), [], [])
                      , Seq(
                          Match(Var("c_41"))
                        , Build(
                            Anno(
                              Op("ArrHigher", [Var("b_41"), Var("c_41")])
                            , Var("a_41")
                            )
                          )
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
              "h_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_41", "d_41", "e_41", "g_41", "h_41"]
          , Seq(
              Match(
                Anno(
                  Op("ArrFirst", [Var("d_41"), Var("e_41")])
                , Var("f_41")
                )
              )
            , Seq(
                Build(Var("d_41"))
              , Seq(
                  CallT(SVar("h_24"), [], [])
                , Seq(
                    Match(Var("g_41"))
                  , Seq(
                      Build(Var("e_41"))
                    , Seq(
                        CallT(SVar("i_24"), [], [])
                      , Seq(
                          Match(Var("h_41"))
                        , Build(
                            Anno(
                              Op("ArrFirst", [Var("g_41"), Var("h_41")])
                            , Var("f_41")
                            )
                          )
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
              "j_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["l_41", "i_41", "j_41", "k_41", "m_41", "n_41", "o_41"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Typed"
                  , [Var("i_41"), Var("j_41"), Var("k_41")]
                  )
                , Var("l_41")
                )
              )
            , Seq(
                Build(Var("i_41"))
              , Seq(
                  CallT(SVar("j_24"), [], [])
                , Seq(
                    Match(Var("m_41"))
                  , Seq(
                      Build(Var("j_41"))
                    , Seq(
                        CallT(SVar("k_24"), [], [])
                      , Seq(
                          Match(Var("n_41"))
                        , Seq(
                            Build(Var("k_41"))
                          , Seq(
                              CallT(SVar("l_24"), [], [])
                            , Seq(
                                Match(Var("o_41"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Typed"
                                    , [Var("m_41"), Var("n_41"), Var("o_41")]
                                    )
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
            )
          )
        )
      , SDefT(
          "OpApp_3_0"
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
            ["s_41", "p_41", "q_41", "r_41", "t_41", "u_41", "v_41"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "OpApp"
                  , [Var("p_41"), Var("q_41"), Var("r_41")]
                  )
                , Var("s_41")
                )
              )
            , Seq(
                Build(Var("p_41"))
              , Seq(
                  CallT(SVar("m_24"), [], [])
                , Seq(
                    Match(Var("t_41"))
                  , Seq(
                      Build(Var("q_41"))
                    , Seq(
                        CallT(SVar("n_24"), [], [])
                      , Seq(
                          Match(Var("u_41"))
                        , Seq(
                            Build(Var("r_41"))
                          , Seq(
                              CallT(SVar("o_24"), [], [])
                            , Seq(
                                Match(Var("v_41"))
                              , Build(
                                  Anno(
                                    Op(
                                      "OpApp"
                                    , [Var("t_41"), Var("u_41"), Var("v_41")]
                                    )
                                  , Var("s_41")
                                  )
                                )
                              )
                            )
                          )
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
          ]
        , []
        , Scope(
            ["y_41", "w_41", "x_41", "z_41", "a_42"]
          , Seq(
              Match(
                Anno(
                  Op("AppBin", [Var("w_41"), Var("x_41")])
                , Var("y_41")
                )
              )
            , Seq(
                Build(Var("w_41"))
              , Seq(
                  CallT(SVar("p_24"), [], [])
                , Seq(
                    Match(Var("z_41"))
                  , Seq(
                      Build(Var("x_41"))
                    , Seq(
                        CallT(SVar("q_24"), [], [])
                      , Seq(
                          Match(Var("a_42"))
                        , Build(
                            Anno(
                              Op("AppBin", [Var("z_41"), Var("a_42")])
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
      , SDefT(
          "Case_2_0"
        , [ VarDec(
              "r_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "s_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_42", "b_42", "c_42", "e_42", "f_42"]
          , Seq(
              Match(
                Anno(
                  Op("Case", [Var("b_42"), Var("c_42")])
                , Var("d_42")
                )
              )
            , Seq(
                Build(Var("b_42"))
              , Seq(
                  CallT(SVar("r_24"), [], [])
                , Seq(
                    Match(Var("e_42"))
                  , Seq(
                      Build(Var("c_42"))
                    , Seq(
                        CallT(SVar("s_24"), [], [])
                      , Seq(
                          Match(Var("f_42"))
                        , Build(
                            Anno(
                              Op("Case", [Var("e_42"), Var("f_42")])
                            , Var("d_42")
                            )
                          )
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
              "t_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_42", "g_42", "i_42"]
          , Seq(
              Match(
                Anno(Op("Do", [Var("g_42")]), Var("h_42"))
              )
            , Seq(
                Build(Var("g_42"))
              , Seq(
                  CallT(SVar("t_24"), [], [])
                , Seq(
                    Match(Var("i_42"))
                  , Build(
                      Anno(Op("Do", [Var("i_42")]), Var("h_42"))
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
          , VarDec(
              "w_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_42", "j_42", "k_42", "l_42", "n_42", "o_42", "p_42"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "If"
                  , [Var("j_42"), Var("k_42"), Var("l_42")]
                  )
                , Var("m_42")
                )
              )
            , Seq(
                Build(Var("j_42"))
              , Seq(
                  CallT(SVar("u_24"), [], [])
                , Seq(
                    Match(Var("n_42"))
                  , Seq(
                      Build(Var("k_42"))
                    , Seq(
                        CallT(SVar("v_24"), [], [])
                      , Seq(
                          Match(Var("o_42"))
                        , Seq(
                            Build(Var("l_42"))
                          , Seq(
                              CallT(SVar("w_24"), [], [])
                            , Seq(
                                Match(Var("p_42"))
                              , Build(
                                  Anno(
                                    Op(
                                      "If"
                                    , [Var("n_42"), Var("o_42"), Var("p_42")]
                                    )
                                  , Var("m_42")
                                  )
                                )
                              )
                            )
                          )
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
          ]
        , []
        , Scope(
            ["s_42", "q_42", "r_42", "t_42", "u_42"]
          , Seq(
              Match(
                Anno(
                  Op("Let", [Var("q_42"), Var("r_42")])
                , Var("s_42")
                )
              )
            , Seq(
                Build(Var("q_42"))
              , Seq(
                  CallT(SVar("x_24"), [], [])
                , Seq(
                    Match(Var("t_42"))
                  , Seq(
                      Build(Var("r_42"))
                    , Seq(
                        CallT(SVar("y_24"), [], [])
                      , Seq(
                          Match(Var("u_42"))
                        , Build(
                            Anno(
                              Op("Let", [Var("t_42"), Var("u_42")])
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
      , SDefT(
          "Abs_2_0"
        , [ VarDec(
              "z_24"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["x_42", "v_42", "w_42", "y_42", "z_42"]
          , Seq(
              Match(
                Anno(
                  Op("Abs", [Var("v_42"), Var("w_42")])
                , Var("x_42")
                )
              )
            , Seq(
                Build(Var("v_42"))
              , Seq(
                  CallT(SVar("z_24"), [], [])
                , Seq(
                    Match(Var("y_42"))
                  , Seq(
                      Build(Var("w_42"))
                    , Seq(
                        CallT(SVar("a_25"), [], [])
                      , Seq(
                          Match(Var("z_42"))
                        , Build(
                            Anno(
                              Op("Abs", [Var("y_42"), Var("z_42")])
                            , Var("x_42")
                            )
                          )
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
              "b_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["c_43", "a_43", "b_43", "d_43", "e_43"]
          , Seq(
              Match(
                Anno(
                  Op("RSection", [Var("a_43"), Var("b_43")])
                , Var("c_43")
                )
              )
            , Seq(
                Build(Var("a_43"))
              , Seq(
                  CallT(SVar("b_25"), [], [])
                , Seq(
                    Match(Var("d_43"))
                  , Seq(
                      Build(Var("b_43"))
                    , Seq(
                        CallT(SVar("c_25"), [], [])
                      , Seq(
                          Match(Var("e_43"))
                        , Build(
                            Anno(
                              Op("RSection", [Var("d_43"), Var("e_43")])
                            , Var("c_43")
                            )
                          )
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
              "d_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "e_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_43", "f_43", "g_43", "i_43", "j_43"]
          , Seq(
              Match(
                Anno(
                  Op("LSection", [Var("f_43"), Var("g_43")])
                , Var("h_43")
                )
              )
            , Seq(
                Build(Var("f_43"))
              , Seq(
                  CallT(SVar("d_25"), [], [])
                , Seq(
                    Match(Var("i_43"))
                  , Seq(
                      Build(Var("g_43"))
                    , Seq(
                        CallT(SVar("e_25"), [], [])
                      , Seq(
                          Match(Var("j_43"))
                        , Build(
                            Anno(
                              Op("LSection", [Var("i_43"), Var("j_43")])
                            , Var("h_43")
                            )
                          )
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
              "f_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_43", "k_43", "m_43"]
          , Seq(
              Match(
                Anno(Op("Product", [Var("k_43")]), Var("l_43"))
              )
            , Seq(
                Build(Var("k_43"))
              , Seq(
                  CallT(SVar("f_25"), [], [])
                , Seq(
                    Match(Var("m_43"))
                  , Build(
                      Anno(Op("Product", [Var("m_43")]), Var("l_43"))
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
              "g_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["o_43", "n_43", "p_43"]
          , Seq(
              Match(
                Anno(Op("Lit", [Var("n_43")]), Var("o_43"))
              )
            , Seq(
                Build(Var("n_43"))
              , Seq(
                  CallT(SVar("g_25"), [], [])
                , Seq(
                    Match(Var("p_43"))
                  , Build(
                      Anno(Op("Lit", [Var("p_43")]), Var("o_43"))
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
              "h_25"
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
                Anno(Op("Var", [Var("q_43")]), Var("r_43"))
              )
            , Seq(
                Build(Var("q_43"))
              , Seq(
                  CallT(SVar("h_25"), [], [])
                , Seq(
                    Match(Var("s_43"))
                  , Build(
                      Anno(Op("Var", [Var("s_43")]), Var("r_43"))
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
              "i_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "j_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_43", "t_43", "u_43", "w_43", "x_43"]
          , Seq(
              Match(
                Anno(
                  Op("ArrProcedure", [Var("t_43"), Var("u_43")])
                , Var("v_43")
                )
              )
            , Seq(
                Build(Var("t_43"))
              , Seq(
                  CallT(SVar("i_25"), [], [])
                , Seq(
                    Match(Var("w_43"))
                  , Seq(
                      Build(Var("u_43"))
                    , Seq(
                        CallT(SVar("j_25"), [], [])
                      , Seq(
                          Match(Var("x_43"))
                        , Build(
                            Anno(
                              Op("ArrProcedure", [Var("w_43"), Var("x_43")])
                            , Var("v_43")
                            )
                          )
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
              "k_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "l_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_44", "y_43", "z_43", "b_44", "c_44"]
          , Seq(
              Match(
                Anno(
                  Op("ArrStmtSeq", [Var("y_43"), Var("z_43")])
                , Var("a_44")
                )
              )
            , Seq(
                Build(Var("y_43"))
              , Seq(
                  CallT(SVar("k_25"), [], [])
                , Seq(
                    Match(Var("b_44"))
                  , Seq(
                      Build(Var("z_43"))
                    , Seq(
                        CallT(SVar("l_25"), [], [])
                      , Seq(
                          Match(Var("c_44"))
                        , Build(
                            Anno(
                              Op("ArrStmtSeq", [Var("b_44"), Var("c_44")])
                            , Var("a_44")
                            )
                          )
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
              "m_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_44", "d_44", "f_44"]
          , Seq(
              Match(
                Anno(Op("ArrStmtList", [Var("d_44")]), Var("e_44"))
              )
            , Seq(
                Build(Var("d_44"))
              , Seq(
                  CallT(SVar("m_25"), [], [])
                , Seq(
                    Match(Var("f_44"))
                  , Build(
                      Anno(Op("ArrStmtList", [Var("f_44")]), Var("e_44"))
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
              "n_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["h_44", "g_44", "i_44"]
          , Seq(
              Match(
                Anno(Op("ArrCmdStmt", [Var("g_44")]), Var("h_44"))
              )
            , Seq(
                Build(Var("g_44"))
              , Seq(
                  CallT(SVar("n_25"), [], [])
                , Seq(
                    Match(Var("i_44"))
                  , Build(
                      Anno(Op("ArrCmdStmt", [Var("i_44")]), Var("h_44"))
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
              "o_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "p_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_44", "j_44", "k_44", "m_44", "n_44"]
          , Seq(
              Match(
                Anno(
                  Op("ArrBindStmt", [Var("j_44"), Var("k_44")])
                , Var("l_44")
                )
              )
            , Seq(
                Build(Var("j_44"))
              , Seq(
                  CallT(SVar("o_25"), [], [])
                , Seq(
                    Match(Var("m_44"))
                  , Seq(
                      Build(Var("k_44"))
                    , Seq(
                        CallT(SVar("p_25"), [], [])
                      , Seq(
                          Match(Var("n_44"))
                        , Build(
                            Anno(
                              Op("ArrBindStmt", [Var("m_44"), Var("n_44")])
                            , Var("l_44")
                            )
                          )
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
              "q_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_44", "o_44", "q_44"]
          , Seq(
              Match(
                Anno(Op("ArrLetStmt", [Var("o_44")]), Var("p_44"))
              )
            , Seq(
                Build(Var("o_44"))
              , Seq(
                  CallT(SVar("q_25"), [], [])
                , Seq(
                    Match(Var("q_44"))
                  , Build(
                      Anno(Op("ArrLetStmt", [Var("q_44")]), Var("p_44"))
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
            ["t_44", "r_44", "s_44", "u_44", "v_44"]
          , Seq(
              Match(
                Anno(
                  Op("ArrAltSeq", [Var("r_44"), Var("s_44")])
                , Var("t_44")
                )
              )
            , Seq(
                Build(Var("r_44"))
              , Seq(
                  CallT(SVar("r_25"), [], [])
                , Seq(
                    Match(Var("u_44"))
                  , Seq(
                      Build(Var("s_44"))
                    , Seq(
                        CallT(SVar("s_25"), [], [])
                      , Seq(
                          Match(Var("v_44"))
                        , Build(
                            Anno(
                              Op("ArrAltSeq", [Var("u_44"), Var("v_44")])
                            , Var("t_44")
                            )
                          )
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
              "t_25"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
            ["z_44", "w_44", "x_44", "y_44", "a_45", "b_45", "c_45"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "ArrAlt"
                  , [Var("w_44"), Var("x_44"), Var("y_44")]
                  )
                , Var("z_44")
                )
              )
            , Seq(
                Build(Var("w_44"))
              , Seq(
                  CallT(SVar("t_25"), [], [])
                , Seq(
                    Match(Var("a_45"))
                  , Seq(
                      Build(Var("x_44"))
                    , Seq(
                        CallT(SVar("u_25"), [], [])
                      , Seq(
                          Match(Var("b_45"))
                        , Seq(
                            Build(Var("y_44"))
                          , Seq(
                              CallT(SVar("v_25"), [], [])
                            , Seq(
                                Match(Var("c_45"))
                              , Build(
                                  Anno(
                                    Op(
                                      "ArrAlt"
                                    , [Var("a_45"), Var("b_45"), Var("c_45")]
                                    )
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
            )
          )
        )
      , SDefT(
          "SignDecl_3_0"
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
            ["g_45", "d_45", "e_45", "f_45", "h_45", "i_45", "j_45"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "SignDecl"
                  , [Var("d_45"), Var("e_45"), Var("f_45")]
                  )
                , Var("g_45")
                )
              )
            , Seq(
                Build(Var("d_45"))
              , Seq(
                  CallT(SVar("w_25"), [], [])
                , Seq(
                    Match(Var("h_45"))
                  , Seq(
                      Build(Var("e_45"))
                    , Seq(
                        CallT(SVar("x_25"), [], [])
                      , Seq(
                          Match(Var("i_45"))
                        , Seq(
                            Build(Var("f_45"))
                          , Seq(
                              CallT(SVar("y_25"), [], [])
                            , Seq(
                                Match(Var("j_45"))
                              , Build(
                                  Anno(
                                    Op(
                                      "SignDecl"
                                    , [Var("h_45"), Var("i_45"), Var("j_45")]
                                    )
                                  , Var("g_45")
                                  )
                                )
                              )
                            )
                          )
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
            ["n_45", "k_45", "l_45", "m_45", "o_45", "p_45", "q_45"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Class"
                  , [Var("k_45"), Var("l_45"), Var("m_45")]
                  )
                , Var("n_45")
                )
              )
            , Seq(
                Build(Var("k_45"))
              , Seq(
                  CallT(SVar("z_25"), [], [])
                , Seq(
                    Match(Var("o_45"))
                  , Seq(
                      Build(Var("l_45"))
                    , Seq(
                        CallT(SVar("a_26"), [], [])
                      , Seq(
                          Match(Var("p_45"))
                        , Seq(
                            Build(Var("m_45"))
                          , Seq(
                              CallT(SVar("b_26"), [], [])
                            , Seq(
                                Match(Var("q_45"))
                              , Build(
                                  Anno(
                                    Op(
                                      "Class"
                                    , [Var("o_45"), Var("p_45"), Var("q_45")]
                                    )
                                  , Var("n_45")
                                  )
                                )
                              )
                            )
                          )
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
              "c_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_45", "r_45", "t_45"]
          , Seq(
              Match(
                Anno(Op("SContext", [Var("r_45")]), Var("s_45"))
              )
            , Seq(
                Build(Var("r_45"))
              , Seq(
                  CallT(SVar("c_26"), [], [])
                , Seq(
                    Match(Var("t_45"))
                  , Build(
                      Anno(Op("SContext", [Var("t_45")]), Var("s_45"))
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
              "d_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_45", "u_45", "w_45"]
          , Seq(
              Match(
                Anno(Op("Context", [Var("u_45")]), Var("v_45"))
              )
            , Seq(
                Build(Var("u_45"))
              , Seq(
                  CallT(SVar("d_26"), [], [])
                , Seq(
                    Match(Var("w_45"))
                  , Build(
                      Anno(Op("Context", [Var("w_45")]), Var("v_45"))
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
              "e_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "f_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_45", "x_45", "y_45", "a_46", "b_46"]
          , Seq(
              Match(
                Anno(
                  Op("InstArrow", [Var("x_45"), Var("y_45")])
                , Var("z_45")
                )
              )
            , Seq(
                Build(Var("x_45"))
              , Seq(
                  CallT(SVar("e_26"), [], [])
                , Seq(
                    Match(Var("a_46"))
                  , Seq(
                      Build(Var("y_45"))
                    , Seq(
                        CallT(SVar("f_26"), [], [])
                      , Seq(
                          Match(Var("b_46"))
                        , Build(
                            Anno(
                              Op("InstArrow", [Var("a_46"), Var("b_46")])
                            , Var("z_45")
                            )
                          )
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
              "g_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_46", "c_46", "e_46"]
          , Seq(
              Match(
                Anno(Op("InstList", [Var("c_46")]), Var("d_46"))
              )
            , Seq(
                Build(Var("c_46"))
              , Seq(
                  CallT(SVar("g_26"), [], [])
                , Seq(
                    Match(Var("e_46"))
                  , Build(
                      Anno(Op("InstList", [Var("e_46")]), Var("d_46"))
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
            ["h_46", "f_46", "g_46", "i_46", "j_46"]
          , Seq(
              Match(
                Anno(
                  Op("InstTuple", [Var("f_46"), Var("g_46")])
                , Var("h_46")
                )
              )
            , Seq(
                Build(Var("f_46"))
              , Seq(
                  CallT(SVar("h_26"), [], [])
                , Seq(
                    Match(Var("i_46"))
                  , Seq(
                      Build(Var("g_46"))
                    , Seq(
                        CallT(SVar("i_26"), [], [])
                      , Seq(
                          Match(Var("j_46"))
                        , Build(
                            Anno(
                              Op("InstTuple", [Var("i_46"), Var("j_46")])
                            , Var("h_46")
                            )
                          )
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
              "j_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_46", "k_46", "l_46", "n_46", "o_46"]
          , Seq(
              Match(
                Anno(
                  Op("InstApp", [Var("k_46"), Var("l_46")])
                , Var("m_46")
                )
              )
            , Seq(
                Build(Var("k_46"))
              , Seq(
                  CallT(SVar("j_26"), [], [])
                , Seq(
                    Match(Var("n_46"))
                  , Seq(
                      Build(Var("l_46"))
                    , Seq(
                        CallT(SVar("k_26"), [], [])
                      , Seq(
                          Match(Var("o_46"))
                        , Build(
                            Anno(
                              Op("InstApp", [Var("n_46"), Var("o_46")])
                            , Var("m_46")
                            )
                          )
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
              "l_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["q_46", "p_46", "r_46"]
          , Seq(
              Match(
                Anno(Op("InstCons", [Var("p_46")]), Var("q_46"))
              )
            , Seq(
                Build(Var("p_46"))
              , Seq(
                  CallT(SVar("l_26"), [], [])
                , Seq(
                    Match(Var("r_46"))
                  , Build(
                      Anno(Op("InstCons", [Var("r_46")]), Var("q_46"))
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
          , VarDec(
              "o_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_46", "s_46", "t_46", "u_46", "w_46", "x_46", "y_46"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "InfixConstr"
                  , [Var("s_46"), Var("t_46"), Var("u_46")]
                  )
                , Var("v_46")
                )
              )
            , Seq(
                Build(Var("s_46"))
              , Seq(
                  CallT(SVar("m_26"), [], [])
                , Seq(
                    Match(Var("w_46"))
                  , Seq(
                      Build(Var("t_46"))
                    , Seq(
                        CallT(SVar("n_26"), [], [])
                      , Seq(
                          Match(Var("x_46"))
                        , Seq(
                            Build(Var("u_46"))
                          , Seq(
                              CallT(SVar("o_26"), [], [])
                            , Seq(
                                Match(Var("y_46"))
                              , Build(
                                  Anno(
                                    Op(
                                      "InfixConstr"
                                    , [Var("w_46"), Var("x_46"), Var("y_46")]
                                    )
                                  , Var("v_46")
                                  )
                                )
                              )
                            )
                          )
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
          ]
        , []
        , Scope(
            ["b_47", "z_46", "a_47", "c_47", "d_47"]
          , Seq(
              Match(
                Anno(
                  Op("ConstrDecl", [Var("z_46"), Var("a_47")])
                , Var("b_47")
                )
              )
            , Seq(
                Build(Var("z_46"))
              , Seq(
                  CallT(SVar("p_26"), [], [])
                , Seq(
                    Match(Var("c_47"))
                  , Seq(
                      Build(Var("a_47"))
                    , Seq(
                        CallT(SVar("q_26"), [], [])
                      , Seq(
                          Match(Var("d_47"))
                        , Build(
                            Anno(
                              Op("ConstrDecl", [Var("c_47"), Var("d_47")])
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
      , SDefT(
          "ConstrDecls_1_0"
        , [ VarDec(
              "r_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["f_47", "e_47", "g_47"]
          , Seq(
              Match(
                Anno(Op("ConstrDecls", [Var("e_47")]), Var("f_47"))
              )
            , Seq(
                Build(Var("e_47"))
              , Seq(
                  CallT(SVar("r_26"), [], [])
                , Seq(
                    Match(Var("g_47"))
                  , Build(
                      Anno(Op("ConstrDecls", [Var("g_47")]), Var("f_47"))
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
              "s_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_47", "h_47", "j_47"]
          , Seq(
              Match(
                Anno(Op("Derive", [Var("h_47")]), Var("i_47"))
              )
            , Seq(
                Build(Var("h_47"))
              , Seq(
                  CallT(SVar("s_26"), [], [])
                , Seq(
                    Match(Var("j_47"))
                  , Build(
                      Anno(Op("Derive", [Var("j_47")]), Var("i_47"))
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
              "t_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "u_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_47", "k_47", "l_47", "n_47", "o_47"]
          , Seq(
              Match(
                Anno(
                  Op("TFunBin", [Var("k_47"), Var("l_47")])
                , Var("m_47")
                )
              )
            , Seq(
                Build(Var("k_47"))
              , Seq(
                  CallT(SVar("t_26"), [], [])
                , Seq(
                    Match(Var("n_47"))
                  , Seq(
                      Build(Var("l_47"))
                    , Seq(
                        CallT(SVar("u_26"), [], [])
                      , Seq(
                          Match(Var("o_47"))
                        , Build(
                            Anno(
                              Op("TFunBin", [Var("n_47"), Var("o_47")])
                            , Var("m_47")
                            )
                          )
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
              "v_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "w_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["r_47", "p_47", "q_47", "s_47", "t_47"]
          , Seq(
              Match(
                Anno(
                  Op("TAppBin", [Var("p_47"), Var("q_47")])
                , Var("r_47")
                )
              )
            , Seq(
                Build(Var("p_47"))
              , Seq(
                  CallT(SVar("v_26"), [], [])
                , Seq(
                    Match(Var("s_47"))
                  , Seq(
                      Build(Var("q_47"))
                    , Seq(
                        CallT(SVar("w_26"), [], [])
                      , Seq(
                          Match(Var("t_47"))
                        , Build(
                            Anno(
                              Op("TAppBin", [Var("s_47"), Var("t_47")])
                            , Var("r_47")
                            )
                          )
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
              "x_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_47", "u_47", "w_47"]
          , Seq(
              Match(
                Anno(Op("TProd", [Var("u_47")]), Var("v_47"))
              )
            , Seq(
                Build(Var("u_47"))
              , Seq(
                  CallT(SVar("x_26"), [], [])
                , Seq(
                    Match(Var("w_47"))
                  , Build(
                      Anno(Op("TProd", [Var("w_47")]), Var("v_47"))
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
              "y_26"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_47", "x_47", "z_47"]
          , Seq(
              Match(
                Anno(Op("TList", [Var("x_47")]), Var("y_47"))
              )
            , Seq(
                Build(Var("x_47"))
              , Seq(
                  CallT(SVar("y_26"), [], [])
                , Seq(
                    Match(Var("z_47"))
                  , Build(
                      Anno(Op("TList", [Var("z_47")]), Var("y_47"))
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
              "z_26"
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
                Anno(Op("TVar", [Var("a_48")]), Var("b_48"))
              )
            , Seq(
                Build(Var("a_48"))
              , Seq(
                  CallT(SVar("z_26"), [], [])
                , Seq(
                    Match(Var("c_48"))
                  , Build(
                      Anno(Op("TVar", [Var("c_48")]), Var("b_48"))
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
              "a_27"
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
                Anno(Op("TCon", [Var("d_48")]), Var("e_48"))
              )
            , Seq(
                Build(Var("d_48"))
              , Seq(
                  CallT(SVar("a_27"), [], [])
                , Seq(
                    Match(Var("f_48"))
                  , Build(
                      Anno(Op("TCon", [Var("f_48")]), Var("e_48"))
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
              "b_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "c_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_48", "g_48", "h_48", "j_48", "k_48"]
          , Seq(
              Match(
                Anno(
                  Op("TCons", [Var("g_48"), Var("h_48")])
                , Var("i_48")
                )
              )
            , Seq(
                Build(Var("g_48"))
              , Seq(
                  CallT(SVar("b_27"), [], [])
                , Seq(
                    Match(Var("j_48"))
                  , Seq(
                      Build(Var("h_48"))
                    , Seq(
                        CallT(SVar("c_27"), [], [])
                      , Seq(
                          Match(Var("k_48"))
                        , Build(
                            Anno(
                              Op("TCons", [Var("j_48"), Var("k_48")])
                            , Var("i_48")
                            )
                          )
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
              "d_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["m_48", "l_48", "n_48"]
          , Seq(
              Match(
                Anno(Op("Hiding", [Var("l_48")]), Var("m_48"))
              )
            , Seq(
                Build(Var("l_48"))
              , Seq(
                  CallT(SVar("d_27"), [], [])
                , Seq(
                    Match(Var("n_48"))
                  , Build(
                      Anno(Op("Hiding", [Var("n_48")]), Var("m_48"))
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
              "e_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_48", "o_48", "q_48"]
          , Seq(
              Match(
                Anno(Op("Impspec", [Var("o_48")]), Var("p_48"))
              )
            , Seq(
                Build(Var("o_48"))
              , Seq(
                  CallT(SVar("e_27"), [], [])
                , Seq(
                    Match(Var("q_48"))
                  , Build(
                      Anno(Op("Impspec", [Var("q_48")]), Var("p_48"))
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
              "f_27"
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
                Anno(Op("As", [Var("r_48")]), Var("s_48"))
              )
            , Seq(
                Build(Var("r_48"))
              , Seq(
                  CallT(SVar("f_27"), [], [])
                , Seq(
                    Match(Var("t_48"))
                  , Build(
                      Anno(Op("As", [Var("t_48")]), Var("s_48"))
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
              "g_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "h_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
          ]
        , []
        , Scope(
            [ "z_48"
            , "u_48"
            , "v_48"
            , "w_48"
            , "x_48"
            , "y_48"
            , "a_49"
            , "b_49"
            , "c_49"
            , "d_49"
            , "e_49"
            ]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Import"
                  , [ Var("u_48")
                    , Var("v_48")
                    , Var("w_48")
                    , Var("x_48")
                    , Var("y_48")
                    ]
                  )
                , Var("z_48")
                )
              )
            , Seq(
                Build(Var("u_48"))
              , Seq(
                  CallT(SVar("g_27"), [], [])
                , Seq(
                    Match(Var("a_49"))
                  , Seq(
                      Build(Var("v_48"))
                    , Seq(
                        CallT(SVar("h_27"), [], [])
                      , Seq(
                          Match(Var("b_49"))
                        , Seq(
                            Build(Var("w_48"))
                          , Seq(
                              CallT(SVar("i_27"), [], [])
                            , Seq(
                                Match(Var("c_49"))
                              , Seq(
                                  Build(Var("x_48"))
                                , Seq(
                                    CallT(SVar("j_27"), [], [])
                                  , Seq(
                                      Match(Var("d_49"))
                                    , Seq(
                                        Build(Var("y_48"))
                                      , Seq(
                                          CallT(SVar("k_27"), [], [])
                                        , Seq(
                                            Match(Var("e_49"))
                                          , Build(
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
                                              , Var("z_48")
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
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
              "l_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_49", "f_49", "h_49"]
          , Seq(
              Match(
                Anno(Op("Exports", [Var("f_49")]), Var("g_49"))
              )
            , Seq(
                Build(Var("f_49"))
              , Seq(
                  CallT(SVar("l_27"), [], [])
                , Seq(
                    Match(Var("h_49"))
                  , Build(
                      Anno(Op("Exports", [Var("h_49")]), Var("g_49"))
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
              "m_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["j_49", "i_49", "k_49"]
          , Seq(
              Match(
                Anno(Op("Exportlist", [Var("i_49")]), Var("j_49"))
              )
            , Seq(
                Build(Var("i_49"))
              , Seq(
                  CallT(SVar("m_27"), [], [])
                , Seq(
                    Match(Var("k_49"))
                  , Build(
                      Anno(Op("Exportlist", [Var("k_49")]), Var("j_49"))
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
              "n_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_49", "l_49", "m_49", "o_49", "p_49"]
          , Seq(
              Match(
                Anno(
                  Op("Body", [Var("l_49"), Var("m_49")])
                , Var("n_49")
                )
              )
            , Seq(
                Build(Var("l_49"))
              , Seq(
                  CallT(SVar("n_27"), [], [])
                , Seq(
                    Match(Var("o_49"))
                  , Seq(
                      Build(Var("m_49"))
                    , Seq(
                        CallT(SVar("o_27"), [], [])
                      , Seq(
                          Match(Var("p_49"))
                        , Build(
                            Anno(
                              Op("Body", [Var("o_49"), Var("p_49")])
                            , Var("n_49")
                            )
                          )
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
              "p_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
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
          , VarDec(
              "s_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_49", "q_49", "r_49", "s_49", "t_49", "v_49", "w_49", "x_49", "y_49"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "FlexibleInstance"
                  , [Var("q_49"), Var("r_49"), Var("s_49"), Var("t_49")]
                  )
                , Var("u_49")
                )
              )
            , Seq(
                Build(Var("q_49"))
              , Seq(
                  CallT(SVar("p_27"), [], [])
                , Seq(
                    Match(Var("v_49"))
                  , Seq(
                      Build(Var("r_49"))
                    , Seq(
                        CallT(SVar("q_27"), [], [])
                      , Seq(
                          Match(Var("w_49"))
                        , Seq(
                            Build(Var("s_49"))
                          , Seq(
                              CallT(SVar("r_27"), [], [])
                            , Seq(
                                Match(Var("x_49"))
                              , Seq(
                                  Build(Var("t_49"))
                                , Seq(
                                    CallT(SVar("s_27"), [], [])
                                  , Seq(
                                      Match(Var("y_49"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "FlexibleInstance"
                                          , [Var("v_49"), Var("w_49"), Var("x_49"), Var("y_49")]
                                          )
                                        , Var("u_49")
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
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
              "t_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_50", "z_49", "b_50"]
          , Seq(
              Match(
                Anno(Op("Default", [Var("z_49")]), Var("a_50"))
              )
            , Seq(
                Build(Var("z_49"))
              , Seq(
                  CallT(SVar("t_27"), [], [])
                , Seq(
                    Match(Var("b_50"))
                  , Build(
                      Anno(Op("Default", [Var("b_50")]), Var("a_50"))
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
          , VarDec(
              "w_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "x_27"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["g_50", "c_50", "d_50", "e_50", "f_50", "h_50", "i_50", "j_50", "k_50"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Instance"
                  , [Var("c_50"), Var("d_50"), Var("e_50"), Var("f_50")]
                  )
                , Var("g_50")
                )
              )
            , Seq(
                Build(Var("c_50"))
              , Seq(
                  CallT(SVar("u_27"), [], [])
                , Seq(
                    Match(Var("h_50"))
                  , Seq(
                      Build(Var("d_50"))
                    , Seq(
                        CallT(SVar("v_27"), [], [])
                      , Seq(
                          Match(Var("i_50"))
                        , Seq(
                            Build(Var("e_50"))
                          , Seq(
                              CallT(SVar("w_27"), [], [])
                            , Seq(
                                Match(Var("j_50"))
                              , Seq(
                                  Build(Var("f_50"))
                                , Seq(
                                    CallT(SVar("x_27"), [], [])
                                  , Seq(
                                      Match(Var("k_50"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "Instance"
                                          , [Var("h_50"), Var("i_50"), Var("j_50"), Var("k_50")]
                                          )
                                        , Var("g_50")
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
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
          , VarDec(
              "b_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["p_50", "l_50", "m_50", "n_50", "o_50", "q_50", "r_50", "s_50", "t_50"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Class"
                  , [Var("l_50"), Var("m_50"), Var("n_50"), Var("o_50")]
                  )
                , Var("p_50")
                )
              )
            , Seq(
                Build(Var("l_50"))
              , Seq(
                  CallT(SVar("y_27"), [], [])
                , Seq(
                    Match(Var("q_50"))
                  , Seq(
                      Build(Var("m_50"))
                    , Seq(
                        CallT(SVar("z_27"), [], [])
                      , Seq(
                          Match(Var("r_50"))
                        , Seq(
                            Build(Var("n_50"))
                          , Seq(
                              CallT(SVar("a_28"), [], [])
                            , Seq(
                                Match(Var("s_50"))
                              , Seq(
                                  Build(Var("o_50"))
                                , Seq(
                                    CallT(SVar("b_28"), [], [])
                                  , Seq(
                                      Match(Var("t_50"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "Class"
                                          , [Var("q_50"), Var("r_50"), Var("s_50"), Var("t_50")]
                                          )
                                        , Var("p_50")
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
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
          , VarDec(
              "f_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_50", "u_50", "v_50", "w_50", "x_50", "z_50", "a_51", "b_51", "c_51"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "Data"
                  , [Var("u_50"), Var("v_50"), Var("w_50"), Var("x_50")]
                  )
                , Var("y_50")
                )
              )
            , Seq(
                Build(Var("u_50"))
              , Seq(
                  CallT(SVar("c_28"), [], [])
                , Seq(
                    Match(Var("z_50"))
                  , Seq(
                      Build(Var("v_50"))
                    , Seq(
                        CallT(SVar("d_28"), [], [])
                      , Seq(
                          Match(Var("a_51"))
                        , Seq(
                            Build(Var("w_50"))
                          , Seq(
                              CallT(SVar("e_28"), [], [])
                            , Seq(
                                Match(Var("b_51"))
                              , Seq(
                                  Build(Var("x_50"))
                                , Seq(
                                    CallT(SVar("f_28"), [], [])
                                  , Seq(
                                      Match(Var("c_51"))
                                    , Build(
                                        Anno(
                                          Op(
                                            "Data"
                                          , [Var("z_50"), Var("a_51"), Var("b_51"), Var("c_51")]
                                          )
                                        , Var("y_50")
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
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
            ["g_51", "d_51", "e_51", "f_51", "h_51", "i_51", "j_51"]
          , Seq(
              Match(
                Anno(
                  Op(
                    "TypeDecl"
                  , [Var("d_51"), Var("e_51"), Var("f_51")]
                  )
                , Var("g_51")
                )
              )
            , Seq(
                Build(Var("d_51"))
              , Seq(
                  CallT(SVar("g_28"), [], [])
                , Seq(
                    Match(Var("h_51"))
                  , Seq(
                      Build(Var("e_51"))
                    , Seq(
                        CallT(SVar("h_28"), [], [])
                      , Seq(
                          Match(Var("i_51"))
                        , Seq(
                            Build(Var("f_51"))
                          , Seq(
                              CallT(SVar("i_28"), [], [])
                            , Seq(
                                Match(Var("j_51"))
                              , Build(
                                  Anno(
                                    Op(
                                      "TypeDecl"
                                    , [Var("h_51"), Var("i_51"), Var("j_51")]
                                    )
                                  , Var("g_51")
                                  )
                                )
                              )
                            )
                          )
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
              "j_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["l_51", "k_51", "m_51"]
          , Seq(
              Match(
                Anno(Op("Program", [Var("k_51")]), Var("l_51"))
              )
            , Seq(
                Build(Var("k_51"))
              , Seq(
                  CallT(SVar("j_28"), [], [])
                , Seq(
                    Match(Var("m_51"))
                  , Build(
                      Anno(Op("Program", [Var("m_51")]), Var("l_51"))
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
            ["p_51", "n_51", "o_51", "q_51", "r_51"]
          , Seq(
              Match(
                Anno(
                  Op("Module", [Var("n_51"), Var("o_51")])
                , Var("p_51")
                )
              )
            , Seq(
                Build(Var("n_51"))
              , Seq(
                  CallT(SVar("k_28"), [], [])
                , Seq(
                    Match(Var("q_51"))
                  , Seq(
                      Build(Var("o_51"))
                    , Seq(
                        CallT(SVar("l_28"), [], [])
                      , Seq(
                          Match(Var("r_51"))
                        , Build(
                            Anno(
                              Op("Module", [Var("q_51"), Var("r_51")])
                            , Var("p_51")
                            )
                          )
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
              "m_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "n_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["u_51", "s_51", "t_51", "v_51", "w_51"]
          , Seq(
              Match(
                Anno(
                  Op("ModuleDec", [Var("s_51"), Var("t_51")])
                , Var("u_51")
                )
              )
            , Seq(
                Build(Var("s_51"))
              , Seq(
                  CallT(SVar("m_28"), [], [])
                , Seq(
                    Match(Var("v_51"))
                  , Seq(
                      Build(Var("t_51"))
                    , Seq(
                        CallT(SVar("n_28"), [], [])
                      , Seq(
                          Match(Var("w_51"))
                        , Build(
                            Anno(
                              Op("ModuleDec", [Var("v_51"), Var("w_51")])
                            , Var("u_51")
                            )
                          )
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
              "o_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_51", "x_51", "z_51"]
          , Seq(
              Match(
                Anno(Op("CLitLit", [Var("x_51")]), Var("y_51"))
              )
            , Seq(
                Build(Var("x_51"))
              , Seq(
                  CallT(SVar("o_28"), [], [])
                , Seq(
                    Match(Var("z_51"))
                  , Build(
                      Anno(Op("CLitLit", [Var("z_51")]), Var("y_51"))
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
              "p_28"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["b_52", "a_52", "c_52"]
          , Seq(
              Match(
                Anno(Op("PrimDouble", [Var("a_52")]), Var("b_52"))
              )
            , Seq(
                Build(Var("a_52"))
              , Seq(
                  CallT(SVar("p_28"), [], [])
                , Seq(
                    Match(Var("c_52"))
                  , Build(
                      Anno(Op("PrimDouble", [Var("c_52")]), Var("b_52"))
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
              "q_28"
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
                Anno(Op("PrimFloat", [Var("d_52")]), Var("e_52"))
              )
            , Seq(
                Build(Var("d_52"))
              , Seq(
                  CallT(SVar("q_28"), [], [])
                , Seq(
                    Match(Var("f_52"))
                  , Build(
                      Anno(Op("PrimFloat", [Var("f_52")]), Var("e_52"))
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
              "r_28"
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
                Anno(Op("PrimString", [Var("g_52")]), Var("h_52"))
              )
            , Seq(
                Build(Var("g_52"))
              , Seq(
                  CallT(SVar("r_28"), [], [])
                , Seq(
                    Match(Var("i_52"))
                  , Build(
                      Anno(Op("PrimString", [Var("i_52")]), Var("h_52"))
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
              "s_28"
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
                Anno(Op("PrimChar", [Var("j_52")]), Var("k_52"))
              )
            , Seq(
                Build(Var("j_52"))
              , Seq(
                  CallT(SVar("s_28"), [], [])
                , Seq(
                    Match(Var("l_52"))
                  , Build(
                      Anno(Op("PrimChar", [Var("l_52")]), Var("k_52"))
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
              "t_28"
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
                Anno(Op("PrimInt", [Var("m_52")]), Var("n_52"))
              )
            , Seq(
                Build(Var("m_52"))
              , Seq(
                  CallT(SVar("t_28"), [], [])
                , Seq(
                    Match(Var("o_52"))
                  , Build(
                      Anno(Op("PrimInt", [Var("o_52")]), Var("n_52"))
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
              "u_28"
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
                Anno(Op("Float", [Var("p_52")]), Var("q_52"))
              )
            , Seq(
                Build(Var("p_52"))
              , Seq(
                  CallT(SVar("u_28"), [], [])
                , Seq(
                    Match(Var("r_52"))
                  , Build(
                      Anno(Op("Float", [Var("r_52")]), Var("q_52"))
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
              "v_28"
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
                Anno(Op("Int", [Var("s_52")]), Var("t_52"))
              )
            , Seq(
                Build(Var("s_52"))
              , Seq(
                  CallT(SVar("v_28"), [], [])
                , Seq(
                    Match(Var("u_52"))
                  , Build(
                      Anno(Op("Int", [Var("u_52")]), Var("t_52"))
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
              "w_28"
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
                Anno(Op("HexadecimalEsc", [Var("v_52")]), Var("w_52"))
              )
            , Seq(
                Build(Var("v_52"))
              , Seq(
                  CallT(SVar("w_28"), [], [])
                , Seq(
                    Match(Var("x_52"))
                  , Build(
                      Anno(Op("HexadecimalEsc", [Var("x_52")]), Var("w_52"))
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
              "x_28"
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
                Anno(Op("OctalEsc", [Var("y_52")]), Var("z_52"))
              )
            , Seq(
                Build(Var("y_52"))
              , Seq(
                  CallT(SVar("x_28"), [], [])
                , Seq(
                    Match(Var("a_53"))
                  , Build(
                      Anno(Op("OctalEsc", [Var("a_53")]), Var("z_52"))
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
              "y_28"
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
                Anno(Op("DecimalEsc", [Var("b_53")]), Var("c_53"))
              )
            , Seq(
                Build(Var("b_53"))
              , Seq(
                  CallT(SVar("y_28"), [], [])
                , Seq(
                    Match(Var("d_53"))
                  , Build(
                      Anno(Op("DecimalEsc", [Var("d_53")]), Var("c_53"))
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
              "z_28"
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
                Anno(Op("ASCIIEsc", [Var("e_53")]), Var("f_53"))
              )
            , Seq(
                Build(Var("e_53"))
              , Seq(
                  CallT(SVar("z_28"), [], [])
                , Seq(
                    Match(Var("g_53"))
                  , Build(
                      Anno(Op("ASCIIEsc", [Var("g_53")]), Var("f_53"))
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
              "a_29"
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
                Anno(Op("CharEsc", [Var("h_53")]), Var("i_53"))
              )
            , Seq(
                Build(Var("h_53"))
              , Seq(
                  CallT(SVar("a_29"), [], [])
                , Seq(
                    Match(Var("j_53"))
                  , Build(
                      Anno(Op("CharEsc", [Var("j_53")]), Var("i_53"))
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
              "b_29"
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
                Anno(Op("Gap", [Var("k_53")]), Var("l_53"))
              )
            , Seq(
                Build(Var("k_53"))
              , Seq(
                  CallT(SVar("b_29"), [], [])
                , Seq(
                    Match(Var("m_53"))
                  , Build(
                      Anno(Op("Gap", [Var("m_53")]), Var("l_53"))
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
              "c_29"
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
                Anno(Op("Escape", [Var("n_53")]), Var("o_53"))
              )
            , Seq(
                Build(Var("n_53"))
              , Seq(
                  CallT(SVar("c_29"), [], [])
                , Seq(
                    Match(Var("p_53"))
                  , Build(
                      Anno(Op("Escape", [Var("p_53")]), Var("o_53"))
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
              "d_29"
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
                Anno(Op("String", [Var("q_53")]), Var("r_53"))
              )
            , Seq(
                Build(Var("q_53"))
              , Seq(
                  CallT(SVar("d_29"), [], [])
                , Seq(
                    Match(Var("s_53"))
                  , Build(
                      Anno(Op("String", [Var("s_53")]), Var("r_53"))
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
              "e_29"
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
                Anno(Op("Char", [Var("t_53")]), Var("u_53"))
              )
            , Seq(
                Build(Var("t_53"))
              , Seq(
                  CallT(SVar("e_29"), [], [])
                , Seq(
                    Match(Var("v_53"))
                  , Build(
                      Anno(Op("Char", [Var("v_53")]), Var("u_53"))
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
              "f_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "g_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["y_53", "w_53", "x_53", "z_53", "a_54"]
          , Seq(
              Match(
                Anno(
                  Op("QModId", [Var("w_53"), Var("x_53")])
                , Var("y_53")
                )
              )
            , Seq(
                Build(Var("w_53"))
              , Seq(
                  CallT(SVar("f_29"), [], [])
                , Seq(
                    Match(Var("z_53"))
                  , Seq(
                      Build(Var("x_53"))
                    , Seq(
                        CallT(SVar("g_29"), [], [])
                      , Seq(
                          Match(Var("a_54"))
                        , Build(
                            Anno(
                              Op("QModId", [Var("z_53"), Var("a_54")])
                            , Var("y_53")
                            )
                          )
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
              "h_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "i_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["d_54", "b_54", "c_54", "e_54", "f_54"]
          , Seq(
              Match(
                Anno(
                  Op("QConSym", [Var("b_54"), Var("c_54")])
                , Var("d_54")
                )
              )
            , Seq(
                Build(Var("b_54"))
              , Seq(
                  CallT(SVar("h_29"), [], [])
                , Seq(
                    Match(Var("e_54"))
                  , Seq(
                      Build(Var("c_54"))
                    , Seq(
                        CallT(SVar("i_29"), [], [])
                      , Seq(
                          Match(Var("f_54"))
                        , Build(
                            Anno(
                              Op("QConSym", [Var("e_54"), Var("f_54")])
                            , Var("d_54")
                            )
                          )
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
              "j_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "k_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["i_54", "g_54", "h_54", "j_54", "k_54"]
          , Seq(
              Match(
                Anno(
                  Op("QVarSym", [Var("g_54"), Var("h_54")])
                , Var("i_54")
                )
              )
            , Seq(
                Build(Var("g_54"))
              , Seq(
                  CallT(SVar("j_29"), [], [])
                , Seq(
                    Match(Var("j_54"))
                  , Seq(
                      Build(Var("h_54"))
                    , Seq(
                        CallT(SVar("k_29"), [], [])
                      , Seq(
                          Match(Var("k_54"))
                        , Build(
                            Anno(
                              Op("QVarSym", [Var("j_54"), Var("k_54")])
                            , Var("i_54")
                            )
                          )
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
              "l_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "m_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["n_54", "l_54", "m_54", "o_54", "p_54"]
          , Seq(
              Match(
                Anno(
                  Op("QConId", [Var("l_54"), Var("m_54")])
                , Var("n_54")
                )
              )
            , Seq(
                Build(Var("l_54"))
              , Seq(
                  CallT(SVar("l_29"), [], [])
                , Seq(
                    Match(Var("o_54"))
                  , Seq(
                      Build(Var("m_54"))
                    , Seq(
                        CallT(SVar("m_29"), [], [])
                      , Seq(
                          Match(Var("p_54"))
                        , Build(
                            Anno(
                              Op("QConId", [Var("o_54"), Var("p_54")])
                            , Var("n_54")
                            )
                          )
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
              "n_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "o_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["s_54", "q_54", "r_54", "t_54", "u_54"]
          , Seq(
              Match(
                Anno(
                  Op("QVarId", [Var("q_54"), Var("r_54")])
                , Var("s_54")
                )
              )
            , Seq(
                Build(Var("q_54"))
              , Seq(
                  CallT(SVar("n_29"), [], [])
                , Seq(
                    Match(Var("t_54"))
                  , Seq(
                      Build(Var("r_54"))
                    , Seq(
                        CallT(SVar("o_29"), [], [])
                      , Seq(
                          Match(Var("u_54"))
                        , Build(
                            Anno(
                              Op("QVarId", [Var("t_54"), Var("u_54")])
                            , Var("s_54")
                            )
                          )
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
              "p_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["w_54", "v_54", "x_54"]
          , Seq(
              Match(
                Anno(Op("BinCon", [Var("v_54")]), Var("w_54"))
              )
            , Seq(
                Build(Var("v_54"))
              , Seq(
                  CallT(SVar("p_29"), [], [])
                , Seq(
                    Match(Var("x_54"))
                  , Build(
                      Anno(Op("BinCon", [Var("x_54")]), Var("w_54"))
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
              "q_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["z_54", "y_54", "a_55"]
          , Seq(
              Match(
                Anno(Op("ConsOp", [Var("y_54")]), Var("z_54"))
              )
            , Seq(
                Build(Var("y_54"))
              , Seq(
                  CallT(SVar("q_29"), [], [])
                , Seq(
                    Match(Var("a_55"))
                  , Build(
                      Anno(Op("ConsOp", [Var("a_55")]), Var("z_54"))
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
              "r_29"
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
                Anno(Op("PrefCon", [Var("b_55")]), Var("c_55"))
              )
            , Seq(
                Build(Var("b_55"))
              , Seq(
                  CallT(SVar("r_29"), [], [])
                , Seq(
                    Match(Var("d_55"))
                  , Build(
                      Anno(Op("PrefCon", [Var("d_55")]), Var("c_55"))
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
              "s_29"
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
                Anno(Op("PrefOp", [Var("e_55")]), Var("f_55"))
              )
            , Seq(
                Build(Var("e_55"))
              , Seq(
                  CallT(SVar("s_29"), [], [])
                , Seq(
                    Match(Var("g_55"))
                  , Build(
                      Anno(Op("PrefOp", [Var("g_55")]), Var("f_55"))
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
              "t_29"
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
                Anno(Op("ConOp", [Var("h_55")]), Var("i_55"))
              )
            , Seq(
                Build(Var("h_55"))
              , Seq(
                  CallT(SVar("t_29"), [], [])
                , Seq(
                    Match(Var("j_55"))
                  , Build(
                      Anno(Op("ConOp", [Var("j_55")]), Var("i_55"))
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
              "u_29"
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
                Anno(Op("Op", [Var("k_55")]), Var("l_55"))
              )
            , Seq(
                Build(Var("k_55"))
              , Seq(
                  CallT(SVar("u_29"), [], [])
                , Seq(
                    Match(Var("m_55"))
                  , Build(
                      Anno(Op("Op", [Var("m_55")]), Var("l_55"))
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
              "v_29"
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
                Anno(Op("BinOp", [Var("n_55")]), Var("o_55"))
              )
            , Seq(
                Build(Var("n_55"))
              , Seq(
                  CallT(SVar("v_29"), [], [])
                , Seq(
                    Match(Var("p_55"))
                  , Build(
                      Anno(Op("BinOp", [Var("p_55")]), Var("o_55"))
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
              "w_29"
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
                Anno(Op("Ins", [Var("q_55")]), Var("r_55"))
              )
            , Seq(
                Build(Var("q_55"))
              , Seq(
                  CallT(SVar("w_29"), [], [])
                , Seq(
                    Match(Var("s_55"))
                  , Build(
                      Anno(Op("Ins", [Var("s_55")]), Var("r_55"))
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
              "x_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "y_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["v_55", "t_55", "u_55", "w_55", "x_55"]
          , Seq(
              Match(
                Anno(
                  Op("Snoc", [Var("t_55"), Var("u_55")])
                , Var("v_55")
                )
              )
            , Seq(
                Build(Var("t_55"))
              , Seq(
                  CallT(SVar("x_29"), [], [])
                , Seq(
                    Match(Var("w_55"))
                  , Seq(
                      Build(Var("u_55"))
                    , Seq(
                        CallT(SVar("y_29"), [], [])
                      , Seq(
                          Match(Var("x_55"))
                        , Build(
                            Anno(
                              Op("Snoc", [Var("w_55"), Var("x_55")])
                            , Var("v_55")
                            )
                          )
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
          "_2_0"
        , [ VarDec(
              "z_29"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          , VarDec(
              "a_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["a_56", "y_55", "z_55", "b_56", "c_56"]
          , Seq(
              Match(
                Anno(
                  Op("", [Var("y_55"), Var("z_55")])
                , Var("a_56")
                )
              )
            , Seq(
                Build(Var("y_55"))
              , Seq(
                  CallT(SVar("z_29"), [], [])
                , Seq(
                    Match(Var("b_56"))
                  , Seq(
                      Build(Var("z_55"))
                    , Seq(
                        CallT(SVar("a_30"), [], [])
                      , Seq(
                          Match(Var("c_56"))
                        , Build(
                            Anno(
                              Op("", [Var("b_56"), Var("c_56")])
                            , Var("a_56")
                            )
                          )
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
          "DR__UNDEFINE_1_0"
        , [ VarDec(
              "b_30"
            , FunType(
                [ConstType(Sort("ATerm", []))]
              , ConstType(Sort("ATerm", []))
              )
            )
          ]
        , []
        , Scope(
            ["e_56", "d_56", "f_56"]
          , Seq(
              Match(
                Anno(Op("DR_UNDEFINE", [Var("d_56")]), Var("e_56"))
              )
            , Seq(
                Build(Var("d_56"))
              , Seq(
                  CallT(SVar("b_30"), [], [])
                , Seq(
                    Match(Var("f_56"))
                  , Build(
                      Anno(Op("DR_UNDEFINE", [Var("f_56")]), Var("e_56"))
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
