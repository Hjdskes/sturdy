{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Shared where

import           Prelude hiding (lookup,read,mod,rem,div)

import           Data.List (find,elemIndex)
import           Data.Map (Map)
import qualified Data.Map as Map

import           Control.Category

import           Control.Arrow
import           Control.Arrow.Const
import           Control.Arrow.MaybeEnvironment
import           Control.Arrow.Fail
import           Control.Arrow.Reader
import           Control.Arrow.State
import           Control.Arrow.MaybeStore
import           Control.Arrow.TryCatch
import           Control.Arrow.Utils

import           Text.Printf
import           Syntax

data Exception v = StaticException String | DynamicException v deriving (Eq)

instance Show v => Show (Exception v) where
  show (StaticException s) = "Static: " ++ s
  show (DynamicException v) = "Dynamic: " ++ show v

exceptionToEither :: Exception v -> Either String v
exceptionToEither (StaticException s) = Left s
exceptionToEither (DynamicException v) = Right v

type Addr = Int
type PointerEnv e = e String Addr
type CompilationUnits = Map String CompilationUnit
type Fields = Map FieldSignature Addr
type MethodReader = Method

type CanFail v c = (ArrowChoice c, ArrowFail (Exception v) c)
type CanUseEnv env c = ArrowMaybeEnv String Addr (PointerEnv env) c
type CanUseStore v c = ArrowMaybeStore Addr v c
type CanUseReader c = ArrowReader MethodReader c
type CanUseState c = ArrowState Addr c
type CanUseConst c = ArrowConst (CompilationUnits, Fields) c
type CanCatch e x y c = ArrowTryCatch e x (Maybe y) c

type CanUseMem env v c = (CanUseEnv env c, CanUseStore v c)

type CanInterp env v c = (UseVal v c,
                          UseFlow v c,
                          UseMem env c,
                          CanFail v c,
                          CanUseMem env v c,
                          CanUseConst c,
                          CanUseReader c,
                          CanUseState c,
                          CanCatch (Exception v) EInvoke v c,
                          CanCatch (Exception v) [Statement] v c,
                          CanCatch (Exception v) (Method, Maybe v, [Expr]) v c)

lookupLocal :: (Show name, CanFail val c, ArrowMaybeEnv name addr env c) => c name addr
lookupLocal = proc x -> do
  v <- lookup -< x
  case v of
    Just y -> returnA -< y
    Nothing -> failA -< StaticException $ printf "Variable %s not bounded" (show x)

lookupField :: (UseVal v c, CanFail v c, CanUseConst c) => c FieldSignature Addr
lookupField = proc x -> do
  (_,fields) <- askConst -< ()
  case Map.lookup x fields of
    Just addr -> returnA -< addr
    Nothing -> failA -< StaticException $ printf "Field %s not bounded" (show x)

readVar :: (Show var, CanFail val c, ArrowMaybeStore var val c) => c var val
readVar = proc x -> do
  v <- read -< x
  case v of
    Just y -> returnA -< y
    Nothing -> failA -< StaticException $ printf "Address %s not bounded" (show x)

readCompilationUnit :: (CanFail v c, CanUseConst c) => c String CompilationUnit
readCompilationUnit = proc n -> do
  (compilationUnits, _) <- askConst -< ()
  case Map.lookup n compilationUnits of
    Just x -> returnA -< x
    Nothing -> failA -< StaticException $ printf "CompilationUnit %s not loaded" (show n)

matchesSignature :: Type -> String -> [Type] -> Member -> Bool
matchesSignature retType n argTypes (MethodMember m) =
  methodName m == n && returnType m == retType && parameters m == argTypes
matchesSignature _ _ _ _ = False

readMethod :: (CanFail v c, CanUseConst c) => c MethodSignature Method
readMethod = proc (MethodSignature c retType n argTypes) -> do
  unit <- readCompilationUnit -< c
  case find (matchesSignature retType n argTypes) (fileBody unit) of
    Just (MethodMember m) -> returnA -< m
    _ -> failA -< StaticException $ printf "Method %s not defined for class %s" (show n) (show c)

alloc :: (UseVal v c, CanUseState c, CanUseStore v c) => c v Addr
alloc = proc val -> do
  addr <- getA -< ()
  write -< (addr, val)
  putA -< succ addr
  returnA -< addr

assert :: (CanFail v c) => c (Bool, String) ()
assert = proc (prop, msg) -> if prop
  then returnA -< ()
  else failA -< StaticException msg

evalInvoke :: CanInterp e v c => c EInvoke (Maybe v)
evalInvoke =
  let ev = proc (localName,methodSignature,args) -> do
        method <- readMethod -< methodSignature
        case localName of
          Just n -> do
            assert -< (Static `notElem` methodModifiers method, "Expected a non-static method for non-static invoke")
            this <- lookupLocal >>> readVar -< n
            runMethod -< (method,Just this,args)
          Nothing -> do
            assert -< (Static `elem` methodModifiers method, "Expected a static method for static invoke")
            runMethod -< (method,Nothing,args)
  in proc e -> case e of
    SpecialInvoke localName methodSignature args -> ev -< (Just localName,methodSignature,args)
    VirtualInvoke localName methodSignature args -> ev -< (Just localName,methodSignature,args)
    InterfaceInvoke localName methodSignature args -> ev -< (Just localName,methodSignature,args)
    StaticInvoke methodSignature args -> ev -< (Nothing,methodSignature,args)
    DynamicInvoke _ _ _ _ _ -> failA -< StaticException "DynamicInvoke is not implemented"

eval :: CanInterp e v c => c Expr v
eval = proc e -> case e of
  NewExpr t -> do
    assert -< (isBaseType t, "Expected a base type for new")
    newSimple -< t
  NewArrayExpr t i -> do
    assert -< (isNonvoidType t, "Expected a nonvoid type for newarray")
    v <- eval -< i
    newArray -< (t, [v])
  NewMultiArrayExpr t is -> do
    assert -< (isBaseType t, "Expected a nonvoid base type for newmultiarray")
    vs <- mapA eval -< is
    newArray -< (t, vs)
  CastExpr t i -> do
    v <- eval -< i
    b <- instanceOf -< (v, t)
    cast -< (v,t,b)
  InstanceOfExpr i t -> (first eval) >>> instanceOf -< (i,t)
  InvokeExpr invokeExpr -> do
    v <- tryCatchA evalInvoke (pi2 >>> failA) -< invokeExpr
    case v of
      Just v' -> returnA -< v'
      Nothing -> failA -< StaticException "Method returned nothing"
  ArrayRef l i -> ((lookupLocal >>> readVar) *** eval) >>> readIndex -< (l,i)
  FieldRef l f -> (first (lookupLocal >>> readVar)) >>> readField -< (l,f)
  SignatureRef fieldSignature -> lookupField >>> readVar -< fieldSignature
  BinopExpr i1 op i2 -> do
    v1 <- eval -< i1
    v2 <- eval -< i2
    case op of
      -- and :: c (v,v) v
      -- or :: c (v,v) v
      -- xor :: c (v,v) v
      Rem -> rem -< (v1,v2)
      Mod -> mod -< (v1,v2)
      Cmp -> cmp -< (v1,v2)
      Cmpg -> cmpg -< (v1,v2)
      Cmpl -> cmpl -< (v1,v2)
      Cmpeq -> eq -< (v1,v2)
      Cmpne -> neq -< (v1,v2)
      Cmpgt -> gt -< (v1,v2)
      Cmpge -> ge -< (v1,v2)
      Cmplt -> lt -< (v1,v2)
      Cmple -> le -< (v1,v2)
      -- shl :: c (v,v) v
      -- shr :: c (v,v) v
      -- ushr :: c (v,v) v
      Plus -> plus -< (v1,v2)
      Minus -> minus -< (v1,v2)
      Mult -> mult -< (v1,v2)
      Div -> div -< (v1,v2)
  UnopExpr op i -> do
    v <- eval -< i
    case op of
      Lengthof -> lengthOf -< v
      Neg -> neg -< v
  ThisRef -> eval -< (Local "@this")
  ParameterRef n -> eval -< (Local ("@parameter" ++ show n))
  CaughtExceptionRef -> eval -< (Local "@caughtexception")
  Local localName -> lookupLocal >>> readVar -< localName
  DoubleConstant f -> doubleConstant -< f
  FloatConstant f -> floatConstant -< f
  IntConstant n -> intConstant -< n
  LongConstant f -> longConstant -< f
  NullConstant -> nullConstant -< ()
  StringConstant s -> stringConstant -< s
  ClassConstant c -> classConstant -< c
  MethodHandle _ -> failA -< StaticException "Evaluation of method handles is not implemented"

currentMethodBody :: (UseVal v c, CanFail v c, CanUseReader c) => c () MethodBody
currentMethodBody = proc () -> do
  m <- askA -< ()
  case methodBody m of
    EmptyBody -> failA -< StaticException $ printf "Empty body for method %s" (show m)
    FullBody{} -> returnA -< methodBody m

statementsFromLabel :: (UseVal v c, CanFail v c, CanUseReader c) => c String [Statement]
statementsFromLabel = proc label -> do
  b <- currentMethodBody -< ()
  case Label label `elemIndex` (statements b) of
    Just i -> returnA -< drop i (statements b)
    Nothing -> failA -< StaticException $ printf "Undefined label: %s" label

runCases :: CanInterp e v c => c (v,[CaseStatement]) (Maybe v)
runCases = case_ (statementsFromLabel >>> runStatements)

runStatements :: CanInterp e v c => c [Statement] (Maybe v)
runStatements = proc stmts -> case stmts of
  [] -> returnA -< Nothing
  (stmt:rest) -> case stmt of
    Label _ -> tryCatchA ((\(_:r) -> r) ^>> runStatements) (proc ((Label labelName):stmts, exception) -> do
      case exception of
        StaticException _ -> failA -< exception
        DynamicException val -> do
          body <- currentMethodBody -< ()
          let clauses = filter (\clause -> fromLabel clause == labelName && (Label (toLabel clause)) `elem` stmts) (catchClauses body)
          catch (proc (clause,val) -> do
            env <- getEnv -< ()
            addr <- alloc -< val
            env' <- extendEnv -< ("@caughtexception", addr, env)
            localEnv (statementsFromLabel >>> runStatements) -< (env',withLabel clause)) -< (val, clauses)) -< stmts
    Tableswitch e cases -> (first eval) >>> runCases -< (e, cases)
    Lookupswitch e cases -> (first eval) >>> runCases -< (e, cases)
    Identity localName e _ -> do
      addr <- eval >>> alloc -< e
      env <- getEnv -< ()
      env' <- extendEnv -< (localName, addr, env)
      localEnv runStatements -< (env', rest)
    IdentityNoType localName e -> do
      addr <- eval >>> alloc -< e
      env <- getEnv -< ()
      env' <- extendEnv -< (localName, addr, env)
      localEnv runStatements -< (env', rest)
    Assign var e -> do
      v <- eval -< e
      case var of
        LocalVar l -> do
          (first lookupLocal) >>> write -< (l,v)
          runStatements -< rest
        ReferenceVar ref -> case ref of
          ArrayRef l i -> do
            (first ((lookupLocal >>> readVar) *** eval)) >>> updateIndex -< ((l,i),v)
            runStatements -< rest
          FieldRef l f -> do
            (first (lookupLocal >>> readVar)) >>> updateField -< (l,(f,v))
            runStatements -< rest
          SignatureRef f -> do
            (first lookupField) >>> write -< (f,v)
            runStatements -< rest
          _ -> failA -< StaticException $ printf "Can only assign a reference or a local variable"
    If e label -> do
      v <- eval -< e
      if_ (statementsFromLabel >>> runStatements) runStatements -< (v, (label, rest))
    Goto label -> (statementsFromLabel >>> runStatements) -< label
    -- -- Nop
    Ret e -> case e of
      Just immediate -> eval >>^ (\v -> Just v) -< immediate
      Nothing -> returnA -< Nothing
    Return e -> case e of
      Just immediate -> eval >>^ (\v -> Just v) -< immediate
      Nothing -> returnA -< Nothing
    Throw immediate -> do
      v <- eval -< immediate
      failA -< DynamicException v
    Invoke e -> do
      evalInvoke -< e
      runStatements -< rest
    _ -> runStatements -< rest

createMethodEnv :: (UseVal v c, UseMem e c, CanFail v c, CanUseMem e v c, CanUseState c) => c [(String, v)] (PointerEnv e)
createMethodEnv = proc pairs -> do
  e <- emptyEnv -< ()
  foldA (proc (env, (s,v)) -> do
    addr <- alloc -< v
    extendEnv -< (s, addr, env)) -< (pairs, e)

runMethod :: CanInterp e v c => c (Method, Maybe v, [Expr]) (Maybe v)
runMethod = proc (method,this,args) -> do
  case methodBody method of
    EmptyBody -> returnA -< Nothing
    FullBody{declarations=decs,statements=stmts} -> do
      argVals <- mapA eval -< args
      let thisPair = case this of
            Just x -> [("@this", x)]
            Nothing -> []
      let paramPairs = zip (map (\i -> "@parameter" ++ show i) [0..]) argVals
      decPairs <- mapA (second defaultValue) -< concatMap (\(t, d) -> zip d (repeat t)) decs
      env <- createMethodEnv -< thisPair ++ paramPairs ++ decPairs
      localEnv (localA runStatements) -< (env, (method, stmts))

runProgram :: CanInterp e v c => c [Expr] (Maybe v)
runProgram = proc args -> do
  (units,fields) <- askConst -< ()
  mapA ((second defaultValue) >>> write) -< map (\(FieldSignature _ t _,a) -> (a,t)) (Map.toList fields)
  mapA (proc unit -> do
    let getMethod :: Member -> [Method]
        getMethod (MethodMember m) = [m]
        getMethod _ = []
        getMethods members = concatMap getMethod members
    case find (\m -> methodName m == "<clinit>") $ getMethods (fileBody unit) of
      Just classInitMethod -> runMethod -< (classInitMethod, Nothing, [])
      Nothing -> returnA -< Nothing) -< Map.elems units
  mainMethod <- askA -< ()
  tryCatchA runMethod (pi2 >>> proc exception -> case exception of
    DynamicException v -> do
      v' <- unbox -< v
      failA -< DynamicException v'
    StaticException _ -> failA -< exception) -< (mainMethod, Nothing, args)

class Arrow c => UseVal v c | c -> v where
  doubleConstant :: c Float v
  floatConstant :: c Float v
  intConstant :: c Int v
  longConstant :: c Int v
  nullConstant :: c () v
  stringConstant :: c String v
  classConstant :: c String v
  newSimple :: c Type v
  newArray :: c (Type, [v]) v
  -- and :: c (v,v) v
  -- or :: c (v,v) v
  -- xor :: c (v,v) v
  rem :: c (v,v) v
  mod :: c (v,v) v
  cmp :: c (v,v) v
  cmpg :: c (v,v) v
  cmpl :: c (v,v) v
  eq :: c (v,v) v
  neq :: c (v,v) v
  gt :: c (v,v) v
  ge :: c (v,v) v
  lt :: c (v,v) v
  le :: c (v,v) v
  -- shl :: c (v,v) v
  -- shr :: c (v,v) v
  -- ushr :: c (v,v) v
  plus :: c (v,v) v
  minus :: c (v,v) v
  mult :: c (v,v) v
  div :: c (v,v) v
  lengthOf :: c v v
  neg :: c v v
  unbox :: c v v
  defaultValue :: c Type v
  instanceOf :: c (v,Type) v
  cast :: c (v,Type,v) v
  readIndex :: c (v,v) v
  updateIndex :: c ((v,v),v) ()
  readField :: c (v,FieldSignature) v
  updateField :: c (v,(FieldSignature,v)) ()

class Arrow c => UseFlow v c | c -> v where
  if_ :: c String (Maybe v) -> c [Statement] (Maybe v) -> c (v,(String,[Statement])) (Maybe v)
  case_ :: c String (Maybe v) -> c (v,[CaseStatement]) (Maybe v)
  catch :: c (CatchClause, v) (Maybe v) -> c (v,[CatchClause]) (Maybe v)

class Arrow c => UseMem e c | c -> e where
  emptyEnv :: c () (PointerEnv e)
