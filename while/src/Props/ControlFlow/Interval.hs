{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Arrows #-}
module Props.ControlFlow.Interval where

import WhileLanguage hiding (HasStore(..))
import Vals.Interval.Val

Concrete
Intervbal
Symbolic
+ 2 proofs

Pure
ReadVars
DeadWrites
ControlFlow
FailedReads
+ 4 proofs (some of which can be automated, if not using getProp)

+ glue proves

=> 15 instances


import Props.ControlFlow.Prop

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Interval
import Data.Order
import Data.Error
import Data.Maybe
import Data.List
import Data.GaloisConnection

import Control.Monad.State
import Control.Monad.Except
import Control.Arrow
import Control.Arrow.Fail
import Control.Arrow.Utils

type M = StateT (Store,AProp Val) (Except String)
runM :: [Statement] -> Error String ((), (Store,AProp Val))
runM ss = fromEither $ runExcept $ runStateT (runKleisli run ss) (initStore,initAProp)

runAbstract :: [Statement] -> Error String ()
runAbstract ss = fmap fst $ runM ss

propAbstract :: [Statement] -> Error String (AProp Val)
propAbstract ss = fmap (snd . snd) $ runM ss

getStore :: M Store
getStore = get >>= return . fst

putStore :: Store -> M ()
putStore env = modify (\(x,y) -> (env,y))

modifyStore :: (Store -> Store) -> M ()
modifyStore f = modify (\(x,y) -> (f x,y))

putProp :: AProp Val -> M ()
putProp prop = modify (\(x,y) -> (x,prop))

modifyProp :: (AProp Val -> AProp Val) -> M ()
modifyProp f = modify (\(x,y) -> (x,f y))


instance Run (Kleisli M) Val where
  fixRun f = voidA $ mapA $ f (fixRun f)

  store = Kleisli $ \(x,v,l) -> do
    modifyProp (pushNode $ CFGAssign l v)
    modifyStore (M.insert x v)

  if_ (Kleisli f1) (Kleisli f2) = Kleisli $ \(v,(x,y),l) -> do
    modifyProp (pushNode $ CFGIf l v)
    case v of
      BoolVal True -> f1 x
      BoolVal False -> f2 y
      Top -> (f1 x) ⊔ (f2 y)
      _ -> throwError "Expected boolean as argument for 'if'"

instance Eval (Kleisli M) Val where
  lookup = Kleisli $ \x -> do
    env <- getStore
    case M.lookup x env of
      Just v -> return v
      Nothing -> throwError "variable not found"

  boolLit = arr BoolVal

  and = proc (v1,v2) -> case (v1,v2) of
    (BoolVal False,_) -> returnA -< BoolVal False
    (_,BoolVal False) -> returnA -< BoolVal False
    (BoolVal True,BoolVal True) -> returnA -< BoolVal True
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two booleans as arguments for 'and'"

  or = proc (v1,v2) -> case (v1,v2) of
    (BoolVal True,_) -> returnA -< BoolVal True
    (_,BoolVal True) -> returnA -< BoolVal True
    (BoolVal False,BoolVal False) -> returnA -< BoolVal False
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two booleans as arguments for 'or'"
  
  not = proc v -> case v of
    BoolVal True -> returnA -< BoolVal False
    BoolVal False -> returnA -< BoolVal True
    Top -> returnA -< Top
    _ -> failA -< "Expected a boolean as argument for 'not'"

  numLit = arr $ \x -> NumVal (IV (x,x))

  add = proc (v1,v2) -> case (v1,v2) of
    (NumVal n1,NumVal n2) -> returnA -< NumVal (n1 + n2)
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two numbers as arguments for 'add'"

  sub = proc (v1,v2) -> case (v1,v2) of
    (NumVal n1,NumVal n2) -> returnA -< NumVal (n1 - n2)
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two numbers as arguments for 'sub'"

  mul = proc (v1,v2) -> case (v1,v2) of
    (NumVal n1,NumVal n2) -> returnA -< NumVal (n1 * n2)
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two numbers as arguments for 'mul'"

  div = proc (v1,v2) -> case (v1,v2) of
    (NumVal n1,NumVal n2) -> returnA -< NumVal (n1 / n2)
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two numbers as arguments for 'mul'"

  eq = proc (v1,v2) -> case (v1,v2) of
    (NumVal n1,NumVal n2)   -> returnA -< BoolVal (n1 == n2)
    (BoolVal b1,BoolVal b2) -> returnA -< BoolVal (b1 == b2)
    (Top,_) -> returnA -< Top
    (_,Top) -> returnA -< Top
    _ -> failA -< "Expected two values of the same type as arguments for 'eq'"

  fixEval f = f (fixEval f)