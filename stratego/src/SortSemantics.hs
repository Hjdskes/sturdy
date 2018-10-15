{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DeriveGeneric #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures -fno-warn-orphans #-}
module SortSemantics where

import           Prelude hiding ((.),fail)

import           SharedSemantics
import           Sort (SortId(..))
import           Syntax hiding (Fail,TermPattern(..))
import           Utils

import           Control.Arrow
import           Control.Arrow.Const
import           Control.Arrow.Deduplicate
import           Control.Arrow.Except
import           Control.Arrow.Fail
import           Control.Arrow.Fix
import           Control.Arrow.Reader
import           Control.Arrow.State
import           Control.Arrow.Transformer.Abstract.Completion
import           Control.Arrow.Transformer.Abstract.Fixpoint
import           Control.Arrow.Transformer.Abstract.HandleExcept
import           Control.Arrow.Transformer.Const
import           Control.Arrow.Transformer.Reader
import           Control.Arrow.Transformer.State
import           Control.Category
import           Control.Monad (zipWithM)

import           Data.Abstract.FreeCompletion hiding (Top)
import qualified Data.Abstract.FreeCompletion as F
import           Data.Abstract.HandleError
import           Data.Abstract.HandleError as E
import qualified Data.Abstract.Maybe as A
import           Data.Abstract.PreciseStore (Store)
import qualified Data.Abstract.PreciseStore as S
import qualified Data.Abstract.StackWidening as SW
import           Data.Abstract.Terminating
import           Data.Abstract.Widening as W
import           Data.Constructor
import           Data.Foldable (foldr')
import           Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as M
import           Data.Hashable
import           Data.List (intercalate)
import           Data.Monoidal
import           Data.Order
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String (IsString,fromString)
import           Data.Text (pack,unpack)

import           GHC.Generics (Generic)

-- TODO: perhaps reuse the Sort module?
data Sort = Bottom | Top | Lexical | Numerical | Option Sort | List Sort | Tuple [Sort] | Sort Sort.SortId
  deriving (Eq, Ord, Generic)
instance IsString Sort where
  fromString s = Sort (Sort.SortId (pack s))

data SortContext = SortContext {
  signatures :: HashMap Constructor [([Sort], Sort)]
, lexicals :: Set Sort
, injectionClosure :: HashMap Sort (Set Sort)
} deriving (Eq,Show)

data Term = Term {
  sort :: Sort
, context :: SortContext
} deriving (Eq)

isLexical :: Term -> Bool
isLexical (Term Lexical _) = True
isLexical (Term s ctx) = Set.member s (lexicals ctx)

isList :: Term -> Bool
isList (Term (List _) _) = True
isList _ = False

type TermEnv = Store TermVar Term
instance UpperBounded TermEnv where
  top = S.empty

-- TODO: perhaps use HasSignature?
newtype Interp s a b =
  Interp (
   Fix (Strat,Term) Term
    (Const SortContext
     (Reader StratEnv
      (State TermEnv
       (Except ()
        (Completion
         (Fixpoint s () ()
          (->))))))) a b)

runInterp :: Interp (SW.Categories (Strat,StratEnv) (TermEnv,Term) SW.Stack) a b -> Int -> StratEnv -> SortContext -> TermEnv -> a -> Terminating (FreeCompletion (Error () (TermEnv,b)))
runInterp (Interp f) k senv sig tenv a =
  runFix' stackWidening sortWidening
    (runCompletion
     (runExcept
      (runState
       (runReader
        (runConst sig f)))))
    (tenv, (senv, a))
  where
    stackWidening :: SW.StackWidening (SW.Categories (Strat,StratEnv) (TermEnv, Term) SW.Stack) (TermEnv, (StratEnv, (Strat, Term)))
    stackWidening = SW.categorize (Iso from' to') (SW.stack (SW.maxSize k SW.topOut))
    sortWidening :: Widening (FreeCompletion (Error () (TermEnv,Term)))
    sortWidening = F.widening (E.widening (\_ _ -> ()) (S.widening W.finite W.** W.finite))

from' :: (TermEnv, (StratEnv, (Strat, Term))) -> ((Strat, StratEnv), (TermEnv, Term))
from' (tenv,(senv,(s,t))) = ((s,senv),(tenv,t))

to' :: ((Strat, StratEnv), (TermEnv, Term)) -> (TermEnv, (StratEnv, (Strat, Term)))
to' ((s,senv),(tenv,t)) = (tenv,(senv,(s,t)))

eval :: Int -> Strat -> StratEnv -> SortContext -> TermEnv -> Term -> Terminating (FreeCompletion (Error () (TermEnv,Term)))
eval i s = runInterp (eval' s) i

-- Instances -----------------------------------------------------------------------------------------
deriving instance Category (Interp s)
deriving instance Arrow (Interp s)
deriving instance ArrowChoice (Interp s)
deriving instance ArrowConst SortContext (Interp s)
deriving instance ArrowDeduplicate Term Term (Interp s)
deriving instance (Complete (FreeCompletion y), PreOrd y) => ArrowExcept x y () (Interp s)
deriving instance ArrowFail () (Interp s)
deriving instance ArrowFix (Strat,Term) Term (Interp s)
deriving instance ArrowReader StratEnv (Interp s)
deriving instance ArrowState TermEnv (Interp s)
deriving instance PreOrd b => PreOrd (Interp s a b)
deriving instance (Complete (FreeCompletion b), PreOrd b) => Complete (Interp s a b)
deriving instance PreOrd b => LowerBounded (Interp s a b)

instance Complete (FreeCompletion Term) where
  Lower x ⊔ Lower y = Lower (x ⊔ y)
  _ ⊔ _ = F.Top

instance Complete (FreeCompletion TermEnv) where
  Lower x ⊔ Lower y = Lower (x ⊔ y)
  _ ⊔ _ = F.Top

instance (PreOrd x, Complete (FreeCompletion x)) => Complete (FreeCompletion [x]) where
  Lower xs ⊔ Lower ys | eqLength xs ys = zipWithM (\x y -> Lower x ⊔ Lower y) xs ys
  _ ⊔ _ = F.Top

instance ArrowApply (Interp s) where
  app = Interp $ (\(Interp f, b) -> (f,b)) ^>> app

instance HasStratEnv (Interp s) where
  readStratEnv = proc _ -> do
    ask -< ()
  localStratEnv senv f = proc a ->
    local f -< (senv,a)

instance IsTermEnv TermEnv Term (Interp s) where
  getTermEnv = get
  putTermEnv = put
  lookupTermVar f g = proc (v,env) ->
    case S.lookup v env of
      A.Just t -> f -< t
      A.JustNothing t -> joined f g -< (t,())
      A.Nothing -> g -< ()
  insertTerm = arr $ \(v,t,env) -> S.insert v t env
  deleteTermVars = arr $ \(vars,env) -> foldr' S.delete env vars
  unionTermEnvs = arr (\(vars,e1,e2) -> S.union e1 (foldr' S.delete e2 vars))

instance IsTerm Term (Interp s) where
  matchTermAgainstConstructor matchSubterms = proc (c,ts,t) -> do
    ctx <- askConst -< ()
    case M.lookup c (signatures ctx) of
      Just sigs -> lubA (returnA ⊔ fail' <<< arr fst <<< second matchSubterms <<< matchTerm t ts) -<< sigs
      _ -> fail -< ()

  matchTermAgainstString = proc (_,t) ->
    if isLexical t
      then returnA ⊔ fail' -< t
      else fail -< ()

  matchTermAgainstNumber = proc (_,t@(Term termSort _)) -> case termSort of
    Numerical -> returnA ⊔ fail' -< t
    _ -> fail -< ()

  matchTermAgainstExplode matchCons matchSubterms = proc t -> case t of
    _ | isLexical t -> do
      matchSubterms -< convertToList [] (context t)
      returnA -< t
    Term Numerical ctx -> do
      matchSubterms -< convertToList [] ctx
      returnA -< t
    Term _ ctx -> do
      matchCons -< Term Lexical ctx
      matchSubterms -< Term (List Top) ctx
      returnA -< t

  equal = proc (t1,t2) ->
    if t1 ⊑ t2 || t2 ⊑ t1
      then returnA ⊔ fail' -< t1
      else fail -< ()

  convertFromList = proc (t,ts) ->
    if isLexical t && isList ts
      then returnA ⊔ fail' -< Term Top (context t) -- cannot deduct target sort from sort Lexical
      else fail -< ()

  -- Sorts don't have "subterms", so we cannot map over those "subterms".
  -- Since the constructor does not change, the output term has the same sort as the input term (if mapping succeeds)
  mapSubterms _ = returnA ⊔ fail'

  cons = proc (c, ts) -> do
    ctx <- askConst -< ()
    case M.lookup c (signatures ctx) of
      Just sigs -> lubA (buildTerm ctx ts) -<< sigs
      Nothing -> fail -< ()

  numberLiteral = proc _ -> do
    ctx <- askConst -< ()
    returnA -< Term Numerical ctx

  stringLiteral = proc _ -> do
    ctx <- askConst -< ()
    returnA -< Term Lexical ctx

--instance Soundness StratEnv Interp where
--  sound senv xs f g = forAll (choose (0,3)) $ \i ->
--    let con :: A.Pow (Error () (TermEnv,_))
--        con = A.dedup $ alpha (fmap (\(x,tenv) -> C.runInterp f senv tenv x) xs)
--        abst :: A.Pow (Error () (TermEnv,_))
--        abst = A.dedup $ runInterp g i senv (alpha (fmap snd xs)) (alpha (fmap fst xs))
--    in counterexample (printf "%s ⊑/ %s" (show con) (show abst)) $ con ⊑ abst


instance Show Sort where
  show x = case x of
    Bottom -> "Bottom"
    Top -> "Top"
    Lexical -> "LEX"
    Numerical -> "NUM"
    Option s -> "Option (" ++ show s ++ ")"
    List s -> "List (" ++ show s ++ ")"
    Tuple ss -> "Tuple (" ++ intercalate ", " (map show ss) ++ ")"
    Sort (SortId s) -> unpack s

instance Hashable Sort

instance Show Term where
  show (Term s _) = show s

instance Hashable Term where
  hashWithSalt salt (Term s _) = salt `hashWithSalt` s

instance UpperBounded Term where
  top = Term Top (SortContext M.empty Set.empty M.empty)

instance PreOrd Term where
  Term Bottom _ ⊑ Term _ _ = True
  Term _ _ ⊑ Term Top _ = True

  Term Lexical _ ⊑ t2 = isLexical t2
  Term (Option s1) ctx1 ⊑ Term (Option s2) ctx2 = Term s1 ctx1 ⊑ Term s2 ctx2
  Term (List s1) ctx1 ⊑ Term (List s2) ctx2 = Term s1 ctx1 ⊑ Term s2 ctx2
  Term (Tuple ss1) ctx1 ⊑ Term (Tuple ss2) ctx2 = (length ss1 == length ss2) &&
    (foldl (&&) True $ map (\(s1,s2) -> Term s1 ctx1 ⊑ Term s2 ctx2) $ zip ss1 ss2)

  Term s1 _ ⊑ Term s2 _ | s1 == s2 = True
  Term s1 ctx ⊑ Term s2 _ = case M.lookup s1 (injectionClosure ctx) of
    Just s -> Set.member s2 s
    Nothing -> False

instance Complete Term where
  t1 ⊔ t2 | t1 ⊑ t2 = t2
          | t2 ⊑ t1 = t1
          | otherwise = Term Top (context t1)

matchTerm :: Term -> [t'] -> Interp s ([Sort],Sort) (Term, ([t'], [Term]))
matchTerm (Term termSort ctx) ts = proc (patParams,patSort) -> do
  if eqLength patParams ts && Term patSort ctx ⊑ Term termSort ctx
    then returnA -< (Term patSort ctx, (ts,map (\s -> Term s ctx) patParams))
    else fail -< ()

buildTerm :: SortContext -> [Term] -> Interp s ([Sort],Sort) Term
buildTerm ctx ts = proc (cParams,cSort) -> do
  if eqLength cParams ts && (Term (Tuple $ map sort ts) ctx)  ⊑ (Term (Tuple cParams)) ctx
    then returnA -< Term cSort ctx
    else returnA -< Term Top ctx

convertToList :: [Term] -> SortContext -> Term
convertToList [] ctx = Term (List Bottom) ctx
convertToList ts ctx = Term (List (sort $ lub ts)) ctx
