{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
-- | Case studies that run the wildcard semantics on given Stratego
-- programs.
module Main where

import qualified ConcreteSemantics as C
import qualified GrammarSemantics as G
import qualified SortSemantics as S
import qualified WildcardSemantics as W
import           Signature
import           Syntax hiding (Fail)

import           Paths_sturdy_stratego

import qualified Criterion.Measurement as CM
-- import qualified Criterion.Types as CT

import           Data.ATerm
import qualified Data.Abstract.FreeCompletion as A
import           Data.Abstract.HandleError
import qualified Data.Abstract.PreciseStore as A
import           Data.Abstract.Terminating
import qualified Data.Concrete.Error as C
import           Data.Constructor
import           Data.Foldable
import qualified Data.HashMap.Lazy as C
import qualified Data.HashSet as H
import qualified Data.Map as M
import           Data.String
import qualified Data.Text.IO as TIO

import           Text.Printf

import qualified TreeAutomata as G

-- import Debug.Trace

main :: IO ()
main = do
    CM.initializeTime
    -- Infinite loop for sort semantics?
    -- print =<< caseStudy 1 1 1 [Sort "Exp"] "pcf" "eval_0_0"
    -- Nonterminating sort semantics
    -- print =<< caseStudy 1 1 1 [Sort "Exp", Sort "Type"] "pcf" "check_eval_0_0"
    -- Working just fine for sort semantics:
    -- print =<< caseStudy 1 1 1 [Sort "Exp"] "arith" "eval_0_0"
    -- 
    print =<< caseStudy 1 1 1 [Sort "Module"] "arrows" "desugar_arrow_0_0"
    -- Cannot run: uses Prim.
    -- print =<< caseStudy 10 11 1 [Sort "SourceFile", Sort "TestSources"] "go2js" "generate_js_ast_0_0"
    -- print =<< caseStudy 1 1 1 [Sort "Module"] "cca" "norm_0_0"

runConcrete :: Strat -> StratEnv -> C.TermEnv -> C.Term
runConcrete function senv store = do
  let term = C.Cons "" [C.Cons "Nil" [], C.Cons "Succ" [C.Cons "Zero" []]]
  case C.eval function senv store term of
    C.Success (_,term') -> term'
    C.Fail _ -> error "Failing concrete semantics"

runGrammar :: Int -> G.GrammarBuilder G.Constr -> Strat -> StratEnv -> A.Store TermVar G.Term -> G.GrammarBuilder G.Constr
runGrammar fuel grammar function senv store = do
  case G.eval fuel function senv store (G.Term grammar) of
    Terminating res' -> G.fromTerm (filterResults res')
    NonTerminating -> fail "Nonterminating grammar semantics"

runWildcard :: Int -> G.Alphabet G.Constr -> Strat -> StratEnv -> A.Store TermVar W.Term -> G.GrammarBuilder G.Constr
runWildcard fuel alphabet function senv store = do
  case W.eval fuel function senv store W.Wildcard of
    Terminating res' ->
      let terms = H.fromList $ filterResults' (toList res')
      in H.foldr (union alphabet) emptyGrammar terms
    NonTerminating -> fail "Nonterminating wildcard semantics"
  where
    union :: G.Alphabet G.Constr -> W.Term -> G.GrammarBuilder G.Constr -> G.GrammarBuilder G.Constr
    union alph t g = g `G.union` go t
      where
        go (W.Cons (Constructor c) ts) = G.addConstructor (G.Constr c) (map go ts)
        go (W.StringLiteral s) = G.fromTerm (G.stringGrammar s)
        go (W.NumberLiteral n) = G.fromTerm (G.numberGrammar n)
        go (W.Wildcard) = G.wildcard alph
    emptyGrammar = G.grammar "empty" (M.fromList [("empty", [])])

runSort :: Int -> S.SortContext -> Strat -> StratEnv -> A.Store TermVar S.Term -> S.Term
runSort fuel ctx function senv store = do
  let res = S.eval fuel function senv ctx store (S.Term { S.sort = S.Top, S.context = ctx })
  case res of
    Terminating res' -> filterResults res'
    NonTerminating -> error "Nonterminating sort semantics"

caseStudy :: Int -> Int -> Int -> [Sort] -> String -> String -> IO String
caseStudy fuelG fuelW fuelS starts name function = do
  printf "------------------ case study: %s %s ----------------------\n" name function
  file <- TIO.readFile =<< getDataFileName (printf "case-studies/%s/%s.aterm" name name)
  case parseModule =<< parseATerm file of
    Left e -> fail (show e)
    Right module_ -> do
      let strat = (Call (fromString function) [] [])
          senv = stratEnv module_
          -- c = runConcrete strat senv (C.TermEnv C.empty)
          -- grammar = G.createGrammar starts (signature module_)
          -- g1 = runGrammar fuelG grammar strat senv A.empty
          -- g2 = runWildcard fuelW (G.alphabet grammar) strat senv A.empty
          g3 = runSort fuelS (S.createContext' (signature module_)) strat senv A.empty

      -- _ <- CM.measure (CT.nfIO (return g1)) 1
      return (printf "Concrete: %s\nGrammar: %s\nWildcard: %s\nSort: %s" (show "concrete") (show "grammar") (show "wildcard") (show g3))
      -- if g1 == g2
      --   then return "Equally precise"
      --   else if g1 `G.subsetOf` g2
      --        then return "More precise"
      --        else return "Less precise"

filterResults :: (Show a, Show b) => A.FreeCompletion (Error () (a, b)) -> b
filterResults r = case r of
  A.Lower (Success (_,b)) -> b
  A.Lower (SuccessOrFail _ (_,b)) -> b
  A.Lower (Fail _) -> error "Fail"
  top -> error (show top)

filterResults' :: [(Error () (W.TermEnv, W.Term))] -> [W.Term]
filterResults' = fmap (\r -> case r of Success (_,t) -> t; SuccessOrFail _ (_,t) -> t; Fail _ -> error "")
  . filter (\r -> case r of Success _ -> True; SuccessOrFail _ _ -> True; Fail _ -> False)
