module Main where

import Control.Monad (foldM)
import Control.Monad.State (StateT, evalStateT, execStateT, runStateT)
import Control.Monad.State qualified as S
import Data.List ((!!))
import Data.List qualified as List
import Data.Map ((!))
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import LuParser (parseLuExp, parseLuFile, parseStatement)
import LuStepper
  ( Reference (Ref),
    Store (MkStr, block, env, fstore, globalstore),
    allocateTable,
    evalE,
    evalS,
    evaluate,
    evaluateS,
    exec,
    go,
    index,
    initialStore,
    setEnv,
    stepBackwardN,
    stepForwardN,
    update,
  )
import LuSyntax (Block (Block), Expression (Val), Value (EnvTableK, NilVal, Table), genStringLit, pretty)
import System.IO (BufferMode (NoBuffering), hSetBuffering, stdout)
import Test.QuickCheck (Gen, arbitrary, ioProperty, property, sample, sample', (==>))
import Test.QuickCheck qualified as QC
import Test.QuickCheck.Monadic qualified as QM
import Text.Read (readMaybe)

{-
instance QC.Arbitrary Store where
  arbitrary :: QC.Gen Store
  arbitrary = do
    (x, st) <- S.runStateT (return $ update (Ref "x") NilVal) initialStore
    y <- S.execStateT x initialStore
    return y -}

instance QC.Arbitrary (StateT Store IO Store) where
  arbitrary :: QC.Gen (StateT Store IO Store)
  arbitrary = do
    len <- QC.chooseInt (0, 200)
    vals <- QC.vectorOf len (QC.arbitrary :: QC.Gen Value)
    refs <- QC.vectorOf len (Ref <$> genStringLit)
    let entries = zip refs vals
    return $ foldM f initialStore entries

f :: Store -> (Reference, Value) -> StateT Store IO Store
f s (r, v) = update r v >> S.get >>= \s' -> return s'

prop_updates_bound :: StateT Store IO Store -> QC.Property
prop_updates_bound state = do
  QM.monadicIO (test state)
  where
    test :: StateT Store IO Store -> QM.PropertyM IO Bool
    test st = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      let e = env s
      let store = globalstore s
      return $ Map.foldr (\a b -> Map.member a store && b) True e

prop_updateOverwrite ::
  StateT Store IO Store ->
  String ->
  Value ->
  Value ->
  QC.Property
prop_updateOverwrite state r v v' = do
  QM.monadicIO (test state (Ref r) v v')
  where
    test :: StateT Store IO Store -> Reference -> Value -> Value -> QM.PropertyM IO Bool
    test st r v v' = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      (_, s') <- S.runStateT (update r v) s
      (_, s'') <- S.runStateT (update r v') s'
      (value, _) <- S.runStateT (index r) s''
      return (value == v')

prop_argsBound :: StateT Store IO Store -> [String] -> [Value] -> QC.Property
prop_argsBound state ss vs = QM.monadicIO (test state ss (Val <$> filter (/= NilVal) vs))
  where
    test :: StateT Store IO Store -> [String] -> [Expression] -> QM.PropertyM IO Bool
    test st args vs = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      (fstr, _) <- S.runStateT (setEnv args vs initialStore) s
      let fenv = env fstr
       in return $ foldr (\name acc -> Map.member name fenv && acc) True args

prop_tableSound :: StateT Store IO Store -> [Value] -> [Value] -> QC.Property
prop_tableSound state keys vals = QM.monadicIO (test state (zip keys vals))
  where
    test :: StateT Store IO Store -> [(Value, Value)] -> QM.PropertyM IO Bool
    test st assocs = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      (v, s') <- S.runStateT (allocateTable assocs) s
      case v of
        EnvTableK k -> do
          (tbl, s'') <- S.runStateT (index (Ref k)) s'
          case tbl of
            Table table -> return $ foldr (\(key, val) acc -> (table ! key == val) && acc) False (filter ((/= NilVal) . fst) assocs)
            _ -> return False
          return True
        _ -> return False

-- do
-- (_, s) <- S.runStateT state initialStore

-- >>> sample $ (arbitrary :: Gen (StateT Store IO Store))
-- No instance for (Show (StateT Store IO Store))
--   arising from a use of `sample'
-- In the first argument of `($)', namely `sample'
-- In the expression:
--   sample $ (arbitrary :: Gen (StateT Store IO Store))
-- In an equation for `it_a1q0QO':
--     it_a1q0QO = sample $ (arbitrary :: Gen (StateT Store IO Store))

instance Show (StateT Store IO a) where
  show :: StateT Store IO a -> String
  show state = "state"

main :: IO ()
main = do
  {-
  hSetBuffering stdout NoBuffering
  putStrLn "update"
  evalStateT go initialStore
  return ()-}

  -- ls <- QC.sample' (QC.arbitrary :: QC.Gen (StateT Store IO Store))
  -- ls' <- mapM (\st -> S.runStateT st initialStore) ls
  -- mapM (\(_, s) -> putStrLn (pretty $ globalstore s)) ls'

  putStrLn "prop update bound"
  QC.quickCheck prop_updates_bound
  putStrLn "prop argsBound"
  QC.quickCheck prop_argsBound
  putStrLn "prop updateOverwrite"
  QC.quickCheck prop_updateOverwrite
  putStrLn "prop tableSound"
  QC.quickCheck prop_tableSound
  return ()
