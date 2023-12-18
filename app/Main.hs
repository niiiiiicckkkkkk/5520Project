module Main where

import Control.Monad (foldM)
import Control.Monad.State (StateT, evalStateT, execStateT, runStateT)
import Control.Monad.State qualified as S
import Data.List ((!!))
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import LuParser (parseLuExp, parseLuFile, parseStatement)
import LuStepper
  ( Reference (Ref),
    Store (MkStr, block, env, fstore, globalstore),
    evaluate,
    evaluateS,
    exec,
    go,
    initialStore,
    stepBackwardN,
    stepForwardN,
    update,
  )
import LuSyntax
import LuSyntax (Block (Block), pretty)
import System.IO (BufferMode (NoBuffering), hSetBuffering, stdout)
import Test.QuickCheck (Gen, arbitrary, ioProperty, property, sample, sample')
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

prop_updateOverwrite :: StateT Store IO Store -> QC.Property
prop_updateOverwrite state = do
  QM.monadicIO (test state)
  where
    test :: StateT Store IO Store -> QM.PropertyM IO Bool
    test st = QM.run $ do
      return False

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
  -- hSetBuffering stdout NoBuffering
  -- evalStateT go initialStore
  -- return ()

  -- ls <- QC.sample' (QC.arbitrary :: QC.Gen (StateT Store IO Store))
  -- ls' <- mapM (\st -> S.runStateT st initialStore) ls
  -- mapM (\(_, s) -> putStrLn (pretty $ globalstore s)) ls'
  QC.quickCheck prop_updates_bound
  return ()
