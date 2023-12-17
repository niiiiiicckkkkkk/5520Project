module Main where

import Control.Monad.State (StateT, evalStateT, runStateT)
import Control.Monad.State qualified as S
import Data.List qualified as List
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
import Test.QuickCheck qualified as QC
import Text.Read (readMaybe)

{-
instance QC.Arbitrary Store where
  arbitrary :: QC.Gen Store
  arbitrary = do
    (x, st) <- S.runStateT (return $ update (Ref "x") NilVal) initialStore
    y <- S.execStateT x initialStore
    return y -}

{-QC.sized $ aux initialStore
where
  aux :: Store -> Int -> QC.Gen Store
  aux store n =
    QC.frequency
      [ (1, return store),
        ( n,
          do
            v <- (QC.arbitrary :: QC.Gen Value)
            s <- genStringLit
            -- IO ((), store)
            (x, st) <- S.runStateT (update (Ref s) v) store
            aux st (n `div` 2)
        )
      ] -}

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  evalStateT go initialStore

-- ls <- QC.sample' (QC.arbitrary :: QC.Gen Store)
-- print $ map (\s -> (pretty $ globalstore s)) ls
-- return ()
