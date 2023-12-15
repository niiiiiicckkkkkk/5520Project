module Main where

import Control.Monad.State (StateT, evalStateT, runStateT)
import Control.Monad.State qualified as S
import Data.List qualified as List
import Data.Maybe (fromMaybe)
import LuParser (parseLuExp, parseLuFile, parseStatement)
import LuStepper
  ( Store (MkStr, block, env, fstore, globalstore),
    evaluate,
    evaluateS,
    exec,
    go,
    initialStore,
    stepBackwardN,
    stepForwardN,
  )
import LuSyntax (Block (Block), pretty)
import System.IO (BufferMode (NoBuffering), hSetBuffering, stdout)
import Text.Read (readMaybe)

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  evalStateT go initialStore
