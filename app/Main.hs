module Main where

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
import Text.Read (readMaybe)

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  evalStateT go initialStore
  return ()

