module Main where

import Control.Monad.State (StateT, evalStateT, execStateT, runStateT)
import LuStepper
  ( go,
    initialStore,
  )
import System.IO (BufferMode (NoBuffering), hSetBuffering, stdout)

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering
  evalStateT go initialStore
  return ()
