module Main where

import Control.Monad.State (StateT, evalStateT, runStateT)
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
  evalStateT (go initialStore) initialStore

{-
  where
    go :: Stepper -> IO ()
    go ss = do
      hSetBuffering stdout NoBuffering
      prompt ss
      putStr (fromMaybe "Lu" (filename ss) ++ "> ")
      str <- getLine
      case List.uncons (words str) of
        -- load a file for stepping
        Just (":l", [fn]) -> do
          parseResult <- LuParser.parseLuFile fn
          case parseResult of
            (Left _) -> do
              putStr "Failed to parse file"
              go ss
            (Right b) -> do
              putStr ("Loaded " ++ fn ++ ", initializing stepper\n")
              go (ss {filename = Just fn, store = (store ss) {block = b} })
        -- dump the store
        Just (":d", _) -> do
          putStrLn (pretty $ globalstore $ store ss)
          putStrLn (pretty $ env $ store ss)
          go ss
        -- quit the stepper
        Just (":q", _) -> return ()
        -- run current block to completion
        Just (":r", _) -> do
          s' <- exec (block (store ss)) (store ss)
          go ss {store = s' {block = mempty}, history = Just ss}
        -- next statement (could be multiple)
        Just (":n", strs) -> do
          let numSteps :: Int
              numSteps = case readMaybe (concat strs) of
                Just x -> x
                Nothing -> 1
           in do
                newStepper <- stepForwardN ss numSteps
                go newStepper
        -- previous statement
        -- NOTE: this should revert steps of the evaluator not
        -- commands to the stepper. With :n 5 followed by :p
        -- it should back up a single statement, not five statements.
        Just (":p", strs) -> do
          let numSteps :: Int
              numSteps = case readMaybe (concat strs) of
                Just x -> x
                Nothing -> 1

          let newStepper = stepBackwardN ss numSteps
          case newStepper of
            Just ss' -> go ss'
            _ -> do
              putStr "No History to revert..."
              go ss

        -- evaluate an expression in the current state
        _ ->
          case LuParser.parseStatement str of
            Right st -> do
              s' <- evaluateS st (store ss)
              -- putStr "evaluated statement\n"
              go $ ss {store = s'}
            Left _s -> do
              -- putStr "evaluated expression\n"
              case LuParser.parseLuExp str of
                Right exp -> do
                  (v, s') <- evaluate exp (store ss)
                  putStrLn (pretty v)
                  go $ ss {store = s'}
                Left _s -> do
                  putStrLn "?"
                  go ss
    prompt :: Stepper -> IO ()
    prompt s = case block (store s) of
      Block [] -> return ()
      Block (s : _) -> putStr "--> " >> putStrLn (pretty s)
-}