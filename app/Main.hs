module Main where

import Data.List qualified as List
import Data.Maybe (fromMaybe)
import LuParser (parseLuExp, parseLuFile, parseStatement)
import LuStepper
  ( Stepper (..),
    Store (MkStr, fstore, vstore),
    evaluate,
    evaluateS,
    exec,
    initialStepper,
    stepBackwardN,
    stepForwardN,
  )
import LuSyntax (Block (Block), Thread (Thread), pretty)
import System.IO (BufferMode (NoBuffering), hSetBuffering, stdout)
import Text.Read (readMaybe)

main :: IO ()
main = go initialStepper
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
            (Right t) -> do
              putStr ("Loaded " ++ fn ++ ", initializing stepper\n")
              go (ss {filename = Just fn, thread = t})
        -- dump the store
        Just (":d", _) -> do
          putStrLn (pretty $ vstore $ store ss)
          go ss
        -- quit the stepper
        Just (":q", _) -> return ()
        -- run current block to completion
        Just (":r", _) ->
          let (t', s') = exec (thread ss) (store ss)
           in go ss {thread = t', store = s', history = Just ss}
        -- next statement (could be multiple)
        Just (":n", strs) -> do
          let numSteps :: Int
              numSteps = case readMaybe (concat strs) of
                Just x -> x
                Nothing -> 1
          let newStepper = stepForwardN ss numSteps
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
            Right st ->
              let s' = evaluateS st (store ss)
               in go $ ss {store = s'}
            Left _s -> do
              case LuParser.parseLuExp str of
                Right exp -> do
                  let v = evaluate exp (store ss)
                  putStrLn (pretty v)
                  go ss
                Left _s -> do
                  putStrLn "?"
                  go ss
    prompt :: Stepper -> IO ()
    prompt Stepper {thread = Thread []} = return ()
    prompt Stepper {thread = Thread ((Block (s : ss)) : _)} =
      putStr "--> " >> putStrLn (pretty s)
    prompt s@(Stepper {thread = Thread (Block [] : bs)}) = prompt s {thread = Thread bs}
