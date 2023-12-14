module LuStepper where

import Control.Monad (when)
import Control.Monad.State (StateT)
import Control.Monad.State qualified as S
import Control.Monad.Trans (lift)
import Data.List qualified as List
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import LuParser qualified
import LuSyntax
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC
import Text.Read (readMaybe)

data Store = MkStr
  { env :: Environment,
    globalstore :: Map String Value,
    fstore :: FunctionStore,
    block :: Block,
    history :: Store,
    filename :: String
  }

initialStore :: Store = MkStr Map.empty Map.empty Map.empty mempty initialStore ""

-- type Table = Map Value Value

type FunctionStore = Map Name Closure

data Closure = Closure {fenv :: Environment, function :: Function}

data Function = Function [String] Block

-- reference into the environment
data Reference
  = Ref String
  | TableRef (String, Value)

{-
tableFromState :: Name -> State Store (Maybe Table)
tableFromState tname = Map.lookup tname <$> S.get
-}

index :: Reference -> StateT Store IO Value
index (Ref r) = do
  s <- S.get
  -- lift $ putStrLn "in index"
  case Map.lookup r (env s) of
    Just k -> case Map.lookup k (globalstore s) of
      Just val -> return val
      Nothing -> error "mapping exists in env but not in globalstore"
    Nothing -> return NilVal
index (TableRef (eref, tkey)) = error "undefined"

update :: Reference -> Value -> StateT Store IO ()
update (Ref eref) v' = do
  s <- S.get
  case Map.lookup eref $ env s of
    Nothing -> do
      let len = length $ Map.keys (globalstore s)
      let gref = "_v" ++ show len
      S.put (defineVar eref gref v' s)
    Just gref -> S.put (updateVar gref v' s)
  where
    updateVar :: String -> Value -> Store -> Store
    updateVar r v' s = s {globalstore = Map.insert r v' $ globalstore s}
update (TableRef (eref, tkey)) v' = do
  s <- S.get
  case Map.lookup eref $ env s of
    Nothing -> return ()
    Just gref ->
      case Map.lookup gref (globalstore s) of
        Nothing -> error "mapping exists in env but not in globalstore -- table"
        Just (Table tb) -> S.put (s {globalstore = Map.insert gref (Table (Map.insert tkey v' tb)) (globalstore s)})
        _ -> error "idk haha"

defineVar :: String -> String -> Value -> Store -> Store
defineVar eref gref v' s =
  s
    { env = Map.insert eref gref $ env s,
      globalstore = Map.insert gref v' $ globalstore s
    }

-- | Convert a variable into a reference into the store.
-- Fails when the var is `t.x` or t[1] and `t` is not defined in the store
-- when the var is `2.y` or `nil[2]` (i.e. not a `TableVal`)
-- or when the var is t[nil]
resolveVar :: Var -> StateT Store IO Reference
resolveVar (Name n) = return $ Ref n
resolveVar (Dot exp n) = error "no tables"
resolveVar (Proj exp1 exp2) = error "no tables"

-- | Expression evaluator
evalE :: Expression -> StateT Store IO (Value)
evalE (Var v) = do
  ref <- resolveVar v -- see above
  index ref
evalE (Val v) = return v
evalE (Op2 e1 o e2) = evalOp2 o <$> evalE e1 <*> evalE e2
evalE (Op1 o e) = evalOp1 o <$> evalE e
evalE (TableConst _fs) = error "no tables"
evalE (FCallExp (FCall var argexps)) = do
  s <- S.get
  r <- resolveVar var
  ref <- index r
  case ref of
    (FRef fref) ->
      let closure = Map.lookup fref (fstore s)
       in case closure of
            Nothing -> error "closure didn't exist but should"
            Just cs -> do
              lift $ putStrLn "evaluating function"
              fstr <- setEnv (extractArgnames . function $ cs) argexps s {env = fenv cs}
              S.put fstr
              evalB (extractFunction . function $ cs)
              s' <- S.get
              let returned = pullReturn s'
               in do
                    S.put s {globalstore = globalstore s', fstore = fstore s'}
                    return returned
    _ -> error "fcall's var did not map to a function"

-- S.StateT $ fStTransformer ref argexps
evalE (FDefExp (FDef argnames block)) = do
  s <- S.get
  let len = length $ Map.keys (fstore s)
  let ref = "_f" ++ show len
  let c = Closure {fenv = env s, function = Function argnames block}
   in S.put s {fstore = Map.insert ref c (fstore s)}
  return (FRef ref)

{-
fStTransformer :: Closure -> [Expression] -> Store -> IO (Value, Store)
fStTransformer cl exps s = do
  (oldStore, fStore) <- evalArgs exps (extractArgnames $ function cl) s s {env = fenv cl}
  (_, fStore') <- (S.runStateT $ evalB (extractFunction $ function cl)) fStore
  case Map.lookup "_return" (env fStore') of
    Nothing -> return (NilVal, oldStore)
    Just gref -> case Map.lookup gref (globalstore fStore') of
      Just v -> return (v, oldStore {globalstore = globalstore fStore', fstore = fstore fStore'})
      Nothing -> error "what the heck just happend"

-- TODO: add bindings from current store to function store too
evalArgs :: [Expression] -> [String] -> Store -> Store -> IO (Store, Store)
evalArgs (e : es) (n : ns) oldStr fStr = do
  (val, oldStr') <- (S.runStateT $ evalE e) oldStr
  (_, fStr') <- (S.runStateT $ update (Ref n) val) fStr
  evalArgs es ns oldStr' fStr'
evalArgs (e : es) [] oldStr fStr = do
  evalArgs es [] oldStr fStr
evalArgs [] (n : ns) oldStr fStr = do
  (_, fStr') <- (S.runStateT $ update (Ref n) NilVal) fStr
  evalArgs [] ns oldStr fStr'
evalArgs [] [] oldStr fStr = return (oldStr, fStr) -}

pullReturn :: Store -> Value
pullReturn store = case Map.lookup "_return" (env store) of
  Nothing -> NilVal
  Just gref -> case Map.lookup gref (globalstore store) of
    Just v -> v
    Nothing -> error "_return reference not available in globalstore"

extractFunction :: Function -> Block
extractFunction (Function argnames block) = block

extractArgnames :: Function -> [String]
extractArgnames (Function argnames block) = argnames

extractStatements :: Block -> [Statement]
extractStatements (Block s) = s

-- current env bindings + closure bindings + args
setEnv :: [String] -> [Expression] -> Store -> StateT Store IO Store
setEnv (n : ns) (e : es) fstr = do
  s <- S.get
  v <- evalE e
  S.put fstr
  update (Ref n) v
  fstr' <- S.get
  S.put s
  setEnv ns es fstr'
setEnv (n : ns) [] fstr = do
  s <- S.get
  S.put fstr
  update (Ref n) NilVal
  fstr' <- S.get
  S.put s
  setEnv ns [] fstr'
setEnv [] (e : es) fstr = return fstr
setEnv [] [] fstr = return fstr

evalOp1 :: Uop -> Value -> Value
evalOp1 Neg (IntVal v) = IntVal $ negate v
evalOp1 Len (StringVal v) = IntVal $ length v
evalOp1 Len (TableVal v) = error "no tables"
evalOp1 Len iv@(IntVal v) = iv
evalOp1 Len (BoolVal True) = IntVal 1
evalOp1 Len (BoolVal False) = IntVal 0
evalOp1 Not v = BoolVal $ not $ toBool v
evalOp1 _ _ = NilVal

evalOp2 :: Bop -> Value -> Value -> Value
evalOp2 Plus (IntVal i1) (IntVal i2) = IntVal (i1 + i2)
evalOp2 Minus (IntVal i1) (IntVal i2) = IntVal (i1 - i2)
evalOp2 Times (IntVal i1) (IntVal i2) = IntVal (i1 * i2)
evalOp2 Divide (IntVal _) (IntVal 0) = NilVal
evalOp2 Divide (IntVal i1) (IntVal i2) = IntVal (i1 `div` i2)
evalOp2 Modulo (IntVal i1) (IntVal 0) = NilVal
evalOp2 Modulo (IntVal i1) (IntVal i2) = IntVal $ i1 `mod` i2
evalOp2 Eq v1 v2 = BoolVal $ v1 == v2
evalOp2 Gt v1 v2 = BoolVal $ v1 > v2
evalOp2 Ge v1 v2 = BoolVal $ v1 >= v2
evalOp2 Lt v1 v2 = BoolVal $ v1 < v2
evalOp2 Le v1 v2 = BoolVal $ v1 <= v2
evalOp2 Concat (StringVal s1) (StringVal s2) = StringVal (s1 ++ s2)
evalOp2 _ _ _ = NilVal

evaluate :: Expression -> Store -> IO (Value, Store)
evaluate e = S.runStateT (evalE e)

evaluateS :: Statement -> Store -> IO Store
evaluateS st = S.execStateT $ evalS st

-- | Determine whether a value should be interpreted as true or false when
-- used as a condition.
toBool :: Value -> Bool
toBool (BoolVal False) = False
toBool NilVal = False
toBool _ = True

eval :: Block -> StateT Store IO ()
eval (Block ss) = mapM_ evalS ss

evalB :: Block -> StateT Store IO ()
evalB (Block ss) = mapM_ evalS ss

-- | Statement evaluator
evalS :: Statement -> StateT Store IO ()
evalS (If e b1 b2) = do
  v <- evalE e
  if toBool v then evalB b1 else evalB b2
evalS w@(While e b) = do
  v <- evalE e
  when (toBool v) $ do
    evalB b
    evalS w
evalS (Assign v e) = do
  -- update global variable or table field v to value of e
  s <- S.get
  ref <- resolveVar v
  e' <- evalE e
  update ref e'
evalS s@(Repeat b e) = evalS (While (Op1 Not e) b) -- keep evaluating block b until expression e is true
evalS Empty = return () -- do nothing
evalS (Return e) = do
  v <- evalE e
  update (Ref "_return") v
evalS (FCallSt f@(FCall v argexps)) = do
  evalE $ FCallExp f
  return ()

exec :: Block -> Store -> IO Store
exec = S.execStateT . eval

-- block to store (state after one statement)
step :: Block -> StateT Store IO ()
step (Block ((FCallSt (FCall v argexps)) : otherSs)) = do
  s <- S.get
  vr <- resolveVar v
  ref <- index vr
  stepin <- lift promptYN
  case ref of
    (FRef fref) -> do
      case Map.lookup fref (fstore s) of
        Nothing -> error "closure not found"
        Just cs -> do
          fstr <- setEnv (extractArgnames . function $ cs) argexps s {env = fenv cs}
          let bk = extractStatements (extractFunction (function cs))
          if stepin
            then go fstr {block = Block bk}
            else do
              evalB $ extractFunction (function cs)
              S.put s {block = Block otherSs}
    _ -> error "function not found"
step (Block ((If e (Block ss1) (Block ss2)) : otherSs)) = do
  v <- evalE e
  s <- S.get
  if toBool v
    then S.put s {block = Block (ss1 ++ otherSs)}
    else S.put s {block = Block (ss2 ++ otherSs)}
step (Block (w@(While e (Block ss)) : otherSs)) = do
  s <- S.get
  v <- evalE e
  if toBool v
    then S.put s {block = Block (ss ++ [w] ++ otherSs)}
    else S.put s {block = Block otherSs}
step (Block (a@(Assign v e) : otherSs)) = do
  lift $ putStrLn "assignment"
  evalS a
  s <- S.get
  S.put s {block = Block otherSs}
step (Block ((Repeat b e) : otherSs)) = step (Block (While (Op1 Not e) b : otherSs))
step (Block (empty : otherSs)) = do
  s <- S.get
  S.put s {block = Block otherSs}
step b@(Block []) = do
  s <- S.get
  S.put s {block = Block []}

-- | Evaluate this thread for a specified number of steps
-- boundedStep :: Int -> Block -> StateT Store IO Block
-- boundedStep 0 b = return b
-- boundedStep _ b | blockFinal b = return b
-- boundedStep n b = step b >>= boundedStep (n - 1)

-- | Evaluate this thread for a specified number of steps, using the specified store
-- steps :: Int -> Block -> Store -> IO (Block, Store)
-- steps n block = S.runStateT (boundedStep n block)

-- | Is this block completely evaluated?
-- blockFinal :: Block -> Bool
-- blockFinal (Block []) = True
-- blockFinal _ = False

-- allStep :: Block -> StateT Store IO Block
-- allStep b | blockFinal b = return b
-- allStep b = step b >>= allStep

-- execStep :: Block -> Store -> IO Store
-- execStep b = S.execStateT (allStep b)

stepForward :: StateT Store IO ()
stepForward = do
  s <- S.get
  step $ block s

{-
  let (block', store') = steps 1 (block ss) (store ss)
   in do
    ss {block = block', store = store', history = Just ss}-}

stepForwardN :: Int -> StateT Store IO ()
stepForwardN 0 = return ()
stepForwardN n = do
  s <- S.get
  stepForward
  stepForwardN (n - 1)

stepBackward :: StateT Store IO ()
stepBackward = do
  s <- S.get
  S.put $ history s

stepBackwardN :: Int -> StateT Store IO ()
stepBackwardN 0 = return ()
stepBackwardN n = do
  stepBackward
  stepBackwardN (n - 1)

promptYN :: IO Bool
promptYN = do
  putStrLn "step in? (y/n)"
  str <- getLine
  case str of
    ('y' : ss) -> return True
    _ -> return False

go :: Store -> StateT Store IO ()
go st = do
  S.put st
  lift $ prompt st
  lift $ putStr ("Lu " ++ filename st ++ "> ")
  str <- lift getLine
  case List.uncons (words str) of
    -- load a file for stepping
    Just (":l", [fn]) -> do
      parseResult <- lift $ LuParser.parseLuFile fn
      case parseResult of
        (Left _) -> do
          lift $ putStr "Failed to parse file"
          go st
        (Right b) -> do
          lift $ putStr ("Loaded " ++ fn ++ ", initializing stepper\n")
          go st {filename = fn, block = b}
    -- dump the store
    Just (":d", _) -> do
      lift $ putStrLn (pretty $ globalstore st)
      lift $ putStrLn (pretty $ env st)
      go st
    -- quit the stepper
    Just (":q", _) -> return ()
    -- run current block to completion
    Just (":r", _) -> do
      evalB $ block st
      s' <- S.get
      go s'
    -- next statement (could be multiple)
    Just (":n", strs) -> do
      let numSteps :: Int
          numSteps = case readMaybe (concat strs) of
            Just x -> x
            Nothing -> 1
       in do
            stepForwardN numSteps
            newStore <- S.get
            go newStore
    -- previous statement
    -- NOTE: this should revert steps of the evaluator not
    -- commands to the stepper. With :n 5 followed by :p
    -- it should back up a single statement, not five statements.
    Just (":p", strs) -> do
      let numSteps :: Int
          numSteps = case readMaybe (concat strs) of
            Just x -> x
            Nothing -> 1

      stepBackwardN numSteps
      s' <- S.get
      go s'
    -- evaluate an expression in the current state
    _ ->
      case LuParser.parseStatement str of
        Right stmt -> do
          evalS stmt
          s' <- S.get
          -- putStr "evaluated statement\n"
          go s'
        Left _s -> do
          -- putStr "evaluated expression\n"
          case LuParser.parseLuExp str of
            Right exp -> do
              v <- evalE exp
              s' <- S.get
              lift $ putStrLn (pretty v)
              go s'
            Left _s -> do
              lift $ putStrLn "?"
              go st

prompt :: Store -> IO ()
prompt st = case block st of
  Block [] -> return ()
  Block (s : _) -> putStr "--> " >> putStrLn (pretty s)
