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
    history :: History,
    filename :: Maybe String,
    status :: ExitStatus,
    rerun :: Bool
  }
  deriving (Show)

initialStore :: Store
initialStore :: Store = MkStr Map.empty Map.empty Map.empty mempty NoHistory Nothing Running False

-- type Table = Map Value Value

type FunctionStore = Map Name Closure

type Terminated = Bool

data Closure = Closure {fenv :: Environment, function :: Function} deriving (Show)

data Function = Function [String] Block deriving (Show)

-- reference into the environment
data Reference
  = Ref String
  | TableRef (String, Value)
  | NoRef
  deriving (Eq, Show)

-- | Control data
data ExitStatus
  = ExitSuccess
  | ExitFailure
  | Running
  deriving (Show)

data History
  = NoHistory
  | OutOfScope
  | Previous Store
  deriving (Show)

{-
tableFromState :: Name -> State Store (Maybe Table)
tableFromState tname = Map.lookup tname <$> S.get
-}

index :: Reference -> StateT Store IO Value
index (Ref r) = do
  s <- S.get
  case Map.lookup r (env s) of
    Just k -> case Map.lookup k (globalstore s) of
      Just val -> return val
      Nothing -> error "mapping exists in env but not in globalstore"
    Nothing -> return NilVal
index (TableRef (eref, tkey)) = do
  s <- S.get
  case Map.lookup eref (env s) of
    Just gkey -> case Map.lookup gkey (globalstore s) of
      Just (Table t) -> case Map.lookup tkey t of
        Just v -> return v
        _ -> return NilVal
      _ -> error "table reference did not map to a table in the global store"
    _ -> error "mapping exists in env but not in globalstore"
index NoRef = return NilVal

update :: Reference -> Value -> StateT Store IO ()
update (Ref eref) v' = do
  -- lift $ putStrLn "in update"
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
        _ -> error "table value not found in globalstore"
update NoRef _ = return ()

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
resolveVar (Name name) = return $ Ref name
resolveVar (Dot exp name) = do
  v <- evalE exp
  case v of
    EnvTableK k -> do return $ TableRef (k, StringVal name)
    _ -> return NoRef
resolveVar (Proj exp1 exp2) = do
  v1 <- evalE exp1
  v2 <- evalE exp2
  case v1 of
    EnvTableK k -> return $ TableRef (k, v2)
    _ -> return NoRef

-- | lookup closure in fstore
fLookup :: Expression -> StateT Store IO (Maybe Closure)
fLookup (CallExp (Call var argexps)) = do
  s <- S.get
  r <- resolveVar var
  ref <- index r
  case ref of
    (FRef fref) -> return $ Map.lookup fref (fstore s)
    _ -> return Nothing
fLookup _ = return Nothing

nonNil :: (Value, Value) -> Bool
nonNil (_, NilVal) = False
nonNil (NilVal, _) = False
nonNil _ = True

tableFieldToValue :: TableField -> StateT Store IO (Value, Value)
tableFieldToValue (FieldName name exp) = do
  v <- evalE exp
  return (StringVal name, v)
tableFieldToValue (FieldKey exp1 exp2) = do
  v1 <- evalE exp1
  v2 <- evalE exp2
  return (v1, v2)

allocateTable :: [(Value, Value)] -> StateT Store IO Value
allocateTable assocs = do
  store <- S.get
  let glength = length (Map.keys $ globalstore store)
  -- string to access Table
  let gKey2Table = "_t" ++ show glength

  -- string to access environment entry
  let gKey2Env = "_v" ++ show (glength + 1)
  let elength = length (Map.keys $ env store)

  -- environment entry for the table
  let eKey2Table = "_tenv" ++ show (elength + 1)
  -- make sure we don't have a nil key or value
  let assocs' = filter nonNil assocs
  -- update the store
  S.put store {globalstore = Map.insert gKey2Table (Table $ Map.fromList assocs') (globalstore store)}
  store' <- S.get
  -- lift $ putStrLn (pretty $ globalstore store')
  -- S.put store' {globalstore = Map.insert gKey2Env (EnvTableK eKey2Table) (globalstore store')}
  -- store'' <- S.get
  -- lift $ putStrLn (pretty $ globalstore store'')
  S.put store' {env = Map.insert eKey2Table gKey2Table (env store')}
  -- store''' <- S.get
  -- lift $ putStrLn (pretty $ env store''')
  return (EnvTableK eKey2Table)

-- | Expression evaluator
evalE :: Expression -> StateT Store IO Value
evalE (Var v) = do
  ref <- resolveVar v -- see above
  index ref
evalE (Val v) = return v
evalE (Op2 e1 o e2) = evalOp2 o <$> evalE e1 <*> evalE e2
evalE (Op1 o e) = do
  v <- evalE e
  evalOp1 o v
evalE (TableConst fs) = do
  assocs <- mapM tableFieldToValue fs
  allocateTable assocs
evalE c@(CallExp (Call v argexps)) = do
  s <- S.get
  mclosure <- fLookup c
  case mclosure of
    Nothing -> error "closure not found"
    Just cs -> do
      stepin <- lift promptYN
      fstr <- setEnv (extractArgnames . function $ cs) argexps s {env = fenv cs}
      s' <- S.get
      S.put fstr {block = extractFunction . function $ cs}
      if stepin
        then do
          S.put fstr {block = extractFunction . function $ cs, history = OutOfScope}
          status <- go
          case status of
            ExitSuccess -> do
              returnS <- S.get
              let returned = pullReturn returnS
               in do
                    case returned of
                      EnvTableK k -> do
                        t <- index (Ref k)
                        S.put returnS {block = block s', env = env s'}
                        update (Ref k) t
                        return returned
                      _ -> do
                        S.put returnS {block = block s', env = env s'}
                        return returned
            ExitFailure -> S.put s {rerun = True} >> return NilVal
            Running -> error "terminated function cannot be running"
        else do
          evalB (extractFunction . function $ cs)
          returnS <- S.get
          let returned = pullReturn returnS
           in do
                case returned of
                  EnvTableK k -> do
                    t <- index (Ref k)
                    S.put returnS {block = block s', env = env s'}
                    update (Ref k) t
                    return returned
                  _ -> do
                    S.put returnS {block = block s', env = env s'}
                    return returned
evalE (DefExp (Def argnames block)) = do
  s <- S.get
  let len = length $ Map.keys (fstore s)
  let ref = "_f" ++ show len
  let c = Closure {fenv = env s, function = Function argnames block}
   in S.put s {fstore = Map.insert ref c (fstore s)}
  return (FRef ref)

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
  case v of
    EnvTableK k -> do
      ref <- resolveVar (Name k)
      t <- index ref
      S.put fstr
      update ref t
    _ -> do
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

evalOp1 :: Uop -> Value -> StateT Store IO Value
evalOp1 Neg (IntVal v) = return $ IntVal $ negate v
evalOp1 Len (StringVal v) = return $ IntVal $ length v
evalOp1 Len (EnvTableK k) = do
  s <- S.get
  case Map.lookup k (env s) of
    Just gkey -> case Map.lookup gkey (globalstore s) of
      Just (Table t) -> return $ IntVal $ Map.size t
      _ -> error "table reference did not map to a table in the globalstore"
    _ -> error "dangling pointer from env to globalstore "
evalOp1 Len iv@(IntVal v) = return iv
evalOp1 Len (BoolVal True) = return $ IntVal 1
evalOp1 Len (BoolVal False) = return $ IntVal 0
evalOp1 Not v = return $ BoolVal $ not $ toBool v
evalOp1 _ _ = return NilVal

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
evalS (CallSt f@(Call v argexps)) = do
  evalE $ CallExp f
  return ()

exec :: Block -> Store -> IO Store
exec = S.execStateT . eval

-- block to store (state after one statement)
step :: Block -> StateT Store IO ExitStatus
step (Block (call@(CallSt (Call v argexps)) : otherSs)) = do
  evalS call
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      return $ checkEmpty otherSs
    else do
      S.put s {block = Block otherSs}
      return $ checkEmpty otherSs
step (Block ((If e (Block ss1) (Block ss2)) : otherSs)) = do
  v <- evalE e
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      return $ checkEmpty otherSs
    else do
      if toBool v
        then S.put s {block = Block (ss1 ++ otherSs)}
        else S.put s {block = Block (ss2 ++ otherSs)}
      return $ checkEmpty otherSs
step (Block (w@(While e (Block ss)) : otherSs)) = do
  v <- evalE e
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      return $ checkEmpty otherSs
    else do
      if toBool v
        then S.put s {block = Block (ss ++ [w] ++ otherSs)}
        else S.put s {block = Block otherSs}
      return $ checkEmpty otherSs
step (Block (a@(Assign v e) : otherSs)) = do
  evalS a
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      return $ checkEmpty otherSs
    else do
      S.put s {block = Block otherSs}
      return $ checkEmpty otherSs
step (Block ((Repeat b e) : otherSs)) = step (Block (While (Op1 Not e) b : otherSs))
step (Block (r@(Return exp) : otherSs)) = do
  evalS r
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      return $ checkEmpty otherSs
    else return ExitSuccess
step (Block (empty : otherSs)) = do
  s <- S.get
  S.put s {block = Block otherSs}
  return $ checkEmpty otherSs
step b@(Block []) = return ExitSuccess

checkEmpty :: [Statement] -> ExitStatus
checkEmpty [] = ExitSuccess
checkEmpty _ = Running

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

stepForward :: StateT Store IO ExitStatus
stepForward = do
  s <- S.get
  status <- step $ block s
  s' <- S.get
  S.put s' {history = Previous s}
  return status

{-
  let (block', store') = steps 1 (block ss) (store ss)
   in do
    ss {block = block', store = store', history = Just ss}-}

stepForwardN :: Int -> StateT Store IO Terminated
stepForwardN 0 = return False
stepForwardN n = do
  status <- stepForward
  case status of
    Running -> stepForwardN (n - 1)
    ExitSuccess -> return True
    ExitFailure -> error "exited function backwards via :n"

stepBackward :: StateT Store IO ExitStatus
stepBackward = do
  s <- S.get
  case history s of
    Previous s' -> do
      S.put s'
      return Running
    OutOfScope -> return ExitFailure
    NoHistory -> do
      lift $ putStrLn "No History to revert..."
      return Running

stepBackwardN :: Int -> StateT Store IO Terminated
stepBackwardN 0 = return False
stepBackwardN n = do
  status <- stepBackward
  case status of
    Running -> stepBackwardN (n - 1)
    ExitFailure -> return True
    ExitSuccess -> error "exited function forward via :p"

promptYN :: IO Bool
promptYN = do
  putStr "step in? (y / n)"
  str <- getLine
  case str of
    ('y' : ss) -> return True
    _ -> return False

go :: StateT Store IO ExitStatus
go = do
  st <- S.get
  lift $ prompt st
  lift $ putStr (fromMaybe "Lu" (filename st) ++ "> ")
  str <- lift getLine
  case List.uncons (words str) of
    -- load a file for stepping
    Just (":l", [fn]) -> do
      parseResult <- lift $ LuParser.parseLuFile fn
      case parseResult of
        (Left _) -> do
          lift $ putStrLn "Failed to parse file"
          go
        (Right b) -> do
          lift $ putStrLn ("Loaded " ++ fn ++ ", initializing stepper")
          S.put st {filename = Just fn, block = b}
          go
    -- dump the store
    Just (":d", _) -> do
      lift $ putStrLn (pretty $ globalstore st)
      lift $ putStrLn (pretty $ env st)
      go
    -- quit the stepper
    Just (":q", _) -> return ExitSuccess
    -- run current block to completion
    Just (":r", _) -> do
      evalB $ block st
      return ExitSuccess
    -- next statement (could be multiple)
    Just (":n", strs) -> do
      let numSteps :: Int
          numSteps = case readMaybe (concat strs) of
            Just x -> x
            Nothing -> 1
       in do
            terminated <- stepForwardN numSteps
            if terminated then return ExitSuccess else go
    -- previous statement
    -- NOTE: this should revert steps of the evaluator not
    -- commands to the stepper. With :n 5 followed by :p
    -- it should back up a single statement, not five statements.
    Just (":p", strs) -> do
      let numSteps :: Int
          numSteps = case readMaybe (concat strs) of
            Just x -> x
            Nothing -> 1
       in do
            terminated <- stepBackwardN numSteps
            if terminated then return ExitFailure else go
    -- evaluate an expression in the current state
    _ ->
      case LuParser.parseStatement str of
        Right stmt -> do
          evalS stmt
          -- putStr "evaluated statement\n"
          go
        Left _s -> do
          -- putStr "evaluated expression\n"
          case LuParser.parseLuExp str of
            Right exp -> do
              v <- evalE exp
              go
            Left _s -> do
              lift $ putStrLn "?"
              go

prompt :: Store -> IO ()
prompt st = case block st of
  Block [] -> return ()
  Block (s : _) -> putStr "--> " >> putStrLn (pretty s)
