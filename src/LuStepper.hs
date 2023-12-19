module LuStepper where

import Control.Monad (when)
import Control.Monad.State (StateT)
import Control.Monad.State qualified as S
import Control.Monad.Trans (lift)
import Data.List qualified as List
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import LuParser qualified as LP
import LuSyntax
import Text.Read (readMaybe)

-- | Store for the State Monad
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

type FunctionStore = Map Name Closure

type Terminated = Bool

-- | Closure holds the environment at function definition and a block of code
data Closure = Closure {fenv :: Environment, function :: Function} deriving (Show)

-- Reference into the environment
data Reference
  = Ref String
  | TableRef (String, Value)
  | NoRef
  deriving (Eq, Show)

-- | Status used to track `go`
data ExitStatus
  = ExitSuccess
  | ExitFailure
  | Running
  deriving (Show)

-- | Track previous store
data History
  = NoHistory
  | OutOfScope
  | Previous Store
  deriving (Show)

-- | Given a reference to the environment index into the store and pull out the value
-- Return NilVal when non-table variable not found
-- Error when table environment key not found (checked in resolveVar)
-- Ref (r :: String) pulls a key to the globalstore from the environment and references the value directly
-- TableRef (envkey :: String, tablekey :: Value) calls lookup on the environment with the envkey to get the
-- key corresponding to the correct table then tablekey is used to index into the table
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

-- | Same logic as index but updates position with value
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
        _ -> error "table value not found in globalstore"
update NoRef _ = return ()

-- | Given the store, envkey and globalkey and a value create a new mapping for a variable
--   inside the provided store
defineVar :: String -> String -> Value -> Store -> Store
defineVar eref gref v' s =
  s
    { env = Map.insert eref gref $ env s,
      globalstore = Map.insert gref v' $ globalstore s
    }

-- | Convert a variable into a reference into the store.
--   Return NoRef for Dot and Proj when LHS variable not found
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

-- | Index the function store and extract the closure for a function if one exists
--   Returns Nothing if called variable doesn't resolve to a function
fLookup :: Expression -> StateT Store IO (Maybe Closure)
fLookup (CallExp (Call var argexps)) = do
  s <- S.get
  r <- resolveVar var
  ref <- index r
  case ref of
    (FRef fref) -> return $ Map.lookup fref (fstore s)
    _ -> return Nothing
fLookup _ = return Nothing

-- | Pull Table References from the environment
pullTables :: Environment -> [(String, String)]
pullTables env = filter (List.isPrefixOf "_tenv" . fst) (Map.assocs env)

-- | Add a list of mappings to a given environment
insertTables :: [(String, String)] -> Environment -> Environment
insertTables assocs env = List.foldr aux env assocs
  where
    aux :: (String, String) -> Environment -> Environment
    aux (k, v) env = if Map.member k env then env else Map.insert k v env

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
  S.put store' {env = Map.insert eKey2Table gKey2Table (env store')}
  return (EnvTableK eKey2Table)

-- | Expression evaluator
evalE :: Expression -> StateT Store IO Value
evalE (Var v) = do
  ref <- resolveVar v
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
      S.put fstr {env = insertTables (pullTables (env s')) (env fstr), block = extractFunction . function $ cs}
      if stepin
        then do
          fstr' <- S.get
          S.put fstr' {block = extractFunction . function $ cs, history = OutOfScope}
          status <- go
          case status of
            ExitSuccess -> do
              returnS <- S.get
              let returned = pullReturn returnS
               in do
                    S.put returnS {block = block s', env = insertTables (pullTables $ env returnS) (env s')}
                    return returned
            ExitFailure -> do
              S.put s {rerun = True} >> return NilVal
            Running -> error "terminated function cannot be running"
        else do
          evalB (extractFunction . function $ cs)
          returnS <- S.get
          let returned = pullReturn returnS
           in do
                S.put returnS {block = block s', env = insertTables (pullTables $ env returnS) (env s')}
                return returned
evalE (DefExp (Def argnames block)) = do
  s <- S.get
  let len = length $ Map.keys (fstore s)
  let ref = "_f" ++ show len
  let c = Closure {fenv = env s, function = Function argnames block}
   in S.put s {fstore = Map.insert ref c (fstore s)}
  return (FRef ref)

-- | Extract a return value from the store
--   Returns NilVal if keyword `_return` is absent
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

-- | Set up a store for function calls
--   Returns store with argument mappings evaluated within the current store
setEnv :: [String] -> [Expression] -> Store -> StateT Store IO Store
setEnv (n : ns) (e : es) fstr = do
  s <- S.get
  v <- evalE e
  case v of
    EnvTableK k -> do
      ref <- resolveVar (Name k)
      if Map.member k (env fstr)
        then do
          S.put fstr
        else do
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
      Just (Table t) -> do
        return $ IntVal $ Map.size t
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
--   used as a condition.
toBool :: Value -> Bool
toBool (BoolVal False) = False
toBool NilVal = False
toBool _ = True

eval :: Block -> StateT Store IO ()
eval (Block ss) = mapM_ evalS ss

evalB :: Block -> StateT Store IO ()
evalB (Block ss) = mapM_ evalS ss

-- evalB :: Block -> StateT Store IO ()
-- evalB (Block []) = return ()
-- evalB (Block (s : ss)) = evalS s >> evalB (Block ss)

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
  s <- S.get
  ref <- resolveVar v
  e' <- evalE e
  update ref e'
evalS s@(Repeat b e) = evalS (While (Op1 Not e) b) -- keep evaluating block b until expression e is true
evalS Empty = return ()
evalS (Return e) = do
  v <- evalE e
  update (Ref "_return") v
evalS (CallSt f@(Call v argexps)) = do
  evalE $ CallExp f
  return ()

exec :: Block -> Store -> IO Store
exec = S.execStateT . eval

-- | Step one line through current block
--   Return ExitSuccess if block empty after step
--   Return Running if block non-empty after step
step :: Block -> StateT Store IO ExitStatus
step (Block (call@(CallSt (Call v argexps)) : otherSs)) = do
  evalS call
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      S.get >>= \safter -> return $ checkEmpty $ block safter
    else do
      S.put s {block = Block otherSs}
      S.get >>= \safter -> return $ checkEmpty $ block safter
step (Block ((If e (Block ss1) (Block ss2)) : otherSs)) = do
  v <- evalE e
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      S.get >>= \safter -> return $ checkEmpty $ block safter
    else do
      if toBool v
        then S.put s {block = Block (ss1 ++ otherSs)}
        else S.put s {block = Block (ss2 ++ otherSs)}
      S.get >>= \safter -> return $ checkEmpty $ block safter
step (Block (w@(While e (Block ss)) : otherSs)) = do
  v <- evalE e
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      S.get >>= \safter -> return $ checkEmpty $ block safter
    else do
      if toBool v
        then S.put s {block = Block (ss ++ [w] ++ otherSs)}
        else S.put s {block = Block otherSs}
      S.get >>= \safter -> return $ checkEmpty $ block safter
step (Block (a@(Assign v e) : otherSs)) = do
  evalS a
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      S.get >>= \safter -> return $ checkEmpty $ block safter
    else do
      S.put s {block = Block otherSs}
      S.get >>= \safter -> return $ checkEmpty $ block safter
step (Block ((Repeat b e) : otherSs)) = step (Block (While (Op1 Not e) b : otherSs))
step (Block (r@(Return exp) : otherSs)) = do
  evalS r
  s <- S.get
  if rerun s
    then do
      S.modify (\s -> s {rerun = False})
      S.get >>= \safter -> return $ checkEmpty $ block safter
    else return ExitSuccess
step (Block (empty : otherSs)) = do
  s <- S.get
  S.put s {block = Block otherSs}
  S.get >>= \safter -> return $ checkEmpty $ block safter
step b@(Block []) = return ExitSuccess

checkEmpty :: Block -> ExitStatus
checkEmpty (Block []) = ExitSuccess
checkEmpty (Block _) = Running

stepForward :: StateT Store IO ExitStatus
stepForward = do
  s <- S.get
  status <- step $ block s
  s' <- S.get
  S.put s' {history = Previous s}
  return status

-- | Run param: n steps within the current store or until the block is empty
--   Return a indicator whether to terminate the stepper or continue prompting for input
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

-- | Reverse param: n steps within the current store or exiting the current block
--   Return a indicator whether to terminate the stepper or continue prompting for input
stepBackwardN :: Int -> StateT Store IO Terminated
stepBackwardN 0 = return False
stepBackwardN n = do
  status <- stepBackward
  case status of
    Running -> stepBackwardN (n - 1)
    ExitFailure -> return True
    ExitSuccess -> error "exited function forward via :p"

-- | Ask user if they want to step into function
promptYN :: IO Bool
promptYN = do
  putStr "step in? (y / n) "
  str <- getLine
  case str of
    ('y' : ss) -> return True
    _ -> return False

-- | Respond to commands from user
go :: StateT Store IO ExitStatus
go = do
  st <- S.get
  lift $ prompt st
  lift $ putStr (fromMaybe "Lu" (filename st) ++ "> ")
  str <- lift getLine
  case List.uncons (words str) of
    -- load a file for stepping
    Just (":l", [fn]) -> do
      parseResult <- lift $ LP.parseLuFile fn
      case parseResult of
        (Left _) -> do
          lift $ putStrLn "Failed to parse file"
          go
        (Right b) -> do
          lift $ putStrLn ("Loaded " ++ fn ++ ", initializing stepper")
          S.put st {filename = Just fn, block = b}
          go
    -- dump the store
    Just (":dv", _) -> do
      lift $ putStrLn (pretty $ globalstore st)
      lift $ putStrLn (pretty $ env st)
      go
    Just (":d", _) -> do
      lift $ dump st
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
    _ ->
      case LP.parseStatement str of
        Right stmt -> do
          evalS stmt
          go
        Left _s -> do
          case LP.parseLuExp str of
            Right exp -> do
              v <- evalE exp
              go
            Left _s -> do
              lift $ putStrLn "?"
              go

printTableVal :: Value -> Store -> String
printTableVal v st = case v of
  EnvTableK k -> case Map.lookup k (env st) of
    Just gkey -> case Map.lookup gkey (globalstore st) of
      Just v' -> printTableVal v' st
      Nothing -> ""
    Nothing -> ""
  v -> pretty v ++ "\n"

dump :: Store -> IO ()
dump st = putStrLn $ printaux st (Map.toList $ env st) ""
  where
    printaux :: Store -> [(String, String)] -> String -> String
    printaux st ((ekey, gkey) : pairs) out =
      if List.isPrefixOf "_tenv" ekey
        then printaux st pairs out
        else case Map.lookup gkey (globalstore st) of
          Just (EnvTableK k) -> case Map.lookup k (env st) of
            Just gkey' -> case Map.lookup gkey' (globalstore st) of
              Just (Table t) ->
                out
                  ++ ekey
                  ++ "   -->  \n"
                  ++ "{\n"
                  ++ List.foldr (\(k, v) acc -> acc ++ pretty k ++ " : " ++ printTableVal v st) "" (Map.toList t)
                  ++ "}"
                  ++ "\n"
                  ++ printaux st pairs out
              Just v -> out ++ ekey ++ "   -->  " ++ pretty v ++ "\n" ++ printaux st pairs out
              Nothing -> out
            Nothing -> out
          Just (FRef r) -> case Map.lookup r (fstore st) of
            Just cl -> out ++ ekey ++ "  -->  " ++ pretty (function cl) ++ "\n" ++ printaux st pairs out
            Nothing -> out
          Just val -> out ++ ekey ++ "  -->  " ++ pretty val ++ "\n" ++ printaux st pairs out
          _ -> out
    printaux st [] out = out

prompt :: Store -> IO ()
prompt st = case block st of
  Block [] -> return ()
  Block (s : _) -> putStr "--> " >> putStrLn (pretty s)
