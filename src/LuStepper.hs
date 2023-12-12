module LuStepper where

import Control.Monad (when)
import Data.List qualified as List
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import LuParser qualified
import LuSyntax
import State (State)
import State qualified as S
import Test.HUnit (Counts, Test (..), runTestTT, (~:), (~?=))
import Test.QuickCheck qualified as QC
import Text.Read (readMaybe)

data Store = MkStr {env :: Environment, globalstore :: Map String Value, fstore :: FunctionStore}

-- type Table = Map Value Value

type FunctionStore = Map Name Closure

data Closure = Closure {fenv :: Environment, function :: Function}

data Function = Function [String] Block

-- reference into the environment
data Reference
  = Ref String
  | TableRef (String, Value)

initialStore :: Store
initialStore = MkStr Map.empty Map.empty Map.empty

{-
tableFromState :: Name -> State Store (Maybe Table)
tableFromState tname = Map.lookup tname <$> S.get
-}

index :: Reference -> State Store Value
index (Ref r) = do
  s <- S.get
  case Map.lookup r (env s) of
    Just k -> case Map.lookup k (globalstore s) of
      Just val -> return val
      Nothing -> error "mapping exists in env but not in globalstore"
    Nothing -> return NilVal
index (TableRef (eref, tkey)) = error "undefined"

update :: Reference -> Value -> State Store ()
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

{-do
s <- S.get
S.put (updateVar r v' s)
where
  updateVar :: String -> Value -> Store -> Store
  updateVar r v' s = s {globalstore = Map.insert r v' $ globalstore s} -}

-- | Convert a variable into a reference into the store.
-- Fails when the var is `t.x` or t[1] and `t` is not defined in the store
-- when the var is `2.y` or `nil[2]` (i.e. not a `TableVal`)
-- or when the var is t[nil]
resolveVar :: Var -> State Store Reference
resolveVar (Name n) = return $ Ref n
resolveVar (Dot exp n) = error "no tables"
resolveVar (Proj exp1 exp2) = error "no tables"

-- | Expression evaluator
evalE :: Expression -> State Store Value
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
              setEnv (fenv cs) (extractArgnames . function $ cs) argexps
              s' <- S.get
              let s'' = (S.execState $ evalB (extractFunction . function $ cs)) s'
              let returned = pullReturn s''
               in do
                    S.put s {globalstore = globalstore s'', fstore = fstore s''}
                    return returned
    _ -> error "fcall's var did not map to a function"
evalE (FDefExp (FDef argnames block)) = do
  s <- S.get
  let len = length $ Map.keys (fstore s)
  let ref = "_f" ++ show len
  let c = Closure {fenv = env s, function = Function argnames block}
   in S.put s {fstore = Map.insert ref c (fstore s)}
  return (FRef ref)

-- let s' = S.execState $ evalB (extractFunction . function $ cs)

pullReturn :: Store -> Value
pullReturn store = case Map.lookup "_return" (env store) of
  Nothing -> error "_return not in environment"
  Just gref -> case Map.lookup gref (globalstore store) of
    Just v -> v
    Nothing -> error "_return reference not available in globalstore"

extractFunction :: Function -> Block
extractFunction (Function argnames block) = block

extractArgnames :: Function -> [String]
extractArgnames (Function argnames block) = argnames

extractStatements :: Block -> [Statement]
extractStatements (Block s) = s

-- old state plus evaluated args
setEnv :: Environment -> [String] -> [Expression] -> State Store ()
setEnv fenv (n : ns) (e : es) = do
  s <- S.get
  val <- evalE e
  let len = length $ Map.keys (globalstore s)
  let gref = "_v" ++ show len
  S.put (defineVar n gref val s)
setEnv fenv [] (e : es) = do
  s <- S.get
  S.put (s {env = fenv})
setEnv fenv (n : ns) [] = do
  s <- S.get
  let len = length $ Map.keys (globalstore s)
  let gref = "_v" ++ show len
  S.put (defineVar n gref NilVal s)
setEnv fenv [] [] = do
  s <- S.get
  S.put (s {env = fenv})

{-
do
  val <- evalE e
  update (StringVal n) val
  setEnv vs ns es
setEnv vs [] (e : es) = return ()
setEnv vs (n : ns) [] = update (StringVal n) NilVal
setEnv vs [] [] = return ()
-}

-- pull out the correct block
-- bind arguments in the new environment
-- return the resulting value

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

evaluate :: Expression -> Store -> (Value, Store)
evaluate e = S.runState (evalE e)

evaluateS :: Statement -> Store -> Store
evaluateS st = S.execState $ evalS st

-- | Determine whether a value should be interpreted as true or false when
-- used as a condition.
toBool :: Value -> Bool
toBool (BoolVal False) = False
toBool NilVal = False
toBool _ = True

eval :: Block -> State Store ()
eval (Block ss) = mapM_ evalS ss

evalB :: Block -> State Store ()
evalB (Block ss) = mapM_ evalS ss

-- | Statement evaluator
evalS :: Statement -> State Store ()
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
evalS (Restore e) = do
  s <- S.get
  S.put s {env = e}

exec :: Block -> Store -> Store
exec = S.execState . eval

step :: Block -> State Store Block
step (Block ((FCallSt (FCall v argexps)) : otherSs)) = do
  s <- S.get
  vr <- resolveVar v
  ref <- index vr
  case ref of
    (FRef fref) -> do
      case Map.lookup fref (fstore s) of
        Nothing -> error "closure not found"
        Just cs -> do
          setEnv (fenv cs) (extractArgnames . function $ cs) argexps
          let bk = extractStatements (extractFunction (function cs))
          let rs = Restore $ env s
          return $ Block (bk ++ [rs] ++ otherSs)
    _ -> error "function not found"
step (Block ((Restore ev) : otherSs)) = do
  s <- S.get
  S.put (s {env = ev})
  step (Block otherSs)
step (Block ((If e (Block ss1) (Block ss2)) : otherSs)) = do
  v <- evalE e
  if toBool v
    then return $ Block (ss1 ++ otherSs)
    else return $ Block (ss2 ++ otherSs)
step (Block (w@(While e (Block ss)) : otherSs)) = do
  v <- evalE e
  if toBool v
    then return $ Block (ss ++ [w] ++ otherSs)
    else return $ Block otherSs
step (Block (a@(Assign v e) : otherSs)) = do
  s' <- evalS a
  return $ Block otherSs
step (Block ((Repeat b e) : otherSs)) = step (Block (While (Op1 Not e) b : otherSs))
step (Block (empty : otherSs)) = return $ Block otherSs
step b@(Block []) = return b

-- | Evaluate this thread for a specified number of steps
boundedStep :: Int -> Block -> State Store Block
boundedStep 0 b = return b
boundedStep _ b | blockFinal b = return b
boundedStep n b = step b >>= boundedStep (n - 1)

-- | Evaluate this thread for a specified number of steps, using the specified store
steps :: Int -> Block -> Store -> (Block, Store)
steps n block = S.runState (boundedStep n block)

-- | Is this block completely evaluated?
blockFinal :: Block -> Bool
blockFinal (Block []) = True
blockFinal _ = False

allStep :: Block -> State Store Block
allStep b | blockFinal b = return b
allStep b = step b >>= allStep

execStep :: Block -> Store -> Store
execStep b = S.execState (allStep b)

-- | Evaluate this thread to completion

-- execThread :: Thread -> Store -> Store
-- execThread t = S.execState (allStep t)

data Stepper = Stepper
  { filename :: Maybe String,
    block :: Block,
    store :: Store,
    history :: Maybe Stepper
  }

initialStepper :: Stepper
initialStepper =
  Stepper
    { filename = Nothing,
      block = mempty,
      store = initialStore,
      history = Nothing
    }

stepForward :: Stepper -> Stepper
stepForward ss =
  let (block', store') = steps 1 (block ss) (store ss)
   in ss {block = block', store = store', history = Just ss}

stepForwardN :: Stepper -> Int -> Stepper
stepForwardN ss 0 = ss
stepForwardN ss n =
  let nextStepper = stepForward ss
   in stepForwardN nextStepper (n - 1)

stepBackward :: Stepper -> Maybe Stepper
stepBackward = history

stepBackwardN :: Stepper -> Int -> Maybe Stepper
stepBackwardN ss 0 = Just ss
stepBackwardN ss n =
  let prevStepper = stepBackward ss
   in case prevStepper of
        Just ss' -> stepBackwardN ss' (n - 1)
        _ -> Nothing
