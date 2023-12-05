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

data Store = MkStr {vstore :: ValueStore, fstore :: FunctionStore}

type ValueStore = Map Value Value

type FunctionStore = Map Name Closure

data Closure = Closure {env :: ValueStore, function :: Function}

data Function = Function [String] Block

initialStore :: Store
initialStore = MkStr Map.empty Map.empty

type Reference = Value

{-
tableFromState :: Name -> State Store (Maybe Table)
tableFromState tname = Map.lookup tname <$> S.get
-}

index :: Reference -> State Store Value
index ref = do
  s <- S.get
  case Map.lookup ref (vstore s) of
    Just val -> return val
    Nothing -> return NilVal

update :: Reference -> Value -> State Store ()
update NilVal v' = return ()
update ref v' = do
  s <- S.get
  S.modify (updateStore $ vstore s)
  where
    updateStore :: ValueStore -> Store -> Store
    updateStore env store = store {vstore = Map.insert ref v' env}

-- | Convert a variable into a reference into the store.
-- Fails when the var is `t.x` or t[1] and `t` is not defined in the store
-- when the var is `2.y` or `nil[2]` (i.e. not a `TableVal`)
-- or when the var is t[nil]
resolveVar :: Var -> State Store Reference
resolveVar (Name n) = do
  return $ StringVal n
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
evalE (FCallExp (FCall var argexps)) = error "function call"
evalE (FDefExp (FDef argnames block)) = error "function declaration"

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

evaluate :: Expression -> Store -> Value
evaluate e = S.evalState (evalE e)

evaluateS :: Statement -> Store -> Store
evaluateS st = S.execState $ evalS st

-- | Determine whether a value should be interpreted as true or false when
-- used as a condition.
toBool :: Value -> Bool
toBool (BoolVal False) = False
toBool NilVal = False
toBool _ = True

eval :: Thread -> State Store ()
eval (Thread (Block ss : bs)) = mapM_ evalS ss
eval _ = mapM_ evalS []

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

exec :: Thread -> Store -> (Thread, Store)
exec t@(Thread (b : bs)) s = (Thread bs, store)
  where
    store = S.execState (eval t) s
exec (Thread []) s = (Thread [], s)

step :: Thread -> State Store Thread
step (Thread []) = return $ Thread []
step (Thread (b : bs)) = do
  b' <- blockStep b
  return $ Thread (b' : bs)

blockStep :: Block -> State Store Block
blockStep (Block ((If e (Block ss1) (Block ss2)) : otherSs)) = do
  v <- evalE e
  if toBool v
    then return $ Block (ss1 ++ otherSs)
    else return $ Block (ss2 ++ otherSs)
blockStep (Block (w@(While e (Block ss)) : otherSs)) = do
  v <- evalE e
  if toBool v
    then return $ Block (ss ++ [w] ++ otherSs)
    else return $ Block otherSs
blockStep (Block (a@(Assign v e) : otherSs)) = do
  s' <- evalS a
  return $ Block otherSs
blockStep (Block ((Repeat b e) : otherSs)) = blockStep (Block (While (Op1 Not e) b : otherSs))
blockStep (Block (empty : otherSs)) = return $ Block otherSs
blockStep b@(Block []) = return b

-- | Evaluate this thread for a specified number of steps
boundedStep :: Int -> Thread -> State Store Thread
boundedStep 0 t = return t
boundedStep _ t | threadFinal t = return t
boundedStep n t = step t >>= boundedStep (n - 1)

-- | Evaluate this thread for a specified number of steps, using the specified store
steps :: Int -> Thread -> Store -> (Thread, Store)
steps n thread = S.runState (boundedStep n thread)

-- | Is this block completely evaluated?
blockFinal :: Block -> Bool
blockFinal (Block []) = True
blockFinal _ = False

threadFinal :: Thread -> Bool
threadFinal (Thread []) = True
threadFinal _ = False

allStep :: Block -> State Store Block
allStep b | blockFinal b = return b
allStep b = blockStep b >>= allStep

execBlock :: Thread -> State Store Thread
execBlock (Thread (b : bs)) = do
  allStep b
  return $ Thread bs
execBlock t@(Thread []) = return t

-- | Evaluate this thread to completion

-- execThread :: Thread -> Store -> Store
-- execThread t = S.execState (allStep t)

data Stepper = Stepper
  { filename :: Maybe String,
    thread :: Thread,
    store :: Store,
    history :: Maybe Stepper
  }

initialStepper :: Stepper
initialStepper =
  Stepper
    { filename = Nothing,
      thread = mempty,
      store = initialStore,
      history = Nothing
    }

stepForward :: Stepper -> Stepper
stepForward ss =
  let (thread', store') = steps 1 (thread ss) (store ss)
   in ss {thread = thread', store = store', history = Just ss}

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
