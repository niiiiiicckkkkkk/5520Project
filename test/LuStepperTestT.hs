module LuStepperTestT (qc, test_all) where

import Control.Monad (foldM)
import Control.Monad.State (StateT)
import Control.Monad.State qualified as S
import Data.Map (Map, (!?), (!))
import Data.Map qualified as Map
import LuStepper
import LuSyntax
import Test.HUnit
import Test.QuickCheck (Gen, arbitrary, ioProperty, property, sample, sample', (==>))
import Test.QuickCheck qualified as QC
import Test.QuickCheck.Monadic qualified as QM

instance QC.Arbitrary Store where
  arbitrary :: QC.Gen Store
  arbitrary = QC.sized $ aux initialStore
    where
      aux :: Store -> Int -> QC.Gen Store
      aux store n =
        QC.frequency
          [ (1, return store),
            ( n,
              do
                v <- (QC.arbitrary :: QC.Gen Value)
                s <- genStringLit
                (_, st) <- S.runStateT (return $ update (Ref s) v) store
                aux st (n `div` 2)
            )
          ]

-- >>> QC.sample' (QC.arbitrary :: QC.Gen Store)

func1 :: Function
func1 = Function ["x"] (Block [Return $ Var (Name "x")])

close1 :: Closure
close1 = Closure {fenv = Map.empty, function = func1}

extendedStore :: Store
extendedStore =
  MkStr
    { env =
        Map.fromList
          [ ("x", "_v0"),
            ("y", "_v1"),
            ("t", "_v2"),
            ("_tenv1", "_t0"),
            ("c", "_v3")
          ],
      globalstore =
        Map.fromList
          [ ("_v0", IntVal 3),
            ("_v1", StringVal "hello"),
            ("_v2", EnvTableK "_tenv1"),
            ("_t0", Table $ Map.fromList [(StringVal "a", IntVal 1), (StringVal "b", IntVal 2)]),
            ("_v3", StringVal "a")
          ],
      fstore =
        Map.fromList [("_f0", close1)],
      block =
        Block
          [Assign (Name "z") (Val (StringVal "ok!"))],
      history = NoHistory,
      filename = Nothing,
      status = Running,
      rerun = False
    }

xref :: Reference
xref = Ref "x"

yref :: Reference
yref = Ref "y"

zref :: Reference
zref = Ref "z"

tref :: Reference
tref = TableRef ("_tenv1", StringVal "a")

test_index :: Test
test_index =
  "index tests"
    ~: TestList
      [ TestCase
          ( do
              v <- S.evalStateT (index xref) initialStore
              assertEqual "" NilVal v
          ),
        TestCase
          ( do
              v <- S.evalStateT (index xref) extendedStore
              assertEqual "" (IntVal 3) v
          ),
        TestCase
          ( do
              v <- S.evalStateT (index zref) extendedStore
              assertEqual "" NilVal v
          ),
        TestCase
          ( do
              v <- S.evalStateT (index yref) extendedStore
              assertEqual "" (StringVal "hello") v
          ),
        TestCase
          ( do
              v <- S.evalStateT (index tref) extendedStore
              assertEqual "" (IntVal 1) v
          )
      ]

test_update :: Test
test_update =
  "update tests"
    ~: TestList
      [ TestCase
          ( do
              s <- S.execStateT (update xref (IntVal 5)) initialStore
              v <- S.evalStateT (index xref) s
              assertEqual "" (IntVal 5) v
          ),
        TestCase
          ( do
              s <- S.execStateT (update xref (IntVal 5)) extendedStore
              v <- S.evalStateT (index xref) s
              assertEqual "" (IntVal 5) v
          ),
        TestCase
          ( do
              s <- S.execStateT (update yref (StringVal "hey!!")) extendedStore
              v <- S.evalStateT (index yref) s
              assertEqual "" (StringVal "hey!!") v
          ),
        TestCase
          ( do
              s <- S.execStateT (update tref (IntVal 5)) extendedStore
              v <- S.evalStateT (index tref) s
              assertEqual "" (IntVal 5) v
          )
      ]

test_resolveVar :: Test
test_resolveVar =
  "resolveVar tests"
    ~: TestList
      [ TestCase
          ( do
              rf <- S.evalStateT (resolveVar (Name "x")) initialStore
              assertEqual "" (Ref "x") rf
          ),
        TestCase
          ( do
              rf <- S.evalStateT (resolveVar (Name "x")) extendedStore
              assertEqual "" (Ref "x") rf
          ),
        TestCase
          ( do
              rf <- S.evalStateT (resolveVar (Name "z")) initialStore
              assertEqual "" (Ref "z") rf
          ),
        TestCase
          ( do
              rf <- S.evalStateT (resolveVar $ Dot (Var (Name "z")) "a") extendedStore
              assertEqual "" NoRef rf
          ),
        TestCase
          ( do
              rf <- S.evalStateT (resolveVar $ Dot (Var (Name "t")) "a") extendedStore
              assertEqual "" (TableRef ("_tenv1", StringVal "a")) rf
          ),
        TestCase
          ( do
              rf <- S.evalStateT (resolveVar $ Proj (Var (Name "t")) (Var (Name "c"))) extendedStore
              assertEqual "" (TableRef ("_tenv1", StringVal "a")) rf
          ),
        TestCase
          ( do
              rf <- S.evalStateT (resolveVar $ Proj (Var (Name "t")) (Var (Name "zz"))) extendedStore
              assertEqual "" (TableRef ("_tenv1", NilVal)) rf
          )
      ]

test_evaluateNot :: Test
test_evaluateNot =
  "evaluate not"
    ~: TestList
      [ TestCase
          ( do
              (v, _) <- evaluate (Op1 Not (Val NilVal)) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op1 Not (Val (IntVal 3))) initialStore
              assertEqual "" (BoolVal False) v
          )
      ]

test_evaluateLen :: Test
test_evaluateLen =
  "evaluate len"
    ~: TestList
      [ TestCase
          ( do
              (v, _) <- evaluate (Op1 Len (Val (StringVal "5520"))) extendedStore
              assertEqual "" (IntVal 4) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op1 Len (Val (EnvTableK "_tenv1"))) extendedStore
              assertEqual "" (IntVal 2) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op1 Len (Val (IntVal 5520))) extendedStore
              assertEqual "" (IntVal 5520) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op1 Len (Val (BoolVal True))) extendedStore
              assertEqual "" (IntVal 1) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op1 Len (Val NilVal)) extendedStore
              assertEqual "" NilVal v
          )
      ]

test_tableConst :: Test
test_tableConst =
  "testing tableConst "
    ~: TestList
      [ TestCase
          ( do
              (_, s') <- evaluate (TableConst [FieldName "x" (Val (IntVal 3))]) initialStore
              (v', s'') <- S.runStateT (index (Ref "_tenv1")) s'
              case v' of
                Table t -> assert $ t == Map.fromList [(StringVal "x", IntVal 3)]
                _ -> assert False
          ),
        TestCase
          ( do
              (_, s') <- evaluate (TableConst [FieldName "x" (Val (IntVal 3)), FieldName "y" (Val (IntVal 5))]) initialStore
              (v', s'') <- S.runStateT (index (Ref "_tenv1")) s'
              case v' of
                Table t -> assert $ t == Map.fromList [(StringVal "x", IntVal 3), (StringVal "y", IntVal 5)]
                _ -> assert False
          ),
        TestCase
          ( do
              (_, s') <- evaluate (TableConst [FieldKey (Val (StringVal "x")) (Val (IntVal 3))]) initialStore
              (v', s'') <- S.runStateT (index (Ref "_tenv1")) s'
              case v' of
                Table t -> assert $ t == Map.fromList [(StringVal "x", IntVal 3)]
                _ -> assert False
          ),
        TestCase
          ( do
              (_, s') <- evaluate (TableConst [FieldKey (Val (StringVal "x")) (Val (IntVal 3)), FieldName "y" (Val (IntVal 5))]) initialStore
              (v', s'') <- S.runStateT (index (Ref "_tenv1")) s'
              case v' of
                Table t -> assert $ t == Map.fromList [(StringVal "x", IntVal 3), (StringVal "y", IntVal 5)]
                _ -> assert False
          ),
        TestCase
          ( do
              (_, s') <- evaluate (TableConst []) initialStore
              (v', s'') <- S.runStateT (index (Ref "_tenv1")) s'
              case v' of
                Table t -> assert $ t == Map.empty
                _ -> assert False
          )
      ]

test_evalOp2 :: Test
test_evalOp2 =
  "evaluate Op2"
    ~: TestList
      [ TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Plus (Val (IntVal 1))) initialStore
              assertEqual "" (IntVal 4) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Minus (Val (IntVal 1))) initialStore
              assertEqual "" (IntVal 2) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Times (Val (IntVal 1))) initialStore
              assertEqual "" (IntVal 3) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 4)) Divide (Val (IntVal 2))) initialStore
              assertEqual "" (IntVal 2) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Divide (Val (IntVal 0))) initialStore
              assertEqual "" NilVal v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Modulo (Val (IntVal 0))) initialStore
              assertEqual "" NilVal v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Modulo (Val (IntVal 2))) initialStore
              assertEqual "" (IntVal 1) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Eq (Val (IntVal 2))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Eq (Val (IntVal 3))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Gt (Val (IntVal 2))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Gt (Val (IntVal 3))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Gt (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 3))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 2))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Ge (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Lt (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 5)) Lt (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Lt (Val (IntVal 3))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Le (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 3)) Le (Val (IntVal 3))) initialStore
              assertEqual "" (BoolVal True) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (IntVal 5)) Le (Val (IntVal 4))) initialStore
              assertEqual "" (BoolVal False) v
          ),
        TestCase
          ( do
              (v, _) <- evaluate (Op2 (Val (StringVal "hello ")) Concat (Val (StringVal "world!"))) initialStore
              assertEqual "" (StringVal "hello world!") v
          )
      ]

tExecTest :: Test
tExecTest =
  "exec wTest"
    ~: TestCase
      ( do
          s <- exec wTest initialStore
          v <- S.evalStateT (index (Ref "x")) s
          assertEqual "" (IntVal 0) v
          v' <- S.evalStateT (index (Ref "y")) s
          assertEqual "" (IntVal 10) v'
      )

tExecFact :: Test
tExecFact =
  "exec wFact"
    ~: TestCase
      ( do
          s <- exec wFact initialStore
          v <- S.evalStateT (index (Ref "f")) s
          assertEqual "" (IntVal 120) v
          v' <- S.evalStateT (index (Ref "n")) s
          assertEqual "" (IntVal 0) v'
          v'' <- S.evalStateT (index (Ref "x")) s
          assertEqual "" (IntVal 1) v''
          v''' <- S.evalStateT (index (Ref "z")) s
          assertEqual "" (IntVal 120) v'''
      )

tExecAbs :: Test
tExecAbs =
  "exec wAbs"
    ~: TestCase
      ( do
          s <- exec wAbs initialStore
          v <- S.evalStateT (index (Ref "x")) s
          assertEqual "" (IntVal 3) v
      )

tExecTimes :: Test
tExecTimes =
  "exec wTimes"
    ~: TestCase
      ( do
          s <- exec wTimes initialStore
          v <- S.evalStateT (index (Ref "x")) s
          assertEqual "" (IntVal 0) v
          v' <- S.evalStateT (index (Ref "y")) s
          assertEqual "" (IntVal 3) v'
          v'' <- S.evalStateT (index (Ref "z")) s
          assertEqual "" (IntVal 30) v''
      )

tExecTable :: Test
tExecTable =
  "exec wTable"
    ~: TestCase
      ( do
          s <- exec wTable initialStore
          v <- S.evalStateT (index (Ref "a")) s
          assertEqual "" (EnvTableK "_tenv1") v
          v' <- S.evalStateT (index (Ref "k")) s
          assertEqual "" (IntVal 20) v'
          v'' <- S.evalStateT (index (Ref "o1")) s
          assertEqual "" (IntVal 10) v''
          v''' <- S.evalStateT (index (Ref "o2")) s
          assertEqual "" (StringVal "great") v'''
          v'''' <- S.evalStateT (index (Ref "o3")) s
          assertEqual "" (IntVal 11) v''''
          t <- S.evalStateT (index (TableRef ("_tenv1", IntVal 20))) s
          assertEqual "" (StringVal "great") t
          t' <- S.evalStateT (index (TableRef ("_tenv1", StringVal "x"))) s
          assertEqual "" (IntVal 11) t'
      )

tExecBfs :: Test
tExecBfs = 
  "exec wBfs" 
  ~: TestCase 
    ( do
      s <- exec wBfs initialStore
      v <- S.evalStateT (index (Ref "found")) s
      assertEqual "" (BoolVal True) v
    )

test_exec :: Test
test_exec = TestList [tExecTest, tExecFact, tExecAbs, tExecTimes, tExecTable, tExecBfs]

test_all :: IO Counts
test_all = runTestTT $ TestList [test_index, test_update, test_resolveVar, test_evaluateNot, test_evaluateLen, test_tableConst, test_evalOp2, test_exec]

instance QC.Arbitrary (StateT Store IO Store) where
  arbitrary :: QC.Gen (StateT Store IO Store)
  arbitrary = do
    len <- QC.chooseInt (0, 200)
    vals <- QC.vectorOf len (QC.arbitrary :: QC.Gen Value)
    refs <- QC.vectorOf len (Ref <$> genStringLit)
    let entries = zip refs vals
    return $ foldM f initialStore entries

f :: Store -> (Reference, Value) -> StateT Store IO Store
f s (r, v) = update r v >> S.get >>= \s' -> return s'

prop_updates_bound :: StateT Store IO Store -> QC.Property
prop_updates_bound state = do
  QM.monadicIO (test state)
  where
    test :: StateT Store IO Store -> QM.PropertyM IO Bool
    test st = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      let e = env s
      let store = globalstore s
      return $ Map.foldr (\a b -> Map.member a store && b) True e

prop_updateOverwrite ::
  StateT Store IO Store ->
  String ->
  Value ->
  Value ->
  QC.Property
prop_updateOverwrite state r v v' = do
  QM.monadicIO (test state (Ref r) v v')
  where
    test :: StateT Store IO Store -> Reference -> Value -> Value -> QM.PropertyM IO Bool
    test st r v v' = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      (_, s') <- S.runStateT (update r v) s
      (_, s'') <- S.runStateT (update r v') s'
      (value, _) <- S.runStateT (index r) s''
      return (value == v')

prop_argsBound :: StateT Store IO Store -> [String] -> [Value] -> QC.Property
prop_argsBound state ss vs = QM.monadicIO (test state ss (Val <$> filter (/= NilVal) vs))
  where
    test :: StateT Store IO Store -> [String] -> [Expression] -> QM.PropertyM IO Bool
    test st args vs = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      (fstr, _) <- S.runStateT (setEnv args vs initialStore) s
      let fenv = env fstr
       in return $ foldr (\name acc -> Map.member name fenv && acc) True args

prop_tableSound :: StateT Store IO Store -> [Value] -> [Value] -> QC.Property
prop_tableSound state keys vals = QM.monadicIO (test state (zip keys vals))
  where
    test :: StateT Store IO Store -> [(Value, Value)] -> QM.PropertyM IO Bool
    test st assocs = QM.run $ do
      (_, s) <- S.runStateT st initialStore
      (v, s') <- S.runStateT (allocateTable assocs) s
      case v of
        EnvTableK k -> do
          (tbl, s'') <- S.runStateT (index (Ref k)) s'
          case tbl of
            Table table -> return $ foldr (\(key, val) acc -> (table ! key == val) && acc) False (filter ((/= NilVal) . fst) assocs)
            _ -> return False
          return True
        _ -> return False

instance Show (StateT Store IO a) where
  show :: StateT Store IO a -> String
  show state = "state"

qc :: IO ()
qc = do
  putStrLn "prop update bound"
  QC.quickCheck prop_updates_bound
  putStrLn "prop argsBound"
  QC.quickCheck prop_argsBound
  putStrLn "prop updateOverwrite"
  QC.quickCheck prop_updateOverwrite
  putStrLn "prop tableSound"
  QC.quickCheck prop_tableSound
  return ()