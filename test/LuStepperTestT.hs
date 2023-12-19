module LuStepperTestT (test_all) where

import Control.Monad.State (StateT)
import Control.Monad.State qualified as S
import Data.Map (Map, (!?))
import Data.Map qualified as Map
import LuStepper
import LuSyntax
import Test.HUnit
import Test.QuickCheck qualified as QC

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

--     ~?= Map.fromList
--       [ ( globalTableName,
--           Map.fromList
--             [ (StringVal "a", TableVal "_t1"),
--               (StringVal "k", IntVal 20),
--               (StringVal "o1", IntVal 10),
--               (StringVal "o2", StringVal "great"),
--               (StringVal "o3", IntVal 11)
--             ]
--         ),
--         ("_t1", Map.fromList [(IntVal 20, StringVal "great"), (StringVal "x", IntVal 11)])
--       ]

-- tExecBfs :: Test
-- tExecBfs = "exec wBfs" ~: TestList [global !? StringVal "found" ~?= Just (BoolVal True)]
--   where
--     ss = exec wBfs initialStore
--     global = case ss !? globalTableName of
--       Just g -> g
--       Nothing -> Map.empty

test_exec :: Test
test_exec = TestList [tExecTest, tExecFact, tExecAbs, tExecTimes, tExecTable]

test_all :: IO Counts
test_all = runTestTT $ TestList [test_index, test_update, test_resolveVar, test_evaluateNot, test_evaluateLen, test_tableConst, test_evalOp2, test_exec]
