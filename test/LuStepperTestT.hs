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
            ("_tenv1", "_t0")
          ],
      globalstore =
        Map.fromList
          [ ("_v0", IntVal 3),
            ("_v1", StringVal "hello"),
            ("_v2", EnvTableK "_tenv1"),
            ("_t0", Table $ Map.fromList [(StringVal "a", IntVal 1), (StringVal "b", IntVal 2)])
          ],
      fstore =
        Map.fromList [("_f0", close1)],
      block =
        Block
          [Assign (Name "z") (Val (StringVal "ok!"))],
      history = Nothing,
      filename = Nothing
    }

xref :: Reference
xref = Ref "x"

tref :: Reference
tref = TableRef ("t", StringVal "a")

test_index :: Test
test_index =
  "index tests"
    ~: TestList
      [ TestCase
          ( do
              v <- S.evalStateT (index xref) extendedStore
              assertEqual "" (IntVal 3) v
          ),
        TestCase
          ( do
              v <- S.evalStateT (index xref) extendedStore
              assertEqual "" (IntVal 3) v
          )
      ]

test_all :: IO Counts
test_all = runTestTT $ TestList [test_index]
