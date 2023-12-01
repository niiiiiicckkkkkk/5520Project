import Control.Applicative (Alternative (..))
import Data.Map ((!))
import Data.Map qualified as Map
import LuParser
import LuParserTest qualified as LP
import LuStepper
import LuStepperTest qualified as LS
import LuSyntax
import Parser qualified as P
import State qualified as S
import Test.HUnit
import Test.QuickCheck ((.&&.))
import Test.QuickCheck qualified as QC

main :: IO ()
main = undefined

{-
putStrLn "*** Testing LuParser ***"
LP.test_all -- unit tests
LP.qc -- quickcheck properties
putStrLn "*** Testing LuStepper ***"
LS.test_all -- unit tests
LS.qc -- quickcheck properties -}

-- all stores should have a vstore, fstore, and counter
-- counter non-negative
-- there are no "hanging" bindings
-- global and local tables always present in the vstore
prop_validStore :: Store -> QC.Property
prop_validStore store =
  QC.counterexample "missing global" (hasGlobalT store)
    .&&. QC.counterexample "missing local" (hasLocalT store)
  where
    hasGlobalT :: Store -> Bool
    hasGlobalT = Map.member "_G" . vstore
    hasLocalT :: Store -> Bool
    hasLocalT = Map.member "_L" . vstore
    clean :: Store -> Bool
    clean store = Map.foldr (foldaux store) False $ (! "_L") (vstore store)
    foldaux :: Store -> Value -> Bool -> Bool
    foldaux s (TableVal t) prev = (&& prev) . Map.member t $ vstore s
    foldaux s (FVal f) prev = (&& prev) . Map.member f $ fstore s
    foldaux _ _ prev = prev

valid :: Store -> Bool
valid store = hasGlobalT store && hasLocalT store && clean store
  where
    hasGlobalT :: Store -> Bool
    hasGlobalT = Map.member "_G" . vstore
    hasLocalT :: Store -> Bool
    hasLocalT = Map.member "_L" . vstore
    clean :: Store -> Bool
    clean store = Map.foldr (foldaux store) False $ (! "_L") (vstore store)
    foldaux :: Store -> Value -> Bool -> Bool
    foldaux s (TableVal t) prev = (&& prev) . Map.member t $ vstore s
    foldaux s (FVal f) prev = (&& prev) . Map.member f $ fstore s
    foldaux _ _ prev = prev

-- new bindings are properly added to the store
prop_updateValid :: Value -> Value -> Store -> Bool
prop_updateValid v1 v2 store =
  S.evalState (aux v1 v2 store) store
  where
    aux :: Value -> Value -> Store -> S.State Store Bool
    aux v1 v2 store = do
      S.put store
      update ("_L", v1) v2
      checkStore v1 v2 <$> S.get
    checkStore :: Value -> Value -> Store -> Bool
    checkStore v1 v2 store = valid store && updated v1 v2 store
    updated :: Value -> Value -> Store -> Bool
    updated v1 v2 store = case Map.lookup v1 (vstore store ! "_L") of
      Just val -> val == v2
      Nothing -> False

-- functions can only access global state and local variables

-- a random list of function params is properly initialized
prop_initFState :: [ArgN] -> [ArgV] -> Store -> Bool
prop_initFState = undefined

test_fCallP :: Test
test_fCallP =
  "parsing function calls" ~:
    TestList
      [ P.parse (fcallP) "foo(x, y, z)" ~?= Right Name "foo" [Name "x", Name "y", Name "z"],
        P.parse (fcallP) "bar(1 + 1, t.x)" ~?= Right Name "bar" [Op2 IntVal 1 Plus IntVal1, Dot Name "t" Name "x"]
      ]

test_fDefP :: Test
test_fDefP =
  "parsing function definitions" ~:
    TestList
      [ P.parse (fdefP) "function (x, y) return x + y end"
          ~?= Right [Name "x", Name "y"] Block [Return Op2 Name "x" Plus Name "y"]
      ]

test_fStatementP :: Test
test_fStatementP = undefined
