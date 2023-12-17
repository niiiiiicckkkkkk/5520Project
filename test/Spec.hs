import LuParserTest qualified as LP
import LuStepperTestT qualified as LS

main :: IO ()
main = do
  putStrLn "*** Testing LuParser ***"
  LP.test_all -- unit tests
  LP.qc -- quickcheck properties
  putStrLn "*** Testing LuStepper ***"
  LS.test_all -- unit tests
  -- LS.qc -- quickcheck properties
  return ()
