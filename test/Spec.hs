import LuParserTest qualified as LP
import LuStepperTest qualified as LS
import Test.HUnit

main :: IO Counts
main = LS.test_all

-- putStrLn "*** Testing LuParser ***"
-- LP.test_all -- unit tests
-- LP.qc -- quickcheck properties
-- putStrLn "*** Testing LuStepper ***"
-- unit tests

-- LS.qc -- quickcheck properties
