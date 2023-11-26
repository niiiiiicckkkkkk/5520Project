import LuParserTest qualified as LP

main :: IO ()
main = do
  putStrLn "*** Testing LuParser ***"
  LP.test_all -- unit tests
  LP.qc -- quickcheck properties
