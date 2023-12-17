module LuParserTest (qc, test_all) where

import Control.Applicative
import LuParser
import LuSyntax
import Parser qualified as P
import Test.HUnit
import Test.QuickCheck qualified as QC

-- | LuParser Unit Tests
test_wsP :: Test
test_wsP =
  TestList
    [ P.parse (wsP P.alpha) "a" ~?= Right 'a',
      P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
      P.parse (wsP P.alpha) "   " ~?= Left "No parses"
    ]

test_stringP :: Test
test_stringP =
  TestList
    [ P.parse (stringP "a") "a" ~?= Right (),
      P.parse (stringP "a") "b" ~?= Left "No parses",
      P.parse (many (stringP "a")) "a  a" ~?= Right [(), ()],
      P.parse (stringP "abcd") "ab" ~?= Left "No parses"
    ]

test_constP :: Test
test_constP =
  TestList
    [ P.parse (constP "&" 'a') "&  " ~?= Right 'a',
      P.parse (many (constP "&" 'a')) "&   &" ~?= Right "aa",
      P.parse (constP "  & " 'a') "  ! " ~?= Left "No parses"
    ]

test_brackets :: Test
test_brackets =
  TestList
    [ P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1, 1, 1],
      P.parse (many (brackets (brackets (constP "1" 1)))) "[[1]] [[  1]]   [1 ]" ~?= Right [1, 1],
      P.parse (many (brackets (constP "1" 1))) "[[1]]" ~?= Right []
    ]

test_stringValP :: Test
test_stringValP =
  TestList
    [ P.parse stringValP "\"a\"" ~?= Right (StringVal "a"),
      P.parse stringValP "\"a\\\"\"" ~?= Right (StringVal "a\\"),
      P.parse (many stringValP) "\"a\"   \"b\"" ~?= Right [StringVal "a", StringVal "b"],
      P.parse (many stringValP) "\" a\"   \"b\"" ~?= Right [StringVal " a", StringVal "b"],
      P.parse (many stringValP) "\"a   \"  \"   c\"" ~?= Right [StringVal "a   ", StringVal "   c"],
      P.parse (many stringValP) "\"a   \" \"  \"  \"   c\"" ~?= Right [StringVal "a   ", StringVal "  ", StringVal "   c"]
    ]

tNameP :: Test
tNameP =
  "parse name"
    ~: TestList
      [ P.parse (many nameP) "x sfds _ nil !bad 2alsobad" ~?= Right ["x", "sfds", "_"],
        P.parse (many nameP) "x_x s123 and2 andgood" ~?= Right ["x_x", "s123", "and2", "andgood"],
        P.parse (many nameP) "_12 _34 until" ~?= Right ["_12", "_34"]
      ]

tuopP :: Test
tuopP =
  "parse tuopP"
    ~: TestList
      [ P.parse (many uopP) "- - #" ~?= Right [Neg, Neg, Len],
        P.parse (many uopP) "not - - # notSomething" ~?= Right [Not, Neg, Neg, Len],
        P.parse (many uopP) "not not not not #" ~?= Right [Not, Not, Not, Not, Len]
      ]

test_bopP :: Test
test_bopP =
  "Parsing bopP"
    ~: TestList
      [ P.parse (many bopP) "+ - * // % ==" ~?= Right [Plus, Minus, Times, Divide, Modulo, Eq],
        P.parse (many bopP) "> >= < <= .." ~?= Right [Gt, Ge, Lt, Le, Concat],
        P.parse (many bopP) "> >= $ <=" ~?= Right [Gt, Ge],
        P.parse (many bopP) ">=.. <= ..>..<" ~?= Right [Ge, Concat, Le, Concat, Gt, Concat, Lt]
      ]

test_tableConstP :: Test
test_tableConstP =
  "Parsing tableConst"
    ~: TestList
      [ P.parse tableConstP "{ x = 2, [3] = false }" ~?= Right (TableConst [FieldName "x" (Val (IntVal 2)), FieldKey (Val (IntVal 3)) (Val (BoolVal False))]),
        P.parse tableConstP "{ abc = 3, [2] = true, [4] = false, [9] = \"here\"}" ~?= Right (TableConst [FieldName "abc" (Val (IntVal 3)), FieldKey (Val (IntVal 2)) (Val (BoolVal True)), FieldKey (Val (IntVal 4)) (Val (BoolVal False)), FieldKey (Val (IntVal 9)) (Val (StringVal "here"))])
      ]

tParseFiles :: Test
tParseFiles =
  "parse files"
    ~: TestList
      [ "fact" ~: p "lu/fact.lu" wFact,
        "test" ~: p "lu/test.lu" wTest,
        "abs" ~: p "lu/abs.lu" wAbs,
        "times" ~: p "lu/times.lu" wTimes,
        "table" ~: p "lu/table.lu" wTable,
        "bfs" ~: p "lu/bfs.lu" wBfs
      ]
  where
    p fn ast = do
      result <- parseLuFile fn
      case result of
        (Left _) -> assert False
        (Right ast') -> assert (ast == ast')

test_comb =
  "parsing combinators"
    ~: TestList
      [ P.parse (wsP P.alpha) "a" ~?= Right 'a',
        P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
        P.parse (stringP "a") "a" ~?= Right (),
        P.parse (stringP "a") "b" ~?= Left "No parses",
        P.parse (many (stringP "a")) "a  a" ~?= Right [(), ()],
        P.parse (constP "&" 'a') "&  " ~?= Right 'a',
        P.parse (many (constP "&" 'a')) "&   &" ~?= Right "aa",
        P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1, 1, 1]
      ]

test_value =
  "parsing values"
    ~: TestList
      [ P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1, IntVal 2, IntVal 3],
        P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True, BoolVal False, BoolVal True],
        P.parse (many nilValP) "nil nil\n nil" ~?= Right [NilVal, NilVal, NilVal],
        P.parse stringValP "\"a\"" ~?= Right (StringVal "a"),
        P.parse stringValP "\"a\\\"\"" ~?= Right (StringVal "a\\"),
        P.parse (many stringValP) "\"a\"   \"b\"" ~?= Right [StringVal "a", StringVal "b"],
        P.parse (many stringValP) "\" a\"   \"b\"" ~?= Right [StringVal " a", StringVal "b"]
      ]

test_exp =
  "parsing expressions"
    ~: TestList
      [ P.parse (many varP) "x y z" ~?= Right [Name "x", Name "y", Name "z"],
        P.parse varP "(x.y[1]).z" ~?= Right (Dot (Var (Proj (Var (Dot (Var (Name "x")) "y")) (Val (IntVal 1)))) "z"),
        P.parse (many nameP) "x sfds _ nil" ~?= Right ["x", "sfds", "_"],
        P.parse (many uopP) "- - #" ~?= Right [Neg, Neg, Len],
        P.parse (many bopP) "+ >= .." ~?= Right [Plus, Ge, Concat],
        P.parse tableConstP "{ x = 2, [3] = false }"
          ~?= Right (TableConst [FieldName "x" (Val (IntVal 2)), FieldKey (Val (IntVal 3)) (Val (BoolVal False))])
      ]

test_stat =
  "parsing statements"
    ~: TestList
      [ P.parse statementP ";" ~?= Right Empty,
        P.parse statementP "x=3" ~?= Right (Assign (Name "x") (Val (IntVal 3))),
        P.parse statementP "if x then y=nil else end"
          ~?= Right (If (Var (Name "x")) (Block [Assign (Name "y") (Val NilVal)]) (Block [])),
        P.parse statementP "while nil do end"
          ~?= Right (While (Val NilVal) (Block [])),
        P.parse statementP "repeat ; ; until false"
          ~?= Right (Repeat (Block [Empty, Empty]) (Val (BoolVal False)))
      ]

test_functioncall :: Test
test_functioncall =
  "parsing function calls"
    ~: TestList
      [ P.parse fCallP "f()" ~?= Right (Call (Name "f") []),
        P.parse fCallP "_myfunction (1 + 1, x, g(3))"
          ~?= Right
            ( Call
                (Name "_myfunction")
                [ Op2 (Val $ IntVal 1) Plus (Val $ IntVal 1),
                  Var $ Name "x",
                  CallExp $ Call (Name "g") [Val $ IntVal 3]
                ]
            ),
        P.parse fCallP "t.foo(\"bar\")" ~?= Right (Call (Dot (Var $ Name "t") "foo") []),
        P.parse fCallP "t.foo[\"bar\"]({a = 3, [2] = \"two\"})"
          ~?= Right
            ( Call
                (Proj (Var $ Dot (Var $ Name "t") "foo") (Var $ Name "bar"))
                [TableConst [FieldName "a" (Val (IntVal 3)), FieldKey (Val (IntVal 2)) (Val $ StringVal "two")]]
            )
      ]

test_functiondef :: Test
test_functiondef =
  "parsing function definitions"
    ~: TestList
      [ P.parse fDefP "function () end" ~?= Right (Def [] (Block [])),
        P.parse fDefP "function (arg1, arg2) y = x + y\n return arg1\n end"
          ~?= Right
            ( Def
                ["arg1", "arg2"]
                ( Block
                    [ Assign (Name "y") (Op2 (Var $ Name "x") Plus (Var $ Name "y")),
                      Return $ Var $ Name "arg1"
                    ]
                )
            ),
        P.parse statementP "function foo(x)\n ; end"
          ~?= Right (Assign (Name "foo") (DefExp $ Def ["x"] (Block [Empty])))
      ]

test_all :: IO Counts
test_all = runTestTT $ TestList [test_comb, test_value, test_exp, test_stat, tParseFiles]

-- | quickcheck properties and exported test
prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = P.parse statementP (pretty s) == Right s

qc :: IO ()
qc = do
  putStrLn "roundtrip_val"
  QC.quickCheck prop_roundtrip_val
  putStrLn "roundtrip_exp"
  QC.quickCheck prop_roundtrip_exp
  putStrLn "roundtrip_stat"
  QC.quickCheck prop_roundtrip_stat