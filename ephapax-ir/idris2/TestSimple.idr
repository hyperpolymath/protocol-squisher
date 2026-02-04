-- SPDX-License-Identifier: PMPL-1.0-or-later
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Protocol Squisher - Simple IR Test

module TestSimple

import Types
import Compat

%default total

-- Test 1: Exact match should be Concorde
test1 : TransportClass
test1 = analyzeCompatibility (Prim I32) (Prim I32)

-- Test 2: Widening should be Business
test2 : TransportClass
test2 = analyzeCompatibility (Prim I32) (Prim I64)

-- Test 3: Incompatible should be Wheelbarrow
test3 : TransportClass
test3 = analyzeCompatibility (Prim I32) (Prim Str)

-- Test 4: Same container should be Business
test4 : TransportClass
test4 = analyzeCompatibility
  (Container Vec (Prim I32))
  (Container Vec (Prim I64))

-- Verify all tests
main : IO ()
main = do
  putStrLn "Test 1 (I32 -> I32):"
  putStrLn $ show test1 ++ " (expected: Concorde)"
  putStrLn "\nTest 2 (I32 -> I64):"
  putStrLn $ show test2 ++ " (expected: Business)"
  putStrLn "\nTest 3 (I32 -> String):"
  putStrLn $ show test3 ++ " (expected: Wheelbarrow)"
  putStrLn "\nTest 4 (Vec<I32> -> Vec<I64>):"
  putStrLn $ show test4 ++ " (expected: Business)"
