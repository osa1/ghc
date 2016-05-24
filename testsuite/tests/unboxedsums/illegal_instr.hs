{-# LANGUAGE UnboxedSums, MagicHash, BangPatterns #-}

module Main where

import GHC.Prim
import GHC.Types

-- This fails with:
--
--   [1 of 1] Compiling Main             ( illegal_instr.hs, illegal_instr.o )
--   /tmp/ghc26928_0/ghc_2.s: Assembler messages:
--
--   /tmp/ghc26928_0/ghc_2.s:341:0: error:
--        Error: operand type mismatch for `movsd'
--   `gcc' failed in phase `Assembler'. (Exit code: 1)
--
-- The program is CoreLint-safe, but CmmLint fails:
--
--   Cmm lint error:
--     in basic block cTh
--       in assignment:
--         _gRg::I64 = _sQU::F32;   // CmmAssign
--         Reg ty: I64
--         Rhs ty: F32

data D = D (# Int# | Float# #)

instance Show D where
  show (D (# _ | #)) = "left"
  show (D (# | _ #)) = "right"

main :: IO ()
main = do
    !(F# f) <- readLn
    !(I# i) <- readLn
    print (D (# | f #))
    print (D (# i | #))
