{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

-- Copyright (c) 2013, Emil Axelsson, Peter Jonsson, Anders Persson and
--                     Josef Svenningsson
-- Copyright (c) 2012, Emil Axelsson, Gergely Dévai, Anders Persson and
--                     Josef Svenningsson
-- Copyright (c) 2009-2011, ERICSSON AB
-- All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
--     * Redistributions of source code must retain the above copyright notice,
--       this list of conditions and the following disclaimer.
--     * Redistributions in binary form must reproduce the above copyright
--       notice, this list of conditions and the following disclaimer in the
--       documentation and/or other materials provided with the distribution.
--     * Neither the name of the ERICSSON AB nor the names of its contributors
--       may be used to endorse or promote products derived from this software
--       without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
-- DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
-- FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
-- DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
-- SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
-- CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
-- OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

module FFTNew
  ( fftP
  ) where



import Prelude ()

import Feldspar.Run
import Feldspar.Data.Vector
import Feldspar.Data.Buffered
import Feldspar.Verify



rotBit :: Data Index -> Data Index -> Data Index
rotBit k i = lefts .|. rights
  where
    k'     = i2n k
    ir     = i .>>. 1
    rights = ir .&. oneBits k'
    lefts  = (((ir .>>. k') .<<. 1) .|. (i .&. 1)) .<<. k'

riffle :: (Pully pull a, Syntax a) => Data Index -> pull -> Pull a
riffle = backPermute . const . rotBit

bitRev :: (Manifestable Run vec a, Finite vec, Syntax a)
    => Store a
    -> Data Length
    -> vec
    -> Run (Manifest a)
bitRev st n = loopStore st (1,1,Incl n) $ \i -> return . riffle i

testBit :: (Bits a, Num a, PrimType a) => Data a -> Data Index -> Data Bool
testBit a i = a .&. (1 .<<. i2n i) /= 0

-- changes compared to FFT.hs are below here

insertZero :: (Bits a, Num a, PrimType a) => Data Index -> Data a -> Data a
insertZero i a = a + (a .&. (allOnes .<<. (i2n i)))


flipBit :: (Bits a, Num a, PrimType a) => Data Index -> Data a -> Data a
flipBit k = (`xor` (1 .<<. (i2n k)))





-- same type as fftCore
fftCoreP
    :: ( Manifestable Run vec (Data (Complex a))
       , Finite vec
       , RealFloat a
       , PrimType a
       , PrimType (Complex a)
       )
    => Store (Data (Complex a))
    -> Bool  -- ^ Inverse?
    -> Data Length
    -> vec
    -> Run (DManifest (Complex a))
fftCoreP st inv n = loopStore st (n+1,-1,Incl 1) $ \i -> return . ilv2 (i-1)
    -- Note: Cannot loop from n to 0 because 0-1 is `maxBound`, so the loop will
    -- go on forever.
  where
   ilv2 k vec = Push n $ \write ->
     dumpPush (toPush vs) $ \i (a,b) -> do
       write (left i) a
       write (right i) b
          
      where
        n = length vec
        k'   = i2n k
        k2   = 1 .<<. k' :: Data Index
        left = insertZero k
        right = flipBit k . left
        vs = Pull n2 ixf
        n2 = n `div` 2
        ixf j = (a+b,twid*(a-b))
          where
            a    = vec ! (left j)
            b    = vec ! (right j)
            twid = polar 1 ((if inv then π else -π) * i2n (lsbs k' (right j)) / i2n k2)
            


fftP'
    :: ( Manifestable Run vec (Data (Complex a))
       , Finite vec
       , RealFloat a
       , PrimType a
       , PrimType (Complex a)
       )
    => Store (Data (Complex a))
    -> Bool  -- ^ Inverse?
    -> vec
    -> Run (DManifest (Complex a))
fftP' st inv v = do
    n <- shareM (ilog2 (length v) - 1)
    v <- fftCoreP1 st inv n v
    st <- replaceBackingStore (length v) st
    bitRev st n v

-- | Radix-2 Decimation-In-Frequency Fast Fourier Transformation of the given
-- complex vector. The given vector must be power-of-two sized, (for example 2,
-- 4, 8, 16, 32, etc.) The output is non-normalized.
fftP
    :: ( Manifestable Run vec (Data (Complex a))
       , Finite vec
       , RealFloat a
       , PrimType a
       , PrimType (Complex a)
       )
    => Store (Data (Complex a))
    -> vec
    -> Run (DManifest (Complex a))
fftP st = fftP' st False
          
            







-- same type as fftCore
fftCoreP1
    :: ( Manifestable Run vec (Data (Complex a))
       , Finite vec
       , RealFloat a
       , PrimType a
       , PrimType (Complex a)
       )
    => Store (Data (Complex a))
    -> Bool  -- ^ Inverse?
    -> Data Length
    -> vec
    -> Run (DManifest (Complex a))
fftCoreP1 st inv n = loopStore st (n+1,-1,Incl 1) $ \i -> return . ilv2 (i-1)
    -- Note: Cannot loop from n to 0 because 0-1 is `maxBound`, so the loop will
    -- go on forever.
  where
    -- ilv2 :: Data Index -> DManifest (Complex a) -> DPush Run (Complex a)
    ilv2 k vec = Push n $ \write ->
        for (0,1,Excl n2) $ \i -> do
          li <- shareM (left i)
          ri <- shareM (right i)
          a <- shareM (vec ! li)
          b <- shareM (vec ! ri)
          let twid = polar 1 ((if inv then π else -π) * i2n (lsbs k' ri) / i2n k2)
          write li (a+b)
          write ri (twid*(a-b))
      where
        n     = length vec
        n2    = n `div` 2
        k'    = i2n k
        k2    = 1 .<<. k' :: Data Index
        left  = insertZero k
        right = flipBit k . left



fftSize :: DManifest (Complex Double) -> Run (DManifest (Complex Double))
fftSize vec = do
  assert (length vec .&. (length vec - 1) == 0) "wrong size"
  st <- newInPlaceStore (length vec)
  fftP st vec

fftSizeRun = connectStdIO fftSize
