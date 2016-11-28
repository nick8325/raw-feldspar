{-# LANGUAGE QuasiQuotes, ScopedTypeVariables #-}

module Demo where



import qualified Prelude

import Feldspar.Run
import Feldspar.Verify
import Feldspar.Data.Vector

absolute :: Run ()
absolute = do
  printf "Enter a number: "
  n :: Data Int32 <- fget stdin
  iff (n == minBound) (printf "Don't enter minBound\n") $ do
    ref <- initRef n
    -- Written in an ugly way just to check the verification
    i <- getRef ref
    iff (i < 0) (setRef ref (negate i)) (return ())

    i <- getRef ref
    assert (i >= 0) "Absolute value is negative"
    assert (i == n || i == negate n) "Absolute value is wrong"
    printf "The absolute value is %d\n" i

blah :: Run ()
blah = do
  ref <- initRef =<< fget stdin
  i :: Data Int32 <- unsafeFreezeRef ref

  for (0, 1, Excl (5 :: Data Int32)) $ \_ -> do
    j <- unsafeFreezeRef ref
    iff (j > 2) (setRef ref 3) (return ())
  j <- unsafeFreezeRef ref
  iff (j < 2) (printf "%d\n" i) (return ())

-- A super-simple verification example.
count :: Run ()
count = do
  printf "Enter a number: "
  n :: Data Word32 <- fget stdin

  let total = forLoop n 0 (\i n -> hintVal (n == i) $ i + 1)
  total <- initRef total >>= unsafeFreezeRef
  assert (total == n) "Count is wrong"
  printf "The count is %d\n" total

------------------------------------------------------------

test_scProd1 = do
    n <- fget stdin
    printf "result: %.3f\n" $
      (scProd (fmap i2n (0 ... n-1)) (fmap i2n (2 ... n+1)) :: Data Double)

test_scProd2 = do
    n  <- fget stdin
    v1 <- manifestFresh $ fmap i2n (0 ... n-1)
    v2 <- manifestFresh $ fmap i2n (2 ... n+1)
    printf "result: %.3f\n" (scProd v1 v2 :: Data Double)

map_inplace :: Run ()
map_inplace = do
    n   <- fget stdin
    loc <- newArr n
    vec <- manifest loc (0 ... n-1)
    manifestStore loc $ map (+1) vec
    vec <- unsafeFreezeArr loc
    printf "result: %d\n" $ sum vec

map2_inplace :: Run ()
map2_inplace = do
    n   <- fget stdin
    assert (n < maxBound) "oops"
    loc :: Arr (Data Word32) <- newArr (n+1)
    vec <- unsafeFreezeArr loc
    for (0, 1, Excl (n :: Data Word32)) $ \i -> do
      setArr loc i (arrIx vec i+1)

tail_inplace :: Run ()
tail_inplace = do
    n <- fget stdin
    loc :: Arr (Data Word32) <- newArr n
    vec <- unsafeFreezeArr loc
    let when cond x = iff cond x (return ())
    when (n > 0) $
      for (0, 1, Excl (n-1)) $ \i -> do
        setArr loc i (arrIx vec (i+1)+1)

filter_inplace :: Run ()
filter_inplace = do
    n <- fget stdin
    loc :: Arr (Data Word32) <- newArr n
    vec <- unsafeFreezeArr loc
    ref <- initRef 0
    let when cond x = iff cond x (return ())
    for (0, 1, Excl n) $ \i -> do
      let x = arrIx vec i
      when (x > 5) $ do
        j <- unsafeFreezeRef ref
        hint (j <= i)
        setArr loc j x
        setRef ref (j+1)

rev_inplace :: Run ()
rev_inplace = do
    n <- fget stdin
    loc :: Arr (Data Word32) <- newArr n
    vec <- unsafeFreezeArr loc >>= unsafeThawArr
    for (0, 1, Excl (n `div` 2 :: Data Word32)) $ \i -> do
      x <- getArr vec i
      y <- getArr vec (n-i-1)
      setArr loc i y
      setArr loc (n-i-1) x

-- ------------------------------------------------------------

-- testAll = do
--     tag "sumInput"     >> compareCompiled sumInput     (runIO sumInput) (Prelude.unlines $ Prelude.map show $ Prelude.reverse [0..20])
--     tag "printFib"     >> compareCompiled printFib     (runIO printFib)     "7\n"
--     tag "test_scProd1" >> compareCompiled test_scProd1 (runIO test_scProd1) "20\n"
--     tag "test_scProd2" >> compareCompiled test_scProd2 (runIO test_scProd2) "20\n"
--     tag "map_inplace"  >> compareCompiled map_inplace  (runIO map_inplace)  "20\n"
--   where
--     tag str = putStrLn $ "---------------- examples/Demo.hs/" Prelude.++ str Prelude.++ "\n"

