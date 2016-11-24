{-# LANGUAGE QuasiQuotes #-}

module Demo where



import qualified Prelude

import Feldspar.Run
import Feldspar.Verify
import Feldspar.Data.Vector

absolute :: Run ()
absolute = do
  printf "Enter a number: "
  n <- fget stdin
  iff (n == minBound) (printf "Don't enter minBound\n") $ do
    ref <- initRef n :: Run (Ref Int32)
    -- Written in an ugly way just to check the verification
    i <- getRef ref
    iff (i < 0) (setRef ref (negate i)) (return ())

    i <- getRef ref
    assert (i >= 0) "Absolute value is negative"
    assert (i == n || i == negate n) "Absolute value is wrong"
    printf "The absolute value is %d\n" i

blah :: Run ()
blah = do
  ref <- initRef =<< fget stdin :: Run (Ref Int32)
  i <- unsafeFreezeRef ref :: Run (Data Int32)

  for (0, 1, Excl (5 :: Data Int32)) $ \_ -> do
    j <- unsafeFreezeRef ref :: Run (Data Int32)
    iff (j > 2) (setRef ref (3 :: Data Int32)) (return ())
  j <- unsafeFreezeRef ref :: Run (Data Int32)
  iff (j < 2) (printf "%d\n" i) (return ())

oops :: Run ()
oops = do
  ref <- initRef (3 :: Data Word32)
  x   <- unsafeFreezeRef ref

  setRef ref (4 :: Data Word32)
  y   <- unsafeFreezeRef ref
  -- XXX this isn't safe.
  -- Need to make dryInterp return fresh variable each time.
  -- To do: transform program back properly, instead of using patch.
  -- That way we don't need variable names to match up.
  printf "%d\n" (x :: Data Word32)
  printf "%d\n" (y :: Data Word32)

sigma :: Run ()
sigma = do
  printf "Enter a number: "
  n <- fget stdin

  let total = forLoop n 0 (\i n -> hintVal (2*n == i*(i-1)) $ i + n)
  total <- initRef total >>= unsafeFreezeRef
  assert (2*total == n*(n-1)) "Total is wrong"
  printf "The sum is %d\n" total

bsearch :: Run ()
bsearch = do
  n   <- newRef >>= unsafeFreezeRef
  x   <- newRef >>= unsafeFreezeRef
  sk  <- newRef >>= unsafeFreezeRef
  assert (sk < n) "skolem axiom"
  arr <- newArr n >>= unsafeFreezeArr :: Run (IArr Int32)
  lo <- initRef (0 :: Data Index)
  hi <- initRef (n :: Data Index)
  while (liftM2 (/=) (unsafeFreezeRef lo) (unsafeFreezeRef hi)) $ do
    do { lo <- unsafeFreezeRef lo; hi <- unsafeFreezeRef hi; assert (lo <= hi) "lohi" }
    do { lo <- unsafeFreezeRef lo; assert (lo < n) "lo" }
    do { hi <- unsafeFreezeRef hi; assert (hi <= n) "hi" }
    let avg x y = x + (y-x) `shiftR` 1
    mid <- liftM2 avg (unsafeFreezeRef lo) (unsafeFreezeRef hi)
    let y = arrIx arr mid :: Data Int32
    iff (x == y) (setRef lo mid >> setRef hi (mid+1) >> break) (iff (x < y) (setRef hi mid) (setRef lo (mid+1)))
  lo <- unsafeFreezeRef lo
  hi <- unsafeFreezeRef hi
  assert (not (arrIx arr sk == x) || lo <  hi) "value not found"
  assert (not (arrIx arr sk == x) || arrIx arr lo == x) "value not found"
  assert (not (arrIx arr lo == x) || lo <  hi) "value found"

bsearch' :: Run ()
bsearch' = do
  lo <- initRef (0 :: Data Index)
  while (liftM2 (/=) (unsafeFreezeRef lo) (unsafeFreezeRef lo)) $ do
    return ()

-- A super-simple verification example.
count :: Run ()
count = do
  printf "Enter a number: "
  n <- fget stdin

  let total = forLoop n 0 (\i n -> hintVal (n == i) $ i + 1)
  total <- initRef total >>= unsafeFreezeRef
  assert (total == n) "Count is wrong"
  printf "The count is %d\n" total

sumInput :: Run ()
sumInput = do
    done <- initRef false
    sum  <- initRef (0 :: Data Word32)
    while (not <$> getRef done) $ do
        printf "Enter a number (0 means done): "
        n <- fget stdin
        iff (n == 0)
          (setRef done true)
          (modifyRef sum (+n))
--     abort
--     printSum sum
    s <- getRef sum
    printf "The sum of your numbers is %d.\n" (s :: Data Word32)

abort :: Run ()
abort = do
    addInclude "<stdlib.h>"
    callProc "abort" []

printSum :: Ref Word32 -> Run ()
printSum s = do
    addDefinition printSum_def
    callProc "printSum" [refArg s]

printSum_def = [cedecl|
    void printSum (typename uint32_t * s) {
        printf ("I think the sum of your numbers is %d.\n", *s);
    }
    |]

-- Compiling and running:

comp_sumInput = icompile sumInput
run_sumInput  = runCompiled sumInput



------------------------------------------------------------

fib :: Data Word32 -> Data Word32
fib n = fst $ forLoop n (0,1) $ \_ (a,b) -> (b,a+b)

printFib :: Run ()
printFib = do
    printf "Enter a positive number: "
    n <- fget stdin
    printf "The %dth Fibonacci number is %d.\n" n (fib n)



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
    manifestStore loc $ map (*33) vec
    vec <- unsafeFreezeArr loc
    printf "result: %d\n" $ sum vec

map2_inplace :: Run ()
map2_inplace = do
    n   <- fget stdin
    loc <- newArr (n :: Data Word32)
    vec <- unsafeFreezeArr loc
    for (0, 1, Excl (n :: Data Word32)) $ \i -> do
      setArr i (arrIx vec (i+1)+1 :: Data Word32) loc :: Run ()

------------------------------------------------------------

testAll = do
    tag "sumInput"     >> compareCompiled sumInput     (runIO sumInput) (Prelude.unlines $ Prelude.map show $ Prelude.reverse [0..20])
    tag "printFib"     >> compareCompiled printFib     (runIO printFib)     "7\n"
    tag "test_scProd1" >> compareCompiled test_scProd1 (runIO test_scProd1) "20\n"
    tag "test_scProd2" >> compareCompiled test_scProd2 (runIO test_scProd2) "20\n"
    tag "map_inplace"  >> compareCompiled map_inplace  (runIO map_inplace)  "20\n"
  where
    tag str = putStrLn $ "---------------- examples/Demo.hs/" Prelude.++ str Prelude.++ "\n"

