{-# LANGUAGE NoMonomorphismRestriction #-}

import qualified Prelude

import qualified Data.Complex as Complex

import Feldspar.Run
import Feldspar.Data.Vector
import Feldspar.Data.Buffered

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Monadic as QC

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Demo
-- import qualified CoDesign
import qualified Concurrent
import DFT
import FFT



almostEq a b
    =          Complex.magnitude d Prelude.< 1e-7
    Prelude.&& Complex.phase d     Prelude.< 1e-7
  where
    d = abs (a-b)

a ~= b = Prelude.and $ Prelude.zipWith almostEq a b

wrapStore :: (Syntax a, Finite (vec a), MonadComp m) =>
    (Store a -> vec a -> m b) -> vec a -> m b
wrapStore f v = do
    st <- newStore $ length v
    f st v

fftS  = wrapStore fft  :: DManifest (Complex Double) -> Run (DManifest (Complex Double))
ifftS = wrapStore ifft :: DManifest (Complex Double) -> Run (DPull (Complex Double))

prop_fft_dft dft' fft' = QC.monadicIO $ do
    n   :: Int              <- QC.pick $ QC.choose (2,5)
    inp :: [Complex Double] <- QC.pick $ QC.vector (2 Prelude.^ n)
    outd <- QC.run $ dft' inp
    outf <- QC.run $ fft' inp
    QC.assert (outd ~= outf)

prop_inverse f fi = QC.monadicIO $ do
    n   :: Int              <- QC.pick $ QC.choose (2,5)
    inp :: [Complex Double] <- QC.pick $ QC.vector (2 Prelude.^ n)
    out1 <- QC.run $ f inp
    out2 <- QC.run $ fi out1
    QC.assert (inp ~= out2)

main =
    marshalledM (return . dft)  $ \dft'  ->
    marshalledM (return . idft) $ \idft' ->
    marshalledM fftS            $ \fft'  ->
    marshalledM ifftS           $ \ifft' ->

      defaultMain $ testGroup "tests"
        [ testCase "Demo"       Demo.testAll
        , testCase "Concurrent" Concurrent.testAll
        -- , testCase "CoDesign"   CoDesign.testAll
        , testProperty "fft_dft"  $ prop_fft_dft dft' fft'
        , testProperty "dft_idft" $ prop_inverse dft' idft'
        , testProperty "fft_ifft" $ prop_inverse fft' ifft'
        ]

  where
    marshalledM = marshalled' def def {externalFlagsPost = ["-lm"]}

