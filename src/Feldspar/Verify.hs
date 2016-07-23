module Feldspar.Verify where

import qualified Language.Embedded.Backend.C as Imp
import Feldspar.Run.Compile
import Feldspar.Run
import qualified Language.Embedded.Verify as Verify
import Feldspar.Verify.Representation

verify :: MonadRun m => m () -> IO ()
verify = verified Imp.icompile

verified :: MonadRun m => (ProgC () -> IO a) -> m () -> IO a
verified = verified' def { compilerAssertions = allExcept [] }

verified' :: MonadRun m => CompilerOpts -> (ProgC () -> IO a) -> m () -> IO a
verified' opts backend prog = do
  (prog', warns) <-
    Verify.runVerify .
    withFeldsparGlobals .
    Verify.verify .
    translate (Env mempty opts) .
    liftRun $ prog
  unless (null warns) $ do
    putStrLn "Warnings:"
    sequence_ [putStrLn ("  " ++ warn) | warn <- warns]
    putStrLn ""
  backend prog'

