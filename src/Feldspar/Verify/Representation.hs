-- Feldspar-specific verification bits (expression evaluation).
module Feldspar.Verify.Representation where

import Language.Embedded.Verify hiding (ite)
import Language.Embedded.Verify.SMT hiding (Bool, abs)
import qualified Language.Embedded.Verify.SMT as SMT
import Feldspar.Primitive.Representation
import Language.Syntactic
import Data.Constraint(Dict(..))
import Data.Int
import Data.Word
import Data.Complex
import Data.Typeable
import Language.Embedded.Imperative.CMD
import Language.Embedded.Verify.Arithmetic
import Control.Monad
import Control.Monad.Trans

instance SMTEval1 Prim where
  type Pred Prim = PrimType'
  newtype SMTExpr Prim Bool = Bool SExpr
    deriving Typeable
  -- XXX leave these uninterpreted?
  newtype SMTExpr Prim Float = Float Rat
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Double = Double Rat
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  -- XXX make these uninterpreted?
  data SMTExpr Prim (Complex Float)
    deriving Typeable
  data SMTExpr Prim (Complex Double)
    deriving Typeable
  newtype SMTExpr Prim Int8   = Int8   (BV Signed W8)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Int16  = Int16  (BV Signed W16)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Int32  = Int32  (BV Signed W32)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Int64  = Int64  (BV Signed W64)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word8  = Word8  (BV Unsigned W8)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word16 = Word16 (BV Unsigned W16)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word32 = Word32 (BV Unsigned W32)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word64 = Word64 (BV Unsigned W64)
    deriving (Typeable, Num, SMTOrd, TypedSExpr)

  eval (Prim exp :: Prim a) =
    simpleMatch (\(exp :&: ty) ->
      case witPrimType ty of
        Dict ->
          case witnessPred (undefined :: Prim a) of
            Dict ->
              primEval exp) exp
  
  witnessPred (_ :: Prim a) =
    case primTypeRep :: PrimTypeRep a of
      BoolT   -> Dict
      Int8T   -> Dict
      Int16T  -> Dict
      Int32T  -> Dict
      Int64T  -> Dict
      Word8T  -> Dict
      Word16T -> Dict
      Word32T -> Dict
      Word64T -> Dict
      FloatT  -> Dict
      DoubleT -> Dict
      ComplexFloatT  -> Dict
      ComplexDoubleT -> Dict

instance SMTOrd (SMTExpr Prim Bool) where
  Bool x .<.  Bool y = SMT.not x .&&. y
  Bool x .>.  Bool y = x .&&. SMT.not y
  Bool x .<=. Bool y = SMT.not x .||. y
  Bool x .>=. Bool y = x .||. SMT.not y

instance TypedSExpr (SMTExpr Prim Bool) where
  smtType _ = tBool
  toSMT (Bool x) = x
  fromSMT = Bool

instance SMTEval Prim Bool where
  fromConstant = Bool . bool
  witnessOrd _ = Dict

instance SMTEval Prim Int8 where
  fromConstant = Int8 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Int16 where
  fromConstant = Int16 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Int32 where
  fromConstant = Int32 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Int64 where
  fromConstant = Int64 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word8 where
  fromConstant = Word8 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word16 where
  fromConstant = Word16 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word32 where
  fromConstant = Word32 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Word64 where
  fromConstant = Word64 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict
  witnessIntegral _ = Dict

instance SMTEval Prim Float where
  fromConstant = Float . fromRational . toRational
  witnessOrd _ = Dict
  witnessNum _ = Dict

instance SMTEval Prim Double where
  fromConstant = Double . fromRational . toRational
  witnessOrd _ = Dict
  witnessNum _ = Dict

instance TypedSExpr (SMTExpr Prim (Complex Float)) where
  smtType = error "complex arithmetic not supported"
  toSMT   = error "complex arithmetic not supported"
  fromSMT = error "complex arithmetic not supported"

instance TypedSExpr (SMTExpr Prim (Complex Double)) where
  smtType = error "complex arithmetic not supported"
  toSMT   = error "complex arithmetic not supported"
  fromSMT = error "complex arithmetic not supported"

instance SMTEval Prim (Complex Float) where
  fromConstant = error "complex arithmetic not supported"
  witnessOrd   = error "complex arithmetic not supported"
  witnessNum   = error "complex arithmetic not supported"

instance SMTEval Prim (Complex Double) where
  fromConstant = error "complex arithmetic not supported"
  witnessOrd   = error "complex arithmetic not supported"
  witnessNum   = error "complex arithmetic not supported"

primEval ::
  forall a.
  (PrimType' (DenResult a), SMTEval Prim (DenResult a)) =>
  Primitive a -> Args (AST PrimDomain) a ->
  Verify (SMTExpr Prim (DenResult a))
primEval (FreeVar x) _ = peekVal x
primEval (Lit x) _ = return (fromConstant x)
primEval Add (x :* y :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) =
    liftM2 (+) (eval (Prim x)) (eval (Prim y))
primEval Sub (x :* y :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) =
    liftM2 (-) (eval (Prim x)) (eval (Prim y))
primEval Mul (x :* y :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) =
    liftM2 (*) (eval (Prim x)) (eval (Prim y))
primEval Neg (x :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) =
    fmap negate (eval (Prim x))
primEval Abs (x :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) =
    fmap abs (eval (Prim x))
primEval Sign (x :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) =
    fmap signum (eval (Prim x))
primEval I2N ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessIntegral (undefined :: Prim b) = do
    fmap i2n (eval (Prim x))
primEval I2B ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessNum (undefined :: Prim b) = do
    x <- eval (Prim x)
    return (fromSMT (SMT.not (x .==. 0)))
primEval B2I (x :* Nil)
  | Dict <- witnessNum (undefined :: Prim (DenResult a)) = do
    x <- eval (Prim x)
    return (smtIte (toSMT x) 1 0)
primEval Not (x :* Nil) =
  fmap (fromSMT . SMT.not . toSMT) (eval (Prim x))
primEval And (x :* y :* Nil) = do
  x <- eval (Prim x)
  y <- eval (Prim y)
  return (fromSMT (toSMT x .&&. toSMT y))
primEval Or (x :* y :* Nil) = do
  x <- eval (Prim x)
  y <- eval (Prim y)
  return (fromSMT (toSMT x .||. toSMT y))
primEval Eq ((x :: ASTF PrimDomain b) :* y :* Nil)
  | Dict <- witnessPred (undefined :: Prim b) =
    fmap fromSMT (liftM2 (.==.) (eval (Prim x)) (eval (Prim y)))
primEval NEq ((x :: ASTF PrimDomain b) :* y :* Nil)
  | Dict <- witnessPred (undefined :: Prim b) =
    fmap fromSMT (liftM2 (./=.) (eval (Prim x)) (eval (Prim y)))
  where
    x ./=. y = SMT.not (x .==. y)
primEval Lt ((x :: ASTF PrimDomain b) :* y :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessOrd  (undefined :: Prim b) =
    fmap fromSMT (liftM2 (.<.) (eval (Prim x)) (eval (Prim y)))
primEval Gt ((x :: ASTF PrimDomain b) :* y :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessOrd  (undefined :: Prim b) =
    fmap fromSMT (liftM2 (.>.) (eval (Prim x)) (eval (Prim y)))
primEval Le ((x :: ASTF PrimDomain b) :* y :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessOrd  (undefined :: Prim b) =
    fmap fromSMT (liftM2 (.<=.) (eval (Prim x)) (eval (Prim y)))
primEval Ge ((x :: ASTF PrimDomain b) :* y :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessOrd  (undefined :: Prim b) =
    fmap fromSMT (liftM2 (.>=.) (eval (Prim x)) (eval (Prim y)))
primEval (ArrIx (IArrComp name :: IArr Index b)) (i :* Nil) = do
  arr <- peek name :: Verify (ArrBinding Prim Index b)
  i   <- eval (Prim i)
  return (fromSMT (select (toSMT (arr_value arr)) (toSMT i)))
primEval Cond (cond :* x :* y :* Nil) =
  liftM3 smtIte (fmap toSMT (eval (Prim cond))) (eval (Prim x)) (eval (Prim y))
primEval exp _ = error ("Unimplemented: " ++ show exp)

i2n ::
  forall a b.
  (SMTEval Prim a, SMTEval Prim b, PrimType' a, PrimType' b, Integral a, Num b) =>
  SMTExpr Prim a -> SMTExpr Prim b
i2n x =
  toBV x $
  case primTypeRep :: PrimTypeRep b of
    Int8T   -> Int8   . i2i
    Int16T  -> Int16  . i2i
    Int32T  -> Int32  . i2i
    Int64T  -> Int64  . i2i
    Word8T  -> Word8  . i2i
    Word16T -> Word16 . i2i
    Word32T -> Word32 . i2i
    Word64T -> Word64 . i2i
    FloatT  -> Float  . i2f
    DoubleT -> Double . i2f
    ComplexFloatT  -> error "complex numbers not supported"
    ComplexDoubleT -> error "complex numbers not supported"

  where
    toBV ::
      forall a b.
      (SMTEval Prim a, PrimType' a, Integral a) =>
      SMTExpr Prim a ->
      (forall s w. (Sign s, Width w) => BV s w -> b) -> b
    toBV (x :: SMTExpr Prim a) k =
      case primTypeRep :: PrimTypeRep a of
        Int8T   -> let Int8   y = x in k y
        Int16T  -> let Int16  y = x in k y
        Int32T  -> let Int32  y = x in k y
        Int64T  -> let Int64  y = x in k y
        Word8T  -> let Word8  y = x in k y
        Word16T -> let Word16 y = x in k y
        Word32T -> let Word32 y = x in k y
        Word64T -> let Word64 y = x in k y

    i2f :: (Sign s, Width w) => BV s w -> Rat
    i2f (BV x) = Rat (fun "to_real" [fun "bv2int" [x]])

    i2i :: forall s1 w1 s2 w2. (Sign s1, Width w1, Sign s2, Width w2) => BV s1 w1 -> BV s2 w2
    i2i x =
      case compare m n of
        LT
         | isSigned x -> fromSMT (zeroExtend (n-m) (toSMT x))
         | otherwise  -> fromSMT (signExtend (n-m) (toSMT x))
        EQ -> fromSMT (toSMT x)
        GT -> fromSMT (extract (toSMT x) (n-1) 0)
      where
        m = width (undefined :: w1)
        n = width (undefined :: w2)
