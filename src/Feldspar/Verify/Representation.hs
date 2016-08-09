-- Feldspar-specific verification bits (expression evaluation).
module Feldspar.Verify.Representation where

import Language.Embedded.Verify hiding (ite)
import Language.Embedded.Verify.SMT hiding (Bool, abs, Real, real)
import qualified Language.Embedded.Verify.SMT as SMT
import Feldspar.Primitive.Representation
import Language.Syntactic
import Data.Constraint(Dict(..))
import Data.Int
import Data.Word
import qualified Data.Complex as Complex
import Data.Typeable
import Language.Embedded.Imperative.CMD
import Language.Embedded.Verify.Arithmetic
import Control.Monad
import Control.Monad.Trans
import qualified Data.Bits as Bits

instance SMTEval1 Prim where
  type Pred Prim = PrimType'
  newtype SMTExpr Prim Bool = Bool SExpr
    deriving Typeable
  newtype SMTExpr Prim Float = Float (Symbolic SFloat)
    deriving (Typeable, Num, Fractional, Floating, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Double = Double (Symbolic SDouble)
    deriving (Typeable, Num, Fractional, Floating, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim (Complex.Complex Float) = CFloat (Symbolic SCFloat)
    deriving (Typeable, Num, Fractional, Floating, TypedSExpr)
  newtype SMTExpr Prim (Complex.Complex Double) = CDouble (Symbolic SCDouble)
    deriving (Typeable, Num, Fractional, Floating, TypedSExpr)
  newtype SMTExpr Prim Int8   = Int8   (BV Signed W8)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Int16  = Int16  (BV Signed W16)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Int32  = Int32  (BV Signed W32)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Int64  = Int64  (BV Signed W64)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word8  = Word8  (BV Unsigned W8)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word16 = Word16 (BV Unsigned W16)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word32 = Word32 (BV Unsigned W32)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)
  newtype SMTExpr Prim Word64 = Word64 (BV Unsigned W64)
    deriving (Typeable, Num, Real, Enum, Integral, Bits, SMTOrd, TypedSExpr)

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

instance SMTEval Prim Int16 where
  fromConstant = Int16 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Int32 where
  fromConstant = Int32 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Int64 where
  fromConstant = Int64 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Word8 where
  fromConstant = Word8 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Word16 where
  fromConstant = Word16 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Word32 where
  fromConstant = Word32 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Word64 where
  fromConstant = Word64 . fromIntegral
  witnessNum      _ = Dict
  witnessOrd      _ = Dict

instance SMTEval Prim Float where
  fromConstant = Float . fromRational . toRational
  witnessOrd _ = Dict
  witnessNum _ = Dict

instance SMTEval Prim Double where
  fromConstant = Double . fromRational . toRational
  witnessOrd _ = Dict
  witnessNum _ = Dict

instance SMTEval Prim (Complex.Complex Float) where
  fromConstant = CFloat . fromComplexConstant
  witnessNum _ = Dict

instance SMTEval Prim (Complex.Complex Double) where
  fromConstant = CDouble . fromComplexConstant
  witnessNum _ = Dict

class Floating a => Complex a where
  type RealPart a
  complex, polar :: RealPart a -> RealPart a -> a
  real, imag, magnitude, phase :: a -> RealPart a
  conjugate :: a -> a

instance Complex (SMTExpr Prim (Complex.Complex Float)) where
  type RealPart (SMTExpr Prim (Complex.Complex Float)) =
    SMTExpr Prim Float
  complex (Float x) (Float y) = CFloat (complex x y)
  polar (Float x) (Float y) = CFloat (polar x y)
  real (CFloat x) = Float (real x)
  imag (CFloat x) = Float (imag x)
  magnitude (CFloat x) = Float (magnitude x)
  phase (CFloat x) = Float (phase x)
  conjugate (CFloat x) = CFloat (conjugate x)

instance Complex (SMTExpr Prim (Complex.Complex Double)) where
  type RealPart (SMTExpr Prim (Complex.Complex Double)) =
    SMTExpr Prim Double
  complex (Double x) (Double y) = CDouble (complex x y)
  polar (Double x) (Double y) = CDouble (polar x y)
  real (CDouble x) = Double (real x)
  imag (CDouble x) = Double (imag x)
  magnitude (CDouble x) = Double (magnitude x)
  phase (CDouble x) = Double (phase x)
  conjugate (CDouble x) = CDouble (conjugate x)

witnessComplex :: (PrimType' a, PrimType' (Complex.Complex a)) => Prim (Complex.Complex a) -> Dict (Floating (SMTExpr Prim a), Complex (SMTExpr Prim (Complex.Complex a)), RealPart (SMTExpr Prim (Complex.Complex a)) ~ SMTExpr Prim a)
witnessComplex (_ :: Prim (Complex.Complex a)) =
  case primTypeRep :: PrimTypeRep (Complex.Complex a) of
    ComplexFloatT  -> Dict
    ComplexDoubleT -> Dict

witnessFractional :: (PrimType' a, Fractional a) => Prim a -> Dict (Floating (SMTExpr Prim a))
witnessFractional (_ :: Prim a) =
  case primTypeRep :: PrimTypeRep a of
    FloatT         -> Dict
    DoubleT        -> Dict
    ComplexFloatT  -> Dict
    ComplexDoubleT -> Dict

toRat :: (PrimType' a, Fractional a) => SMTExpr Prim a -> Rat
toRat (x :: SMTExpr Prim a) =
  case primTypeRep :: PrimTypeRep a of
    FloatT         -> let Float   (Symbolic y) = x in y
    DoubleT        -> let Double  (Symbolic y) = x in y
    ComplexFloatT  -> let CFloat  (Symbolic y) = x in y
    ComplexDoubleT -> let CDouble (Symbolic y) = x in y

fromRat :: forall a. (PrimType' a, Num a) => Rat -> SMTExpr Prim a
fromRat x =
  case primTypeRep :: PrimTypeRep a of
    Int8T -> Int8 (f2i x)
  where
    f2i :: forall s w. (Sign s, Width w) => Rat -> BV s w
    f2i (Rat x) =
      BV $ List [fam "int2bv" [width (undefined :: w)], fun "to_int" [x]]

witnessIntegral :: (PrimType' a, Integral a) => Prim a -> Dict (Integral (SMTExpr Prim a), Bits (SMTExpr Prim a))
witnessIntegral (_ :: Prim a) =
  case primTypeRep :: PrimTypeRep a of
    Int8T   -> Dict
    Int16T  -> Dict
    Int32T  -> Dict
    Int64T  -> Dict
    Word8T  -> Dict
    Word16T -> Dict
    Word32T -> Dict
    Word64T -> Dict

witnessBits :: (PrimType' a, Bits.Bits a) => Prim a -> Dict (Num a, Integral (SMTExpr Prim a), Bits (SMTExpr Prim a))
witnessBits (_ :: Prim a) =
  case primTypeRep :: PrimTypeRep a of
    Int8T   -> Dict
    Int16T  -> Dict
    Int32T  -> Dict
    Int64T  -> Dict
    Word8T  -> Dict
    Word16T -> Dict
    Word32T -> Dict
    Word64T -> Dict

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
primEval Div (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    liftM2 div (eval (Prim x)) (eval (Prim y))
primEval Mod (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    liftM2 mod (eval (Prim x)) (eval (Prim y))
primEval Quot (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    liftM2 quot (eval (Prim x)) (eval (Prim y))
primEval Rem (x :* y :* Nil)
  | Dict <- witnessIntegral (undefined :: Prim (DenResult a)) =
    liftM2 rem (eval (Prim x)) (eval (Prim y))
primEval FDiv (x :* y :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    liftM2 (/) (eval (Prim x)) (eval (Prim y))
primEval Pi Nil
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    return pi
primEval Exp (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap exp (eval (Prim x))
primEval Log (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap log (eval (Prim x))
primEval Sqrt (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap sqrt (eval (Prim x))
primEval Pow (x :* y :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    liftM2 (**) (eval (Prim x)) (eval (Prim y))
primEval Sin (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap sin (eval (Prim x))
primEval Cos (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap cos (eval (Prim x))
primEval Tan (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap tan (eval (Prim x))
primEval Asin (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap asin (eval (Prim x))
primEval Acos (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap acos (eval (Prim x))
primEval Atan (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap atan (eval (Prim x))
primEval Sinh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap sinh (eval (Prim x))
primEval Cosh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap cosh (eval (Prim x))
primEval Tanh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap tanh (eval (Prim x))
primEval Asinh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap asinh (eval (Prim x))
primEval Acosh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap acosh (eval (Prim x))
primEval Atanh (x :* Nil)
  | Dict <- witnessFractional (undefined :: Prim (DenResult a)) =
    fmap atanh (eval (Prim x))
primEval Complex (x :* y :* Nil)
  | Dict <- witnessComplex (undefined :: Prim (DenResult a)) =
    liftM2 complex (eval (Prim x)) (eval (Prim y))
primEval Polar (x :* y :* Nil)
  | Dict <- witnessComplex (undefined :: Prim (DenResult a)) =
    liftM2 polar (eval (Prim x)) (eval (Prim y))
primEval Real ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap real (eval (Prim x))
primEval Imag ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap imag (eval (Prim x))
primEval Magnitude ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap magnitude (eval (Prim x))
primEval Phase ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap phase (eval (Prim x))
primEval Conjugate ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessComplex (undefined :: Prim b) =
    fmap conjugate (eval (Prim x))
primEval I2N ((x :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessNum (undefined :: Prim b) = do
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
primEval Round ((x :: ASTF PrimDomain b) :* Nil) = do
  x <- eval (Prim x)
  return (fromRat (toRat x))
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
primEval BitAnd (x :* y :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    liftM2 (.&.) (eval (Prim x)) (eval (Prim y))
primEval BitOr (x :* y :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    liftM2 (.|.) (eval (Prim x)) (eval (Prim y))
primEval BitXor (x :* y :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    liftM2 xor (eval (Prim x)) (eval (Prim y))
primEval BitCompl (x :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)) =
    fmap complement (eval (Prim x))
primEval ShiftL (x :* (y :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)),
    Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessIntegral (undefined :: Prim b) = do
    -- XXX should check for undefined behaviour
    x <- eval (Prim x)
    y <- eval (Prim y)
    return (shiftL x (i2n y))
primEval ShiftR (x :* (y :: ASTF PrimDomain b) :* Nil)
  | Dict <- witnessBits (undefined :: Prim (DenResult a)),
    Dict <- witnessPred (undefined :: Prim b),
    Dict <- witnessIntegral (undefined :: Prim b) = do
    -- XXX should check for undefined behaviour
    x <- eval (Prim x)
    y <- eval (Prim y)
    return (shiftR x (i2n y))
primEval (ArrIx (IArrComp name :: IArr Index b)) (i :* Nil) = do
  i <- eval (Prim i)
  arrIx name i
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
    FloatT  -> Float  . Symbolic . i2f
    DoubleT -> Double . Symbolic . i2f
    ComplexFloatT  -> CFloat  . Symbolic . i2f
    ComplexDoubleT -> CDouble . Symbolic . i2f

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
         | isSigned x -> fromSMT (signExtend (n-m) (toSMT x))
         | otherwise  -> fromSMT (zeroExtend (n-m) (toSMT x))
        EQ -> fromSMT (toSMT x)
        GT -> fromSMT (extract (toSMT x) (n-1) 0)
      where
        m = width (undefined :: w1)
        n = width (undefined :: w2)

newtype Symbolic a = Symbolic { unSymbolic :: Rat }
  deriving (Eq, Ord, Show, TypedSExpr, SMTOrd)

data SFloat
data SDouble
data SCFloat
data SCDouble

class SymbParam a where symbType :: a -> String
instance SymbParam SFloat   where symbType _ = "float"
instance SymbParam SDouble  where symbType _ = "double"
instance SymbParam SCFloat  where symbType _ = "cfloat"
instance SymbParam SCDouble where symbType _ = "cdouble"

instance SymbParam a => Fresh (Symbolic a) where
  fresh = freshSExpr

instance SymbParam a => Num (Symbolic a) where
  fromInteger = Symbolic . fromInteger
  x + y = symbFun "+" [x, y]
  x - y = symbFun "-" [x, y]
  x * y = symbFun "*" [x, y]
  abs = smtAbs
  signum = smtSignum

instance SymbParam a => Fractional (Symbolic a) where
  fromRational = Symbolic . fromRational
  x / y = symbFun "/" [x, y]

instance SymbParam a => Floating (Symbolic a) where
  pi = fromRational (toRational pi)
  exp x = symbFun "exp" [x]
  log x = symbFun "log" [x]
  sqrt x = symbFun "sqrt" [x]
  x ** y = symbFun "pow" [x, y]
  sin x = symbFun "sin" [x]
  cos x = symbFun "cos" [x]
  tan x = symbFun "tan" [x]
  asin x = symbFun "asin" [x]
  acos x = symbFun "acos" [x]
  atan x = symbFun "atan" [x]
  sinh x = symbFun "sinh" [x]
  cosh x = symbFun "cosh" [x]
  tanh x = symbFun "tanh" [x]
  asinh x = symbFun "asinh" [x]
  acosh x = symbFun "acosh" [x]
  atanh x = symbFun "atanh" [x]

class SymbParam a => SymbComplex a where type SymbRealPart a
instance SymbComplex SCFloat where type SymbRealPart SCFloat = SFloat
instance SymbComplex SCDouble where type SymbRealPart SCDouble = SDouble

instance SymbComplex a => Complex (Symbolic a) where
  type RealPart (Symbolic a) = Symbolic (SymbRealPart a)
  complex x y = symbFun "complex" [symbCast x, symbCast y]
  polar x y = symbFun "polar" [symbCast x, symbCast y]
  real x = symbCast (symbFun "real" [x])
  imag x = symbCast (symbFun "imag" [x])
  magnitude x = symbCast (symbFun "magnitude" [x])
  phase x = symbCast (symbFun "phase" [x])
  conjugate x = symbFun "conjugate" [x]

symbCast :: Symbolic a -> Symbolic b
symbCast = Symbolic . unSymbolic

symbFun :: SymbParam a => String -> [Symbolic a] -> Symbolic a
symbFun name (args :: [Symbolic a]) =
  fromSMT $
  fun (symbType (undefined :: a) ++ "-" ++ name)
    (map toSMT args)

fromComplexConstant :: forall a b. (RealFrac a, SymbParam b) => Complex.Complex a -> Symbolic b
fromComplexConstant x =
  symbFun "complex" [real, imag]
  where
    real = Symbolic (fromRational (toRational (Complex.realPart x)))
    imag = Symbolic (fromRational (toRational (Complex.imagPart x)))

declareSymbFun :: SymbParam a => String -> a -> [SExpr] -> SExpr -> SMT ()
declareSymbFun name (_ :: a) args res = do
  declareFun (symbType (undefined :: a) ++ "-" ++ name) args res
  return ()

declareSymbArith :: SymbParam a => a -> SMT ()
declareSymbArith x = do
  declareSymbFun "+" x [tReal, tReal] tReal
  declareSymbFun "-" x [tReal, tReal] tReal
  declareSymbFun "*" x [tReal, tReal] tReal
  declareSymbFun "/" x [tReal, tReal] tReal
  declareSymbFun "exp" x [tReal] tReal
  declareSymbFun "log" x [tReal] tReal
  declareSymbFun "sqrt" x [tReal] tReal
  declareSymbFun "pow" x [tReal, tReal] tReal
  declareSymbFun "sin" x [tReal] tReal
  declareSymbFun "cos" x [tReal] tReal
  declareSymbFun "tan" x [tReal] tReal
  declareSymbFun "asin" x [tReal] tReal
  declareSymbFun "acos" x [tReal] tReal
  declareSymbFun "atan" x [tReal] tReal
  declareSymbFun "sinh" x [tReal] tReal
  declareSymbFun "cosh" x [tReal] tReal
  declareSymbFun "tanh" x [tReal] tReal
  declareSymbFun "asinh" x [tReal] tReal
  declareSymbFun "acosh" x [tReal] tReal
  declareSymbFun "atanh" x [tReal] tReal

declareSymbComplex :: SymbParam a => a -> SMT ()
declareSymbComplex x = do
  declareSymbArith x
  declareSymbFun "complex" x [tReal, tReal] tReal
  declareSymbFun "polar" x [tReal, tReal] tReal
  declareSymbFun "real" x [tReal] tReal
  declareSymbFun "imag" x [tReal] tReal
  declareSymbFun "magnitude" x [tReal] tReal
  declareSymbFun "phase" x [tReal] tReal
  declareSymbFun "conjugate" x [tReal] tReal

declareFeldsparGlobals :: SMT ()
declareFeldsparGlobals = do
  declareSymbArith (undefined :: SFloat)
  declareSymbArith (undefined :: SDouble)
  declareSymbComplex (undefined :: SCFloat)
  declareSymbComplex (undefined :: SCDouble)
